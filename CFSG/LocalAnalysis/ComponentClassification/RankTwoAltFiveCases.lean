module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypNF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveDefs

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoClassical CFSG.Blueprint

namespace CFSG.ComponentClassification.RankTwoAltFive

structure Setting310 {G : Type} [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (T V₀ : Subgroup G) : Prop where
  hyp : RankTwoHypNF G A
  oddCore : standardComponentOddCore G = ⊥
  equiv : Nonempty (↥A ≃* A5)
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  noConj : ∀ x : G, ¬ rightConjugate R x ≤ A
  sup_top : rankTwoX A ⊔ R = ⊤
  loc : Case310Local A R g T V₀
  cardR : Nat.card R = 4

variable {G : Type} [Group G] [Finite G]

theorem Setting310.card_V₀ {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀) :
    Nat.card V₀ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.equiv
  rw [h.loc.sylowV₀.card_eq, Nat.card_congr e.toEquiv, fact_A5]
  rfl

theorem Setting310.elemR {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀) :
    IsElemAbelian 2 R := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => h.loc.elem.2 x (mem_sup_left hx)⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val
    (h.loc.elem.1.is_comm.comm ⟨(x : G), mem_sup_left x.2⟩ ⟨(y : G), mem_sup_left y.2⟩)

theorem setting310_ofNF {A R T V₀ : Subgroup G} {g : G}
    (hH : RankTwoHypNF G A) (hO : standardComponentOddCore G = ⊥)
    (hA5 : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)))
    (hodd : Odd (Nat.card (center ↥A))) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hno : ∀ x : G, ¬ rightConjugate R x ≤ A) (hXR : rankTwoX A ⊔ R = ⊤)
    (hloc : Case310Local A R g T V₀) : Setting310 A R g T V₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  have hAperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hZ : center ↥A = ⊥ := RankTwoAlt.center_eq_bot_of_odd_five hAperf e hodd
  let eA : ↥A ≃* A5 :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hV₀ : Nat.card V₀ = 4 := by
    rw [hloc.sylowV₀.card_eq, Nat.card_congr eA.toEquiv, fact_A5]
    rfl
  have hRV₀ : R ⊓ V₀ = ⊥ := by
    have h := hloc.spread 1 (by rw [rightConjugate_one]; exact le_sup_left)
    rwa [rightConjugate_one] at h
  have hV₀A : V₀ ≤ A := hloc.inf_A ▸ inf_le_right
  have hV₀N : V₀ ≤ normalizer (R : Set G) :=
    (hV₀A.trans (le_centralizer_iff.mp hR.le)).trans (centralizer_le_normalizer _)
  have hsup := card_sup_eq_mul hV₀N hRV₀
  have hle : R ⊔ V₀ ≤ R ⊔ T := sup_le le_sup_left (hloc.inf_A ▸ inf_le_left)
  have h16 := Subgroup.card_le_of_le hle
  rw [hsup, hV₀, hloc.card] at h16
  obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hH.rank
  obtain ⟨S, hS, hUS⟩ :=
    exists_isSylowOf_le hUK (fun v => ⟨1, Subtype.ext (by simpa using hU.2 v v.2)⟩)
  obtain ⟨c, -, hSc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hR hS
  have h4 := Subgroup.card_le_of_le hUS
  rw [hSc, Lemma34.card_conj, hU4] at h4
  exact ⟨hH, hO, ⟨eA⟩, hR, hno, hXR, hloc, by omega⟩

theorem setting310_of {A R T V₀ : Subgroup G} {g : G}
    (hH : RankTwoHyp G A) (hO : standardComponentOddCore G = ⊥)
    (hA5 : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)))
    (hodd : Odd (Nat.card (center ↥A))) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hno : ∀ x : G, ¬ rightConjugate R x ≤ A) (hXR : rankTwoX A ⊔ R = ⊤)
    (hloc : Case310Local A R g T V₀) : Setting310 A R g T V₀ :=
  setting310_ofNF hH.toNF hO hA5 hodd hR hno hXR hloc

theorem mem_centralizer_of_sq_mem {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : R ≤ centralizer (R : Set G)) {u : G} (huK : u ∈ K) (huN : u ∈ normalizer (R : Set G))
    (hu : u * u ∈ centralizer (R : Set G)) : u ∈ centralizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
  rcases Nat.eq_zero_or_pos a with rfl | ha
  ·
    obtain ⟨k, hk⟩ := hb
    have hu1 : u ^ (2 * (k + 1)) = u := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, ← one_mul b, ← pow_zero 2,
        ← hab, pow_orderOf_eq_one, one_mul]
    rw [← hu1, pow_mul, sq]
    exact pow_mem hu _
  ·
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    have hv : IsPGroup 2 (zpowers (u ^ b)) := by
      apply IsPGroup.of_card (n := a)
      rw [Nat.card_zpowers, orderOf_pow' u hb0, hab, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
    have hvN : zpowers (u ^ b) ≤ normalizer (R : Set G) := zpowers_le.mpr (pow_mem huN b)
    have hsup := IsPGroup.to_sup_of_normal_left' hR.isPGroup hv hvN
    have heq := hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr (pow_mem huK b))) hsup
    have hvR : u ^ b ∈ R := heq ▸ (le_sup_right : zpowers (u ^ b) ≤ R ⊔ zpowers (u ^ b))
      (mem_zpowers _)
    have hw : u ^ 2 ^ a ∈ centralizer (R : Set G) := by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt ha
      rw [show 0 + c + 1 = c + 1 by ring, pow_succ, pow_mul', sq]
      exact pow_mem hu _
    have hcop : Nat.Coprime b (2 ^ a) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr
        (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hb))))
    have hgcd := Nat.gcd_eq_gcd_ab b (2 ^ a)
    rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
    have hu' : u = (u ^ b) ^ (Nat.gcdA b (2 ^ a)) * (u ^ 2 ^ a) ^ (Nat.gcdB b (2 ^ a)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd, zpow_one]
    rw [hu']
    exact mul_mem (zpow_mem (hRc hvR) _) (zpow_mem hw _)

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {w c : G} (hw : orderOf w = 2) (hc : c ∈ zpowers w) :
    c = 1 ∨ c = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
  · right; rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one]

theorem rankTwoX_eq_top_of_IIa {A R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) (hXR : rankTwoX A ⊔ R = ⊤) {y : G}
    (hyK : y ∈ centralizer (A : Set G)) (hyN : y ∈ normalizer (R : Set G))
    (hyC : y ∉ centralizer (R : Set G)) : rankTwoX A = ⊤ := by
  set X := rankTwoX A with hXdef
  have hXn : X.Normal := normalClosure_normal
  have hRc : R ≤ centralizer (R : Set G) := le_centralizer_self_of_isElemAbelian hRe
  have hrr : ∀ r ∈ R, r * r = 1 := fun r hr => by rw [← sq]; exact hRe.2 r hr
  have hsq : ∀ g : G, g * g ∈ X := by
    intro g
    have hg : g ∈ ((X ⊔ R : Subgroup G) : Set G) := by rw [hXR]; trivial
    rw [normal_mul] at hg
    obtain ⟨x, hx, r, hr, rfl⟩ := hg
    have h1 : x * r * (x * r) = x * (r * x * r⁻¹) * (r * r) := by group
    rw [h1, hrr r hr, mul_one]
    exact mul_mem hx (hXn.conj_mem x hx r)
  have hy₁X : y * y ∈ X := hsq y
  have hy₁K : y * y ∈ centralizer (A : Set G) := mul_mem hyK hyK
  have hy₁N : y * y ∈ normalizer (R : Set G) := mul_mem hyN hyN
  have hy₁C : y * y ∉ centralizer (R : Set G) := fun h =>
    hyC (mem_centralizer_of_sq_mem hR hRc hyK hyN h)
  set y₁ := y * y with hy₁def
  have hc : ∀ r ∈ R, r⁻¹ * (y₁ * r * y₁⁻¹) ∈ R ⊓ X := by
    intro r hr
    refine mem_inf.mpr ⟨mul_mem (inv_mem hr) ((mem_normalizer_iff.mp hy₁N r).mp hr), ?_⟩
    have h1 : r⁻¹ * (y₁ * r * y₁⁻¹) = (r⁻¹ * y₁ * r) * y₁⁻¹ := by group
    rw [h1]
    refine mul_mem ?_ (inv_mem hy₁X)
    simpa using hXn.conj_mem y₁ hy₁X r⁻¹
  have hRX : R ≤ X := by
    by_contra hRX
    obtain ⟨r₀, hr₀, hne⟩ : ∃ r₀ ∈ R, y₁ * r₀ * y₁⁻¹ ≠ r₀ := by
      by_contra h
      push Not at h
      apply hy₁C
      rw [mem_centralizer_iff]
      intro r hr
      have h1 := h r hr
      calc r * y₁ = y₁ * r * y₁⁻¹ * y₁ := by rw [h1]
        _ = y₁ * r := by group
    set w := r₀⁻¹ * (y₁ * r₀ * y₁⁻¹) with hwdef
    have hwX : w ∈ R ⊓ X := hc r₀ hr₀
    have hw1 : w ≠ 1 := fun h => hne (by
      have h1 : y₁ * r₀ * y₁⁻¹ = r₀ * w := by rw [hwdef]; group
      rw [h1, h, mul_one])
    have hw2 : orderOf w = 2 :=
      orderOf_eq_prime (hRe.2 w (mem_inf.mp hwX).1) hw1
    have hcard : Nat.card (R ⊓ X : Subgroup G) ≤ 2 := by
      have hdvd : Nat.card (R ⊓ X : Subgroup G) ∣ 4 := hR4 ▸ card_dvd_of_le inf_le_left
      have hne4 : Nat.card (R ⊓ X : Subgroup G) ≠ 4 := fun h => hRX (by
        have := eq_of_le_of_card_ge (inf_le_left : R ⊓ X ≤ R) (by rw [h, hR4])
        rw [← this]
        exact inf_le_right)
      have h4 : Nat.card (R ⊓ X : Subgroup G) ∈ Nat.divisors 4 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [this] at h4
      simp only [Finset.mem_insert, Finset.mem_singleton] at h4
      omega
    have hzw : zpowers w = R ⊓ X := eq_of_le_of_card_ge (zpowers_le.mpr hwX)
      (by rw [Nat.card_zpowers, hw2]; exact hcard)
    have h1w : ∀ c ∈ R ⊓ X, c = 1 ∨ c = w := fun c hc' =>
      eq_one_or_eq_of_mem_zpowers hw2 (hzw ▸ hc')
    have hyw : y₁ * w * y₁⁻¹ = w := by
      rcases h1w _ (hc w (mem_inf.mp hwX).1) with h | h
      · calc y₁ * w * y₁⁻¹ = w * (w⁻¹ * (y₁ * w * y₁⁻¹)) := by group
          _ = w := by rw [h, mul_one]
      · exfalso
        apply hw1
        have h2 : y₁ * w * y₁⁻¹ = w * w := by
          calc y₁ * w * y₁⁻¹ = w * (w⁻¹ * (y₁ * w * y₁⁻¹)) := by group
            _ = w * w := by rw [h]
        have h3 : w * w = 1 := hrr w (mem_inf.mp hwX).1
        rw [h3] at h2
        calc w = y₁⁻¹ * (y₁ * w * y₁⁻¹) * y₁ := by group
          _ = 1 := by rw [h2]; group
    have hy₁sq : y₁ * y₁ ∈ centralizer (R : Set G) := by
      rw [mem_centralizer_iff]
      intro r hr
      have h2 : y₁ * y₁ * r * (y₁ * y₁)⁻¹ = r := by
        rcases h1w _ (hc r hr) with h | h
        · have h1 : y₁ * r * y₁⁻¹ = r := by
            calc y₁ * r * y₁⁻¹ = r * (r⁻¹ * (y₁ * r * y₁⁻¹)) := by group
              _ = r := by rw [h, mul_one]
          calc y₁ * y₁ * r * (y₁ * y₁)⁻¹ = y₁ * (y₁ * r * y₁⁻¹) * y₁⁻¹ := by group
            _ = r := by rw [h1, h1]
        · have h1 : y₁ * r * y₁⁻¹ = r * w := by
            calc y₁ * r * y₁⁻¹ = r * (r⁻¹ * (y₁ * r * y₁⁻¹)) := by group
              _ = r * w := by rw [h]
          calc y₁ * y₁ * r * (y₁ * y₁)⁻¹ = y₁ * (y₁ * r * y₁⁻¹) * y₁⁻¹ := by group
            _ = y₁ * (r * w) * y₁⁻¹ := by rw [h1]
            _ = (y₁ * r * y₁⁻¹) * (y₁ * w * y₁⁻¹) := by group
            _ = r := by rw [h1, hyw, mul_assoc, hrr w (mem_inf.mp hwX).1, mul_one]
      calc r * (y₁ * y₁) = y₁ * y₁ * r * (y₁ * y₁)⁻¹ * (y₁ * y₁) := by rw [h2]
        _ = y₁ * y₁ * r := by group
    exact hy₁C (mem_centralizer_of_sq_mem hR hRc hy₁K hy₁N hy₁sq)
  rw [← hXR]
  exact (sup_eq_left.mpr hRX).symm

@[expose] def Asc310IIa : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ : Subgroup G),
    Setting310 A R g T V₀ → rankTwoX A = ⊤ →
    ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
      NativeSporadic.IsSporadic (rankTwoX A) .J2

@[expose] def Asc310IIb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ : Subgroup G),
    Setting310 A R g T V₀ →
    centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
      NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧
        ∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
          ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹

theorem asc08Lemma310Local_of_cases (ha : Asc310IIa)
    (hb : Asc310IIb) : Asc08Lemma310Local := by
  intro G _ _ A hH hO hA5 hodd R hR hno hXR g T V₀ hloc
  have hS := setting310_of hH hO hA5 hodd hR hno hXR hloc
  by_cases hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G)
  · exact Or.inr (hb G A R g T V₀ hS hIIb)
  · obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hIIb
    have hX := rankTwoX_eq_top_of_IIa hR hS.elemR hS.cardR hXR (mem_inf.mp hy).1
      (mem_inf.mp hy).2 hyC
    exact Or.inl (ha G A R g T V₀ hS hX hIIb)

end CFSG.ComponentClassification.RankTwoAltFive
