module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow

public section

namespace CFSG.OddStandard.Seitz77.Sec26

open CFSG.ComponentClassification.GoldschmidtFour
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ABGLocalTools CFSG.Open Subgroup
open scoped commutatorElement Pointwise

theorem zpow_involution {G : Type*} [Group G] {x : G} (hx2 : x * x = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have ht2' : x ^ 2 = 1 := by rwa [sq]
  have : x ^ k = x ^ (k % 2) * (x ^ 2) ^ (k / 2) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    omega
  rw [ht2', one_zpow, mul_one] at this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [this, h0]; simp
  · right; rw [this, h1]; simp

theorem inf_centralizer_le_of_mem_sup {G : Type*} [Group G] {W : Subgroup G} {t x : G}
    (hW : IsElemAbelian 2 W) (htN : t ∈ normalizer (W : Set G)) (ht2 : t * t = 1)
    (hx : x ∈ W ⊔ zpowers t) (hxW : x ∉ W) :
    W ⊓ centralizer ({x} : Set G) ≤ W ⊓ centralizer ({t} : Set G) := by
  have htN' : zpowers t ≤ normalizer (W : Set G) := by
    rw [zpowers_le]; exact htN
  obtain ⟨w, hw, y, hy, hxy⟩ : x ∈ (W : Set G) * (zpowers t : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left W (zpowers t) htN']; exact hx
  have hxy' : w * y = x := hxy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rcases zpow_involution ht2 k with hk | hk
  · rw [hk, mul_one] at hxy'
    exact absurd (hxy' ▸ hw) hxW
  · rw [hk] at hxy'
    intro u hu
    refine ⟨hu.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxu : u * x = x * u := mem_centralizer_singleton_iff.mp hu.2
    have huw : u * w = w * u := L34.comm_of_isElemAbelian hW hu.1 hw
    rw [← hxy'] at hxu
    have h3 : w * (u * t) = w * (t * u) := by
      calc w * (u * t) = (w * u) * t := by group
        _ = (u * w) * t := by rw [huw]
        _ = u * (w * t) := by group
        _ = (w * t) * u := hxu
        _ = w * (t * u) := by group
    exact mul_left_cancel h3

theorem card_commutator_mul_card_centralizer {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    {x : G} (hW : IsElemAbelian 2 W) (hxN : x ∈ normalizer (W : Set G)) (hx2 : x * x = 1) :
    Nat.card ↥⁅W, zpowers x⁆ * Nat.card ↥(W ⊓ centralizer ({x} : Set G)) = Nat.card W := by
  have hcomm : ∀ {a b : G}, a ∈ W → b ∈ W → a * b = b * a := fun {a b} ha hb =>
    L34.comm_of_isElemAbelian hW ha hb
  have hconj : ∀ w ∈ W, x⁻¹ * w * x ∈ W := fun w hw => (mem_normalizer_iff''.mp hxN w).mp hw
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let f : ↥W →* G := MonoidHom.mk' (fun w => (w : G)⁻¹ * (x⁻¹ * (w : G) * x)) (by
    intro a b
    have ha : (a : G) ∈ W := a.2
    have hb : (b : G) ∈ W := b.2
    have hc : (a : G)⁻¹ * (x⁻¹ * (a : G) * x) ∈ W := W.mul_mem (W.inv_mem ha) (hconj a ha)
    have h1 : (b : G)⁻¹ * ((a : G)⁻¹ * (x⁻¹ * (a : G) * x)) =
        ((a : G)⁻¹ * (x⁻¹ * (a : G) * x)) * (b : G)⁻¹ := hcomm (W.inv_mem hb) hc
    calc ((a * b : ↥W) : G)⁻¹ * (x⁻¹ * ((a * b : ↥W) : G) * x)
        = (b : G)⁻¹ * ((a : G)⁻¹ * (x⁻¹ * (a : G) * x)) * (x⁻¹ * (b : G) * x) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]; group
      _ = ((a : G)⁻¹ * (x⁻¹ * (a : G) * x)) * ((b : G)⁻¹ * (x⁻¹ * (b : G) * x)) := by
          rw [h1]; group)
  have hker : f.ker = (W ⊓ centralizer ({x} : Set G)).subgroupOf W := by
    ext w
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨w.2, ?_⟩
      have h' : (w : G)⁻¹ * (x⁻¹ * (w : G) * x) = 1 := h
      have h1 : x⁻¹ * (w : G) * x = (w : G) := by
        calc x⁻¹ * (w : G) * x = (w : G) * ((w : G)⁻¹ * (x⁻¹ * (w : G) * x)) := by group
          _ = (w : G) := by rw [h', mul_one]
      calc (w : G) * x = x * (x⁻¹ * (w : G) * x) := by group
        _ = x * (w : G) := by rw [h1]
    · rintro ⟨-, h⟩
      have h' : (w : G) * x = x * (w : G) := h
      show (w : G)⁻¹ * (x⁻¹ * (w : G) * x) = 1
      calc (w : G)⁻¹ * (x⁻¹ * (w : G) * x) = (w : G)⁻¹ * (x⁻¹ * ((w : G) * x)) := by group
        _ = (w : G)⁻¹ * (x⁻¹ * (x * (w : G))) := by rw [h']
        _ = 1 := by group
  have hrange : f.range = ⁅W, zpowers x⁆ := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      have h1 : f w = ⁅(w : G)⁻¹, x⁻¹⁆ := by
        show (w : G)⁻¹ * (x⁻¹ * (w : G) * x) = _
        rw [commutatorElement_def]; group
      rw [h1]
      exact Subgroup.commutator_mem_commutator (W.inv_mem w.2) (inv_mem (mem_zpowers x))
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rcases zpow_involution hx2 k with h | h
      · rw [h]; simp
      · rw [h]
        refine ⟨⟨a⁻¹, W.inv_mem ha⟩, ?_⟩
        show ((a⁻¹)⁻¹) * (x⁻¹ * a⁻¹ * x) = ⁅a, x⁆
        rw [commutatorElement_def, hxinv]; group
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have e1 : Nat.card (↥W ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have e2 : Nat.card f.ker = Nat.card ↥(W ⊓ centralizer ({x} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hrange] at e1
  rw [hcard, e1, e2]

theorem weak_closure_of_actions {G : Type} [Group G] [Finite G] {S W V₁ : Subgroup G} {t : G}
    (hSN : S ≤ normalizer (W : Set G)) (hW : IsElemAbelian 2 W)
    (hcardW : Nat.card W = 2 ^ 8) (htS : t ∈ S) (ht2 : t * t = 1)
    (hCt : W ⊓ centralizer ({t} : Set G) = V₁) (hcardV₁ : Nat.card V₁ = 16)
    (hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers t → Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ 16)
    (hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 8) :
    ∀ g : G, rightConjugate W g ≤ S → rightConjugate W g = W := by
  intro g hgS
  set U := rightConjugate W g with hU
  have hUel : IsElemAbelian 2 U := L34.isElemAbelian_map _ hW
  have hcardU : Nat.card U = 2 ^ 8 := by rw [hU, rightConjugate_card, hcardW]
  have h32 : 32 ≤ Nat.card ↥(W ⊓ U) := by
    have h8 := hR1 U hgS hUel
    have h := Subgroup.relIndex_mul_card (H := W) (K := U)
    rw [hcardU] at h
    have hpos : 0 < Nat.card ↥(W ⊓ U) := Nat.card_pos
    by_contra hlt
    have hlt' : Nat.card ↥(W ⊓ U) < 32 := not_le.mp hlt
    have : W.relIndex U * Nat.card ↥(W ⊓ U) ≤ 8 * 31 := Nat.mul_le_mul h8 (by omega)
    omega
  have hcent : ∀ u ∈ U, W ⊓ U ≤ centralizer ({u} : Set G) := by
    intro u hu x hx
    rw [mem_centralizer_singleton_iff]
    exact (L34.comm_of_isElemAbelian hUel hu hx.2).symm
  have hUY : ∀ u ∈ U, u ∈ W ⊔ zpowers t := by
    intro u hu
    by_contra hnY
    have h1 := hR2 u (hgS hu) hnY
    have h2 : Nat.card ↥(W ⊓ U) ≤ Nat.card ↥(W ⊓ centralizer ({u} : Set G)) :=
      Subgroup.card_le_of_le (le_inf inf_le_left (hcent u hu))
    omega
  have hUW : U ≤ W := by
    intro u hu
    by_contra huW
    have hle : W ⊓ U ≤ W ⊓ centralizer ({t} : Set G) :=
      (le_inf inf_le_left (hcent u hu)).trans
        (inf_centralizer_le_of_mem_sup hW (hSN htS) ht2 (hUY u hu) huW)
    have h4 := Subgroup.card_le_of_le (hCt ▸ hle)
    omega
  exact Subgroup.eq_of_le_of_card_ge hUW (by rw [hcardU, hcardW])

theorem stronglyClosed_of_cor4 {G : Type} [Group G] [Finite G] (T : Sylow 2 G) (W : Subgroup G)
    (hWT : W ≤ (T : Subgroup G)) (hW : IsElemAbelian 2 W)
    (hweak : ∀ h : G, rightConjugate W h ≤ (T : Subgroup G) → rightConjugate W h = W)
    (R : ℕ) (hR : ∀ B : Subgroup G, B ≤ (T : Subgroup G) → IsElemAbelian 2 B → W.relIndex B ≤ R)
    (hlow : ∀ x ∈ (T : Subgroup G), x ∉ W → x * x = 1 → R < Nat.card ↥⁅W, Subgroup.zpowers x⁆) :
    ∀ a ∈ W, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ W := by
  intro a ha g hg
  by_contra hna
  obtain ⟨U, hUV, h, hUP, hnle, hcomm⟩ :=
    goldschmidt_theorem_four_holds G T W hWT hW hweak ⟨a, ha, g, hg, hna⟩
  have hU : IsElemAbelian 2 U :=
    L34.isElemAbelian_of_forall
      (fun x hx y hy => L34.comm_of_isElemAbelian hW (hUV hx) (hUV hy))
      (fun x hx => hW.2 x (hUV hx))
  have hBel : IsElemAbelian 2 (rightConjugate U h) :=
    L34.isElemAbelian_map _ hU
  obtain ⟨w, hwB, hwW⟩ := Set.not_subset.mp hnle
  have h1 := hcomm w hwB
  have h2 := hR _ hUP hBel
  have hw2 : w * w = 1 := by
    have := hBel.2 w hwB
    simpa [sq] using this
  have h3 := hlow w (hUP hwB) hwW hw2
  omega

theorem exists_mem_normalizer_not_mem {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup G} (hS : IsPGroup p S) (hTS : T < S) :
    ∃ x ∈ S, x ∈ normalizer (T : Set G) ∧ x ∉ T := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hTS.not_ge (subgroupOf_eq_top.mp h)
  obtain ⟨x, hx, hxT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hTS.le] at hx
  exact ⟨x, x.2, hx, hxT⟩

theorem isSylowOf_top_of_normalizer_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M T : Subgroup G} (hT : IsSylowOf p T M) (hN : normalizer (T : Set G) ≤ M) :
    IsSylowOf p T ⊤ := by
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hST : (S : Subgroup G) ≤ T := by
    by_contra hne
    obtain ⟨x, hxS, hxN, hxT⟩ :=
      exists_mem_normalizer_not_mem S.isPGroup' (lt_of_le_not_ge hTS hne)
    have hQ := hT.eq_of_le (le_inf hTS Subgroup.le_normalizer) (inf_le_right.trans hN)
      S.isPGroup'.to_inf_left
    exact hxT (hQ ▸ ⟨hxS, hxN⟩)
  rw [isSylowOf_iff]
  refine ⟨le_top, hT.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, le_antisymm hTS hST]
  exact S.not_dvd_index

theorem isSylowOf_top_of_weakly_closed {G : Type} [Group G] [Finite G] {S W : Subgroup G}
    (hS : IsSylowOf 2 S (normalizer (W : Set G))) (hWS : W ≤ S)
    (hweak : ∀ g : G, rightConjugate W g ≤ S → rightConjugate W g = W) :
    IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (S : Set G) ≤ normalizer (W : Set G) := by
    intro g hg
    have hle : rightConjugate W g ≤ S := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      exact (mem_normalizer_iff.mp hg x).mpr (hWS hx)
    exact (rightConjugate_eq_self_iff W g).mp (hweak g hle)
  exact isSylowOf_top_of_normalizer_le hS hN

theorem exists_sylow_eq_of_isSylowOf_top {H : Type} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsSylowOf 2 P ⊤) : ∃ S : Sylow 2 H, (S : Subgroup H) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.card_eq
  rw [Subgroup.card_top] at h
  exact ⟨Sylow.ofCard P h, Sylow.coe_ofCard _ _⟩

theorem seitz26_core {G : Type} [Group G] [Finite G] {S W V₁ : Subgroup G} {t : G}
    (hS : IsSylowOf 2 S (normalizer (W : Set G))) (hWS : W ≤ S) (hW : IsElemAbelian 2 W)
    (hcardW : Nat.card W = 2 ^ 8) (htS : t ∈ S) (ht2 : t * t = 1) (htW : t ∉ W)
    (hCt : W ⊓ centralizer ({t} : Set G) = V₁) (hcardV₁ : Nat.card V₁ = 16)
    (hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers t → Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ 16)
    (hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 8)
    (hA : ∀ (T : Sylow 2 G) (A : Subgroup G), A ≠ ⊥ → A ≤ (T : Subgroup G) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) →
      ∀ x ∈ (T : Subgroup G), x * x = 1 → x ∈ A) :
    False := by
  have hSN : S ≤ normalizer (W : Set G) := hS.le
  have hweak := weak_closure_of_actions hSN hW hcardW htS ht2 hCt hcardV₁ hR2 hR1
  obtain ⟨T, hT⟩ := exists_sylow_eq_of_isSylowOf_top (isSylowOf_top_of_weakly_closed hS hWS hweak)
  subst hT
  have hlow : ∀ x ∈ (T : Subgroup G), x ∉ W → x * x = 1 → 8 < Nat.card ↥⁅W, zpowers x⁆ := by
    intro x hxT hxW hx2
    have hcard := card_commutator_mul_card_centralizer hW (hSN hxT) hx2
    have hC16 : Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 16 := by
      by_cases hxY : x ∈ W ⊔ zpowers t
      · have hle := inf_centralizer_le_of_mem_sup hW (hSN htS) ht2 hxY hxW
        have := Subgroup.card_le_of_le (hCt ▸ hle)
        omega
      · exact hR2 x hxT hxY
    rw [hcardW] at hcard
    by_contra hle
    have h1 : Nat.card ↥⁅W, zpowers x⁆ ≤ 8 := not_lt.mp hle
    have := Nat.mul_le_mul h1 hC16
    omega
  have hclosed := stronglyClosed_of_cor4 T W hWS hW hweak 8
    (fun B hB hBel => hR1 B hB hBel) hlow
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h] at hcardW
    simp at hcardW
  have hAb : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    L34.comm_of_isElemAbelian hW ha hb
  exact htW (hA T W hWne hWS hAb hclosed t htS ht2)

end CFSG.OddStandard.Seitz77.Sec26
