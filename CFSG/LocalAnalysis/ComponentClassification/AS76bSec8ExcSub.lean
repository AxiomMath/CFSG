module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ComponentClassification.AS76b
open scoped commutatorElement

theorem commutator_le_admResidual_of_isPGroup {G : Type*} [Group G] {X P : Subgroup G}
    (hPX : P ≤ X) (hP : IsPGroup 2 P) : ⁅P, P⁆ ≤ admResidual X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sInf ?_
  rintro Y ⟨-, hN, -, hab⟩
  let φ : ↥P →* ↥X ⧸ Y.subgroupOf X := (QuotientGroup.mk' (Y.subgroupOf X)).comp (inclusion hPX)
  have hφ : IsPGroup 2 φ.range := hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hφ.exists_le_sylow
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmem : ∀ x (hx : x ∈ P), φ ⟨x, hx⟩ ∈ (S : Subgroup (↥X ⧸ Y.subgroupOf X)) :=
    fun x hx => hS ⟨⟨x, hx⟩, rfl⟩
  have hcomm : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ :=
    congrArg Subtype.val ((hab S).is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
  have h1 : φ ⁅(⟨a, ha⟩ : ↥P), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have h2 : (inclusion hPX ⁅(⟨a, ha⟩ : ↥P), ⟨b, hb⟩⁆ : ↥X) ∈ Y.subgroupOf X := by
    rw [← QuotientGroup.ker_mk' (Y.subgroupOf X)]
    exact h1
  simpa [commutatorElement_def] using mem_subgroupOf.mp h2

theorem conj_mem_admResidual {G : Type*} [Group G] {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ admResidual X) : x * y * x⁻¹ ∈ admResidual X := by
  refine mem_sInf.2 fun Y hY => ?_
  have hyY : y ∈ Y := mem_sInf.1 hy Y hY
  obtain ⟨hYX, hN, -⟩ := hY
  have h1 := hN.conj_mem ⟨y, hYX hyY⟩ (mem_subgroupOf.2 hyY) ⟨x, hx⟩
  exact mem_subgroupOf.1 h1

end CFSG.ComponentClassification.RankTwoExceptional

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] {Γ : Subgroup X}

theorem mem_cent_iff {x c : Γ} : c ∈ cent x ↔ (c : X) * x = x * c := by
  rw [cent, mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem map_cent (x : Γ) : (cent x).map Γ.subtype = Γ ⊓ centralizer {(x : X)} := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2 (mem_cent_iff.1 hc)⟩
  · intro hg
    obtain ⟨hgΓ, hgc⟩ := mem_inf.1 hg
    exact ⟨⟨g, hgΓ⟩, mem_cent_iff.2 (mem_centralizer_singleton_iff.1 hgc), rfl⟩

noncomputable def centEquiv (x : Γ) : ↥(cent x) ≃* ↥(Γ ⊓ centralizer {(x : X)}) :=
  ((cent x).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_cent x))

theorem charTwo_of_inf (x : Γ) (h : CFSG.IsCharacteristicP 2 ↥(Γ ⊓ centralizer {(x : X)})) :
    CharTwo x :=
  CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv (centEquiv x).symm h

theorem centreData_of_inf {x : X} (hx : x ∈ Γ) {Zx : Subgroup X} (hmem : x ∈ Zx) (hne : x ≠ 1)
    (hcomm : ∀ a ∈ Zx, ∀ b ∈ Zx, a * b = b * a) (hsq : ∀ a ∈ Zx, a * a = 1)
    (hcent : ∀ z ∈ Zx, ∀ c ∈ Γ, c * x = x * c → z * c = c * z)
    (hinv : ∀ w ∈ Γ, w * x = x * w → (∀ c ∈ Γ, c * x = x * c → w * c = c * w) → w * w = 1 →
      w ∈ Zx) :
    CentreData (⟨x, hx⟩ : Γ) (Zx.subgroupOf Γ) where
  mem := mem_subgroupOf.2 hmem
  ne_one h := hne (congrArg Subtype.val h)
  elem := ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext
      (hcomm _ (mem_subgroupOf.1 a.2) _ (mem_subgroupOf.1 b.2)))⟩⟩,
    fun a ha => Subtype.ext (by
      rw [Subgroup.coe_pow, sq]
      exact hsq _ (mem_subgroupOf.1 ha))⟩
  le_cent z hz := mem_cent_iff.2 (hcent _ (mem_subgroupOf.1 hz) x hx rfl)
  commute z hz c hc := Subtype.ext (hcent _ (mem_subgroupOf.1 hz) _ c.2 (mem_cent_iff.1 hc))
  centre_inv w hw hwc hw2 := mem_subgroupOf.2 (hinv _ w.2 (mem_cent_iff.1 hw)
    (fun c hc hcx => congrArg Subtype.val (hwc ⟨c, hc⟩ (mem_cent_iff.2 hcx)))
    (congrArg Subtype.val hw2))

theorem sylowData_of_inf {x : X} (hx : x ∈ Γ) {Zx : Subgroup X}
    (h : ∀ w ∈ Γ, w * x = x * w → (∀ b ∈ Γ, b * x * b⁻¹ * x = x * (b * x * b⁻¹) →
      w * (b * x * b⁻¹) = b * x * b⁻¹ * w) → (∃ k : ℕ, w ^ 2 ^ k = 1) → w ∈ Zx) :
    SylowData (⟨x, hx⟩ : Γ) (Zx.subgroupOf Γ) := by
  intro w hw hwc hw2
  refine mem_subgroupOf.2 (h _ w.2 (mem_cent_iff.1 hw) (fun b hb hbx => ?_) ?_)
  · have h1 := hwc ⟨b, hb⟩ (mem_cent_iff.2 hbx)
    exact mem_cent_iff.1 h1
  · obtain ⟨k, hk⟩ := hw2
    exact ⟨k, by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩

section Scalar

variable {K : Type*} [Field K] {ζ : K → X}

theorem pow_conj_of_scalar {u : X} {l : K} (hact : ∀ c, u * ζ c * u⁻¹ = ζ (l * c)) (k : ℕ)
    (c : K) : u ^ k * ζ c * (u ^ k)⁻¹ = ζ (l ^ k * c) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    calc u ^ (k + 1) * ζ c * (u ^ (k + 1))⁻¹ = u ^ k * (u * ζ c * u⁻¹) * (u ^ k)⁻¹ := by group
      _ = ζ (l ^ (k + 1) * c) := by rw [hact, ih, pow_succ, mul_assoc]

theorem regular_of_scalar (hζ : Function.Injective ζ) (hζ0 : ζ 0 = 1) {Zx : Subgroup X}
    (hZx : ∀ g, g ∈ Zx ↔ ∃ c, ζ c = g) (hZΓ : Zx ≤ Γ) {u : X} (hu : u ∈ Γ) {l : K}
    (hl : ∀ c : K, c ≠ 0 → ∃ k : ℕ, l ^ k = c) (hact : ∀ c, u * ζ c * u⁻¹ = ζ (l * c))
    (hodd : Odd (orderOf u)) (hcent : ∀ a ∈ Γ, a * ζ 1 = ζ 1 * a → ∀ c, a * ζ c = ζ c * a) :
    Regular (Zx.subgroupOf Γ) ⟨u, hu⟩ := by
  have hpow := pow_conj_of_scalar hact
  have hne : ∀ c, ζ c = 1 → c = 0 := fun c h => hζ (h.trans hζ0.symm)
  have hl0 : l ≠ 0 := by
    intro h
    have h1 := hact 1
    rw [h, zero_mul, hζ0] at h1
    have h2 : ζ 1 = 1 := by
      calc ζ 1 = u⁻¹ * (u * ζ 1 * u⁻¹) * u := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (hne 1 h2)
  have hζmem : ∀ c, ζ c ∈ Zx := fun c => (hZx _).2 ⟨c, rfl⟩
  have hN : ∀ a : Γ, a ∈ normalizer (Zx.subgroupOf Γ : Set Γ) →
      ∀ c, ∃ c', (a : X) * ζ c * (a : X)⁻¹ = ζ c' := by
    intro a ha c
    have h1 := (mem_normalizer_iff.1 ha ⟨ζ c, hZΓ (hζmem c)⟩).1 (mem_subgroupOf.2 (hζmem c))
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    obtain ⟨c', hc'⟩ := (hZx _).1 h1
    exact ⟨c', hc'.symm⟩
  have hC : ∀ a : Γ, (∀ c, (a : X) * ζ c = ζ c * a) →
      a ∈ centralizer (Zx.subgroupOf Γ : Set Γ) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨c, hc⟩ := (hZx g).1 (mem_subgroupOf.1 hg)
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ha c])
  have hyN : (⟨u, hu⟩ : Γ) ∈ normalizer (Zx.subgroupOf Γ : Set Γ) := by
    rw [mem_normalizer_iff]
    intro g
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    show (g : X) ∈ Zx ↔ u * g * u⁻¹ ∈ Zx
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := (hZx _).1 hg
      rw [← hc, hact]
      exact hζmem _
    · intro hg
      obtain ⟨c, hc⟩ := (hZx _).1 hg
      have h1 := hact (l⁻¹ * c)
      rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul, hc] at h1
      have h2 : (g : X) = ζ (l⁻¹ * c) := by
        calc (g : X) = u⁻¹ * (u * g * u⁻¹) * u := by group
          _ = u⁻¹ * (u * ζ (l⁻¹ * c) * u⁻¹) * u := by rw [h1]
          _ = ζ (l⁻¹ * c) := by group
      rw [h2]
      exact hζmem _
  have hcyc : ∀ a : Γ, a ∈ normalizer (Zx.subgroupOf Γ : Set Γ) → ∃ k : ℕ,
      ∀ c, ((u ^ k)⁻¹ * a) * ζ c = ζ c * ((u ^ k)⁻¹ * a) := by
    intro a ha
    obtain ⟨c, hc⟩ := hN a ha 1
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, hζ0] at hc
      have h2 : ζ 1 = 1 := by
        calc ζ 1 = (a : X)⁻¹ * ((a : X) * ζ 1 * (a : X)⁻¹) * a := by group
          _ = 1 := by rw [hc]; group
      exact one_ne_zero (hne 1 h2)
    obtain ⟨k, hk⟩ := hl c hc0
    refine ⟨k, hcent _ (mul_mem (inv_mem (pow_mem hu k)) a.2) ?_⟩
    have h2 := hpow k 1
    rw [mul_one, hk, ← hc] at h2
    calc (u ^ k)⁻¹ * a * ζ 1 = (u ^ k)⁻¹ * ((a : X) * ζ 1 * (a : X)⁻¹) * a := by group
      _ = (u ^ k)⁻¹ * (u ^ k * ζ 1 * (u ^ k)⁻¹) * a := by rw [h2]
      _ = ζ 1 * ((u ^ k)⁻¹ * a) := by group
  refine ⟨hyN, by rw [Subgroup.orderOf_mk]; exact hodd, ?_, ?_, ?_⟩
  · intro j hj hj1 j' hj' hj'1
    obtain ⟨c, hc⟩ := (hZx _).1 (mem_subgroupOf.1 hj)
    obtain ⟨c', hc'⟩ := (hZx _).1 (mem_subgroupOf.1 hj')
    have hc0 : c ≠ 0 := fun h => hj1 (Subtype.ext (by rw [← hc, h, hζ0, Subgroup.coe_one]))
    have hc'0 : c' ≠ 0 := fun h => hj'1 (Subtype.ext (by rw [← hc', h, hζ0, Subgroup.coe_one]))
    obtain ⟨k, hk⟩ := hl (c' / c) (div_ne_zero hc'0 hc0)
    refine ⟨⟨u, hu⟩ ^ k, pow_mem hyN k, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, ← hc, hpow, hk,
      div_mul_cancel₀ _ hc0, hc']
  · intro a ha j hj hj1 haj
    obtain ⟨k, hk⟩ := hcyc a ha
    obtain ⟨c, hc⟩ := (hZx _).1 (mem_subgroupOf.1 hj)
    have hc0 : c ≠ 0 := fun h => hj1 (Subtype.ext (by rw [← hc, h, hζ0, Subgroup.coe_one]))
    have haj' : (a : X) * ζ c * (a : X)⁻¹ = ζ c := by
      have := congrArg Subtype.val haj
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hc] at this
    have hlk : l ^ k = 1 := by
      have h1 : u ^ k * ζ c * (u ^ k)⁻¹ = ζ c := by
        have e : (u ^ k)⁻¹ * a * ζ c = ζ c * ((u ^ k)⁻¹ * a) := hk c
        calc u ^ k * ζ c * (u ^ k)⁻¹ =
            u ^ k * (ζ c * ((u ^ k)⁻¹ * a)) * ((u ^ k)⁻¹ * (a : X))⁻¹ * (u ^ k)⁻¹ := by group
          _ = u ^ k * ((u ^ k)⁻¹ * a * ζ c) * ((u ^ k)⁻¹ * (a : X))⁻¹ * (u ^ k)⁻¹ := by
            rw [e]
          _ = (a : X) * ζ c * (a : X)⁻¹ := by group
          _ = ζ c := haj'
      rw [hpow] at h1
      have h2 := hζ h1
      have h3 : (l ^ k - 1) * c = 0 := by rw [sub_mul, one_mul, h2, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hc0)
    refine hC a fun c' => ?_
    have h1 : u ^ k * ζ c' = ζ c' * u ^ k := by
      have := hpow k c'
      rw [hlk, one_mul] at this
      calc u ^ k * ζ c' = u ^ k * ζ c' * (u ^ k)⁻¹ * u ^ k := by group
        _ = ζ c' * u ^ k := by rw [this]
    calc (a : X) * ζ c' = u ^ k * (((u ^ k)⁻¹ * a) * ζ c') := by group
      _ = u ^ k * (ζ c' * ((u ^ k)⁻¹ * a)) := by rw [hk c']
      _ = (u ^ k * ζ c') * ((u ^ k)⁻¹ * a) := by group
      _ = ζ c' * u ^ k * ((u ^ k)⁻¹ * a) := by rw [h1]
      _ = ζ c' * a := by group
  · intro a ha
    obtain ⟨k, hk⟩ := hcyc a ha
    refine ⟨k, hC _ fun c => ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hk c

end Scalar

theorem commute_of_simple {R : Subgroup X} [IsSimpleGroup R] {S : Set X}
    (hS : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) {s₀ : X} (hs₀ : s₀ ∈ S) (hs₀R : s₀ ∈ R)
    (hs₀1 : s₀ ≠ 1) {w : X} (hw : ∀ s ∈ S, s ∈ R → w * s = s * w) : ∀ r ∈ R, w * r = r * w := by
  set N := closure (S ∩ (R : Set X)) with hNdef
  have hNR : N ≤ R := closure_le _ |>.2 Set.inter_subset_right
  have hconj : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    intro r hr n hn
    induction hn using closure_induction with
    | mem s hs => exact subset_closure ⟨hS r hr s hs.1, mul_mem (mul_mem hr hs.2) (inv_mem hr)⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hnorm : (N.subgroupOf R).Normal := by
    refine ⟨fun n hn r => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    simpa using hconj r r.2 n hn
  have htop : N.subgroupOf R = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf R) with h | h
    · exfalso
      have h1 : (⟨s₀, hs₀R⟩ : R) ∈ N.subgroupOf R :=
        mem_subgroupOf.2 (subset_closure ⟨hs₀, hs₀R⟩)
      rw [h, mem_bot] at h1
      exact hs₀1 (congrArg Subtype.val h1)
    · exact h
  have hNw : N ≤ centralizer ({w} : Set X) := by
    refine (closure_le _).2 fun s hs => ?_
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (hw s hs.1 hs.2).symm
  intro r hr
  have h1 : (⟨r, hr⟩ : R) ∈ N.subgroupOf R := by rw [htop]; trivial
  exact (mem_centralizer_singleton_iff.1 (hNw (mem_subgroupOf.1 h1))).symm

theorem commutator_subgroupOf_of_perfect {P : Subgroup X} (hPΓ : P ≤ Γ) (hP : ⁅P, P⁆ = P) :
    ⁅P.subgroupOf Γ, P.subgroupOf Γ⁆ = P.subgroupOf Γ := by
  apply map_injective Γ.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hPΓ, hP]

theorem conj_mem_commutator_self {H : Subgroup X} {x y : X} (hx : x ∈ H) (hy : y ∈ ⁅H, H⁆) :
    x * y * x⁻¹ ∈ ⁅H, H⁆ := by
  rw [Subgroup.commutator_def] at hy ⊢
  induction hy using closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    refine subset_closure ⟨x * a * x⁻¹, mul_mem (mul_mem hx ha) (inv_mem hx), x * b * x⁻¹,
      mul_mem (mul_mem hx hb) (inv_mem hx), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem commutator_conj_of_scalar {K : Type*} [Field K] {ζ : K → X} {g g' : X} {l l' : K}
    (hl : l ≠ 0) (hl' : l' ≠ 0) (hg : ∀ c, g * ζ c * g⁻¹ = ζ (l * c))
    (hg' : ∀ c, g' * ζ c * g'⁻¹ = ζ (l' * c)) : ⁅g, g'⁆ * ζ 1 = ζ 1 * ⁅g, g'⁆ := by
  have hinv : ∀ {h : X} {μ : K}, μ ≠ 0 → (∀ c, h * ζ c * h⁻¹ = ζ (μ * c)) →
      ∀ c, h⁻¹ * ζ c * h = ζ (μ⁻¹ * c) := by
    intro h μ hμ hh c
    have h1 := hh (μ⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul] at h1
    calc h⁻¹ * ζ c * h = h⁻¹ * (h * ζ (μ⁻¹ * c) * h⁻¹) * h := by rw [h1]
      _ = ζ (μ⁻¹ * c) := by group
  have e : ⁅g, g'⁆ * ζ 1 * ⁅g, g'⁆⁻¹ = ζ 1 := by
    rw [commutatorElement_def]
    calc g * g' * g⁻¹ * g'⁻¹ * ζ 1 * (g * g' * g⁻¹ * g'⁻¹)⁻¹ =
        g * (g' * (g⁻¹ * (g'⁻¹ * ζ 1 * g') * g) * g'⁻¹) * g⁻¹ := by group
      _ = ζ (l * (l' * (l⁻¹ * (l'⁻¹ * 1)))) := by rw [hinv hl' hg', hinv hl hg, hg', hg]
      _ = ζ 1 := by
        congr 1
        field_simp
  calc ⁅g, g'⁆ * ζ 1 = ⁅g, g'⁆ * ζ 1 * ⁅g, g'⁆⁻¹ * ⁅g, g'⁆ := by group
    _ = ζ 1 * ⁅g, g'⁆ := by rw [e]

theorem center_eq_bot_of_simple {R : Type*} [Group R] [IsSimpleGroup R]
    (h : ∃ x y : R, x * y ≠ y * x) : center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center R) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    have hy : y ∈ center R := by rw [h1]; trivial
    exact hxy (mem_center_iff.1 hy x)

theorem commutator_eq_self_of_simple {R : Subgroup X} [IsSimpleGroup R]
    (h : ∃ x y : R, x * y ≠ y * x) : ⁅R, R⁆ = R := by
  have htop : commutator R = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with h1 | h1
    · exfalso
      obtain ⟨x, y, hxy⟩ := h
      apply hxy
      have h2 : ⁅x, y⁆ ∈ commutator R := commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    · exact h1
  rw [← map_subtype_commutator, htop, ← MonoidHom.range_eq_map, range_subtype]

theorem le_normalizer_of_normal_subgroupOf {N H R : Subgroup X} (hN : (N.subgroupOf H).Normal)
    (hNH : N ≤ H) (hRH : R ≤ H) : R ≤ normalizer (N : Set X) := by
  intro r hr
  rw [mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have h1 := hN.conj_mem ⟨v, hNH hv⟩ (mem_subgroupOf.2 hv) ⟨r, hRH hr⟩
    exact mem_subgroupOf.1 h1
  · intro hv
    have h1 := hN.conj_mem ⟨r * v * r⁻¹, hNH hv⟩ (mem_subgroupOf.2 hv) ⟨r, hRH hr⟩⁻¹
    have h2 := mem_subgroupOf.1 h1
    have e : ((⟨r, hRH hr⟩⁻¹ * ⟨r * v * r⁻¹, hNH hv⟩ * (⟨r, hRH hr⟩⁻¹)⁻¹ : H) : X) = v := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at h2

theorem mem_of_commute_of_sup {V R : Subgroup X} (hRV : R ≤ normalizer (V : Set X))
    (hVR : V ⊓ R = ⊥) (hZR : center R = ⊥) {w : X} (hw : w ∈ V ⊔ R)
    (hcomm : ∀ r ∈ R, w * r = r * w) : w ∈ V := by
  have hw' : w ∈ ((R ⊔ V : Subgroup X) : Set X) := by rw [sup_comm]; exact hw
  rw [coe_mul_of_left_le_normalizer_right R V hRV] at hw'
  obtain ⟨r, hr, v, hv, hrv⟩ := hw'
  have hrv' : r * v = w := hrv
  have hrZ : (⟨r, hr⟩ : R) ∈ center R := by
    rw [mem_center_iff]
    intro r'
    obtain ⟨s, hs⟩ := r'
    have h1 := hcomm s hs
    rw [← hrv'] at h1
    have hR : (s * r)⁻¹ * (r * s) ∈ R := mul_mem (inv_mem (mul_mem hs hr)) (mul_mem hr hs)
    have hV : (s * r)⁻¹ * (r * s) ∈ V := by
      have e : (s * r)⁻¹ * (r * s) = v * (s⁻¹ * v⁻¹ * s) := by
        calc (s * r)⁻¹ * (r * s) = (s * r)⁻¹ * (r * v * s) * (s⁻¹ * v⁻¹ * s) := by group
          _ = (s * r)⁻¹ * (s * (r * v)) * (s⁻¹ * v⁻¹ * s) := by rw [h1]
          _ = v * (s⁻¹ * v⁻¹ * s) := by group
      rw [e]
      refine mul_mem hv ?_
      have h2 := (mem_normalizer_iff.1 (hRV (inv_mem hs)) v⁻¹).1 (inv_mem hv)
      rwa [inv_inv] at h2
    have h3 : (s * r)⁻¹ * (r * s) ∈ V ⊓ R := mem_inf.2 ⟨hV, hR⟩
    rw [hVR, mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  rw [hZR, mem_bot] at hrZ
  have hr1 : r = 1 := congrArg Subtype.val hrZ
  rw [← hrv', hr1, one_mul]
  exact hv

end CFSG.ComponentClassification.RankTwoExceptional.Exc
