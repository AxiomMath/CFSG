module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section Generic

variable {G : Type} [Group G]

@[expose] def conjSub (δ : G) (W : Subgroup G) : Subgroup G := W.map (MulAut.conj δ).toMonoidHom

theorem mem_conjSub_iff {δ x : G} {W : Subgroup G} : x ∈ conjSub δ W ↔ δ⁻¹ * x * δ ∈ W :=
  mem_map_conj_iff W δ x

structure Delta (S₁ T : Subgroup G) (δ : G) : Prop where
  mem : δ ∈ T
  norm : ∀ x, x ∈ S₁ ↔ δ * x * δ⁻¹ ∈ S₁
  not_mem : δ ∉ S₁
  sq_mem : δ * δ ∈ S₁

end Generic

section Step

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

theorem mem_S₁_of_mem_normalizer [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hST : S₁ ≤ T) {x : G}
    (hxT : x ∈ T) (hxN : x ∈ normalizer (W : Set G)) : x ∈ S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.sylow_S₁.eq_of_le (Q := T ⊓ normalizer (W : Set G))
    (le_inf hST S.sylow_S₁.le) inf_le_right (hT.to_inf_left)
  rw [← h]
  exact ⟨hxT, hxN⟩

variable {T : Subgroup G} {δ : G}

theorem conjSub_le_S₁ (D : Delta S₁ T δ) : conjSub δ W ≤ S₁ := fun x hx =>
  have h1 : δ⁻¹ * x * δ ∈ W := mem_conjSub_iff.1 hx
  have h2 : δ * (δ⁻¹ * x * δ) * δ⁻¹ ∈ S₁ := (D.norm _).1 (S.W_le_S₁ h1)
  by simpa [mul_assoc] using h2

theorem card_conjSub : Nat.card (conjSub δ W) = 2 ^ 8 := by
  rw [conjSub, card_map_conj, S.card_W]

theorem elem_conjSub :
    (∀ x ∈ conjSub δ W, ∀ y ∈ conjSub δ W, x * y = y * x) ∧
      ∀ x ∈ conjSub δ W, x * x = 1 :=
  isElemAbelian_map_conj (fun _ ha _ hb => S.comm_of_mem_W ha hb)
    (fun _ ha => S.mul_self_of_mem_W ha) δ

theorem conjSub_ne [Finite G] (hT : IsPGroup 2 T) (hST : S₁ ≤ T) (D : Delta S₁ T δ) :
    conjSub δ W ≠ W := by
  intro heq
  apply D.not_mem
  refine S.mem_S₁_of_mem_normalizer hT hST D.mem ?_
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : δ * y * δ⁻¹ ∈ conjSub δ W := by
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using hy
    rwa [heq] at this
  · intro hy
    rw [← heq, mem_conjSub_iff] at hy
    simpa [mul_assoc] using hy


theorem φ_one : φ 1 = 1 := by
  have h := S.φ_mul 1 S₁.one_mem 1 S₁.one_mem
  rw [mul_one] at h
  simpa using h

theorem conjSub_le_S₀ [Finite G] (D : Delta S₁ T δ) : conjSub δ W ≤ S₀ := by
  by_contra hnot
  obtain ⟨s, hsW', hsS₀⟩ := Set.not_subset.mp hnot
  have hW'S₁ : conjSub δ W ≤ S₁ := S.conjSub_le_S₁ D
  obtain ⟨hab, hsq⟩ := S.elem_conjSub (δ := δ)
  have hcard : Nat.card (conjSub δ W) = 2 ^ 8 := S.card_conjSub
  have hsS₁ : s ∈ S₁ := hW'S₁ hsW'
  have hφne : φ s ≠ 1 := fun h => hsS₀ ((S.φ_eq_one_iff s hsS₁).1 h)
  have hi : 128 ≤ Nat.card ↥(conjSub δ W ⊓ S₀) := by
    have hmul : ∀ x ∈ conjSub δ W, ∀ y ∈ conjSub δ W, φ (x * y) = φ x * φ y := fun x hx y hy =>
      S.φ_mul x (hW'S₁ hx) y (hW'S₁ hy)
    have him : (φ '' (conjSub δ W : Set G)).ncard ≤ 2 := by
      have hfin : Finite (RingAut F) := ringAut_finite
      have hsub : φ '' (conjSub δ W : Set G) ⊆ {a : RingAut F | a * a = 1} := by
        rintro _ ⟨x, hx, rfl⟩
        show φ x * φ x = 1
        rw [← S.φ_mul x (hW'S₁ hx) x (hW'S₁ hx), hsq x hx, S.φ_one]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ringAut_card_sq_eq_one_le S.card_F)
    have h := le_card_fiber_of_partial_hom (conjSub δ W) φ hmul (a := 256) (b := 2)
      (by rw [hcard]; norm_num) him
    have hfib : Nat.card {x : G // x ∈ conjSub δ W ∧ φ x = 1} =
        Nat.card ↥(conjSub δ W ⊓ S₀) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [mem_inf]
      exact and_congr_right fun hx => S.φ_eq_one_iff x (hW'S₁ hx)
    rw [hfib] at h
    omega
  have hii : Nat.card ↥(conjSub δ W ⊓ S₀) ≤ 16 * 4 := by
    obtain ⟨l, -, hl⟩ := S.conj_κ s hsS₁
    have hmul : ∀ x ∈ conjSub δ W ⊓ S₀, ∀ y ∈ conjSub δ W ⊓ S₀,
        Multiplicative.ofAdd (κ (x * y)) =
          Multiplicative.ofAdd (κ x) * Multiplicative.ofAdd (κ y) :=
      fun x hx y hy => by rw [S.κ_add x hx.2 y hy.2, ofAdd_add]
    refine card_le_mul_of_partial_hom (conjSub δ W ⊓ S₀) (fun z => Multiplicative.ofAdd (κ z))
      hmul (a := 16) (b := 4) ?_ ?_
    · refine le_trans (Nat.card_le_card_of_injective
        (fun x => (⟨x.1, ?_, ?_⟩ : ↥(W ⊓ centralizer ({s} : Set G)))) ?_)
        (S.card_fix_le s hsS₁ hsS₀)
      · obtain ⟨x, hx, hκx⟩ := x
        exact (S.κ_eq_zero_iff x hx.2).1 (ofAdd_eq_one.mp hκx)
      · obtain ⟨x, hx, -⟩ := x
        exact mem_centralizer_singleton_iff.mpr (hab x hx.1 s hsW')
      · intro a b hab'
        have h1 := congrArg (fun z : ↥(W ⊓ centralizer ({s} : Set G)) => (z : G)) hab'
        exact Subtype.ext h1
    · have hsub : (fun z => Multiplicative.ofAdd (κ z)) ''
          ((conjSub δ W ⊓ S₀ : Subgroup G) : Set G) ⊆
          Multiplicative.ofAdd '' {b : F | l * φ s b = b} := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨κ u, ?_, rfl⟩
        have hus : s * u * s⁻¹ = u := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hab s hsW' u hu.1
        have h2 := hl u hu.2
        rw [hus] at h2
        exact h2.symm
      calc _ ≤ (Multiplicative.ofAdd '' {b : F | l * φ s b = b}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Set.ncard {b : F | l * φ s b = b} :=
            Set.ncard_image_of_injective _ Multiplicative.ofAdd.injective
        _ ≤ 4 := by
            rw [← Nat.card_coe_set_eq]
            exact card_fix_semilinear_le S.card_F (φ s) hφne l
  omega


theorem inf_conjSub_eq_W₀ [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) (hST : S₁ ≤ T)
    (D : Delta S₁ T δ) :
    W ⊓ conjSub δ W = W₀ ∧ ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b := by
  have hle : conjSub δ W ≤ S₀ := S.conjSub_le_S₀ D
  have hcard : Nat.card (conjSub δ W) = 2 ^ 8 := S.card_conjSub
  obtain ⟨hab, hsq⟩ := S.elem_conjSub (δ := δ)
  have hnot : ¬ conjSub δ W ≤ W := fun hle' =>
    S.conjSub_ne hT hST D (Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard, S.card_W]))
  obtain ⟨s, hsW', hsW⟩ := Set.not_subset.mp hnot
  have hsS₀ : s ∈ S₀ := hle hsW'
  have hfix := S.inf_centralizer_eq_W₀ hsS₀ hsW
  have hWW' : W ⊓ conjSub δ W ≤ W₀ := by
    rw [← hfix]
    exact le_inf inf_le_left fun x hx => mem_centralizer_singleton_iff.mpr (hab x hx.2 s hsW')
  have hcardWW' : Nat.card ↥(W ⊓ conjSub δ W) ≤ 16 :=
    (Subgroup.card_le_of_le hWW').trans S.card_W₀.le
  have hmul : ∀ x ∈ conjSub δ W, ∀ y ∈ conjSub δ W,
      Multiplicative.ofAdd (κ (x * y)) = Multiplicative.ofAdd (κ x) * Multiplicative.ofAdd (κ y) :=
    fun x hx y hy => by rw [S.κ_add x (hle hx) y (hle hy), ofAdd_add]
  have hcnt := card_eq_card_fiber_mul_ncard_image (conjSub δ W)
    (fun z => Multiplicative.ofAdd (κ z)) hmul
  have hfib : Nat.card {x : G // x ∈ conjSub δ W ∧ Multiplicative.ofAdd (κ x) = 1} =
      Nat.card ↥(W ⊓ conjSub δ W) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [mem_inf, ofAdd_eq_one]
    constructor
    · rintro ⟨hx, h0⟩
      exact ⟨(S.κ_eq_zero_iff x (hle hx)).1 h0, hx⟩
    · rintro ⟨hxW, hx⟩
      exact ⟨hx, (S.κ_eq_zero_iff x (hle hx)).2 hxW⟩
  have hF : Nat.card (Multiplicative F) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, S.card_F]
  have himg : ((fun z => Multiplicative.ofAdd (κ z)) '' (conjSub δ W : Set G)).ncard ≤ 16 := by
    calc _ ≤ (Set.univ : Set (Multiplicative F)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = 16 := by rw [Set.ncard_univ, hF]
  rw [hcard, hfib] at hcnt
  have h1 : Nat.card ↥(W ⊓ conjSub δ W) = 16 := by
    by_contra hne
    have h15 : Nat.card ↥(W ⊓ conjSub δ W) ≤ 15 := by omega
    have := Nat.mul_le_mul h15 himg
    omega
  have h2 : ((fun z => Multiplicative.ofAdd (κ z)) '' (conjSub δ W : Set G)).ncard = 16 := by
    by_contra hne
    have h15 : ((fun z => Multiplicative.ofAdd (κ z)) '' (conjSub δ W : Set G)).ncard ≤ 15 := by
      omega
    have := Nat.mul_le_mul hcardWW' h15
    omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hWW' (by rw [S.card_W₀, h1]), fun b => ?_⟩
  have huniv : (fun z => Multiplicative.ofAdd (κ z)) '' (conjSub δ W : Set G) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, hF, h2]) (Set.toFinite _)
  have hb : Multiplicative.ofAdd b ∈ (fun z => Multiplicative.ofAdd (κ z)) ''
      (conjSub δ W : Set G) := by
    rw [huniv]
    exact Set.mem_univ _
  obtain ⟨w, hw, hwb⟩ := hb
  exact ⟨w, hw, Multiplicative.ofAdd.injective hwb⟩

end SylowA

end Step

end CFSG.OddStandard.Seitz77
