module

public import CFSG.LocalAnalysis.OddStandard.Seitz77U
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMatrix
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.Open (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

section Radicals

variable {G : Type*} [Group G]

structure Radicals (V V₁ V₂ : Subgroup G) (q : ℕ) : Prop where
  le₁ : V₁ ≤ V
  le₂ : V₂ ≤ V
  normal₁ : (V₁.subgroupOf V).Normal
  normal₂ : (V₂.subgroupOf V).Normal
  elem₁ : IsElemAbelian 2 V₁
  elem₂ : IsElemAbelian 2 V₂
  card₁ : Nat.card V₁ = q ^ 2
  card₂ : Nat.card V₂ = q ^ 2
  card : Nat.card V = q ^ 3
  inf_eq : V₁ ⊓ V₂ = V ⊓ centralizer (V : Set G)
  sup_eq : V₁ ⊔ V₂ = V
  card_center : Nat.card ↥(V ⊓ centralizer (V : Set G)) = q
  le_of_elem : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → E ≤ V₁ ∨ E ≤ V₂
  eq_of_card : ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E = q ^ 2 →
    E = V₁ ∨ E = V₂
  le_of_sq : ∀ x ∈ V, x ^ 2 = 1 → x ∈ V₁ ∨ x ∈ V₂

theorem isElemAbelian_of_forall {E : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h2 : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, h2⟩

theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

theorem IsElemAbelian.mono {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

namespace Radicals

variable {V V₁ V₂ : Subgroup G} {q : ℕ}

theorem ne (hR : Radicals V V₁ V₂ q) (hq : 2 ≤ q) : V₁ ≠ V₂ := by
  intro h
  have h1 := hR.card_center
  rw [← hR.inf_eq, ← h, inf_idem, hR.card₁] at h1
  have : q < q ^ 2 := by nlinarith
  omega

theorem property (hR : Radicals V V₁ V₂ q) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    W ≤ V ∧ IsElemAbelian 2 W ∧ Nat.card W = q ^ 2 := by
  rcases hW with rfl | rfl
  · exact ⟨hR.le₁, hR.elem₁, hR.card₁⟩
  · exact ⟨hR.le₂, hR.elem₂, hR.card₂⟩

theorem normal (hR : Radicals V V₁ V₂ q) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    (W.subgroupOf V).Normal := by
  rcases hW with rfl | rfl
  · exact hR.normal₁
  · exact hR.normal₂

theorem eq_or_eq (hR : Radicals V V₁ V₂ q) (hq : 2 ≤ q) {W₁ W₂ : Subgroup G}
    (hW : Radicals V W₁ W₂ q) : (W₁ = V₁ ∧ W₂ = V₂) ∨ (W₁ = V₂ ∧ W₂ = V₁) := by
  rcases hR.eq_of_card W₁ hW.le₁ hW.elem₁ hW.card₁ with h1 | h1 <;>
    rcases hR.eq_of_card W₂ hW.le₂ hW.elem₂ hW.card₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) (hW.ne hq)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) (hW.ne hq)

end Radicals

end Radicals

section Map

variable {H G : Type*} [Group H] [Group G] {φ : H →* G}

theorem isElemAbelian_map (φ : H →* G) {E : Subgroup H} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map φ) := CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_comap (hφ : Function.Injective φ) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.comap φ) := CFSG.Open.IsElemAbelian.comap hE hφ

theorem map_inf_centralizer (hφ : Function.Injective φ) (V : Subgroup H) :
    (V ⊓ centralizer (V : Set H)).map φ =
      V.map φ ⊓ centralizer ((V.map φ : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨u, ⟨huV, huC⟩, rfl⟩
    refine ⟨⟨u, huV, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 huC v hv]
  · rintro ⟨⟨u, huV, rfl⟩, hC⟩
    refine ⟨u, ⟨huV, mem_centralizer_iff.2 fun v hv => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hC (φ v) ⟨v, hv, rfl⟩

theorem eq_map_comap_of_le {E : Subgroup G} {V : Subgroup H} (hE : E ≤ V.map φ) :
    E = (E.comap φ).map φ := by
  refine le_antisymm (fun x hx => ?_) (map_comap_le _ _)
  obtain ⟨u, -, rfl⟩ := hE hx
  exact ⟨u, hx, rfl⟩

theorem Radicals.map (hφ : Function.Injective φ) {V V₁ V₂ : Subgroup H} {q : ℕ}
    (hR : Radicals V V₁ V₂ q) : Radicals (V.map φ) (V₁.map φ) (V₂.map φ) q := by
  have hnorm : ∀ {W : Subgroup H}, W ≤ V → (W.subgroupOf V).Normal →
      ((W.map φ).subgroupOf (V.map φ)).Normal := by
    intro W hWV hW
    rw [normal_subgroupOf_iff_le_normalizer (map_mono hWV)]
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨v * w * v⁻¹, ?_, by simp⟩
      have := (normal_subgroupOf_iff_le_normalizer hWV).1 hW hv
      exact (mem_normalizer_iff.1 this w).1 hw
    · rintro ⟨w, hw, hwx⟩
      refine ⟨v⁻¹ * w * v, ?_, ?_⟩
      · have := (normal_subgroupOf_iff_le_normalizer hWV).1 hW (V.inv_mem hv)
        have h := (mem_normalizer_iff.1 this w).1 hw
        rwa [inv_inv] at h
      · rw [map_mul, map_mul, map_inv, hwx]
        group
  have hcardmap : ∀ W : Subgroup H, Nat.card (W.map φ) = Nat.card W := fun W =>
    Subgroup.card_map_of_injective hφ
  refine ⟨map_mono hR.le₁, map_mono hR.le₂, hnorm hR.le₁ hR.normal₁, hnorm hR.le₂ hR.normal₂,
    isElemAbelian_map φ hR.elem₁, isElemAbelian_map φ hR.elem₂, by rw [hcardmap, hR.card₁],
    by rw [hcardmap, hR.card₂], by rw [hcardmap, hR.card], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ φ hφ, ← map_inf_centralizer hφ, hR.inf_eq]
  · rw [← Subgroup.map_sup, hR.sup_eq]
  · rw [← map_inf_centralizer hφ, hcardmap, hR.card_center]
  · intro E hE hEl
    rw [eq_map_comap_of_le hE]
    have hle : E.comap φ ≤ V := by
      rw [← comap_map_eq_self_of_injective hφ V]
      exact comap_mono hE
    rcases hR.le_of_elem _ hle (isElemAbelian_comap hφ hEl) with h | h
    · exact Or.inl (map_mono h)
    · exact Or.inr (map_mono h)
  · intro E hE hEl hc
    rw [eq_map_comap_of_le hE]
    have hle : E.comap φ ≤ V := by
      rw [← comap_map_eq_self_of_injective hφ V]
      exact comap_mono hE
    have hc' : Nat.card (E.comap φ) = q ^ 2 := by
      rw [← hcardmap, ← eq_map_comap_of_le hE, hc]
    rcases hR.eq_of_card _ hle (isElemAbelian_comap hφ hEl) hc' with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · rintro _ ⟨u, hu, rfl⟩ hu2
    have hu2' : u ^ 2 = 1 := hφ (by rw [map_pow, hu2, map_one])
    rcases hR.le_of_sq u hu hu2' with h | h
    · exact Or.inl ⟨u, h, rfl⟩
    · exact Or.inr ⟨u, h, rfl⟩

end Map

section Unip

open CFSG.OddStandard.Seitz77

variable {K : Type} [Field K]

theorem radOne_normal : (radOne K).Normal := by
  refine ⟨fun h hh g => ?_⟩
  rw [mem_radOne] at hh ⊢
  rw [coordB_mul, coordB_mul, coordB_inv, hh]
  ring

theorem radTwo_normal : (radTwo K).Normal := by
  refine ⟨fun h hh g => ?_⟩
  rw [mem_radTwo] at hh ⊢
  rw [coordA_mul, coordA_mul, coordA_inv, hh]
  ring

theorem radicals_unipAll [Finite K] [CharP K 2] :
    Radicals (⊤ : Subgroup (unipAll K)) (radOne K) (radTwo K) (Nat.card K) where
  le₁ := le_top
  le₂ := le_top
  normal₁ := by
    have := radOne_normal (K := K)
    exact Subgroup.normal_subgroupOf
  normal₂ := by
    have := radTwo_normal (K := K)
    exact Subgroup.normal_subgroupOf
  elem₁ := isElemAbelian_of_forall (fun _ hx _ hy => mul_comm_of_mem_radOne hx hy)
    fun _ hx => by rw [sq]; exact mul_self_of_mem_radOne hx
  elem₂ := isElemAbelian_of_forall (fun _ hx _ hy => mul_comm_of_mem_radTwo hx hy)
    fun _ hx => by rw [sq]; exact mul_self_of_mem_radTwo hx
  card₁ := card_radOne
  card₂ := card_radTwo
  card := by rw [Subgroup.card_top, card_unipAll]
  inf_eq := by
    rw [radOne_inf_radTwo, top_inf_eq, coe_top, centralizer_univ, center_unipAll]
  sup_eq := radOne_sup_radTwo
  card_center := by
    rw [top_inf_eq, coe_top, centralizer_univ, center_unipAll, card_radCenter]
  le_of_elem E _ hE := le_radOne_or_le_radTwo E fun g hg => by rw [← sq]; exact hE.2 g hg
  eq_of_card E _ hE hc := eq_radOne_or_radTwo_of_card (fun g hg => by rw [← sq]; exact hE.2 g hg)
    hc
  le_of_sq x _ hx := (sq_eq_one_iff x).1 (by rw [← sq]; exact hx)

variable (K) in
@[expose] noncomputable def unipEmb : unipAll K →* projectiveSL 3 K :=
  (proj 3 K).comp (unipAll K).subtype

theorem unipEmb_injective : Function.Injective (unipEmb K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨rfl, rfl, rfl⟩ := proj_unipU_eq_one_iff.1 (by simpa [unipEmb, coe_uelt] using hg)
  exact uelt_zero

theorem map_top_unipEmb : (⊤ : Subgroup (unipAll K)).map (unipEmb K) = projUnip K := by
  rw [unipEmb, ← Subgroup.map_map, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem map_radOne_unipEmb : (radOne K).map (unipEmb K) = projRad K 0 := by
  rw [unipEmb, ← Subgroup.map_map, radOne, subgroupOf_map_subtype,
    inf_eq_left.2 unipOne_le_unipAll]
  rfl

theorem map_radTwo_unipEmb : (radTwo K).map (unipEmb K) = projRad K 1 := by
  rw [unipEmb, ← Subgroup.map_map, radTwo, subgroupOf_map_subtype,
    inf_eq_left.2 unipTwo_le_unipAll]
  rfl

theorem radicals_projUnip [Finite K] [CharP K 2] :
    Radicals (projUnip K) (projRad K 0) (projRad K 1) (Nat.card K) := by
  rw [← map_top_unipEmb, ← map_radOne_unipEmb, ← map_radTwo_unipEmb]
  exact radicals_unipAll.map unipEmb_injective

end Unip

section Levi

open CFSG.LieType.Chevalley (SL2)

variable (K : Type) [Field K]

@[expose] noncomputable def radCoordZero : Multiplicative (Fin 2 → K) →* projectiveSL 3 K where
  toFun w := proj 3 K (unipU K (-(Multiplicative.toAdd w) 1) 0 (Multiplicative.toAdd w 0))
  map_one' := by simp [unipU_zero]
  map_mul' w w' := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← map_mul, unipU_mul]
    congr 2 <;> ring

@[expose] noncomputable def radCoordOne : Multiplicative (Fin 2 → K) →* projectiveSL 3 K where
  toFun w := proj 3 K (unipU K 0 (Multiplicative.toAdd w 1) (Multiplicative.toAdd w 0))
  map_one' := by simp [unipU_zero]
  map_mul' w w' := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← map_mul, unipU_mul]
    congr 2 <;> ring

@[expose] noncomputable def radCoord (i : Fin 2) :
    Multiplicative (Fin 2 → K) →* projectiveSL 3 K :=
  ![radCoordZero K, radCoordOne K] i

@[expose] noncomputable def torSLZero : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun l := ⟨diagonal ![(l : K) ^ 2, (l⁻¹ : Kˣ), (l⁻¹ : Kˣ)], by
    simp [det_diagonal, Fin.prod_univ_three, sq]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l l' := by
    apply Subtype.ext
    show diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [mul_pow, mul_comm]

@[expose] noncomputable def torSLOne : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun l := ⟨diagonal ![(l : K), (l : K), ((l⁻¹ : Kˣ) : K) ^ 2], by
    simp [det_diagonal, Fin.prod_univ_three]
    field_simp⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l l' := by
    apply Subtype.ext
    show diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [mul_pow, mul_comm]

@[expose] noncomputable def torSL (i : Fin 2) : Kˣ →* SpecialLinearGroup (Fin 3) K :=
  ![torSLZero K, torSLOne K] i

variable {K}

theorem radCoord_zero_apply (w : Multiplicative (Fin 2 → K)) :
    radCoord K 0 w =
      proj 3 K (unipU K (-(Multiplicative.toAdd w) 1) 0 (Multiplicative.toAdd w 0)) :=
  rfl

theorem radCoord_one_apply (w : Multiplicative (Fin 2 → K)) :
    radCoord K 1 w = proj 3 K (unipU K 0 (Multiplicative.toAdd w 1) (Multiplicative.toAdd w 0)) :=
  rfl

theorem coe_torSL_zero (l : Kˣ) :
    (torSL K 0 l : Matrix (Fin 3) (Fin 3) K) = diagonal ![(l : K) ^ 2, (l⁻¹ : Kˣ), (l⁻¹ : Kˣ)] :=
  rfl

theorem coe_torSL_one (l : Kˣ) :
    (torSL K 1 l : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), (l : K), ((l⁻¹ : Kˣ) : K) ^ 2] :=
  rfl

theorem leviProj_zero_apply (B : SL2 K) : leviProj K 0 B = proj 3 K (leviOne K B) :=
  rfl

theorem leviProj_one_apply (B : SL2 K) : leviProj K 1 B = proj 3 K (leviTwo K B) :=
  rfl

theorem radCoord_injective (i : Fin 2) : Function.Injective (radCoord K i) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  apply Multiplicative.toAdd.injective
  revert hw
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · intro hw
    rw [radCoord_zero_apply, proj_unipU_eq_one_iff] at hw
    funext j
    fin_cases j
    · simpa using hw.2.2
    · simpa using hw.1
  · intro hw
    rw [radCoord_one_apply, proj_unipU_eq_one_iff] at hw
    funext j
    fin_cases j
    · simpa using hw.2.2
    · simpa using hw.2.1

theorem range_radCoord (i : Fin 2) : (radCoord K i).range = projRad K i := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · ext x
    rw [MonoidHom.mem_range, mem_projRad_zero]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, _, (radCoord_zero_apply w).symm⟩
    · rintro ⟨a, c, rfl⟩
      exact ⟨Multiplicative.ofAdd ![c, -a], by rw [radCoord_zero_apply]; simp⟩
  · ext x
    rw [MonoidHom.mem_range, mem_projRad_one]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, _, (radCoord_one_apply w).symm⟩
    · rintro ⟨b, c, rfl⟩
      exact ⟨Multiplicative.ofAdd ![c, b], by rw [radCoord_one_apply]; simp⟩

theorem leviProj_conj_radCoord (i : Fin 2) (B : SL2 K) (w : Multiplicative (Fin 2 → K)) :
    leviProj K i B * radCoord K i w * (leviProj K i B)⁻¹ =
      radCoord K i (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ
        Multiplicative.toAdd w)) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [radCoord_zero_apply, radCoord_zero_apply, leviProj_zero_apply, ← map_inv, ← map_mul,
      ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviOne_mul_unipU B _ _)]
    congr 2 <;> simp <;> ring
  · rw [radCoord_one_apply, radCoord_one_apply, leviProj_one_apply, ← map_inv, ← map_mul,
      ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviTwo_mul_unipU B _ _)]
    congr 2 <;> simp

theorem torSL_zero_mul_unipU (l : Kˣ) (a c : K) :
    torSL K 0 l * unipU K a 0 c =
      unipU K ((l : K) ^ 3 * a) 0 ((l : K) ^ 3 * c) * torSL K 0 l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_zero,
    diagonal_mul,
    mul_diagonal, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem torSL_one_mul_unipU (l : Kˣ) (b c : K) :
    torSL K 1 l * unipU K 0 b c =
      unipU K 0 ((l : K) ^ 3 * b) ((l : K) ^ 3 * c) * torSL K 1 l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_one,
    diagonal_mul,
    mul_diagonal, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem torSL_conj_radCoord (i : Fin 2) (l : Kˣ) (w : Multiplicative (Fin 2 → K)) :
    proj 3 K (torSL K i l) * radCoord K i w * (proj 3 K (torSL K i l))⁻¹ =
      radCoord K i (Multiplicative.ofAdd (((l : K) ^ 3) • Multiplicative.toAdd w)) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [radCoord_zero_apply, radCoord_zero_apply, ← map_inv, ← map_mul, ← map_mul,
      mul_inv_eq_iff_eq_mul.2 (torSL_zero_mul_unipU l _ _)]
    simp
  · rw [radCoord_one_apply, radCoord_one_apply, ← map_inv, ← map_mul, ← map_mul,
      mul_inv_eq_iff_eq_mul.2 (torSL_one_mul_unipU l _ _)]
    simp

theorem torSL_zero_mul_leviOne (l : Kˣ) (B : SL2 K) :
    torSL K 0 l * leviOne K B = leviOne K B * torSL K 0 l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_zero,
    diagonal_mul,
    mul_diagonal, coe_leviOne]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem torSL_one_mul_leviTwo (l : Kˣ) (B : SL2 K) :
    torSL K 1 l * leviTwo K B = leviTwo K B * torSL K 1 l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_one,
    diagonal_mul,
    mul_diagonal, coe_leviTwo]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem torSL_mul_levi (i : Fin 2) (l : Kˣ) (B : SL2 K) :
    torSL K i l * levi K i B = levi K i B * torSL K i l := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨torSL_zero_mul_leviOne l B, torSL_one_mul_leviTwo l B⟩

theorem map_mem_normalizer_projRad {G : Type*} [Group G] (i : Fin 2) (φ : G →* projectiveSL 3 K)
    (h : ∀ g w, ∃ w', φ g * radCoord K i w * (φ g)⁻¹ = radCoord K i w') (g : G) :
    φ g ∈ normalizer (projRad K i : Set (projectiveSL 3 K)) := by
  have key : ∀ g, ∀ x ∈ projRad K i, φ g * x * (φ g)⁻¹ ∈ projRad K i := by
    intro g x hx
    rw [← range_radCoord] at hx ⊢
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', hw'⟩ := h g w
    exact ⟨w', hw'.symm⟩
  refine mem_normalizer_of_conj_mem (key g) fun x hx => ?_
  have := key g⁻¹ x hx
  rwa [map_inv, inv_inv] at this

theorem three_ne_zero_of_charTwo [CharP K 2] : (3 : K) ≠ 0 := by
  rw [show (3 : K) = 2 + 1 by norm_num, CharTwo.two_eq_zero, zero_add]
  exact one_ne_zero

theorem exists_eq_torSL_zero_mul [Finite K] [CharP K 2] {g : SpecialLinearGroup (Fin 3) K}
    (h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    ∃ (l : Kˣ) (a c : K) (B : SL2 K), g = torSL K 0 l * unipU K a 0 c * leviOne K B := by
  have hdet := g.2
  rw [Matrix.det_fin_three, h10, h20] at hdet
  have hα : (g : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((g : Matrix (Fin 3) (Fin 3) K) 0 0)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hα hr
  set t := torSL K 0 (Units.mk0 r hr0)⁻¹ with ht
  have e00 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_zero, diagonal_mul]
    simp [hr]
    field_simp
  have e10 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_zero, diagonal_mul, h10, mul_zero]
  have e20 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_zero, diagonal_mul, h20, mul_zero]
  obtain ⟨a, c, B, hB⟩ := eq_unipU_mul_leviOne e00 e10 e20
  refine ⟨Units.mk0 r hr0, a, c, B, ?_⟩
  rw [ht, map_inv, inv_mul_eq_iff_eq_mul] at hB
  rw [hB, mul_assoc]

theorem exists_eq_torSL_one_mul [Finite K] [CharP K 2] {g : SpecialLinearGroup (Fin 3) K}
    (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    ∃ (l : Kˣ) (b c : K) (B : SL2 K), g = torSL K 1 l * unipU K 0 b c * leviTwo K B := by
  have hdet := g.2
  rw [Matrix.det_fin_three, h20, h21] at hdet
  have hα : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((g : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, inv_eq_zero] at hr
    exact hα hr
  set t := torSL K 1 (Units.mk0 r hr0)⁻¹ with ht
  have e22 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_one, diagonal_mul]
    simp only [Fin.isValue, inv_inv, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons,
      head_cons, Units.val_mk0]
    rw [sq, ← hr, inv_mul_cancel₀ hα]
  have e20 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_one, diagonal_mul, h20, mul_zero]
  have e21 : ((t * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    rw [ht, Matrix.SpecialLinearGroup.coe_mul, coe_torSL_one, diagonal_mul, h21, mul_zero]
  obtain ⟨b, c, B, hB⟩ := eq_unipU_mul_leviTwo e22 e20 e21
  refine ⟨Units.mk0 r hr0, b, c, B, ?_⟩
  rw [ht, map_inv, inv_mul_eq_iff_eq_mul] at hB
  rw [hB, mul_assoc]

theorem exists_eq_of_mem_normalizer_zero [Finite K] [CharP K 2] {x : projectiveSL 3 K}
    (hx : x ∈ normalizer (projRad K 0 : Set (projectiveSL 3 K))) :
    ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K),
      x = radCoord K 0 w * proj 3 K (torSL K 0 l) * leviProj K 0 B := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  obtain ⟨h10, h20⟩ := col_zero_of_mem_normalizer three_ne_zero_of_charTwo hx
  obtain ⟨l, a, c, B, rfl⟩ := exists_eq_torSL_zero_mul h10 h20
  refine ⟨Multiplicative.ofAdd ![(l : K) ^ 3 * c, -((l : K) ^ 3 * a)], l, B, ?_⟩
  rw [torSL_zero_mul_unipU, radCoord_zero_apply, leviProj_zero_apply, map_mul, map_mul]
  simp

theorem exists_eq_of_mem_normalizer_one [Finite K] [CharP K 2] {x : projectiveSL 3 K}
    (hx : x ∈ normalizer (projRad K 1 : Set (projectiveSL 3 K))) :
    ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K),
      x = radCoord K 1 w * proj 3 K (torSL K 1 l) * leviProj K 1 B := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  obtain ⟨h20, h21⟩ := row_two_of_mem_normalizer three_ne_zero_of_charTwo hx
  obtain ⟨l, b, c, B, rfl⟩ := exists_eq_torSL_one_mul h20 h21
  refine ⟨Multiplicative.ofAdd ![(l : K) ^ 3 * c, (l : K) ^ 3 * b], l, B, ?_⟩
  rw [torSL_one_mul_unipU, radCoord_one_apply, leviProj_one_apply, map_mul, map_mul]
  simp

theorem mem_normalizer_projRad_iff [Finite K] [CharP K 2] (i : Fin 2) (x : projectiveSL 3 K) :
    x ∈ normalizer (projRad K i : Set (projectiveSL 3 K)) ↔
      ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K),
        x = radCoord K i w * proj 3 K (torSL K i l) * leviProj K i B := by
  constructor
  · revert x
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => exists_eq_of_mem_normalizer_zero, fun _ => exists_eq_of_mem_normalizer_one⟩
  · rintro ⟨w, l, B, rfl⟩
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact le_normalizer (by rw [← range_radCoord]; exact ⟨w, rfl⟩)
    · exact map_mem_normalizer_projRad i ((proj 3 K).comp (torSL K i))
        (fun l w => ⟨_, torSL_conj_radCoord i l w⟩) l
    · exact map_mem_normalizer_projRad i (leviProj K i)
        (fun B w => ⟨_, leviProj_conj_radCoord i B w⟩) B

end Levi

section Frame

variable {G : Type*} [Group G] {K : Type} [Field K]

structure Frame (A V : Subgroup G) (K : Type) [Field K] where
  φ : projectiveSL 3 K →* G
  injective : Function.Injective φ
  range_eq : φ.range = A
  map_projUnip : (projUnip K).map φ = V

namespace Frame

variable {A V : Subgroup G}

theorem mem_A (F : Frame A V K) (x : projectiveSL 3 K) : F.φ x ∈ A := by
  have h : F.φ x ∈ F.φ.range := ⟨x, rfl⟩
  rwa [F.range_eq] at h

theorem map_le (F : Frame A V K) (X : Subgroup (projectiveSL 3 K)) : X.map F.φ ≤ A := by
  rintro _ ⟨x, -, rfl⟩
  exact F.mem_A x

theorem exists_eq (F : Frame A V K) {a : G} (ha : a ∈ A) : ∃ x, F.φ x = a := by
  rw [← F.range_eq] at ha
  exact ha

@[expose] noncomputable def equiv (F : Frame A V K) : projectiveSL 3 K ≃* A :=
  (MonoidHom.ofInjective F.injective).trans (MulEquiv.subgroupCongr F.range_eq)

theorem mem_V (F : Frame A V K) {x : projectiveSL 3 K} (hx : x ∈ projUnip K) : F.φ x ∈ V := by
  have h : F.φ x ∈ (projUnip K).map F.φ := ⟨x, hx, rfl⟩
  rwa [F.map_projUnip] at h

theorem exists_eq_of_mem_V (F : Frame A V K) {v : G} (hv : v ∈ V) :
    ∃ x ∈ projUnip K, F.φ x = v := by
  have h : v ∈ (projUnip K).map F.φ := by rwa [F.map_projUnip]
  exact h

theorem radicals [Finite K] [CharP K 2] (F : Frame A V K) :
    Radicals V ((projRad K 0).map F.φ) ((projRad K 1).map F.φ) (Nat.card K) := by
  have h := (radicals_projUnip (K := K)).map F.injective
  rwa [F.map_projUnip] at h

end Frame

theorem exists_frame [Finite G] [Finite K] [CharP K 2] {A V : Subgroup G}
    (e : A ≃* projectiveSL 3 K) (hV : IsSylowOf 2 V A) : Nonempty (Frame A V K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hV
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  let Q' : Sylow 2 (projectiveSL 3 K) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) U₀ Q'
  let φ : projectiveSL 3 K →* G :=
    A.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom)
  have hφ : Function.Injective φ :=
    A.subtype_injective.comp (e.symm.injective.comp (MulAut.conj g).injective)
  refine ⟨⟨φ, hφ, ?_, ?_⟩⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm _).2
    · intro hx
      refine ⟨(MulAut.conj g)⁻¹ (e ⟨x, hx⟩), ?_⟩
      change ((e.symm ((MulAut.conj g) ((MulAut.conj g)⁻¹ (e ⟨x, hx⟩))) : A) : G) = x
      rw [MulAut.apply_inv_self, MulEquiv.symm_apply_apply]
  · have hQ'g : (Q' : Subgroup (projectiveSL 3 K)) =
        (projUnip K).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, hU₀, ← projUnip_eq_projUnitriangular]
      rfl
    have hQ'e : (Q' : Subgroup (projectiveSL 3 K)) = (Q : Subgroup A).map e.toMonoidHom := rfl
    rw [← hQ, show φ = (A.subtype.comp e.symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom
      from rfl, ← Subgroup.map_map, ← hQ'g, hQ'e, Subgroup.map_map]
    congr 1
    ext x
    simp

theorem exists_radicals_of_mulEquiv [Finite G] [Finite K] [CharP K 2] {A V : Subgroup G}
    (e : A ≃* projectiveSL 3 K) (hV : IsSylowOf 2 V A) :
    ∃ V₁ V₂ : Subgroup G, Radicals V V₁ V₂ (Nat.card K) := by
  obtain ⟨F⟩ := exists_frame e hV
  exact ⟨_, _, F.radicals⟩

theorem Frame.exists_eq_radical [Finite K] [CharP K 2] {A V V₁ V₂ W : Subgroup G}
    (F : Frame A V K) (hR : Radicals V V₁ V₂ (Nat.card K)) (hW : W = V₁ ∨ W = V₂) :
    ∃ i : Fin 2, W = (projRad K i).map F.φ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases F.radicals.eq_or_eq hq hR with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hW with rfl | rfl
  · exact ⟨0, h1⟩
  · exact ⟨1, h2⟩
  · exact ⟨1, h1⟩
  · exact ⟨0, h2⟩

theorem exists_conj_of_mulEquiv [Finite K] [CharP K 2] {A : Subgroup G}
    (e : A ≃* projectiveSL 3 K) {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) : ∃ a ∈ A, a * x * a⁻¹ = y := by
  have key : ∀ {z : G} (hz : z ∈ A), orderOf z = 2 →
      ∃ w : projectiveSL 3 K, w * e ⟨z, hz⟩ * w⁻¹ = ComponentClassification.RankTwoL3Even.x0 K := by
    intro z hz hz2
    have hz2' : orderOf (e ⟨z, hz⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hz2
    refine ComponentClassification.RankTwoL3Even.exists_conj_eq_x0 ?_ ?_
    · rw [← sq, ← hz2', pow_orderOf_eq_one]
    · intro h
      rw [h, orderOf_one] at hz2'
      exact absurd hz2' (by norm_num)
  obtain ⟨u, hu⟩ := key hx hx2
  obtain ⟨w, hw⟩ := key hy hy2
  refine ⟨((e.symm w : A) : G)⁻¹ * (e.symm u : A), A.mul_mem (A.inv_mem (e.symm w).2) (e.symm u).2,
    ?_⟩
  have h : w⁻¹ * u * e ⟨x, hx⟩ * (w⁻¹ * u)⁻¹ = e ⟨y, hy⟩ := by
    rw [show w⁻¹ * u * e ⟨x, hx⟩ * (w⁻¹ * u)⁻¹ = w⁻¹ * (u * e ⟨x, hx⟩ * u⁻¹) * w by group, hu,
      ← hw]
    group
  have h' := congrArg (fun z => ((e.symm z : A) : G)) h
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h'
  exact h'

end Frame

section LeviData

open CFSG.LieType.Chevalley (SL2)

variable {G : Type*} [Group G] {K : Type} [Field K]

structure LeviData (A W : Subgroup G) (K : Type) [Field K] where
  ι : Multiplicative (Fin 2 → K) →* G
  ι_injective : Function.Injective ι
  range_ι : ι.range = W
  ι_mem : ∀ w, ι w ∈ A
  lev : SL2 K →* G
  lev_injective : Function.Injective lev
  lev_mem : ∀ B, lev B ∈ A
  lev_conj : ∀ (B : SL2 K) (w : Multiplicative (Fin 2 → K)), lev B * ι w * (lev B)⁻¹ =
    ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd w))
  tor : Kˣ →* G
  tor_mem : ∀ l, tor l ∈ A
  tor_conj : ∀ (l : Kˣ) (w : Multiplicative (Fin 2 → K)), tor l * ι w * (tor l)⁻¹ =
    ι (Multiplicative.ofAdd (((l : K) ^ 3) • Multiplicative.toAdd w))
  tor_comm : ∀ (l : Kˣ) (B : SL2 K), tor l * lev B = lev B * tor l
  mem_normalizer_iff : ∀ x ∈ A, x ∈ normalizer (W : Set G) ↔
    ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K), x = ι w * tor l * lev B
  transitive : ∀ v ∈ W, ∀ w ∈ W, v ≠ 1 → w ≠ 1 → ∃ B : SL2 K, lev B * v * (lev B)⁻¹ = w

theorem mem_normalizer_map_iff {H : Type*} [Group H] {φ : H →* G} (hφ : Function.Injective φ)
    (y : H) (X : Subgroup H) :
    φ y ∈ normalizer ((X.map φ : Subgroup G) : Set G) ↔ y ∈ normalizer (X : Set H) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    rw [← mem_map_iff_mem hφ (K := X), h, ← map_inv, ← map_mul, ← map_mul,
      mem_map_iff_mem hφ]
  · intro h g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨y * x * y⁻¹, (h x).1 hx, by simp⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have := (h (y⁻¹ * x * y)).2 (by simpa [mul_assoc] using hx)
        exact this
      · rw [map_mul, map_mul, map_inv, hxg]
        group

@[expose] noncomputable def Frame.leviData [Finite K] [CharP K 2] {A V : Subgroup G}
    (F : Frame A V K) (i : Fin 2) : LeviData A ((projRad K i).map F.φ) K where
  ι := F.φ.comp (radCoord K i)
  ι_injective := F.injective.comp (radCoord_injective i)
  range_ι := by rw [MonoidHom.range_comp, range_radCoord]
  ι_mem _ := F.mem_A _
  lev := F.φ.comp (leviProj K i)
  lev_injective := F.injective.comp (leviProj_injective i)
  lev_mem _ := F.mem_A _
  lev_conj B w := by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, leviProj_conj_radCoord]
  tor := F.φ.comp ((proj 3 K).comp (torSL K i))
  tor_mem _ := F.mem_A _
  tor_conj l w := by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, torSL_conj_radCoord]
  tor_comm l B := by
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, leviProj, MonoidHom.comp_apply, ← map_mul, ← map_mul,
      torSL_mul_levi]
  mem_normalizer_iff x hx := by
    obtain ⟨y, rfl⟩ := F.exists_eq hx
    rw [mem_normalizer_map_iff F.injective, mem_normalizer_projRad_iff]
    constructor
    · rintro ⟨w, l, B, rfl⟩
      exact ⟨w, l, B, by simp only [MonoidHom.comp_apply, map_mul]⟩
    · rintro ⟨w, l, B, h⟩
      refine ⟨w, l, B, F.injective ?_⟩
      simpa only [MonoidHom.comp_apply, map_mul] using h
  transitive v hv w hw hv1 hw1 := by
    obtain ⟨r, hr, rfl⟩ := hv
    obtain ⟨s, hs, rfl⟩ := hw
    have hr1 : r ≠ 1 := fun h => hv1 (by rw [h, map_one])
    have hs1 : s ≠ 1 := fun h => hw1 (by rw [h, map_one])
    have key : ∃ B : SL2 K, leviProj K i B * r * (leviProj K i B)⁻¹ = s := by
      fin_cases i
      · exact projRad_zero_transitive hr hs hr1 hs1
      · exact projRad_one_transitive hr hs hr1 hs1
    obtain ⟨B, hB⟩ := key
    refine ⟨B, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hB]

theorem Frame.leviData_ι [Finite K] [CharP K 2] {A V : Subgroup G} (F : Frame A V K)
    (i : Fin 2) : (F.leviData i).ι = F.φ.comp (radCoord K i) :=
  rfl

theorem Frame.leviData_lev [Finite K] [CharP K 2] {A V : Subgroup G} (F : Frame A V K)
    (i : Fin 2) : (F.leviData i).lev = F.φ.comp (leviProj K i) :=
  rfl

theorem exists_leviData [Finite G] [Finite K] [CharP K 2] {A V V₁ V₂ W : Subgroup G}
    (e : A ≃* projectiveSL 3 K) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂ (Nat.card K))
    (hW : W = V₁ ∨ W = V₂) : Nonempty (LeviData A W K) := by
  obtain ⟨F⟩ := exists_frame e hV
  obtain ⟨i, rfl⟩ := F.exists_eq_radical hR hW
  exact ⟨F.leviData i⟩

namespace LeviData

variable {A W : Subgroup G}

theorem lev_mem_normalizer (D : LeviData A W K) (B : SL2 K) :
    D.lev B ∈ normalizer (W : Set G) := by
  have hW : ∀ y, y ∈ W ↔ y ∈ D.ι.range := fun y => by rw [D.range_ι]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hW, hW]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (D.lev_conj B w).symm⟩
  · rintro ⟨w, hw⟩
    refine ⟨Multiplicative.ofAdd (((B⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Multiplicative.toAdd w), ?_⟩
    have h := D.lev_conj B⁻¹ w
    rw [hw, map_inv, inv_inv] at h
    rw [← h]
    group

theorem tor_mem_normalizer (D : LeviData A W K) (l : Kˣ) :
    D.tor l ∈ normalizer (W : Set G) := by
  have hW : ∀ y, y ∈ W ↔ y ∈ D.ι.range := fun y => by rw [D.range_ι]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hW, hW]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (D.tor_conj l w).symm⟩
  · rintro ⟨w, hw⟩
    refine ⟨Multiplicative.ofAdd ((((l⁻¹ : Kˣ) : K) ^ 3) • Multiplicative.toAdd w), ?_⟩
    have h := D.tor_conj l⁻¹ w
    rw [hw, map_inv, inv_inv] at h
    rw [← h]
    group

end LeviData

end LeviData

end CFSG.LocalAnalysis.EvenBN.LinearThree
