module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem map_conj_centralizer_singleton' {G : Type*} [Group G] (χ β : G) :
    (centralizer {β}).map (MulAut.conj χ).toMonoidHom = centralizer {χ * β * χ⁻¹} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    change χ * y * χ⁻¹ * (χ * β * χ⁻¹) = χ * β * χ⁻¹ * (χ * y * χ⁻¹)
    calc χ * y * χ⁻¹ * (χ * β * χ⁻¹) = χ * (y * β) * χ⁻¹ := by group
      _ = χ * (β * y) * χ⁻¹ := by rw [hy]
      _ = χ * β * χ⁻¹ * (χ * y * χ⁻¹) := by group
  · intro hx
    rw [mem_centralizer_singleton_iff] at hx
    refine ⟨χ⁻¹ * x * χ, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc χ⁻¹ * x * χ * β = χ⁻¹ * (x * (χ * β * χ⁻¹)) * χ := by group
        _ = χ⁻¹ * ((χ * β * χ⁻¹) * x) * χ := by rw [hx]
        _ = β * (χ⁻¹ * x * χ) := by group
    · change χ * (χ⁻¹ * x * χ) * χ⁻¹ = x
      group

theorem map_conj_inner {P : Type*} [Group P] (χ : MulAut P) :
    (inner P).map (MulAut.conj χ).toMonoidHom = inner P := by
  have hn := OuterAutomorphisms.inner_normal P
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hn.conj_mem y hy χ
  · intro x hx
    refine ⟨χ⁻¹ * x * χ, ?_, ?_⟩
    · have h := hn.conj_mem x hx χ⁻¹
      rwa [inv_inv] at h
    · change χ * (χ⁻¹ * x * χ) * χ⁻¹ = x
      group

theorem map_conj_inner_inf_centralizer {P : Type*} [Group P] (χ β : MulAut P) :
    (inner P ⊓ centralizer {β}).map (MulAut.conj χ).toMonoidHom =
      inner P ⊓ centralizer {χ * β * χ⁻¹} := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj χ).injective, map_conj_inner,
    map_conj_centralizer_singleton']

theorem mem_normalizer_of_normal_subgroupOf {G : Type*} [Group G] {N M : Subgroup G}
    (hNM : N ≤ M) (hn : (N.subgroupOf M).Normal) {y : G} (hy : y ∈ M) :
    y ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h := hn.conj_mem ⟨g, hNM hg⟩ (mem_subgroupOf.mpr hg) ⟨y, hy⟩
    exact mem_subgroupOf.mp h
  · intro hg
    have hgM : y * g * y⁻¹ ∈ M := hNM hg
    have h := hn.conj_mem ⟨_, hgM⟩ (mem_subgroupOf.mpr hg) ⟨y⁻¹, inv_mem hy⟩
    have h' := mem_subgroupOf.mp h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
      show y⁻¹ * (y * g * y⁻¹) * y = g by group] using h'

section Components

variable {G : Type*} [Group G]

theorem isComponentOf_of_normal_of_comm [Finite G] {Y N X : Subgroup G} (hNY : N ≤ Y)
    (hnorm : ∀ y ∈ Y, y ∈ normalizer (N : Set G))
    (hcomm : ∀ x ∈ Y, x ∈ centralizer (N : Set G) → ∀ y ∈ Y, y ∈ centralizer (N : Set G) →
      x * y = y * x)
    (hX : CFSG.Assembly.IsComponentOf X Y) : CFSG.Assembly.IsComponentOf X N := by
  have hX' := (isComponentOf_iff_isComponent_subgroupOf hX.1).mp hX
  have hNn : (N.subgroupOf Y).Normal := ⟨fun r hr y => by
    rw [mem_subgroupOf] at hr ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp (hnorm y y.2) r).mp hr⟩
  rcases CFSG.LocalCores.component_normal_subgroup hX' hNn with hle | hcom
  · refine isComponentOf_of_le hX (fun x hx => ?_) hNY
    have := hle (show (⟨x, hX.1 hx⟩ : Y) ∈ X.subgroupOf Y from hx)
    exact this
  · exfalso
    have hcent : ∀ x ∈ X, x ∈ centralizer (N : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro r hr
      have h1 := mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hcom (show (⟨x, hX.1 hx⟩ : Y) ∈
          X.subgroupOf Y from hx)) ⟨r, hNY hr⟩ (mem_subgroupOf.mpr hr)
      exact congrArg Subtype.val h1
    have : Group.IsPerfect X := ⟨hX.2.2.1⟩
    have : IsSimpleGroup (X ⧸ center X) := hX.2.2.2
    have : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative X (isMulCommutative_iff.mpr fun x y =>
      Subtype.ext (hcomm x (hX.1 x.2) (hcent x x.2) y (hX.1 y.2) (hcent y y.2)))

theorem exists_ne_commute_of_isQuasisimple {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) :
    ∃ x y : L, x * y ≠ y * x := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.2
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_contra hc
  push Not at hc
  exact Group.IsPerfect.not_isMulCommutative L (isMulCommutative_iff.mpr hc)

theorem eq_of_isComponentOf_simple {N X : Subgroup G} (hN : IsSimpleGroup N)
    (hX : CFSG.Assembly.IsComponentOf X N) : X = N := by
  have hX' := (isComponentOf_iff_isComponent_subgroupOf hX.1).mp hX
  have h := isComponent_eq_top_of_isSimpleGroup hX'
  exact le_antisymm hX.1 fun x hx => by
    have : (⟨x, hx⟩ : N) ∈ X.subgroupOf N := h ▸ mem_top _
    exact this

end Components

section Inner

variable {K : Type} [Field K] {n : ℕ}

theorem eq_one_of_sq_eq_one_charTwo [CharP K 2] {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (x + 1) ^ 2 = 0 := by linear_combination h + (x + 1) * h22
  have h2 : x + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
  rwa [CharTwo.add_eq_zero] at h2

theorem exists_involution_eq_conjAut [Finite K] [CharP K 2] (hn : 3 ≤ n) (A : GL (Fin n) K)
    (h2 : conjAut n K A ^ 2 = 1) (h1 : conjAut n K A ≠ 1) :
    ∃ t : projectiveSL n K, orderOf t = 2 ∧ conjAut n K A = MulAut.conj t := by
  have hA2 : conjAut n K (A * A) = 1 := by rw [map_mul, ← sq, h2]
  obtain ⟨c, hc⟩ := (UnbalancedCatalog.conjAut_eq_one_iff hn _).mp hA2
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact c.ne_zero hb
  set u : Kˣ := Units.mk0 b hb0 with hu
  set B : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) u⁻¹ * A with hB
  have hBB : B * B = 1 := by
    have hcomm : A * GeneralLinearGroup.scalar (Fin n) u⁻¹ =
        GeneralLinearGroup.scalar (Fin n) u⁻¹ * A :=
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u⁻¹ A).eq
    calc B * B = GeneralLinearGroup.scalar (Fin n) u⁻¹ * (A * GeneralLinearGroup.scalar (Fin n)
          u⁻¹) * A := by rw [hB]; group
      _ = GeneralLinearGroup.scalar (Fin n) u⁻¹ * GeneralLinearGroup.scalar (Fin n) u⁻¹ *
          (A * A) := by rw [hcomm]; group
      _ = 1 := by
          rw [← hc, ← map_mul, ← map_mul, ← map_one (GeneralLinearGroup.scalar (Fin n))]
          congr 1
          ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, hu, Units.val_mk0, Units.val_one,
            hb]
          field_simp
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    refine eq_one_of_sq_eq_one_charTwo ?_
    rw [sq, ← det_mul, ← Units.val_mul, hBB, Units.val_one, det_one]
  set g : SpecialLinearGroup (Fin n) K := ⟨B, hdet⟩ with hg
  have hcA : conjAut n K A = MulAut.conj (proj n K g) := by
    rw [← conjAut_toGL]
    have hBg : SpecialLinearGroup.toGL g = B := Units.ext rfl
    rw [hBg, hB, map_mul, conjAut_scalar, one_mul]
  refine ⟨proj n K g, orderOf_eq_prime ?_ ?_, hcA⟩
  · rw [sq, ← map_mul]
    have hgg : g * g = 1 := Subtype.ext (by
      change (B : Matrix (Fin n) (Fin n) K) * B = 1
      rw [← Units.val_mul, hBB, Units.val_one])
    rw [hgg, map_one]
  · intro ht
    apply h1
    rw [hcA, ht, map_one]

end Inner

end CFSG.ComponentClassification.OutcomeLocal
