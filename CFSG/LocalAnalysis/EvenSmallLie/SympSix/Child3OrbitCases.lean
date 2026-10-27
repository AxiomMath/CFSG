module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Patterns
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Subdegree
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegreeEightRankOneExclusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module Matrix MulAction CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Labels

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (hinf : L ⊓ zpowers z = ⊥)

@[expose] def rankOneOrbit (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G) : Set G :=
  {x | ∃ (v : Fin 3 → ZMod 2) (a : G) (ha : a ∈ L), x = z * a ∧
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 (vecMulVec v v) 0 1}

theorem vecMulVec_mem (v : Fin 3 → ZMod 2) : vecMulVec v v ∈ binarySymMatrices 3 := by
  rw [mem_binarySymMatrices, transpose_vecMulVec]

theorem z_mul_tauHom (B : 𝕍) :
    z * tauHom φ he (Multiplicative.ofAdd B) =
      radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) := by
  rw [radHom_apply, zPow_one, mul_comm_z hzC (tauHom_mem φ he _)]

include hinf in
theorem labSet_rankOneOrbit : labSet φ he hzC hz (rankOneOrbit φ e z) = patternSet {0} := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  constructor
  · rintro ⟨v, a, ha, hx, hmat⟩
    have haτ := eq_tauHom_of_toMatrix φ he ha ⟨vecMulVec v v, vecMulVec_mem v⟩ hmat
    rw [haτ, z_mul_tauHom φ he hzC hz] at hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (lab_ext φ he hzC hz hinf hx)
    by_cases hv : v = 0
    · subst hv
      refine Or.inl ⟨(kindOf_eq_zero_iff _).2 (Subtype.ext ?_), rfl⟩
      ext i j
      simp [vecMulVec_apply]
    · refine Or.inr ⟨0, Finset.mem_singleton_self 0, rfl, ?_⟩
      exact (kindOf_eq_one_iff _).2 ((sym_rank_one_iff _).2 ⟨v, hv, rfl⟩)
  · rintro (⟨hk, hε⟩ | ⟨i, hi, hε, hk⟩)
    · rw [kindOf_eq_zero_iff] at hk
      dsimp only at hk hε
      subst hk hε
      refine ⟨0, tauHom φ he (Multiplicative.ofAdd 0), tauHom_mem φ he _, ?_, ?_⟩
      · rw [z_mul_tauHom φ he hzC hz]
      · rw [toMatrix_tauHom]
        congr 1
    · rw [Finset.mem_singleton] at hi
      subst hi
      dsimp only at hk hε
      obtain ⟨v, -, hv⟩ := (sym_rank_one_iff B).1 ((kindOf_eq_one_iff B).1 hk)
      subst hε
      refine ⟨v, tauHom φ he (Multiplicative.ofAdd B), tauHom_mem φ he _, ?_, ?_⟩
      · rw [z_mul_tauHom φ he hzC hz]
        rfl
      · rw [toMatrix_tauHom, ← hv]
        rfl

include he in
theorem rankOneOrbit_subset : rankOneOrbit φ e z ⊆ (radSub φ z e : Set G) := by
  rintro x ⟨v, a, ha, rfl, hmat⟩
  rw [eq_tauHom_of_toMatrix φ he ha ⟨vecMulVec v v, vecMulVec_mem v⟩ hmat]
  exact mul_mem (mem_sup_right (mem_zpowers z))
    (mem_sup_left ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩))

include hinf in
theorem labSet_altEight :
    labSet φ he hzC hz (z • tauSet φ e (fun B => ∀ i, B i i = 0)) = patternSet {1} := by
  rw [labSet_smul_tauSet φ he hzC hz hinf]
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [Set.mem_ofPred_eq]
  rw [alt_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

include hinf in
theorem labSet_lagrangian :
    labSet φ he hzC hz (z • tauSet φ e (fun _ => True)) = patternSet {0, 1, 2, 3} := by
  rw [labSet_smul_tauSet φ he hzC hz hinf]
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [Set.mem_ofPred_eq, and_true]
  generalize kindOf B = k
  revert k ε
  decide

end Labels

theorem orbit_cases {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {T : Sylow 2 (centralizer (L : Set G))} {z : G} (hS : Setting L T z)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) :
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) ∨
      conjClass (sp6N₂ φ e z) z = z • tauSet φ e (fun B => ∀ i, B i i = 0) := by
  classical
  obtain ⟨-, hzC, -, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hS.oddCore_eq hS.standard
      hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem hS.order hS.core_z
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, -, -, -, ⟨σ, hσs, -, -, hσ⟩, -, -, -, -, -, hpat, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  have hΛ := labSet_eq_patternSet φ he hzC hS.order hinf hpat
  set S := Finset.univ.filter fun i =>
    piece i ⊆ labSet φ he hzC hS.order (conjClass (radN φ e z) z) with hSdef
  have hcard : Nat.card (conjClass (radN φ e z) z) = 1 + ∑ i ∈ S, pieceCard i := by
    rw [← card_labSet φ he hzC hS.order (conjClass_subset_radSub φ) hinf, hΛ, card_patternSet]
  obtain ⟨-, -, -, -, -, -, -, hsizes, -⟩ := hpat
  rw [hcard] at hsizes
  have hR : ∀ P : M₃ → Prop, z • tauSet φ e P ⊆ (radSub φ z e : Set G) :=
    smul_tauSet_subset_radSub φ he
  have hobs := fun {Λ : Set (𝕍 × ZMod 2)} => labSet_conjClass_ne_of_obstruction (Λ := Λ) φ he hzC
    hS.order hinf
  rcases patternSet_cases S hsizes with hS' | hS' | hS' | hS' | hS' | hS' | hS' | hS' | hS' |
    hS' | hS' | hS' <;> rw [hS'] at hΛ
  ·
    exfalso
    have hΩ : conjClass (radN φ e z) z = rankOneOrbit φ e z :=
      eq_of_labSet_eq φ he hzC hS.order (conjClass_subset_radSub φ) (rankOneOrbit_subset φ he)
        (hΛ.trans (labSet_rankOneOrbit φ he hzC hS.order hinf).symm)
    obtain ⟨ν, -, -, -, -, -, -, hab⟩ :=
      standard_binary_symplectic_six_full_rank_one_eight_orbit_exclusion hS.oddCore_eq
        hS.standard hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem hS.order hS.core_z hb
        hnd hV φ (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl hΩ
    obtain ⟨x, y, hxy⟩ := hS.nonab
    exact hxy (hab hS.simple x y)
  ·
    exact Or.inr (eq_of_labSet_eq φ he hzC hS.order (conjClass_subset_radSub φ) (hR _)
      (hΛ.trans (labSet_altEight φ he hzC hS.order hinf).symm))
  · exact absurd (hΛ.trans patternSet_fifteen) (hobs fun H _ _ =>
      binary_symmetric_three_fifteen_point_linear_orbit_obstruction.2.2.2.2 H)
  · exact absurd hΛ (labSet_conjClass_ne_subdegree φ he hzC hS.order hinf σ hσs hσ (Or.inl rfl))
  · exact absurd hΛ (labSet_conjClass_ne_subdegree φ he hzC hS.order hinf σ hσs hσ (Or.inr rfl))
  · exact absurd (hΛ.trans patternSet_X₁) (hobs fun H _ _ =>
      binary_symmetric_three_mixed_layer_orbit_obstructions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
        (by simp) H)
  · exact absurd (hΛ.trans patternSet_X₂) (hobs fun H _ _ =>
      binary_symmetric_three_mixed_layer_orbit_obstructions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
        (by simp) H)
  · exact absurd (hΛ.trans patternSet_singular) (hobs fun H _ _ =>
      binary_symmetric_three_singular_set_affine_orbit_obstruction.2.2.2 H)
  ·
    refine Or.inl (eq_of_labSet_eq φ he hzC hS.order (conjClass_subset_radSub φ) ?_ ?_)
    · rw [show (sp6A₂ φ e : Set G) = tauSet φ e (fun _ => True) from hA]
      exact hR _
    · rw [show (sp6A₂ φ e : Set G) = tauSet φ e (fun _ => True) from hA,
        labSet_lagrangian φ he hzC hS.order hinf]
      exact hΛ
  · exact absurd (hΛ.trans patternSet_Y₁) (hobs fun H _ _ =>
      binary_symmetric_three_mixed_layer_orbit_obstructions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
        (by simp) H)
  · exact absurd (hΛ.trans patternSet_Y₂) (hobs fun H _ _ =>
      binary_symmetric_three_mixed_layer_orbit_obstructions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
        (by simp) H)
  · exact absurd (hΛ.trans patternSet_Z) (hobs fun H _ _ =>
      binary_symmetric_three_mixed_layer_orbit_obstructions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
        (by simp) H)

end CFSG.EvenSmallLie.Child3
