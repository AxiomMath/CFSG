module

public import CFSG.LieType.Chevalley.E6A5CubeImages
public import CFSG.LieType.Chevalley.C2E6A5CubeFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.C2E6Std (setA jA rootA i6 eq_one_of_smul_rootA single_eq_rootA_sub
  single_one_eq_rootA labA smul_rootA_eq_of_not_precedes isRoot_rootA)
open scoped Pointwise

variable {K : Type} [Field K]

theorem eq_one_of_mem_torusGroup_of_fix
    {t : ModGL Tag.E6 K} (ht : t ∈ torusGroup Tag.E6 K)
    (hfix : ∀ j, (t : Module.End K (RootModule Tag.E6 K)) (vecA K j) = vecA K j) : t = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hχ : ∀ j, rootChar l (rootA j) = 1 := fun j => by
    have h1 := hfix j
    change rootDiag l (rootVec Tag.E6 K (rootA j)) = _ at h1
    rw [rootDiag_rootVec l (isRoot_rootA j)] at h1
    have hne : rootVec Tag.E6 K (rootA j) ≠ 0 := by
      rw [C2E6Std.rootVec_eq_single (isRoot_rootA j)]
      exact Finsupp.single_ne_zero.2 one_ne_zero
    exact Units.ext (smul_left_injective K hne (h1.trans (one_smul K _).symm))
  have hl : l = 1 := funext fun i => by
    have h1 : rootChar l (Pi.single i 1) = l i := by
      have := rootChar_nsmul_single l i 1
      rwa [one_smul, pow_one] at this
    rw [← h1, Pi.one_apply]
    by_cases hi : i = i6 1
    · rw [hi, single_one_eq_rootA, hχ]
    · obtain ⟨a, b, hab⟩ := single_eq_rootA_sub i hi
      rw [hab, rootChar_sub, hχ, hχ, inv_one, mul_one]
  rw [hl, rootDiagUnit_one]

theorem list_prod_weylElt_rootVec
    (ω : List (Fin Tag.E6.rank)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt Tag.E6 K i 1).prod : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      ε • rootVec Tag.E6 K ((coxeterSystem Tag.E6).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, Tag.E6.cartan i j * ((coxeterSystem Tag.E6).wordProd ω • β) j) : Kˣ) :
        K)), mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem Tag.E6).wordProd (i :: ω) • β =
        reflect Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

theorem canonicalRep_rootVec
    (w : WeylGroup Tag.E6) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K β) = ε • rootVec Tag.E6 K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_rootVec ω hβ

theorem borel_apply_vecA_eq_zero
    {c : ModGL Tag.E6 K} (hc : c ∈ borelGroup Tag.E6 K)
    {j j' : Fin 20} (h : (labA j).Precedes (labA j')) :
    (c : Module.End K (RootModule Tag.E6 K)) (vecA K j) (labA j') = 0 := by
  have := (triangular_borel_structure.{0, 0} Tag.E6 K).2.2.2.2.2.2.2.2.2.1 c hc (labA j') (labA j) h
  rwa [vecA, C2E6Std.rootVec_eq_single (isRoot_rootA j)]

theorem cubeHom_eq_one_of_diag_eq_unitriangular {δ υ : SpecialLinearGroup (Fin 6) K}
    (hδ : δ ∈ diagSL K) (hυ : υ ∈ LinearFlag.unitriangular 6 K) (h : cubeHom δ = cubeHom υ) :
    cubeHom υ = 1 := by
  have h1 : cubeHom (δ⁻¹ * υ) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨l, -, hl⟩ := (cubeHom_eq_one_iff _).1 h1
  obtain ⟨d, hd⟩ := mem_diagSL.mp hδ
  have e1 : ((δ * (δ⁻¹ * υ) : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (δ : Matrix (Fin 6) (Fin 6) K) *
        ((δ⁻¹ * υ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := rfl
  rw [mul_inv_cancel_left] at e1
  have hυd : (υ : Matrix (Fin 6) (Fin 6) K) = diagonal (fun i => d i * l) := by
    rw [e1, hd, hl, Matrix.smul_one_eq_diagonal, diagonal_mul_diagonal]
  have hυ1 : υ = 1 := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show (υ : Matrix (Fin 6) (Fin 6) K) i j = (1 : Matrix (Fin 6) (Fin 6) K) i j
    by_cases hij : i = j
    · subst hij
      rw [(LinearFlag.mem_unitriangular.mp hυ).2 i, one_apply_eq]
    · rw [hυd, diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [hυ1, map_one]

theorem psiA_injective [Finite K] :
    Function.Injective (psiA K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix := (psiA_eq_one_iff g).mp hg
  have hgS : (g : ModGL Tag.E6 K) ∈ (subsystemGroup Tag.E6 K setA : Set (ModGL Tag.E6 K)) := g.2
  rw [(subsystem_root_group_bruhat Tag.E6 K setA).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E6 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E6 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E6 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ groupA K := parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K)
    (A := setA) (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
      (vecA K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        (vecA K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E6) K w = b⁻¹ * (g : ModGL Tag.E6 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_moduleA_of_mem_groupA (inv_mem hvS) _ (vecA_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', rootA j' = w • rootA j → ¬(labA j).Precedes (labA j') := by
    intro j j' hj' hp
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec (K := K) w (isRoot_rootA j)
    have h0 := borel_apply_vecA_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hp
    rw [← hn j, hne, ← hj', C2E6Std.rootVec_eq_single (isRoot_rootA j'), Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_rootA (smul_rootA_eq_of_not_precedes hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (torusA K : Set (ModGL Tag.E6 K)) * (unipotentA K : Set (ModGL Tag.E6 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E6) (K := K) (A := setA)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  set t' : groupA K := ⟨t, torusA_le_groupA ht⟩
  set u' : groupA K := ⟨u, unipotentA_le_groupA hu⟩
  have hgtu : g = t' * u' := Subtype.ext hgbv.symm
  have hψ : psiA K t' * psiA K u' = 1 := by rw [← map_mul, ← hgtu, hg]
  obtain ⟨δ, hδ, hδt⟩ : psiA K t' ∈ (diagSL K).map cubeHom :=
    map_psiA_torusA_le (Subgroup.mem_map_of_mem _ (show t' ∈ (torusA K).subgroupOf (groupA K) from ht))
  obtain ⟨υ, hυ, hυu⟩ : psiA K u' ∈ (LinearFlag.unitriangular 6 K).map cubeHom := by
    rw [← map_psiA_unipotentA]
    exact Subgroup.mem_map_of_mem _ hu
  have hcube : cubeHom δ⁻¹ = cubeHom υ := by
    rw [map_inv, hδt, hυu]
    exact (eq_inv_of_mul_eq_one_right hψ).symm
  have hυ1 := cubeHom_eq_one_of_diag_eq_unitriangular (inv_mem hδ) hυ hcube
  have hu1 : psiA K u' = 1 := by rw [← hυu, hυ1]
  have hu'1 : u' = 1 := psiA_injOn_unipotentA (show u' ∈ (unipotentA K).subgroupOf (groupA K) from hu)
    (one_mem _) (hu1.trans (map_one (psiA K)).symm)
  have ht1 : psiA K t' = 1 := by rw [hu1, mul_one] at hψ; exact hψ
  have ht'1 : t' = 1 := by
    refine Subtype.ext ?_
    refine eq_one_of_mem_torusGroup_of_fix (subsystemTorus_le_torusGroup ht) fun j => ?_
    exact (psiA_eq_one_iff t').mp ht1 _ (vecA_mem j)
  rw [hgtu, hu'1, ht'1, mul_one]

end CFSG.LieType.Chevalley.E6A5Cube
