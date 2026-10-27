module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.SeitzReduction.UnitaryPilot

open CFSG.GH74.Generic.S1.SymBlocksUni

open scoped Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem normHypForm_apply_coord (n : ℕ) (v : (F × F) × (Fin n → K)) :
    normHypForm E n v = hypPlane F v.1 + ∑ i, normQuad E (v.2 i) := by
  simp only [normHypForm, hypSum_apply, hypPlane_apply, Qn_apply]

@[expose] noncomputable def normPerm {n : ℕ} (hn : 3 ≤ n) :
    Equiv.Perm (Fin n) →* normOmega E n :=
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  codRestrictedρ (QR := hypPlane F) (QE := normQuad E)
    (LinearEquiv.refl F ((F × F) × (Fin n → K))) (normHypForm_polarBilin_nondegenerate E n)
    (normQuad_polarBilin_nondegenerate E) (normHypForm_apply_coord E n)
    (by rw [finrank_normHypForm E n]; omega)

private theorem normHypForm_apply_coord_refl (n : ℕ) :
    ∀ v : (F × F) × (Fin n → K),
      normHypForm E n v =
        hypPlane F ((LinearEquiv.refl F ((F × F) × (Fin n → K))) v).1 +
          ∑ i, normQuad E (((LinearEquiv.refl F ((F × F) × (Fin n → K))) v).2 i) :=
  normHypForm_apply_coord E n

private noncomputable def normPermAux {n : ℕ} (hn : 3 ≤ n) :
    Equiv.Perm (Fin n) →* normOmega E n :=
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  codRestrictedρ (QR := hypPlane F) (QE := normQuad E)
    (LinearEquiv.refl F ((F × F) × (Fin n → K))) (normHypForm_polarBilin_nondegenerate E n)
    (normQuad_polarBilin_nondegenerate E) (normHypForm_apply_coord_refl E n)
    (by rw [finrank_normHypForm E n]; omega)

private theorem normPerm_eq_aux {n : ℕ} (hn : 3 ≤ n) :
    normPerm E hn = normPermAux E hn := rfl

theorem normPerm_apply {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (v : (F × F) × (Fin n → K)) :
    ((normPerm E hn σ : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v =
        (v.1, fun j => v.2 (σ⁻¹ j)) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨⟨a, b⟩, x⟩ := v
  rw [normPerm_eq_aux E hn]
  unfold normPermAux
  dsimp only
  rw [coe_codRestrictedρ_apply, coordPermHom_apply]
  rfl

theorem normPerm_conj_normPlaneTorus {r p : ℕ} (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ f + 1) (χ : Multiplicative (ZMod p) →* Kˣ)
    (σ : Equiv.Perm (Fin r)) (u : Fin r → Multiplicative (ZMod p)) :
    normPerm E hr σ * normPlaneTorus E (by omega : 2 ≤ r) hpq χ u *
      (normPerm E hr σ)⁻¹ =
      normPlaneTorus E (by omega : 2 ≤ r) hpq χ (fun i => u (σ⁻¹ i)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [← map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [normPerm_apply E hr (σ⁻¹),
    normPlaneTorus_apply E (by omega : 2 ≤ r) hpq χ u,
    normPerm_apply E hr σ,
    normPlaneTorus_apply E (by omega : 2 ≤ r) hpq χ (fun i => u (σ⁻¹ i))]
  refine Prod.ext rfl (funext fun j => ?_)
  simp [inv_inv]

@[expose] noncomputable def normBlock (n : ℕ) (S : Finset (Fin n)) : Subgroup (normOmega E n) :=
  (supportedDerived (normHypForm E n)
    (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)).subgroupOf (normOmega E n)

theorem normBlock_mono (n : ℕ) : Monotone (normBlock E n) := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  intro S T hST
  simp only [normBlock]
  have hsup : coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S ≤
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) T := by
    simp only [coordSupport]
    exact sup_le_sup_left (Finset.sup_mono hST) _
  refine Subgroup.subgroupOf_mono (normOmega E n)
    (supportedDerived_le_supportedDerived_of_le hsup ?_ ?_)
  · exact coordSupport_nondegenerate (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (hψ := normHypForm_apply_coord E n)
      (hQ := normHypForm_polarBilin_nondegenerate E n)
      (hQE := normQuad_polarBilin_nondegenerate E) S
  · exact coordSupport_nondegenerate (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (hψ := normHypForm_apply_coord E n)
      (hQ := normHypForm_polarBilin_nondegenerate E n)
      (hQE := normQuad_polarBilin_nondegenerate E) T

theorem normBlock_univ (n : ℕ) : normBlock E n Finset.univ = ⊤ := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  simp only [normBlock]
  rw [coordSupport_univ, coordAnchor_sup_coordActive,
    CFSG.RankThree.PartOne.supportedDerived_top_eq_orthDerived
      (normHypForm_polarBilin_nondegenerate E n)]
  rw [Subgroup.subgroupOf_self]

theorem map_normBlock_normPerm {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    (normBlock E n S).map (MulAut.conj (normPerm E hn σ)).toMonoidHom =
      normBlock E n (S.image σ) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  simpa only [normBlock, normPerm] using
    (map_coordSupport_subgroup (QR := hypPlane F) (QE := normQuad E)
      (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (normHypForm_polarBilin_nondegenerate E n) (normQuad_polarBilin_nondegenerate E)
      (normHypForm_apply_coord E n) (by rw [finrank_normHypForm E n]; omega) σ S)

theorem normPerm_commute_normBlock_pair {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (σ : Equiv.Perm (Fin n)) (x : normBlock E n {i, j}) (hi : σ i = i) (hj : σ j = j) :
    normPerm E hn σ * (x : normOmega E n) = (x : normOmega E n) * normPerm E hn σ := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  rw [normPerm_eq_aux E hn]
  unfold normPermAux
  let ρ : normOmega E n :=
    codRestrictedρ (QR := hypPlane F) (QE := normQuad E)
      (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (normHypForm_polarBilin_nondegenerate E n) (normQuad_polarBilin_nondegenerate E)
      (normHypForm_apply_coord_refl E n) (by rw [finrank_normHypForm E n]; omega) σ
  have hcomm : ρ * (x : normOmega E n) * ρ⁻¹ = (x : normOmega E n) :=
    (codRestrictedρ_centralizes_pair (QR := hypPlane F) (QE := normQuad E)
      (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (hQ := normHypForm_polarBilin_nondegenerate E n)
      (hQE := normQuad_polarBilin_nondegenerate E)
      (hψ := normHypForm_apply_coord_refl E n)
      (h8 := by rw [finrank_normHypForm E n]; omega) hij σ hi hj) x x.2
  have hmul : ρ * (x : normOmega E n) = (x : normOmega E n) * ρ := by
    calc ρ * (x : normOmega E n) = (ρ * (x : normOmega E n) * ρ⁻¹) * ρ := by group
      _ = (x : normOmega E n) * ρ := by rw [hcomm]
  exact hmul

private theorem coe_suEquiv_apply {n : ℕ} (h : UnitaryFieldData 2 f K)
    (g : SUid (unitaryInvolution K 2 f) n) :
    (((suEquiv h n g : unitarySU 2 f K n) : GL (Fin n) K)) = (g : GL (Fin n) K) :=
  MulEquiv.subgroupCongr_apply _ g

private theorem coe_suEquiv_symm {n : ℕ} (h : UnitaryFieldData 2 f K)
    (g : unitarySU 2 f K n) :
    (((suEquiv h n).symm g : SUid (unitaryInvolution K 2 f) n) : GL (Fin n) K) =
      (g : GL (Fin n) K) :=
  MulEquiv.subgroupCongr_symm_apply _ g

private theorem suEmb_apply_smul (m : ℕ) (g : SUid (unitaryInvolution K 2 f) m)
    (p : (F × F) × (Fin m → K)) :
    ((suEmb E m g : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) p =
      (p.1, ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ p.2) := by
  rw [suEmb_apply, CFSG.ClassicalGroups.Unitary.smul_def]

theorem normPerm_eq_uniEmb (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 3 ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    normPerm E hn σ = uniEmb E h n (permSUHom h σ) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [normPerm_apply]
  change (v.1, fun j => v.2 (σ⁻¹ j)) =
    ((suEmb E n ((suEquiv h n).symm (permSUHom h σ)) : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v
  rw [suEmb_apply_smul, coe_suEquiv_symm, permSUHom_apply, coe_permSU,
    Matrix.permMatrix_mulVec]
  exact Prod.ext rfl (funext fun j => rfl)

theorem exists_perm_castSucc {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : σ (Fin.last m) = Fin.last m) :
    ∃ σ' : Equiv.Perm (Fin m), ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i) := by
  have hne : ∀ i : Fin m, σ (Fin.castSucc i) ≠ Fin.last m := by
    intro i hi
    have hinv : σ.symm (Fin.last m) = Fin.last m := by
      simpa using (congrArg σ.symm hσ).symm
    have h2 : Fin.castSucc i = Fin.last m := by
      simpa [hinv] using congrArg σ.symm hi
    exact Fin.castSucc_ne_last i h2
  let f : Fin m → Fin m := fun i => (σ (Fin.castSucc i)).castPred (hne i)
  have hf : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (f i) := fun i =>
    (Fin.castSucc_castPred (σ (Fin.castSucc i)) (hne i)).symm
  have hinj : Function.Injective f := by
    intro i j hij
    have h : σ (Fin.castSucc i) = σ (Fin.castSucc j) := by rw [hf i, hf j, hij]
    exact Fin.castSucc_injective m (σ.injective h)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

private theorem perm_last_eq_last {m : ℕ} {σ' : Equiv.Perm (Fin m)}
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    σ (Fin.last m) = Fin.last m := by
  obtain ⟨x, hx⟩ := σ.surjective (Fin.last m)
  rcases Fin.eq_castSucc_or_eq_last x with ⟨i, rfl⟩ | rfl
  · rw [hσ i] at hx
    exact absurd hx (Fin.castSucc_ne_last (σ' i))
  · exact hx

private theorem perm_inv_apply_castSucc {m : ℕ} {σ' : Equiv.Perm (Fin m)}
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i))
    (a : Fin m) : σ⁻¹ (Fin.castSucc a) = Fin.castSucc (σ'⁻¹ a) := by
  show σ.symm (Fin.castSucc a) = Fin.castSucc (σ'.symm a)
  rw [Equiv.symm_apply_eq, hσ (σ'.symm a), Equiv.apply_symm_apply]

private theorem blkMat_permMatrix_castSucc {R : Type} [Field R] {m : ℕ}
    {σ' : Equiv.Perm (Fin m)} {σ : Equiv.Perm (Fin (m + 1))}
    (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    blkMat (Fin.castSucc : Fin m → Fin (m + 1)) ((σ'⁻¹).permMatrix R) =
      (σ⁻¹).permMatrix R := by
  have hlast : σ (Fin.last m) = Fin.last m := perm_last_eq_last hσ
  have hinv_last : σ⁻¹ (Fin.last m) = Fin.last m := by
    show σ.symm (Fin.last m) = Fin.last m
    simpa using (congrArg σ.symm hlast).symm
  have hinv_cast : ∀ a : Fin m, σ⁻¹ (Fin.castSucc a) = Fin.castSucc (σ'⁻¹ a) :=
    fun a => perm_inv_apply_castSucc hσ a
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
  · rw [blkMat_apply_ι (ι := Fin.castSucc) (Fin.castSucc_injective m)
        ((σ'⁻¹).permMatrix R) a b,
      CFSG.RankThree.Classical.permMatrix_apply',
      CFSG.RankThree.Classical.permMatrix_apply', hinv_cast a]
    by_cases h : σ'⁻¹ a = b
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hq => h (Fin.castSucc_injective m hq))]
  · rw [blkMat_apply_of_not_mem_right ((σ'⁻¹).permMatrix R) (Fin.castSucc a)
        (j := Fin.last m) (fun y => (Fin.castSucc_ne_last y).symm),
      CFSG.RankThree.Classical.permMatrix_apply', hinv_cast a, Matrix.one_apply]
    simp [Fin.castSucc_ne_last]
  · rw [blkMat_apply_of_not_mem_left ((σ'⁻¹).permMatrix R) (i := Fin.last m)
        (fun x => (Fin.castSucc_ne_last x).symm) (Fin.castSucc b),
      CFSG.RankThree.Classical.permMatrix_apply', hinv_last, Matrix.one_apply]
  · rw [blkMat_apply_of_not_mem_left ((σ'⁻¹).permMatrix R) (i := Fin.last m)
        (fun x => (Fin.castSucc_ne_last x).symm) (Fin.last m),
      CFSG.RankThree.Classical.permMatrix_apply', hinv_last, Matrix.one_apply]

theorem uniCast_permSUHom (h : UnitaryFieldData 2 f K) {m : ℕ} (σ' : Equiv.Perm (Fin m))
    (σ : Equiv.Perm (Fin (m + 1))) (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    uniCast h m (permSUHom h σ') = permSUHom h σ := by
  apply Subtype.ext
  apply Units.ext
  have hR : (((permSUHom h σ : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = (σ⁻¹).permMatrix K := by
    rw [permSUHom_apply, coe_permSU]
  rw [hR]
  unfold uniCast
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [coe_suEquiv_apply, coe_coe_blkEmb, coe_suEquiv_symm, permSUHom_apply, coe_permSU]
  exact blkMat_permMatrix_castSucc hσ

theorem normPerm_eq_normOmegaCast (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 2 ≤ m)
    (σ' : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    normPerm E (by omega : 3 ≤ m + 1) σ =
      normOmegaCast E (Nat.le_succ m) (uniEmb E h m (permSUHom h σ')) := by
  rw [normPerm_eq_uniEmb E h (by omega) σ]
  rw [← uniCast_permSUHom h σ' σ hσ]
  exact uniEmb_uniCast E h m (permSUHom h σ')

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
