module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCases
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv spCentEquiv_apply linA linA_apply
  linA_mul_self form_similitude)

theorem inner_psp_component_cases {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSp r p f)
    (hr : 3 ≤ r) (A : gsp r K) (hA : orderOf (conjAut r K A) = 2)
    {L : Subgroup (fixedSubgroup (conjAut r K A))} (hL : IsComponent L) :
    (∃ z ∈ L, (∀ y ∈ L, z * y = y * z) ∧ z * z = 1 ∧ z ≠ 1) ∨
    CentralModel p .PSL r f L ∨ (Even r ∧ CentralModel p .PSp (r / 2) (2 * f) L) ∨
    CentralModel p .PSU r f L := by
  have hf : 1 ≤ f := hadm.2.1
  have hA1 : conjAut r K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp r K A (conjSp r K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut r K A (conjAut r K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj r K).ker ≤ center (StatedSp r K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (fixedSubgroup (conjAut r K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut r K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut r K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQR, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  set Q := ⁅R.comap (proj r K), R.comap (proj r K)⁆ with hQdef
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  let Φ := (MulEquiv.subgroupCongr
    (show fixedSubgroup (conjSp r K A) = spCent r K A from rfl)).trans (spCentEquiv A)
  have hMc := LocalCores.isComponent_map_mulEquiv Φ hQ'
  have htrans : ∀ {t : StatedLieTag} {n f' : ℕ},
      CentralModel p t n f' ((Q.subgroupOf (fixedSubgroup (conjSp r K A))).map Φ.toMonoidHom) →
        CentralModel p t n f' L := fun h =>
    ((((h.of_mulEquiv ((Q.subgroupOf (fixedSubgroup (conjSp r K A))).equivMapOfInjective
      Φ.toMonoidHom Φ.injective)).of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hQ.1).symm).of_centerQuotient_equiv eQR.symm).of_mulEquiv
      (L.equivMapOfInjective (fixedSubgroup (conjAut r K A)).subtype (subtype_injective _)))
  rcases similitudeCentralizer_component_cases hp hp2 hf hK hr finrank_standard
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hMc with ⟨z, hzM, hzc, hzz, hzns⟩ | h | ⟨he, h⟩ | h
  ·
    left
    obtain ⟨w, hwQ, hwz0⟩ := hzM
    have hwz : Φ w = z := hwz0
    have hwQ' : ((w : fixedSubgroup (conjSp r K A)) : StatedSp r K) ∈ Q := hwQ
    set t : StatedProj (StatedSp r K) := proj r K (w : StatedSp r K) with htdef
    have htR : t ∈ R := hQR ▸ Subgroup.mem_map_of_mem _ hwQ'
    obtain ⟨z', hz'L, hz't0⟩ := Subgroup.mem_map.1 htR
    have hz't : (z' : StatedProj (StatedSp r K)) = t := hz't0
    refine ⟨z', hz'L, fun y hy => ?_, ?_, ?_⟩
    ·
      have hyR : (y : StatedProj (StatedSp r K)) ∈ R := Subgroup.mem_map_of_mem _ hy
      rw [← hQR] at hyR
      obtain ⟨u, huQ, huy⟩ := Subgroup.mem_map.1 hyR
      have huB : u ∈ fixedSubgroup (conjSp r K A) := hQ.1 huQ
      have hu' : (⟨u, huB⟩ : fixedSubgroup (conjSp r K A)) ∈
          Q.subgroupOf (fixedSubgroup (conjSp r K A)) := huQ
      have h1 := hzc _ (Subgroup.mem_map_of_mem Φ.toMonoidHom hu')
      rw [← hwz] at h1
      have h2 : w * ⟨u, huB⟩ = ⟨u, huB⟩ * w := by
        apply Φ.injective
        rw [map_mul, map_mul]
        exact h1
      have h3 := congrArg (fun g : fixedSubgroup (conjSp r K A) =>
        proj r K (g : StatedSp r K)) h2
      simp only [Subgroup.coe_mul, map_mul] at h3
      apply Subtype.ext
      change (z' : StatedProj (StatedSp r K)) * y = y * z'
      rw [hz't, ← huy]
      exact h3
    ·
      have h1 : w * w = 1 := by
        apply Φ.injective
        rw [map_mul, hwz, hzz, map_one]
      apply Subtype.ext
      change (z' : StatedProj (StatedSp r K)) * z' = 1
      rw [hz't, htdef, ← map_mul]
      change proj r K ((w * w : fixedSubgroup (conjSp r K A)) : StatedSp r K) = 1
      rw [h1]
      exact map_one _
    ·
      intro h1
      have h2 : t = 1 := by
        rw [← hz't, h1]
        rfl
      have h3 : (w : StatedSp r K) ∈ (proj r K).ker := h2
      rw [ker_proj, Subgroup.mem_subgroupOf] at h3
      obtain ⟨c', hc'⟩ := h3
      apply hzns c'
      rw [← hwz]
      refine LinearMap.ext fun x => ?_
      change ((spCentEquiv A ⟨_, w.2⟩ : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) x = _
      rw [spCentEquiv_apply]
      change ((((w : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x = (c' : K) • x
      rw [← hc']
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  · exact Or.inr (Or.inl (htrans h))
  · exact Or.inr (Or.inr (Or.inl ⟨he, htrans h⟩))
  · exact Or.inr (Or.inr (Or.inr (htrans h)))

end CFSG.ComponentClassification.CatLeafProof.X10Sp
