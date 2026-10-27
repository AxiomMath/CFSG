module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eSpSim
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv spCentEquiv_apply linA linA_apply
  linA_mul_self form_similitude)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel CentralModel.of_mulEquiv
  CentralModel.of_centerQuotient_equiv)

theorem sp_comp_types {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hr : 2 ≤ r) (A' : gsp r K)
    (hAsp : (A' : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K) (hA : orderOf (conjAut r K A') = 2)
    {L : Subgroup (fixedSubgroup (conjAut r K A'))} (hL : IsComponent L) :
    (∃ k, 1 ≤ k ∧ Nonempty (L ≃* StatedSp k K)) ∨ CentralModel p .PSL r f L ∨
      CentralModel p .PSU r f L := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hA1 : conjAut r K A' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut r K A' * conjAut r K A' = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  have hAns : ∀ c : Kˣ,
      (A' : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A').2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A' * A')).1
    (by rw [map_mul, hA2])
  set M := ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp r K A' (conjSp r K A' x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut r K A' (conjAut r K A' s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj r K).ker ≤ center (StatedSp r K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A' x).symm)
  set R := L.map (fixedSubgroup (conjAut r K A')).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut r K A')) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut r K A')) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQR, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  set Q := ⁅R.comap (proj r K), R.comap (proj r K)⁆ with hQdef
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hAμ : ∀ v w, pairedSympForm K r (((linA A' : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A' : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    have hJ : ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
        formJ r K * ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        (1 : K) • formJ r K := by
      rw [one_smul]
      exact SymplecticTorusWeyl.mem_statedSp_iff.mp hAsp
    rw [linA_apply, linA_apply, form_similitude hJ, one_mul]
  let Φ := (MulEquiv.subgroupCongr
    (show fixedSubgroup (conjSp r K A') = spCent r K A' from rfl)).trans (spCentEquiv A')
  have hMc := LocalCores.isComponent_map_mulEquiv Φ hQ'
  have htrans : ∀ {t : StatedLieTag} {n f' : ℕ},
      CentralModel p t n f' ((Q.subgroupOf (fixedSubgroup (conjSp r K A'))).map Φ.toMonoidHom) →
        CentralModel p t n f' L := fun h =>
    ((((h.of_mulEquiv ((Q.subgroupOf (fixedSubgroup (conjSp r K A'))).equivMapOfInjective
      Φ.toMonoidHom Φ.injective)).of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hQ.1).symm).of_centerQuotient_equiv eQR.symm).of_mulEquiv
      (L.equivMapOfInjective (fixedSubgroup (conjAut r K A')).subtype (subtype_injective _)))
  rcases sim_comp_types hp hp2 hf hK hr finrank_standard pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hMc with ⟨k, hk, ⟨eS⟩, hscal⟩ | h | h
  ·
    left
    refine ⟨k, hk, ⟨?_⟩⟩
    have hinj : Function.Injective ((proj r K).comp Q.subtype) := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have hyk : (y : StatedSp r K) ∈ (proj r K).ker := hy
      rw [ker_proj, Subgroup.mem_subgroupOf] at hyk
      obtain ⟨c', hc'⟩ := hyk
      have hyB : (y : StatedSp r K) ∈ fixedSubgroup (conjSp r K A') := hQ.1 y.2
      have hmem : Φ ⟨y, hyB⟩ ∈ (Q.subgroupOf (fixedSubgroup (conjSp r K A'))).map Φ.toMonoidHom :=
        ⟨⟨y, hyB⟩, y.2, rfl⟩
      have hc1 := hscal _ hmem (c' : K) (by
        refine LinearMap.ext fun x => ?_
        change ((spCentEquiv A' ⟨_, hyB⟩ : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) x = _
        rw [spCentEquiv_apply]
        change ((((y : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x = (c' : K) • x
        rw [← hc']
        ext i
        simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply])
      have hc1' : c' = 1 := Units.ext hc1
      apply Subtype.ext
      apply Subtype.ext
      change ((y : StatedSp r K) : GL (Fin r ⊕ Fin r) K) = 1
      rw [← hc', hc1', map_one]
    have hrange : ((proj r K).comp Q.subtype).range = R := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hQR]
    exact ((L.equivMapOfInjective (fixedSubgroup (conjAut r K A')).subtype
      (subtype_injective _)).trans ((MulEquiv.subgroupCongr hrange).symm.trans
        (MonoidHom.ofInjective hinj).symm)).trans
      (((Subgroup.subgroupOfEquivOfLe hQ.1).symm.trans
        ((Q.subgroupOf (fixedSubgroup (conjSp r K A'))).equivMapOfInjective Φ.toMonoidHom
          Φ.injective)).trans eS)
  · exact Or.inr (Or.inl (htrans h))
  · exact Or.inr (Or.inr (htrans h))

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp
