module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDSetting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FivePocket

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] noncomputable def sec4FDEquiv : omegaGroup sec4IQ_nondegenerate ≃* Sec4IOmega :=
  omegaProjEquiv sec4IQ_nondegenerate
    (piOrth_not_mem_omegaGroup_seven sec4IQ_nondegenerate sec4IQ_finrank)

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def sec4FDCover0 (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) :
    ↥L →* ↥(omegaGroup sec4IQ_nondegenerate) :=
  (sec4FDEquiv.symm : Sec4IOmega ≃* ↥(omegaGroup sec4IQ_nondegenerate)).toMonoidHom.comp
    (sec4ICover e)

theorem sec4FDCover0_proj (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (l : ↥L) :
    toProj Sec4IQ ((sec4FDCover0 e l : ↥(omegaGroup sec4IQ_nondegenerate)) : OGroup Sec4IQ) =
      ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) := by
  have h1 : (sec4FDCover0 e l : ↥(omegaGroup sec4IQ_nondegenerate)) =
      sec4FDEquiv.symm (sec4ICover e l) := rfl
  rw [h1, ← coe_omegaToProj sec4IQ_nondegenerate (sec4FDEquiv.symm (sec4ICover e l))]
  change ((sec4FDEquiv (sec4FDEquiv.symm (sec4ICover e l)) : Sec4IOmega) : ProjOrth Sec4IQ) =
    ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ)
  rw [sec4FDEquiv.apply_symm_apply, sec4ICover_apply]

theorem sec4FDCover0_cover [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) : OddCentralCover (sec4FDCover0 e) := by
  have h := sec4ICover_odd hL e
  have hker : (sec4FDCover0 e).ker = (sec4ICover e).ker :=
    MonoidHom.ker_comp_of_injective (sec4ICover e) (sec4FDEquiv.symm).toMonoidHom
      (sec4FDEquiv.symm).injective
  refine ⟨?_, ?_, ?_⟩
  · exact (sec4FDEquiv.symm).surjective.comp h.surjective
  · rw [hker]; exact h.ker_le_center
  · rw [hker]; exact h.odd_card_ker

theorem sec4FDCover0_setting [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} (hss : s * s = 1)
    {y : ProjOrth Sec4IQ} (hact : Sec4IActs e s y) {t : OGroup Sec4IQ} (htt : t * t = 1)
    (hty : toProj Sec4IQ t = y) :
    Sec4FDCover L s (omegaGroup sec4IQ_nondegenerate) t (sec4FDCover0 e) := by
  have hπ := piOrth_not_mem_omegaGroup_seven sec4IQ_nondegenerate sec4IQ_finrank
  have hnorm := omegaGroup_normal sec4IQ_nondegenerate
  refine ⟨sec4FDCover0_cover hL e, hact.1, hss, htt, ?_⟩
  intro l l' hl'
  let w : ↥(omegaGroup sec4IQ_nondegenerate) :=
    ⟨t * ((sec4FDCover0 e l : ↥(omegaGroup sec4IQ_nondegenerate)) : OGroup Sec4IQ) * t⁻¹,
      hnorm.conj_mem _ (sec4FDCover0 e l).2 t⟩
  have hwproj : omegaToProj sec4IQ_nondegenerate w =
      omegaToProj sec4IQ_nondegenerate (sec4FDCover0 e l') := by
    apply Subtype.ext
    rw [coe_omegaToProj, coe_omegaToProj]
    change toProj Sec4IQ (t * ((sec4FDCover0 e l : ↥(omegaGroup sec4IQ_nondegenerate)) :
        OGroup Sec4IQ) * t⁻¹) =
      toProj Sec4IQ ((sec4FDCover0 e l' : ↥(omegaGroup sec4IQ_nondegenerate)) : OGroup Sec4IQ)
    rw [map_mul, map_mul, map_inv, sec4FDCover0_proj e l, sec4FDCover0_proj e l', hty]
    exact (hact.2 l l' hl').symm
  have heq : w = sec4FDCover0 e l' :=
    omegaToProj_injective_of_not_mem sec4IQ_nondegenerate hπ hwproj
  exact (congrArg Subtype.val heq).symm

private theorem hasType_toProj_iff_invType {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) (hn : Odd (Module.finrank (ZMod 3) V))
    (hσ : quadSign Q = 1) {w : omegaGroup hQ}
    (hww : (w : OGroup Q) * (w : OGroup Q) = 1) {r : ℕ} {α : ℤˣ}
    (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    HasType (toProj Q (w : OGroup Q)) r α ↔ invType (w : OGroup Q) = (r, α) := by
  constructor
  · rintro ⟨-, t, htt, htype, htproj⟩
    have hmem : (w : OGroup Q)⁻¹ * t ∈ piGroup Q := by
      have h1 : toProj Q ((w : OGroup Q)⁻¹ * t) = 1 := by
        rw [map_mul, map_inv, htproj, inv_mul_cancel]
      rwa [← QuotientGroup.ker_mk' (piGroup Q), MonoidHom.mem_ker]
    rcases mem_piGroup_iff.mp hmem with h | h
    · have htw : t = (w : OGroup Q) := (inv_mul_eq_one.mp h).symm
      rw [← htw]
      exact htype
    · exfalso
      have htw : t = piOrth Q * (w : OGroup Q) := by
        have h1 : t = (w : OGroup Q) * piOrth Q := by
          calc t = (w : OGroup Q) * ((w : OGroup Q)⁻¹ * t) := by group
            _ = (w : OGroup Q) * piOrth Q := by rw [h]
        rw [h1, mul_piOrth_comm]
      have hev : Even (invDim (w : OGroup Q)) :=
        ((involution_mem_omegaGroup_iff hQ hww).mp w.2).1
      have hsub : Odd (Module.finrank (ZMod 3) V - invDim (w : OGroup Q)) :=
        Nat.Odd.sub_even (invDim_le (w : OGroup Q)) hn hev
      have hd : invDim t = Module.finrank (ZMod 3) V - invDim (w : OGroup Q) := by
        have h2 := congrArg Prod.fst (invType_piOrth_mul_of_odd hQ hww hn hσ)
        rw [← htw] at h2
        exact h2
      have hrt : invDim t = r := congrArg Prod.fst htype
      rw [hrt] at hd
      have hrev : Even r := by rcases hr with h | h | h <;> rw [h] <;> decide
      have hodd : Odd r := by rw [hd]; exact hsub
      exact (Nat.not_even_iff_odd.mpr hodd) hrev
  · intro htypew
    refine ⟨?_, (w : OGroup Q), hww, htypew, rfl⟩
    intro hw1
    have hwmem : (w : OGroup Q) ∈ piGroup Q := by
      rwa [← QuotientGroup.ker_mk' (piGroup Q), MonoidHom.mem_ker]
    rcases mem_piGroup_iff.mp hwmem with h1 | h1
    · rw [h1, invType_one] at htypew
      have hr0 : r = 0 := by
        have h2 := congrArg Prod.fst htypew
        simpa using h2.symm
      rcases hr with h | h | h <;> omega
    · exact hπ (h1 ▸ w.2)

theorem sec4FDCover0_type_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {v : G} (hvL : v ∈ L)
    (hvv : v * v = 1) {r : ℕ} {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    InducesTypeSome L v 7 1 r α ↔
      invType ((sec4FDCover0 e ⟨v, hvL⟩ : ↥(omegaGroup sec4IQ_nondegenerate)) : OGroup Sec4IQ) =
        (r, α) := by
  rw [sec4I_inducesTypeSome_mem_iff e hvL hr]
  have hww : (sec4FDCover0 e ⟨v, hvL⟩ : ↥(omegaGroup sec4IQ_nondegenerate)) *
      (sec4FDCover0 e ⟨v, hvL⟩ : ↥(omegaGroup sec4IQ_nondegenerate)) = 1 := by
    rw [← map_mul]
    have h1 : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext hvv
    rw [h1, map_one]
  have hcoe : ((sec4FDCover0 e ⟨v, hvL⟩ : ↥(omegaGroup sec4IQ_nondegenerate)) :
        OGroup Sec4IQ) *
      ((sec4FDCover0 e ⟨v, hvL⟩ : ↥(omegaGroup sec4IQ_nondegenerate)) : OGroup Sec4IQ) = 1 := by
    simpa using congrArg Subtype.val hww
  rw [← sec4FDCover0_proj e ⟨v, hvL⟩]
  exact hasType_toProj_iff_invType sec4IQ_nondegenerate
    (piOrth_not_mem_omegaGroup_seven sec4IQ_nondegenerate sec4IQ_finrank)
    (by rw [sec4IQ_finrank]; decide) sec4IQ_quadSign hcoe hr

end CFSG.OddStandard.SmallF3.Omega
