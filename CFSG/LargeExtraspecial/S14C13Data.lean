module

public import CFSG.LargeExtraspecial.S14Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

section Generic

variable {V M : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup M] [Module (ZMod 2) M]

theorem isCompl_of_radDecomp {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
    {ρ : CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}
    (hD : S2.RadDecomp ρ ⊥ ⊤ p p₁) :
    IsCompl (S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))) := by
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot, top_inf_eq, top_inf_eq] at hD
  exact IsCompl.of_eq hD.2 hD.1

omit [FiniteDimensional (ZMod 2) V] in
theorem isCompl_of_spRadDecomp {f : LinearMap.BilinForm (ZMod 2) V}
    {ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}
    (hD : S2.SpRadDecomp ρ ⊥ ⊤ p p₁) :
    IsCompl (S2.fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)))
      (S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V))) := by
  rw [S2.SpRadDecomp, S2.spRadFix_bot, S2.spRadFix_bot, top_inf_eq, top_inf_eq] at hD
  exact IsCompl.of_eq hD.2 hD.1

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem pairGen_N0_of_occurs (hCE : CentralExtInput.{0}) {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t) :
    S6.PairGen S g t ∧ Nbar S g t = N0bar S g t := by
  obtain ⟨H, C, ht, ht1, hVQ, hcase, -⟩ := case_of_occurs hocc
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  exact ⟨hcase.elim (S6.pairGen_of_omegaCase H hNo C ht ht1 hVQ)
      (S6.pairGen_of_spCase H C ht ht1 hVQ),
    hcase.elim (S6.Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ)
      (S6.Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ)⟩

theorem nqHyp_of_occurs (hCE : CentralExtInput.{0}) {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t) : NQHyp S g t := by
  obtain ⟨H, C, ht, ht1, hVQ, -, -⟩ := case_of_occurs hocc
  obtain ⟨hgen, hN0⟩ := pairGen_N0_of_occurs hCE hSt hocc
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  exact S6.timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb

theorem omega_data (hCE : CentralExtInput.{0}) {t : S.O} {c : Config} (hSt : Stage S g t)
    (hocc : c.Occurs S g t) [NQHyp S g t] {d : ℕ} (hΩ' : RNOmega S g t d) :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate)
      (hX : RmodN S g t = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
      (p p₁ : Vt S g t), finrank (ZMod 2) (Vt S g t) = d ∧ p ≠ 0 ∧ Q p = 0 ∧ Q p₁ = 0 ∧
        polar Q p p₁ = 1 ∧ LmodN S g t = pointRadical Q p ∧
        IsCompl (S2.fixOf (nqRep S g t hX) (pointRadical Q p : Set _))
          (S2.fixOf (nqRep S g t hX) (pointRadical Q p₁ : Set _)) := by
  obtain ⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩ := hΩ'
  have haQ := H.conj_mem
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  obtain ⟨-, hN0⟩ := pairGen_N0_of_occurs hCE hSt hocc
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  obtain ⟨Q, hQ, hpol, hX, hE, horb⟩ := hΩ.exists_form
  have hD := isCompl_of_radDecomp (S6.timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ hN0 hh hb hX hE)
  refine ⟨Q, hQ, hX, aV ht, bV (mem_Lbar_of_pair H ht hh), hdim, aV_ne_zero H ht,
    (horb _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩,
    (horb _ (bV_ne_zero H _)).mpr ((mem_orbitOf_RmodN_iff haQ ht).mpr
      ⟨S.ρ h, hh, (ρ_cl_conj_z S h haQ).symm⟩), ?_, hE, hD⟩
  rw [← polarBilin_apply_apply, hpol]
  exact beta_aV_bV H C ht ht1 hVQ hh hb

theorem sp_data (hCE : CentralExtInput.{0}) {t : S.O} {c : Config} (hSt : Stage S g t)
    (hocc : c.Occurs S g t) [NQHyp S g t] {d : ℕ} (hSp' : RNSp S g t d) :
    ∃ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ) (p₁ : Vt S g t),
      finrank (ZMod 2) (Vt S g t) = d ∧ beta H C ht ht1 hVQ (aV ht) p₁ = 1 ∧
        IsCompl (S2.fixOf (nqRep S g t hSp.eq_sp)
            (spPointRadical (beta H C ht ht1 hVQ) (aV ht) : Set _))
          (S2.fixOf (nqRep S g t hSp.eq_sp)
            (spPointRadical (beta H C ht ht1 hVQ) p₁ : Set _)) := by
  obtain ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩ := hSp'
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  obtain ⟨-, hN0⟩ := pairGen_N0_of_occurs hCE hSt hocc
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  exact ⟨H, C, ht, ht1, hVQ, hSp, bV (mem_Lbar_of_pair H ht hh), hdim,
    beta_aV_bV H C ht ht1 hVQ hh hb,
    isCompl_of_spRadDecomp (S6.timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb)⟩

end CFSG.LargeExtraspecial.S14
