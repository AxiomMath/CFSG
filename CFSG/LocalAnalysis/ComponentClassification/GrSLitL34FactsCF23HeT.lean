module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Socle
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHe
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.QuasithinUnique.Ch1

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

@[expose] def nlEquiv : ↥(NL hKa) ≃* LK h :=
  (Subgroup.subgroupOfEquivOfLe (inn_le_GAut hKa)).trans
    (MonoidHom.ofInjective (OutInv.conj_injective (h := h))).symm

theorem conj_nlEquiv (γ : ↥(NL hKa)) :
    MulAut.conj (nlEquiv hKa γ) = ((γ : ↥(GAut hKa)) : MulAut (LK h)) := by
  rw [nlEquiv, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
  rfl

theorem center_oddBarK_eq_bot
    (e : OddBar h.K ≃* Blueprint.NativeSporadic.He) : center (OddBar h.K) = ⊥ := by
  have hS : IsSimpleGroup Blueprint.NativeSporadic.He := CFSG.Sporadic.He.fam_he_simplicity.2.2
  have : IsSimpleGroup (OddBar h.K) := @MulEquiv.isSimpleGroup _ _ _ Units.instGroup hS e
  exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_K

@[expose] def lkEquivP
    (e : OddBar h.K ≃* Blueprint.NativeSporadic.He) :
    LK h ≃* ↥heP :=
  ((QuotientGroup.quotientMulEquivOfEq (center_oddBarK_eq_bot e)).trans
    QuotientGroup.quotientBot).trans (e.trans heEquivP)

theorem phi_abar_mul_self : phi hKa (abar h) * phi hKa (abar h) = 1 := by
  rw [← map_mul, abar_mul_self, map_one]

theorem phi_abar_mem_NL
    (e : OddBar h.K ≃* Blueprint.NativeSporadic.He)
    (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) : phi hKa (abar h) ∈ NL hKa := by
  set α := phi hKa (abar h) with hαdef
  set β : LK h ≃* LK h := ((α : ↥(GAut hKa)) : MulAut (LK h)) with hβdef
  have hα2 := phi_abar_mul_self hKa
  have hβ2 : ∀ x, β (β x) = x := fun x => by
    have := congrArg (fun g : ↥(GAut hKa) => ((g : MulAut (LK h)) x)) hα2
    simpa only [Subgroup.coe_mul, MulAut.mul_apply, Subgroup.coe_one, MulAut.one_apply] using this
  set ε := lkEquivP e with hεdef
  by_cases hin : transAut ε β ∈ inner heP
  · obtain ⟨l, hl⟩ := isInnerAut_of_transAut_mem_inner ε β hin
    rw [mem_subgroupOf]
    refine ⟨l⁻¹, ?_⟩
    ext x
    rw [MulAut.conj_apply, inv_inv]
    exact (hl x).symm
  · exfalso
    have hc := he_outer_fixSub_card (transAut ε β) (transAut_mul_self ε β hβ2) hin
    rw [Set.mem_singleton_iff] at hc
    have hfix : ∀ γ ∈ Jhat hKa, ∀ hγ : γ ∈ NL hKa,
        transAut ε β (ε (nlEquiv hKa ⟨γ, hγ⟩)) = ε (nlEquiv hKa ⟨γ, hγ⟩) := by
      intro γ hγJ hγ
      rw [transAut_apply]
      congr 1
      apply OutInv.conj_injective
      rw [conj_apply_eq, conj_nlEquiv]
      have hc' : γ * α = α * γ := mem_centralizer_singleton_iff.mp ((Jhat_component hKa).1 hγJ)
      have hc'' := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) hc'
      simp only [Subgroup.coe_mul] at hc''
      rw [hβdef]
      calc (α : MulAut (LK h)) * (γ : MulAut (LK h)) * (α : MulAut (LK h))⁻¹ =
          (γ : MulAut (LK h)) * (α : MulAut (LK h)) * (α : MulAut (LK h))⁻¹ := by rw [hc'']
        _ = (γ : MulAut (LK h)) := by group
    let f : ↥(Jhat hKa) → ↥(fixSub (transAut ε β)) := fun γ =>
      ⟨ε (nlEquiv hKa ⟨γ, Jhat_le_NL hKa γ.2⟩), hfix γ γ.2 (Jhat_le_NL hKa γ.2)⟩
    have hf : Function.Injective f := by
      intro γ γ' hγγ'
      have h1 := congrArg (fun z : ↥(fixSub (transAut ε β)) => (z : ↥heP)) hγγ'
      have h2 := (nlEquiv hKa).injective (ε.injective h1)
      exact Subtype.ext (congrArg (fun z : ↥(NL hKa) => (z : ↥(GAut hKa))) h2)
    have hle := Nat.card_le_card_of_injective f hf
    rw [hc] at hle
    have hq : Nat.card (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) = 20160 :=
      CatLeaf.card_of_isL34Type (lieModel_Jhat hKa hL)
    have hdvd := Subgroup.card_quotient_dvd_card (center ↥(Jhat hKa))
    rw [hq] at hdvd
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega

end CFSG.ComponentClassification.GSThmB.CF23L34
