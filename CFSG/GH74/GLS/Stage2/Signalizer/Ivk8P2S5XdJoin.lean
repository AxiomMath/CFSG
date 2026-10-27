module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Xd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section XD

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem XDR_eq_iSup (M D : Subgroup G) :
    XDR M D = ⨆ d : G, ⨆ (_ : d ∈ Dstar M D), XdR M d := rfl

theorem XDR_mem_XfamR (hB12 : Bender12) (h183 : Lemma18_3a) (h171 : Prop17_1) (hcl : Claim18Xd)
    {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {D : Subgroup G} (hDE : D ≤ E)
    (hD : (Dstar M D).Nonempty) (hDtop : XDR M D ≠ ⊤) : XDR M D ∈ XfamR z M (Vof M E) := by
  have hF := S5Facts.of_ctx h171 hctx
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf hF.hz2
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  have hσ : ∀ q ∈ piF M, q.Prime := fun q hq => prime_of_mem_piF hq
  set W : Subgroup G := XDR M D with hW
  have hXd : ∀ d ∈ Dstar M D, XdR M d ∈ XfamR z M (Vof M E) := fun d hd =>
    XdR_mem_XfamR hB12 h183 h171 hcl hctx (hDE hd.1) hd.2.1 hd.2.2
  have hXdW : ∀ d ∈ Dstar M D, XdR M d ≤ W := fun d hd =>
    le_iSup₂_of_le d hd le_rfl
  have hVW : ∀ v ∈ Vof M E, v ∈ normalizer (W : Set G) := by
    intro v hv
    refine mem_normalizer_of_cj_eq ?_
    rw [hW, XDR_eq_iSup, cj_iSup]
    refine iSup_congr fun d => ?_
    rw [cj_iSup]
    refine iSup_congr fun hd => ?_
    exact cj_eq_of_mem_normalizer ((hXd d hd).2.2.1 v hv)
  have hzN : ∀ d ∈ Dstar M D, z ∈ normalizer ((XdR M d : Subgroup G) : Set G) := by
    intro d hd
    obtain ⟨hzC, -, -, -⟩ := centralizer_facts hB12 h171 hctx (hDE hd.1)
    exact centralizer_le_normalizer_XdR hσ' d hzC
  have hzW : z ∈ normalizer (W : Set G) := by
    refine mem_normalizer_of_cj_eq ?_
    rw [hW, XDR_eq_iSup, cj_iSup]
    refine iSup_congr fun d => ?_
    rw [cj_iSup]
    refine iSup_congr fun hd => ?_
    exact cj_eq_of_mem_normalizer (hzN d hd)
  obtain ⟨d₀, hd₀⟩ := hD
  refine ⟨?_, hDtop, hVW, ?_, ?_, ?_⟩
  · intro h
    exact (hXd d₀ hd₀).1 (eq_bot_iff.2 (h ▸ hXdW d₀ hd₀))
  · refine le_antisymm ?_ ?_
    · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact commutator_zpowers_self_mem hz2' hzW hx n
    · refine iSup₂_le fun d hd => ?_
      calc XdR M d = ⁅XdR M d, zpowers z⁆ := ((hXd d hd).2.2.2.1).symm
        _ ≤ ⁅W, zpowers z⁆ := Subgroup.commutator_mono (hXdW d hd) le_rfl
  all_goals
    have hDF : D ≤ Fm M := hDE.trans (hF.hEV.trans hF.hVF)
    have hFsN : Fs M ⊓ normalizer (D : Set G) ≤ normalizer (W : Set G) := by
      rintro a ⟨haFs, haD⟩
      have haM : a ∈ M := Fs_le M haFs
      have hle : cj a W ≤ W := by
        rw [hW, XDR_eq_iSup, cj_iSup]
        refine iSup_le fun d => ?_
        rw [cj_iSup]
        refine iSup_le fun hd => ?_
        rw [cj_XdR M a d]
        have hd' : a * d * a⁻¹ ∈ Dstar M D := by
          refine ⟨(Subgroup.mem_normalizer_iff.1 haD d).1 hd.1, ?_, ?_⟩
          · intro h1
            apply hd.2.1
            have := congrArg (fun y => a⁻¹ * y * a) h1
            simpa [mul_assoc] using this
          · intro hle'
            apply hd.2.2
            intro x hx
            have h1 : a * x * a⁻¹ ∈ centralizer ({a * d * a⁻¹} : Set G) := by
              rw [← cj_centralizer]
              exact ⟨x, hx, rfl⟩
            have h2 : a * x * a⁻¹ ∈ M := hle' h1
            have := M.mul_mem (M.mul_mem (M.inv_mem haM) h2) haM
            simpa [mul_assoc] using this
        exact hXdW _ hd'
      refine mem_normalizer_of_forall_conj fun y hy => ?_
      exact hle ⟨y, hy, rfl⟩
    have hben := bender_apply hB12 hF.hkps hF.hMc hF.hnq hDF hFsN
  · exact eq_bot_iff.2 ((inf_le_inf_right M
      (Fpi_le_Fpi_of_normal hσ' Subgroup.le_normalizer le_rfl)).trans hben.1.le)
  · exact (Fpi_le_Fpi_of_normal hσ Subgroup.le_normalizer le_rfl).trans hben.2

end XD

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
