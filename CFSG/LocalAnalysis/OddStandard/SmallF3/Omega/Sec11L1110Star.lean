module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11InputsT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11L1110_star [Finite G] (hp : Asc82Pre11) (hT : Asc82Step1110Type) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {h : G} (hh : h ∈ centralizer ({z} : Set G)) (hsS : h⁻¹ * t * h ∈ S) :
    h⁻¹ * t * h = t ∨ h⁻¹ * t * h = t * z := by
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic hp.basic hctx'
  obtain ⟨s, hsdef⟩ : ∃ s, s = h⁻¹ * t * h := ⟨_, rfl⟩
  rw [← hsdef] at hsS hne1 hne2
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [ht2]; group
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hsS)
  have hsz : s * z = z * s := hctx.central s hsS
  have hW' : IsStrClosedModZ t z (secW t K1 K2) := sec11_strClosed_secW hp hctx' hctx.hyp
  have hnotW : s ∉ secW t K1 K2 := by
    intro hsW
    have h1 : h⁻¹ * t * h ∈ secW t K1 K2 ⊔ zpowers z := by
      rw [← hsdef]
      exact Subgroup.mem_sup_left hsW
    rcases hW' h hh h1 with e | e
    · exact hne1 (hsdef.trans e)
    · exact hne2 (hsdef.trans e)
  have hs_hat : s ∈ hatCent t z :=
    sec10D_mem_hatCent (Subgroup.mem_centralizer_singleton_iff.mpr hsz) (Or.inl (by
      calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [hst]
        _ = t := by group))
  have hN := hp.r10.l104 G t L S z K1 K2 hctx' hW' h hh (by rw [← hsdef]; exact hs_hat)
  rw [← hsdef] at hN
  obtain ⟨hn1, -⟩ := sec10C_no_swap hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5
    hp.basic hctx' hsS hs2 hN
  by_cases hLC : s ∈ L ⊔ centralizer (L : Set G)
  · exact hnotW (sec10C_inner_in_W hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5
      hp.basic hp.r10.l106 hctx' hsS hs2 hLC hn1)
  · have hsty : InducesTypeSome L s 5 1 2 1 :=
      sec10C_type_i2p hp.facts hp.basic hctx' hsS hs2 hLC hn1
    exact hT G t L S z K1 K2 T R hctx h hh (by rw [← hsdef]; exact hsS)
      (by rw [← hsdef]; exact hsty)

end CFSG.OddStandard.SmallF3.Omega
