module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ce

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_cs [Finite G] (hW : Asc82Step109W) (hKL : Asc82StepKL) (h3 : Asc82Sec3Res10)
    (h : Asc82Res10a) (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g) :
    IsStrClosedModZ t z S := by
  intro k hk hs
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hsS : k⁻¹ * t * k ∈ S := by
    have e : S ⊔ zpowers z = S := sup_eq_left.mpr (Subgroup.zpowers_le.mpr hctx.mem_S)
    rwa [e] at hs
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic hb hctx'
  obtain ⟨s, hsdef⟩ : ∃ s, s = k⁻¹ * t * k := ⟨_, rfl⟩
  rw [← hsdef] at hsS hne1 hne2
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [ht2]; group
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hsS)
  have hsz : s * z = z * s := hctx.central s hsS
  have hW' : IsStrClosedModZ t z (secW t K1 K2) := hW G t L S z K1 K2 g hctx
  have hnotW : s ∉ secW t K1 K2 := by
    intro hsW
    have h1 : k⁻¹ * t * k ∈ secW t K1 K2 ⊔ zpowers z := by
      rw [← hsdef]
      exact Subgroup.mem_sup_left hsW
    rcases hW' k hk h1 with e | e
    · exact hne1 (hsdef.trans e)
    · exact hne2 (hsdef.trans e)
  have hs_hat : s ∈ hatCent t z :=
    sec10D_mem_hatCent (Subgroup.mem_centralizer_singleton_iff.mpr hsz) (Or.inl (by
      calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [hst]
        _ = t := by group))
  have hN := h.l104 G t L S z K1 K2 hctx' hW' k hk (by rw [← hsdef]; exact hs_hat)
  rw [← hsdef] at hN
  obtain ⟨hn1, -⟩ := sec10C_no_swap h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb hctx' hsS hs2 hN
  by_cases hLC : s ∈ L ⊔ centralizer (L : Set G)
  · exact hnotW
      (sec10C_inner_in_W h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb h.l106 hctx' hsS hs2 hLC hn1)
  have hsty : InducesTypeSome L s 5 1 2 1 := sec10C_type_i2p hf hb hctx' hsS hs2 hLC hn1
  obtain ⟨z', u0, hz'S, hz'2, hz'ty, hz'nt, hu0B, hu02, hu0ty, hu0z, hlast⟩ :=
    sec10C_Zdata h3 h hf hb hctx
  obtain ⟨k', hk'⟩ := sec10C_tz_conj h3.l36 h.l106 hf hb hctx' hsS hs2 hsty ⟨k, hsdef.symm⟩
    hz'S hz'2 hz'ty hz'nt
  refine hKL G t L S z K1 K2 g hctx u0 hu0B hu02 hu0ty hu0z ⟨k' * g⁻¹, ?_⟩
  calc (k' * g⁻¹)⁻¹ * t * (k' * g⁻¹) = g * (k'⁻¹ * t * k') * g⁻¹ := by group
    _ = g * (t * z') * g⁻¹ := by rw [hk']
    _ = t * u0 := hlast

end CFSG.OddStandard.SmallF3.Omega
