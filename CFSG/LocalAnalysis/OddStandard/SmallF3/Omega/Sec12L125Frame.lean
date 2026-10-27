module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121T

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec125_core_of (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E)
    (hV : IsElemAb2 (secV t S L E) 8) : Sec125Core t (secV t S L E) E := by
  let F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htE : t ∈ E := sec120_A_le_E F hE htA
  have hVE : secV t S L E ≤ E := sec121_V_le_E F hE
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hB1 : ∃ b ∈ secB S L, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : secB S L = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h16 := F.bdata.2.1
    rw [hbot, Subgroup.card_bot] at h16
    omega
  have hnofix : ∃ v ∈ secV t S L E, t * v ≠ v * t := by
    obtain ⟨b, hb, hb1⟩ := hB1
    obtain ⟨v, hv, hfv⟩ := sec121_f_surj_V F hE hb
    refine ⟨v, hv, fun hcomm => hb1 ?_⟩
    rw [← hfv]
    change v * t * v⁻¹ * t⁻¹ = 1
    rw [← hcomm]
    group
  refine
    { comm := fun v hv w hw => CFSG.Open.IsElemAbelian.comm hV.1 hv hw
      sq := fun v hv => by
        have h2 := hV.1.2 v hv
        rwa [pow_two] at h2
      tsq := sec12E_t_sq F
      tnorm := fun v hv =>
        (Subgroup.mem_normalizer_iff.mp (sec121_E_le_normalizer_V F hE htE) v).mp hv
      sup := sec121_V_sup_zpowers F hE
      nofix := hnofix
      trans := ?_
      two := ?_ }
  · intro v hv hcomm
    have hf : sec12f t v = 1 := by
      change v * t * v⁻¹ * t⁻¹ = 1
      rw [hcomm]
      group
    have hvB : v ∈ secB S L := (sec121_f_eq_one_iff_V F hE hv).mp hf
    obtain ⟨w, hw, hfw⟩ := sec121_f_surj_V F hE hvB
    refine ⟨w, hw, ?_⟩
    have hfw' : w * t * w⁻¹ * t⁻¹ = v := hfw
    calc w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t := by group
      _ = v * t := by rw [hfw']
  · intro c hc h2
    have hcA : c ∈ centralizer (secA t S L : Set G) :=
      Subgroup.centralizer_le (sec120_A_le_E F hE) hc
    have hcA' : c ∈ secA t S L := sec12E_two_C F hcA h2
    rcases (sec12E_mem_A F).mp hcA' with hB | ⟨b, hb, rfl⟩
    · exact hBV hB
    · exfalso
      obtain ⟨v, hv, hne⟩ := hnofix
      apply hne
      have h1 : v * (t * b) = (t * b) * v := Subgroup.mem_centralizer_iff.mp hc v (hVE hv)
      have hbv : b * v = v * b := CFSG.Open.IsElemAbelian.comm hV.1 (hBV hb) hv
      have h3 : (v * t) * b = (t * v) * b := by
        calc (v * t) * b = v * (t * b) := by group
          _ = (t * b) * v := h1
          _ = t * (b * v) := by group
          _ = t * (v * b) := by rw [hbv]
          _ = (t * v) * b := by group
      exact (mul_right_cancel h3).symm

end CFSG.OddStandard.SmallF3.Omega
