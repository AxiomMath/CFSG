module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12FusXA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82StepFusionX_of (hp : Asc82Pre11) (h123 : Asc82Lemma123) (hI : Asc82FactInvB) :
    Asc82StepFusionX := by
  intro G _ _ t L S z K1 K2 E X hctx hX u huX hu2 _
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hpsp, -, -, -, hSL, hSyl⟩ := hp.basic G t L S z hctx.toSec10Ctx.toSec10Z
  have hA5 := (h123 G t L S z K1 K2 E X hctx hX).1
  have hSN : S ≤ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) := by
    intro s hs
    have hM := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (F.hSM hs))
    have hL := Subgroup.mem_normalizer_iff.mp (hSL hs)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at hM hL ⊢
    rw [hM n, hL n]
  have hXY : X ≤ (secM t S L ⊓ L) ⊔ S := (le_sup_left : X ≤ X ⊔ secA t S L).trans hX.sup.le
  have hXN : X ≤ secM t S L ⊓ L := sec12fx_le_of_alt hctx.sylow.2.1 hSN hXY hA5
  obtain ⟨l, hl, b, hb, hlb⟩ := hI G L hpsp (S ⊓ L) hSyl u (hXN huX).2 hu2
  have htb : t * b ∈ conjClassIn ⊤ t := by
    have h1 : t * b ∈ secTB t S L := ⟨b, hb, rfl⟩
    rw [← F.alt1.1] at h1
    exact h1.1
  obtain ⟨g, -, hg⟩ := htb
  have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp F.htC l hl
  have hu : u = l * b * l⁻¹ := by rw [← hlb]; group
  refine ⟨(l * g)⁻¹, ?_⟩
  calc (l * g)⁻¹⁻¹ * t * (l * g)⁻¹ = l * (g * t * g⁻¹) * l⁻¹ := by group
    _ = l * (t * b) * l⁻¹ := by rw [← hg]
    _ = (l * t) * b * l⁻¹ := by group
    _ = t * (l * b * l⁻¹) := by rw [hlt]; group
    _ = t * u := by rw [← hu]

end CFSG.OddStandard.SmallF3.Omega
