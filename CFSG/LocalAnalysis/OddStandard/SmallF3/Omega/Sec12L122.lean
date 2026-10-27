module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Th
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Nat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122X
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Hyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma122_of (hp : Asc82Pre11) (h121 : Asc82Lemma121) (hSp : Asc82FactSplit5)
    (hNoZ4 : Asc82StepNoZ4) : Asc82Lemma122 := by
  intro G _ _ t L S z K1 K2 E hctx
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hPSp, -, htL, htS, -, hSyl⟩ := hp.basic G t L S z hctx.toSec10Ctx.toSec10Z
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  have hSc : S ≤ centralizer ({t} : Set G) := hS.1
  have hVab : IsElemAb2 (secV t S L E) 8 :=
    ((h121 G t L S z K1 K2 E hctx).1).resolve_right (hNoZ4 G t L S z K1 K2 E hctx)
  obtain ⟨φ, hφ, -, -, hlast⟩ := F.bdata.2.2.2.2.2
  have hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hφ
  obtain ⟨s, W, hM⟩ := sec122_mod_exists F hE hVab hperm
  obtain ⟨X0, hX0B, hX0sup⟩ := hSp G t L S z K1 K2 hctx.toSec10Ctx hPSp
    (sec122_S_le_normalizer_L F hSc) (sec122_centralizer_inf_S F hS htS) hSyl htL
  have hYcV := sec122_Yc_le_normalizer_V F hSc hctx.S_norm hctx.ML_norm
  have hYcB := sec122_Yc_le_normalizer_B F
  have hYcY := sec122_Yc_le_normalizer_Y F hSc
  obtain ⟨X, hXX0, hXW, hXA, hXsup⟩ := sec122_exists_X hM hYcV hYcB hYcY le_sup_left
    (sec122_A_le_Yc htS) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    (fun a ha => (sec12E_mem_A F).mp ha) (fun b hb => sec12E_t_comm_B F hb) hX0B hX0sup
  have hXYc : X ≤ (secM t S L ⊓ L) ⊔ S := hXX0.trans (le_sup_left.trans hX0sup.le)
  have hXB : X ≤ normalizer (secB S L : Set G) := hXYc.trans hYcB
  have hXt : ∀ x ∈ X, x * t = t * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (sec122_Yc_le_cent F hSc (hXYc hx)) t rfl).symm
  have hact : ∀ x ∈ X, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := fun x hx =>
    hlast x (Subgroup.mem_inf.mpr ⟨sec122_Yc_le_normalizer_L F hSc (hXYc hx), hXB hx⟩)
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ x ∈ X,
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := by
    intro σ hσ
    obtain ⟨y, hy, hyσ⟩ := hperm.2.2.2.2 σ hσ
    exact sec122_surj F hXsup hy hyσ (fun v hv => (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩)
  have hθ := sec122_theta hperm.2.1 hperm.2.2.1 hact
    (fun x hx hc => sec122_ker F hS htS hXYc hXA hx hc) hsurj
  exact ⟨X, hXA, hXsup, Or.inl ⟨hVab, sec122_natmods hM hXB hXW hXt hact hsurj hθ⟩⟩

end CFSG.OddStandard.SmallF3.Omega
