module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic9
public import CFSG.GH74.KGroups.Generic10
public import CFSG.GH74.KGroups.Generic11
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.KGroups.Sz8D
public import CFSG.GH74.KGroups.KI5
public import CFSG.GH74.Uniqueness.SU.KInputs
import CFSG.Goldschmidt.Steps.GSz8Mult
import CFSG.Goldschmidt.Steps.G3MFSz8
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Kernel.J4Count.KFacts

public section

namespace CFSG.GH74.KGroups.KI5D

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8
  CFSG.GH74.KGroups.Sz8D

theorem ki5d :
    CFSG.GH74.KGroups.KI5.KI5d := by
  intro K _ _ hK hZ2 hZ ⟨e⟩ hZcard φ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hquasi : CFSG.Open.IsQuasisimple K := ⟨hperf, hsimple⟩
  obtain ⟨eO⟩ := CFSG.GH74.KGroups.KI5.equiv_open_of_szModel ⟨e⟩
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.KI5.equiv_P_of_szModel ⟨e⟩
  have hel := CFSG.Goldschmidt.GSz8Mult.isElemAbelian_center hquasi eO
  have hMF := CFSG.Goldschmidt.GMFSz8 K hquasi hel ⟨eO⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨k, hk⟩ := exists_conj_stabilizes P φ
  obtain ⟨M, hMP, hMA⟩ := autModel eP
  have hfix : ∀ σ : Equiv.Perm (Fin 65), (∀ s ∈ S0, σ * s * σ⁻¹ ∈ S0) →
      (∀ s ∈ S0, σ⁻¹ * s * σ ∈ S0) → σ cpt = cpt := by
    intro σ h1 h2
    apply fix_unique (σ cpt)
    intro s hs
    have hsS : s ∈ S0 := (mem_elemsT QS QS_ok s).1 hs
    have h3 := S0_fix _ ((mem_elemsT QS QS_ok _).2 (h2 s hsS))
    calc s (σ cpt) = σ ((σ⁻¹ * s * σ) cpt) := by
          simp [Equiv.Perm.mul_apply]
      _ = σ cpt := by rw [h3]
  obtain ⟨g, hg⟩ := aut_inner_of_pairing hperf hZcard
    (fun P b hb c hc hbc hcc => ((hMF P).1 b hb c hc hbc hcc).1)
    (fun P b hb hbc hbZ z hz => (hMF P).2 b hb hbc hbZ z hz)
    M S0 E0 (by rw [hMP]; exact QS_le) (v := 6) (m := 455) card_S (card_K' eP) (by decide)
    E0_le E0_central (fun σ => σ cpt = cpt) hfix tt (by rw [hMP]; exact tt_mem) (ys 0) (ys_mem 0)
    ys0_ne (by
      intro κ h1 h2 h3 h5 h4t σ hσA hσfix hσP h4σ
      rw [hMA] at hσA
      rw [hMP] at hσP
      exact hfin_sz8 κ h1 h2 h3 h5 h4t σ hσA hσfix hσP h4σ)
    P (φ.trans (MulAut.conj k)) hk
  refine ⟨k⁻¹ * g, ?_⟩
  ext x
  have h1 := hg x
  simp only [MulEquiv.trans_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  calc φ x = k⁻¹ * (k * φ x * k⁻¹) * k := by group
    _ = k⁻¹ * (g * x * g⁻¹) * k := by rw [h1]
    _ = k⁻¹ * g * x * (k⁻¹ * g)⁻¹ := by group

theorem ki5
    : CFSG.GH74.Uniqueness.SU.K.KI5 := CFSG.GH74.KGroups.KI5.ki5_of_d ki5d

end CFSG.GH74.KGroups.KI5D
