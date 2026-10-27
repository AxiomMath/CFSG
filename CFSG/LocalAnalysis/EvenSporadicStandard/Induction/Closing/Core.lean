module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Fusion

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem ClosingSetup.false_of_fusion {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t u : H}
    (S : ClosingSetup H N L t u) (hf : Sol78Fusion u t) (hm : UMovesCond (↥L ⧸ center ↥L)) :
    False := by
  have ht2 := S.t_order
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution_of_fStar S.fstar ht2
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : H, t₁ = g * t * g⁻¹ := ⟨_, rfl⟩
  rw [← ht₁] at hne hcomm
  have ht₁t₁ : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = g * (t * t) * g⁻¹ := by rw [ht₁]; group
      _ = 1 := by rw [S.t_mul_self]; group
  have ht₁C : t₁ ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 hcomm
  have hN : t₁ ∈ normalizer (L : Set H) := S.centralizer_t_le ht₁C
  obtain ⟨x, hxL, hxcomm⟩ := exists_umoves_lift S.centre_odd hm S.u_mem S.u_mul_self
    S.u_not_central hN ht₁t₁
  have hxt : x * t = t * x := S.t_comm hxL
  have hxit : x⁻¹ * t = t * x⁻¹ := S.t_comm (L.inv_mem hxL)
  have hmem : x⁻¹ * t₁ * x ∈ fusedSet u t := by
    refine ⟨isConj_iff.2 ⟨x⁻¹ * g, ?_⟩, ?_, ?_⟩
    · rw [ht₁]; group
    · calc x⁻¹ * t₁ * x * u = x⁻¹ * (t₁ * (x * u * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * u * x⁻¹) * t₁) * x := by rw [← hxcomm]
        _ = u * (x⁻¹ * t₁ * x) := by group
    · calc x⁻¹ * t₁ * x * t = x⁻¹ * t₁ * (x * t) := by rw [mul_assoc]
        _ = x⁻¹ * t₁ * (t * x) := by rw [hxt]
        _ = x⁻¹ * (t₁ * t) * x := by group
        _ = x⁻¹ * (t * t₁) * x := by rw [hcomm]
        _ = (x⁻¹ * t) * t₁ * x := by group
        _ = (t * x⁻¹) * t₁ * x := by rw [hxit]
        _ = t * (x⁻¹ * t₁ * x) := by group
  have h1 := S.fusedSet_eq hf hmem
  apply hne
  calc t₁ = x * (x⁻¹ * t₁ * x) * x⁻¹ := by group
    _ = x * t * x⁻¹ := by rw [h1]
    _ = t := by rw [hxt]; group

end CFSG.EvenSporadicStandard.Induction.Closing

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Closing

theorem solomonCoreP_of_fusion :
    ∀ (s : TauCeti.SporadicName) (Exc : ExcClass) (Q : PairClass), Q.InL →
      FusionRowData s Exc → ExcExcluded s Exc Q → SolomonCoreP s Q := by
  intro s Exc Q hQ D hexc H _ _ N L K t u hcov hhyp hQu
  have huL := hQ H L K u hQu
  have S := ClosingSetup.of_hypQ hhyp huL
  have hY : IsSporadic (↥L ⧸ center ↥L) s := hcov.2.2
  have hf := S.sol78Fusion_of_data (D.autCenter _ hY) (D.oddCore _ hY) fun u₁ hN h1 h2 h3 =>
    hexc H N L K t u hcov hhyp hQu u₁ hN h1 h2 h3
  exact S.false_of_fusion hf (D.uMoves _ hY)

@[expose] def noExc : ExcClass := fun _ _ _ => False

theorem excExcluded_noExc (s : TauCeti.SporadicName) (Q : PairClass) : ExcExcluded s noExc Q := by
  intro H _ _ N L K t u _ _ _ u₁ hN _ _ _
  exact fun h => h

end CFSG.EvenSporadicStandard.Induction
