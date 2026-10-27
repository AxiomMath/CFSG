module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferNormFix
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
open scoped commutatorElement

theorem parabComm_of_projectiveSL
    (hGA : CFSG.Open.GriessAllModelsStatement) (hM : Lin.LinModelComm)
    {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : CFSG.Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥) {n f : ℕ} (hn : 2 ≤ n)
    (_hf : 1 ≤ f) (e : ↥Y ⧸ Subgroup.center ↥Y ≃* projectiveSL n (GaloisField 2 f))
    (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) : PairComm p Y P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨I, C, hI, hne'⟩ := exists_linCover hGA hY hodd hn e hpar
  have hPY : P ≤ Y := hpar.1
  have hn1 : 1 ≤ n := by omega
  have hblock := C.exists_block hPY hn1 hna
  have hn3 : 3 ≤ n := by
    obtain ⟨a, ha⟩ := hblock
    exact three_le_of_two_le_linBlockLen hI (hne' hne) ha
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hperf : Group.IsPerfect ↥Y := ⟨hY.1⟩
  intro b₁ b₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨k₃, hk₃⟩ hb₁Y hb₂Y hb₁P hb₂P hW₁ hW₂ y hy
  let β₁ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₁, hb₁Y⟩
  let β₂ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₂, hb₂Y⟩
  have hN₁ := C.normFix_autHom hPY hn1 β₁ hb₁P hW₁
  have hN₂ := C.normFix_autHom hPY hn1 β₂ hb₂P hW₂
  have hodd₃ : Odd (orderOf ⁅C.autHom β₁, C.autHom β₂⁆) := by
    rw [← map_commutatorElement]
    exact C.odd_orderOf_autHom ⁅β₁, β₂⁆ hp_odd hk₃
  have hcomm := hM (GaloisField 2 f) n I hn3 hI hblock (C.autHom β₁) (C.autHom β₂)
    (C.odd_orderOf_autHom β₁ hp_odd hk₁) (C.odd_orderOf_autHom β₂ hp_odd hk₂) hodd₃ hN₁ hN₂
  exact C.centralizes_of_autHom_eq_one ⁅β₁, β₂⁆ (by rw [map_commutatorElement]; exact hcomm) y hy

theorem parabCommOn_idxA_of
    (hGA : CFSG.Open.GriessAllModelsStatement) (hM : Lin.LinModelComm) :
    ParabCommOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxA) := by
  intro A _ _ Y P p hp hp2 hY h2 hF hpar hne hna
  obtain ⟨n, f, hn, hf, ⟨e⟩⟩ := ToralCensus.exists_mulEquiv_projectiveSL_of_isLieOf hF
  exact Or.inl (parabComm_of_projectiveSL hGA hM hp hp2 hY h2 hn hf e hpar hne hna)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
