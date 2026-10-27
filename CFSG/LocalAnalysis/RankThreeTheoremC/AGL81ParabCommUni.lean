module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniTransferNormFix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding Uni
open scoped commutatorElement

theorem parabComm_of_uni
    {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxTwistedA (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P)
    (hne : P ≠ Y) (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    PairComm p Y P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    Lin.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨K, _, f, t, s, ε, h, I, hε, hI, ⟨C⟩⟩ := exists_uniCover hY hodd hF hpar hne
  have hPY : P ≤ Y := hpar.1
  have hbig := C.exists_big_block hε hI hPY hna
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hperf : Group.IsPerfect ↥Y := ⟨hY.1⟩
  intro b₁ b₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨k₃, hk₃⟩ hb₁Y hb₂Y hb₁P hb₂P hW₁ hW₂ y hy
  let β₁ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₁, hb₁Y⟩
  let β₂ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₂, hb₂Y⟩
  have hN₁ := C.normFix_autHom hε hI hPY β₁ hb₁P hW₁
  have hN₂ := C.normFix_autHom hε hI hPY β₂ hb₂P hW₂
  have hodd₃ : Odd (orderOf ⁅C.autHom β₁, C.autHom β₂⁆) := by
    rw [← map_commutatorElement]
    exact C.odd_orderOf_autHom ⁅β₁, β₂⁆ hp_odd hk₃
  have hcomm := uniModelComm_holds K f h t s ε hε I hI hbig (C.autHom β₁) (C.autHom β₂)
    (C.odd_orderOf_autHom β₁ hp_odd hk₁) (C.odd_orderOf_autHom β₂ hp_odd hk₂) hodd₃ hN₁ hN₂
  exact C.centralizes_of_autHom_eq_one ⁅β₁, β₂⁆
    (by rw [map_commutatorElement]; exact hcomm) y hy

theorem parabCommOn_idxTwistedA_of :
    ParabCommOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxTwistedA) := by
  intro A _ _ Y P p hp hp2 hY h2 hF hpar hne hna
  exact Or.inl (parabComm_of_uni hp hp2 hY h2 hF hpar hne hna)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
