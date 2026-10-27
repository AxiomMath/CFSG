module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28LinTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28NormalSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem linL28_card_eq_eight {K : Type} [Field K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (h : 504 ∈ linBlockOrders K) : Nat.card K = 8 := by
  obtain ⟨m, -, hm⟩ := h
  exact ((ordA_eq_504_iff hK).1 hm.symm).2

theorem linL28_card_units_eq_seven {K : Type} [Field K] (hK : Nat.card K = 8) :
    Nat.card Kˣ = 7 := by
  rw [Nat.card_units, hK]

theorem kFactCompParabL28RankOn_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabL28RankOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA N hNP hPN d ψ hd hψ
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  have h8 := linL28_card_eq_eight hK
    (card_mem_of_l28Section hCP.parab.1 ρ hρs hQ hNP hPN ψ hd hψ)
  have h7 : Nat.card (GaloisField 2 f)ˣ = 7 := linL28_card_units_eq_seven h8
  obtain ⟨φ, hinj, hrange, hc⟩ := exists_linTorus_embedding (r := 2) (by omega)
    (by rw [h7]; norm_num) ρ hker e hcompat hcomap
  exact l28_E_of_torus h7 φ hinj (hrange.trans hCP.parab.1) hc

theorem linBlock_eq_two_of_l28 {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {n : ℕ} {I : Set ℕ} {a : Fin n} (hq : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a))
    (h504 : Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 504) :
    linBlockLen n I a = 2 ∧ Nat.card K = 8 := by
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a)).symm hq)
  rw [card_range_toGL_quotient_center (by omega)] at h504
  obtain ⟨h1, h8⟩ := (ordA_eq_504_iff hK).mp h504
  exact ⟨by omega, h8⟩

theorem linL28_four_le_of_two_blocks {n : ℕ} {I : Set ℕ} {a b : Fin n} (hab : a ≠ b)
    (ha : linBlockLen n I a = 2) (hb : linBlockLen n I b = 2) : 4 ≤ n := by
  have ha' := linBlockLen_le (I := I) a
  have hb' := linBlockLen_le (I := I) b
  by_contra hn
  have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hab' with h | h
  · exact linBlock_disjoint (I := I) hab (r := b) (by omega) (by omega) le_rfl (by omega)
  · exact linBlock_disjoint (I := I) hab (r := a) le_rfl (by omega) (by omega) (by omega)

theorem linL28_three_le_pRank_of_two_blocks {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L) {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ}
    {I : Set ℕ} (ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L)
    (hker : ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K)
    (hcompat : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n K I) {a b : Fin n} (hab : a ≠ b)
    (ha : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a))
    (ha504 : Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 504)
    (hb : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I b))
    (hb504 : Nat.card (↥(linBlockSL K n I b) ⧸ Subgroup.center ↥(linBlockSL K n I b)) = 504) :
    3 ≤ Open.pRank 7 L := by
  obtain ⟨hla, hK8⟩ := linBlock_eq_two_of_l28 hK ha ha504
  obtain ⟨hlb, -⟩ := linBlock_eq_two_of_l28 hK hb hb504
  have h4 := linL28_four_le_of_two_blocks hab hla hlb
  have h7 : Nat.card Kˣ = 7 := linL28_card_units_eq_seven hK8
  obtain ⟨φ, hinj, hrange, -⟩ := exists_linTorus_embedding (r := 3) (by omega)
    (by rw [h7]; norm_num) ρ hker e hcompat hcomap
  exact three_le_pRank_of_torus h7 φ hinj (hrange.trans hPL)

theorem exists_linLeviData_of_comap_eq {Y : Type} [Group Y] {L P : Subgroup Y} {K : Type}
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) {I : Set ℕ}
    (ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n K I) :
    ∃ β : ↥((P.subgroupOf L).comap ρ) →* (∀ a : Fin n, Matrix.GeneralLinearGroup
        (Fin (linBlockLen n I a)) K),
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ (linBlockSL K n I) ≤ β.range ∧
        ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (linBlockSL K n I) := by
  revert hcomap
  generalize (P.subgroupOf L).comap ρ = Q
  rintro rfl
  exact ⟨linLeviHom K n I, isPGroup_ker_linLeviHom hn, pi_le_range_linLeviHom,
    commutator_range_linLeviHom_le⟩

theorem kFactCompParabL28TwoRankOn_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabL28TwoRankOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨β, hβk, hβp, hβc⟩ := exists_linLeviData_of_comap_eq (by omega) ρ hcomap
  obtain ⟨a, b, hab, ha, hb, ha504, hb504⟩ := two_blocks_of_l28Section hCP.parab.1 ρ hρs β hβk
    hβp hβc (isQuasisimple_or_isSolvable_linBlockSL I) hNP hPN ψ hd₁ hd₂ hψ
  exact linL28_three_le_pRank_of_two_blocks hCP.parab.1 hK ρ hker e hcompat hcomap hab ha ha504
    hb hb504

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
