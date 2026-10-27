module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)

theorem odd_card_center_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have hz' : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hn : (Subgroup.zpowers (z : X)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (z : X) := Subgroup.mem_center_iff.mp z.2 g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (Subgroup.mem_zpowers _) k⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (z : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  rw [h] at hle
  have h1 : (z : X) = 1 := (Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hz'
  norm_num at hz'

theorem exists_mulEquiv_statedSp_of_isQuasisimple_idxB
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxB (↥Y ⧸ Subgroup.center ↥Y)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 2 ≤ r ∧
      Nonempty (↥Y ≃* StatedSp r K) := by
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  have hL : IsComponentOf (⊤ : Subgroup ↥Y) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hY
  let eT : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup ↥Y)).map eT.toMonoidHom = Subgroup.center ↥Y :=
    Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup ↥Y)) = Nat.card (Subgroup.center ↥Y) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup ↥Y) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥Y) ≃*
      ↥Y ⧸ Subgroup.center ↥Y := QuotientGroup.congr _ _ eT hcT
  obtain ⟨d, hd, ⟨e⟩⟩ := hF
  have hB : IsLieOf IdxB (↥(⊤ : Subgroup ↥Y) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥Y)) :=
    ⟨d, hd, ⟨eQ.trans e⟩⟩
  obtain ⟨r, K, hf, hfin, hK, hr, ⟨φ⟩⟩ :=
    exists_mulEquiv_statedSp_of_idxB (oddCenterRest_of_griess hGA) hL (hcard ▸ hodd) hB
  exact ⟨r, K, hf, hfin, hK, hr, ⟨eT.symm.trans φ⟩⟩

variable {r : ℕ} {K : Type} [Field K]

theorem exists_flagStabilizer_of_isParabolicTwo [Finite K] [CharP K 2] {A : Type} [Group A]
    [Finite A] {L P : Subgroup A} (hpar : IsParabolicTwo L P) (hne : P ≠ L)
    (φ : ↥L ≃* StatedSp r K) :
    ∃ (ρ : StatedSp r K ≃* ↥L) (I : Set ℕ) (t : ℕ), (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧ t ∈ I ∧
      (∀ c ∈ I, c ≤ t) ∧ (P.subgroupOf L).comap ρ.toMonoidHom = flagStabilizer r K I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPL, T, ⟨hTL, hT2, hTi⟩, hNP⟩ := hpar
  set T₀ : Subgroup ↥L := T.subgroupOf L
  have hNT₀ : Subgroup.normalizer (T₀ : Set ↥L) ≤ P.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNP ⟨x.2, Subgroup.mem_normalizer_fintype fun s hs => ?_⟩
    have h1 : (⟨s, hTL hs⟩ : ↥L) ∈ T₀ := Subgroup.mem_subgroupOf.2 hs
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨s, hTL hs⟩).1 h1
    simpa [T₀, Subgroup.mem_subgroupOf] using h2
  have hT₁ : IsPGroup 2 (T₀.map φ.toMonoidHom) := (hT2.comap_subtype (K := L)).map _
  have hT₁i : ¬ 2 ∣ (T₀.map φ.toMonoidHom).index := by
    rw [show φ.toMonoidHom = (φ : ↥L →* StatedSp r K) from rfl, Subgroup.index_map_equiv]
    exact hTi
  let S₁ : Sylow 2 (StatedSp r K) := hT₁.toSylow hT₁i
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r K) U S₁
  let ψ : ↥L ≃* StatedSp r K := φ.trans (MulAut.conj x⁻¹)
  have hψT : T₀.map ψ.toMonoidHom = SymplecticFlag.unipotent r K := by
    have h1 : ((x • U : Sylow 2 (StatedSp r K)) : Subgroup (StatedSp r K)) =
        T₀.map φ.toMonoidHom := by rw [hx]; rfl
    rw [Sylow.coe_subgroup_smul, hU] at h1
    have h1' : T₀.map φ.toMonoidHom =
        (SymplecticFlag.unipotent r K).map (MulAut.conj x).toMonoidHom := by
      rw [← h1]
      rfl
    have h2 : T₀.map ψ.toMonoidHom = (T₀.map φ.toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      change x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [h2, h1', Subgroup.map_map, this, Subgroup.map_id]
  have hB : SymplecticFlag.borelSubgroup r K ≤ (P.subgroupOf L).map ψ.toMonoidHom := by
    rw [← SymplecticHigher.normalizer_unipotent, ← hψT,
      ← Subgroup.map_normalizer_eq_of_bijective _ ψ.bijective]
    exact Subgroup.map_mono hNT₀
  obtain ⟨hPeq, -⟩ := SymplecticHigher.borel_overgroups _ hB
  set I := SymplecticHigher.borelCuts K ((P.subgroupOf L).map ψ.toMonoidHom)
  have hI := SymplecticHigher.borelCuts_le (K := K) ((P.subgroupOf L).map ψ.toMonoidHom)
  have hcomap : (P.subgroupOf L).comap ψ.symm.toMonoidHom = flagStabilizer r K I := by
    rw [← hPeq, Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
  have hne' : I.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have htop : (P.subgroupOf L).comap ψ.symm.toMonoidHom = ⊤ := by
      rw [hcomap, hemp, SymplecticHigher.flagStabilizer_empty]
    apply hne
    refine le_antisymm hPL fun y hy => ?_
    have hyψ : ψ ⟨y, hy⟩ ∈ (P.subgroupOf L).comap ψ.symm.toMonoidHom := htop ▸ Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hyψ
  classical
  obtain ⟨i₀, hi₀⟩ := hne'
  set t := Nat.findGreatest (· ∈ I) r
  refine ⟨ψ.symm, I, t, hI, Nat.findGreatest_spec (hI i₀ hi₀).2 hi₀,
    fun c hc => Nat.le_findGreatest (hI c hc).2 hc, hcomap⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
