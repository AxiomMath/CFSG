module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverCore
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430ChevBridge

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB

theorem lieIndex_isBOfTwo {S : Type} [Group S] {ℓ : ℕ} (h : catalogIs S (isBOfTwo ℓ)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B ℓ q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B ℓ q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | B r q =>
      obtain ⟨rfl, hq⟩ : r = ℓ ∧ q.card = 2 := hi
      exact ⟨q, hv, hq, ⟨e⟩⟩
    | _ => exact (show False from hi).elim

theorem statedClassicalModel_PSp_of_isBOfTwo {S : Type} [Group S] {ℓ : ℕ}
    (h : catalogIs S (isBOfTwo ℓ)) : StatedClassicalModel S .PSp ℓ 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isBOfTwo h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  rcases CFSG.Models.lieModel_B ℓ q hv e with hm | hm
  · rw [h1, h2] at hm
    exact hm.statedClassicalModel (by decide)
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem iso_sp_of_isBOfTwo {S : Type} [Group S] {ℓ : ℕ} (h : catalogIs S (isBOfTwo ℓ)) :
    Nonempty (S ≃* ↥(StatedSp ℓ (ZMod 2))) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_PSp_of_isBOfTwo h
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := K) (by rw [hK]; norm_num)
  exact ⟨e'.trans (statedProjEquivZMod2 φ
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ ℓ))⟩

theorem center_eq_bot_of_isBOfTwo
    {H : Type} [Group H] [Finite H] (hq : CFSG.Open.IsQuasisimple H)
    {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (hcat : catalogIs (H ⧸ Subgroup.center H) (isBOfTwo ℓ)) :
    Subgroup.center H = ⊥ := by
  have hSC := statedClassicalModel_PSp_of_isBOfTwo hcat
  obtain ⟨-, ⟨eG⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hSC
    (Or.inr (Or.inr (Or.inl ⟨by norm_num, hℓ⟩)))
  have hperf : Group.IsPerfect H := ⟨hq.1⟩
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp ℓ 2 1 = (1, 1) := by
    change (Nat.gcd 2 (2 ^ 1 - 1), 1) = (1, 1)
    norm_num
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp ℓ 2 1 = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (H ⧸ Subgroup.center H)) = 1 := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
      Nat.card_congr eG.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he]
    first
      | exact Nat.card_unique
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | decide
  have hdvd := CFSG.RankThree.PerfectCover.card_center_dvd_hopf hperf
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430ChevBridge
