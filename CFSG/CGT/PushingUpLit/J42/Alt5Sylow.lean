module

public import CFSG.CGT.PushingUpLit.SolK.FourD
public import CFSG.CGT.PushingUpLit.SolK.FourC

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

theorem card_le_four_of_le_alt {N : Subgroup (Perm (Fin (2 * 2 + 1)))} (hN2 : IsPGroup 2 N)
    (hNA : N ≤ alternatingGroup (Fin (2 * 2 + 1))) : Nat.card ↥N ≤ 4 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
  have hdvd : Nat.card ↥N ∣ Nat.card ↥(alternatingGroup (Fin (2 * 2 + 1))) :=
    Subgroup.card_dvd_of_le hNA
  have hA60 : Nat.card ↥(alternatingGroup (Fin (2 * 2 + 1))) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hk, hA60] at hdvd
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

namespace SolCfg

include S

theorem pCoreOf_eq_W_of_rOf_bot (hR : rOf M X = ⊥) : pCoreOf 2 M = S.D.W := by
  refine le_antisymm (fun q hq => ?_) S.W_le_Q
  obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq q hq
  have h1 : r = 1 := by
    rw [hR] at hr
    exact Subgroup.mem_bot.1 hr
  rw [h1, mul_one]
  exact hw

theorem card_pCoreOf_of_rOf_bot (hR : rOf M X = ⊥) : Nat.card ↥(pCoreOf 2 M) = 16 := by
  rw [S.pCoreOf_eq_W_of_rOf_bot hR]
  have h1 : Nat.card ↥S.D.W = Nat.card ↥(coreMod (2 * 2 + 1)) := Nat.card_congr S.D.β.toEquiv
  have h2 : Nat.card ↥(coreMod (2 * 2 + 1)) * 2 = 2 ^ (2 * 2 + 1) :=
    card_coreMod_mul_two (by decide)
  omega

theorem card_TOf_eq (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) : Nat.card ↥(TOf M (w * r)) = 64 := by
  have hRbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  have hF : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have h4 : Nat.card ↥(S.TN (w * r)) = 4 :=
    hF.card_eq_four hcard (S.TN_ne_bot hT hQe hR hw hr hcard hKM)
  have h := S.card_eq_card_inf_mul hT (TOf_le_M M (w * r)) (isPGroup_TOf M (w * r))
  have hinf : TOf M (w * r) ⊓ pCoreOf 2 M = pCoreOf 2 M :=
    inf_eq_right.2 (S.Q_le_TOf hT (S.mul_mem_Q hw hr))
  rw [hinf, S.card_pCoreOf_of_rOf_bot hRbot] at h
  have h4' : Nat.card ↥(((TOf M (w * r)).subgroupOf M).map S.θ) = 4 := h4
  omega

theorem eq_TOf_of_le_alt (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) {w r : G} (hw : w ∈ S.D.W)
    (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) (hKM : ¬ CGOf (w * r) ≤ M)
    {U : Subgroup G} (hUM : U ≤ M) (hU2 : IsPGroup 2 U) (hTU : TOf M (w * r) ≤ U) :
    U = TOf M (w * r) := by
  have hRbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  have h := S.card_eq_card_inf_mul hT hUM hU2
  have hθ2 := S.theta_isPGroup hUM hU2
  have hθA : (U.subgroupOf M).map S.θ ≤ alternatingGroup (Fin (2 * 2 + 1)) := by
    intro σ hσ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 hσ
    exact hA m
  have h4 := card_le_four_of_le_alt hθ2 hθA
  have hQU : Nat.card ↥(U ⊓ pCoreOf 2 M) ≤ 16 := by
    rw [← S.card_pCoreOf_of_rOf_bot hRbot]
    exact Subgroup.card_le_of_le inf_le_right
  have hT64 := S.card_TOf_eq hT hQe hR hw hr hcard hKM
  have hle : Nat.card ↥U ≤ Nat.card ↥(TOf M (w * r)) := by
    rw [hT64, h]
    calc Nat.card ↥(U ⊓ pCoreOf 2 M) * Nat.card ↥((U.subgroupOf M).map S.θ) ≤ 16 * 4 :=
          Nat.mul_le_mul hQU h4
      _ = 64 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTU hle).symm

theorem exists_sylow_eq_TOf_alt (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) {w r : G} (hw : w ∈ S.D.W)
    (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) (hKM : ¬ CGOf (w * r) ≤ M) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = TOf M (w * r) := by
  have hT2 : IsPGroup 2 ↥(TOf M (w * r)) := isPGroup_TOf M _
  obtain ⟨P, hP⟩ := hT2.exists_le_sylow
  refine ⟨P, ?_⟩
  by_contra hne
  have hlt : TOf M (w * r) ≠ (P : Subgroup G) := fun h => hne h.symm
  obtain ⟨n, hnP, hnT, hnN⟩ := exists_mem_normalizer_of_lt P.isPGroup' hP hlt
  have hnM : n ∈ M := S.normalizer_TOf_le_M hT hQe hw hr hcard hnN
  have hU : (P : Subgroup G) ⊓ M = TOf M (w * r) :=
    S.eq_TOf_of_le_alt hT hQe hR hA hw hr hcard hKM inf_le_right
      (isPGroup_of_le P.isPGroup' inf_le_left) (le_inf hP (TOf_le_M M _))
  exact hnT (hU ▸ Subgroup.mem_inf.2 ⟨hnP, hnM⟩)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
