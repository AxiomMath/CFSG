module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeModelDefs
import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.Quasithin (StatedGU)
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU det_pow_card_add_one_of_mem_statedGU statedSU_le_statedGU)

namespace I294LargeUni

variable {L : Type} [Field L] [Finite L] {ℓ f n r : ℕ}

theorem field (hL : Nat.card L = (ℓ ^ f) ^ 2) :
    ∃ f', ℓ ^ f = ringChar L ^ f' ∧ UnitaryFieldData (ringChar L) f' L := by
  haveI := Fintype.ofFinite L
  exact exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)

theorem two_le (hL : Nat.card L = (ℓ ^ f) ^ 2) : 2 ≤ ℓ ^ f := by
  have h1 : 1 < Nat.card L := Finite.one_lt_card
  rw [hL] at h1
  by_contra h
  have h2 : ℓ ^ f ≤ 1 := by omega
  have h3 : (ℓ ^ f) ^ 2 ≤ 1 := by
    calc (ℓ ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := by norm_num
  omega

theorem exp_pos (hp : r.Prime) {q : ℕ} (hq2 : 2 ≤ q) (hpq : ¬ r ∣ q) :
    1 ≤ padicValInt r ((-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1) := by
  haveI : Fact r.Prime := ⟨hp⟩
  have hne0 : (-(q : ZMod r)) ≠ 0 :=
    neg_ne_zero.2 (fun h => hpq ((ZMod.natCast_eq_zero_iff q r).1 h))
  have hepos : 0 < orderOf (-(q : ZMod r)) := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.2
      ⟨r - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne0⟩
  have hdvd : (r : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx : (-(q : ZMod r)) ^ orderOf (-(q : ZMod r)) = 1 := pow_orderOf_eq_one _
    push_cast
    exact sub_eq_zero.2 hx
  have hne : (-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1 ≠ 0 := by
    intro h
    have h1 : (-(q : ℤ)) ^ orderOf (-(q : ZMod r)) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have h3 : q = 1 := (Nat.pow_eq_one.1 h2).resolve_right (by omega)
    omega
  rcases (padicValInt_dvd_iff 1 ((-(q : ℤ)) ^ orderOf (-(q : ZMod r)) - 1)).1
      (by simpa using hdvd) with h | h
  · exact absurd h hne
  · exact h

theorem commOrRank_GU (hp : r.Prime) (h5 : 5 ≤ r) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ r ∣ ℓ ^ f) (hn : 1 ≤ n) : I294Large.CommOrRank r ↥(StatedGU n (ℓ ^ f) L) := by
  haveI : Fact r.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  exact I294Large.CommOrRank.of_sylow_sigmaModel hp (exp_pos hp (two_le hL) hpq)
    (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)

@[expose] noncomputable def det (n q : ℕ) (L : Type) [Field L] : ↥(StatedGU n q L) →* Lˣ :=
  Matrix.GeneralLinearGroup.det.comp (StatedGU n q L).subtype

theorem det_val {q : ℕ} (g : ↥(StatedGU n q L)) :
    ((det n q L g : Lˣ) : L) = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det := rfl

theorem mem_statedSU_iff (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (A : GL (Fin n) L) :
    A ∈ StatedSU n (ℓ ^ f) L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) L).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) L) = 1 :=
  Set.ext_iff.1 (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).1 A

theorem subgroupOf_eq_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    (StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L) = (det n (ℓ ^ f) L).ker := by
  obtain ⟨f', hq, h⟩ := field hL
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    exact Units.ext (by rw [det_val]; exact ((mem_statedSU_iff hℓ hL hn _).1 hg).1)
  · intro hg
    exact mem_statedSU_of_mem_statedGU h hq g.2 (by rw [← det_val, hg]; rfl)

theorem not_dvd_index (hp : r.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq1 : ¬ r ∣ ℓ ^ f + 1) : ¬ r ∣ (det n (ℓ ^ f) L).ker.index := by
  haveI : Fact r.Prime := ⟨hp⟩
  obtain ⟨f', hq, h⟩ := field hL
  intro hdvd
  rw [Subgroup.index_ker] at hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (det n (ℓ ^ f) L).range) r hdvd
  obtain ⟨g, hg⟩ := y.2
  have hpow : (y : Lˣ) ^ (ℓ ^ f + 1) = 1 := by
    rw [← hg]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, det_val, Units.val_one]
    exact det_pow_card_add_one_of_mem_statedGU h hq g.2
  have h1 : orderOf (y : Lˣ) ∣ ℓ ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hy] at h1
  exact hpq1 h1

@[expose] noncomputable def equivKer (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    ↥(StatedSU n (ℓ ^ f) L) ≃* ↥(det n (ℓ ^ f) L).ker :=
  (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU).symm.trans
    (MulEquiv.subgroupCongr (subgroupOf_eq_ker hℓ hL hn))

@[expose] noncomputable def proj (n q : ℕ) (L : Type) [Field L] :
    ↥(StatedSU n q L) →* StatedProj (StatedSU n q L) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))

theorem proj_surjective (n q : ℕ) : Function.Surjective (proj n q L) :=
  QuotientGroup.mk'_surjective _

theorem proj_ker (n q : ℕ) :
    (proj n q L).ker = (StatedScalars (Fin n) L).subgroupOf (StatedSU n q L) :=
  QuotientGroup.ker_mk' _

theorem not_dvd_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (hpq1 : ¬ r ∣ ℓ ^ f + 1) : ¬ r ∣ Nat.card (proj n (ℓ ^ f) L).ker := by
  rw [proj_ker, (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).2.2]
  exact fun h => hpq1 (h.trans (Nat.gcd_dvd_right _ _))

theorem commOrRank_PSU_of_not_dvd (hp : r.Prime) (h5 : 5 ≤ r) (hℓ : ℓ.Prime)
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq : ¬ r ∣ ℓ ^ f) (hn : 1 ≤ n)
    (hpq1 : ¬ r ∣ ℓ ^ f + 1) :
    I294Large.CommOrRank r (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  have hGU := commOrRank_GU hp h5 hL hpq hn
  have hSU : I294Large.CommOrRank r ↥(StatedSU n (ℓ ^ f) L) :=
    I294Large.CommOrRank.of_mulEquiv hp (equivKer hℓ hL hn).symm
      (I294Large.CommOrRank.of_normal_coprime_index hp _ (not_dvd_index hp hL hpq1) hGU)
  exact I294Large.CommOrRank.of_surjective_coprime_ker hp (proj n (ℓ ^ f) L) (proj_surjective _ _)
    (not_dvd_ker hℓ hL hn hpq1) hSU

theorem sylow_comm_PSU_of_dvd (hp : r.Prime) (h5 : 5 ≤ r) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ r ∣ ℓ ^ f) (hn : 1 ≤ n) (hnr : n < r) (hpq1 : r ∣ ℓ ^ f + 1) :
    ∀ S : Sylow r (StatedProj (StatedSU n (ℓ ^ f) L)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSU n (ℓ ^ f) L))) := by
  haveI : Fact r.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  have he : orderOf (-((ℓ ^ f : ℕ) : ZMod r)) = 1 := by
    have h0 : (((ℓ ^ f + 1 : ℕ)) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq1
    have h1 : ((ℓ ^ f : ℕ) : ZMod r) = -1 := by
      rw [Nat.cast_add, Nat.cast_one] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have h2 : -((ℓ ^ f : ℕ) : ZMod r) = 1 := neg_eq_iff_eq_neg.2 h1
    rw [h2, orderOf_one]
  have hGU : ∀ P : Sylow r ↥(StatedGU n (ℓ ^ f) L),
      IsMulCommutative (P : Subgroup ↥(StatedGU n (ℓ ^ f) L)) :=
    sylow_isMulCommutative_of_sigmaModel_of_lt hp
      (e := orderOf (-((ℓ ^ f : ℕ) : ZMod r))) (by rw [he, Nat.div_one]; exact hnr)
      (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)
  have hSub := sylow_comm_of_subgroup
    ((StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L)) hGU
  have hSU := sylow_comm_of_surjective
    (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).surjective
    hSub
  exact sylow_comm_of_surjective (proj n (ℓ ^ f) L) (proj_surjective _ _) hSU

end I294LargeUni

open I294LargeUni in
theorem i294LargeModelPSU_holds : I294LargeModelPSU := by
  intro r hr h5 ℓ f hℓ hf K _ _ hK hpq n hn hLU hS
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS'⟩ := hS
  by_cases hpq1 : r ∣ ℓ ^ f + 1
  · by_cases hnr : n < r
    · exact (hS' (sylow_comm_PSU_of_dvd (n := n) hr h5 hK hpq (by omega) hnr hpq1 S)).elim
    · push Not at hnr
      have hn6 : 6 ≤ n := by
        by_contra h
        have h5n : n = 5 := by omega
        have hr5 : r = 5 := by omega
        exact hLU ⟨by rw [h5n, hr5], hpq1⟩
      obtain ⟨f', hq, hU⟩ := field hK
      have key : ∀ q : ℕ, q = ringChar K ^ f' → r ∣ q + 1 →
          4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
        intro q hq' hdvd
        subst hq'
        exact odFour_le_pRank_psu hU hr hn6 hdvd
      exact key (ℓ ^ f) hq hpq1
  · rcases commOrRank_PSU_of_not_dvd (n := n) hr h5 hℓ hK hpq (by omega) hpq1 with hc | hrk
    · exact (hS' (hc S)).elim
    · omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
