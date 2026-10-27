module

public import Certificates.Certificate22400
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Certificates CFSG.Certificates.Native

theorem eq_of_card_eq_two {G : Type*} [Group G] {H : Subgroup G} (hH : Nat.card H = 2) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hdvd : orderOf (⟨a, ha⟩ : H) ∣ 2 := hH ▸ orderOf_dvd_natCard _
  have ho : orderOf (⟨a, ha⟩ : H) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h)) ha1
    · exact h
  have hz : zpowers (⟨a, ha⟩ : H) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, ho, hH])
  have hbz : (⟨b, hb⟩ : H) ∈ zpowers (⟨a, ha⟩ : H) := hz ▸ mem_top _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hbz
  have hk' : (⟨a, ha⟩ : H) ^ k = 1 ∨ (⟨a, ha⟩ : H) ^ k = ⟨a, ha⟩ := by
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, show (⟨a, ha⟩ : H) ^ (2 : ℤ) = 1 by
        rw [zpow_ofNat, ← ho, pow_orderOf_eq_one], one_zpow]
    · right
      rw [zpow_add, zpow_mul, show (⟨a, ha⟩ : H) ^ (2 : ℤ) = 1 by
        rw [zpow_ofNat, ← ho, pow_orderOf_eq_one], one_zpow, one_mul, zpow_one]
  rcases hk' with h | h
  · rw [hk] at h
    exact absurd (congrArg Subtype.val h) hb1
  · rw [hk] at h
    exact (congrArg Subtype.val h).symm

section Chains

variable {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size} {base : List (Fin 315)}
  {hb : base.Nodup} {W : Array (List ℤ)}

theorem rep_arrTable_chain
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true) {j : ℕ}
    (hj : j < S.size) : Rep 315 (arrTable 315 S[j]!) (CFSG.Monster.B.Co2.permOfArr 315 S[j]!) :=
  rep_arrTable (by norm_num) (rep_permOfArr_of_chainOK hc hj)

theorem tp_arrTable_chain
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true) {j : ℕ}
    (hj : j < S.size) : tp 315 (arrTable 315 S[j]!) = CFSG.Monster.B.Co2.permOfArr 315 S[j]! :=
  CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (co2Rep_natArr_iff.2 (rep_arrTable_chain hc hj))

theorem genOf_chain
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true) :
    genOf 315 ((List.range k).map fun i => arrTable 315 S[i]!) =
      (RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hb W).originalSubgroup := by
  rw [ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨T, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (tp_arrTable_chain hc (by omega)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, tp_arrTable_chain hc (by omega)⟩

end Chains

theorem cent2B_ok : rawChainOK 315 (cent2BStrong.extract 0 2)
    cent2BStrong (([0, 3] : List (Fin 315)).map Fin.val).toArray cent2BWords 4 = true := by
  have hc := cent2B_check.1
  rwa [← cent2BBase_eq] at hc

theorem crT_parts :
    rawChainOK 315 (crTStrong.extract 0 3) crTStrong
      (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray crTWords 4 = true ∧
    inP crTStrong[0]! = true ∧ inP (CFSG.Monster.B.Co2.Native.compA 315 crTStrong[2]! outerArr) =
      true := by
  have h := crTCheck_eq
  simp only [crTCheck, Bool.and_eq_true, ← crTBase_eq] at h
  obtain ⟨hch, -⟩ := h
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at hch
  exact ⟨hch.1.1.1.1.1.1.1, hch.1.1.1.1.1.2, hch.1.1.1.2⟩

theorem c2BGens_eq : c2BGens = (List.range 2).map fun i => arrTable 315 cent2BStrong[i]! := rfl

theorem crTGens_eq : crTGens = (List.range 3).map fun i => arrTable 315 crTStrong[i]! := rfl

theorem genOf_c2BGens :
    genOf 315 c2BGens = centralizerIn P permA := by
  have he : genOf 315 c2BGens = cent2BChain.originalSubgroup := by
    rw [c2BGens_eq, genOf_chain (hk := by decide) (hb := by decide) cent2B_ok]
    rfl
  rw [he]
  refine Subgroup.eq_of_le_of_card_ge cent2B_facts.1 ?_
  rw [inner_classes.2.2.1, cent2B_facts.2.1]

theorem genOf_crTGens :
    genOf 315 crTGens = centralizerIn R permTwoA := by
  rw [crTGens_eq, genOf_chain (hk := by decide) (hb := by decide) crT_parts.1,
    centralizerIn_R_permTwoA.1]
  rfl

theorem crT_gen0_mem :
    CFSG.Monster.B.Co2.permOfArr 315 crTStrong[0]! ∈ P :=
  (mem_P_iff (rep_permOfArr_of_chainOK crT_parts.1 (by decide))).1 crT_parts.2.1

theorem crT_gen2_outer :
    CFSG.Monster.B.Co2.permOfArr 315 crTStrong[2]! * permU ∈ P :=
  (mem_P_iff (CFSG.Monster.B.Co2.rep_compA
    (rep_permOfArr_of_chainOK crT_parts.1 (by decide)) rep_permU)).1 crT_parts.2.2

theorem exists_odd_gens_c2A :
    ∃ x y : Equiv.Perm (Fin 315), x ∈ centralizerIn P permTwoA ∧
      y ∈ centralizerIn P permTwoA ∧ orderOf x = 5 ∧ orderOf y = 5 ∧
      closure {x, y} = centralizerIn P permTwoA :=
  Certificates.certificate22400.1

theorem exists_s0 :
    ∃ S₀ : Subgroup (Equiv.Perm (Fin 315)), S₀ ≤ centralizerIn P permTwoA ∧
      Nat.card S₀ = 128 ∧ permTwoA ∈ S₀ ∧
      Nat.card ↥(centralizerIn R permTwoA ⊓ centralizer (S₀ : Set (Equiv.Perm (Fin 315)))) =
        2 :=
  Certificates.certificate22400.2.1

theorem exists_perfect_sixty :
    ∃ G : Subgroup (Equiv.Perm (Fin 315)), G ≤ centralizerIn P permA ∧ Nat.card G = 60 ∧
      ⁅G, G⁆ = G :=
  Certificates.certificate22400.2.2.1

end CFSG.ComponentClassification.HarrisLit.EndB
