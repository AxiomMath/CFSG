module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAPcCover
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClasses
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import Certificates.Certificate13624
public import Certificates.Certificate13625
public import Certificates.Certificate13626
public import Certificates.Certificate13627
public import CFSG.Monster.Existence.BabyW2Classes

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.GMS CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.B
  CFSG.Monster.B.Pinned

@[expose] def TwoBCent (s : B) : Prop :=
  ∃ t : B, BabyInv 1 t ∧ t ∈ Subgroup.centralizer ({s} : Set B)

theorem twoBCent_conj {s : B} (h : TwoBCent s) (c : B) : TwoBCent (c * s * c⁻¹) := by
  obtain ⟨t, ht, hts⟩ := h
  refine ⟨c * t * c⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht.1
  · exact (CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj
      (isConj_iff.2 ⟨c, rfl⟩)).symm.trans ht.2
  · rw [Subgroup.mem_centralizer_singleton_iff] at hts ⊢
    calc c * t * c⁻¹ * (c * s * c⁻¹) = c * (t * s) * c⁻¹ := by group
      _ = c * (s * t) * c⁻¹ := by rw [hts]
      _ = c * s * c⁻¹ * (c * t * c⁻¹) := by group

theorem centralizer_pow_eq_of_coprime_five {s : B} (hs : s ^ 5 = 1) {k : ℕ}
    (hk : Nat.Coprime k 5) :
    Subgroup.centralizer ({s ^ k} : Set B) = Subgroup.centralizer ({s} : Set B) :=
  PcCover.centralizer_pow_eq_of_coprime' (by norm_num) hs hk

theorem twoBCent_pow_iff {s : B} (hs : s ^ 5 = 1) {k : ℕ} (hk : Nat.Coprime k 5) :
    TwoBCent (s ^ k) ↔ TwoBCent s := by
  unfold TwoBCent
  rw [centralizer_pow_eq_of_coprime_five hs hk]

section TwoB

theorem twoBCent_of_inv {W s : B} (hsq : W * W = 1) (hne : W ≠ 1)
    (hrk : Matrix.rank (bMat W - 1) = 2048) (hcm : W * s = s * W) : TwoBCent s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf W = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) hne
  exact ⟨W, CFSG.Monster.Existence.babyInv_one_of_rank_2048 ho hrk,
    Subgroup.mem_centralizer_singleton_iff.2 hcm⟩

theorem twoBCent_targets : ∀ i ∈ CFSG.KC.BM.PcFive.targets,
    TwoBCent (CFSG.KC.BM.PcFive.psi xFive (CFSG.KC.BM.PcFive.qW xFive hFive)
      (CFSG.KC.BM.PcFive.zW xFive hFive) (CFSG.KC.BM.PcFive.dec i)) := by
  intro i hi
  have hi' : i ∈ [1, 660, 30] ∨ i ∈ [3125, 3126, 3127] := by
    simp only [CFSG.KC.BM.PcFive.targets, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rcases hi' with h | h
  · obtain ⟨W, hsq, hne, hrk, hcm⟩ := Certificates.certificate13626 i h
    exact twoBCent_of_inv hsq hne hrk hcm
  · obtain ⟨W, hsq, hne, hrk, hcm⟩ := Certificates.certificate13627 i h
    exact twoBCent_of_inv hsq hne hrk hcm

end TwoB

section Cover

theorem bFiveTwoBCover_holds : BFiveTwoBCover := by
  obtain ⟨hC, hφ⟩ := Certificates.certificate13624
  obtain ⟨R, F⟩ := Certificates.certificate13625
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hcard : Nat.card B = 5 ^ 6 * 265906014798491276235365154816 := by
    rw [CFSG.RankThree.OddKernel.card_B_eq]
    norm_num
  have hm : ¬ 5 ∣ 265906014798491276235365154816 := by norm_num
  exact CFSG.KC.BM.PcFive.forall_of_census R.pcHyp hφ R.z1 hC hcard hm TwoBCent
    (fun x c hx => twoBCent_conj hx c) (fun x hx k hk => twoBCent_pow_iff hx hk)
    (fun j hj => ⟨_, F.2.2.2.1 j hj⟩) (fun m hm => ⟨_, F.2.2.2.2 m hm⟩) twoBCent_targets

end Cover

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
