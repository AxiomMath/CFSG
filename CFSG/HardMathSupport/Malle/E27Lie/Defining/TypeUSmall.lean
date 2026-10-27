module

public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepA
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepB
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepC
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepD

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P
  CFSG.LieType.Multipliers.U43

theorem false_of_typeTwistedA_two_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 3 ∧ q.exponent = 1)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := CFSG.AGLEmbedding.kFactUnitarySylowStructure ↥K 3 ⟨.twistedA 2 q, hv⟩
    (by norm_num) ⟨q, hq.1, rfl⟩ ⟨e⟩
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 ↥K))
  have hS₀ : Nat.card (S₀ : Subgroup ↥K) = 27 := by
    rw [(hS S₀).1]
    simp [hq.2]
  have hRK : R ≤ K := h.le_of_mem hz
  have hR' : Nat.card (R.subgroupOf K) = 27 := by
    rw [← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  let P : Sylow 3 ↥K := Sylow.ofCard (R.subgroupOf K)
    (by rw [hR', ← hS₀, S₀.card_eq_multiplicity])
  have hab : ∀ a ∈ (P : Subgroup ↥K), ∀ b ∈ (P : Subgroup ↥K), a * b = b * a := by
    intro a ha b hb
    have hc := congrArg (Subtype.val : R → X)
      (h.elem.1.is_comm.comm (⟨a, ha⟩ : R) ⟨b, hb⟩)
    exact Subtype.ext hc
  have hcomm := (hS P).2.1
  have h1 : ⁅(P : Subgroup ↥K), (P : Subgroup ↥K)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab a ha b hb
  have h2 : (P : Subgroup ↥K) ⊓ Subgroup.centralizer ((P : Subgroup ↥K) : Set ↥K) = P :=
    inf_eq_left.mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hab a ha b hb).symm
  rw [h1, h2] at hcomm
  have hc := congrArg (fun H : Subgroup ↥K => Nat.card H) hcomm
  simp only [Subgroup.card_bot] at hc
  have : Nat.card (P : Subgroup ↥K) = 27 := hR'
  omega

theorem false_of_typeTwistedA_three_three {X : Type} [Group X]
    [Finite X] {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.p = 3 ∧ q.exponent = 1)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  rw [hq.1, hq.2] at hcl
  obtain ⟨θ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.nonempty_mulEquiv_X₀_of_classical hcl
  have hH : Nat.card p3.H = 729 := card_p3
  have hH3 : IsPGroup 3 p3.H := IsPGroup.of_card (n := 6) (by rw [hH]; norm_num)
  have key : ∀ r : ℕ, 81 ≤ Nat.card (p3.H ⊓ Subgroup.centralizer ({ev r} : Set X₀) : Subgroup X₀) →
      81 ∣ Nat.card (Subgroup.centralizer ({ev r} : Set X₀)) := fun r hr =>
    (eightyOne_dvd_card_of_isPGroup (hH3.to_le inf_le_left) hr).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  refine E27Config.false_of_centralizer_kill h hz θ p3.H ?_ fun s hs hs3 hs1 => ?_
  · rw [hH, card_X₀]
    have h3 : (3265920 : ℕ) = 3 ^ 6 * 4480 := by norm_num
    rw [h3, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · obtain ⟨k, hk, rfl⟩ := p3.exists_eq_elem p3_chkBase p3_chkTree p3_chkClosed
      (by show 0 < 729; norm_num) hs
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hs1 p3.elem_zero
    obtain ⟨l, hl1, hl4, c, hc⟩ := p3_exists_conj_rep hk hk0 hs3
    rw [← card_centralizer_map_equiv (MulAut.conj c) (p3.elem k), MulAut.conj_apply, hc]
    interval_cases l
    · refine key _ ?_
      have hle : p3.H ≤ Subgroup.centralizer ({ev (repW 1)} : Set X₀) :=
        p3.H_le_centralizer p3_chkComGens_A
      rw [inf_eq_left.mpr hle, hH]
      norm_num
    · refine key _ (le_trans ?_ (p3.le_card_inf_centralizer p3_chkBase p3_chkTree p3_chkSorted
        p3_chkComIdx_B))
      rw [lengths_B.2.2]
      norm_num
    · refine key _ (le_trans ?_ (p3.le_card_inf_centralizer p3_chkBase p3_chkTree p3_chkSorted
        p3_chkComIdx_C))
      rw [lengths_C.2.2]
      norm_num
    · refine key _ (le_trans ?_ (p3.le_card_inf_centralizer p3_chkBase p3_chkTree p3_chkSorted
        p3_chkComIdx_D))
      rw [lengths_D.2.2]

end CFSG.HardMathSupport.Malle.E27Lie
