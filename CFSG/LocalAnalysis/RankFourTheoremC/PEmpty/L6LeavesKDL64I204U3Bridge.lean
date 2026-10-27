module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.UnitaryModel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB

theorem kdI204U3_notMulComm {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ¬ IsMulCommutative G := fun hc =>
  h ((@Group.is_simple_iff_prime_card G _ hc).1 inferInstance)

theorem kdI204U3_center_bot {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right fun ht =>
    kdI204U3_notMulComm h (Subgroup.center_eq_top_iff.1 ht)

theorem kdI204U3_commutator_top {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : commutator G = ⊤ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left fun hb =>
    kdI204U3_notMulComm h ((commutator_eq_bot_iff G).1 hb)

theorem kdI204U3_pPrimeCore_bot {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    {L : Subgroup Z} (hLn : L.Normal) [IsSimpleGroup ↥L] (hpL : p ∣ Nat.card ↥L)
    (hC : Subgroup.centralizer (L : Set Z) = ⊥) : CFSG.pPrimeCore p Z = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hNL : (N ⊓ L).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L).subgroupOf L) with h | h
  · refine eq_bot_iff.2 fun k hk => ?_
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro x hx
    have hcL : k * x * k⁻¹ * x⁻¹ ∈ L := L.mul_mem (hLn.conj_mem x hx k) (L.inv_mem hx)
    have hcN : k * x * k⁻¹ * x⁻¹ ∈ N := by
      have hc2 : x * k⁻¹ * x⁻¹ ∈ N := hN.conj_mem k⁻¹ (N.inv_mem hk) x
      have heq : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
      rw [heq]
      exact N.mul_mem hk hc2
    have hmem : (⟨k * x * k⁻¹ * x⁻¹, hcL⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hcN, hcL⟩)
    rw [h, Subgroup.mem_bot] at hmem
    have hc1 : k * x * k⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hmem
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)).symm
  · exfalso
    have hLN : L ≤ N := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (N ⊓ L).subgroupOf L := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
    have hcopL : Nat.Coprime p (Nat.card ↥L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopL hpL

theorem chev204Hyp_of_U3p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Z : Type} [Group Z] [Finite Z]
    {L : Subgroup Z} (hLn : L.Normal) (hU3 : P64IsU3p p ↥L)
    (hC : Subgroup.centralizer (L : Set Z) = ⊥) {B : Subgroup Z} (hB : IsElemAbelian p B)
    (hSC : ∀ y ∈ Subgroup.centralizer (B : Set Z), y ^ p = 1 → y ∈ B) :
    Chev204Hyp p L B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, hFld, hFin, hK, ⟨e⟩⟩ := hU3
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have e1 : ↥L ≃* StatedProj (StatedSU 3 (p ^ 1) K) := by rw [pow_one]; exact e
  have hnq : ((3 : ℕ), p ^ 1) ≠ ((3 : ℕ), (2 : ℕ)) := by
    intro h
    have h2 : p ^ 1 = 2 := (Prod.mk.inj h).2
    rw [pow_one] at h2
    omega
  have hadm : StatedLieAdmissible StatedLieTag.PSU 3 p 1 := ⟨hp, le_rfl, le_rfl, hnq⟩
  have hchevL : IsChevSimple p ↥L :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isChevSimple_of_statedPSU hadm hK1 e1
  have hsimpP : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ 1) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p 1 hK1 3 le_rfl hnq
  have hsimpL : IsSimpleGroup ↥L := e1.isSimpleGroup
  have hform := CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound ↥L 3 p 1
    ⟨hadm, K, hFld, hFin, hK1, ⟨e1⟩⟩
  have hpL : p ∣ Nat.card ↥L := by
    have hpz : (p : ℤ) ∣ ((p ^ 1 : ℕ) : ℤ) := by norm_num
    have hN : (p : ℤ) ∣ (Nat.card ↥L : ℤ) * (Nat.gcd 3 (p ^ 1 + 1) : ℤ) := by
      rw [hform.1]
      exact Dvd.dvd.mul_right (dvd_pow hpz (by norm_num)) _
    have hN' : p ∣ Nat.card ↥L * Nat.gcd 3 (p ^ 1 + 1) := by exact_mod_cast hN
    rcases (Nat.Prime.dvd_mul hp).1 hN' with h | h
    · exact h
    · exfalso
      have h3 : p ≤ 3 := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left _ _))
      omega
  have hnp : ¬ (Nat.card ↥L).Prime := by
    intro hprime
    have hpeq : p = Nat.card ↥L := (Nat.prime_dvd_prime_iff_eq hp hprime).1 hpL
    have h2 : ¬ 2 ∣ Nat.card ↥L := fun h => by
      have h2p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).1 h
      omega
    have h4 : 4 ≤ 2 ^ (Nat.card ↥L).factorization 2 := hform.2.2.2.1
    rw [Nat.factorization_eq_zero_of_not_dvd h2, pow_zero] at h4
    omega
  have hZL : Subgroup.center ↥L = ⊥ := kdI204U3_center_bot hnp
  have hcomm : commutator ↥L = ⊤ := kdI204U3_commutator_top hnp
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
  have hsimpQ : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := eQ.isSimpleGroup
  have hchevQ : IsChevSimple p (↥L ⧸ Subgroup.center ↥L) :=
    isChevSimple_of_mulEquiv eQ.symm hchevL
  have hq : CFSG.Open.IsQuasisimple ↥L := by
    unfold CFSG.Open.IsQuasisimple
    exact ⟨hcomm, hsimpQ⟩
  have hcomp : GLAPComponent p ⊤ L :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hq hpL le_top inferInstance
  have hcore : GLAPPrimeCore p Z = ⊥ := kdI204U3_pPrimeCore_bot hp hLn hpL hC
  have hscp : IsSCp p (⊤ : Subgroup Z) B := by
    refine ⟨le_top, hB, fun E _ hE hBE => le_antisymm ?_ hBE⟩
    intro y hy
    refine hSC y (Subgroup.mem_centralizer_iff.2 fun b hb => ?_) (hE.2 y hy)
    have hbE : b ∈ E := hBE hb
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hbE⟩ ⟨y, hy⟩)
  have hnormL : Subgroup.normalizer (L : Set Z) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hLn
  have hBN : B ≤ Subgroup.normalizer (L : Set Z) := by
    rw [hnormL]
    exact le_top
  exact ⟨hp, hp2, hcore, hcomp, hscp, hBN, hchevQ⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
