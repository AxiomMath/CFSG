module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFAK148G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6TwoG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


private theorem ord_g2_two_pow_four {a : ℕ} (ha : 1 ≤ a) :
    ∃ O, Odd O ∧ O % 4 = 1 ∧ orderG2 (2 ^ a) = 2 ^ (a * 6) * O := by
  have h6 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 6)
  have h2 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 2)
  have p6 : 1 ≤ (2 ^ a) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have p2 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e1 : ((2 ^ a) ^ 6 - 1) % 4 = 3 := by omega
  have e2 : ((2 ^ a) ^ 2 - 1) % 4 = 3 := by omega
  have hmod : (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) % 4 = 1 := by
    rw [Nat.mul_mod, e1, e2]
  refine ⟨((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1),
    (odd_pow_two_pow_sub_one ha (by norm_num)).mul (odd_pow_two_pow_sub_one ha (by norm_num)),
    hmod, ?_⟩
  simp only [orderG2]
  rw [pow_mul 2 a 6, mul_assoc]

private theorem ord_g2_ne_A2 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderG2 (2 ^ a) ≠ orderA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := ord_g2_two_pow_four ha
  have hg := orderA_two_mul_gcd (2 ^ b)
  rw [← h, e₁] at hg
  have hodd_g : Odd (Nat.gcd 3 (2 ^ b - 1)) :=
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_sub_one hb (by norm_num))
  have hg' : 2 ^ (a * 6) * (O₁ * Nat.gcd 3 (2 ^ b - 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) := by
    rw [← mul_assoc, hg, ← pow_mul]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb2 : b = 2 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb2, pow_mul]
    norm_num [Nat.pow_mod]
  have hg3 : Nat.gcd 3 (2 ^ b - 1) = 3 := by
    apply Nat.gcd_eq_left
    omega
  rw [hg3] at hprod
  have e2 := mod_four_sq hb
  have e3 := mod_four_cube_sub hb
  have h4 := congrArg (· % 4) hprod
  simp only [Nat.mul_mod O₁ 3, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e2, e3] at h4
  omega

private theorem ord_g2_ne_U3 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderG2 (2 ^ a) ≠ orderTwistedA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := ord_g2_two_pow_four ha
  have hg := orderTwistedA_mul_gcd (r := 2) (m := b) (by norm_num) hb
  rw [← h, e₁, twP_two] at hg
  have hodd_g : Odd (Nat.gcd (2 + 1) (2 ^ b + 1)) := odd_gcd_twisted hb
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_add_one hb (by norm_num))
  have hg' : 2 ^ (a * 6) * (O₁ * Nat.gcd (2 + 1) (2 ^ b + 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) := by
    rw [← mul_assoc, hg, ← pow_mul]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb2 : b = 2 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb2, pow_mul]
    norm_num [Nat.pow_mod]
  have hg3 : Nat.gcd (2 + 1) (2 ^ b + 1) = 1 := by
    have h3 : ¬ 3 ∣ 2 ^ b + 1 := by omega
    exact (Nat.prime_three.coprime_iff_not_dvd).2 h3
  rw [hg3] at hprod
  have e2 := mod_four_sq hb
  have e3 := mod_four_cube_add hb
  have h4 := congrArg (· % 4) hprod
  simp only [mul_one, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e2, e3] at h4
  omega

private theorem ord_u33_ne_A2 {b : ℕ} (hb : 1 ≤ b) : (6048 : ℕ) ≠ orderA 2 (2 ^ b) := by
  intro h
  have hg := orderA_two_mul_gcd (2 ^ b)
  rw [← h] at hg
  have hodd_g : Odd (Nat.gcd 3 (2 ^ b - 1)) :=
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_sub_one hb (by norm_num))
  have hg' : 2 ^ 5 * (189 * Nat.gcd 3 (2 ^ b - 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) := by
    rw [pow_mul, ← hg]
    ring
  have := (two_pow_mul_odd_inj ((by decide : Odd 189).mul hodd_g) hP hg').1
  omega

private theorem ord_u33_ne_U3 {b : ℕ} (hb : 1 ≤ b) : (6048 : ℕ) ≠ orderTwistedA 2 (2 ^ b) := by
  intro h
  have hg := orderTwistedA_mul_gcd (r := 2) (m := b) (by norm_num) hb
  rw [← h] at hg
  have hg' : 2 ^ 5 * (189 * Nat.gcd (2 + 1) (2 ^ b + 1)) =
      2 ^ (b * (2 * (2 + 1) / 2)) * twP 2 (2 ^ b) := by
    rw [← hg]
    ring
  have h3 := (two_pow_mul_odd_inj ((by decide : Odd 189).mul (odd_gcd_twisted hb))
    (odd_twP hb) hg').1
  have e : (2 * (2 + 1) / 2 : ℕ) = 3 := by norm_num
  rw [e] at h3
  omega

section Certs


set_option linter.unusedSectionVars false

private theorem card_of_tyF {T : Type} [Group T] [Finite T] (h : catalogIs T (S265.tyF 3)) :
    ∃ m, 1 ≤ m ∧ (Nat.card T = orderA 2 (2 ^ m) ∨ Nat.card T = orderTwistedA 2 (2 ^ m)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      have hi' : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1 := hi
      obtain ⟨hr, hq, -⟩ := hi'
      obtain rfl : r = 2 := by omega
      refine ⟨q.exponent, q.exponent_pos, Or.inl ?_⟩
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 2 q, hv⟩ T ⟨e⟩]
      show orderA 2 q.card = _
      rw [TauCeti.PrimePower.card_def, hq]
    | twistedA r q =>
      have hi' : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1 := hi
      obtain ⟨hr, hq, -⟩ := hi'
      obtain rfl : r = 2 := by omega
      refine ⟨q.exponent, q.exponent_pos, Or.inr ?_⟩
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ T ⟨e⟩]
      show orderTwistedA 2 q.card = _
      rw [TauCeti.PrimePower.card_def, hq]
    | _ => exact False.elim hi

private theorem not_comm_of_quasisimple {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    ¬ IsMulCommutative Q := by
  intro hc
  have hle : commutator Q ≤ ⊥ := by
    show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (IsMulCommutative.is_comm.comm a b)
  have htop : commutator Q = ⊤ := hq.1
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ commutator Q := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ commutator Q := by rw [htop]; exact Subgroup.mem_top y
    have hx' := hle hx
    have hy' := hle hy
    rw [Subgroup.mem_bot] at hx' hy'
    rw [hx', hy']
  haveI := hq.2
  exact (not_subsingleton (Q ⧸ Subgroup.center Q)) hsub

variable {G : Type} [Group G] [Finite G]

private theorem pSimple_equiv_of_lie {I : Subgroup G} (hQI : CFSG.Open.IsQuasisimple (PQuot 3 I))
    (idx : TauCeti.ValidLieTypeIndex) (e : PQuot 3 I ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    Nonempty (PSimple 3 I ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
  haveI : IsSimpleGroup (PQuot 3 I) := by
    haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie idx).Group := (CFSG.Assembly.lie_finite_simple idx).2
    exact MulEquiv.isSimpleGroup e
  have hcenter : Subgroup.center (PQuot 3 I) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (not_comm_of_quasisimple hQI)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans e⟩

theorem false_of_isTD4 {X S : Subgroup G} {b : G} (hS : GLAPComponent 3 X S)
    (hchev : IsChevSimple 2 (PSimple 3 S)) (hb3 : b ^ 3 = 1) (hTD4 : IsTD4 3 S)
    (hNI : NonInner 3 b S) (hcent : centCard2 3 S b = Nat.sqrt (card2 3 S))
    (hI : Ipart 3 S b ≠ ⊥) (hty : catalogIs (PSimple 3 (Ipart 3 S b)) (S265.tyF 3)) : False := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hcore := FR.Res.td4Core_holds X S b hNI.1 hS hchev hb3 hTD4 hNI
    (FR.exists_perfect_of_ipart hp3 hNI.1 hb3 hI)
  rw [FR.fixSub_indAut hNI.1] at hcore
  obtain ⟨E, hEC, hE, -, hperf, -, -⟩ := hcore
  obtain ⟨J₀, hJ₀, hIeq, -⟩ := FR.ipart_single hp3 hNI.1 hb3 hE hEC hperf hI
  rw [hIeq] at hty
  obtain ⟨m, hm1, hcardT⟩ := card_of_tyF hty
  have hfix : Nat.sqrt (card2 3 S) ≤ 2 * twoPart (Nat.card ↥(lemma102_fixSub 3 hNI.1)) := by
    rw [← hcent, lemma102_centCard2_eq_fixSub 3 hNI.1]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hQI : CFSG.Open.IsQuasisimple (PQuot 3 J₀) := isQuasisimple_pQuot_of_glaPComponent hp3 hJ₀
  rcases k148_outer K148G2SimpleFact_holds K148TwoG2Fact_holds hS hchev hTD4 hNI.1 hb3 hNI hJ₀ hfix
    with ⟨q, hv, hq2, -, ⟨eG2⟩⟩ | hU3
  · obtain ⟨eS⟩ := pSimple_equiv_of_lie hQI ⟨.G2 q, hv⟩ eG2
    have hcard : Nat.card (PSimple 3 J₀) = orderG2 (2 ^ q.exponent) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.G2 q, hv⟩ _ ⟨eS⟩]
      show orderG2 q.card = _
      rw [TauCeti.PrimePower.card_def, hq2]
    rcases hcardT with h | h
    · exact ord_g2_ne_A2 q.exponent_pos hm1 (hcard.symm.trans h)
    · exact ord_g2_ne_U3 q.exponent_pos hm1 (hcard.symm.trans h)
  · obtain ⟨i, hi, ⟨eU⟩⟩ := hU3
    cases i with
    | cyclic _ _ => exact False.elim hi
    | alternating _ _ => exact False.elim hi
    | sporadic _ => exact False.elim hi
    | lie idx =>
      obtain ⟨eS⟩ := pSimple_equiv_of_lie hQI idx eU
      have hcard : Nat.card (PSimple 3 J₀) = 6048 :=
        card_isU33 CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hi, ⟨eS⟩⟩
      rcases hcardT with h | h
      · exact ord_u33_ne_A2 hm1 (hcard.symm.trans h)
      · exact ord_u33_ne_U3 hm1 (hcard.symm.trans h)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
