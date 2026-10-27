module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73E

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem normal_range_longSL2_odd [Finite K] (hodd : Odd (Nat.card K))
    (F : HypFrame (quadOdd 3 K) 3) {i j : Fin 3} (hij : i ≠ j) (s t : Bool) :
    ((F.longSL2 hij s t).range.subgroupOf (centralizer {F.longSL2 hij s t (-1)})).Normal := by
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set ρ := F.longSL2 hij s t with hρ
  set ρ' := F.longSL2 hij s (!t) with hρ'
  set fr := F.toFrame hij s t with hfr
  have hθ : ∀ A, spinAction (quadOdd 3 K) (ρ A) = fr.La A := spinAction_longSL2 F hij s t
  have hθ' : ∀ A, spinAction (quadOdd 3 K) (ρ' A) = fr.swap.La A := fun A => by
    rw [hρ', spinAction_longSL2, toFrame_not]
  have hmapJ : ρ.range.map (spinAction (quadOdd 3 K)) = fr.La.range :=
    map_longSL2_range F hij s t
  have hmapJ' : ρ'.range.map (spinAction (quadOdd 3 K)) = fr.swap.La.range := by
    rw [hρ', map_longSL2_range, toFrame_not]
  have hker2 : ∀ k ∈ (spinAction (quadOdd 3 K)).ker, k * k = 1 := fun k hk =>
    mul_self_eq_one_of_mem_ker_spinAction h2 hk
  rw [normal_subgroupOf_iff (range_longSL2_le_centralizer F hij s t)]
  intro a g ha hg
  have hgt : g * ρ (-1) = ρ (-1) * g := mem_centralizer_singleton_iff.mp hg
  set P := ρ.range.map (MulAut.conj g).toMonoidHom with hP
  have hPsq : P ≤ closure {x | ∃ y ∈ P, y * y = x} := by
    rw [hP, ← MonoidHom.range_comp]
    exact range_le_closure_mul_self_sl2 hodd _
  have hgO : spinAction (quadOdd 3 K) g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction (quadOdd 3 K) g)
  have hconj : spinAction (quadOdd 3 K) g * fr.La (-1) * (spinAction (quadOdd 3 K) g)⁻¹ =
      fr.La (-1) := by
    rw [← hθ, ← map_inv, ← map_mul, ← map_mul, hgt, mul_inv_cancel_right]
  have hfundP : IsFundamental (quadOdd 3 K) (P.map (spinAction (quadOdd 3 K))) (fr.La (-1)) := by
    have h := (IsFundamental.of_frame fr).conj hgO
    rw [hconj] at h
    rwa [hP, map_conj_map, hmapJ]
  obtain ⟨L', -, -, -, huniq⟩ := (IsFundamental.of_frame fr).exists_twin hodd
  have hmem : g * a * g⁻¹ ∈ P := ⟨a, ha, rfl⟩
  rcases huniq _ hfundP with h | h
  · refine le_of_le_comap_map_of_mul_self (spinAction (quadOdd 3 K))
      (ker_spinAction_le_center (quadOdd 3 K)) hker2 hPsq ?_ hmem
    rw [hmapJ, ← h]
    exact le_comap_map _ P
  · exfalso
    have hfund' : IsFundamental (quadOdd 3 K) (ρ'.range.map (spinAction (quadOdd 3 K)))
        (fr.La (-1)) := by
      rw [hmapJ']
      exact IsFundamental.of_frame_swap fr
    have hJ' : ρ'.range.map (spinAction (quadOdd 3 K)) = L' := by
      rcases huniq _ hfund' with h' | h'
      · exact absurd (hmapJ'.symm.trans h') (Frame.La_range_ne_swap_La_range fr).symm
      · exact h'
    have hPJ' : P ≤ ρ'.range := le_of_le_comap_map_of_mul_self (spinAction (quadOdd 3 K))
      (ker_spinAction_le_center (quadOdd 3 K)) hker2 hPsq
      (by rw [hJ', ← h]; exact le_comap_map _ P)
    have htP : ρ (-1) ∈ P := by
      refine ⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩, ?_⟩
      show g * ρ (-1) * g⁻¹ = ρ (-1)
      rw [hgt, mul_inv_cancel_right]
    obtain ⟨A, hA⟩ := hPJ' htP
    have hA1 : A = -1 := by
      apply fr.swap.La_injective
      rw [← hθ', hA, hθ, Frame.La_swap_neg_one]
    rw [hA1, hρ', longSL2_neg_one_not F hij hQ s t] at hA
    exact spinGroup.negOne_ne_one (quadOdd 3 K) hQ (mul_right_cancel (hA.trans (one_mul _).symm))

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem normal_spinJ_odd :
    ((spinJ₁ K).subgroupOf (centralizer {tSeven K})).Normal ∧
      ((spinJ₂ K).subgroupOf (centralizer {tSeven K})).Normal ∧
        ((spinJ₃ K).subgroupOf (centralizer {tSeven K})).Normal := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have hodd := odd_card_spin hp hp2 hK
  refine ⟨normal_range_shortSeven h2,
    normal_range_longSL2_odd hodd _ fin3_zero_ne_one true true, ?_⟩
  rw [← centralizer_longSL2_true_false hp hp2 hK]
  exact normal_range_longSL2_odd hodd _ fin3_zero_ne_one true false

theorem pPrimeCore_spinJ_odd :
    pPrimeCore 2 ↥(spinJ₁ K) = ⊥ ∧ pPrimeCore 2 ↥(spinJ₂ K) = ⊥ ∧
      pPrimeCore 2 ↥(spinJ₃ K) = ⊥ := by
  have hodd := odd_card_spin hp hp2 hK
  exact ⟨pPrimeCore_range_sl2_odd hodd _ injective_shortSeven,
    pPrimeCore_range_sl2_odd hodd _ (longSL2_injective _ fin3_zero_ne_one true true),
    pPrimeCore_range_sl2_odd hodd _ (longSL2_injective _ fin3_zero_ne_one true false)⟩

theorem card_ker_spinMulOdd : Nat.card (spinMulOdd (odd_card_spin hp hp2 hK)).ker = 2 := by
  obtain ⟨hzz, hz1, hzc, htt, -, -, hz1', ht2', hzt3, -⟩ := spinZ_facts hp hp2 hK
  set w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K :=
    ((⟨spinZ K, hz1'⟩, ⟨tSeven K, ht2'⟩), ⟨spinZ K * tSeven K, hzt3⟩) with hw
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  have hww : w * w = 1 :=
    Prod.ext (Prod.ext (Subtype.ext hzz) (Subtype.ext htt)) (Subtype.ext hztzt)
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) h)
  have hker : (spinMulOdd (odd_card_spin hp hp2 hK)).ker = zpowers w := by
    ext x
    rw [mem_ker_spinMulOdd_iff hp hp2 hK]
    constructor
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact mem_zpowers _
    · exact eq_one_or_eq_of_mem_zpowers_of_mul_self hww
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hker, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hww) hw1

theorem card_spinE_odd : 2 * Nat.card (spinE K) = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 3 := by
  have h := card_ker_mul_card_range (spinMulOdd (odd_card_spin hp hp2 hK))
  rw [card_ker_spinMulOdd hp hp2 hK, range_spinMulOdd, Nat.card_prod, Nat.card_prod,
    card_range_sl2 _ injective_shortSeven,
    card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true true),
    card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true false)] at h
  rw [h]
  ring

theorem normal_spinE_odd : ((spinE K).subgroupOf (centralizer {tSeven K})).Normal := by
  obtain ⟨h1, h2, h3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ_odd (K := K) hp hp2 hK
  rw [subgroupOf_sup (sup_le h1 h2) h3, subgroupOf_sup h1 h2]
  exact Subgroup.sup_normal _ _

theorem index_spinE_dvd_odd :
    ((spinE K).subgroupOf (centralizer {tSeven K})).index ∣ 2 ^ 4 := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hC := card_centralizer_tSeven_dvd (two_ne_zero_spin hp hp2 hK)
  have hE := card_spinE_odd hp hp2 hK
  have hEC := card_mul_index ((spinE K).subgroupOf (centralizer {tSeven K}))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv] at hEC
  have hpos : 0 < Nat.card (spinE K) := Nat.card_pos
  have h16 : 8 * Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 = Nat.card (spinE K) * 2 ^ 4 := by
    rw [mul_assoc, ← mul_pow, ← hE]
    ring
  rw [← hEC, h16] at hC
  exact Nat.dvd_of_mul_dvd_mul_left hpos hC

theorem le_spinE_of_coprime_odd {P : Subgroup (spinGroup (quadOdd 3 K))}
    (hPC : P ≤ centralizer {tSeven K}) (hP : Nat.Coprime 2 (Nat.card P)) : P ≤ spinE K := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  exact le_of_coprime_of_index_dvd (normal_spinE_odd hp hp2 hK) (index_spinE_dvd_odd hp hp2 hK)
    hPC hP

theorem mul_self_eq_one_of_commute_odd {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinE K)
    (h1 : ∀ a ∈ spinJ₁ K, x * a = a * x) (h2 : ∀ b ∈ spinJ₂ K, x * b = b * x)
    (h3 : ∀ c ∈ spinJ₃ K, x * c = c * x) : x * x = 1 := by
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have hodd := odd_card_spin hp hp2 hK
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  rw [← range_spinMulOdd hodd] at hx
  obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩, rfl⟩ := hx
  rw [spinMulOdd_apply] at h1 h2 h3 ⊢
  change a * b * c * (a * b * c) = 1
  change ∀ a' ∈ spinJ₁ K, a * b * c * a' = a' * (a * b * c) at h1
  change ∀ b' ∈ spinJ₂ K, a * b * c * b' = b' * (a * b * c) at h2
  change ∀ c' ∈ spinJ₃ K, a * b * c * c' = c' * (a * b * c) at h3
  have hac : ∀ a' ∈ spinJ₁ K, a * a' = a' * a := fun a' ha' =>
    comm_left_of_comm (commute_spinJ₁_spinJ₂ ha' hb).symm (commute_spinJ₁_spinJ₃ ha' hc).symm
      (h1 a' ha')
  have hbc : ∀ b' ∈ spinJ₂ K, b * b' = b' * b := fun b' hb' =>
    comm_mid_of_comm (commute_spinJ₁_spinJ₂ ha hb')
      (commute_spinJ₂_spinJ₃_odd hodd hb' hc).symm (h2 b' hb')
  have hcc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c := fun c' hc' =>
    comm_right_of_comm (commute_spinJ₁_spinJ₃ ha hc') (commute_spinJ₂_spinJ₃_odd hodd hb hc')
      (h3 c' hc')
  have ha2 : a * a = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hzz
      (mem_zpowers_of_commute_spinJ₁_odd hodd ha hac) with rfl | rfl
    · exact mul_one 1
    · exact hzz
  have hb2 : b * b = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt
      (mem_zpowers_of_commute_spinJ₂_odd hodd hb hbc) with rfl | rfl
    · exact mul_one 1
    · exact htt
  have hc2 : c * c = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt
      (h3eq ▸ mem_zpowers_of_commute_spinJ₃_odd hodd hc hcc) with rfl | rfl
    · exact mul_one 1
    · exact hztzt
  have hab : Commute a b := commute_spinJ₁_spinJ₂ ha hb
  have hac' : Commute a c := commute_spinJ₁_spinJ₃ ha hc
  have hbc' : Commute b c := commute_spinJ₂_spinJ₃_odd hodd hb hc
  rw [← pow_two, (hac'.mul_left hbc').mul_pow, hab.mul_pow]
  simp only [pow_two, ha2, hb2, hc2, one_mul]

theorem pPrimeCore_centralizer_tSeven_odd :
    pPrimeCore 2 ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) = ⊥ := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ_odd (K := K) hp hp2 hK
  obtain ⟨o1, o2, o3⟩ := pPrimeCore_spinJ_odd (K := K) hp hp2 hK
  rw [pPrimeCore_eq_bot_iff]
  intro O hOn hOc
  have hO'c : Nat.Coprime 2 (Nat.card (O.map (centralizer {tSeven K}).subtype)) := by
    rwa [card_map_of_injective (subtype_injective _)]
  have hO'E := le_spinE_of_coprime_odd hp hp2 hK (map_subtype_le O) hO'c
  rw [eq_bot_iff]
  intro x hx
  have hxE : (x : spinGroup (quadOdd 3 K)) ∈ spinE K := hO'E ⟨x, hx, rfl⟩
  have hxx : (x : spinGroup (quadOdd 3 K)) * x = 1 :=
    mul_self_eq_one_of_commute_odd hp hp2 hK hxE
      (fun _ ha => commute_of_mem_of_pPrimeCore_eq_bot l1 n1 o1 hOn hOc hx ha)
      (fun _ hb => commute_of_mem_of_pPrimeCore_eq_bot l2 n2 o2 hOn hOc hx hb)
      (fun _ hc => commute_of_mem_of_pPrimeCore_eq_bot l3 n3 o3 hOn hOc hx hc)
  have hxx' : x ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hxx
  have ho : orderOf x ∣ Nat.gcd 2 (Nat.card O) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxx') (Subgroup.orderOf_dvd_natCard O hx)
  rw [Nat.Coprime.gcd_eq_one hOc, Nat.dvd_one, orderOf_eq_one_iff] at ho
  exact (mem_bot).mpr ho

end Card

end CFSG.ComponentClassification.HarrisLit.T1
