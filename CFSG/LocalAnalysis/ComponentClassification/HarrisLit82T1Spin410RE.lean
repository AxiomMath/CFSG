module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

noncomputable abbrev spinJ₁ (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  (shortSeven K).range

noncomputable abbrev spinJ₂ (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true).range

noncomputable abbrev spinJ₃ (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false).range

noncomputable abbrev spinE (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  spinJ₁ K ⊔ spinJ₂ K ⊔ spinJ₃ K

theorem SL2Pair.commute_toFun_of_commute {A : Type*} [Ring A] [Algebra K A] (P : SL2Pair A)
    {y : A} (hX : Commute P.X y) (hY : Commute P.Y y) (M : Matrix (Fin 2) (Fin 2) K) :
    Commute (P.toFun M) y := by
  unfold SL2Pair.toFun
  exact (((((hX.mul_left hY).smul_left _).add_left (hX.smul_left _)).add_left
    (hY.smul_left _)).add_left ((hY.mul_left hX).smul_left _)).add_left
    (((Commute.one_left y).sub_left (hX.mul_left hY)).sub_left (hY.mul_left hX))

theorem polar_vec_short {i : Fin 3} (hi : i ≠ 2) (r : Bool) :
    polar (quadOdd 3 K) ((oddFrame 3 K).vec i r) (oddFrame 3 K).z = 0 ∧
      ∀ u, polar (quadOdd 3 K) ((oddFrame 3 K).vec i r) ((oddFrame 3 K).vec 2 u) = 0 :=
  ⟨(oddFrame 3 K).polar_vec_z i r, fun u => (oddFrame 3 K).polar_vec_of_ne hi r u⟩

theorem commute_shortSeven_longSL2 (t : Bool) (M N : SL(2, K)) :
    Commute (shortSeven K M) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true t N) := by
  refine LieType.Universal.Spin.commute_of_coe ?_
  rw [OddFrame.coe_shortSL2, HypFrame.coe_longSL2]
  have h0 := polar_vec_short (K := K) (i := 0) (by decide)
  have h1 := polar_vec_short (K := K) (i := 1) (by decide)
  set P := (oddFrame 3 K).shortPair 2 true with hP
  set R := (oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true t with hR
  have hXX : Commute R.X P.X := commute_ι_mul_ι _ (h0 true).1 ((h0 true).2 true) (h1 t).1
    ((h1 t).2 true)
  have hXY : Commute R.X P.Y := commute_ι_mul_ι _ ((h0 true).2 false) (h0 true).1
    ((h1 t).2 false) (h1 t).1
  have hYX : Commute R.Y P.X := commute_ι_mul_ι _ (h1 (!t)).1 ((h1 (!t)).2 true) (h0 false).1
    ((h0 false).2 true)
  have hYY : Commute R.Y P.Y := commute_ι_mul_ι _ ((h1 (!t)).2 false) (h1 (!t)).1
    ((h0 false).2 false) (h0 false).1
  refine SL2Pair.commute_toFun_of_commute P ?_ ?_ _
  · exact (SL2Pair.commute_toFun_of_commute R hXX hYX _).symm
  · exact (SL2Pair.commute_toFun_of_commute R hXY hYY _).symm

theorem commute_spinJ₁_spinJ₂ {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (hb : b ∈ spinJ₂ K) : a * b = b * a := by
  obtain ⟨M, rfl⟩ := ha
  obtain ⟨N, rfl⟩ := hb
  exact commute_shortSeven_longSL2 true M N

theorem commute_spinJ₁_spinJ₃ {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (hb : b ∈ spinJ₃ K) : a * b = b * a := by
  obtain ⟨M, rfl⟩ := ha
  obtain ⟨N, rfl⟩ := hb
  exact commute_shortSeven_longSL2 false M N

theorem commutator_eq_bot_of_le_center {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hAB : ⁅A, B⁆ ≤ center G) : ⁅A, B⁆ = ⊥ := by
  have hcen : ∀ H : Subgroup G, ⁅⁅A, B⁆, H⁆ = ⊥ := fun H =>
    commutator_eq_bot_iff_le_centralizer.mpr (hAB.trans (center_le_centralizer _))
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := hcen A
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by rw [commutator_comm B A]; exact hcen A
  have h := commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := B) h1 h2
  rwa [hA] at h

theorem commutator_spinJ₂_spinJ₃ [Finite K] (h4 : 4 ≤ Nat.card K) :
    ⁅spinJ₂ K, spinJ₃ K⁆ = ⊥ := by
  refine commutator_eq_bot_of_le_center ?_ ?_
  · exact Subgroup.isPerfect_iff.mp (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4
      (MonoidHom.ofInjective (longSL2_injective _ fin3_zero_ne_one true true)).symm)
  · rw [commutator_le]
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    apply ker_spinAction_le_center
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      spinAction_longSL2, spinAction_longSL2,
      show (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false = (frame01 K).swap from
        toFrame_not _ fin3_zero_ne_one true true, Frame.La_comm_La_swap]
    group

theorem commute_spinJ₂_spinJ₃ [Finite K] (h4 : 4 ≤ Nat.card K) {a b : spinGroup (quadOdd 3 K)}
    (ha : a ∈ spinJ₂ K) (hb : b ∈ spinJ₃ K) : a * b = b * a := by
  have h := commutator_eq_bot_iff_le_centralizer.mp (commutator_spinJ₂_spinJ₃ (K := K) h4) ha
  exact (mem_centralizer_iff.mp h b hb).symm

@[expose] noncomputable def spinMul₁₂ (K : Type) [Field K] :
    spinJ₁ K × spinJ₂ K →* spinGroup (quadOdd 3 K) :=
  MonoidHom.noncommCoprod (spinJ₁ K).subtype (spinJ₂ K).subtype fun a b =>
    commute_spinJ₁_spinJ₂ a.2 b.2

theorem commute_spinMul₁₂_spinJ₃ [Finite K] (h4 : 4 ≤ Nat.card K) (x : spinJ₁ K × spinJ₂ K)
    (c : spinJ₃ K) : Commute (spinMul₁₂ K x) ((spinJ₃ K).subtype c) := by
  change (x.1 : spinGroup (quadOdd 3 K)) * x.2 * c = c * (x.1 * x.2)
  rw [mul_assoc, commute_spinJ₂_spinJ₃ h4 x.2.2 c.2, ← mul_assoc,
    commute_spinJ₁_spinJ₃ x.1.2 c.2, mul_assoc]

@[expose] noncomputable def spinMul [Finite K] (h4 : 4 ≤ Nat.card K) :
    (spinJ₁ K × spinJ₂ K) × spinJ₃ K →* spinGroup (quadOdd 3 K) :=
  MonoidHom.noncommCoprod (spinMul₁₂ K) (spinJ₃ K).subtype (commute_spinMul₁₂_spinJ₃ h4)

theorem spinMul_apply [Finite K] (h4 : 4 ≤ Nat.card K) (x : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) :
    spinMul h4 x = (x.1.1 : spinGroup (quadOdd 3 K)) * x.1.2 * x.2 :=
  rfl

theorem range_spinMul [Finite K] (h4 : 4 ≤ Nat.card K) : (spinMul h4).range = spinE K := by
  refine le_antisymm ?_ (sup_le (sup_le ?_ ?_) ?_)
  · rintro _ ⟨x, rfl⟩
    rw [spinMul_apply]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left x.1.1.2))
      (mem_sup_left (mem_sup_right x.1.2.2))) (mem_sup_right x.2.2)
  · intro a ha
    exact ⟨((⟨a, ha⟩, 1), 1), by rw [spinMul_apply]; simp⟩
  · intro b hb
    exact ⟨((1, ⟨b, hb⟩), 1), by rw [spinMul_apply]; simp⟩
  · intro c hc
    exact ⟨((1, 1), ⟨c, hc⟩), by rw [spinMul_apply]; simp⟩

section Centres

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem mem_zpowers_of_commute_spinJ₁ {a : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (hc : ∀ a' ∈ spinJ₁ K, a * a' = a' * a) :
    a ∈ zpowers (spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero) := by
  have hsinj : Function.Injective (shortSeven K) :=
    LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true
  rw [← shortSeven_neg_one, ← map_center_range_sl2 hp hp2 hK h5 _ hsinj]
  refine ⟨⟨a, ha⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

theorem mem_zpowers_of_commute_spinJ₂ {b : spinGroup (quadOdd 3 K)} (hb : b ∈ spinJ₂ K)
    (hc : ∀ b' ∈ spinJ₂ K, b * b' = b' * b) : b ∈ zpowers (tSeven K) := by
  rw [← map_center_range_longSL2 _ fin3_zero_ne_one hp hp2 hK h5 true true]
  refine ⟨⟨b, hb⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

theorem mem_zpowers_of_commute_spinJ₃ {c : spinGroup (quadOdd 3 K)} (hc3 : c ∈ spinJ₃ K)
    (hc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c) :
    c ∈ zpowers ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (-1)) := by
  rw [← map_center_range_longSL2 _ fin3_zero_ne_one hp hp2 hK h5 true false]
  refine ⟨⟨c, hc3⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

end Centres

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem eq_of_mul_mul_eq_one {G : Type*} [Group G] {z t a b c : G} (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ g, z * g = g * z) (htt : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ z)
    (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = t) (hc : c = 1 ∨ c = z * t) (habc : a * b * c = 1) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = z ∧ b = t ∧ c = z * t) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha, hb, hc] at habc ⊢
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exfalso
    rw [one_mul, one_mul] at habc
    exact htz ((eq_inv_of_mul_eq_one_right habc).trans hzi)
  · exfalso
    rw [one_mul, mul_one] at habc
    exact ht1 habc
  · exfalso
    rw [one_mul, ← mul_assoc, ← hzc t, mul_assoc, htt, mul_one] at habc
    exact hz1 habc
  · exfalso
    rw [mul_one, mul_one] at habc
    exact hz1 habc
  · exfalso
    rw [mul_one, ← mul_assoc, hzz, one_mul] at habc
    exact ht1 habc
  · exfalso
    rw [mul_one] at habc
    exact htz ((eq_inv_of_mul_eq_one_right habc).trans hzi)
  · exact Or.inr ⟨rfl, rfl, rfl⟩

noncomputable abbrev spinZ (K : Type) [Field K] : spinGroup (quadOdd 3 K) :=
  spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

omit h5 in
theorem two_ne_zero_spin : (2 : K) ≠ 0 :=
  CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (hK ▸ (hp.odd_of_ne_two hp2).pow)

omit hp hp2 [Field K] [Finite K] in
theorem four_le_card_spin : 4 ≤ Nat.card K := by
  rw [hK]
  omega

omit h5 in
theorem spinZ_facts :
    spinZ K * spinZ K = 1 ∧ spinZ K ≠ 1 ∧ spinZ K ∈ center (spinGroup (quadOdd 3 K)) ∧
      tSeven K * tSeven K = 1 ∧ tSeven K ≠ 1 ∧ tSeven K ∉ center (spinGroup (quadOdd 3 K)) ∧
      spinZ K ∈ spinJ₁ K ∧ tSeven K ∈ spinJ₂ K ∧ spinZ K * tSeven K ∈ spinJ₃ K ∧
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (-1) =
        spinZ K * tSeven K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  have hZ := center_spinGroup_quadOdd h2 (le_refl 3)
  have ht2 : orderOf (tSeven K) = 2 :=
    orderOf_longSL2_neg_one _ fin3_zero_ne_one hodd true true
  have htZ : tSeven K ∉ center (spinGroup (quadOdd 3 K)) := by
    rw [center_spinGroup_quadOdd_eq_ker h2 (le_refl 3), MonoidHom.mem_ker]
    exact spinAction_longSL2_neg_one_ne_one _ fin3_zero_ne_one hodd true true
  refine ⟨spinGroup.negOne_mul_self _ hQ, spinGroup.negOne_ne_one _ hQ, hZ ▸ mem_zpowers _,
    by rw [← pow_two, ← ht2, pow_orderOf_eq_one], ?_, htZ, ⟨-1, shortSeven_neg_one hQ⟩,
    ⟨-1, rfl⟩, ⟨-1, longSL2_neg_one_not _ fin3_zero_ne_one hQ true true⟩,
    longSL2_neg_one_not _ fin3_zero_ne_one hQ true true⟩
  intro h1
  exact htZ (h1 ▸ one_mem _)

theorem mem_ker_spinMul_iff (h4 : 4 ≤ Nat.card K) (x : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) :
    x ∈ (spinMul h4).ker ↔ x = 1 ∨ x = ((⟨spinZ K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.1⟩,
      ⟨tSeven K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.2.1⟩),
      ⟨spinZ K * tSeven K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.2.2.1⟩) := by
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have htz : tSeven K ≠ spinZ K := fun h => htc (h ▸ hzc)
  rw [MonoidHom.mem_ker, spinMul_apply]
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩ := x
  constructor
  · intro habc
    change a * b * c = 1 at habc
    have hac : ∀ a' ∈ spinJ₁ K, a * a' = a' * a := by
      intro a' ha'
      have hbc : a = (b * c)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← mul_assoc, habc]
      rw [hbc, mul_inv_rev]
      calc c⁻¹ * b⁻¹ * a' = c⁻¹ * (b⁻¹ * a') := mul_assoc _ _ _
        _ = c⁻¹ * (a' * b⁻¹) := by
          rw [commute_spinJ₁_spinJ₂ ha' (inv_mem hb)]
        _ = a' * (c⁻¹ * b⁻¹) := by
          rw [← mul_assoc, ← commute_spinJ₁_spinJ₃ ha' (inv_mem hc), mul_assoc]
    have hbb : ∀ b' ∈ spinJ₂ K, b * b' = b' * b := by
      intro b' hb'
      have hbeq : b = a⁻¹ * c⁻¹ := by
        rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← mul_assoc]
        rw [show b * c * a = a⁻¹ * (a * b * c) * a by group, habc]
        group
      rw [hbeq]
      calc a⁻¹ * c⁻¹ * b' = a⁻¹ * (c⁻¹ * b') := mul_assoc _ _ _
        _ = a⁻¹ * (b' * c⁻¹) := by
          rw [← commute_spinJ₂_spinJ₃ h4 hb' (inv_mem hc)]
        _ = b' * (a⁻¹ * c⁻¹) := by
          rw [← mul_assoc, commute_spinJ₁_spinJ₂ (inv_mem ha) hb', mul_assoc]
    have hcc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c := by
      intro c' hc'
      have hceq : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
      rw [hceq, mul_inv_rev]
      calc b⁻¹ * a⁻¹ * c' = b⁻¹ * (a⁻¹ * c') := mul_assoc _ _ _
        _ = b⁻¹ * (c' * a⁻¹) := by
          rw [commute_spinJ₁_spinJ₃ (inv_mem ha) hc']
        _ = c' * (b⁻¹ * a⁻¹) := by
          rw [← mul_assoc, commute_spinJ₂_spinJ₃ h4 (inv_mem hb) hc', mul_assoc]
    have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
      rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
    have h1 := eq_one_or_eq_of_mem_zpowers_of_mul_self hzz
      (mem_zpowers_of_commute_spinJ₁ hp hp2 hK h5 ha hac)
    have h2 := eq_one_or_eq_of_mem_zpowers_of_mul_self htt
      (mem_zpowers_of_commute_spinJ₂ hp hp2 hK h5 hb hbb)
    have h3 := eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt
      (h3eq ▸ mem_zpowers_of_commute_spinJ₃ hp hp2 hK h5 hc hcc)
    rcases eq_of_mul_mul_eq_one hzz hz1 hzcomm htt ht1 htz h1 h2 h3 habc with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; rfl
    · right; rfl
  · rintro (h | h)
    · rw [h]
      simp
    · rw [h]
      change spinZ K * tSeven K * (spinZ K * tSeven K) = 1
      rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]

end Card

end CFSG.ComponentClassification.HarrisLit.T1
