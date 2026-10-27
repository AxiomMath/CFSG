module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Lin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74FDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {K : Type} [Field K]

theorem spinZ_commute (g : spinGroup (quadOdd 3 K)) : spinZ K * g = g * spinZ K :=
  Subtype.ext (by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul, mul_neg_one])

theorem orderOf_spinZ (h2 : (2 : K) ≠ 0) : orderOf (spinZ K) = 2 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, spinGroup.negOne_mul_self])
    (spinGroup.negOne_ne_one _ _)

theorem eq_one_or_eq_spinZ (h2 : (2 : K) ≠ 0) {x : spinGroup (quadOdd 3 K)}
    (hx : spinAction (quadOdd 3 K) x = 1) : x = 1 ∨ x = spinZ K := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  exact (mem_ker_spinAction_iff (quadOdd 3 K) (nondegenerate_quadOdd 3 K) x).mp
    (MonoidHom.mem_ker.mpr hx)

theorem orderOf_spinZ_mul (h2 : (2 : K) ≠ 0) {x : spinGroup (quadOdd 3 K)}
    (hx : Odd (orderOf x)) : orderOf (spinZ K * x) = 2 * orderOf x := by
  rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime (spinZ_commute x) _), orderOf_spinZ h2]
  rw [orderOf_spinZ h2]
  exact Nat.coprime_two_left.mpr hx

theorem eq_of_spinAction_eq_of_odd (h2 : (2 : K) ≠ 0) {x y : spinGroup (quadOdd 3 K)}
    (hx : Odd (orderOf x)) (hy : Odd (orderOf y))
    (h : spinAction (quadOdd 3 K) x = spinAction (quadOdd 3 K) y) : x = y := by
  have h1 : spinAction (quadOdd 3 K) (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rcases eq_one_or_eq_spinZ h2 h1 with h3 | h3
  · exact mul_inv_eq_one.mp h3
  · exfalso
    have h4 : x = spinZ K * y := by rw [← h3, inv_mul_cancel_right]
    have h5 := orderOf_spinZ_mul h2 hy
    rw [← h4] at h5
    rw [h5] at hx
    exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hx

theorem mul_comm_of_spinAction (h2 : (2 : K) ≠ 0) {x g : spinGroup (quadOdd 3 K)}
    (hx : Odd (orderOf x))
    (hc : spinAction (quadOdd 3 K) g * spinAction (quadOdd 3 K) x =
      spinAction (quadOdd 3 K) x * spinAction (quadOdd 3 K) g) : g * x = x * g := by
  have hconj : orderOf (g * x * g⁻¹) = orderOf x := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h1 : g * x * g⁻¹ = x := eq_of_spinAction_eq_of_odd h2 (hconj ▸ hx) hx (by
    rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right])
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

noncomputable abbrev rootThreeHom (K : Type) [Field K] :
    Fin 5 → (Multiplicative K →* spinGroup (quadOdd 3 K)) :=
  ![(oddFrame 3 K).toHypFrame.longRoot fin3_zero_ne_two true true,
    (oddFrame 3 K).toHypFrame.longRoot fin3_zero_ne_two false true,
    (oddFrame 3 K).toHypFrame.longRoot fin3_one_ne_two true true,
    (oddFrame 3 K).toHypFrame.longRoot fin3_one_ne_two false true,
    (oddFrame 3 K).shortRoot 2 true]

abbrev vecFive (K : Type) [Field K] : Fin 5 → Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  ![oddVec 3 K 0 true, oddVec 3 K 0 false, oddVec 3 K 1 true, oddVec 3 K 1 false, oddZ 3 K]

theorem spinAction_rootThree (i : Fin 5) (c : K) :
    spinAction (quadOdd 3 K) (rootThreeHom K i (.ofAdd c)) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (c • vecFive K i) := by
  fin_cases i
  · exact HypFrame.spinAction_longRoot_eq_eichler _ fin3_zero_ne_two true true c
  · exact HypFrame.spinAction_longRoot_eq_eichler _ fin3_zero_ne_two false true c
  · exact HypFrame.spinAction_longRoot_eq_eichler _ fin3_one_ne_two true true c
  · exact HypFrame.spinAction_longRoot_eq_eichler _ fin3_one_ne_two false true c
  · exact OddFrame.spinAction_shortRoot_eq_eichler _ 2 true c

theorem polar_eTwo_vecFive (i : Fin 5) :
    polar (quadOdd 3 K) (oddVec 3 K 2 true) (vecFive K i) = 0 := by
  fin_cases i <;> simp [oddZ, polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl,
    polar_quadOdd_single_inr_inr]

theorem polar_fTwo_vecFive (i : Fin 5) :
    polar (quadOdd 3 K) (oddVec 3 K 2 false) (vecFive K i) = 0 := by
  fin_cases i <;> simp [oddZ, polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl,
    polar_quadOdd_single_inr_inr]

theorem qThree_eq : qThree K = rootThreeHom K 4 (.ofAdd 1) :=
  OddFrame.shortSL2_upperSL2 _ 2 true 1

theorem spinAction_qThree : spinAction (quadOdd 3 K) (qThree K) =
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) := by
  rw [qThree_eq, spinAction_rootThree, one_smul]
  rfl

theorem rootThree_pow_char [Finite K] (i : Fin 5) (c : K) :
    rootThreeHom K i (.ofAdd c) ^ ringChar K = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero, map_one]

theorem odd_ringChar [Finite K] (hodd : Odd (Nat.card K)) : Odd (ringChar K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn] at hodd
  exact (Nat.odd_pow_iff n.ne_zero).mp hodd

noncomputable abbrev radThree (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) :=
  closure (Set.range fun p : Fin 5 × K => rootThreeHom K p.1 (.ofAdd p.2))

theorem rootThree_mem_radThree (i : Fin 5) (c : K) :
    rootThreeHom K i (.ofAdd c) ∈ radThree K :=
  subset_closure ⟨(i, c), rfl⟩

theorem spinAction_radThree_le :
    (radThree K).map (spinAction (quadOdd 3 K)) ≤ rootGroup (quadOdd 3 K) (oddVec 3 K 2 true) := by
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨⟨i, c⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, spinAction_rootThree]
  exact eichler_mem_rootGroup (by rw [polar_smul_right, polar_eTwo_vecFive, smul_zero])

theorem spinAction_mem_rootGroup {x : spinGroup (quadOdd 3 K)} (hx : x ∈ radThree K) :
    spinAction (quadOdd 3 K) x ∈ rootGroup (quadOdd 3 K) (oddVec 3 K 2 true) :=
  spinAction_radThree_le ⟨x, hx, rfl⟩

noncomputable abbrev prodThree (c : Fin 5 → K) : spinGroup (quadOdd 3 K) :=
  rootThreeHom K 0 (.ofAdd (c 0)) * rootThreeHom K 1 (.ofAdd (c 1)) *
    rootThreeHom K 2 (.ofAdd (c 2)) * rootThreeHom K 3 (.ofAdd (c 3)) *
    rootThreeHom K 4 (.ofAdd (c 4))

theorem prodThree_mem (c : Fin 5 → K) : prodThree c ∈ radThree K :=
  mul_mem (mul_mem (mul_mem (mul_mem (rootThree_mem_radThree 0 _) (rootThree_mem_radThree 1 _))
    (rootThree_mem_radThree 2 _)) (rootThree_mem_radThree 3 _)) (rootThree_mem_radThree 4 _)

abbrev yFive (c : Fin 5 → K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  c 0 • vecFive K 0 + c 1 • vecFive K 1 + c 2 • vecFive K 2 + c 3 • vecFive K 3 +
    c 4 • vecFive K 4

theorem spinAction_prodThree (c : Fin 5 → K) :
    spinAction (quadOdd 3 K) (prodThree c) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yFive c) := by
  have hp : ∀ i (a : K), polar (quadOdd 3 K) (oddVec 3 K 2 true) (a • vecFive K i) = 0 :=
    fun i a => by rw [polar_smul_right, polar_eTwo_vecFive, smul_zero]
  simp only [prodThree, map_mul, spinAction_rootThree]
  rw [eichler_mul (hp 0 _) (hp 1 _), eichler_mul (by rw [polar_add_right, hp, hp, add_zero])
    (hp 2 _), eichler_mul (by rw [polar_add_right, polar_add_right, hp, hp, hp, add_zero,
    add_zero]) (hp 3 _), eichler_mul (by rw [polar_add_right, polar_add_right, polar_add_right,
    hp, hp, hp, hp, add_zero, add_zero, add_zero]) (hp 4 _)]

theorem yFive_injective {c d : Fin 5 → K}
    (h : eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yFive c) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yFive d)) : c = d := by
  have hpe : ∀ c : Fin 5 → K, polar (quadOdd 3 K) (oddVec 3 K 2 true) (yFive c) = 0 := fun c => by
    simp only [yFive, polar_add_right, polar_smul_right, polar_eTwo_vecFive, smul_zero, add_zero]
  have hpf : ∀ c : Fin 5 → K, polar (quadOdd 3 K) (oddVec 3 K 2 false) (yFive c) = 0 := fun c => by
    simp only [yFive, polar_add_right, polar_smul_right, polar_fTwo_vecFive, smul_zero, add_zero]
  have h1 := LinearEquiv.congr_fun h (oddVec 3 K 2 false)
  rw [eichler_apply quadOdd_eTwo (hpe c), eichler_apply quadOdd_eTwo (hpe d), polar_fTwo_eTwo,
    hpf, hpf] at h1
  funext i
  fin_cases i
  · have := congrFun h1 (.inl 0)
    simpa [yFive, vecFive, oddZ, Pi.single_apply] using this
  · have := congrFun h1 (.inr (.inl 0))
    simpa [yFive, vecFive, oddZ, Pi.single_apply] using this
  · have := congrFun h1 (.inl 1)
    simpa [yFive, vecFive, oddZ, Pi.single_apply] using this
  · have := congrFun h1 (.inr (.inl 1))
    simpa [yFive, vecFive, oddZ, Pi.single_apply] using this
  · have := congrFun h1 (.inr (.inr ()))
    simpa [yFive, vecFive, oddZ, Pi.single_apply] using this

theorem exists_prodThree {g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hg : g ∈ rootGroup (quadOdd 3 K) (oddVec 3 K 2 true)) :
    ∃ c : Fin 5 → K, spinAction (quadOdd 3 K) (prodThree c) = g := by
  obtain ⟨y, hy, rfl⟩ := mem_rootGroup.mp hg
  refine ⟨![y (.inl 0), y (.inr (.inl 0)), y (.inl 1), y (.inr (.inl 1)), y (.inr (.inr ()))],
    ?_⟩
  have hyf : y (.inr (.inl 2)) = 0 := by
    have := hy
    rwa [polar_comm, oddVec_true, polar_quadOdd_single_inl] at this
  have hdec : y = yFive ![y (.inl 0), y (.inr (.inl 0)), y (.inl 1), y (.inr (.inl 1)),
      y (.inr (.inr ()))] + y (.inl 2) • oddVec 3 K 2 true := by
    funext σ
    rcases σ with m | m | ⟨⟩
    · fin_cases m <;> simp [yFive, vecFive, oddZ]
    · fin_cases m <;> simp [yFive, vecFive, oddZ, hyf]
    · simp [yFive, vecFive, oddZ]
  rw [spinAction_prodThree]
  conv_rhs => rw [hdec]
  rw [eichler_add_smul_self quadOdd_eTwo]

variable [Finite K]

theorem rootThree_commute (hodd : Odd (Nat.card K)) (i j : Fin 5) (a b : K) :
    rootThreeHom K i (.ofAdd a) * rootThreeHom K j (.ofAdd b) =
      rootThreeHom K j (.ofAdd b) * rootThreeHom K i (.ofAdd a) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  refine mul_comm_of_spinAction h2 ?_ (rootGroup_commute (spinAction_mem_rootGroup
    (rootThree_mem_radThree i a)) (spinAction_mem_rootGroup (rootThree_mem_radThree j b)))
  exact (odd_ringChar hodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one (rootThree_pow_char j b))

theorem radThree_comm (hodd : Odd (Nat.card K)) {x y : spinGroup (quadOdd 3 K)}
    (hx : x ∈ radThree K) (hy : y ∈ radThree K) : x * y = y * x := by
  have hs : Set.range (fun p : Fin 5 × K => rootThreeHom K p.1 (.ofAdd p.2)) ⊆
      centralizer (Set.range fun p : Fin 5 × K => rootThreeHom K p.1 (.ofAdd p.2)) := by
    rintro _ ⟨⟨i, a⟩, rfl⟩ _ ⟨⟨j, b⟩, rfl⟩
    exact rootThree_commute hodd j i b a
  have h1 : radThree K ≤ centralizer
      (Set.range fun p : Fin 5 × K => rootThreeHom K p.1 (.ofAdd p.2)) :=
    (closure_le _).mpr hs
  have h2 : radThree K ≤ centralizer (radThree K : Set (spinGroup (quadOdd 3 K))) := by
    rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (h1 hz) g hg).symm
  exact mem_centralizer_iff.mp (h2 hy) x hx

theorem pow_char_of_mem_radThree (hodd : Odd (Nat.card K)) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ radThree K) : x ^ ringChar K = 1 := by
  induction hx using closure_induction with
  | mem _ h =>
    obtain ⟨⟨i, c⟩, rfl⟩ := h
    exact rootThree_pow_char i c
  | one => exact one_pow _
  | mul a b ha hb iha ihb => rw [(Commute.mul_pow (radThree_comm hodd ha hb)), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem odd_orderOf_of_mem_radThree (hodd : Odd (Nat.card K)) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ radThree K) : Odd (orderOf x) :=
  (odd_ringChar hodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one (pow_char_of_mem_radThree hodd hx))

theorem eq_of_mem_radThree (hodd : Odd (Nat.card K)) {x y : spinGroup (quadOdd 3 K)}
    (hx : x ∈ radThree K) (hy : y ∈ radThree K)
    (h : spinAction (quadOdd 3 K) x = spinAction (quadOdd 3 K) y) : x = y :=
  eq_of_spinAction_eq_of_odd (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd)
    (odd_orderOf_of_mem_radThree hodd hx) (odd_orderOf_of_mem_radThree hodd hy) h

theorem card_radThree (hodd : Odd (Nat.card K)) : Nat.card (radThree K) = Nat.card K ^ 5 := by
  let φ : (Fin 5 → K) → radThree K := fun c => ⟨prodThree c, prodThree_mem c⟩
  have hinj : Function.Injective φ := by
    intro c d h
    have h' : prodThree c = prodThree d := congrArg Subtype.val h
    apply yFive_injective
    rw [← spinAction_prodThree, ← spinAction_prodThree, h']
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := exists_prodThree (spinAction_mem_rootGroup hx)
    exact ⟨c, Subtype.ext (eq_of_mem_radThree hodd (prodThree_mem c) hx hc)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_fun, Nat.card_fin]

theorem radThree_le_centralizer (hodd : Odd (Nat.card K)) :
    radThree K ≤ centralizer {qThree K} := fun x hx =>
  mem_centralizer_singleton_iff.mpr (radThree_comm hodd hx (by
    rw [qThree_eq]
    exact rootThree_mem_radThree 4 1))

theorem spinAction_commThree (hodd : Odd (Nat.card K)) {g : spinGroup (quadOdd 3 K)}
    (hg : g ∈ centralizer {qThree K}) : CommThree (spinAction (quadOdd 3 K) g) where
  two := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  map := map_spinAction _ g
  comm := by
    rw [← spinAction_qThree, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hg]

theorem conj_mem_radThree (hodd : Odd (Nat.card K)) {g x : spinGroup (quadOdd 3 K)}
    (hg : g ∈ centralizer {qThree K}) (hx : x ∈ radThree K) : g * x * g⁻¹ ∈ radThree K := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hc := spinAction_commThree hodd hg
  have hU : spinAction (quadOdd 3 K) (g * x * g⁻¹) ∈
      rootGroup (quadOdd 3 K) (oddVec 3 K 2 true) := by
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_rootGroup_of_apply_eq_smul hc.mem_orthogonalGroup
      (apply_eTwo_eq_smul h2 hc.comm) (spinAction_mem_rootGroup hx)
  obtain ⟨c, hcx⟩ := exists_prodThree hU
  have hodd' : Odd (orderOf (g * x * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem_radThree hodd hx
  rw [← eq_of_spinAction_eq_of_odd h2 (odd_orderOf_of_mem_radThree hodd (prodThree_mem c)) hodd'
    hcx]
  exact prodThree_mem c

end CFSG.ComponentClassification.HarrisLit.T1.S74
