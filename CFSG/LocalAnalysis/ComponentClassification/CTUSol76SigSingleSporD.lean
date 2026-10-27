module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporTools
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.Quasithin.Vol2.KGFact3312J1
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ3

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem not_card_dvd_prime_pow_mul_prime_pow {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {q r a b : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (h : Nat.card K ∣ q ^ a * r ^ b) : False := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 hd₂
  have := Fintype.ofFinite K
  exact sig_not_isSolvable_of_isQuasisimple hK
    (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hq hr hqr
      (by rw [← Nat.card_eq_fintype_card, ← hd]))

theorem dvd_card_quot_center_of_card_dvd {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {q r p a b : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hp : p.Prime) (h : Nat.card K ∣ q ^ a * r ^ b * p) : p ∣ Nat.card (K ⧸ center K) := by
  by_contra hnp
  obtain ⟨-, hsimp, x, y, hxy⟩ := hK
  have h1 : Nat.card (K ⧸ center K) ∣ q ^ a * r ^ b :=
    Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hnp).symm
      ((Subgroup.card_quotient_dvd_card _).trans h)
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.mp h1
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 hd₂
  have := Fintype.ofFinite (K ⧸ center K)
  have hsol := CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (G := K ⧸ center K) hq hr hqr (by rw [← Nat.card_eq_fintype_card, ← hd])
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 hsol x y)

theorem exists_mem_shape_card_centralizerIn {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {shape : List (ℕ × ℕ)} (h : OddStandard.MathieuInnerStatement G shape)
    {u : Equiv.Perm (Fin n)} (hu : u ∈ G) (hu2 : orderOf u = 2) :
    ∃ s, (s, Nat.card (Sporadic.Schreier.centralizerIn G u)) ∈ shape := by
  obtain ⟨⟨recs, hshape, hrecs, -, hcover⟩, -⟩ := h
  obtain ⟨r, hr, hur⟩ := hcover u hu hu2
  refine ⟨r.classSize, ?_⟩
  rw [GH74.GLS.IVK.GHInv.card_centralizerIn_eq_of_mem_conjClass G hur, (hrecs r hr).2.2.2.1,
    ← hshape]
  exact List.mem_map_of_mem hr

theorem exists_card_dvd_of_mathieuInnerStatement {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {shape : List (ℕ × ℕ)} (h : OddStandard.MathieuInnerStatement G shape) {T : Type} [Group T]
    (e : T ≃* ↥G) {y : T} (hy2 : orderOf y = 2) {K : Subgroup T}
    (hK : K ≤ centralizer ({y} : Set T)) : ∃ s c, (s, c) ∈ shape ∧ Nat.card K ∣ c := by
  have hu : orderOf ((e y : ↥G) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy2]
  obtain ⟨s, hs⟩ := exists_mem_shape_card_centralizerIn h (e y).2 hu
  refine ⟨s, _, hs, ?_⟩
  rw [← GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn G e y]
  exact Subgroup.card_dvd_of_le hK

theorem singleComponentCleanAt_M11 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M11) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  obtain ⟨e⟩ := hP
  obtain ⟨s, c, hsc, hKc⟩ := exists_card_dvd_of_mathieuInnerStatement
    OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.1 e hy2 hK.1
  simp only [List.mem_singleton, Prod.mk.injEq] at hsc
  obtain ⟨-, rfl⟩ := hsc
  exact not_card_dvd_prime_pow_mul_prime_pow (a := 4) (b := 1) hq Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num; exact hKc)

theorem singleComponentCleanAt_M12 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M12) := by
  refine singleComponentCleanAt_of_primePow 5 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    obtain ⟨s, c, hsc, hKc⟩ := exists_card_dvd_of_mathieuInnerStatement
      OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.1 e hy2 hK.1
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hsc
    rw [pow_one]
    rcases hsc with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (not_card_dvd_prime_pow_mul_prime_pow (a := 6) (b := 1) hq Nat.prime_two
        Nat.prime_three (by norm_num) (by norm_num; exact hKc)).elim
    · exact dvd_card_quot_center_of_card_dvd (a := 4) (b := 1) hq Nat.prime_two Nat.prime_three
        (by norm_num) Nat.prime_five (by norm_num; exact hKc)
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 5 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.M12
    rw [Sporadic.Schreier.m12_card]
    norm_num

theorem singleComponentCleanAt_M22 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M22) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  obtain ⟨e⟩ := hP
  obtain ⟨s, c, hsc, hKc⟩ := exists_card_dvd_of_mathieuInnerStatement
    OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.2.1 e hy2 hK.1
  simp only [List.mem_singleton, Prod.mk.injEq] at hsc
  obtain ⟨-, rfl⟩ := hsc
  exact not_card_dvd_prime_pow_mul_prime_pow (a := 7) (b := 1) hq Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num; exact hKc)

theorem singleComponentCleanAt_M23 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M23) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    obtain ⟨s, c, hsc, hKc⟩ := exists_card_dvd_of_mathieuInnerStatement
      OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.2.2.1 e hy2 hK.1
    simp only [List.mem_singleton, Prod.mk.injEq] at hsc
    obtain ⟨-, rfl⟩ := hsc
    rw [pow_one]
    exact dvd_card_quot_center_of_card_dvd (a := 7) (b := 1) hq Nat.prime_two Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num; exact hKc)
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.M23
    rw [Sporadic.Schreier.m23_card]
    norm_num

theorem singleComponentCleanAt_M24 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .M24) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  obtain ⟨e⟩ := hP
  have e' : T ≃* ↥Blueprint.NativeSporadic.M24 := e
  have h3 : Nat.Coprime (Nat.card K) 3 := by
    have h : ¬ 3 ∣ Nat.card ↥(K.subgroupOf (centralizer ({y} : Set T))) :=
      RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m24_centralizerIn_comps
        e' y hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
    rw [Nat.card_congr (subgroupOfEquivOfLe hK.1).toEquiv] at h
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
  obtain ⟨s, c, hsc, hKc⟩ := exists_card_dvd_of_mathieuInnerStatement
    OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.2.2.2 e' hy2 hK.1
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hsc
  rcases hsc with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact not_card_dvd_prime_pow_mul_prime_pow (r := 7) (a := 10) (b := 1) hq Nat.prime_two
      (by norm_num) (by norm_num) (h3.dvd_of_dvd_mul_left (by norm_num; exact hKc))
  · exact not_card_dvd_prime_pow_mul_prime_pow (a := 9) (b := 1) hq Nat.prime_two Nat.prime_five
      (by norm_num) (h3.dvd_of_dvd_mul_left (by norm_num; exact hKc))

theorem singleComponentCleanAt_J1 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .J1) := by
  refine singleComponentCleanAt_of_primePow 5 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    have e' : T ≃* Blueprint.NativeSporadic.J1 := e
    have hC : Nat.card ↥(centralizer ({y} : Set T)) = 120 := by
      rw [GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv e' y]
      exact Quasithin.H13.KG3312.j1_card_centralizer (e' y) (by rw [MulEquiv.orderOf_eq, hy2])
    have hKc : Nat.card K ∣ 120 := hC ▸ Subgroup.card_dvd_of_le hK.1
    rw [pow_one]
    exact dvd_card_quot_center_of_card_dvd (a := 3) (b := 1) hq Nat.prime_two Nat.prime_three
      (by norm_num) Nat.prime_five (by norm_num; exact hKc)
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 5 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.J1
    rw [Sporadic.J1.card_J1]
    norm_num

theorem singleComponentCleanAt_J3 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .J3) := by
  refine singleComponentCleanAt_of_primePow 5 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · have hKc : Nat.card K ∣ 1920 :=
      (KG.centralizer_perfect_card_of_J3 hP y hy2).2 ▸ Subgroup.card_dvd_of_le hK.1
    rw [pow_one]
    exact dvd_card_quot_center_of_card_dvd (a := 7) (b := 1) hq Nat.prime_two Nat.prime_three
      (by norm_num) Nat.prime_five (by norm_num; exact hKc)
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 5 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.J3
    rw [Sporadic.J3.card_J3]
    norm_num

end CFSG.ComponentClassification.Sol76.Sig
