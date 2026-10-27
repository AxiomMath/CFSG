module

public import CFSG.GH74.Generic.BProg.B3.S3T4H175
public import CFSG.GH74.Generic.BProg.B3.S3T4L4G
public import CFSG.GH74.Generic.BProg.B2.PuL4InnerSD

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace S3T4

theorem exists_pow_four_of_pow_eq_one {Γ : Type*} [Monoid Γ] {x : Γ} {k : ℕ} (hk : Odd k)
    (hx : x ^ k = 1) : ∃ j : ℕ, (x ^ j) ^ 4 = x := by
  obtain ⟨a, rfl⟩ := hk
  refine ⟨(a + 1) ^ 2, ?_⟩
  rw [← pow_mul]
  have h : (a + 1) ^ 2 * 4 = (2 * a + 1) * (2 * a + 3) + 1 := by ring
  rw [h, pow_succ, pow_mul, hx, one_pow, one_mul]

theorem mul_eq_one_of_sq_eq_one {K : Type*} [Field K] {a b : Kˣ} (ha : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 2 = 1) (hb1 : b ≠ 1) : a * b = 1 := by
  have key : ∀ c : Kˣ, c ^ 2 = 1 → c ≠ 1 → c = -1 := by
    intro c hc hc1
    have h1 : (c : K) * c = 1 := by rw [← Units.val_mul, ← pow_two, hc, Units.val_one]
    rcases mul_self_eq_one_iff.1 h1 with h2 | h2
    · exact absurd (Units.ext h2) hc1
    · exact Units.ext (by rw [h2, Units.val_neg, Units.val_one])
  rw [key a ha ha1, key b hb hb1, neg_one_mul, neg_neg]

theorem mem_of_congr_eq_conj {N : Type} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type} [Group P] (e : ↥H ≃* P)
    {t : N} {x : P} (ht : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = MulAut.conj x) :
    t ∈ H := by
  apply B2.T4.T4OutCore.mem_of_conjNormal_mem_inner hfaith
  refine ⟨e.symm x, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]

theorem conjAut_mem_inner_of_pow {F : Type} [Field F] {A : GL (Fin 4) F} {k : ℕ} (hk : Odd k)
    (hA : GeneralLinearGroup.det A ^ k = 1) :
    LinearFlag.conjAut 4 F A ∈ (MulAut.conj : LinearFlag.projectiveSL 4 F →*
      MulAut (LinearFlag.projectiveSL 4 F)).range := by
  obtain ⟨j, hj⟩ := exists_pow_four_of_pow_eq_one hk hA
  exact B2.T4.T4OutCore.conjAut_mem_inner_of_det (y := GeneralLinearGroup.det A ^ j) hj.symm

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem primeFormConjHom_mem_inner_of_pow {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) {k : ℕ}
    (hk : Odd k) (hkc : p ^ f + 1 = 2 * k)
    (hA : GeneralLinearGroup.det (A : GL (Fin 4) K) ^ k = 1) :
    primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  obtain ⟨j, hj⟩ := exists_pow_four_of_pow_eq_one hk hA
  have hv : h.norm ((GeneralLinearGroup.det (A : GL (Fin 4) K) ^ j : Kˣ) : K) = 1 := by
    have hjk : j * (2 * k) = k * (2 * j) := by ring
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, hkc, hjk, pow_mul,
      hA, one_pow, Units.val_one]
  exact B2.T4.T4OutCore.primeFormConjHom_mem_inner_of_det h A hv hj.symm

end Unitary

end S3T4

open S3T4

section CertifiedLeaf


open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag in
theorem leaf514Fam_l4m : Leaf514Fam (fun X _ => B2.TA7.PuL4m X) := by
  intro N _ _ H L v w h4 hP hS3 _ _ hsv hsw hsvw
  have hnorm : H.Normal := hsv.normal
  have hSD : B2.T4.PuL4SD ↥H := hP
  have hnot : ∀ t : N, B2.ShapeInCent H t L → t ∉ H := fun t hs ht =>
    B2.PuL4InnerSD.false_of_inner_shape3_SD hs hSD ht hS3
  have hsq : ∀ t : N, B2.ShapeInCent H t L → t ^ 2 = 1 := fun t hs => by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  obtain ⟨p, f, hp, hp2, hf, hq3, ⟨hq4, hL⟩ | ⟨hq4, hU⟩⟩ := hP
  ·
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := B2.T4.T4OutCore.linear_model hL
    have hF4 : Nat.card F % 4 = 3 := by rw [hF]; exact hq4
    have h5 : 5 ≤ Nat.card F := by rw [hF]; omega
    obtain ⟨k, hk, hkc⟩ : ∃ k : ℕ, Odd k ∧ Nat.card Fˣ = 2 * k := by
      refine ⟨(Nat.card F - 1) / 2, ?_, ?_⟩
      · rw [Nat.odd_iff]; omega
      · rw [Nat.card_units]; omega
    have hdiag : ∀ t : N, B2.ShapeInCent H t L → ∃ A : GL (Fin 4) F,
        MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = LinearFlag.conjAut 4 F A ∧
          (GeneralLinearGroup.det A ^ k) ^ 2 = 1 ∧ GeneralLinearGroup.det A ^ k ≠ 1 := by
      intro t hs
      by_cases hd : ∃ A : GL (Fin 4) F,
          MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = LinearFlag.conjAut 4 F A
      · obtain ⟨A, hA⟩ := hd
        refine ⟨A, hA, ?_, fun h1 => hnot t hs ?_⟩
        · rw [← pow_mul, mul_comm, ← hkc]
          exact pow_card_eq_one'
        · obtain ⟨x, hx⟩ := conjAut_mem_inner_of_pow hk h1
          exact mem_of_congr_eq_conj hs.faithful e (hA.trans hx.symm)
      · push Not at hd
        exact (outGraph_lin4 H hs hF4 h5 e hd h4).elim
    obtain ⟨Av, hv, hv2, hv1⟩ := hdiag v hsv
    obtain ⟨Aw, hw, hw2, hw1⟩ := hdiag w hsw
    apply hnot (v * w) hsvw
    have hdet : GeneralLinearGroup.det (Av * Aw) ^ k = 1 := by
      rw [map_mul, mul_pow]
      exact mul_eq_one_of_sq_eq_one hv2 hv1 hw2 hw1
    obtain ⟨x, hx⟩ := conjAut_mem_inner_of_pow hk hdet
    refine mem_of_congr_eq_conj hsvw.faithful e (x := x) ?_
    rw [map_mul, map_mul, hv, hw, ← map_mul, hx]
  ·
    obtain ⟨K, _, h, ⟨e⟩⟩ := B2.T4.T4OutCore.primeForm_model (n := 4) (by norm_num)
      (fun hh => absurd hh.1 (by norm_num)) hU
    obtain ⟨k, hk, hkc⟩ : ∃ k : ℕ, Odd k ∧ p ^ f + 1 = 2 * k := by
      refine ⟨(p ^ f + 1) / 2, ?_, ?_⟩
      · rw [Nat.odd_iff]; omega
      · omega
    have hdiag : ∀ t : N, B2.ShapeInCent H t L →
        ∃ A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
          MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
            primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ∧
          (GeneralLinearGroup.det (A : GL (Fin 4) K) ^ k) ^ 2 = 1 ∧
            GeneralLinearGroup.det (A : GL (Fin 4) K) ^ k ≠ 1 := by
      intro t hs
      by_cases hd : ∃ A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
          MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
            primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A
      · obtain ⟨A, hA⟩ := hd
        refine ⟨A, hA, ?_, fun h1 => hnot t hs ?_⟩
        · have hN := norm_det_eq_one h (1 : GL (Fin 4) K) A.2
          rw [← pow_mul, mul_comm, ← hkc]
          refine Units.ext ?_
          rw [Units.val_pow_eq_pow_val, ← UnitaryFieldData.norm_eq_pow h,
            GeneralLinearGroup.val_det_apply]
          exact hN
        · obtain ⟨x, hx⟩ := primeFormConjHom_mem_inner_of_pow h A hk hkc h1
          exact mem_of_congr_eq_conj hs.faithful e (hA.trans hx.symm)
      · push Not at hd
        exact (false_of_uni_not_diag H h hs hq3 hp2 e hd h4).elim
    obtain ⟨Av, hv, hv2, hv1⟩ := hdiag v hsv
    obtain ⟨Aw, hw, hw2, hw1⟩ := hdiag w hsw
    apply hnot (v * w) hsvw
    have hdet : GeneralLinearGroup.det ((Av * Aw : primeFormUnitary h
        ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : GL (Fin 4) K) ^ k = 1 := by
      rw [Subgroup.coe_mul, map_mul, mul_pow]
      exact mul_eq_one_of_sq_eq_one hv2 hv1 hw2 hw1
    obtain ⟨x, hx⟩ := primeFormConjHom_mem_inner_of_pow h (Av * Aw) hk hkc hdet
    refine mem_of_congr_eq_conj hsvw.faithful e (x := x) ?_
    rw [map_mul, map_mul, hv, hw, ← map_mul, hx]

end CertifiedLeaf

end CFSG.GH74.Generic.BProg.B3
