module

public import CFSG.GH74.GLS.Stage2.Final.ModelType
public import CFSG.GH74.GLS.Stage2.Final.ModelH2Facts
public import CFSG.GH74.GLS.Stage2.Final.ModelCenter

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

structure GoodModel {F : Type} [Field F] [Finite F] (M : ModelData F) : Prop where
  two_ne_zero : (2 : F) ≠ 0
  odd_index : Odd (Nsub M).index
  quat : ∃ (a b : F) (h : a ^ 2 + b ^ 2 = -1), ∀ g, rhoQ h g ∈ M.H2
  qs : CFSG.IsQuasisimple ↥M.H2
  center2 : IsPGroup 2 ↥(Subgroup.center ↥M.H2)
  even : 2 ∣ Nat.card ↥M.H2

theorem goodModel_sp {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    GoodModel (ModelData.sp F) where
  two_ne_zero := h2
  odd_index := odd_index_Nsub _ h2 (ModelSp.odd_index_sp h2)
  quat := ModelSp.exists_rho_sp h2
  qs := ModelH2.h2_quasisimple_sp F h5
  center2 := ModelH2.h2_center_two_sp F
  even := ModelH2.h2_even_sp F h2

theorem goodModel_lin {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    GoodModel (ModelData.lin F) where
  two_ne_zero := h2
  odd_index := odd_index_Nsub _ h2 (ModelOrd.odd_index_lin F h2)
  quat := by
    obtain ⟨a, b, hab⟩ :=
      (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
        (ringChar_ne_two_of_two_ne_zero h2)).1
    exact ⟨a, b, hab, rhoQ_mem_H2_lin hab⟩
  qs := ModelH2.h2_quasisimple_lin F h5
  center2 := ModelH2.h2_center_two_lin F
  even := ModelH2.h2_even_lin F h2

theorem goodModel_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    GoodModel (ModelData.uni hF) where
  two_ne_zero := by
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    exact CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow (Fact.out : p.Prime) hp2 hF'
  odd_index := by
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have h2 : (2 : F) ≠ 0 :=
      CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow (Fact.out : p.Prime) hp2 hF'
    exact odd_index_Nsub _ h2 (ModelOrd.odd_index_uni hF hp2)
  quat := exists_rhoQ_uni hF hp2
  qs := ModelH2.h2_quasisimple_uni hF h5
  center2 := ModelH2.h2_center_two_uni hF
  even := ModelH2.h2_even_uni hF hp2

theorem exists_uni_params {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), CharP F p ∧ q = p ^ f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp⟩ : ∃ p, CharP F p := ⟨ringChar F, inferInstance⟩
  obtain ⟨n, hpp, hn⟩ := FiniteField.card F p
  have hfp : Fact p.Prime := ⟨hpp⟩
  rw [← Nat.card_eq_fintype_card] at hn
  have hdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hn, hF]; exact Dvd.intro_left q (by ring)
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hpp).1 hdvd
  exact ⟨p, f, hfp, hp, hqf⟩

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hc
  have := FiniteField.even_card_iff_char_two.1 hc
  rw [← Nat.card_eq_fintype_card] at this
  obtain ⟨k, hk⟩ := h
  omega

theorem cases_IsSp4L4U4 {K : Type} [Group K] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : IVK.IsSp4L4U4 K q) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      GoodModel (ModelData.sp F) ∧ ZsTwo (ModelData.sp F) ∧ Nonempty (K ≃* PG (ModelData.sp F))) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ q % 4 = 3 ∧
      GoodModel (ModelData.lin F) ∧ ZsTwo (ModelData.lin F) ∧
        Nonempty (K ≃* PG (ModelData.lin F))) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (p f : ℕ) (_ : Fact p.Prime) (_ : CharP F p)
      (hF : Nat.card F = (p ^ f) ^ 2), q = p ^ f ∧ q % 4 = 1 ∧
      GoodModel (ModelData.uni hF) ∧ ZsTwo (ModelData.uni hF) ∧
        Nonempty (K ≃* PG (ModelData.uni hF))) := by
  rcases hK with ⟨F, iF, fF, hF, ⟨e⟩⟩ | ⟨h4, ⟨h1, F, iF, fF, hF, ⟨e⟩⟩ | ⟨h1, -⟩⟩ |
      ⟨h4, ⟨h1, -⟩ | ⟨-, F, iF, fF, hF, ⟨e⟩⟩⟩
  · have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact hq)
    exact Or.inl ⟨F, iF, fF, hF, goodModel_sp h2 (by rw [hF]; exact h5), zsTwo_sp,
      ⟨e.trans (ModelSp.spEquiv F)⟩⟩
  · have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact hq)
    have hF4 : Nat.card F % 4 = 3 := by rw [hF]; exact h4
    exact Or.inr (Or.inl ⟨F, iF, fF, hF, h4, goodModel_lin h2 (by rw [hF]; exact h5),
      zsTwo_lin hF4, ⟨show K ≃* PG (ModelData.lin F) from e⟩⟩)
  · exact absurd h1 (by norm_num)
  · exact absurd h1 (by norm_num)
  · obtain ⟨p, f, hfp, hcp, hqf⟩ := exists_uni_params hF
    subst hqf
    have hp2 : p ≠ 2 := by
      rintro rfl
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at h5
      · have : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
        obtain ⟨k, hk⟩ := hq
        omega
    exact Or.inr (Or.inr ⟨F, iF, fF, p, f, hfp, hcp, hF, rfl, h4, goodModel_uni hF hp2 h5,
      zsTwo_uni hF h4, ⟨show K ≃* PG (ModelData.uni hF) from e⟩⟩)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
