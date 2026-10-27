module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesFixed
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalEquality

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

section Cyclic

variable {G : Type*} [Group G] [Finite G]

theorem card_pow_eq_one_of_isCyclic [IsCyclic G] {d : ℕ} (hd : d ∣ Nat.card G) :
    Nat.card {x : G // x ^ d = 1} = d := by
  let : Fintype G := Fintype.ofFinite G
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd Nat.card_pos
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hd0
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact Nat.card_pos.ne' hc
    have hxord : orderOf (g ^ c) = d := by
      rw [orderOf_pow' g hc0, hord, hc, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by omega)]
    have hpow : ∀ y ∈ Subgroup.zpowers (g ^ c), y ^ d = 1 := by
      rintro y ⟨j, rfl⟩
      dsimp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxord,
        pow_orderOf_eq_one, one_zpow]
    calc d = Nat.card (Subgroup.zpowers (g ^ c)) := by rw [Nat.card_zpowers, hxord]
      _ ≤ Nat.card {x : G // x ^ d = 1} :=
        Nat.card_le_card_of_injective (fun y => ⟨y.1, hpow y.1 y.2⟩) (by
          intro y y' h
          apply Subtype.ext
          simpa using congrArg Subtype.val h)

theorem exists_two_pow_orderOf_iff (x : G) :
    (∃ k : ℕ, orderOf x = 2 ^ k) ↔ x ^ (2 ^ (Nat.card G).factorization 2) = 1 := by
  have hN : Nat.card G ≠ 0 := Nat.card_pos.ne'
  constructor
  · rintro ⟨k, hk⟩
    have hdvd : 2 ^ k ∣ Nat.card G := hk ▸ orderOf_dvd_natCard x
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hN).mp hdvd
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact Nat.pow_dvd_pow 2 hle
  · intro h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨k, hk⟩

theorem card_two_pow_orderOf_of_isCyclic [IsCyclic G] :
    Nat.card {x : G // ∃ k : ℕ, orderOf x = 2 ^ k} = 2 ^ (Nat.card G).factorization 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight exists_two_pow_orderOf_iff)]
  exact card_pow_eq_one_of_isCyclic (Nat.ordProj_dvd _ _)

end Cyclic

section Characters

variable (F : Type) [Field F] [Fintype F]

theorem card_two_pow_units_hom :
    Nat.card {η : Fˣ →* ℂˣ // ∃ k : ℕ, orderOf η = 2 ^ k} =
      2 ^ (Nat.card F - 1).factorization 2 := by
  have := CentralSL2.finite_units_hom F
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
  have : IsCyclic (Fˣ →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  rw [card_two_pow_orderOf_of_isCyclic, CentralSL2.card_units_hom]

theorem card_two_pow_units_hom_ne_one :
    Nat.card {η : Fˣ →* ℂˣ // (∃ k : ℕ, orderOf η = 2 ^ k) ∧ η ≠ 1} =
      2 ^ (Nat.card F - 1).factorization 2 - 1 := by
  have := CentralSL2.finite_units_hom F
  let : Fintype (Fˣ →* ℂˣ) := Fintype.ofFinite _
  rw [← card_two_pow_units_hom F]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit : (Finset.univ.filter fun η : Fˣ →* ℂˣ => ∃ k : ℕ, orderOf η = 2 ^ k) =
      insert 1 (Finset.univ.filter fun η : Fˣ →* ℂˣ => (∃ k : ℕ, orderOf η = 2 ^ k) ∧ η ≠ 1) := by
    ext η
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases h1 : η = 1
      · exact Or.inl h1
      · exact Or.inr ⟨h, h1⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact ⟨0, by rw [orderOf_one, pow_zero]⟩
      · exact h
  rw [hsplit, Finset.card_insert_of_notMem (by simp)]
  simp

variable (b : Fˣ) (m : ℕ)

theorem card_principalSeriesParameter_filter (hm : 0 < m) (Q : (Fˣ →* ℂˣ) → Prop) :
    Nat.card {P : CentralSL2.PrincipalSeriesParameter F b m // Q P.1.1} =
      Nat.card {η : Fˣ →* ℂˣ // Q η} * m := by
  have := CentralSL2.finite_units_hom F
  let e : {P : CentralSL2.PrincipalSeriesParameter F b m // Q P.1.1} ≃
      (η : {η : Fˣ →* ℂˣ // Q η}) × {z : ℂˣ // z ^ m = η.1 (CentralSL2.torusConstant F b m)} :=
    { toFun := fun P => ⟨⟨P.1.1.1, P.2⟩, ⟨P.1.1.2, P.1.2⟩⟩
      invFun := fun x => ⟨⟨(x.1.1, x.2.1), x.2.2⟩, x.1.2⟩
      left_inv := fun P => rfl
      right_inv := fun x => rfl }
  have hfin : ∀ η : {η : Fˣ →* ℂˣ // Q η},
      Finite {z : ℂˣ // z ^ m = η.1 (CentralSL2.torusConstant F b m)} := fun η =>
    Nat.finite_of_card_ne_zero (by rw [CentralSL2.card_pow_eq m hm]; exact hm.ne')
  let : Fintype {η : Fˣ →* ℂˣ // Q η} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [CentralSL2.card_pow_eq m hm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem card_two_pow_principalSeriesParameter (hm : 0 < m) :
    Nat.card {P : CentralSL2.PrincipalSeriesParameter F b m //
      (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1} =
      m * (2 ^ (Nat.card F - 1).factorization 2 - 1) := by
  rw [card_principalSeriesParameter_filter F b m hm
    (fun η => (∃ k : ℕ, orderOf η = 2 ^ k) ∧ η ≠ 1), card_two_pow_units_hom_ne_one, mul_comm]

end Characters

section Count

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem fieldParameter_eq_of_two_power (hd : Odd (Nat.card Sigma))
    {P : CentralSL2.PrincipalSeriesParameter F b m} {k : ℕ} (hk : orderOf P.1.1 = 2 ^ k)
    (σ : Sigma) : CentralSL2.fieldParameter hSigma σ P = P := by
  have h := parameterStabilizer_eq_top_of_two_power hSigma hd P hk
  have hσ : σ ∈ CentralSL2.parameterStabilizer hSigma P := by rw [h]; exact Subgroup.mem_top σ
  exact hσ

theorem ncard_principalInduced_two_power (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma)) :
    Set.ncard ((fun P : CentralSL2.PrincipalSeriesParameter F b m =>
      CentralSL2.principalInduced (hm := hm) (heven := heven) hSigma P 1) ''
        {P | (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1}) =
      m * (2 ^ (Nat.card F - 1).factorization 2 - 1) / 2 := by
  set S : Set (CentralSL2.PrincipalSeriesParameter F b m) :=
    {P | (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1} with hSdef
  have hcardS := card_two_pow_principalSeriesParameter F b m hm
  have hfinP : Finite (CentralSL2.PrincipalSeriesParameter F b m) :=
    Nat.finite_of_card_ne_zero (by
      rw [CentralSL2.card_principalSeriesParameter F b m hm]
      have := Fintype.one_lt_card (α := F)
      have hq : 1 < Nat.card F := by rw [Nat.card_eq_fintype_card]; exact this
      exact Nat.mul_ne_zero (by omega) hm.ne')
  have hS : ∀ P ∈ S, CentralSL2.weylParameter F b m heven P ∈ S ∧
      CentralSL2.weylParameter F b m heven P ≠ P := by
    rintro P ⟨⟨k, hk⟩, hP⟩
    refine ⟨⟨⟨k, ?_⟩, ?_⟩, ?_⟩
    · exact (orderOf_inv P.1.1).trans hk
    · intro h
      apply hP
      refine MonoidHom.ext fun c => ?_
      have h' := DFunLike.congr_fun (show (P.1.1)⁻¹ = (1 : Fˣ →* ℂˣ) from h) c
      rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at h'
      rw [h', MonoidHom.one_apply]
    · intro h
      exact hP ((CentralSL2.weylParameter_eq_self_iff F b m heven hb P).mp h)
  have hf : ∀ P ∈ S, ∀ Q ∈ S,
      CentralSL2.principalInduced (hm := hm) (heven := heven) hSigma P 1 =
        CentralSL2.principalInduced hSigma Q 1 ↔
      Q = P ∨ Q = CentralSL2.weylParameter F b m heven P := by
    rintro P ⟨⟨k, hk⟩, hP⟩ Q ⟨-, hQ⟩
    rw [CentralSL2.principalInduced_eq_iff hSigma hb hd hP hQ]
    have hkw : orderOf (CentralSL2.weylParameter F b m heven P).1.1 = 2 ^ k := by
      exact (orderOf_inv P.1.1).trans hk
    constructor
    · rintro ⟨⟨σ, hσ | hσ⟩, -⟩
      · left
        rw [hσ, fieldParameter_eq_of_two_power hSigma hd hk]
      · right
        rw [hσ, fieldParameter_eq_of_two_power hSigma hd hkw]
    · intro h
      refine ⟨⟨1, ?_⟩, fun τ h₁ h₂ => rfl⟩
      rw [CentralSL2.fieldParameter_one, CentralSL2.fieldParameter_one]
      exact h
  have h2 := CentralSL2.two_mul_ncard_image_of_pairs
    (fun P : CentralSL2.PrincipalSeriesParameter F b m =>
      CentralSL2.principalInduced (hm := hm) (heven := heven) hSigma P 1)
    (CentralSL2.weylParameter F b m heven) S hS hf
  rw [show Set.ncard S = m * (2 ^ (Nat.card F - 1).factorization 2 - 1) by
    rw [← hcardS, ← Nat.card_coe_set_eq]; rfl] at h2
  omega

end Count

end CFSG.Wreathed
