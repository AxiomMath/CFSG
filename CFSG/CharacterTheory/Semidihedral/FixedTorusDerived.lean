module

public import CFSG.CharacterTheory.Semidihedral.FixedTorusDerivedSupport

public section

namespace CFSG.Semidihedral.FixedTorusDerived

noncomputable section

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData

universe u

theorem odd_field_fixed_torus_derived_subgroup_has_exact_torus_centralizer
    (F : Type u) [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (A : Subgroup (F ≃+* F)) (hA : Odd (Nat.card A))
    (a : Fˣ) (ha : ¬IsSquare a) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    let φ := torusFieldAction F a A hfix
    (∀ X : SL F, X ∈ Torus F a ↔ ∃ x y : F,
      (X : Matrix (Fin 2) (Fin 2) F) = torusMatrix F a x y ∧ x ^ 2 + (a : F) * y ^ 2 = 1) ∧
    (∀ X : Torus F a, X ∈ W F a ↔ Odd (orderOf X)) ∧
    IsCyclic (W F a) ∧ Nat.card (W F a) = torusSize (Nat.card F) / 2 ∧
    (∀ (sigma : A) (X : W F a), ((φ sigma X).val.val : Matrix (Fin 2) (Fin 2) F) =
      (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F)) ∧
    IsCyclic A ∧
    (∀ sigma : A,
      orderOf sigma ∣ f ∧
      Nat.card (MatrixCover.FixedField F (Subgroup.zpowers (sigma : F ≃+* F))) =
        p ^ (f / orderOf sigma) ∧
      Nat.card F = (p ^ (f / orderOf sigma)) ^ orderOf sigma ∧
      Nat.card {X : W F a // φ sigma X = X} =
        (if Nat.card F % 4 = 1 then p ^ (f / orderOf sigma) + 1
          else p ^ (f / orderOf sigma) - 1) / 2 ∧
      (sigma ≠ 1 → Nat.card {X : W F a // φ sigma X = X} ^ 2 < Nat.card (W F a))) ∧
    (∀ sigma0 : A, Subgroup.zpowers sigma0 = ⊤ →
      commutator (W F a ⋊[φ] A) =
        ⁅(SemidirectProduct.inl : W F a →* W F a ⋊[φ] A).range,
          Subgroup.zpowers (SemidirectProduct.inr sigma0 : W F a ⋊[φ] A)⁆ ∧
      commutator (W F a ⋊[φ] A) =
        (Subgroup.closure (Set.range fun X : W F a => X⁻¹ * φ sigma0 X)).map
          (SemidirectProduct.inl : W F a →* W F a ⋊[φ] A) ∧
      Nat.card (commutator (W F a ⋊[φ] A)) =
        Nat.card (W F a) / Nat.card {X : W F a // ∀ sigma : A, φ sigma X = X}) ∧
    Subgroup.centralizer (commutator (W F a ⋊[φ] A) : Set (W F a ⋊[φ] A)) =
      (SemidirectProduct.inl : W F a →* W F a ⋊[φ] A).range ∧
    Function.Injective φ ∧
    (Nat.card A = 1 → commutator (W F a ⋊[φ] A) = ⊥ ∧
      (SemidirectProduct.inl : W F a →* W F a ⋊[φ] A).range = ⊤) := by
  intro φ
  have hqodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  obtain ⟨hcoord, -, -, -, -, hWcyc, hWcard, hWodd, -⟩ :=
    nonsquare_matrix_semilinear_involution_centralizer F a A hfix hqodd ha
  obtain ⟨-, -, -, hcyc, hautcard, -⟩ :=
    CFSG.Semidihedral.SemilinearOuterQuotient.odd_field_projective_semilinear_exact_outer_quotient
      F hp hpodd hf hcard
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hautcard]; omega)
  have hAcyc : IsCyclic A := Subgroup.isCyclic A
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  have hfixed : ∀ sigma : A,
      orderOf sigma ∣ f ∧
      Nat.card (MatrixCover.FixedField F (Subgroup.zpowers (sigma : F ≃+* F))) =
        p ^ (f / orderOf sigma) ∧
      Nat.card F = (p ^ (f / orderOf sigma)) ^ orderOf sigma ∧
      Nat.card {X : W F a // φ sigma X = X} =
        (if Nat.card F % 4 = 1 then p ^ (f / orderOf sigma) + 1
          else p ^ (f / orderOf sigma) - 1) / 2 ∧
      (sigma ≠ 1 → Nat.card {X : W F a // φ sigma X = X} ^ 2 < Nat.card (W F a)) := by
    intro sigma
    set σ := (sigma : F ≃+* F) with hσ
    have hordσ : orderOf σ = orderOf sigma := Subgroup.orderOf_coe sigma
    obtain ⟨hdvd, hKcard⟩ := CFSG.Wreathed.OddFieldTorus.card_fixedField hp hf hcard σ
    rw [hordσ] at hdvd hKcard
    have hmodd : Odd (orderOf sigma) := hA.of_dvd_nat (orderOf_dvd_natCard sigma)
    have hmpos : 0 < orderOf sigma := hmodd.pos
    have hq : Nat.card F = (p ^ (f / orderOf sigma)) ^ orderOf sigma := by
      rw [hcard, ← pow_mul, Nat.div_mul_cancel hdvd]
    have hFix : Nat.card (MatrixCover.FixedField F (Subgroup.zpowers σ)) =
        Nat.card (CFSG.Wreathed.OddFieldTorus.fixedField σ) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [CFSG.Wreathed.OddFieldTorus.mem_fixedField]
      constructor
      · intro hx
        exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
      · intro hx g
        have hstab : σ ∈ MulAction.stabilizer (F ≃+* F) x := by
          rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
          exact hx
        have h := Subgroup.zpowers_le.mpr hstab g.2
        rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h
    have hbodd : Odd (p ^ (f / orderOf sigma)) := hpodd.pow
    have hb3 : 3 ≤ p ^ (f / orderOf sigma) := by
      have hfm : 1 ≤ f / orderOf sigma :=
        (Nat.one_le_div_iff hmpos).mpr (Nat.le_of_dvd (by omega) hdvd)
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (f / orderOf sigma) := Nat.pow_le_pow_right hp.pos hfm
    have hmod : p ^ (f / orderOf sigma) % 4 = Nat.card F % 4 := by
      rw [hq, CFSG.Wreathed.OddFieldTorus.pow_mod_four hbodd hmodd]
    have hcW : Nat.card {X : W F a // φ sigma X = X} =
        torusSize (p ^ (f / orderOf sigma)) / 2 := by
      rw [card_fixed_W hqodd ha A hfix sigma, hKcard]
    refine ⟨hdvd, hFix.trans hKcard, hq, ?_, fun hne => ?_⟩
    · rw [hcW, torusSize, hmod]
    · have hm1 : orderOf sigma ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      have hm3 : 3 ≤ orderOf sigma := by
        rcases hmodd with ⟨k, hk⟩
        omega
      rw [hcW, hWcard, hq]
      exact torusSize_half_sq_lt hb3 hbodd hm3
  have hsmall : ∀ s : A, s ≠ 1 →
      Nat.card {X : W F a // φ s X = X} ^ 2 < Nat.card (W F a) := fun s hs =>
    (hfixed s).2.2.2.2 hs
  have hderived : ∀ sigma0 : A, Subgroup.zpowers sigma0 = ⊤ → _ := fun sigma0 h0 =>
    CFSG.Wreathed.OddFieldTorus.semidirect_cyclic_derived φ (W_mul_comm F a) sigma0 h0 hsmall
  obtain ⟨g0, hg0⟩ := hAcyc.exists_generator
  have hg0top : Subgroup.zpowers g0 = ⊤ := (Subgroup.eq_top_iff' _).mpr hg0
  have : Nonempty {X : W F a // ∀ sigma : A, φ sigma X = X} := ⟨⟨1, fun _ => map_one _⟩⟩
  have hcfix_pos : 0 < Nat.card {X : W F a // ∀ sigma : A, φ sigma X = X} := Nat.card_pos
  refine ⟨hcoord, hWodd, hWcyc, hWcard, fun _ _ => rfl, hAcyc, hfixed, fun sigma0 h0 => ?_,
    (hderived g0 hg0top).2.2.2, ?_, fun hA1 => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hderived sigma0 h0
    exact ⟨h1, h2, (Nat.div_eq_of_eq_mul_left hcfix_pos h3.symm).symm⟩
  ·
    refine (injective_iff_map_eq_one φ).mpr fun s hs => ?_
    by_contra hne
    have h := hsmall s hne
    have hall : Nat.card {X : W F a // φ s X = X} = Nat.card (W F a) := by
      rw [hs]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    rw [hall] at h
    have hpos : 0 < Nat.card (W F a) := Nat.card_pos
    nlinarith
  ·
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    have h1top : Subgroup.zpowers (1 : A) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun x => by
        rw [Subsingleton.elim x 1]
        exact Subgroup.one_mem _
    obtain ⟨-, h2, -, -⟩ := hderived 1 h1top
    refine ⟨?_, ?_⟩
    · rw [h2]
      have hrange : Set.range (fun X : W F a => X⁻¹ * φ 1 X) = {1} := by
        ext X
        simp
      rw [hrange, Subgroup.closure_singleton_one, Subgroup.map_bot]
    · rw [eq_top_iff]
      intro x _
      refine ⟨x.left, ?_⟩
      apply SemidirectProduct.ext
      · rfl
      · exact Subsingleton.elim _ _

end

end CFSG.Semidihedral.FixedTorusDerived
