module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMCenter
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM2

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem finite_mulAut (P : Type) [Group P] [Finite P] : Finite (MulAut P) :=
  Finite.of_injective (fun a : MulAut P => (a : P → P)) fun a b hab => MulEquiv.ext (congrFun hab)

theorem card_mulAut_dvd_of_outer {P : Type} [Group P] [Finite P] {a g N : ℕ}
    (hout : Nat.card (Outer P) ∣ a * g) (hcard : Nat.card P * g = N) :
    Nat.card (MulAut P) ∣ a * N := by
  haveI := finite_mulAut P
  have hinn : Nat.card (inner P) ∣ Nat.card P := Subgroup.card_range_dvd _
  have hAut : Nat.card (MulAut P) = Nat.card (Outer P) * Nat.card (inner P) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (inner P)).trans rfl
  rw [hAut, ← hcard]
  calc Nat.card (Outer P) * Nat.card (inner P) ∣ (a * g) * Nat.card P := mul_dvd_mul hout hinn
    _ = a * (Nat.card P * g) := by ring

noncomputable def descend (S : Type) [Group S] : MulAut S →* MulAut (S ⧸ Subgroup.center S) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.characteristic_iff_map_eq.1 inferInstance σ)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' σ τ := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      simp only [map_mul, MulAut.mul_apply]
      rfl

theorem descend_injective (S : Type) [Group S] [Group.IsPerfect S] :
    Function.Injective (descend S) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hcen : ∀ x : S, x⁻¹ * σ x ∈ Subgroup.center S := fun x => by
    have h1 : (QuotientGroup.mk (σ x) : S ⧸ Subgroup.center S) = QuotientGroup.mk x :=
      DFunLike.congr_fun hσ (QuotientGroup.mk x)
    exact QuotientGroup.eq.1 h1.symm
  let c : S →* Subgroup.center S :=
    { toFun := fun x => ⟨x⁻¹ * σ x, hcen x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hcen x) (y⁻¹)
        have e1 : (x * y)⁻¹ * σ (x * y) = y⁻¹ * (x⁻¹ * σ x) * σ y := by
          rw [map_mul, mul_inv_rev]
          group
        change (x * y)⁻¹ * σ (x * y) = (x⁻¹ * σ x) * (y⁻¹ * σ y)
        rw [e1, hc]
        group }
  have hker : commutator S ≤ c.ker := Abelianization.commutator_subset_ker c
  ext x
  have hx : x ∈ commutator S := Group.IsPerfect.mem_commutator
  have h1 : c x = 1 := hker hx
  have h2 : x⁻¹ * σ x = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 h2).symm

noncomputable def quotCenterEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr _ _ e (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e)

noncomputable def slEquivStatedSL (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 3 K).symm)

theorem linear_aut_dvd {W K : Type} [Group W] [Finite W] [Field K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h3 : 3 ∣ p ^ f - 1) (e : W ≃* StatedSL 3 K)
    (hZ : Nat.card (Subgroup.center W) = 3) :
    Nat.card (MulAut (W ⧸ Subgroup.center W)) ∣ 2 * f * Nat.card W := by
  let e' : W ≃* Matrix.SpecialLinearGroup (Fin 3) K := e.trans (slEquivStatedSL K).symm
  let ψ : W ⧸ Subgroup.center W ≃* LinearFlag.projectiveSL 3 K :=
    (quotCenterEquiv e').trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 K)).symm
  haveI : Finite (LinearFlag.projectiveSL 3 K) := Finite.of_equiv _ ψ.toEquiv
  have hout : Nat.card (Outer (LinearFlag.projectiveSL 3 K)) ∣ 2 * f * 3 := by
    have := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound (n := 3) hp hf
      (le_refl 3) hK
    rwa [Nat.gcd_eq_left h3] at this
  have hcard : Nat.card (LinearFlag.projectiveSL 3 K) * 3 = Nat.card W := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W)
    rw [hZ, Nat.card_congr ψ.toEquiv] at h1
    exact h1.symm
  rw [Nat.card_congr (MulAut.congr ψ).toEquiv]
  exact card_mulAut_dvd_of_outer hout hcard

theorem unitary_aut_dvd {W K : Type} [Group W] [Finite W] [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1) (hq2 : p ^ f ≠ 2)
    (e : W ≃* unitarySU p f K 3) (hZ : Nat.card (Subgroup.center W) = 3) :
    Nat.card (MulAut (W ⧸ Subgroup.center W)) ∣ 2 * f * Nat.card W := by
  haveI : Finite K := h.finite
  haveI : Finite (unitarySU p f K 3) := Finite.of_equiv W e.toEquiv
  have hZ' : Nat.card (Subgroup.center (unitarySU p f K 3)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans hZ
  have hscal : unitaryScalars h 3 = Subgroup.center (unitarySU p f K 3) :=
    Subgroup.eq_of_le_of_card_ge (unitaryScalars_le_center h 3) (by
      rw [hZ', card_unitaryScalars h (by norm_num), Nat.gcd_eq_left h3])
  let ψ : W ⧸ Subgroup.center W ≃* unitaryPSU h 3 :=
    (quotCenterEquiv e).trans (QuotientGroup.quotientMulEquivOfEq hscal.symm)
  haveI : Finite (unitaryPSU h 3) := Finite.of_equiv _ ψ.toEquiv
  have hout : Nat.card (Outer (unitaryPSU h 3)) ∣ 2 * f * 3 := by
    have := (UnitaryHigher.unitary_full_diagonal_outer_order h (n := 3) (le_refl 3)
      (fun h' => hq2 h'.2)).2.2.2.2.1
    rw [Nat.gcd_eq_left h3] at this
    exact dvd_of_eq this
  have hcard : Nat.card (unitaryPSU h 3) * 3 = Nat.card W := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W)
    rw [hZ, Nat.card_congr ψ.toEquiv] at h1
    exact h1.symm
  rw [Nat.card_congr (MulAut.congr ψ).toEquiv]
  exact card_mulAut_dvd_of_outer hout hcard

theorem finite_of_sl3EpsOfChar {p : ℕ} {W : Type} [Group W] (h : SL3EpsOfChar p W) : Finite W := by
  rcases h with ⟨F, hF, hfin, -, -, ⟨e⟩⟩ | ⟨F, hF, hfin, q, -, -, -, -, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv

theorem sl3Eps_aut_data {p : ℕ} {W : Type} [Group W] [Finite W] (h : SL3EpsOfChar p W) :
    ∃ (r : ℕ) (ε : Bool) (f : ℕ), L3Cond r ε ∧ Nat.card W = L3Ord r ε ∧ r = p ^ f ∧
      Nat.card (MulAut (W ⧸ Subgroup.center W)) ∣ 2 * f * L3Ord r ε := by
  obtain ⟨hZ3, -⟩ := sl3Eps_facts h
  rcases h with ⟨F, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨F, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e⟩⟩
  ·
    haveI := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F p
    have hK : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    have hr4 : 4 ≤ Nat.card F := by
      have : 1 < Nat.card F := Finite.one_lt_card
      omega
    have hW : Nat.card W = L3Ord (Nat.card F) true := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
      simp [L3Ord]
    refine ⟨Nat.card F, true, n, ⟨fun _ => ⟨hr4, hmod⟩, fun h => by simp at h⟩, hW, hK, ?_⟩
    have h3 : 3 ∣ Nat.card F - 1 := by omega
    rw [hK] at h3
    rw [← hW]
    exact linear_aut_dvd hp n.pos hK h3 e hZ3
  ·
    haveI := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F p
    have hK : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    have hqd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hK, hcard]; ring⟩
    obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hp).1 hqd
    subst hqf
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with hf0 | hf0
      · subst hf0
        simp at hq3
      · exact hf0
    have hU : UnitaryFieldData p f F :=
      ⟨hp, hf1, by rw [hcard, ← pow_mul, mul_comm]⟩
    have hW : Nat.card W = L3Ord (p ^ f) false := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hcard]
      simp [L3Ord]
    refine ⟨p ^ f, false, f, ⟨fun h => by simp at h, fun _ => ⟨by omega, hq3⟩⟩, hW, rfl, ?_⟩
    have h3 : 3 ∣ p ^ f + 1 := by omega
    rw [← hW]
    exact unitary_aut_dvd hU h3 hq2 e hZ3

theorem l3AutDvd_of_isL3Kind {p : ℕ} {X : Type} [Group X] [Finite X] (h : IsL3Kind p X) :
    ∃ (r : ℕ) (ε : Bool) (f e : ℕ), (e = 1 ∨ e = 3) ∧ L3Cond r ε ∧ Nat.card X * e = L3Ord r ε ∧
      r = p ^ f ∧ Nat.card (MulAut X) ∣ 2 * f * L3Ord r ε := by
  rcases h with hSL | ⟨W, hW, hWSL, ⟨ψ⟩⟩
  · obtain ⟨r, ε, f, hc, hcard, hr, hdvd⟩ := sl3Eps_aut_data hSL
    haveI := CFSG.HardMathSupport.Dickson.Sec6.BM.isPerfect_of_sl3EpsOfChar hSL
    refine ⟨r, ε, f, 1, Or.inl rfl, hc, by rw [mul_one, hcard], hr, ?_⟩
    exact (Subgroup.card_dvd_of_injective _ (descend_injective X)).trans hdvd
  · haveI := finite_of_sl3EpsOfChar hWSL
    obtain ⟨r, ε, f, hc, hcard, hr, hdvd⟩ := sl3Eps_aut_data hWSL
    obtain ⟨hZ3, -⟩ := sl3Eps_facts hWSL
    refine ⟨r, ε, f, 3, Or.inr rfl, hc, ?_, hr, ?_⟩
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W)
      rw [hZ3, ← Nat.card_congr ψ.toEquiv] at h1
      rw [← hcard, h1]
    · rw [Nat.card_congr (MulAut.congr ψ).toEquiv]
      exact hdvd

end CFSG.HardMathSupport.Dickson.Sec6.BM2
