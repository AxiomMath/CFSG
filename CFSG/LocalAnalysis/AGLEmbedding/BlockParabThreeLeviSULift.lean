module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem exists_primitive_cube_root_of_card_four (hF : Nat.card F = (2 ^ 1) ^ 2) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have := Fintype.ofFinite F
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hle : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have := (Finset.card_le_card hle).trans (Finset.card_le_two (a := (0 : F)) (b := 1))
    rw [Finset.card_univ, hF4] at this
    omega
  refine ⟨ω, hω.1, hω.2, ?_⟩
  have := FiniteField.pow_card_sub_one_eq_one ω hω.1
  rwa [hF4] at this

theorem exists_mem_center_orderOf_eq_three (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}
    (hn : 3 ∣ n) (hn0 : 0 < n) :
    ∃ z ∈ Subgroup.center (SU (unitaryInvolution F 2 1) n), orderOf z = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_primitive_cube_root_of_card_four hF
  set u : Fˣ := Units.mk0 ω hω0 with hu
  set g : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) u with hg
  have hgmat : (g : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) ω :=
    Matrix.GeneralLinearGroup.coe_scalar u
  have hσ : unitaryInvolution F 2 1 ω = ω ^ 2 := by
    rw [unitaryInvolution_apply, pow_one]
  have hgSU : g ∈ SU (unitaryInvolution F 2 1) n := by
    rw [mem_SU, hgmat]
    obtain ⟨k, rfl⟩ := hn
    refine ⟨?_, ?_⟩
    · rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, pow_mul, hω3, one_pow]
    · ext i j
      simp only [conjTr, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hσ,
        Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [show ω ^ 2 * antidiag (3 * k) i j * ω = ω ^ 3 * antidiag (3 * k) i j by ring, hω3,
        one_mul]
  set z : SU (unitaryInvolution F 2 1) n := ⟨g, hgSU⟩ with hz
  refine ⟨z, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hz, hgmat]
    exact (Matrix.scalar_commute ω (fun r => mul_comm ω r) _).symm
  · apply orderOf_eq_prime
    · apply Subtype.ext
      apply Units.ext
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hz, hgmat, Subgroup.coe_one,
        Units.val_one]
      rw [← map_pow, hω3, map_one]
    · intro h1
      have := congrArg (fun w : SU (unitaryInvolution F 2 1) n =>
        ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ⟨0, hn0⟩ ⟨0, hn0⟩) h1
      simp only [hz, hgmat, Subgroup.coe_one, Units.val_one, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact hω1 this

theorem exists_lift_su (hGA : CFSG.Open.GriessAllModelsStatement) (hF : Nat.card F = (2 ^ 1) ^ 2)
    {n : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] (hc : StatedClassicalModel X .PSU n 2 1)
    (hX : Subgroup.center X = ⊥) (π : SU (unitaryInvolution F 2 1) n →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E) (p : E →* X)
    (hp : Function.Surjective p) (hk : p.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 p.ker) :
    ∃ α : SU (unitaryInvolution F 2 1) n →* E, Function.Surjective α ∧
      α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨e, he16, hcard⟩ := card_hopfMultiplier_of_model_psu_two hGA hc
  by_cases h3n : 3 ∣ n
  ·
    have hperf : Group.IsPerfect (SU (unitaryInvolution F 2 1) n) :=
      (isQuasisimple_SU (n := n) hF (by omega) (fun h => by simp at h; omega)).1
    obtain ⟨z, hzc, hz3⟩ := exists_mem_center_orderOf_eq_three hF h3n (by omega)
    have hzker : z ∈ π.ker := by
      have : π z ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w, rfl⟩ := hπ w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc w]
      rw [hX, Subgroup.mem_bot] at this
      exact this
    have h3k : 3 ∣ Nat.card π.ker := by
      have := Subgroup.orderOf_dvd_natCard π.ker hzker
      rwa [hz3] at this
    obtain ⟨m, hm⟩ := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf π hπ hker
    have hcard' : Nat.card (hopfMultiplier X) = 3 * e := by rw [hcard, Nat.gcd_eq_right h3n]
    have hm3 : Nat.Coprime 3 m := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hm3
      have h9 : 3 * 3 ∣ 3 * e := by
        rw [← hcard', hm]
        exact Nat.mul_dvd_mul h3k hm3
      have : 3 ∣ e := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
      have := this.trans he16
      norm_num at this
    obtain ⟨α, hα, hcomp⟩ := exists_lift_of_coprime_multiplier_index hperf hE π hπ hker p hp hk
      Nat.prime_three h3 m hm3 hm
    refine ⟨α, hα, fun x hx => hker ?_⟩
    rw [MonoidHom.mem_ker, ← hcomp, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, map_one]
  ·
    have hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
      rw [hcard, show Nat.gcd n 3 = 1 from
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3n)), one_mul]
      exact Nat.Coprime.coprime_dvd_right he16 (by norm_num)
    have hbot := ker_eq_bot_of_coprime_hopfMultiplier hE p hp hk h3 hM
    let ψ : E ≃* X := MulEquiv.ofBijective p ⟨(MonoidHom.ker_eq_bot_iff p).1 hbot, hp⟩
    refine ⟨ψ.symm.toMonoidHom.comp π, ψ.symm.surjective.comp hπ, fun x hx => hker ?_⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective] at hx
    exact hx

end CFSG.AGLEmbedding
