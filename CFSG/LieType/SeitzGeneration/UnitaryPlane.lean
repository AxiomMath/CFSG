module

public import CFSG.LieType.SeitzGeneration.UnitaryHeis
public import CFSG.LieType.SeitzGeneration.OutdiagPlane

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem isPrimitiveRoot_three_of_pow_eq_one {z : K} (h3 : z ^ 3 = 1) (h1 : z ≠ 1) :
    IsPrimitiveRoot z 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := orderOf_eq_prime h3 h1
  rw [← this]
  exact IsPrimitiveRoot.orderOf z

theorem bar_mul_inv_eq_one (h : UnitaryFieldData ℓ f K) {s : Kˣ} (hs : h.bar (s : K) * s = 1) :
    h.bar ((s⁻¹ : Kˣ) : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hs, inv_one]

theorem pair_of_normalizedU (hcoreI : UnitaryHeisCore) (hcoreO : UnitaryOuterHeisCore)
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    (H : Subgroup (GL (Fin 3) K)) (hHU : H ≤ primeFormUnitary h (idGram K 3))
    (hH : ∀ c : Kˣ, h.bar (c : K) * c = 1 → Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H)
    {x g : GL (Fin 3) K} (hx : x ∈ H) (hg : g ∈ H) {w α s : Kˣ}
    (hrel : g * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hg3 : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (s ^ 3)) :
    ∃ x' ∈ H, ∃ y' ∈ H, NonScalarGL x' ∧ NonScalarGL y' ∧ NonScalarGL (x' * y') ∧
      NonScalarGL (x' * y' ^ 2) ∧ Subgroup.closure (planeFixU ℓ f K x' y') = ⊤ := by
  have hxU := hHU hx
  have hgU := hHU hg
  have hsN : h.bar (s : K) * s = 1 := by
    have h1 := bar_mul_eq_one_of_pow_three h hgU (lam := (s : K) ^ 3) (by
      rw [hg3, coe_scalarGL, Units.val_pow_eq_pow_val])
    refine bar_mul_eq_one_of_cube h hq3 s.ne_zero rfl ?_
    rwa [h.bar_apply, ← pow_succ] at h1
  have hsiN := bar_mul_inv_eq_one h hsN
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin 3) K, y' = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g :=
    ⟨_, rfl⟩
  have hy'H : y' ∈ H := by rw [hy']; exact H.mul_mem (hH _ hsiN) hg
  have hy'U := hHU hy'H
  have hrel' : y' * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * y') := by
    rw [hy']
    calc (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g) * x
        = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (g * x) := mul_assoc _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) := by rw [hrel]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) w *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (x * g)) := by
        rw [← mul_assoc, (commute_scalarGL s⁻¹
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w)).eq, mul_assoc]
      _ = _ := by
        congr 1
        rw [← mul_assoc, ← mul_assoc, (commute_scalarGL s⁻¹ x).eq]
  have hy3 : y' ^ 3 = 1 := by
    rw [hy', Commute.mul_pow (commute_scalarGL s⁻¹ g) 3, ← map_pow, hg3, ← map_mul, ← mul_pow,
      inv_mul_cancel, one_pow, map_one]
  have hmat : ∀ {a b : GL (Fin 3) K} {c : Kˣ},
      a * b = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (b * a) →
        (a : Matrix (Fin 3) (Fin 3) K) * b = (c : K) • ((b : Matrix (Fin 3) (Fin 3) K) * a) := by
    intro a b c hab
    have h1 := congrArg Units.val hab
    rw [Units.val_mul, Units.val_mul (Matrix.GeneralLinearGroup.scalar (Fin 3) c), coe_scalarGL,
      Matrix.smul_mul, Matrix.one_mul, ← Units.val_mul] at h1
    exact h1
  have hy3M : (y' : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hx3M : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = (α : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, coe_scalarGL]
  have hw3K : (w : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have hw1K : (w : K) ≠ 1 := fun h' => hw1 (Units.val_eq_one.1 h')
  have hωK := isPrimitiveRoot_three_of_pow_eq_one hw3K hw1K
  obtain ⟨hn1, hn2, hn3, hn4⟩ := nonScalarGL_lines_of_quasi hrel' (by norm_num) hw1
  have hαN : h.bar (α : K) * α = 1 :=
    bar_mul_eq_one_of_pow_three h hxU (lam := (α : K)) (by
      rw [Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hx3, coe_scalarGL])
  by_cases hcube : ∃ μ : K, μ ^ 3 = (α : K)
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by rintro rfl; exact α.ne_zero (by rw [← hμ]; norm_num)
    have hαN' : (α : K) ^ (ℓ ^ f + 1) = 1 := by
      rwa [h.bar_apply, ← pow_succ] at hαN
    have hμN := bar_mul_eq_one_of_cube h hq3 hμ0 hμ hαN'
    have hμiN : h.bar (μ⁻¹) * μ⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hμN, inv_one]
    obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = μ⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμ0), rfl⟩
    have huN : h.bar (u : K) * u = 1 := by rw [hu]; exact hμiN
    obtain ⟨x₁, hx₁⟩ : ∃ g : GL (Fin 3) K, g = Matrix.GeneralLinearGroup.scalar (Fin 3) u * x :=
      ⟨_, rfl⟩
    have hx₁H : x₁ ∈ H := by rw [hx₁]; exact H.mul_mem (hH u huN) hx
    have hx₁U := hHU hx₁H
    have hx₁c : (x₁ : Matrix (Fin 3) (Fin 3) K) = (u : K) • (x : Matrix (Fin 3) (Fin 3) K) := by
      rw [hx₁, coe_scalarGL_mul]
    have hx₁3 : (x₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [hx₁c, smul_pow, hx3M, smul_smul, hu, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow,
        one_smul]
    have hrel₁ : y' * x₁ = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x₁ * y') := by
      rw [hx₁]
      calc y' * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * x)
          = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (y' * x) := by
            rw [← mul_assoc, ← (commute_scalarGL u y').eq, mul_assoc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * y')) := by rw [hrel']
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) w *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (x * y')) := by
            rw [← mul_assoc, (commute_scalarGL u (Matrix.GeneralLinearGroup.scalar (Fin 3) w)).eq,
              mul_assoc]
        _ = _ := by rw [mul_assoc]
    have hxy₁ : (x₁ : Matrix (Fin 3) (Fin 3) K) * y' =
        ((w⁻¹ : Kˣ) : K) • ((y' : Matrix (Fin 3) (Fin 3) K) * x₁) := by
      rw [hmat hrel₁, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ w.ne_zero, one_smul]
    have hω' : IsPrimitiveRoot ((w⁻¹ : Kˣ) : K) 3 := by
      refine isPrimitiveRoot_three_of_pow_eq_one ?_ ?_
      · rw [← Units.val_pow_eq_pow_val, inv_pow, hw3, inv_one, Units.val_one]
      · intro h1; exact hw1 (inv_eq_one.1 (Units.val_eq_one.1 h1))
    obtain ⟨hm1, hm2, hm3, hm4⟩ := nonScalarGL_lines_of_quasi hrel₁ (by norm_num) hw1
    exact ⟨x₁, hx₁H, y', hy'H, hm1, hm2, hm3, hm4,
      closure_planeFixU_heis_inner hcoreI h hq3 hq hx₁U hy'U hω' hxy₁ hx₁3 hy3M⟩
  · exact ⟨x, hx, y', hy'H, hn1, hn2, hn3, hn4, closure_planeFixU_heis_outer hcoreO h hq3 hq hxU
      hy'U hωK (hmat hrel') hy3M hx3M hcube⟩

theorem exists_pair_closure_planeFixU (hcoreI : UnitaryHeisCore) (hcoreO : UnitaryOuterHeisCore)
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    (H : Subgroup (GL (Fin 3) K)) (hHU : H ≤ primeFormUnitary h (idGram K 3))
    (hH : ∀ c : Kˣ, h.bar (c : K) * c = 1 → Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H)
    {x y : GL (Fin 3) K} (hx : x ∈ H) (hy : y ∈ H) {ω α β : Kˣ}
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y))
    (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hy3 : y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) β)
    (hind : ∀ a b : ℕ, (∃ c : Kˣ, x ^ a * y ^ b = Matrix.GeneralLinearGroup.scalar (Fin 3) c) →
      3 ∣ a ∧ 3 ∣ b) :
    ∃ x' ∈ H, ∃ y' ∈ H, NonScalarGL x' ∧ NonScalarGL y' ∧ NonScalarGL (x' * y') ∧
      NonScalarGL (x' * y' ^ 2) ∧ Subgroup.closure (planeFixU ℓ f K x' y') = ⊤ := by
  have hfin := h.finite
  have hF3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq, sq]
    have h3 : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this
    rw [h3]
    exact Dvd.dvd.mul_right hq3 _
  have hω3 := cube_eq_one_of_quasi_commute hyx
  have hx3M : ((x ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (α : K) • 1 := by
    rw [hx3, coe_scalarGL]
  have hy3M : ((y ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (β : K) • 1 := by
    rw [hy3, coe_scalarGL]
  by_cases hω1 : ω = 1
  · subst hω1
    have hxy : x * y = y * x := by rw [map_one, one_mul] at hyx; exact hyx.symm
    have hind' : ∀ a b : ℕ,
        (∃ c : K, ((x ^ a * y ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) →
          3 ∣ a ∧ 3 ∣ b := fun a b ⟨c, hc⟩ => hind a b (exists_scalarGL_of_coe_eq (by norm_num) hc)
    refine ⟨x, hx, y, hy, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc; have := hind 1 0 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 0 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 2 ⟨c, by simpa using hc⟩; omega
    · exact closure_planeFixU_abelian h hq3 hq (hHU hx) (hHU hy) hxy α.ne_zero β.ne_zero hx3M
        hy3M hind'
  · have hw : ∀ g, Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) g :=
      fun g => commute_scalarGL ω g
    have hw3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K) ^ 3 = 1 := by
      rw [← map_pow, hω3, map_one]
    obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hF3 hw hw3 hyx α.ne_zero β.ne_zero hx3M
      hy3M
    obtain ⟨su, hsu⟩ : ∃ u : Kˣ, (u : K) = s := ⟨Units.mk0 s hs0, rfl⟩
    have hg3 : (x ^ a * y ^ b) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (su ^ 3) := by
      apply Units.ext
      rw [hs3, coe_scalarGL, Units.val_pow_eq_pow_val, hsu]
    have hxc := fun (c : Kˣ) => (commute_scalarGL (F := K) (n := 3) c x).eq
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [pow_one, pow_zero, mul_one] at hg3
      refine pair_of_normalizedU hcoreI hcoreO h hq3 hq H hHU hH hy hx (w := ω⁻¹) (α := β)
        (s := su) ?_ ?_ ?_ hy3 hg3
      · rw [hyx, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      · rw [inv_pow, hω3, inv_one]
      · exact inv_ne_one.2 hω1
    · simp only [pow_zero, one_mul, pow_one] at hg3
      exact pair_of_normalizedU hcoreI hcoreO h hq3 hq H hHU hH hx hy (w := ω) (α := α)
        (s := su) hyx hω3 hω1 hx3 hg3
    · simp only [pow_one] at hg3
      refine pair_of_normalizedU hcoreI hcoreO h hq3 hq H hHU hH hx (H.mul_mem hx hy) (w := ω)
        (α := α) (s := su) ?_ hω3 hω1 hx3 hg3
      calc x * y * x = x * (y * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y)) := by rw [hyx]
        _ = _ := by rw [← mul_assoc, ← hxc ω, mul_assoc]
    · simp only [pow_one] at hg3
      have h2 : y ^ 2 * x = Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2) := by
        rw [map_pow]; exact pow_mul_eq_of_quasi_commute hw hyx 2
      have hω2 : ω ^ 2 ≠ 1 := by
        intro h'
        apply hω1
        calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
          _ = 1 := by rw [hω3, h', inv_one, one_mul]
      refine pair_of_normalizedU hcoreI hcoreO h hq3 hq H hHU hH hx
        (H.mul_mem hx (H.pow_mem hy 2)) (w := ω ^ 2) (α := α) (s := su) ?_
        (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hω2 hx3 hg3
      calc x * y ^ 2 * x = x * (y ^ 2 * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2)) := by rw [h2]
        _ = _ := by rw [← mul_assoc, ← hxc (ω ^ 2), mul_assoc]

end CFSG.LieType.SeitzGeneration
