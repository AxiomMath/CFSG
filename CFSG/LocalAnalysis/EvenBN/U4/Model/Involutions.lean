module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Orbits

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Involutions

variable [CharP K 2]

theorem miyamotoZ1_mem_gramSU : miyamotoZ1 K ∈ gramSU h (miyamotoJ4 K) := by
  rw [miyamotoZ1_eq h]
  exact miyamotoUnipotent_le_SU h false false (miyamotoZ_le_P h ⟨1, map_one _, rfl⟩)

theorem miyamotoZ2_mem_gramSU : LocalAnalysis.miyamotoZ2 K ∈ gramSU h (miyamotoJ4 K) := by
  rw [miyamotoZ2_eq h]
  exact miyamotoUnipotent_le_SU h false false ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h)
    ((miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, map_zero _⟩))

theorem miyamotoXGL_A1_mul_self {b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h 0 b c d * miyamotoXGL h 0 b c d = 1 := by
  rw [miyamotoXGL_mul_A1 h hb, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, miyamotoXGL_zero]

include h in
theorem orderOf_miyamotoZ1 : orderOf (miyamotoZ1 K) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [miyamotoZ1_eq h]
  refine orderOf_eq_prime (by rw [sq, miyamotoXGL_A1_mul_self h (map_zero _)]) fun e => ?_
  rw [← miyamotoXGL_zero h, miyamotoXGL_inj] at e
  exact one_ne_zero e.2.2.2

include h in
theorem orderOf_miyamotoZ2 : orderOf (LocalAnalysis.miyamotoZ2 K) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [miyamotoZ2_eq h]
  refine orderOf_eq_prime (by rw [sq, miyamotoXGL_A1_mul_self h (map_zero _)]) fun e => ?_
  rw [← miyamotoXGL_zero h, miyamotoXGL_inj] at e
  exact one_ne_zero e.2.2.1

theorem exists_conj_mem_P {x : GL (Fin 4) K} (hx : x ∈ gramSU h (miyamotoJ4 K))
    (hx2 : orderOf x = 2) :
    ∃ g ∈ gramSU h (miyamotoJ4 K), g⁻¹ * x * g ∈ miyamotoP h := by
  have := finite_gramSU_miyamotoJ4 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := gramSU h (miyamotoJ4 K)
  set x' : S := ⟨x, hx⟩
  have hx'2 : orderOf x' = 2 := by
    rw [← hx2]
    exact (orderOf_injective S.subtype S.subtype_injective x').symm
  have hp : IsPGroup 2 (zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨P', hP'⟩ := exists_sylow_miyamotoP h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P'
  have hmem : g * x' * g⁻¹ ∈ (P' : Subgroup S) := by
    rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists]
    exact ⟨x', hQ (mem_zpowers x'), rfl⟩
  rw [hP', mem_subgroupOf] at hmem
  refine ⟨((g⁻¹ : S) : GL (Fin 4) K), (g⁻¹).2, ?_⟩
  simpa using hmem

theorem exists_conj_mem_A1 {p : GL (Fin 4) K} (hp : p ∈ miyamotoP h) (hp2 : p * p = 1) :
    ∃ g ∈ gramSU h (miyamotoJ4 K), g⁻¹ * p * g ∈ miyamotoA1 h := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hp
  by_cases ha : a = 0
  · exact ⟨1, one_mem _, by simp [(miyamotoXGL_mem_A1_iff_of_mem_P h hp).2 ha]⟩
  rw [miyamotoXGL_mul_self h hb, ← miyamotoXGL_zero h, miyamotoXGL_inj] at hp2
  obtain ⟨-, -, hab, htr⟩ := hp2
  have hb0 : b = 0 := (mul_eq_zero.1 hab).resolve_left ha
  subst hb0
  simp only [mul_zero, zero_add] at htr
  have hba : h.bar a ≠ 0 := by simpa using ha
  set l := c / a with hl
  have hlF : h.bar l = l := by
    rw [hl, map_div₀, div_eq_div_iff hba ha]
    linear_combination -htr + (a * h.bar c) * h2
  have hy : miyamotoXGL h 0 l 0 0 ∈ miyamotoP h := (miyamotoXGL_mem_P h).2 ⟨hlF, by simp⟩
  have hdF : h.bar d = d := by
    rw [← add_bar_eq_zero_iff h]
    linear_combination hd - htr
  refine ⟨miyamotoXGL h 0 l 0 0 * miyamotoR2 K, mul_mem (miyamotoUnipotent_le_SU h _ _ hy)
    (miyamotoR2_mem_gramSU h), ?_⟩
  have e1 : (miyamotoXGL h 0 l 0 0)⁻¹ * miyamotoXGL h a 0 c d * miyamotoXGL h 0 l 0 0 =
      miyamotoXGL h a 0 0 d := by
    rw [miyamotoXGL_conj h hlF (map_zero _), miyamotoXGL_inj]
    refine ⟨rfl, rfl, ?_, by simp⟩
    rw [hl]
    field_simp
    linear_combination c * h2
  have e2 : (miyamotoR2 K)⁻¹ * miyamotoXGL h a 0 0 d * miyamotoR2 K = miyamotoXGL h 0 0 a d := by
    apply Units.ext
    rw [show (miyamotoR2 K)⁻¹ = miyamotoR2 K from inv_eq_of_mul_eq_one_right miyamotoR2_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
  rw [_root_.mul_inv_rev, show (miyamotoR2 K)⁻¹ * (miyamotoXGL h 0 l 0 0)⁻¹ *
      miyamotoXGL h a 0 c d * (miyamotoXGL h 0 l 0 0 * miyamotoR2 K) =
      (miyamotoR2 K)⁻¹ * ((miyamotoXGL h 0 l 0 0)⁻¹ * miyamotoXGL h a 0 c d *
        miyamotoXGL h 0 l 0 0) * miyamotoR2 K by group, e1, e2]
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hdF⟩

theorem miyamoto_involutions {x : GL (Fin 4) K} (hx : x ∈ gramSU h (miyamotoJ4 K))
    (hx2 : orderOf x = 2) :
    ∃ g ∈ gramSU h (miyamotoJ4 K), g⁻¹ * x * g = miyamotoZ1 K ∨
      g⁻¹ * x * g = LocalAnalysis.miyamotoZ2 K := by
  obtain ⟨g₁, hg₁, hp⟩ := exists_conj_mem_P h hx hx2
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hp2 : g₁⁻¹ * x * g₁ * (g₁⁻¹ * x * g₁) = 1 := by
    rw [show g₁⁻¹ * x * g₁ * (g₁⁻¹ * x * g₁) = g₁⁻¹ * (x * x) * g₁ by group, hxx]
    group
  obtain ⟨g₂, hg₂, hA⟩ := exists_conj_mem_A1 h hp hp2
  set y := g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂ with hy
  have hy1 : y ≠ 1 := by
    intro e
    have : x = 1 := by
      calc x = g₁ * g₂ * y * (g₁ * g₂)⁻¹ := by rw [hy]; group
        _ = 1 := by rw [e]; group
    rw [this, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hyx : ∀ k : GL (Fin 4) K, k⁻¹ * y * k = (g₁ * g₂ * k)⁻¹ * x * (g₁ * g₂ * k) := by
    intro k
    rw [hy]
    group
  have hSU : ∀ {k : GL (Fin 4) K}, k ∈ gramSU h (miyamotoJ4 K) →
      g₁ * g₂ * k ∈ gramSU h (miyamotoJ4 K) := fun hk => mul_mem (mul_mem hg₁ hg₂) hk
  by_cases hQ : miyamotoQA1 h y = 0
  · obtain ⟨n, hn, e⟩ := exists_N1_conj_z1 h hA hy1 hQ
    refine ⟨g₁ * g₂ * n⁻¹, hSU (inv_mem (miyamotoN1_le_gramSU h hn)), Or.inl ?_⟩
    rw [← hyx, ← e, miyamotoZ1_eq h]
    group
  · have hmem : y ∈ {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h,
        g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y} := by
      rw [miyamoto_orbit_z2_I1N1 h]
      exact ⟨hA, hQ⟩
    obtain ⟨k, hk, e⟩ := hmem
    have hkS : k ∈ gramSU h (miyamotoJ4 K) :=
      sup_le (miyamotoI1_le_SU h) (miyamotoN1_le_gramSU h) hk
    refine ⟨g₁ * g₂ * k⁻¹, hSU (inv_mem hkS), Or.inr ?_⟩
    rw [← hyx, ← e]
    group

omit [CharP K 2] in
theorem miyamotoZ1_not_conj_Z2 (g : GL (Fin 4) K) :
    g⁻¹ * miyamotoZ1 K * g ≠ LocalAnalysis.miyamotoZ2 K := by
  intro e
  have e' : miyamotoZ1 K * g = g * LocalAnalysis.miyamotoZ2 K := by
    rw [← e]
    group
  have ent : ∀ i j, ((miyamotoZ1 K : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K))
      i j = ((g : Matrix (Fin 4) (Fin 4) K) * (LocalAnalysis.miyamotoZ2 K :
        Matrix (Fin 4) (Fin 4) K)) i j := fun i j => by
    rw [← Units.val_mul, ← Units.val_mul, e']
  have q02 := ent 0 0
  have q12 := ent 1 0
  have q22 := ent 2 0
  have q03 := ent 0 1
  have q13 := ent 1 1
  have q23 := ent 2 1
  simp [miyamotoZ1, LocalAnalysis.miyamotoZ2, Matrix.mul_apply, Fin.sum_univ_four] at q02 q12 q22
  simp [miyamotoZ1, LocalAnalysis.miyamotoZ2, Matrix.mul_apply, Fin.sum_univ_four] at q03 q13 q23
  have hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 0 := by
    rw [Matrix.det_succ_column _ 2]
    simp [Fin.sum_univ_succ, Matrix.det_succ_column _ 2, Fin.succAbove, q02, q12, q22, q03, q13,
      q23, Matrix.submatrix]
  exact (g.isUnit.map Matrix.detMonoidHom).ne_zero hdet

end Involutions

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

@[expose] def miyamotoZ1G : G :=
  ((η.symm ⟨miyamotoZ1 K, by have := h.charP; exact miyamotoZ1_mem_gramSU h⟩ : L) : G)

@[expose] def miyamotoZ2G : G :=
  ((η.symm ⟨LocalAnalysis.miyamotoZ2 K, by have := h.charP; exact miyamotoZ2_mem_gramSU h⟩ :
    L) : G)

theorem miyamoto_two_fourG :
    miyamotoZ1G h L η ∈ L ∧ miyamotoZ2G h L η ∈ L ∧ orderOf (miyamotoZ1G h L η) = 2 ∧
      orderOf (miyamotoZ2G h L η) = 2 ∧
      (∀ x ∈ L, orderOf x = 2 → ∃ g ∈ L, g⁻¹ * x * g = miyamotoZ1G h L η ∨
        g⁻¹ * x * g = miyamotoZ2G h L η) ∧
      ∀ g ∈ L, g⁻¹ * miyamotoZ1G h L η * g ≠ miyamotoZ2G h L η := by
  have : CharP K 2 := h.charP
  have hord : ∀ y : L, orderOf (y : G) =
      orderOf ((η y : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) := by
    intro y
    calc orderOf (y : G) = orderOf y := orderOf_injective L.subtype L.subtype_injective y
      _ = orderOf (η y) := (MulEquiv.orderOf_eq η y).symm
      _ = orderOf ((η y : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :=
        (orderOf_injective (gramSU h (miyamotoJ4 K)).subtype
          (gramSU h (miyamotoJ4 K)).subtype_injective (η y)).symm
  unfold miyamotoZ1G miyamotoZ2G
  refine ⟨(η.symm _).2, (η.symm _).2, ?_, ?_, fun x hx hx2 => ?_, fun g hg e => ?_⟩
  · rw [hord, MulEquiv.apply_symm_apply]
    exact orderOf_miyamotoZ1 h
  · rw [hord, MulEquiv.apply_symm_apply]
    exact orderOf_miyamotoZ2 h
  · have hx2' : orderOf ((η ⟨x, hx⟩ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = 2 := by
      rw [← hord]
      exact hx2
    obtain ⟨g, hg, hc⟩ := miyamoto_involutions h (η ⟨x, hx⟩).2 hx2'
    refine ⟨((η.symm ⟨g, hg⟩ : L) : G), (η.symm _).2, ?_⟩
    have key : ∀ z : gramSU h (miyamotoJ4 K),
        ((⟨g, hg⟩ : gramSU h (miyamotoJ4 K))⁻¹ * η ⟨x, hx⟩ * ⟨g, hg⟩ :
          gramSU h (miyamotoJ4 K)) = z →
        ((η.symm ⟨g, hg⟩ : L) : G)⁻¹ * x * ((η.symm ⟨g, hg⟩ : L) : G) = ((η.symm z : L) : G) := by
      intro z hz
      rw [← hz, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    rcases hc with hc | hc
    · exact Or.inl (key ⟨miyamotoZ1 K, miyamotoZ1_mem_gramSU h⟩ (Subtype.ext hc))
    · exact Or.inr (key ⟨LocalAnalysis.miyamotoZ2 K, miyamotoZ2_mem_gramSU h⟩ (Subtype.ext hc))
  · have e' : ((η ⟨g, hg⟩)⁻¹ * ⟨miyamotoZ1 K, miyamotoZ1_mem_gramSU h⟩ * η ⟨g, hg⟩ :
        gramSU h (miyamotoJ4 K)) = ⟨LocalAnalysis.miyamotoZ2 K, miyamotoZ2_mem_gramSU h⟩ := by
      apply η.symm.injective
      apply Subtype.ext
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, coe_mul, coe_inv]
      exact e
    exact miyamotoZ1_not_conj_Z2 ((η ⟨g, hg⟩ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K)
      (by simpa using congrArg Subtype.val e')

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
