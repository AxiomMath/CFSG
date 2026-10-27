module

public import CFSG.LargeExtraspecial.AS35ZSOr
import all CFSG.Fischer.F4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

theorem eq_one_of_cube_of_finrank {c : V ≃ₗ[ZMod 2] V} (hc : ∀ v, c (c (c v)) = v)
    (hdim : finrank (ZMod 2) V ≤ finrank (ZMod 2) (fixSpace c) + 1) : c = 1 := by
  rw [← A2Mod.commSpace_eq_bot_iff]
  have hsum := finrank_commSpace_add_finrank_fixSpace c
  have h1 : finrank (ZMod 2) (commSpace c) ≤ 1 := by omega
  by_contra hne
  have h1' : finrank (ZMod 2) (commSpace c) = 1 :=
    le_antisymm h1 (Submodule.one_le_finrank_iff.2 hne)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h1' hw hw0
  have hcw : c w ∈ commSpace c := apply_mem_commSpace_of_commute rfl hw
  rw [hspan, Submodule.mem_span_singleton] at hcw
  obtain ⟨t, ht⟩ := hcw
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at ht
    exact hw0 ht
  · rw [one_smul] at ht
    exact hw0 (fixed_eq_zero_of_cube hc hw ht.symm)

theorem K_cases' (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω * ω := by
  obtain ⟨c₄, rfl⟩ := eF4.surjective c
  have h : ∀ c : CFSG.Fischer.F4, c = 0 ∨ c = 1 ∨ c = CFSG.Fischer.F4.ω ∨
      c = CFSG.Fischer.F4.ω * CFSG.Fischer.F4.ω := by decide
  rcases h c₄ with rfl | rfl | rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl (map_one _))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

theorem omega_cube : ω * ω * ω = (1 : K) := by
  have := frob_mul_self omega_ne_zero
  rw [frob_omega] at this
  have e2 : ω * ω = ω + 1 := by rw [← frob_omega, frob_apply, _root_.sq]
  linear_combination ω * e2 + this

theorem pow_four_eq {G : Type*} [Group G] {g : G} (hg3 : g ^ 3 = 1) : g ^ 2 * g ^ 2 = g := by
  rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, hg3, one_mul, pow_one]

namespace ZSHyp

variable (h : ZSHyp n q ρ)
include h

theorem apply_eq_self_of_cube (H₀ : ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, oLine ρ x.1 a = a)
    {g : SUid frob n} (hg3 : g ^ 3 = 1) {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    {μ : K} (hμ : μ ≠ 0) (hgx : g • x = μ • x) {a : V} (ha : a ∈ lineA ρ x) :
    rs ρ g a = a := by
  have hsq : ∀ {s : SUid frob n}, s ^ 3 = 1 → (∀ b ∈ lineA ρ x, rs ρ (s ^ 2) b = b) →
      rs ρ s a = a := fun {s} hs3 h2 => by
    have hmem : rs ρ (s ^ 2) a ∈ lineA ρ x := by rw [h2 a ha]; exact ha
    rw [← pow_four_eq hs3, map_mul, LinearEquiv.mul_apply, h2 a ha, h2 a ha]
  have hω : ∀ {s : SUid frob n}, s ^ 3 = 1 → s • x = ω • x → ∀ b ∈ lineA ρ x, rs ρ s b = b :=
    fun {s} hs3 hsx b hb => by
      rw [h.apply_eq_oLine hx0 hx hs3 hsx hb]
      exact H₀ ⟨x, hx0, hx⟩ b hb
  rcases K_cases' μ with rfl | rfl | rfl | rfl
  · exact absurd rfl hμ
  · rw [one_smul] at hgx
    exact hsq hg3 fun b hb => h.sq_apply_eq_self_of_fix hx0 hx hgx hb
  · exact hω hg3 hgx a ha
  · refine hsq hg3 fun b hb => hω ?_ ?_ b hb
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hg3, one_pow]
    · rw [_root_.sq, mul_smul, hgx, smul_comm, hgx, smul_smul]
      congr 1
      have := omega_cube
      linear_combination (ω : K) * this

end ZSHyp

noncomputable abbrev pp (i j : Fin n) (c : K) : Fin n → K := Pi.single i 1 + Pi.single j c

theorem pp_iso {i j : Fin n} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    herm frob (pp i j c) (pp i j c) = 0 :=
  isotropic_single_add_single hij hc

theorem pp_ne_zero {i j : Fin n} (hij : i ≠ j) (c : K) : pp i j c ≠ 0 := by
  intro h0
  have := congrFun h0 i
  simp [pp, hij] at this

theorem herm_pp (i j k l : Fin n) (c d : K) :
    herm frob (pp i j c) (pp k l d) = pp k l d i + frob c * pp k l d j :=
  herm_single_add_single_left i j c _

theorem herm_pp_one_omega {i j : Fin n} (hij : i ≠ j) : herm frob (pp i j 1) (pp i j ω) ≠ 0 := by
  rw [herm_pp]
  simp only [pp, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
    Pi.single_eq_of_ne hij.symm, add_zero, zero_add, map_one, one_mul]
  intro h0
  apply omega_ne_one
  linear_combination h0 - two_eq_zero

theorem herm_pp_disj {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (c d : K) : herm frob (pp i j c) (pp k l d) = 0 := by
  rw [herm_pp]
  simp [pp, hik, hil, hjk, hjl]

noncomputable abbrev blk (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (i j : Fin n) : Submodule (ZMod 2) V :=
  lineA ρ (pp i j 1) ⊔ lineA ρ (pp i j ω)

omit [FiniteDimensional (ZMod 2) V] in
theorem le_orth_of_polar {W₁ W₂ : Submodule (ZMod 2) V}
    (h0 : ∀ v ∈ W₁, ∀ w ∈ W₂, polar q v w = 0) :
    W₁ ≤ LinearMap.BilinForm.orthogonal (polarBilin q) W₂ := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  show polar q w v = 0
  rw [polar_comm]
  exact h0 v hv w hw

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_sup_sup {A₁ A₂ B₁ B₂ : Submodule (ZMod 2) V}
    (h0 : ∀ A ∈ ({A₁, A₂} : Set _), ∀ B ∈ ({B₁, B₂} : Set _), ∀ v ∈ A, ∀ w ∈ B,
      polar q v w = 0) : ∀ v ∈ A₁ ⊔ A₂, ∀ w ∈ B₁ ⊔ B₂, polar q v w = 0 := by
  intro v hv w hw
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.1 hw
  rw [polar_add_left, polar_add_right, polar_add_right,
    h0 A₁ (by simp) B₁ (by simp) a₁ ha₁ b₁ hb₁, h0 A₁ (by simp) B₂ (by simp) a₁ ha₁ b₂ hb₂,
    h0 A₂ (by simp) B₁ (by simp) a₂ ha₂ b₁ hb₁, h0 A₂ (by simp) B₂ (by simp) a₂ ha₂ b₂ hb₂]
  simp

namespace ZSHyp

variable (h : ZSHyp n q ρ)
include h

theorem finrank_blk {i j : Fin n} (hij : i ≠ j) : finrank (ZMod 2) (blk ρ i j) = 4 :=
  h.finrank_sup_lineA (pp_ne_zero hij 1) (pp_iso hij one_ne_zero) (pp_ne_zero hij ω)
    (pp_iso hij omega_ne_zero) (herm_pp_one_omega hij)

theorem nondeg_blk {i j : Fin n} (hij : i ≠ j) :
    blk ρ i j ⊓ LinearMap.BilinForm.orthogonal (polarBilin q) (blk ρ i j) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [Submodule.mem_bot]
  refine h.eq_zero_of_polar_sup (pp_ne_zero hij 1) (pp_iso hij one_ne_zero) (pp_ne_zero hij ω)
    (pp_iso hij omega_ne_zero) (herm_pp_one_omega hij) hv1 fun w hw => ?_
  have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hv2) w hw
  rw [polar_comm]
  exact this

theorem blk_le_orth {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    blk ρ k l ≤ LinearMap.BilinForm.orthogonal (polarBilin q) (blk ρ i j) := by
  refine le_orth_of_polar (polar_sup_sup ?_)
  rintro A (rfl | rfl) B (rfl | rfl) v hv w hw <;>
    exact h.polar_eq_zero_of_perp (pp_ne_zero hkl _)
      (pp_iso hkl (by first | exact one_ne_zero | exact omega_ne_zero)) (pp_ne_zero hij _)
      (pp_iso hij (by first | exact one_ne_zero | exact omega_ne_zero))
      (herm_pp_disj hik.symm hjk.symm hil.symm hjl.symm _ _) hv hw

theorem blk_apply_eq_self (H₀ : ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, oLine ρ x.1 a = a)
    {i j : Fin n} (hij : i ≠ j) {g : SUid frob n} (hg3 : g ^ 3 = 1) {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ c : K, g • pp i j c = μ • pp i j c) {v : V} (hv : v ∈ blk ρ i j) :
    rs ρ g v = v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, h.apply_eq_self_of_cube H₀ hg3 (pp_ne_zero hij 1) (pp_iso hij one_ne_zero) hμ
    (hg 1) ha, h.apply_eq_self_of_cube H₀ hg3 (pp_ne_zero hij ω) (pp_iso hij omega_ne_zero) hμ
    (hg ω) hb]

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
