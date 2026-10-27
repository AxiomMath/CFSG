module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Quaternion

open QuaternionGroup

theorem inv_a' {n : ℕ} (i : ZMod (2 * n)) : (a i : QuaternionGroup n)⁻¹ = a (-i) :=
  inv_eq_of_mul_eq_one_right (by rw [a_mul_a, add_neg_cancel, a_zero])

theorem inv_xa' {n : ℕ} (i : ZMod (2 * n)) :
    (xa i : QuaternionGroup n)⁻¹ = xa ((n : ZMod (2 * n)) + i) :=
  inv_eq_of_mul_eq_one_right (by
    rw [xa_mul_xa]
    have : (n : ZMod (2 * n)) + ((n : ZMod (2 * n)) + i) - i = (2 * n : ℕ) := by
      push_cast; ring
    rw [this, ZMod.natCast_self, a_zero])

theorem exists_inv_of_quaternion (n m : ℕ) (hm : n = 2 * m) (x : QuaternionGroup n) :
    ∃ j : QuaternionGroup n, j * x * j⁻¹ = x⁻¹ ∧ j * j = a (n : ZMod (2 * n)) := by
  have h2m : ((n : ℕ) : ZMod (2 * n)) + ((n : ℕ) : ZMod (2 * n)) = 0 := by
    rw [← Nat.cast_add]
    have : n + n = 2 * n := by ring
    rw [this]
    exact ZMod.natCast_self _
  have hnm : (n : ZMod (2 * n)) = 2 * (m : ZMod (2 * n)) := by
    rw [hm]; push_cast; ring
  cases x with
  | a i =>
    refine ⟨xa 0, ?_, ?_⟩
    · rw [xa_mul_a, inv_xa', xa_mul_xa, inv_a']
      congr 1
      linear_combination h2m
    · rw [xa_mul_xa]
      congr 1
      ring
  | xa i =>
    refine ⟨a (m : ZMod (2 * n)), ?_, ?_⟩
    · rw [a_mul_xa, inv_a', xa_mul_a, inv_xa']
      congr 1
      rw [hnm] at h2m ⊢
      linear_combination -h2m
    · rw [a_mul_a]
      congr 1
      rw [hnm]
      ring

theorem a_n_ne_one {n : ℕ} (hn : n ≠ 0) : (a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
  intro h
  rw [one_def] at h
  have h1 : (n : ZMod (2 * n)) = 0 := a.inj h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
  omega

theorem a_n_mul_self {n : ℕ} : (a (n : ZMod (2 * n)) : QuaternionGroup n) *
    a (n : ZMod (2 * n)) = 1 := by
  rw [a_mul_a, ← Nat.cast_add, show n + n = 2 * n by ring, ZMod.natCast_self, a_zero]

end Quaternion

section Group

variable {G : Type} [Group G]

theorem isQuatSub_exists_inv {R : Subgroup G} (h : IsQuatSub R) {u : G} (hu : u ∈ R) :
    ∃ j ∈ R, j * u * j⁻¹ = u⁻¹ ∧ j * j ≠ 1 ∧ (j * j) * (j * j) = 1 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hn : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by ring
  obtain ⟨j, hj1, hj2⟩ := exists_inv_of_quaternion (2 ^ (k' + 1)) (2 ^ k') hn (e ⟨u, hu⟩)
  refine ⟨((e.symm j : ↥R) : G), (e.symm j).2, ?_, ?_, ?_⟩
  · have h1 : e.symm j * ⟨u, hu⟩ * (e.symm j)⁻¹ = ⟨u, hu⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hj1]
    have := congrArg (fun t : ↥R => (t : G)) h1
    simpa using this
  · intro h1
    have h2 : e.symm j * e.symm j = 1 := Subtype.ext h1
    rw [← map_mul, hj2] at h2
    have : (QuaternionGroup.a ((2 ^ (k' + 1) : ℕ) : ZMod (2 * 2 ^ (k' + 1))) :
          QuaternionGroup (2 ^ (k' + 1))) =
        1 := e.symm.injective (by rw [h2, map_one])
    exact a_n_ne_one (by positivity) this
  · have h2 : (e.symm j * e.symm j) * (e.symm j * e.symm j) = 1 := by
      rw [← map_mul, hj2, ← map_mul, a_n_mul_self, map_one]
    have := congrArg (fun t : ↥R => (t : G)) h2
    simpa using this

end Group

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_invert (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ (R R' R₃ : Subgroup G) (j₁ j₂ : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧
      IsSylow2In R₃ K₃ ∧ u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧
      Commutes R' R₃ ∧ j₁ ∈ R ∧ j₂ ∈ R' ∧ j₁ * u₁ * j₁⁻¹ = u₁⁻¹ ∧ j₂ * u₂ * j₂⁻¹ = u₂⁻¹ ∧
      j₁ * j₁ = z ∧ j₂ * j₂ = z := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := T7J.exists_sylow_triple h
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hqR : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.stand.mem hR)
  have hqR' : IsQuatSub R' :=
    hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.hK'.1 hR')
  obtain ⟨j₁, hj₁, e₁, n₁, s₁⟩ := isQuatSub_exists_inv hqR h₁
  obtain ⟨j₂, hj₂, e₂, n₂, s₂⟩ := isQuatSub_exists_inv hqR' h₂
  have hz₁ : j₁ * j₁ = z := by
    rcases h.hz.unique (j₁ * j₁) (K.mul_mem (hR.1 hj₁) (hR.1 hj₁)) s₁ with h1 | h1
    · exact absurd h1 n₁
    · exact h1
  have hz₂ : j₂ * j₂ = z := by
    rcases h.hzK'.unique (j₂ * j₂) (K'.mul_mem (hR'.1 hj₂) (hR'.1 hj₂)) s₂ with h1 | h1
    · exact absurd h1 n₂
    · exact h1
  exact ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23, hj₁, hj₂, e₁, e₂, hz₁, hz₂⟩

end Datum

section Elt

variable {G : Type} [Group G] {z u₁ u₂ j₁ j₂ : G} {R R' R₃ : Subgroup G}

structure InvData (z u₁ u₂ j₁ j₂ : G) (R R' R₃ : Subgroup G) : Prop where
  z2 : z * z = 1
  s₁ : u₁ * u₁ = z
  s₂ : u₂ * u₂ = z
  u₁R : u₁ ∈ R
  u₂R : u₂ ∈ R'
  j₁R : j₁ ∈ R
  j₂R : j₂ ∈ R'
  c₁₂ : Commutes R R'
  c₁₃ : Commutes R R₃
  c₂₃ : Commutes R' R₃
  inv₁ : j₁ * u₁ * j₁⁻¹ = u₁⁻¹
  inv₂ : j₂ * u₂ * j₂⁻¹ = u₂⁻¹
  sq₁ : j₁ * j₁ = z
  sq₂ : j₂ * j₂ = z

omit [Group G] in
theorem inv_eq_mul_of_sq {G : Type} [Group G] {u z : G} (h : u * u = z) (hz : z * z = 1) :
    u⁻¹ = u * z :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h, hz])

namespace InvData

variable (d : InvData z u₁ u₂ j₁ j₂ R R' R₃)
include d

theorem comm_j₁j₂ : j₁ * j₂ = j₂ * j₁ := d.c₁₂ j₁ d.j₁R j₂ d.j₂R

theorem comm_j₁u₂ : j₁ * u₂ = u₂ * j₁ := d.c₁₂ j₁ d.j₁R u₂ d.u₂R

theorem comm_j₂u₁ : j₂ * u₁ = u₁ * j₂ := (d.c₁₂ u₁ d.u₁R j₂ d.j₂R).symm

theorem comm_u₁u₂ : u₁ * u₂ = u₂ * u₁ := d.c₁₂ u₁ d.u₁R u₂ d.u₂R

theorem comm_zu₂ : z * u₂ = u₂ * z := by
  rw [← d.s₂]; group

theorem sq_v : (j₁ * j₂) * (j₁ * j₂) = 1 := by
  calc (j₁ * j₂) * (j₁ * j₂) = j₁ * (j₂ * j₁) * j₂ := by group
    _ = j₁ * (j₁ * j₂) * j₂ := by rw [← d.comm_j₁j₂]
    _ = (j₁ * j₁) * (j₂ * j₂) := by group
    _ = 1 := by rw [d.sq₁, d.sq₂, d.z2]

theorem comm_j₁u₂_inv : j₁ * u₂⁻¹ = u₂⁻¹ * j₁ := by
  have := d.comm_j₁u₂
  calc j₁ * u₂⁻¹ = u₂⁻¹ * (u₂ * j₁) * u₂⁻¹ := by group
    _ = u₂⁻¹ * (j₁ * u₂) * u₂⁻¹ := by rw [this]
    _ = u₂⁻¹ * j₁ := by group

theorem j₁u₁ : j₁ * u₁ = u₁⁻¹ * j₁ := by
  have := d.inv₁
  calc j₁ * u₁ = (j₁ * u₁ * j₁⁻¹) * j₁ := by group
    _ = u₁⁻¹ * j₁ := by rw [this]

theorem j₂u₂ : j₂ * u₂ = u₂⁻¹ * j₂ := by
  have := d.inv₂
  calc j₂ * u₂ = (j₂ * u₂ * j₂⁻¹) * j₂ := by group
    _ = u₂⁻¹ * j₂ := by rw [this]

theorem inv_mul_inv : u₁⁻¹ * u₂⁻¹ = u₁ * u₂ := by
  rw [inv_eq_mul_of_sq d.s₁ d.z2, inv_eq_mul_of_sq d.s₂ d.z2]
  calc u₁ * z * (u₂ * z) = u₁ * (z * u₂) * z := by group
    _ = u₁ * (u₂ * z) * z := by rw [d.comm_zu₂]
    _ = (u₁ * u₂) * (z * z) := by group
    _ = u₁ * u₂ := by rw [d.z2, mul_one]

theorem v_comm_u : (j₁ * j₂) * (u₁ * u₂) = (u₁ * u₂) * (j₁ * j₂) := by
  calc (j₁ * j₂) * (u₁ * u₂) = j₁ * (j₂ * u₁) * u₂ := by group
    _ = j₁ * (u₁ * j₂) * u₂ := by rw [d.comm_j₂u₁]
    _ = (j₁ * u₁) * (j₂ * u₂) := by group
    _ = (u₁⁻¹ * j₁) * (u₂⁻¹ * j₂) := by rw [d.j₁u₁, d.j₂u₂]
    _ = u₁⁻¹ * (j₁ * u₂⁻¹) * j₂ := by group
    _ = u₁⁻¹ * (u₂⁻¹ * j₁) * j₂ := by rw [d.comm_j₁u₂_inv]
    _ = (u₁⁻¹ * u₂⁻¹) * (j₁ * j₂) := by group
    _ = (u₁ * u₂) * (j₁ * j₂) := by rw [d.inv_mul_inv]

theorem v_inv_u₂ : (j₁ * j₂) * u₂ * (j₁ * j₂)⁻¹ = u₂⁻¹ := by
  calc (j₁ * j₂) * u₂ * (j₁ * j₂)⁻¹ = j₁ * (j₂ * u₂ * j₂⁻¹) * j₁⁻¹ := by group
    _ = j₁ * u₂⁻¹ * j₁⁻¹ := by rw [d.inv₂]
    _ = u₂⁻¹ := by rw [d.comm_j₁u₂_inv]; group

end InvData

end Elt

end S16

end CFSG.ClassicalInvolution.Asc77
