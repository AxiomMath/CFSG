module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open scoped MatrixGroups commutatorElement

section FixTwo

theorem fix_of_pow3_two {G Y : Type*} [Group G] (act : G → Y → Y)
    (hmul : ∀ x y s, act (x * y) s = act x (act y s)) (hone : ∀ s, act 1 s = s)
    {L : Subgroup G} (hL : Q3W.Pow3 L) {s₀ s₁ : Y}
    (hmap : ∀ w ∈ L, (act w s₀ = s₀ ∧ act w s₁ = s₁) ∨ (act w s₀ = s₁ ∧ act w s₁ = s₀)) :
    ∀ w ∈ L, act w s₀ = s₀ ∧ act w s₁ = s₁ := by
  have hinv : ∀ w s, act w⁻¹ (act w s) = s := by
    intro w s
    rw [← hmul, inv_mul_cancel, hone]
  have hiT : ∀ w, act w s₀ = s₀ → act w s₁ = s₁ → act w⁻¹ s₀ = s₀ ∧ act w⁻¹ s₁ = s₁ := by
    intro w h0 h1
    exact ⟨by calc act w⁻¹ s₀ = act w⁻¹ (act w s₀) := by rw [h0]
                _ = s₀ := hinv w s₀,
           by calc act w⁻¹ s₁ = act w⁻¹ (act w s₁) := by rw [h1]
                _ = s₁ := hinv w s₁⟩
  have hiS : ∀ w, act w s₀ = s₁ → act w s₁ = s₀ → act w⁻¹ s₀ = s₁ ∧ act w⁻¹ s₁ = s₀ := by
    intro w h0 h1
    exact ⟨by calc act w⁻¹ s₀ = act w⁻¹ (act w s₁) := by rw [h1]
                _ = s₁ := hinv w s₁,
           by calc act w⁻¹ s₁ = act w⁻¹ (act w s₀) := by rw [h0]
                _ = s₀ := hinv w s₀⟩
  let N : Subgroup G :=
    { carrier := {w | act w s₀ = s₀ ∧ act w s₁ = s₁}
      mul_mem' := by
        rintro x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
        refine ⟨?_, ?_⟩
        · rw [hmul, hy0, hx0]
        · rw [hmul, hy1, hx1]
      one_mem' := ⟨hone _, hone _⟩
      inv_mem' := fun {x} hx => hiT x hx.1 hx.2 }
  have hcomm : ⁅L, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have e1 : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]
    show act ⁅x, y⁆ s₀ = s₀ ∧ act ⁅x, y⁆ s₁ = s₁
    rw [e1]
    simp only [hmul]
    rcases hmap x hx with ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩ <;>
    rcases hmap y hy with ⟨hy0, hy1⟩ | ⟨hy0, hy1⟩
    · obtain ⟨hx0', hx1'⟩ := hiT x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiT y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiT x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiS y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiS x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiT y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiS x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiS y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
  intro w hw
  have h3 : act (w ^ 3) s₀ = s₀ ∧ act (w ^ 3) s₁ = s₁ := hcomm (hL w hw)
  have hw3 : ∀ s, act (w ^ 3) s = act w (act w (act w s)) := by
    intro s
    rw [pow_three, hmul, hmul]
  rcases hmap w hw with h | ⟨h0, h1⟩
  · exact h
  · have e : s₁ = s₀ := by
      have := h3.1
      rw [hw3, h0, h1, h0] at this
      exact this
    subst e
    exact ⟨h0, h1⟩

end FixTwo

section Cubes

theorem pow3_mem_ker {G H : Type*} [Group G] [Group H] {L : Subgroup G} (hL : Q3W.Pow3 L)
    (ψ : ↥L →* H) (hψ : ∀ x y : ↥L, ψ ⁅x, y⁆ = 1) (ℓ : ↥L) : ψ ℓ ^ 3 = 1 := by
  have h1 : ⁅L, L⁆ ≤ ψ.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆, hψ _ _, rfl⟩
  obtain ⟨k, hk, hkℓ⟩ := h1 (hL ℓ ℓ.2)
  have hk' : k = ℓ ^ 3 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hkℓ)
  rw [← map_pow, ← hk']
  exact hk

end Cubes


section Inn

theorem commutator_mem_inn3 (x y : MulAut SL(2, ZMod 3)) : ⁅x, y⁆ ∈ Q3T6.inn3 := by
  have hsq : ∀ z : MulAut SL(2, ZMod 3), z * z ∈ Q3T6.inn3 := fun z =>
    Subgroup.mul_self_mem_of_index_two Q3T6.inn3_index z
  have hQ : ∀ q : MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3, q * q = 1 := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hsq z
  have hinv : ∀ q : MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3, q⁻¹ = q := fun q =>
    inv_eq_of_mul_eq_one_right (hQ q)
  have hcomm : ∀ a b : MulAut SL(2, ZMod 3) ⧸ Q3T6.inn3, a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  rw [← QuotientGroup.eq_one_iff (N := Q3T6.inn3)]
  have h := map_commutatorElement (QuotientGroup.mk' Q3T6.inn3) x y
  simp only [QuotientGroup.mk'_apply] at h
  rw [h]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)

theorem exists_inner_of_pow3 {K G : Type*} [Group K] [Group G] (e : K ≃* SL(2, ZMod 3))
    {L : Subgroup G} (hL : Q3W.Pow3 L) (ψ : ↥L →* MulAut K) (ℓ : ↥L) :
    ∃ q : K, ψ ℓ = MulAut.conj q := by
  set Ψ : ↥L →* MulAut SL(2, ZMod 3) := (MulAut.congr e).toMonoidHom.comp ψ with hΨ
  have hcube : Ψ ℓ ^ 3 ∈ Q3T6.inn3 := by
    have h1 : ⁅L, L⁆ ≤ (Q3T6.inn3.comap Ψ).map L.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      refine ⟨⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆, ?_, rfl⟩
      show Ψ ⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆ ∈ Q3T6.inn3
      rw [map_commutatorElement]
      exact commutator_mem_inn3 _ _
    obtain ⟨k, hk, hkℓ⟩ := h1 (hL ℓ ℓ.2)
    have hk' : k = ℓ ^ 3 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hkℓ)
    have h3 : Ψ (ℓ ^ 3) ∈ Q3T6.inn3 := by simpa [hk'] using hk
    rwa [map_pow] at h3
  have hmem : Ψ ℓ ∈ Q3T6.inn3 := by
    have hsq := Subgroup.mul_self_mem_of_index_two Q3T6.inn3_index (Ψ ℓ)
    have : Ψ ℓ = Ψ ℓ ^ 3 * (Ψ ℓ * Ψ ℓ)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hcube (Subgroup.inv_mem _ hsq)
  obtain ⟨g, hg⟩ := hmem
  refine ⟨e.symm g, ?_⟩
  ext k
  apply e.injective
  have h1 : MulAut.conj g (e k) = Ψ ℓ (e k) :=
    congrArg (fun φ : MulAut SL(2, ZMod 3) => φ (e k)) hg
  have h2 : Ψ ℓ (e k) = e (ψ ℓ k) := by
    show e (ψ ℓ (e.symm (e k))) = e (ψ ℓ k)
    rw [MulEquiv.symm_apply_apply]
  rw [h2] at h1
  rw [← h1]
  simp [MulAut.conj_apply, map_mul, map_inv]

end Inn

section Centralizer

theorem sl2Three_sq_cases : ∀ a q : SL(2, ZMod 3), a * a = -1 → q * a = a * q →
    q * q = 1 ∨ q * q = -1 := by
  decide +kernel

end Centralizer

end CFSG.ClassicalInvolution.Q3.Q3T7S23
