module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.Uniqueness.Bender

open scoped commutatorElement

structure Frame311 (q d : ℕ) {G : Type*} [Group G] (F F₀ : Subgroup G) (t : G) : Prop where
  le : F ≤ F₀
  normal : ∀ x ∈ F₀, ∀ y ∈ F, x * y * x⁻¹ ∈ F
  comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  exp : ∀ x ∈ F, x ^ (q + 1) = 1
  card : Nat.card F * d = (q + 1) ^ 2
  iso : Nonempty (F ≃* Multiplicative (ZMod (q + 1)) × Multiplicative (ZMod ((q + 1) / d)))
  perm : ∃ π : F₀ →* Equiv.Perm (Fin 3), Function.Surjective π ∧ π.ker = F.subgroupOf F₀
  cyc : IsCyclic ↥⁅F, Subgroup.zpowers t⁆
  card_comm : Nat.card ↥⁅F, Subgroup.zpowers t⁆ = q + 1
  inv : ∀ x ∈ ⁅F, Subgroup.zpowers t⁆, t * x * t⁻¹ = x⁻¹
  card_cent : Nat.card ↥(F ⊓ Subgroup.centralizer ({t} : Set G)) * d = q + 1

theorem Frame311.map {q d : ℕ} {G G' : Type*} [Group G] [Group G'] (ψ : G ≃* G')
    {F F₀ : Subgroup G} {t : G} (h : Frame311 q d F F₀ t) :
    Frame311 q d (F.map ψ.toMonoidHom) (F₀.map ψ.toMonoidHom) (ψ t) := by
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have hmemF : ∀ x : G', x ∈ F.map ψ.toMonoidHom ↔ ψ.symm x ∈ F := fun x =>
    Subgroup.mem_map_equiv
  have hcomm : ⁅F.map ψ.toMonoidHom, Subgroup.zpowers (ψ t)⁆ =
      (⁅F, Subgroup.zpowers t⁆).map ψ.toMonoidHom := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rfl
  refine ⟨Subgroup.map_mono h.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x' * y' * x'⁻¹, h.normal x' hx' y' hy', by simp⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h.comm x' hx' y' hy']
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow, h.exp x' hx', map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact h.card
  · obtain ⟨e⟩ := h.iso
    exact ⟨(Subgroup.equivMapOfInjective F ψ.toMonoidHom hinj).symm.trans e⟩
  · obtain ⟨π, hπs, hπk⟩ := h.perm
    let e : F₀ ≃* F₀.map ψ.toMonoidHom := Subgroup.equivMapOfInjective F₀ ψ.toMonoidHom hinj
    have he : ∀ y : F₀.map ψ.toMonoidHom, ((e.symm y : F₀) : G) = ψ.symm (y : G') := by
      intro y
      apply ψ.injective
      have h1 : ((e (e.symm y) : F₀.map ψ.toMonoidHom) : G') = ψ ((e.symm y : F₀) : G) :=
        Subgroup.coe_equivMapOfInjective_apply F₀ ψ.toMonoidHom hinj _
      rw [e.apply_symm_apply] at h1
      rw [MulEquiv.apply_symm_apply, ← h1]
    refine ⟨π.comp e.symm.toMonoidHom, hπs.comp e.symm.surjective, ?_⟩
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have h1 : (π (e.symm y) = 1) ↔ e.symm y ∈ π.ker := Iff.rfl
    rw [MulEquiv.coe_toMonoidHom, h1, hπk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      hmemF, he]
  · rw [hcomm]
    exact (Subgroup.equivMapOfInjective _ ψ.toMonoidHom hinj).isCyclic.mp h.cyc
  · rw [hcomm, Subgroup.card_map_of_injective hinj]
    exact h.card_comm
  · intro x hx
    rw [hcomm] at hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have := h.inv x' hx'
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_inv]
    exact congrArg ψ this
  · have : (F.map ψ.toMonoidHom ⊓ Subgroup.centralizer ({ψ t} : Set G')) =
        (F ⊓ Subgroup.centralizer ({t} : Set G)).map ψ.toMonoidHom := by
      ext x
      constructor
      · rintro ⟨hxF, hxc⟩
        obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hxF
        have hc : ψ x' * ψ t = ψ t * ψ x' := Subgroup.mem_centralizer_singleton_iff.mp hxc
        refine ⟨x', ⟨hx', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
        apply ψ.injective
        simpa only [map_mul] using hc
      · rintro ⟨x', ⟨hx', hxc⟩, rfl⟩
        have hc : x' * t = t * x' := Subgroup.mem_centralizer_singleton_iff.mp hxc
        refine ⟨⟨x', hx', rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hc]
    rw [this, Subgroup.card_map_of_injective hinj]
    exact h.card_cent

theorem perm_fin_three_eq_one_or_eq_of_commute :
    ∀ σ τ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → σ * τ = τ * σ → σ = 1 ∨ σ = τ := by
  decide

theorem mem_of_mul_self_mem_of_odd {G : Type*} [Group G] {F : Subgroup G} {x : G}
    (hodd : Odd (orderOf x)) (hx2 : x * x ∈ F) : x ∈ F := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : x = (x * x) ^ (m + 1) := by
    have h2 : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
    calc x = x * x ^ (2 * m + 1) := by rw [h2, mul_one]
      _ = (x * x) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
  rw [h1]
  exact F.pow_mem hx2 (m + 1)

theorem Frame311.mem_of_commute_of_odd {q d : ℕ} {G : Type*} [Group G] {F F₀ : Subgroup G} {t : G}
    (h : Frame311 q d F F₀ t) (hq : 0 < q) {x : G} (hx : x ∈ F₀) (ht : t ∈ F₀) (ht2 : t * t = 1)
    (hxt : x * t = t * x) (hodd : Odd (orderOf x)) : x ∈ F := by
  obtain ⟨π, -, hπk⟩ := h.perm
  have htF : t ∉ F := by
    intro htF
    have hle : F ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      intro f hf
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgF : t ^ k ∈ F := F.zpow_mem htF k
      exact (h.comm f hf _ hgF).symm
    have hbot : ⁅F, Subgroup.zpowers t⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have hc := h.card_comm
    rw [hbot, Subgroup.card_bot] at hc
    omega
  have hπt : π ⟨t, ht⟩ ≠ 1 := by
    intro h1
    apply htF
    have : (⟨t, ht⟩ : F₀) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at this
    exact this
  have hπt2 : π ⟨t, ht⟩ * π ⟨t, ht⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, ht⟩ : F₀) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hπc : π ⟨x, hx⟩ * π ⟨t, ht⟩ = π ⟨t, ht⟩ * π ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hxt)
  have hsq : (π ⟨x, hx⟩) * (π ⟨x, hx⟩) = 1 := by
    rcases perm_fin_three_eq_one_or_eq_of_commute _ _ hπt2 hπt hπc with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hπt2]
  have hx2 : x * x ∈ F := by
    have : (⟨x, hx⟩ * ⟨x, hx⟩ : F₀) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hsq
    rw [hπk, Subgroup.mem_subgroupOf] at this
    exact this
  exact mem_of_mul_self_mem_of_odd hodd hx2

theorem Frame311.card_F₀ {q d : ℕ} {G : Type*} [Group G] {F F₀ : Subgroup G} {t : G}
    (h : Frame311 q d F F₀ t) [Finite F₀] : Nat.card F₀ = 6 * Nat.card F := by
  obtain ⟨π, hπs, hπk⟩ := h.perm
  have h1 : Nat.card (F₀ ⧸ π.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h3 : Nat.card π.ker = Nat.card F := by
    rw [hπk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  rw [h1, h3] at h2
  exact h2

end CFSG.GH74.Uniqueness.Bender
