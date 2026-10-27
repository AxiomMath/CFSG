module

public import CFSG.LargeExtraspecial.AS35CHyp

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

structure W2Data (X : Type) [Group X] (z : X) : Prop where
  orderOf_eq : orderOf z = 2
  sylow_le : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ centralizer ({z} : Set X)
  card_dvd : Nat.card (centralizer ({z} : Set X)) ∣ 2 ^ 8 * 3 ^ 2 * 5
  weaklyClosed : ∀ x ∈ oTwoCent z, IsConj z x → x = z
  mem_oTwoCent : ∀ t ∈ oTwoCent z, orderOf t = 2 → z ∈ oTwoCent t
  selfCentralizing : ∀ c ∈ centralizer ({z} : Set X), (∀ r ∈ oTwoCent z, c * r = r * c) →
    c ∈ oTwoCent z
  sq_eq : ∀ r ∈ oTwoCent z, r ^ 2 = 1 ∨ r ^ 2 = z
  aut : ∃ A : Subgroup (MulAut X), Nat.card A = 32 ∧ (∀ a ∈ A, a z = z) ∧
    ∀ x : X, MulAut.conj x ∈ A → x ∈ oTwoCent z

@[expose] def W2Concl (X : Type) [Group X] (z : X) : Prop :=
  ∀ g₁ g₂ : X, orderOf (g₁ * z * g₁⁻¹ * (g₂ * z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)

@[expose] def W2Good (X : Type) [Group X] : Prop :=
  ∀ z : X, W2Data X z → W2Concl X z

variable {X Y : Type} [Group X] [Group Y]

theorem centralizer_map (e : X ≃* Y) (z : X) :
    centralizer ({e z} : Set Y) = (centralizer ({z} : Set X)).map e.toMonoidHom := by
  ext y
  simp only [mem_centralizer_singleton_iff, mem_map]
  constructor
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    simp [map_mul, h]
  · rintro ⟨x, hx, rfl⟩
    simp [← map_mul, hx]

theorem mem_centralizer_map_iff (e : X ≃* Y) {z : X} {y : Y} :
    y ∈ centralizer ({e z} : Set Y) ↔ e.symm y ∈ centralizer ({z} : Set X) := by
  rw [centralizer_map e z]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨e.symm y, h, by simp⟩

theorem map_oTwoCent_le (e : X ≃* Y) (z : X) :
    (oTwoCent z).map e.toMonoidHom ≤ oTwoCent (e z) := by
  refine le_oTwoCent ?_ ?_ ((isPGroup_oTwoCent z).map _)
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_map_iff]
    simpa using oTwoCent_le_centralizer z hx
  · rintro c hc _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_map_iff] at hc
    refine ⟨e.symm c * p * (e.symm c)⁻¹, conj_mem_oTwoCent hc hp, ?_⟩
    simp

theorem mem_oTwoCent_map_iff (e : X ≃* Y) {z : X} {y : Y} :
    y ∈ oTwoCent (e z) ↔ e.symm y ∈ oTwoCent z := by
  constructor
  · intro hy
    have h := map_oTwoCent_le e.symm (e z) ⟨y, hy, rfl⟩
    simpa using h
  · intro hy
    exact map_oTwoCent_le e z ⟨e.symm y, hy, by simp⟩

theorem isConj_map_iff (e : X ≃* Y) {a b : X} : IsConj (e a) (e b) ↔ IsConj a b := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, e.injective ?_⟩
    simp [map_mul, hc]
  · rintro ⟨c, rfl⟩
    exact ⟨e c, by simp [map_mul]⟩

theorem W2Data.map [Finite X] (e : X ≃* Y) {z : X} (h : W2Data X z) : W2Data Y (e z) where
  orderOf_eq := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq
  sylow_le := by
    obtain ⟨P, hP⟩ := h.sylow_le
    have hs : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨P.mapSurjective hs, ?_⟩
    rw [Sylow.coe_mapSurjective, centralizer_map e z]
    exact Subgroup.map_mono hP
  card_dvd := by
    rw [centralizer_map e z, Subgroup.card_map_of_injective e.injective]
    exact h.card_dvd
  weaklyClosed := by
    intro x hx hc
    rw [mem_oTwoCent_map_iff] at hx
    have hc' : IsConj z (e.symm x) := by
      rw [← isConj_map_iff e]
      simpa using hc
    have := h.weaklyClosed _ hx hc'
    rw [← this]
    simp
  mem_oTwoCent := by
    intro t ht ht2
    rw [mem_oTwoCent_map_iff] at ht
    have h1 := h.mem_oTwoCent _ ht (by rw [← ht2, ← MulEquiv.orderOf_eq e]; simp)
    have h2 := map_oTwoCent_le e (e.symm t) ⟨z, h1, rfl⟩
    simpa using h2
  selfCentralizing := by
    intro c hc hcr
    rw [mem_centralizer_map_iff] at hc
    rw [mem_oTwoCent_map_iff]
    refine h.selfCentralizing _ hc fun r hr => e.injective ?_
    have := hcr (e r) ((mem_oTwoCent_map_iff e).2 (by simpa using hr))
    simpa [map_mul] using this
  sq_eq := by
    intro r hr
    rw [mem_oTwoCent_map_iff] at hr
    rcases h.sq_eq _ hr with h1 | h1
    · left
      apply e.symm.injective
      simpa [map_pow] using h1
    · right
      apply e.symm.injective
      simpa [map_pow] using h1
  aut := by
    obtain ⟨A, hA, hAz, hAc⟩ := h.aut
    refine ⟨A.map (MulAut.congr e).toMonoidHom, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hA]
    · rintro _ ⟨a, ha, rfl⟩
      simp [MulAut.congr_apply, hAz a ha]
    · rintro y ⟨a, ha, hay⟩
      rw [mem_oTwoCent_map_iff]
      refine hAc _ ?_
      have : a = MulAut.conj (e.symm y) := by
        ext x
        have := congrArg (fun φ : MulAut Y => φ (e x)) hay
        simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
        apply e.injective
        simpa [map_mul] using this
      exact this ▸ ha

theorem W2Concl.of_map (e : X ≃* Y) {z : X} (h : W2Concl Y (e z)) : W2Concl X z := by
  intro g₁ g₂
  have : orderOf (e (g₁ * z * g₁⁻¹ * (g₂ * z * g₂⁻¹))) ∈ ({1, 2, 3} : Set ℕ) := by
    simpa [map_mul, map_inv] using h (e g₁) (e g₂)
  rwa [MulEquiv.orderOf_eq] at this

theorem W2Good.of_mulEquiv [Finite X] (e : X ≃* Y) (h : W2Good Y) : W2Good X :=
  fun _ hz => W2Concl.of_map e (h _ (hz.map e))

end AS35W

end CFSG.LargeExtraspecial
