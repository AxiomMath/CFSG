module

public import CFSG.GH74.GLS.Stage4.T6W.T6HInv

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6W

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem a_normH {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {x : G} (hx : x ∈ N.H) :
    N.a⁻¹ * x * N.a ∈ N.H ∧ N.a * x * N.a⁻¹ ∈ N.H := by
  have ha := Subgroup.mem_normalizer_iff.1 h.sec5.weyl.a_normH
  refine ⟨?_, (ha x).1 hx⟩
  rw [ha (N.a⁻¹ * x * N.a)]
  have : N.a * (N.a⁻¹ * x * N.a) * N.a⁻¹ = x := by group
  rw [this]
  exact hx

theorem RA_struct {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) (hm₁ : ∃ m : ℕ, N.q₁ = p ^ m) :
    (Nat.card ↥(RA N p u) = 1 ∨ Nat.card ↥(RA N p u) = N.q₁ ∨ Nat.card ↥(RA N p u) = N.q₂ ∨
      Nat.card ↥(RA N p u) = N.q₁ * N.q₂) ∧ ∀ r ∈ RA N p u, r ^ p = 1 := by
  set A' : Subgroup G := (RA N p u).map (MulAut.conj N.a).toMonoidHom with hA'
  have hmem : ∀ y, y ∈ A' ↔ ∃ r ∈ RA N p u, N.a * r * N.a⁻¹ = y := by
    intro y
    simp [hA', Subgroup.mem_map]
  have hAK : A' ≤ N.K₁ ⊔ N.K₂ := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (hmem y).1 hy
    exact RA_conj_K h hr
  have hAp : IsPGroup p ↥A' := (RA_pGroup h).map _
  have hAab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hmem x).1 hx
    obtain ⟨s, hs, rfl⟩ := (hmem y).1 hy
    have := (RA_inv h).2 r hr s hs
    calc N.a * r * N.a⁻¹ * (N.a * s * N.a⁻¹) = N.a * (r * s) * N.a⁻¹ := by group
      _ = N.a * (s * r) * N.a⁻¹ := by rw [this]
      _ = N.a * s * N.a⁻¹ * (N.a * r * N.a⁻¹) := by group
  have hAH : ∀ x ∈ N.H, ∀ y ∈ A', x * y * x⁻¹ ∈ A' := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hmem y).1 hy
    obtain ⟨hx1, -⟩ := a_normH h hx
    refine (hmem _).2 ⟨(N.a⁻¹ * x * N.a) * r * (N.a⁻¹ * x * N.a)⁻¹, RA_H h hx1 hr, ?_⟩
    group
  obtain ⟨A₁, A₂, hA₁K, hA₂K, hAeq, hcard, hc₁, hc₂, he₁, he₂⟩ := t6_hinv h hm₁ hAK hAp hAab hAH
  have hcardA : Nat.card ↥A' = Nat.card ↥(RA N p u) :=
    Subgroup.card_map_of_injective (MulAut.conj N.a).injective
  refine ⟨?_, ?_⟩
  · rw [← hcardA, hcard]
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2 <;> simp [h1, h2]
  · intro r hr
    have hy : N.a * r * N.a⁻¹ ∈ A' := (hmem _).2 ⟨r, hr, rfl⟩
    rw [hAeq] at hy
    have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy =>
      h.sec5.loc.K_comm x (hA₁K hx) y (hA₂K hy)
    obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := (mem_sup_iff_of_comm hcomm _).1 hy
    have hc12 : Commute x₁ x₂ := hcomm x₁ hx₁ x₂ hx₂
    have h1 : (N.a * r * N.a⁻¹) ^ p = 1 := by
      rw [hx, hc12.mul_pow, he₁ x₁ hx₁, he₂ x₂ hx₂, one_mul]
    have h2 : (N.a * r * N.a⁻¹) ^ p = N.a * r ^ p * N.a⁻¹ := by
      simp
    rw [h2] at h1
    have : r ^ p = N.a⁻¹ * (N.a * r ^ p * N.a⁻¹) * N.a := by group
    rw [this, h1]; group

theorem RB_conj {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {b : G} (hb : b ∈ RB N p u) :
    N.w₁⁻¹ * b * N.w₁ ∈ RA N p u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hw₁K : N.w₁ ∈ N.K₁ := h.sec5.loc.w₁_mem
  have hw₁M : N.w₁ ∈ M₂ N := K₁_le_M₂ h hw₁K
  have hw₁z : N.w₁ * N.z = N.z * N.w₁ := h.ctx.C.zc₁ N.w₁ hw₁K
  have hw₁u : N.w₁ * u * N.w₁⁻¹ = N.z * u := by rw [h.sec5.loc.w₁_u, hzu]
  have hconj : N.w₁⁻¹ * (N.z * u) * N.w₁ = u := by
    calc N.w₁⁻¹ * (N.z * u) * N.w₁ = N.w₁⁻¹ * (N.w₁ * u * N.w₁⁻¹) * N.w₁ := by rw [hw₁u]
      _ = u := by group
  refine ⟨by simpa using R₂_norm N p ((M₂ N).inv_mem hw₁M) hb.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hbc : b * (N.z * u) = (N.z * u) * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
  show N.w₁⁻¹ * b * N.w₁ * u = u * (N.w₁⁻¹ * b * N.w₁)
  calc N.w₁⁻¹ * b * N.w₁ * u = N.w₁⁻¹ * b * N.w₁ * (N.w₁⁻¹ * (N.z * u) * N.w₁) := by rw [hconj]
    _ = N.w₁⁻¹ * (b * (N.z * u)) * N.w₁ := by group
    _ = N.w₁⁻¹ * ((N.z * u) * b) * N.w₁ := by rw [hbc]
    _ = (N.w₁⁻¹ * (N.z * u) * N.w₁) * (N.w₁⁻¹ * b * N.w₁) := by group
    _ = u * (N.w₁⁻¹ * b * N.w₁) := by rw [hconj]

theorem RB_exp {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) (hm₁ : ∃ m : ℕ, N.q₁ = p ^ m) :
    ∀ b ∈ RB N p u, b ^ p = 1 := by
  intro b hb
  have h1 := (RA_struct h hm₁).2 _ (RB_conj h hb)
  have h2 : (N.w₁⁻¹ * b * N.w₁) ^ p = N.w₁⁻¹ * b ^ p * N.w₁ := by
    simpa using (conj_pow : (N.w₁⁻¹ * b * N.w₁⁻¹⁻¹) ^ p = N.w₁⁻¹ * b ^ p * N.w₁⁻¹⁻¹)
  rw [h2] at h1
  have : b ^ p = N.w₁ * (N.w₁⁻¹ * b ^ p * N.w₁) * N.w₁⁻¹ := by group
  rw [this, h1]; group

theorem R₂_exp {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) (hm₁ : ∃ m : ℕ, N.q₁ = p ^ m) :
    ∀ r ∈ R₂ N p, r ^ p ∈ N.X₂ := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have hXc : ∀ x ∈ N.X₂, ∀ r ∈ R₂ N p, x * r = r * x := by
    intro x hx r hr
    have := R₂_cent h r hr x hx
    calc x * r = (r * x * r⁻¹) * r := by rw [this]
      _ = r * x := by group
  have hcomm := (R₂_inv_comm h).2
  let Ω : Subgroup G :=
    { carrier := {r | r ∈ R₂ N p ∧ r ^ p ∈ N.X₂}
      mul_mem' := by
        rintro a b ⟨haR, hap⟩ ⟨hbR, hbp⟩
        obtain ⟨x, hx, hxe⟩ := t6_pow_mul hXc hcomm haR hbR p
        refine ⟨(R₂ N p).mul_mem haR hbR, ?_⟩
        rw [hxe]
        exact N.X₂.mul_mem (N.X₂.mul_mem hap hbp) hx
      one_mem' := ⟨(R₂ N p).one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haR, hap⟩
        refine ⟨(R₂ N p).inv_mem haR, ?_⟩
        rw [inv_pow]
        exact N.X₂.inv_mem hap }
  have hΩR : Ω ≤ R₂ N p := fun r hr => hr.1
  have hXΩ : N.X₂ ≤ Ω := fun x hx => ⟨X₂_le_R₂ h hx, N.X₂.pow_mem hx p⟩
  have hΩU : ∀ g ∈ t2U N.z u, ∀ k ∈ Ω, g * k * g⁻¹ ∈ Ω := by
    intro g hg k hk
    refine ⟨R₂_norm N p (U_le_M₂ h hg) hk.1, ?_⟩
    have : (g * k * g⁻¹) ^ p = g * k ^ p * g⁻¹ := by simp
    rw [this]
    exact (Subgroup.mem_normalizer_iff.1 (U_le_M₂ h hg) _).1 hk.2
  have hRA : RA N p u ≤ Ω := fun r hr => ⟨hr.1, by rw [(RA_struct h hm₁).2 r hr]; exact N.X₂.one_mem⟩
  have hRB : RB N p u ≤ Ω := fun r hr => ⟨hr.1, by rw [RB_exp h hm₁ r hr]; exact N.X₂.one_mem⟩
  have h1 := card_four_decomp h hXΩ hΩR hΩU
  have h2 := R₂_card_eq h
  have e1 : Ω ⊓ Subgroup.centralizer {u} = RA N p u :=
    le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hRA hx, hx.2⟩)
  have e2 : Ω ⊓ Subgroup.centralizer {N.z * u} = RB N p u :=
    le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hRB hx, hx.2⟩)
  rw [e1, e2] at h1
  have hcard : Nat.card ↥(R₂ N p) ≤ Nat.card ↥Ω := by
    rw [h1, h2]
  have heq : Ω = R₂ N p := Subgroup.eq_of_le_of_card_ge hΩR hcard
  intro r hr
  have : r ∈ Ω := heq ▸ hr
  exact this.2

end CFSG.GH74.GLS.Stage4.Rest.T6W
