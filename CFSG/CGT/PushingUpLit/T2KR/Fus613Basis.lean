module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Cfg
public import CFSG.CGT.PushingUpLit.T2KR.Fus613Act

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75 CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}

structure Basis (H : MData G L M n) (r b : G) (e₁ e₂ : Fin 2 → Fq n) (ω : Fq n) : Prop where
  ω_eq : ω ^ 2 + ω + 1 = 0
  e₁_ne : e₁ ≠ 0
  span : ∀ w : Fin 2 → Fq n, ∃ α β : Fq n, w = α • e₁ + β • e₂
  r1 : H.act r e₁ = e₁
  r2 : H.act r e₂ = e₂ + e₁
  b1 : H.act b e₁ = e₁
  b2 : H.act b e₂ = e₂
  b_semi : ∀ (c : Fq n) (w : Fin 2 → Fq n), H.act b (c • w) = c ^ 2 • H.act b w

theorem exists_basis {H : MData G L M n} {T' : Subgroup G} {x r b : G} (c : Cfg H T' x r b) :
    ∃ e₁ e₂ ω, Basis H r b e₁ e₂ ω := by
  classical
  have hn := c.n_eq
  have hF : Fintype.card (Fq n) = 4 := by
    rw [H.hcard, hn]; norm_num
  have h2 : (2 : Fq n) = 0 := two_eq_zero
  have h3 : ∀ x : Fin 2 → Fq n, (2 : Fq n) • x = 0 := fun x => by rw [h2, zero_smul]
  have hrM : r ∈ M := H.le c.r_L
  set b' : ↥M := ⟨b, c.b_M⟩ with hb'
  have hb2 : b' * b' = 1 := Subtype.ext c.b_sq
  have hχ : H.chi b' ≠ 1 := H.chi_ne_one_of_not_mem hb2 c.b_LQ
  have hσσ : ∀ y, H.chi b' (H.chi b' y) = y := H.chi_involution hb2
  obtain ⟨ω, hω1⟩ := exists_add_eq_one (H.chi b') hχ hσσ
  have hω : ω ^ 2 + ω + 1 = 0 := by
    rcases f4_cases hF ω with h | h | h
    · rw [h, map_zero] at hω1; simp at hω1
    · rw [h, map_one] at hω1
      have : (1 : Fq n) + 1 = 0 := by linear_combination h2
      rw [this] at hω1
      simp at hω1
    · exact h
  have hσω : H.chi b' ω = ω ^ 2 := frob_eq_sq hF (H.chi b') hχ hω
  have hσ : ∀ y : Fq n, H.chi b' y = y ^ 2 := by
    intro y
    rcases f4_cases hF y with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rcases root_cases hω h with h' | h'
      · rw [h', hσω]
      · rw [h', map_pow, hσω]
  let β : (Fin 2 → Fq n) →+ (Fin 2 → Fq n) := AddMonoidHom.mk' (H.actHom b') (H.actHom_add b')
  have hβ : ∀ (c : Fq n) (w : Fin 2 → Fq n), β (c • w) = H.chi b' c • β w :=
    fun c w => H.isSemilinear_chi b' c w
  have hββ : ∀ w, β (β w) = w := fun w => by
    have := congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p w)
      (show H.actHom b' * H.actHom b' = 1 by rw [← map_mul, hb2, map_one])
    exact this
  have hβact : ∀ w, β w = H.act b w := fun w => rfl
  have hr2 := c.r_sq
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, H.act r w₀ ≠ w₀ := by
    by_contra hcon
    push Not at hcon
    apply c.r_Q
    have : r ∈ oTwoIn L := by
      refine NatData.mem_oTwoIn_of_centralizes H.D c.r_L fun v hv => ?_
      have h1 := H.conj_vec hrM (H.D.ψe v)
      rw [H.vec_ψe hv, hcon] at h1
      rw [h1, H.vec_ψe hv]
    rw [c.hO] at this
    exact H.blockU_le_QM this
  obtain ⟨e₂, he₂b, he₂r⟩ : ∃ e₂, H.act b e₂ = e₂ ∧ H.act r e₂ ≠ e₂ := by
    obtain ⟨c₁, c₂, hc₁, hc₂, hw⟩ := exists_fixed_decomp (H.chi b') hω1 β hβ hββ w₀
    by_contra hcon
    push Not at hcon
    apply hw₀
    have e1 := hcon c₁ (by rw [← hβact]; exact hc₁)
    have e2 := hcon c₂ (by rw [← hβact]; exact hc₂)
    rw [hw, H.act_add hrM, H.act_smul_L c.r_L, e1, e2]
  set e₁ := H.act r e₂ + e₂ with he₁
  have he₁ne : e₁ ≠ 0 := by
    intro h
    apply he₂r
    linear_combination (norm := module) h - h3 e₂
  have hbr : ∀ w, H.act b (H.act r w) = H.act r (H.act b w) := by
    intro w
    rw [← H.act_mul hrM w, ← H.act_mul c.b_M w, c.rb]
  have he₁b : H.act b e₁ = e₁ := by
    rw [he₁, H.act_add c.b_M, hbr, he₂b]
  have he₁r : H.act r e₁ = e₁ := by
    rw [he₁, H.act_add hrM, H.act_involution hrM hr2, add_comm]
  have hre₂ : H.act r e₂ = e₂ + e₁ := by
    rw [he₁]
    linear_combination (norm := module) (-1 : Fq n) • h3 e₂
  have htv : IsTv H e₁ e₂ r 1 := ⟨he₁r, by rw [one_smul]; exact hre₂⟩
  have hind : ∀ α β' : Fq n, α • e₁ + β' • e₂ = 0 → α = 0 ∧ β' = 0 := by
    intro α β' h
    have h1 := congrArg (fun w => H.act r w + w) h
    simp only [H.act_zero hrM, add_zero] at h1
    rw [htv.act_coord c.r_L] at h1
    have h4 : β' • e₁ = 0 := by
      linear_combination (norm := module) h1 - h3 (α • e₁ + β' • e₂)
    have hβ0 : β' = 0 := (smul_eq_zero.1 h4).resolve_right he₁ne
    subst hβ0
    refine ⟨?_, rfl⟩
    have h5 : α • e₁ = 0 := by simpa using h
    exact (smul_eq_zero.1 h5).resolve_right he₁ne
  have hspan : ∀ w : Fin 2 → Fq n, ∃ α β' : Fq n, w = α • e₁ + β' • e₂ := by
    let Φ : Fq n × Fq n → (Fin 2 → Fq n) := fun p => p.1 • e₁ + p.2 • e₂
    have hinj : Function.Injective Φ := by
      intro p p' hpp
      have : (p.1 - p'.1) • e₁ + (p.2 - p'.2) • e₂ = 0 := by
        simp only [Φ] at hpp
        rw [sub_smul, sub_smul]
        linear_combination (norm := module) hpp
      obtain ⟨h1, h2'⟩ := hind _ _ this
      exact Prod.ext (sub_eq_zero.1 h1) (sub_eq_zero.1 h2')
    have hcard : Fintype.card (Fq n × Fq n) = Fintype.card (Fin 2 → Fq n) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      ring
    have hbij := (Fintype.bijective_iff_injective_and_card Φ).2 ⟨hinj, hcard⟩
    intro w
    obtain ⟨⟨α, β'⟩, hΦ⟩ := hbij.2 w
    exact ⟨α, β', hΦ.symm⟩
  refine ⟨e₁, e₂, ω, ⟨hω, he₁ne, hspan, he₁r, hre₂, he₁b, he₂b, fun c' w => ?_⟩⟩
  have := H.isSemilinear_chi b' c' w
  rw [hσ c'] at this
  exact this

end CFSG.CGT.PushingUpLit.T2KR.P613
