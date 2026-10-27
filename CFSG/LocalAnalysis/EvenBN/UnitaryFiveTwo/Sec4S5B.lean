module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5A
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S4B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem not_A₂sub_le_A₁sub_sup_Fsub : ¬ A₂sub ≤ A₁sub ⊔ Fsub := fun hle => by
  have hx : x₁SU 1 F4.ω one_omega_rel ∈ A₂sub := X₁sub_le_A₂sub (x₁SU_mem _ _ _)
  have h0 := (mem_A₁sub_sup_Fsub_iff.1 (hle hx)).2
  rw [mat_x₁SU] at h0
  have h1 : x₁Mat 1 F4.ω 2 1 = 1 := by simp [x₁Mat]
  rw [h1] at h0
  exact one_ne_zero h0

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem S₃_le_normalizer_V₃ (h : d.Hyp) : d.S₃ ≤ normalizer (d.V₃ : Set G) := fun g hg =>
  mem_normalizer_fintype fun x hx => h.conj_mem_V₃ hg hx

theorem S_eq_A₁_sup_A₂ : d.S = d.A₁ ⊔ d.A₂ := by
  show d.pull Ssub = d.pull A₁sub ⊔ d.pull A₂sub
  rw [Ssub_eq_A₁sub_sup_A₂sub, d.pull_sup]

theorem F_le_V₃ (h : d.Hyp) : d.F ≤ d.V₃ := h.F_le_Y.trans h.Y_le_V₃

theorem ι_mem_F {ξ : SU52} (hξ : ξ ∈ Fsub) : d.ι ξ ∈ d.F := ⟨ξ, hξ, rfl⟩

theorem commutator_mem_V₃_of_mem_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {a b : G} (ha : a ∈ d.S₃)
    (hb : b ∈ d.S₃) : a * b * a⁻¹ * b⁻¹ ∈ d.V₃ := by
  have hset := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (h.S_le_S₃ hg) hx
  rw [h.S₃_eq_S_sup_V₃ hK] at ha hb
  obtain ⟨s, hs, v, hv, rfl⟩ : a ∈ (d.S : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact ha
  obtain ⟨s', hs', v', hv', rfl⟩ : b ∈ (d.S : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact hb
  have hs₃ := h.S_le_S₃ hs
  have hs'₃ := h.S_le_S₃ hs'
  have hc₁ : v * s' * v⁻¹ * s'⁻¹ ∈ d.V₃ := h.Y_le_V₃ ((h.mem_V₃_iff.1 hv).2 s' hs'₃)
  have hc₂ : v * v' * v⁻¹ * v'⁻¹ ∈ d.V₃ :=
    h.Y_le_V₃ ((h.mem_V₃_iff.1 hv).2 v' (V₃_le_S₃ hv'))
  have hc₃ : v' * s⁻¹ * v'⁻¹ * s ∈ d.V₃ := by
    have := (h.mem_V₃_iff.1 hv').2 s⁻¹ (inv_mem hs₃)
    rw [inv_inv] at this
    exact h.Y_le_V₃ this
  have e : s * v * (s' * v') * (s * v)⁻¹ * (s' * v')⁻¹ =
      (s * (v * s' * v⁻¹ * s'⁻¹) * s⁻¹) *
        ((s * s') * ((v * v' * v⁻¹ * v'⁻¹) * (v' * s⁻¹ * v'⁻¹ * s)) * (s * s')⁻¹) *
        (s * s' * s⁻¹ * s'⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem (h.conj_mem_V₃ hs₃ hc₁)
    (h.conj_mem_V₃ (mul_mem hs₃ hs'₃) (mul_mem hc₂ hc₃)))
    (h.commutator_S_le_V₃ (commutator_mem_commutator hs hs'))

theorem sup_V₃_comm_sq_mem_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {P' : Subgroup G} (hP'S : P' ≤ d.S)
    (hc : ∀ x ∈ P', ∀ y ∈ P', x * y * x⁻¹ * y⁻¹ ∈ d.F) (hs : ∀ x ∈ P', x * x ∈ d.F) :
    (∀ x ∈ P' ⊔ d.V₃, ∀ y ∈ P' ⊔ d.V₃, x * y * x⁻¹ * y⁻¹ ∈ d.Y) ∧
      ∀ x ∈ P' ⊔ d.V₃, x * x ∈ d.Y := by
  have hset := coe_mul_of_left_le_normalizer_right P' d.V₃ fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (h.S_le_S₃ (hP'S hg)) hx
  have hN : ∀ g ∈ d.S, ∀ y ∈ d.Y, g * y * g⁻¹ ∈ d.Y := fun g hg y hy =>
    (mem_normalizer_iff.1 (h.S_le_normalizer_Y hg) y).1 hy
  constructor
  · intro x hx y hy
    obtain ⟨s, hs, v, hv, rfl⟩ : x ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hx
    obtain ⟨s', hs', v', hv', rfl⟩ : y ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hy
    have hsS := hP'S hs
    have hs'S := hP'S hs'
    have hc₁ : v * s' * v⁻¹ * s'⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 s' (h.S_le_S₃ hs'S)
    have hc₂ : v * v' * v⁻¹ * v'⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 v' (V₃_le_S₃ hv')
    have hc₃ : v' * s⁻¹ * v'⁻¹ * s ∈ d.Y := by
      have := (h.mem_V₃_iff.1 hv').2 s⁻¹ (inv_mem (h.S_le_S₃ hsS))
      rwa [inv_inv] at this
    have e : s * v * (s' * v') * (s * v)⁻¹ * (s' * v')⁻¹ =
        (s * (v * s' * v⁻¹ * s'⁻¹) * s⁻¹) *
          ((s * s') * ((v * v' * v⁻¹ * v'⁻¹) * (v' * s⁻¹ * v'⁻¹ * s)) * (s * s')⁻¹) *
          (s * s' * s⁻¹ * s'⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hN s hsS _ hc₁) (hN (s * s') (mul_mem hsS hs'S) _ (mul_mem hc₂ hc₃)))
      (h.F_le_Y (hc s hs s' hs'))
  · intro x hx
    obtain ⟨s, hs', v, hv, rfl⟩ : x ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hx
    have hsS := hP'S hs'
    have hc : v * s * v⁻¹ * s⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 s (h.S_le_S₃ hsS)
    have e : s * v * (s * v) = (s * (v * s * v⁻¹ * s⁻¹) * s⁻¹) * (s * s) * (v * v) := by group
    rw [e]
    exact mul_mem (mul_mem (hN s hsS _ hc) (h.F_le_Y (hs s hs'))) (h.D₂_mul_self_mem_Y hK
      (h.V₃_le_D₂ hK hv))

theorem A₁V₃_elemAb (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    (∀ x ∈ d.A₁ ⊔ d.V₃, ∀ y ∈ d.A₁ ⊔ d.V₃, x * y * x⁻¹ * y⁻¹ ∈ d.Y) ∧
      ∀ x ∈ d.A₁ ⊔ d.V₃, x * x ∈ d.Y := by
  have hP : (d.A₁ ⊔ d.F) ⊔ d.V₃ = d.A₁ ⊔ d.V₃ := by
    rw [sup_assoc, sup_eq_right.2 h.F_le_V₃]
  have hmodel : ∀ x ∈ d.A₁ ⊔ d.F, ∃ ξ ∈ A₁sub ⊔ Fsub, d.ι ξ = x := fun x hx => by
    have : x ∈ d.pull (A₁sub ⊔ Fsub) := by
      rw [d.pull_sup]
      exact hx
    exact this
  have := h.sup_V₃_comm_sq_mem_Y hK (P' := d.A₁ ⊔ d.F) (sup_le d.A₁_le_S F_le_S)
    (fun x hx y hy => by
      obtain ⟨ξ, hξ, rfl⟩ := hmodel x hx
      obtain ⟨η, hη, rfl⟩ := hmodel y hy
      have := ι_mem_F (d := d) (commutator_mem_Fsub_of_mem_A₁sub_sup_Fsub hξ hη)
      rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at this)
    (fun x hx => by
      obtain ⟨ξ, hξ, rfl⟩ := hmodel x hx
      have := ι_mem_F (d := d) (mul_self_mem_Fsub_of_mem_A₁sub_sup_Fsub hξ)
      rwa [map_mul] at this)
  rwa [hP] at this

theorem A₂V₃_elemAb (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    (∀ x ∈ d.A₂ ⊔ d.V₃, ∀ y ∈ d.A₂ ⊔ d.V₃, x * y * x⁻¹ * y⁻¹ ∈ d.Y) ∧
      ∀ x ∈ d.A₂ ⊔ d.V₃, x * x ∈ d.Y :=
  h.sup_V₃_comm_sq_mem_Y hK (d.A₂_le_S)
    (fun x hx y hy => by
      obtain ⟨ξ, hξ, rfl⟩ := hx
      obtain ⟨η, hη, rfl⟩ := hy
      have := ι_mem_F (d := d) (commutator_mem_Fsub hξ hη)
      rw [commutatorElement_def] at this
      rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at this)
    (fun x hx => by
      obtain ⟨ξ, hξ, rfl⟩ := hx
      have := ι_mem_F (d := d) (mul_self_mem_Fsub hξ)
      rwa [map_mul] at this)

theorem le_A₁V₃_or_le_A₂V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {B : Subgroup G} (hBS : B ≤ d.S₃) (hV : d.V₃ ≤ B)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ d.Y) (hs : ∀ x ∈ B, x * x ∈ d.Y) :
    B ≤ d.A₁ ⊔ d.V₃ ∨ B ≤ d.A₂ ⊔ d.V₃ := by
  let E : Subgroup SU52 := (B ⊓ d.S).comap d.ι
  have hES : E ≤ Ssub := fun x hx => d.ι_mem_pull_iff.1 (Subgroup.mem_inf.1 hx).2
  have hcF : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Fsub := fun x hx y hy => by
    have hxB := (Subgroup.mem_inf.1 hx).1
    have hyB := (Subgroup.mem_inf.1 hy).1
    have hxS := (Subgroup.mem_inf.1 hx).2
    have hyS := (Subgroup.mem_inf.1 hy).2
    have hY := hc _ hxB _ hyB
    have hS' : d.ι x * d.ι y * (d.ι x)⁻¹ * (d.ι y)⁻¹ ∈ d.S :=
      mul_mem (mul_mem (mul_mem hxS hyS) (inv_mem hxS)) (inv_mem hyS)
    have hF : d.ι x * d.ι y * (d.ι x)⁻¹ * (d.ι y)⁻¹ ∈ d.F := by
      rw [← h.S_inf_Y]
      exact Subgroup.mem_inf.2 ⟨hS', hY⟩
    have e : d.ι (x * y * x⁻¹ * y⁻¹) = d.ι x * d.ι y * (d.ι x)⁻¹ * (d.ι y)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← e] at hF
    exact d.ι_mem_pull_iff.1 hF
  have hsF : ∀ x ∈ E, x * x ∈ Fsub := fun x hx => by
    have hxB := (Subgroup.mem_inf.1 hx).1
    have hxS := (Subgroup.mem_inf.1 hx).2
    have hF : d.ι x * d.ι x ∈ d.F := by
      rw [← h.S_inf_Y]
      exact Subgroup.mem_inf.2 ⟨mul_mem hxS hxS, hs _ hxB⟩
    rw [← map_mul] at hF
    exact d.ι_mem_pull_iff.1 hF
  have hset := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (h.S_le_S₃ hg) hx
  have hdec : ∀ b ∈ B, ∃ σ ∈ E, ∃ v ∈ d.V₃, b = d.ι σ * v := fun b hb => by
    have hb₃ := hBS hb
    rw [h.S₃_eq_S_sup_V₃ hK] at hb₃
    obtain ⟨s, hs, v, hv, hsv⟩ : b ∈ (d.S : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hb₃
    obtain ⟨σ, hσ, rfl⟩ := hs
    refine ⟨σ, Subgroup.mem_inf.2 ⟨?_, ⟨σ, hσ, rfl⟩⟩, v, hv, hsv.symm⟩
    have : d.ι σ = b * v⁻¹ := by rw [← hsv]; group
    rw [this]
    exact mul_mem hb (inv_mem (hV hv))
  rcases le_A₁sub_sup_Fsub_or_le_A₂sub hES hcF hsF with hE | hE
  · left
    intro b hb
    obtain ⟨σ, hσ, v, hv, rfl⟩ := hdec b hb
    have h1 : d.ι σ ∈ d.pull (A₁sub ⊔ Fsub) := d.ι_mem_pull_iff.2 (hE hσ)
    rw [d.pull_sup] at h1
    exact mul_mem ((sup_le le_sup_left (h.F_le_V₃.trans le_sup_right) :
      d.A₁ ⊔ d.F ≤ d.A₁ ⊔ d.V₃) h1) (mem_sup_right hv)
  · right
    intro b hb
    obtain ⟨σ, hσ, v, hv, rfl⟩ := hdec b hb
    exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (hE hσ) : d.ι σ ∈ d.A₂)) (mem_sup_right hv)

theorem conj_A₁V₃_le (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {g : G}
    (hgS₃ : g ∈ normalizer (d.S₃ : Set G)) (hgY : g ∈ normalizer (d.Y : Set G)) :
    (∀ x ∈ d.A₁ ⊔ d.V₃, g * x * g⁻¹ ∈ d.A₁ ⊔ d.V₃) ∨
      (∀ x ∈ d.A₁ ⊔ d.V₃, g * x * g⁻¹ ∈ d.A₂ ⊔ d.V₃) := by
  have hgV := h.mem_normalizer_V₃ hgS₃ hgY
  have hle : d.A₁ ⊔ d.V₃ ≤ d.S₃ := sup_le (d.A₁_le_S.trans h.S_le_S₃) V₃_le_S₃
  obtain ⟨hc, hs⟩ := h.A₁V₃_elemAb hK
  let B : Subgroup G := (d.A₁ ⊔ d.V₃).map (MulAut.conj g).toMonoidHom
  have hmem : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ d.A₁ ⊔ d.V₃ := fun x => mem_map_conj_iff _ g x
  have hBS : B ≤ d.S₃ := fun x hx => by
    have := (mem_normalizer_iff.1 hgS₃ _).1 (hle ((hmem x).1 hx))
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  have hV : d.V₃ ≤ B := fun v hv => (hmem v).2 (mem_sup_right (by
    have := (mem_normalizer_iff.1 (inv_mem hgV) v).1 hv
    rwa [inv_inv] at this))
  have hcB : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ d.Y := fun x hx y hy => by
    have h1 := hc _ ((hmem x).1 hx) _ ((hmem y).1 hy)
    have h2 := (mem_normalizer_iff.1 hgY _).1 h1
    rwa [show g * (g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
      x * y * x⁻¹ * y⁻¹ by group] at h2
  have hsB : ∀ x ∈ B, x * x ∈ d.Y := fun x hx => by
    have h1 := hs _ ((hmem x).1 hx)
    have h2 := (mem_normalizer_iff.1 hgY _).1 h1
    rwa [show g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ = x * x by group] at h2
  rcases h.le_A₁V₃_or_le_A₂V₃ hK hBS hV hcB hsB with hB | hB
  · left
    intro x hx
    exact hB ((hmem _).2 (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]))
  · right
    intro x hx
    exact hB ((hmem _).2 (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]))

theorem conj_A₂V₃_le (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {g : G}
    (hgS₃ : g ∈ normalizer (d.S₃ : Set G)) (hgY : g ∈ normalizer (d.Y : Set G)) :
    (∀ x ∈ d.A₂ ⊔ d.V₃, g * x * g⁻¹ ∈ d.A₁ ⊔ d.V₃) ∨
      (∀ x ∈ d.A₂ ⊔ d.V₃, g * x * g⁻¹ ∈ d.A₂ ⊔ d.V₃) := by
  have hgV := h.mem_normalizer_V₃ hgS₃ hgY
  have hle : d.A₂ ⊔ d.V₃ ≤ d.S₃ := sup_le (d.A₂_le_S.trans h.S_le_S₃) V₃_le_S₃
  obtain ⟨hc, hs⟩ := h.A₂V₃_elemAb hK
  let B : Subgroup G := (d.A₂ ⊔ d.V₃).map (MulAut.conj g).toMonoidHom
  have hmem : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ d.A₂ ⊔ d.V₃ := fun x => mem_map_conj_iff _ g x
  have hBS : B ≤ d.S₃ := fun x hx => by
    have := (mem_normalizer_iff.1 hgS₃ _).1 (hle ((hmem x).1 hx))
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  have hV : d.V₃ ≤ B := fun v hv => (hmem v).2 (mem_sup_right (by
    have := (mem_normalizer_iff.1 (inv_mem hgV) v).1 hv
    rwa [inv_inv] at this))
  have hcB : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ d.Y := fun x hx y hy => by
    have h1 := hc _ ((hmem x).1 hx) _ ((hmem y).1 hy)
    have h2 := (mem_normalizer_iff.1 hgY _).1 h1
    rwa [show g * (g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
      x * y * x⁻¹ * y⁻¹ by group] at h2
  have hsB : ∀ x ∈ B, x * x ∈ d.Y := fun x hx => by
    have h1 := hs _ ((hmem x).1 hx)
    have h2 := (mem_normalizer_iff.1 hgY _).1 h1
    rwa [show g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ = x * x by group] at h2
  rcases h.le_A₁V₃_or_le_A₂V₃ hK hBS hV hcB hsB with hB | hB
  · left
    intro x hx
    exact hB ((hmem _).2 (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]))
  · right
    intro x hx
    exact hB ((hmem _).2 (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]))

theorem D₂_le_normalizer_A₁V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.D₂ ≤ normalizer ((d.A₁ ⊔ d.V₃ : Subgroup G) : Set G) := fun u hu => by
  have huS₃ := h.D₂_le_normalizer_S₃ hu
  have huY : u ∈ normalizer (d.Y : Set G) :=
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' hu hy).symm
  rcases h.conj_A₁V₃_le hK huS₃ huY with h1 | h2
  · exact mem_normalizer_fintype h1
  · exfalso
    have hX : d.X₂ ≤ d.X₂ ⊓ d.D₂ := fun x hx => by
      refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
      have h3 := h2 x (mem_sup_left (X₂_le_A₁ hx))
      have h4 : u * x * u⁻¹ ∈ d.D₂ := (sup_le h.A₂_le_D₂' (h.V₃_le_D₂ hK)) h3
      have := mul_mem (mul_mem (inv_mem hu) h4) hu
      rwa [show u⁻¹ * (u * x * u⁻¹) * u = x by group] at this
    rw [h.X₂_inf_D₂] at hX
    have := Subgroup.card_le_of_le hX
    rw [card_X₂ (d := d), Subgroup.card_bot] at this
    omega

theorem D₁_le_normalizer_S₃ (h : d.Hyp) (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.D₁ ≤ normalizer (d.S₃ : Set G) := fun x hx => mem_normalizer_fintype fun g hg => by
  have hxC : x ∈ centralizer (d.W : Set G) := (Subgroup.mem_inf.1 hx).2
  exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.D₁_le_normalizer_R₃ hKY hx) g).1
    (S₃_le_R₃ hg), mul_mem (mul_mem hxC (S₃_le_centralizer_W hg)) (inv_mem hxC)⟩

theorem D₁_le_normalizer_V₃ (h : d.Hyp) (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.D₁ ≤ normalizer (d.V₃ : Set G) := fun x hx =>
  h.mem_normalizer_V₃ (h.D₁_le_normalizer_S₃ hKY hx) (h.D₁_le_normalizer_Y hKY hx)

theorem D₁_le_normalizer_A₁V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.D₁ ≤ normalizer ((d.A₁ ⊔ d.V₃ : Subgroup G) : Set G) := fun x hx => by
  have hxV : x ∈ normalizer (d.V₃ : Set G) := h.D₁_le_normalizer_V₃ hKY hx
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : d.A₁ ⊔ d.V₃ ≤ (d.A₁ ⊔ d.V₃).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun v hv => ?_)
    · change x * a * x⁻¹ ∈ d.A₁ ⊔ d.V₃
      have hW : x * a * x⁻¹ * a⁻¹ ∈ d.W := by
        have := commutator_mem_commutator hx (h.A₁_le_D₁ ha)
        rw [h.commutator_D₁_eq_W hK, commutatorElement_def] at this
        exact this
      rw [show x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a by group]
      exact mul_mem (mem_sup_right (h.W_le_V₃ hW)) (mem_sup_left ha)
    · exact mem_sup_right ((mem_normalizer_iff.1 hxV v).1 hv)
  exact hle hy

theorem not_A₂_le_A₁V₃ (h : d.Hyp) : ¬ d.A₂ ≤ d.A₁ ⊔ d.V₃ := fun hle => by
  apply not_A₂sub_le_A₁sub_sup_Fsub
  intro ξ hξ
  have hξS : d.ι ξ ∈ d.A₂ := ⟨ξ, hξ, rfl⟩
  have hset := coe_mul_of_left_le_normalizer_right d.A₁ d.V₃ fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (h.S_le_S₃ (d.A₁_le_S hg)) hx
  obtain ⟨a₁, ha₁, v, hv, hav⟩ : d.ι ξ ∈ (d.A₁ : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact hle hξS
  have hvS : v ∈ d.S := by
    have := mul_mem (inv_mem (d.A₁_le_S ha₁)) (d.A₂_le_S hξS)
    rwa [← hav, inv_mul_cancel_left] at this
  have hvS' : v ∈ ⁅d.S, d.S⁆ := by
    have : v ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨hvS, hv⟩
    rwa [h.S_inf_V₃] at this
  rw [commutator_S_eq] at hvS'
  have hF : d.ι ξ ∈ d.A₁ ⊔ d.F := by
    rw [← hav]
    exact mul_mem (mem_sup_left ha₁)
      ((sup_le_sup (d.pull_mono X₄sub_le_A₁sub') le_rfl : d.X₄ ⊔ d.F ≤ d.A₁ ⊔ d.F) hvS')
  have : d.ι ξ ∈ d.pull (A₁sub ⊔ Fsub) := by
    rw [d.pull_sup]
    exact hF
  exact d.ι_mem_pull_iff.1 this

theorem D₁_le_normalizer_A₂V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.D₁ ≤ normalizer ((d.A₂ ⊔ d.V₃ : Subgroup G) : Set G) := fun x hx => by
  have hxS₃ := h.D₁_le_normalizer_S₃ hKY hx
  have hxY := h.D₁_le_normalizer_Y hKY hx
  have hxA₁ := h.D₁_le_normalizer_A₁V₃ hK hKY hx
  rcases h.conj_A₂V₃_le hK hxS₃ hxY with h1 | h2
  · exfalso
    apply h.not_A₂_le_A₁V₃
    intro a ha
    have := (mem_normalizer_iff.1 (inv_mem hxA₁) _).1 (h1 a (mem_sup_left ha))
    rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at this
  · exact mem_normalizer_fintype h2

theorem S_le_normalizer_V₃ (h : d.Hyp) : d.S ≤ normalizer (d.V₃ : Set G) := fun g hg =>
  h.S₃_le_normalizer_V₃ (h.S_le_S₃ hg)

theorem D₂_inf_A₁V₃_le_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {c : G} (hcD : c ∈ d.D₂) (hcA : c ∈ d.A₁ ⊔ d.V₃) : c ∈ d.V₃ := by
  have hset := coe_mul_of_left_le_normalizer_right d.A₁ d.V₃ fun g hg =>
    h.S_le_normalizer_V₃ (d.A₁_le_S hg)
  obtain ⟨a', ha', v, hv, hav⟩ : c ∈ (d.A₁ : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact hcA
  have ha'D : a' ∈ d.D₂ := by
    have := mul_mem hcD (inv_mem (h.V₃_le_D₂ hK hv))
    rwa [← hav, mul_inv_cancel_right] at this
  have ha'A₂ : a' ∈ d.A₂ := by
    have : a' ∈ d.D₂ ⊓ d.H := Subgroup.mem_inf.2 ⟨ha'D, h.L_le_H (d.pull_le_L _ ha')⟩
    rwa [h.D₂_inf_H] at this
  have ha'34 : a' ∈ d.X₃ ⊔ d.X₄ := h.A₁_inf_D₀_le ha' (h.A₂_le_D₀ ha'A₂)
  have ha'V : a' ∈ d.V₃ :=
    h.commutator_S_le_V₃ (by rw [commutator_S_eq]; exact X₃₄_le_XF ha'34)
  rw [← hav]
  exact mul_mem ha'V hv

theorem D₂_le_cenMod_V₃_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : d.D₂ ≤ cenMod d.V₃ d.S₃ :=
  fun u hu => by
  have huV := h.D₂_le_normalizer_V₃ hu
  have huA₁ := h.D₂_le_normalizer_A₁V₃ hK hu
  refine ⟨huV, fun s hs => ?_⟩
  have hgen : d.S₃ ≤ centModSub d.V₃ u := by
    rw [h.S₃_eq_S_sup_V₃ hK, S_eq_A₁_sup_A₂]
    refine sup_le (sup_le (fun a ha => ?_) (fun a ha => ?_)) (fun v hv => ?_)
    · refine ⟨h.S_le_normalizer_V₃ (d.A₁_le_S ha), ?_⟩
      have hcD : a * u * a⁻¹ * u⁻¹ ∈ d.D₂ :=
        mul_mem ((mem_normalizer_iff.1 (h.S_le_normalizer_D₂ (d.A₁_le_S ha)) u).1 hu)
          (inv_mem hu)
      have hcA : a * u * a⁻¹ * u⁻¹ ∈ d.A₁ ⊔ d.V₃ := by
        rw [show a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) by group]
        exact mul_mem (mem_sup_left ha)
          ((mem_normalizer_iff.1 huA₁ a⁻¹).1 (mem_sup_left (inv_mem ha)))
      exact h.D₂_inf_A₁V₃_le_V₃ hK hcD hcA
    · exact ⟨h.S_le_normalizer_V₃ (d.A₂_le_S ha), h.Y_le_V₃
        (h.D₂_commutator_mem_Y hK (h.A₂_le_D₂' ha) hu)⟩
    · refine ⟨h.S₃_le_normalizer_V₃ (V₃_le_S₃ hv), ?_⟩
      rw [show v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) by group]
      exact mul_mem hv ((mem_normalizer_iff.1 huV v⁻¹).1 (inv_mem hv))
  have := inv_mem (mem_centModSub.1 (hgen hs)).2
  rwa [show (s * u * s⁻¹ * u⁻¹)⁻¹ = u * s * u⁻¹ * s⁻¹ by group] at this

theorem D₁_inf_A₂V₃_le_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {c : G} (hcD : c ∈ d.D₁) (hcA : c ∈ d.A₂ ⊔ d.V₃) : c ∈ d.V₃ := by
  have hS₃ : c ∈ d.S₃ := (sup_le (d.A₂_le_S.trans h.S_le_S₃) V₃_le_S₃) hcA
  have hc₃ : c ∈ d.D₃ := Subgroup.mem_inf.2 ⟨oTwo_le _ (S₃_le_R₃ hS₃), hcD⟩
  obtain ⟨x₂, hx₂, w, hw, hcw⟩ := h.exists_eq_mul_of_mem_D₃' hc₃
  have hwV : w ∈ d.V₃ := h.D₃_inf_D₂_le_V₃ hK hw
  have hset := coe_mul_of_left_le_normalizer_right d.A₂ d.V₃ fun g hg =>
    h.S_le_normalizer_V₃ (d.A₂_le_S hg)
  obtain ⟨a', ha', v, hv, hav⟩ : c ∈ (d.A₂ : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact hcA
  have hx₂S : x₂ ∈ d.S := X₂_le_S' hx₂
  have hx₂A₂ : x₂ ∈ d.A₂ := by
    have e : a'⁻¹ * x₂ = v * w⁻¹ := by
      have : x₂ = c * w⁻¹ := by rw [hcw]; group
      rw [this, ← hav]
      group
    have hS : a'⁻¹ * x₂ ∈ d.S := mul_mem (inv_mem (d.A₂_le_S ha')) hx₂S
    have hV : a'⁻¹ * x₂ ∈ d.V₃ := by
      rw [e]
      exact mul_mem hv (inv_mem hwV)
    have hS' : a'⁻¹ * x₂ ∈ ⁅d.S, d.S⁆ := by
      have : a'⁻¹ * x₂ ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨hS, hV⟩
      rwa [h.S_inf_V₃] at this
    have := mul_mem ha' (commutator_S_le_A₂ hS')
    rwa [mul_inv_cancel_left] at this
  have hx₂1 : x₂ = 1 := by
    have : x₂ ∈ d.X₂ ⊓ d.A₂ := Subgroup.mem_inf.2 ⟨hx₂, hx₂A₂⟩
    rw [h.X₂_inf_A₂] at this
    exact Subgroup.mem_bot.1 this
  rw [hcw, hx₂1, one_mul]
  exact hwV

theorem D₁_le_cenMod_V₃_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.D₁ ≤ cenMod d.V₃ d.S₃ := fun x hx => by
  have hxV := h.D₁_le_normalizer_V₃ hKY hx
  have hxA₂ := h.D₁_le_normalizer_A₂V₃ hK hKY hx
  refine ⟨hxV, fun s hs => ?_⟩
  have hgen : d.S₃ ≤ centModSub d.V₃ x := by
    rw [h.S₃_eq_S_sup_V₃ hK, S_eq_A₁_sup_A₂]
    refine sup_le (sup_le (fun a ha => ?_) (fun a ha => ?_)) (fun v hv => ?_)
    · refine ⟨h.S_le_normalizer_V₃ (d.A₁_le_S ha), ?_⟩
      have hW : x * a * x⁻¹ * a⁻¹ ∈ d.W := by
        have := commutator_mem_commutator hx (h.A₁_le_D₁ ha)
        rw [h.commutator_D₁_eq_W hK, commutatorElement_def] at this
        exact this
      have := inv_mem (h.W_le_V₃ hW)
      rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at this
    · refine ⟨h.S_le_normalizer_V₃ (d.A₂_le_S ha), ?_⟩
      have haR : a ∈ d.R := (le_sup_left : d.S ≤ d.S ⊔ zpowers d.t) (d.A₂_le_S ha)
      have hcD : x * a * x⁻¹ * a⁻¹ ∈ d.D₁ := by
        rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
        exact mul_mem hx ((mem_normalizer_iff.1 (h.R_le_normalizer_D₁ haR) x⁻¹).1 (inv_mem hx))
      have hcA : x * a * x⁻¹ * a⁻¹ ∈ d.A₂ ⊔ d.V₃ :=
        mul_mem ((mem_normalizer_iff.1 hxA₂ a).1 (mem_sup_left ha)) (inv_mem (mem_sup_left ha))
      have := inv_mem (h.D₁_inf_A₂V₃_le_V₃ hK hcD hcA)
      rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at this
    · refine ⟨h.S₃_le_normalizer_V₃ (V₃_le_S₃ hv), ?_⟩
      rw [show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
      exact mul_mem hv ((mem_normalizer_iff.1 hxV v⁻¹).1 (inv_mem hv))
  have := inv_mem (mem_centModSub.1 (hgen hs)).2
  rwa [show (s * x * s⁻¹ * x⁻¹)⁻¹ = x * s * x⁻¹ * s⁻¹ by group] at this

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
