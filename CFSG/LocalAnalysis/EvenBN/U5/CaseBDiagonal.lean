module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBFactors
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem eq_of_inv_mul_mem_of_add {B : Subgroup G} {k : Type*} [Field k]
    {θ : (Fin 2 → k) → G} (hadd : ∀ v w, (θ v * θ w)⁻¹ * θ (v + w) ∈ B)
    (hinj : ∀ v, θ v ∈ B → v = 0) {v w : Fin 2 → k} (h : (θ w)⁻¹ * θ v ∈ B) : v = w := by
  have h4 := hadd w (v - w)
  rw [add_sub_cancel] at h4
  have h5 : θ (v - w) ∈ B := by
    have := inv_mem (mul_mem h4 (inv_mem h))
    have e : ((θ w * θ (v - w))⁻¹ * θ v * ((θ w)⁻¹ * θ v)⁻¹)⁻¹ = θ (v - w) := by group
    rwa [e] at this
  exact sub_eq_zero.1 (hinj _ h5)

theorem IsNaturalSection.card_eq {X A B : Subgroup G} {k : Type*} [Field k] [Finite k]
    (hN : IsNaturalSection X A B k) (hBA : B ≤ A) :
    Nat.card A = Nat.card B * Nat.card k ^ 2 := by
  obtain ⟨-, θ, hθA, hadd, hinj, hsurj, -⟩ := hN
  let Φ : (Fin 2 → k) × B → A := fun p => ⟨θ p.1 * p.2, mul_mem (hθA p.1) (hBA p.2.2)⟩
  have hbij : Function.Bijective Φ := by
    refine ⟨fun p p' e => ?_, fun a => ?_⟩
    · have e' : θ p.1 * p.2 = θ p'.1 * p'.2 := congrArg Subtype.val e
      have hv : p.1 = p'.1 := eq_of_inv_mul_mem_of_add hadd hinj
        (by
          have : (θ p'.1)⁻¹ * θ p.1 = (p'.2 : G) * (p.2 : G)⁻¹ := by
            calc (θ p'.1)⁻¹ * θ p.1 = (θ p'.1)⁻¹ * (θ p.1 * p.2) * (p.2 : G)⁻¹ := by group
              _ = (θ p'.1)⁻¹ * (θ p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [e']
              _ = (p'.2 : G) * (p.2 : G)⁻¹ := by group
          rw [this]
          exact mul_mem p'.2.2 (inv_mem p.2.2))
      have hb : (p.2 : G) = p'.2 := by
        rw [hv] at e'
        exact mul_left_cancel e'
      exact Prod.ext hv (Subtype.ext hb)
    · obtain ⟨v, hv⟩ := hsurj a a.2
      exact ⟨(v, ⟨_, hv⟩), Subtype.ext (by simp [Φ])⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod, Nat.card_fun, Nat.card_fin,
    mul_comm]

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable {c : d.CaseBData} (hB : d.CaseBHyp)
include hB

theorem commutator_Kc_map_conj_t_inv : ⁅c.Kc, c.Kc.map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [hB.hyp.t_inv']
  exact commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 (c.Kt_le_centralizer_Kc hB))

@[expose] def δ : c.Kc →* G := Common.diagonalHom c.Kc d.t (c.commutator_Kc_map_conj_t_inv hB)

theorem δ_apply (x : c.Kc) : c.δ hB x = (x : G) * (d.t⁻¹ * x * d.t) := rfl

theorem injective_δ : Function.Injective (c.δ hB) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 := Common.map_ker_diagonalHom_le (c.commutator_Kc_map_conj_t_inv hB) ⟨x, hx, rfl⟩
  rw [hB.hyp.t_inv'] at h1
  change (x : G) ∈ c.Kc ⊓ c.Kt at h1
  rw [c.Kc_inf_Kt hB, mem_bot] at h1
  exact (mem_bot).2 (Subtype.ext h1)

theorem conj_mem_Kt {x : G} (hx : x ∈ c.Kc) : d.t⁻¹ * x * d.t ∈ c.Kt := by
  refine ⟨x, hx, ?_⟩
  change d.t * x * d.t⁻¹ = d.t⁻¹ * x * d.t
  rw [hB.hyp.t_inv']

omit [Finite G] hB in
theorem conj_mem_Kc {y : G} (hy : y ∈ c.Kt) : d.t⁻¹ * y * d.t ∈ c.Kc := by
  obtain ⟨x, hx, rfl⟩ := hy
  change d.t⁻¹ * (d.t * x * d.t⁻¹) * d.t ∈ c.Kc
  rw [show d.t⁻¹ * (d.t * x * d.t⁻¹) * d.t = x by group]
  exact hx

theorem range_δ : (c.δ hB).range = d.L₁ ⊓ centralizer ({d.t} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mul_mem (c.Kc_le_L₁ a.2) (c.Kt_le_L₁ hB (c.conj_mem_Kt hB a.2)),
      Common.range_diagonalHom_le (c.commutator_Kc_map_conj_t_inv hB) hB.hyp.t_mul_t ⟨a, rfl⟩⟩
  · intro x hx
    obtain ⟨hxL, hxt⟩ := Subgroup.mem_inf.1 hx
    rw [← c.Kc_sup_Kt hB] at hxL
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => c.commute_of_mem_Kc_of_mem_Kt hB ha hb) hxL
    have hxt0 : a * b * d.t = d.t * (a * b) := mem_centralizer_singleton_iff.1 hxt
    have hxt' : d.t⁻¹ * (a * b) * d.t = a * b := by
      calc d.t⁻¹ * (a * b) * d.t = d.t⁻¹ * ((a * b) * d.t) := by group
        _ = d.t⁻¹ * (d.t * (a * b)) := by rw [hxt0]
        _ = a * b := by group
    have e : (d.t⁻¹ * b * d.t) * (d.t⁻¹ * a * d.t) = a * b := by
      calc (d.t⁻¹ * b * d.t) * (d.t⁻¹ * a * d.t) = (d.t⁻¹ * a * d.t) * (d.t⁻¹ * b * d.t) :=
            c.commute_of_mem_Kc_of_mem_Kt hB (c.conj_mem_Kc hb) (c.conj_mem_Kt hB ha)
        _ = d.t⁻¹ * (a * b) * d.t := by group
        _ = a * b := hxt'
    obtain ⟨-, hbt⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (c.Kc_inf_Kt hB) (c.conj_mem_Kc hb) ha
      (c.conj_mem_Kt hB ha) hb e
    exact ⟨⟨a, ha⟩, by rw [δ_apply, hbt]⟩

theorem D_inf_X : d.D ⊓ c.X = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxX⟩
  refine (mem_bot).2 (c.eq_one_of_mem_X hB hxX fun a ha => ?_)
  have := commutatorElement_mem_F hB (inv_mem ha) hxD
  rw [inv_inv] at this
  simpa only [mul_assoc] using this

theorem X_sup_D_inf_Kc : c.X ⊔ (d.D ⊓ c.Kc) = c.Kc := by
  rw [← sup_inf_eq_of_le' (c.X_le_Kc hB) (c.X_le_normalizer_D hB), sup_comm]
  exact inf_eq_right.2 (c.Kc_le_D_sup_X hB)

theorem card_D_inf_Kc : Nat.card (d.D ⊓ c.Kc : Subgroup G) = (2 ^ f) ^ 8 := by
  obtain ⟨-, -, hN⟩ := hB.sec3_12 c.k inferInstance inferInstance c.card_k c.ψ
  obtain ⟨-, -, -, hc2⟩ := c.F_eq hB
  have hFK : (d.F ⊔ c.Kc) ⊓ d.D = d.F ⊔ (c.Kc ⊓ d.D) :=
    sup_inf_eq_of_le' hB.F_le_D (hB.F_le_L₁.trans c.L₁_le_normalizer_Kc)
  have h1 := hN.card_eq (le_inf le_sup_left hB.F_le_D)
  change Nat.card ((d.F ⊔ c.Kc) ⊓ d.D : Subgroup G) = _ at h1
  rw [hFK] at h1
  have h2 := Common.card_sup_mul_card_inf_eq (A := d.F) (B := c.Kc ⊓ d.D)
    ((inf_le_left.trans c.Kc_le_L₁).trans hB.L₁_le_normalizer_F)
  have h3 : d.F ⊓ (c.Kc ⊓ d.D) = c.F₂ := by
    rw [← inf_assoc, c.F_inf_Kc hB]
    exact inf_eq_left.2 (inf_le_left.trans hB.F_le_D)
  rw [h1, h3, hc2, hB.hyp.card_F hB.gms, Nat.card_eq_fintype_card (α := c.k), c.card_k,
    inf_comm] at h2
  have hpos : 0 < (2 ^ f) ^ 8 := by positivity
  have e : (2 ^ f) ^ 8 * Nat.card (d.D ⊓ c.Kc : Subgroup G) = (2 ^ f) ^ 8 * (2 ^ f) ^ 8 := by
    rw [← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos e

theorem card_Kc :
    Nat.card c.Kc = (2 ^ f) ^ 8 * ((2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1)) := by
  have h2 := Common.card_sup_mul_card_inf_eq (A := d.D ⊓ c.Kc) (B := c.X)
    fun x hx => Common.mem_normalizer_inf (c.X_le_normalizer_D hB hx)
      (c.L₁_le_normalizer_Kc (c.X_le_L₁ hB hx))
  have hinf : (d.D ⊓ c.Kc) ⊓ c.X = ⊥ := by
    rw [eq_bot_iff, ← c.D_inf_X hB]
    exact inf_le_inf_right _ inf_le_left
  have hX : Nat.card c.X = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
    rw [Nat.card_congr c.φX.toEquiv, SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_eq_fintype_card (α := c.k), c.card_k]
    ring_nf
  rw [hinf, card_bot, mul_one, sup_comm, c.X_sup_D_inf_Kc hB, c.card_D_inf_Kc hB, hX] at h2
  exact h2

theorem card_L₁_inf_centralizer_t :
    Nat.card (d.L₁ ⊓ centralizer ({d.t} : Set G) : Subgroup G) = Nat.card c.Kc := by
  have hδ : Nat.card ((c.δ hB).range) = Nat.card c.Kc :=
    Nat.card_congr (MonoidHom.ofInjective (c.injective_δ hB)).toEquiv.symm
  rwa [c.range_δ hB] at hδ

end CaseBData

namespace CaseBHyp

variable (hB : d.CaseBHyp)
include hB

theorem A₃_le_L₁ : d.A₃ ≤ d.L₁ := by
  obtain ⟨c⟩ := hB.nonempty_caseBData
  exact d.A₃_le_P.trans (c.P_le_S.trans (c.S_le_L₁ hB))

theorem L₁_inf_centralizer_t : d.L₁ ⊓ centralizer ({d.t} : Set G) = d.A₃ ⊔ d.N₁ := by
  obtain ⟨c⟩ := hB.nonempty_caseBData
  have hle : d.A₃ ⊔ d.N₁ ≤ d.L₁ ⊓ centralizer ({d.t} : Set G) :=
    le_inf (sup_le hB.A₃_le_L₁ d.N₁_le_L₁)
      (sup_le ((d.pull_le_L _).trans hB.hyp.L_le_centralizer)
        ((d.pull_le_L _).trans hB.hyp.L_le_centralizer))
  have hA₃N₁ : d.A₃ ⊓ d.N₁ = ⊥ := by
    have h := (d.sec2_1_two hB.hyp.two_le).2.2.2.2.2.2.2.2.2.2.2.2
    rw [eq_bot_iff, ← h]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans d.A₃_le_P)
      (inf_le_right.trans d.N₁_le_centralizer_I₁))
  have hcard := Common.card_sup_mul_card_inf_eq (A := d.A₃) (B := d.N₁) d.N₁_le_normalizer_A₃
  rw [hA₃N₁, card_bot, mul_one, d.card_A₃, d.card_N₁] at hcard
  exact (eq_of_le_of_card_ge hle (by
    rw [c.card_L₁_inf_centralizer_t hB, c.card_Kc hB, hcard])).symm

end CaseBHyp

end Data

end CFSG.LocalAnalysis.EvenBN.U5
