module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem t_mem_W : t ∈ W :=
  hc.U_le (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))

theorem T_le_W : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hc.U_le

theorem t_not_comm : ¬ (t * z₁ = z₁ * t) := fun h1 => hc.z₁_ne (by
  rw [h1, mul_assoc, mul_inv_cancel, mul_one])

theorem relIndex_W₀ : (W ⊓ centralizer {z₁}).relIndex W = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, hc.t_mem_W⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf, mem_centralizer_singleton_iff]
  by_cases hb : (b : X) * z₁ = z₁ * b
  · right
    refine ⟨⟨b.2, hb⟩, fun ⟨_, hbt⟩ => hc.t_not_comm ?_⟩
    calc t * z₁ = (b : X)⁻¹ * ((b * t) * z₁) := by group
      _ = (b : X)⁻¹ * (z₁ * (b * t)) := by rw [hbt]
      _ = (b : X)⁻¹ * (z₁ * b) * t := by group
      _ = (b : X)⁻¹ * (b * z₁) * t := by rw [hb]
      _ = z₁ * t := by group
  · left
    exact ⟨⟨mul_mem b.2 hc.t_mem_W, hc.mul_t b b.2 hb⟩, fun ⟨_, h1⟩ => hb h1⟩

theorem conj_mem_W₀ {g x : X} (hg : g ∈ W) (hx : x ∈ W ⊓ centralizer {z₁}) :
    g * x * g⁻¹ ∈ W ⊓ centralizer {z₁} := by
  have hn := Subgroup.normal_of_index_eq_two hc.relIndex_W₀
  exact hn.conj_mem ⟨x, hx.1⟩ hx ⟨g, hg⟩

theorem card_W₀ : 2 * Nat.card ↥(W ⊓ centralizer {z₁}) = Nat.card W := by
  have h1 := Subgroup.relIndex_mul_card (H := W ⊓ centralizer {z₁}) (K := W)
  rw [hc.relIndex_W₀, inf_of_le_left (inf_le_left : W ⊓ centralizer {z₁} ≤ W)] at h1
  exact h1

theorem W₀_le_z₂ : W ⊓ centralizer {z₁} ≤ centralizer {t * z₁ * t⁻¹} := by
  intro x hx
  have h1 := hc.conj_mem_W₀ (inv_mem hc.t_mem_W) hx
  rw [inv_inv] at h1
  have h2 : t⁻¹ * x * t * z₁ = z₁ * (t⁻¹ * x * t) := mem_centralizer_singleton_iff.mp h1.2
  rw [mem_centralizer_singleton_iff]
  calc x * (t * z₁ * t⁻¹) = t * (t⁻¹ * x * t * z₁) * t⁻¹ := by group
    _ = t * (z₁ * (t⁻¹ * x * t)) * t⁻¹ := by rw [h2]
    _ = t * z₁ * t⁻¹ * x := by group

theorem comm_z {x : X} (hx : x ∈ W) : x * z = z * x := by
  by_cases hx₁ : x * z₁ = z₁ * x
  · have hx₂ := mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ ⟨hx, mem_centralizer_singleton_iff.mpr
      hx₁⟩)
    rw [hc.z_eq]
    calc x * (z₁ * (t * z₁ * t⁻¹)) = (x * z₁) * (t * z₁ * t⁻¹) := by group
      _ = z₁ * (x * (t * z₁ * t⁻¹)) := by rw [hx₁]; group
      _ = z₁ * ((t * z₁ * t⁻¹) * x) := by rw [hx₂]
      _ = z₁ * (t * z₁ * t⁻¹) * x := by group
  ·
    have hxt := hc.mul_t x hx hx₁
    have hxt₂ := mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ ⟨mul_mem hx hc.t_mem_W,
      mem_centralizer_singleton_iff.mpr hxt⟩)
    have hxtz : x * t * z = z * (x * t) := by
      rw [hc.z_eq]
      calc x * t * (z₁ * (t * z₁ * t⁻¹)) = (x * t * z₁) * (t * z₁ * t⁻¹) := by group
        _ = z₁ * (x * t * (t * z₁ * t⁻¹)) := by rw [hxt]; group
        _ = z₁ * ((t * z₁ * t⁻¹) * (x * t)) := by rw [hxt₂]
        _ = z₁ * (t * z₁ * t⁻¹) * (x * t) := by group
    have htz : t * z = z * t := by
      have := hs.setup.z_mem.1
      exact (mem_centralizer_singleton_iff.mp (hs.sylow.le this)).symm
    calc x * z = x * t * z * t⁻¹ := by
          rw [mul_assoc x t z, htz]; group
      _ = z * (x * t) * t⁻¹ := by rw [hxtz]
      _ = z * x := by group

theorem comm_beta {x : X} (hx : x ∈ W) :
    x * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * x :=
  mem_centralizer_singleton_iff.mp (hc.isSylowOf_W.le hx)

theorem card_S_lt : Nat.card S < Nat.card ↥(W ⊓ centralizer {z₁}) := by
  have hS := (hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3).2.2.2.2.1
  have h1 := hc.card_W₀
  have h2 := hc.card_le
  have hpos : 0 < Nat.card S := Nat.card_pos
  omega

theorem not_le_centralizer_conj (g : X) :
    ¬ (W ⊓ centralizer {z₁} ≤ centralizer {g * t * g⁻¹}) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥((W ⊓ centralizer {z₁}).map (MulAut.conj g⁻¹).toMonoidHom) :=
    (hc.isSylowOf_W.isPGroup.to_le inf_le_left).map _
  have hle' : (W ⊓ centralizer {z₁}).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer ({t} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * (g * t * g⁻¹) = g * t * g⁻¹ * x := mem_centralizer_singleton_iff.mp (hle hx)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g) := by group
  have h1 := card_le_twoPart hp hle'
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
  have h2 : twoPart (centralizer ({t} : Set X)) = Nat.card S := hs.sylow.card_eq.symm
  rw [h2] at h1
  exact absurd hc.card_S_lt (not_lt.mpr h1)

end Config415

end CFSG.ComponentClassification.HarrisLit
