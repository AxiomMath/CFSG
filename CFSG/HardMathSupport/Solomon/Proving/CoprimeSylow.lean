module

public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_normalized_sylow_of_coprime {Y B : Subgroup G} [Finite Y] {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hB : IsPGroup p B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hpY : ¬ p ∣ Nat.card Y) :
    ∃ R : Subgroup G, IsPGroup q R ∧ R ≤ Y ∧
      (∀ R' : Subgroup G, R ≤ R' → R' ≤ Y → IsPGroup q R' → R' = R) ∧
      B ≤ Subgroup.normalizer (R : Set G) := by
  let φ : B →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hBY)
  let _ : MulAction B (Sylow q Y) := MulAction.compHom _ φ
  have hcard : ¬ p ∣ Nat.card (Sylow q Y) := by
    intro h
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow q Y))
    exact hpY (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  have hmod := IsPGroup.card_modEq_card_fixedPoints (p := p) (G := B) (α := Sylow q Y) hB
  have hne : Nat.card (MulAction.fixedPoints B (Sylow q Y)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hcard (Nat.modEq_zero_iff_dvd.1 hmod)
  obtain ⟨Pf⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  let P : Sylow q Y := Pf.1
  have hPfix : ∀ b : B, b • P = P := fun b => MulAction.mem_fixedPoints.1 Pf.2 b
  have hstab : ∀ (b : B) (y : Y), y ∈ (P : Sylow q Y).toSubgroup →
      φ b y ∈ (P : Sylow q Y).toSubgroup := by
    intro b y hy
    have h2 : (φ b) • (P : Sylow q Y).toSubgroup = (P : Sylow q Y).toSubgroup :=
      congrArg Sylow.toSubgroup (hPfix b)
    rw [← h2]
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hy, rfl⟩
  have hconj : ∀ (b : B) (x : G),
      x ∈ (P : Sylow q Y).toSubgroup.map Y.subtype →
        (b : G) * x * (b : G)⁻¹ ∈ (P : Sylow q Y).toSubgroup.map Y.subtype := by
    intro b x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_map.2 ⟨φ b y, hstab b y hy, rfl⟩
  refine ⟨(P : Sylow q Y).toSubgroup.map Y.subtype, P.isPGroup'.map Y.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro R' hRR' hR'Y hR'q
    have hP'q : IsPGroup q (R'.subgroupOf Y) :=
      IsPGroup.comap_of_injective hR'q Y.subtype (Subgroup.subtype_injective Y)
    have hPP' : (P : Sylow q Y).toSubgroup ≤ R'.subgroupOf Y := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      exact hRR' (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    have hPeq : R'.subgroupOf Y = (P : Sylow q Y).toSubgroup := P.is_maximal' hP'q hPP'
    have := congrArg (Subgroup.map Y.subtype) hPeq
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hR'Y] at this
    exact this
  · intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj ⟨b, hb⟩ x hx, fun hx => ?_⟩
    have := hconj ⟨b, hb⟩⁻¹ _ hx
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Solomon.Proving
