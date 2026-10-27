module

import CFSG.GroupTheory.ThompsonAxB
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt

theorem N10 :
    ∀ (G : Type) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P R B : Subgroup G), IsPGroup p P →
      Nat.Coprime (Nat.card R) p → IsPGroup p B → R ≤ Subgroup.normalizer (P : Set G) →
      B ≤ Subgroup.normalizer (P : Set G) → ⁅R, B⁆ = ⊥ →
      P ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (R : Set G) →
      P ≤ Subgroup.centralizer (R : Set G) := by
  intro G _ _ p _ P R B hP hR hB hRP hBP hRB hfix
  have hRB' : R ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : G) = r * x * (r : G)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : G) = b * x * (b : G)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : G) * r = r * b := Subgroup.mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : G) * (b * x * (b : G)⁻¹) * (r : G)⁻¹ = (r * b) * x * ((r : G) * b)⁻¹ := by
          group
      _ = (b * r) * x * ((b : G) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : G) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : G) * x = x * r :=
      Subgroup.mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : G)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

end CFSG.Goldschmidt
