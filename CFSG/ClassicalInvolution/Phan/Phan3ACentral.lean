module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open Subgroup

theorem ker_le_center_of_card_lt {G S : Type*} [Group G] [Finite G] [Group S]
    (hS : CFSG.IsQuasisimple S) (p : G →* S) (hp : Function.Surjective p)
    (hcomm : ∀ x ∈ p.ker, ∀ y ∈ p.ker, x * y = y * x)
    (hbig : Nat.card (center S) * (Nat.card p.ker).factorial < Nat.card S) :
    p.ker ≤ center G := by
  classical
  have : Finite S := Finite.of_surjective p hp
  let ρ : G →* Equiv.Perm p.ker := (MulAut.toPerm p.ker).comp MulAut.conjNormal
  have hρ : ∀ c ∈ ρ.ker, ∀ x ∈ p.ker, c * x = x * c := by
    intro c hc x hx
    have h1 : ρ c ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [MonoidHom.mem_ker.mp hc]; rfl
    have h2 : c * x * c⁻¹ = x := by
      have h3 := congrArg Subtype.val h1
      change ((MulAut.conjNormal c : MulAut p.ker) ⟨x, hx⟩ : G) = x at h3
      rwa [MulAut.conjNormal_apply] at h3
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h2]
  have hidx : ρ.ker.index ≤ (Nat.card p.ker).factorial := by
    rw [Subgroup.index_ker, ← Nat.card_perm]
    exact Subgroup.card_le_card_group _
  have : (ρ.ker.map p).Normal := Subgroup.Normal.map inferInstance p hp
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hS (ρ.ker.map p) with h | h
  · exfalso
    have h1 : (ρ.ker.map p).index ≤ ρ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (ρ.ker.index_map_dvd hp)
    have h2 : Nat.card (ρ.ker.map p) ≤ Nat.card (center S) := Subgroup.card_le_of_le h
    have h3 : Nat.card S = (ρ.ker.map p).index * Nat.card (ρ.ker.map p) :=
      (Subgroup.index_mul_card _).symm
    have h4 : Nat.card S ≤ (Nat.card p.ker).factorial * Nat.card (center S) := by
      rw [h3]
      exact Nat.mul_le_mul (h1.trans hidx) h2
    rw [mul_comm] at hbig
    omega
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : p g ∈ ρ.ker.map p := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨c, hcC, hcg⟩ := hg
    have hn : c⁻¹ * g ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
    have hcx : c * x = x * c := hρ c hcC x hx
    have hnx : (c⁻¹ * g) * x = x * (c⁻¹ * g) := hcomm _ hn x hx
    calc g * x = c * ((c⁻¹ * g) * x) := by group
      _ = c * (x * (c⁻¹ * g)) := by rw [hnx]
      _ = (c * x) * (c⁻¹ * g) := by rw [← mul_assoc]
      _ = (x * c) * (c⁻¹ * g) := by rw [hcx]
      _ = x * g := by group

end CFSG.ClassicalInvolution.Phan.Q3G
