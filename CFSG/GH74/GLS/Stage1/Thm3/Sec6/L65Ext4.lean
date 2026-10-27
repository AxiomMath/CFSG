module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext3
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let Ψ : ↥A × ↥B →* G := (A.subtype).noncommCoprod (B.subtype) (fun x y => by
    show (x : G) * y = y * x
    exact hc x x.2 y y.2)
  have hΨ : ∀ x : ↥A, ∀ y : ↥B, Ψ (x, y) = (x : G) * y := fun x y => by
    simp [Ψ, MonoidHom.noncommCoprod_apply]
  have hrange : Ψ.range = A ⊔ B := by
    ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      rw [hΨ]
      exact mul_mem (mem_sup_left x.2) (mem_sup_right y.2)
    · intro hg
      obtain ⟨a, ha, b, hb, rfl⟩ := M.mem_sup_of_commute hc hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hΨ _ _⟩
  have hker : Nat.card ↥Ψ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), p.1.1.2, by
          have h1 := p.2
          rw [MonoidHom.mem_ker, hΨ, mul_eq_one_iff_eq_inv] at h1
          rw [h1]; exact B.inv_mem p.1.2.2⟩
        invFun := fun c => ⟨(⟨c, c.2.1⟩, ⟨(c : G)⁻¹, B.inv_mem c.2.2⟩), by
          rw [MonoidHom.mem_ker, hΨ]; simp⟩
        left_inv := ?_
        right_inv := fun c => rfl }
    rintro ⟨⟨x, y⟩, hxy⟩
    have h1 := hxy
    rw [MonoidHom.mem_ker, hΨ, mul_eq_one_iff_eq_inv] at h1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp only
      rw [h1, inv_inv]
  have h := Subgroup.card_ker_mul_card_range Ψ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm] at h
  exact h

section Cfg65Cards

variable {z : G} {S K₁ K₂ : Subgroup G} {t : G}

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem P₂_card (hII : II4_4_4_center) : Nat.card ↥(Pof S K₂) = 16 := by
  rw [← h.P₁_card hII]
  have hmap : Pof S K₂ = (Pof S K₁).map (MulAut.conj t).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨t * x * t⁻¹, h.t_conj_P₂ hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hsq : t * (t * x * t⁻¹) * t⁻¹ = x := by
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
          _ = x := by rw [h.t_sq, h.t_inv, h.t_sq]; group
      exact hsq
    · rintro ⟨y, hy, rfl⟩
      exact h.t_conj_P₁ hy
  rw [hmap]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective

theorem P_card (hII : II4_4_4_center) : Nat.card ↥(Pz S z) = 128 := by
  have hz2 : orderOf z = 2 := h.std.orderOf_z
  have h1 := card_sup_mul_card_inf (h.P_comm hII)
  rw [h.P_inf hII, Nat.card_zpowers, hz2, h.P₁_card hII, h.P₂_card hII] at h1
  rw [h.Pz_eq_sup hII]
  omega

theorem S_card_le (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) :
    Nat.card ↥S ≤ 256 := by
  classical
  have hP := h.P_card hII
  have hinj : Function.Injective
      (fun s : ↥S => if hs : (s : G) ∈ Pz S z then
          (Sum.inl ⟨(s : G), hs⟩ : ↥(Pz S z) ⊕ ↥(Pz S z))
        else Sum.inr ⟨(s : G) * t, ((h.S_cases hII h4hij s.2).resolve_left hs)⟩) := by
    intro s s' hss
    by_cases hs : (s : G) ∈ Pz S z <;> by_cases hs' : (s' : G) ∈ Pz S z
    · simp [hs, hs'] at hss
      exact hss
    · simp [hs, hs'] at hss
    · simp [hs, hs'] at hss
    · simp [hs, hs'] at hss
      exact hss
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_sum, hP] at this
  omega

theorem C_card_le (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer)
    {a b : G} (hAB : AB65 S K₁ a b) (hrec : Bg.B_reciprocity) :
    Nat.card ↥(S ⊓ centralizer ({uElt t a} : Set G)) ≤ 128 := by
  have h1 := (h.u_extremal hAB hII h4hij hrec).2
  have h2 := h.S_card_le hII h4hij
  omega

end Cfg65

end Cfg65Cards

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
