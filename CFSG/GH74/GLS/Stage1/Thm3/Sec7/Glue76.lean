module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue73

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem sq_prod_eq_one {a b z : G} (hz : z * z = 1) (h1 : a * a = z) (h2 : b * b = z)
    (hc : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [h1, h2]; exact hz

namespace Cfg7

theorem t_mul_z (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : t * z = z * t :=
  Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII h.ch.t_mem)

theorem w₀_facts (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {u₁ : G}
    (hu₁P : u₁ ∈ Pof S K₁) (hu₁sq : u₁ * u₁ = z) :
    (u₁ * (t * u₁ * t⁻¹)) * (u₁ * (t * u₁ * t⁻¹)) = 1 ∧ u₁ * (t * u₁ * t⁻¹) ≠ 1 := by
  have hu₂P : t * u₁ * t⁻¹ ∈ Pof S K₂ := h.tP₁ u₁ hu₁P
  have hcomm : u₁ * (t * u₁ * t⁻¹) = (t * u₁ * t⁻¹) * u₁ := h.P_comm hII u₁ hu₁P _ hu₂P
  have htz : t * z * t⁻¹ = z := by
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [h.t_mul_z hII]
      _ = z := by group
  have hu₂sq : (t * u₁ * t⁻¹) * (t * u₁ * t⁻¹) = z := by
    have : (t * u₁ * t⁻¹) * (t * u₁ * t⁻¹) = t * (u₁ * u₁) * t⁻¹ := by group
    rw [this, hu₁sq, htz]
  refine ⟨sq_prod_eq_one h.z_sq hu₁sq hu₂sq hcomm, ?_⟩
  intro h1
  have h2 : t * u₁ * t⁻¹ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : u₁⁻¹ ∈ Pof S K₁ := (Pof S K₁).inv_mem hu₁P
  have h4 : u₁⁻¹ ∈ zpowers z := (h.P_inf hII).le ⟨h3, h2 ▸ hu₂P⟩
  have h5 : u₁ ∈ zpowers z := by simpa using (zpowers z).inv_mem h4
  exact C73.sq_not_mem_zpowers h.z_sq h.z_ne hu₁sq h5

end Cfg7

theorem lemma_7_6 (hII : II4_4_4_center) (hL76 : L76_struct) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (t u : G) (q : ℕ),
      Cfg7 G z S K₁ K₂ t u q → Concl73 z S K₁ K₂ → Concl74c z t → (Pz S z).relIndex (S1 S K₁) = 2 →
        ∀ D : Subgroup G, Data74 z S K₁ K₂ t D → (∃ n, IVK.IsSemidihedralTwoGroup ↥D n) →
          16 ≤ Nat.card ↥(Pof S K₁) → ∀ d₀ : G, (center ↥D).map D.subtype = zpowers d₀ →
            Concl76 z S t D d₀ := by
  intro G _ _ z S K₁ K₂ t u q h hc73 hc74 hidx D hD hsd h16 d₀ hd₀
  obtain ⟨u₁, hu₁P, hu₁sq, -, hcen, ⟨y, hyD, hyP, hyy, -⟩, hinv⟩ :=
    hL76 G z S K₁ K₂ t u q h hidx D hD hsd h16
  obtain ⟨hw₀sq, hw₀ne⟩ := h.w₀_facts hII hu₁P hu₁sq
  have hd : d₀ = u₁ * (t * u₁ * t⁻¹) := by
    have h1 : zpowers d₀ = zpowers (u₁ * (t * u₁ * t⁻¹)) := hd₀.symm.trans hcen
    have h2 : d₀ ∈ zpowers (u₁ * (t * u₁ * t⁻¹)) := h1 ▸ mem_zpowers d₀
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
    rcases B.zpow_of_sq_eq_one hw₀sq k with h3 | h3
    · exfalso
      have h4 : d₀ = 1 := hk.symm.trans h3
      have h5 : u₁ * (t * u₁ * t⁻¹) ∈ zpowers (1 : G) := by
        rw [h4] at h1
        exact h1 ▸ mem_zpowers _
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h5
      exact hw₀ne h5
    · exact hk.symm.trans h3
  refine ⟨?_, ⟨y, hyD, hyP, hd ▸ hyy⟩, hinv⟩
  rw [hd]
  have h4 : u₁ * u₁ * u₁ * u₁ = 1 := by
    calc u₁ * u₁ * u₁ * u₁ = (u₁ * u₁) * (u₁ * u₁) := by group
      _ = z * z := by rw [hu₁sq]
      _ = 1 := h.z_sq
  have hzu : z * u₁ = u₁⁻¹ := by
    rw [← hu₁sq]
    exact eq_inv_of_mul_eq_one_left h4
  have key : z * (u₁ * (t * u₁ * t⁻¹)) * t = u₁⁻¹ * t * u₁ := by
    calc z * (u₁ * (t * u₁ * t⁻¹)) * t = (z * u₁) * (t * u₁) := by group
      _ = u₁⁻¹ * (t * u₁) := by rw [hzu]
      _ = u₁⁻¹ * t * u₁ := by group
  rw [key]
  exact h.ch.t_conj.trans (isConj_iff.2 ⟨u₁⁻¹, by simp⟩)

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
