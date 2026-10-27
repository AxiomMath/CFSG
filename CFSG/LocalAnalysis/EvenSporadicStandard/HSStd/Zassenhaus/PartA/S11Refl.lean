module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Rho

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Refl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
variable (hb : PAB G L t E W z) (a : PA10 L t E z)

structure S11XData {x : G} (hx : x ∈ a.L₁) (X : Subgroup G) : Prop where
  le : X ≤ a.L₁ ⊓ centralizer ({x} : Set G)
  card : Nat.card X = 9
  three : ∀ g ∈ a.L₁ ⊓ centralizer ({x} : Set G), orderOf g = 3 → g ∈ X
  cube : ∀ g ∈ X, g ^ 3 = 1
  ab : ∀ g ∈ X, ∀ h ∈ X, g * h = h * g
  lift : ∀ b ∈ centralizer ({s11Pi a.L₁ (S11_e a) ⟨x, hx⟩} : Set (alternatingGroup (Fin 6))),
    ∃ c : ↥a.L₁, (c : G) ∈ X ∧ s11Pi a.L₁ (S11_e a) c = b

include hb in
theorem S11_exists_XData {x : G} (hx : x ∈ a.L₁) (hx3 : orderOf x = 3) :
    ∃ X : Subgroup G, S11XData a hx X := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, -, -⟩ := s11_exists_X (e := S11_e a) (S11_u_sq hb a)
    (S11_hZ hb a) hx hx3
  exact ⟨X, ⟨h1, h2, h3, h4, h5, h6⟩⟩

variable {a} {x : G} {hx : x ∈ a.L₁} {X : Subgroup G}

theorem S11XData.le_L₁ (h : S11XData a hx X) : X ≤ a.L₁ := fun _ hg => (h.le hg).1

theorem S11XData.mem_x (h : S11XData a hx X) (hx3 : orderOf x = 3) : x ∈ X :=
  h.three x ⟨hx, mem_centralizer_singleton_iff.2 rfl⟩ hx3

theorem S11XData.conj_le (h : S11XData a hx X) : conjSub t X ≤ conjSub t a.L₁ :=
  Subgroup.map_mono h.le_L₁

include hb in
theorem S11XData.comm (h : S11XData a hx X) : ∀ p ∈ X, ∀ q ∈ conjSub t X, p * q = q * p :=
  fun p hp q hq => S11_comm_L₁t hb a p (h.le_L₁ hp) q (h.conj_le hq)

include hb in
theorem S11XData.inf (h : S11XData a hx X) : ∀ g ∈ X, g ∈ conjSub t X → g = 1 := by
  intro g hg hgt
  have hu := S11_inter_le hb a (h.le_L₁ hg) (h.conj_le hgt)
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hu
  have h3 := h.cube g hg
  have h2 : g * g = 1 := by
    rw [← hn, ← zpow_add, ← two_mul, zpow_mul]
    have : a.u ^ (2 : ℤ) = 1 := by rw [zpow_two, S11_u_sq hb a]
    rw [this, one_zpow]
  calc g = g ^ 3 := by rw [pow_succ, pow_two, h2, one_mul]
    _ = 1 := h3

include hb in
theorem S11_T_facts (h : S11XData a hx X) (hxy : a.y = x * (t * x * t⁻¹)) :
    Nat.card ↥(X ⊔ conjSub t X) = 81 ∧ X ⊔ conjSub t X ≤ Cen a.y ⊓ Cen a.u := by
  have hcm : Cm X (conjSub t X) := fun p hp =>
    mem_centralizer_iff.2 fun q hq => (h.comm hb p hp q hq).symm
  have hbot : X ⊓ conjSub t X = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact h.inf hb g hg.1 hg.2
  have hXt : Nat.card (conjSub t X) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, h.card]
  refine ⟨by rw [card_sup_of_cm hcm hbot, hXt, h.card], ?_⟩
  have hxt : t * x * t⁻¹ ∈ conjSub t a.L₁ := ⟨x, hx, rfl⟩
  refine sup_le ?_ ?_
  · intro g hg
    have hgL := h.le_L₁ hg
    refine ⟨mem_Cen.2 ?_, mem_Cen.2 (S11_L₁_u hb a g hgL)⟩
    rw [hxy]
    have h1 : g * x = x * g := mem_centralizer_singleton_iff.1 (h.le hg).2
    have h2 : g * (t * x * t⁻¹) = (t * x * t⁻¹) * g := S11_comm_L₁t hb a g hgL _ hxt
    calc g * (x * (t * x * t⁻¹)) = (g * x) * (t * x * t⁻¹) := (mul_assoc _ _ _).symm
      _ = x * (g * (t * x * t⁻¹)) := by rw [h1, mul_assoc]
      _ = x * ((t * x * t⁻¹) * g) := by rw [h2]
      _ = (x * (t * x * t⁻¹)) * g := (mul_assoc _ _ _).symm
  · rintro _ ⟨g, hg, rfl⟩
    have hgL := h.le_L₁ hg
    have hq : (MulAut.conj t).toMonoidHom g = t * g * t⁻¹ := rfl
    have hqL : t * g * t⁻¹ ∈ conjSub t a.L₁ := ⟨g, hgL, rfl⟩
    refine ⟨mem_Cen.2 ?_, mem_Cen.2 ?_⟩
    · rw [hq, hxy]
      have h1 : g * x = x * g := mem_centralizer_singleton_iff.1 (h.le hg).2
      have h2 : (t * g * t⁻¹) * x = x * (t * g * t⁻¹) :=
        (S11_comm_L₁t hb a x hx _ hqL).symm
      have h3 : (t * g * t⁻¹) * (t * x * t⁻¹) = (t * x * t⁻¹) * (t * g * t⁻¹) := by
        calc (t * g * t⁻¹) * (t * x * t⁻¹) = t * (g * x) * t⁻¹ := by group
          _ = t * (x * g) * t⁻¹ := by rw [h1]
          _ = (t * x * t⁻¹) * (t * g * t⁻¹) := by group
      calc (t * g * t⁻¹) * (x * (t * x * t⁻¹)) = ((t * g * t⁻¹) * x) * (t * x * t⁻¹) :=
            (mul_assoc _ _ _).symm
        _ = x * ((t * g * t⁻¹) * (t * x * t⁻¹)) := by rw [h2, mul_assoc]
        _ = x * ((t * x * t⁻¹) * (t * g * t⁻¹)) := by rw [h3]
        _ = (x * (t * x * t⁻¹)) * (t * g * t⁻¹) := (mul_assoc _ _ _).symm
    · exact S11_conj_u hb a g hgL

include hb in
theorem S11_card_C0 (hx : x ∈ a.L₁) (hx3 : orderOf x = 3) (hxy : a.y = x * (t * x * t⁻¹)) :
    Nat.card (centralizer ({S11_rhoBar hb a ⟨a.y, S11_y_mem_Cen hb a⟩} :
      Set (Wr2 (MulAut (alternatingGroup (Fin 6)))))) = 648 := by
  have hπ := S11_pi_x_ord hb a hx hx3
  rw [S11_rho_y hb a hx hxy, card_centralizer_base_self,
    card_centralizer_conj_of_orderOf_eq_three hπ]
  norm_num

include hb in
theorem S11_card_B_le (hx : x ∈ a.L₁) (hx3 : orderOf x = 3) (hxy : a.y = x * (t * x * t⁻¹)) :
    Nat.card ↥(Cen a.y ⊓ Cen a.u) ≤ 4 * 648 := by
  have hy := S11_y_mem_Cen hb a
  have h1 := card_centralizer_le_card_ker_mul (S11_rhoBar hb a) (⟨a.y, hy⟩ : ↥(Cen a.u))
  have h2 : Nat.card (centralizer ({(⟨a.y, hy⟩ : ↥(Cen a.u))} : Set ↥(Cen a.u))) =
      Nat.card ↥(Cen a.u ⊓ Cen a.y) := card_centralizer_subtype (Cen a.u) hy
  have h3 : Nat.card ↥(Cen a.u ⊓ Cen a.y) = Nat.card ↥(Cen a.y ⊓ Cen a.u) := by
    rw [inf_comm]
  have h4 := S11_card_C0 hb hx hx3 hxy
  have h5 : Nat.card (centralizer ({S11_rhoBar hb a ⟨a.y, hy⟩} :
      Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) ⊓ (S11_rhoBar hb a).range :
      Subgroup (Wr2 (MulAut (alternatingGroup (Fin 6))))) ≤ 648 := by
    rw [← h4]
    exact Subgroup.card_le_of_le inf_le_left
  rw [← h3, ← h2]
  refine h1.trans ?_
  rw [S11_card_ker]
  exact Nat.mul_le_mul le_rfl h5

include hb in
theorem S11_card_O (h : S11XData a hx X) (hx3 : orderOf x = 3)
    (hxy : a.y = x * (t * x * t⁻¹)) : Nat.card (S11_O a) = 9 := by
  have h1 := S11_card_B hb a
  have h2 := S11_card_B_le hb hx hx3 hxy
  obtain ⟨hT, hTle⟩ := S11_T_facts hb h hxy
  have h3 : 81 ∣ Nat.card ↥(Cen a.y ⊓ Cen a.u) := hT ▸ Subgroup.card_dvd_of_le hTle
  have hpos : 0 < Nat.card (S11_O a) := Nat.card_pos
  omega

end Refl

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
