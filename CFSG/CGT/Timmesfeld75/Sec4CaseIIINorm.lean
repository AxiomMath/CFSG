module

public import CFSG.CGT.Timmesfeld75.Sec3EightFixed
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.exists_conj_not_comm [IsSimpleGroup G]
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hnab : ∃ a b : G, a * b ≠ b * a) (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), ∃ x ∈ conjSubgroup g (normIn T₁ T),
      ∃ l ∈ normIn T T₁, x * l ≠ l * x := by
  by_contra hcon
  push Not at hcon
  have hS := h.sec3
  have hcard : Nat.card T = Nat.card (normIn T T₁) * 2 := by rw [hq, mul_comm]
  have hLn : ∀ g ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup g (normIn T T₁) = normIn T T₁ := by
    intro g hg
    apply conjSubgroup_eq_of_le
    intro y hy
    obtain ⟨l, hl, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
    have hyT : g * l * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hg (normIn_le T T₁ hl)
    have hyC : g * l * g⁻¹ ∈ Subgroup.centralizer (normIn T₁ T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hginv : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hg
      have hx : g⁻¹ * e * g⁻¹⁻¹ ∈ conjSubgroup g⁻¹ (normIn T₁ T) :=
        conj_mem_conjSubgroup g⁻¹ he
      have := hcon g⁻¹ hginv _ hx l hl
      calc e * (g * l * g⁻¹) = g * (g⁻¹ * e * g⁻¹⁻¹ * l) * g⁻¹ := by group
        _ = g * (l * (g⁻¹ * e * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
        _ = (g * l * g⁻¹) * e := by group
    rw [← hS.cfg.inf_centralizer_normIn]
    exact ⟨hyT, hyC⟩
  exact false_of_normal hTO hBW h214 hInv hnab hS hcard hLn

end CFSG.CGT.Timmesfeld75
