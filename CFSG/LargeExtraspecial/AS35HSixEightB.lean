module

public import CFSG.LargeExtraspecial.AS35EResid
public import CFSG.LargeExtraspecial.AS35HQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace S14

@[expose] def SixFiveTransvectionStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
    (∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, a * b = b * a → a ≠ b →
      ∃ c ∈ S.DbarAsc, c * a = a * c ∧ c * b ≠ b * c) ∧
    (∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, orderOf (a * b) = 3 →
      ∃ c ∈ S.DbarAsc, c * a = a * c ∧ c * b = b * c)

@[expose] def AschbacherFiveNineOneStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
    ∀ t ∈ S.DSet, S.z ∈ oTwoCent (S.z * t)

@[expose] def AschTwoAutStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Setting H), 2 ≤ T.width → T.AschTwo →
    (∀ α : H ≃* H, (∀ q ∈ T.QG, α q = q) →
      (∀ g : H, α (g * T.z * g⁻¹) = g * T.z * g⁻¹) ∨
        ∀ g : H, α (g * T.z * g⁻¹) = T.z * (g * T.z * g⁻¹) * T.z⁻¹) ∧
    (∀ g : H, ∃ l ∈ T.zGen, g * T.z * g⁻¹ = l * T.z * l⁻¹) ∧
    Nat.card (CFSG.Open.timmesfeldPSU (T.width + 2)) ≤ Nat.card T.zGen

end S14

namespace CQuot

variable {G : Type} [Group G] {x : G}

theorem conj_commute_of_inv {g c : G} (hg : g * x * g⁻¹ = x⁻¹)
    (hc : c * x = x * c) : g * c * g⁻¹ * x = x * (g * c * g⁻¹) := by
  have h1 : g * x⁻¹ * g⁻¹ = x := by
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = x := by rw [hg, inv_inv]
  have hc' : c * x⁻¹ = x⁻¹ * c := by
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hc]
      _ = x⁻¹ * c := by group
  calc g * c * g⁻¹ * x = g * c * g⁻¹ * (g * x⁻¹ * g⁻¹) := by rw [h1]
    _ = g * (c * x⁻¹) * g⁻¹ := by group
    _ = g * (x⁻¹ * c) * g⁻¹ := by rw [hc']
    _ = (g * x⁻¹ * g⁻¹) * (g * c * g⁻¹) := by group
    _ = x * (g * c * g⁻¹) := by rw [h1]

theorem inv_conj_of_inv {g : G} (hg : g * x * g⁻¹ = x⁻¹) :
    g⁻¹ * x * g⁻¹⁻¹ = x⁻¹ := by
  calc g⁻¹ * x * g⁻¹⁻¹ = (g⁻¹ * x⁻¹ * g)⁻¹ := by group
    _ = (g⁻¹ * (g * x * g⁻¹) * g)⁻¹ := by rw [hg]
    _ = x⁻¹ := by group

@[expose] def conjCx (g : G) (hg : g * x * g⁻¹ = x⁻¹) : Cx x ≃* Cx x where
  toFun c := ⟨g * c * g⁻¹, mem_centralizer_singleton_iff.mpr
    (conj_commute_of_inv hg (mem_centralizer_singleton_iff.mp c.2))⟩
  invFun c := ⟨g⁻¹ * c * g⁻¹⁻¹, mem_centralizer_singleton_iff.mpr
    (conj_commute_of_inv (inv_conj_of_inv hg) (mem_centralizer_singleton_iff.mp c.2))⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by
    change g * (a * b : G) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹)
    group)

@[simp] theorem coe_conjCx (g : G) (hg : g * x * g⁻¹ = x⁻¹) (c : Cx x) :
    ((conjCx g hg c : Cx x) : G) = g * c * g⁻¹ := rfl

theorem conj_mem_oTwoCent_conj {G : Type} [Group G] {a y : G} (g : G) (hy : y ∈ oTwoCent a) :
    g * y * g⁻¹ ∈ oTwoCent (g * a * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_oTwoCent (P := (oTwoCent a).map (MulAut.conj g).toMonoidHom) ?_ ?_
    ((isPGroup_oTwoCent a).map _) ⟨y, hy, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hw' := mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer a hw)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * (g * a * g⁻¹) = g * (w * a) * g⁻¹ := by group
      _ = g * (a * w) * g⁻¹ := by rw [hw']
      _ = g * a * g⁻¹ * (g * w * g⁻¹) := by group
  · rintro c hc _ ⟨w, hw, rfl⟩
    have hc' : g⁻¹ * c * g ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      calc g⁻¹ * c * g * a = g⁻¹ * (c * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * c) * g := by rw [hc]
        _ = a * (g⁻¹ * c * g) := by group
    refine ⟨g⁻¹ * c * g * w * (g⁻¹ * c * g)⁻¹, conj_mem_oTwoCent hc' hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end CQuot

end CFSG.LargeExtraspecial
