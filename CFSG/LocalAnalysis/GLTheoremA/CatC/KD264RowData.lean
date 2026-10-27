module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264GenCore
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem kd264RowData_of_central {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hno3 : ∀ S : Subgroup T, IsElemAbelian p S → Nat.card S < p ^ 3)
    (z₀ : T) (hz₀ : orderOf z₀ = p) (P₀ : Sylow p T) (hzP : ∀ g ∈ (P₀ : Subgroup T), g * z₀ = z₀ * g)
    {J₀ : Subgroup T} (hJ₀ : GLAPComponent p (Subgroup.centralizer ({z₀} : Set T)) J₀) :
    KD264RowData p T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA hAmax k hk1 hk2 hAk
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  swap
  · exact absurd (hno3 A hA) (not_lt.2 hAk)
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hA
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T P₀ S
  set z : T := g * z₀ * g⁻¹ with hz
  have hmemS : ∀ a ∈ (S : Subgroup T), ∃ b ∈ (P₀ : Subgroup T), g * b * g⁻¹ = a := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, hb, hba⟩ := ha
    exact ⟨b, hb, by rw [← hba, MulAut.smul_def, MulAut.conj_apply]⟩
  have hzA : ∀ a ∈ A, a * z = z * a := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := hmemS a (hAS ha)
    calc g * b * g⁻¹ * (g * z₀ * g⁻¹) = g * (b * z₀) * g⁻¹ := by group
      _ = g * (z₀ * b) * g⁻¹ := by rw [hzP b hb]
      _ = (g * z₀ * g⁻¹) * (g * b * g⁻¹) := by group
  have hzo : orderOf z = p := by
    rw [hz, show g * z₀ * g⁻¹ = MulAut.conj g z₀ from rfl, MulEquiv.orderOf_eq, hz₀]
  have hZel : IsElemAbelian p (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hzo]; exact pow_orderOf_eq_one z)
  have hAC : A ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup T) : Set T) := by
    intro a ha
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hzA a ha
  have hsup := CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hA hZel hAC
  have hle := hAmax _ hsup
  have heq : A = A ⊔ Subgroup.zpowers z := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hzA' : Subgroup.zpowers z ≤ A := heq ▸ le_sup_right
  refine ⟨Subgroup.zpowers z, hzA', by rw [Nat.card_zpowers, hzo, pow_one], ?_⟩
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hmap := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj g) hJ₀
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj g) z₀] at hmap
  exact ⟨_, hmap⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
