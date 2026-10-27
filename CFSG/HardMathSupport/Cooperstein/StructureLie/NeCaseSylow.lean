module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Defs
import CFSG.Quasithin.Background.F9Comp
import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput hiding centerIn

section Gamma

variable {Γ : Type} [Group Γ]

theorem comm_of_mem_centerIn {L : Subgroup Γ} {z l : Γ} (hz : z ∈ LieInput.centerIn L) (hl : l ∈ L) :
    z * l = l * z := by
  unfold LieInput.centerIn at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  have := Subgroup.mem_center_iff.1 hz' ⟨l, hl⟩
  exact (congrArg Subtype.val this).symm

theorem exists_mul_of_mem_sup_centerIn {L R : Subgroup Γ} (hRL : R ≤ L) {x : Γ}
    (hx : x ∈ R ⊔ LieInput.centerIn L) : ∃ r ∈ R, ∃ z ∈ LieInput.centerIn L, x = r * z := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, (LieInput.centerIn L).one_mem, by simp⟩
    · exact ⟨1, R.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, R.one_mem, 1, (LieInput.centerIn L).one_mem, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, hr, z, hz, rfl⟩ := ha
    obtain ⟨r', hr', z', hz', rfl⟩ := hb
    refine ⟨r * r', R.mul_mem hr hr', z * z', (LieInput.centerIn L).mul_mem hz hz', ?_⟩
    have := comm_of_mem_centerIn hz (hRL hr')
    calc r * z * (r' * z') = r * (z * r') * z' := by group
      _ = r * (r' * z) * z' := by rw [this]
      _ = r * r' * (z * z') := by group
  | inv a _ ha =>
    obtain ⟨r, hr, z, hz, rfl⟩ := ha
    refine ⟨r⁻¹, R.inv_mem hr, z⁻¹, (LieInput.centerIn L).inv_mem hz, ?_⟩
    have := comm_of_mem_centerIn hz (hRL hr)
    calc (r * z)⁻¹ = z⁻¹ * r⁻¹ := by group
      _ = r⁻¹ * z⁻¹ := by
        have h2 : r * z = z * r := this.symm
        calc z⁻¹ * r⁻¹ = (r * z)⁻¹ := by group
          _ = (z * r)⁻¹ := by rw [h2]
          _ = r⁻¹ * z⁻¹ := by group

end Gamma

section XLevel

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem pCoreOf_top_bar : pCoreOf 2 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) = ⊥ := by
  rw [CFSG.Quasithin.Fan86.Model.pCoreOf_top_eq]
  exact CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2

theorem inf_normalizer_ne_of_ne_bot (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hne : barM X (S ⊓ L) ≠ ⊥) :
    barM X L ⊓ Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ≠ barM X L := by
  intro h
  have hLN : barM X L ≤ Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    inf_eq_left.1 h
  have hQ : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hRL : barM X (S ⊓ L) ≤ barM X L := by
    rw [barM_inf hQ]
    exact inf_le_right
  have hRp : IsPGroup 2 (barM X (S ⊓ L)) :=
    isPGroup_barM (hA.twoRadical.isPGroup.to_le inf_le_left)
  have h1 : barM X (S ⊓ L) ≤ pCoreOf 2 (barM X L) :=
    CFSG.HardMathSupport.Cooperstein.Proving.le_pCoreOf_of_normal_in hRL
      (fun h hh a ha => (Subgroup.mem_normalizer_iff.1 (hLN hh) a).1 ha) hRp
  have h2 : pCoreOf 2 (barM X L) ≤ pCoreOf 2 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hL.component.2.1
  rw [pCoreOf_top_bar] at h2
  exact hne (le_bot_iff.1 (h1.trans h2))

end XLevel

end CFSG.HardMathSupport.Cooperstein.StructureLie
