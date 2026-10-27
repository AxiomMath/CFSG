module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

namespace B2FamAlt

theorem glaPPrimeCoreOf_fixSubgroup_eq_bot_of_oddCore {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a) (β : MulAut S)
    (h : CFSG.oddCore ↥(Subgroup.centralizer ({β} : Set (MulAut S))) = ⊥) :
    GLAPPrimeCoreOf 2 (fixSubgroup β) = ⊥ := by
  set C := fixSubgroup β with hC
  set O := GLAPPrimeCoreOf 2 C with hOdef
  set κ : S →* MulAut S := MulAut.conj with hκ
  have hinj : Function.Injective κ :=
    CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hnc
  set Cβ := Subgroup.centralizer ({β} : Set (MulAut S)) with hCβ
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hconj : ∀ (γ : MulAut S) (s : S), γ * κ s * γ⁻¹ = κ (γ s) := by
    intro γ s
    ext x
    simp [hκ, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have hκC : O.map κ ≤ Cβ := by
    rintro _ ⟨o, ho, rfl⟩
    have hfix : β o = o := hOC ho
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hconj β o
    rw [hfix] at this
    calc κ o * β = β * κ o * β⁻¹ * β := by rw [this]
      _ = β * κ o := by group
  have hγO : ∀ γ : MulAut S, γ ∈ Cβ → ∀ o ∈ O, γ o ∈ O := by
    intro γ hγ o ho
    have hcomm : γ * β = β * γ := Subgroup.mem_centralizer_singleton_iff.mp hγ
    have hCγ : C.map γ.toMonoidHom = C := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : β c = c := hc
        show β (γ c) = γ c
        have := congrArg (fun f : MulAut S => f c) hcomm
        simp only [MulAut.mul_apply] at this
        rw [← this, hc']
      · intro hx
        have hx' : β x = x := hx
        refine ⟨γ⁻¹ x, ?_, by simp⟩
        show β (γ⁻¹ x) = γ⁻¹ x
        have hcomm' : γ⁻¹ * β = β * γ⁻¹ := by
          calc γ⁻¹ * β = γ⁻¹ * (β * γ) * γ⁻¹ := by group
            _ = γ⁻¹ * (γ * β) * γ⁻¹ := by rw [hcomm]
            _ = β * γ⁻¹ := by group
        have := congrArg (fun f : MulAut S => f x) hcomm'
        simp only [MulAut.mul_apply] at this
        rw [← this, hx']
    have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 2
      γ.toMonoidHom γ.injective C
    rw [hCγ] at hmap
    rw [← hOdef] at hmap
    rw [← hmap]
    exact ⟨o, ho, rfl⟩
  set T : Subgroup ↥Cβ := (O.map κ).subgroupOf Cβ with hT
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    obtain ⟨o, ho, hto⟩ := ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hto, hconj]
    exact ⟨_, hγO g g.2 o ho, rfl⟩
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T = Nat.card (O.map κ) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hκC).toEquiv
    rw [h1, Subgroup.card_map_of_injective hinj]
    exact Nat.coprime_two_left.mp (i183_coprime_card_glaPPrimeCoreOf Nat.prime_two C)
  have hTbot : T = ⊥ := by
    have hle : T ≤ CFSG.oddCore ↥Cβ := le_sSup ⟨hTn, hTodd⟩
    rw [h] at hle
    exact le_bot_iff.mp hle
  refine eq_bot_iff.mpr fun o ho => ?_
  have hmem : (⟨κ o, hκC ⟨o, ho, rfl⟩⟩ : ↥Cβ) ∈ T := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact ⟨o, ho, rfl⟩
  rw [hTbot, Subgroup.mem_bot] at hmem
  have : κ o = 1 := congrArg Subtype.val hmem
  exact (Subgroup.mem_bot).mpr (hinj (this.trans (map_one κ).symm))

theorem commutator_eq_bot_of_oddCore {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (β : MulAut S)
    (h : β ≠ 1 → CFSG.oddCore ↥(Subgroup.centralizer ({β} : Set (MulAut S))) = ⊥) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  by_cases h1 : β = 1
  · subst h1
    exact commutator_glaPLayer_eq_bot_of_perfect_le_layer (perfectInLayer_one hnc)
  rw [glaPPrimeCoreOf_fixSubgroup_eq_bot_of_oddCore hnc β (h h1), Subgroup.commutator_bot_right]

theorem commutator_eq_bot_of_isSolvable {S : Type} [Group S] [Finite S] (β : MulAut S)
    (h : Group.IsSolvable (fixSubgroup β)) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  rw [glaPLayer_eq_bot_of_isSolvable Nat.prime_two, Subgroup.commutator_bot_left]

end B2FamAlt

end CFSG.HardMathSupport.Solomon.Coordinator
