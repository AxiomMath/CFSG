module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGDispatch
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6ULang
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Fix
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Gen
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KGConcl)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut (kgConcl_of_mulEquiv)
open scoped Pointwise

set_option linter.unusedSectionVars false


theorem closure_fix_conj {G : Type*} [Group G] (γ φ ψ : MulAut G)
    (h : Subgroup.closure ({x : G | φ x = x} ∪ {x : G | ψ x = x}) = ⊤) :
    Subgroup.closure ({x : G | (γ * φ * γ⁻¹) x = x} ∪ {x : G | (γ * ψ * γ⁻¹) x = x}) = ⊤ := by
  have key : ∀ θ : MulAut G, {x : G | (γ * θ * γ⁻¹) x = x} = γ '' {x : G | θ x = x} := by
    intro θ
    ext x
    constructor
    · intro hx
      refine ⟨γ⁻¹ x, ?_, by simp⟩
      have : γ (θ (γ⁻¹ x)) = x := hx
      show θ (γ⁻¹ x) = γ⁻¹ x
      calc θ (γ⁻¹ x) = γ⁻¹ (γ (θ (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [this]
    · rintro ⟨y, hy, rfl⟩
      have : θ y = y := hy
      show γ (θ (γ⁻¹ (γ y))) = γ y
      simp [this]
  rw [key, key, ← Set.image_union]
  have h2 := MonoidHom.map_closure γ.toMonoidHom ({x : G | φ x = x} ∪ {x : G | ψ x = x})
  rw [h, Subgroup.map_top_of_surjective _ γ.surjective] at h2
  exact h2.symm

theorem kgConcl_C6 {F : Type} [Field F] [Finite F] [CharP F 2] (p : ℕ) : KGConcl (C6 F) p := by
  intro S B hS2 hnc hSI hBp hBS
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hn : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  obtain ⟨Θ, hΘ⟩ := exists_fieldGraphCoordinate_E6 F
  have hΘ' : IsCoord Θ := hΘ
  have hcomm : ∀ a b : F ≃+* F, a * b = b * a :=
    CFSG.RankThree.PartOne.OutStructure.ringAut_comm F
  haveI hcyc : IsCyclic (F ≃+* F) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hn).2
  have hQ : ∀ a b : (F ≃+* F) × Multiplicative (ZMod 2), a * b = b * a := fun a b =>
    Prod.ext (hcomm _ _) (mul_comm _ _)
  have hSker : S ⊓ Θ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxk⟩
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hS2 hxS
    have hinn := e6_inner_of_ker hn Θ hΘ (MonoidHom.mem_ker.mp hxk) hk
    have hx : x ∈ S ⊓ (MulAut.conj : C6 F →* MulAut (C6 F)).range := ⟨hxS, hinn⟩
    rw [hSI] at hx
    exact hx
  obtain ⟨hSab, hBcomm⟩ := commute_of_inf_ker_eq_bot hQ Θ hSker
  obtain ⟨a, haS, b, hbS, haa, hbb, ha1, ha2, hb⟩ := exists_involutions_of_types Θ hS2 hnc hSker
  have hΘa : Θ a = ((Θ a).1, 1) := Prod.ext rfl ha2
  have hδ2 : (Θ a).1 * (Θ a).1 = 1 := by
    have h1 : Θ (a * a) = Θ a * Θ a := map_mul _ _ _
    rw [haa, map_one] at h1
    exact (congrArg Prod.fst h1).symm
  have hδ1 : (Θ a).1 ≠ 1 := ha1
  have hane : a ≠ 1 := fun h => ha1 (by rw [h, map_one]; rfl)
  have hbne : b ≠ 1 := by
    intro h
    rw [h, map_one] at hb
    have := congrArg Prod.snd hb
    have h01 : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 := by decide
    exact h01 this.symm
  obtain ⟨h, hh⟩ := exists_conj_stabU F hS2
  have hinv : (MulAut.conj h⁻¹ : MulAut (C6 F)) = (MulAut.conj h)⁻¹ := map_inv _ _
  have hcA := hh a haS
  have hcB := hh b hbS
  rw [hinv] at hcA hcB
  have ha'2 : ((MulAut.conj h)⁻¹ * a * MulAut.conj h) * ((MulAut.conj h)⁻¹ * a * MulAut.conj h) =
      1 := by
    calc ((MulAut.conj h)⁻¹ * a * MulAut.conj h) * ((MulAut.conj h)⁻¹ * a * MulAut.conj h)
        = (MulAut.conj h)⁻¹ * (a * a) * MulAut.conj h := by group
      _ = 1 := by rw [haa]; group
  have hb'2 : ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) =
      1 := by
    calc ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * ((MulAut.conj h)⁻¹ * b * MulAut.conj h)
        = (MulAut.conj h)⁻¹ * (b * b) * MulAut.conj h := by group
      _ = 1 := by rw [hbb]; group
  have hΘinv : Θ ((MulAut.conj h)⁻¹) = 1 := by
    rw [← hinv]
    exact Θ_conj hΘ' h⁻¹
  have hΘa' : Θ ((MulAut.conj h)⁻¹ * a * MulAut.conj h) = ((Θ a).1, 1) := by
    rw [map_mul, map_mul, hΘinv, Θ_conj hΘ' h, one_mul, mul_one, ← hΘa]
  have hΘb' : Θ ((MulAut.conj h)⁻¹ * b * MulAut.conj h) =
      ((1 : F ≃+* F), Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [map_mul, map_mul, hΘinv, Θ_conj hΘ' h, one_mul, mul_one, hb]
  obtain ⟨β, hβ, hβeq⟩ := e6_lang hn hΘ' hcomm hδ2 hδ1 (ulang_holds hδ2 hδ1) hcA ha'2 hΘa'
  have hτs : β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β ∈ stabU F :=
    (stabU F).mul_mem ((stabU F).mul_mem ((stabU F).inv_mem hβ) hcB) hβ
  have hτ2 : (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) *
      (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) = 1 := by
    calc (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) *
          (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β)
        = β⁻¹ * (((MulAut.conj h)⁻¹ * b * MulAut.conj h) *
            ((MulAut.conj h)⁻¹ * b * MulAut.conj h)) * β := by group
      _ = 1 := by rw [hb'2]; group
  have hΘτ : Θ (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) =
      ((1 : F ≃+* F), Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [map_mul, map_mul, map_inv, hΘb']
    have h1 := hQ ((Θ β)⁻¹) ((1 : F ≃+* F), Multiplicative.ofAdd (1 : ZMod 2))
    rw [h1, mul_assoc]
    exact mul_eq_left.mpr (inv_mul_cancel (Θ β))
  have hfix := fun c => e6_fix_theta Θ hΘ hτs hτ2 hΘτ c
  have hgen := e6_gen_core hδ2 hδ1 hfix
  rw [← fieldAutE6_eq_entrywise] at hgen
  have ha_eq : a = (MulAut.conj h * β) * fieldAutE6 F (Θ a).1 * (MulAut.conj h * β)⁻¹ := by
    calc a = MulAut.conj h * ((MulAut.conj h)⁻¹ * a * MulAut.conj h) * (MulAut.conj h)⁻¹ := by
          group
      _ = _ := by rw [hβeq]; group
  have hb_eq : b = (MulAut.conj h * β) *
      (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) * (MulAut.conj h * β)⁻¹ := by
    group
  have hclo := closure_fix_conj (MulAut.conj h * β) (fieldAutE6 F (Θ a).1)
    (β⁻¹ * ((MulAut.conj h)⁻¹ * b * MulAut.conj h) * β) hgen
  rw [← ha_eq, ← hb_eq] at hclo
  exact ⟨a, b, haS, hbS, hane, hbne, fun t ht => hSab t ht a haS, fun t ht => hSab t ht b hbS,
    fun t ht => hBcomm t (hBS ht) a haS, fun t ht => hBcomm t (hBS ht) b hbS, hclo⟩

theorem kgConclE6_holds : KGConclE6 := by
  intro K _ _ f hm p
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6 hm.2
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  exact kgConcl_of_mulEquiv e (kgConcl_C6 p)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
