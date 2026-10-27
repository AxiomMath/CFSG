module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangSylow

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem commutator_self_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem closure_eq_top_of_le_closure {G : Type*} [Group G] {Γ : Subgroup G} {X : Set G}
    (hX : X ⊆ Γ) (h : Γ ≤ Subgroup.closure X) :
    Subgroup.closure {s : ↥Γ | (s : G) ∈ X} = ⊤ := by
  have hmap : (Subgroup.closure {s : ↥Γ | (s : G) ∈ X}).map Γ.subtype = Subgroup.closure X := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, hX hx⟩, hx, rfl⟩
  rw [eq_top_iff]
  rintro γ -
  have : (γ : G) ∈ (Subgroup.closure {s : ↥Γ | (s : G) ∈ X}).map Γ.subtype := by
    rw [hmap]
    exact h γ.2
  obtain ⟨c, hc, hcγ⟩ := this
  exact (Subtype.ext hcγ : c = γ) ▸ hc

namespace LangSetup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem Γ_le_model : S.Γ ≤ S.D.model := commutator_self_le_self _

theorem finite_Γ : Finite S.Γ := by
  have := S.finite
  exact Finite.of_injective (Subgroup.inclusion S.Γ_le_model) (Subgroup.inclusion_injective _)

end LangSetup

theorem LangSetup.exists_conj_le {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hsyl : ∃ S₀ : Sylow p S.Γ,
      (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ)
    {F : Subgroup (ModGL τ L)} (hFΓ : F ≤ S.Γ) (hF : ∀ x ∈ F, x ^ p = 1) :
    ∃ h ∈ S.Γ, F.map (MulAut.conj h).toMonoidHom ≤ S.E := by
  haveI : Fact p.Prime := ⟨S.hp⟩
  haveI := S.finite_Γ
  obtain ⟨S₀, hS₀⟩ := hsyl
  refine exists_conj_le_of_sylow_torsion_modGL (T := S.D.torus ⊓ S.Γ) S₀ ?_
    (fun x hx hxp => S.E_all x hx hxp) hFΓ hF
  intro x hx
  have := hS₀ hx
  rw [Subgroup.mem_subgroupOf] at this ⊢
  exact Subgroup.mem_inf.2 ⟨this, x.2⟩

theorem conj_injective_of_center_bot {K : Type*} [Group K] (h : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro g g' hgg
  have hc : g'⁻¹ * g ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.2 fun x => by
      have e1 := congrArg (fun φ : MulAut K => φ x) hgg
      simp only [MulAut.conj_apply] at e1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [e1]
        _ = g'⁻¹ * g * x := by group
  rw [h, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
