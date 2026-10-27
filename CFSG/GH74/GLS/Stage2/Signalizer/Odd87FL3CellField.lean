module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section CellField

theorem fl3_field_false {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal]
    {hz : z ∈ H₀} {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    {F : Type} [Field F] [Finite F] {p0 f : ℕ} (hp0 : p0.Prime) (hp02 : p0 ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p0 ^ f) (e : ↥(layer (Sec H₀ H₁)) ≃* projectiveSL 3 F)
    (α : MulAut (projectiveSL 3 F))
    (hcomm : ∀ x : ↥(layer (Sec H₀ H₁)), e (layerAut (zSec z H₀ hz H₁) x) = α (e x))
    (hα : α * α = 1) (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hαeq : α = conjAut 3 F A * fieldAut 3 F σ) : False := by
  have : Fact p0.Prime := ⟨hp0⟩
  obtain ⟨F0, _, _, _, hodd0, h30, Q, hQperf, hQfix, c, hc⟩ :=
    fl3_field_section hp0 hp02 hf hcard α hα A σ hσ hαeq
  have hker : e.toMonoidHom.ker ≤ center ↥(layer (Sec H₀ H₁)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact bot_le
  have hQ : Group.IsPerfect ↥Q := hQperf
  have hCS : CentSection (zSec z H₀ hz H₁) (projectiveSL 3 F0) :=
    centSection_of_fixed_perfect (π := e.toMonoidHom) e.surjective hker (α := α) hcomm Q hQfix c hc
  have : IsSimpleGroup (projectiveSL 3 F0) := isSimpleGroup_projectiveSL3_fl3 F0
  have : Group.IsPerfect (projectiveSL 3 F0) := isPerfect_projectiveSL3_fl3 F0
  have : Nontrivial (projectiveSL 3 F0) := IsSimpleGroup.toNontrivial
  have hns : ¬ Group.IsSolvable (projectiveSL 3 F0) := Group.IsPerfect.not_isSolvable _
  have hKF := kindFactor_of_section_sec hctx hsig hns hCS.isSection
  exact not_kindFactor hp02 (involved_qdSL_projectiveSL3 (p := p0))
    (not_card_dvd_factorial_projectiveSL3 hodd0 h30) hKF

end CellField

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
