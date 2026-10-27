module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU28

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.R56

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Sigma


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem centralizer_t_le_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    Subgroup.centralizer ({t} : Set Y) ≤ sigmaStarNorm (Om R) (tightCore R) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  intro c hct
  have hcz : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hct
    calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [this]
      _ = t := by group
  have hL : conjSub c (tightCore R) ∈ twinSet (Om R) (tightCore R) :=
    ⟨hΩ.conjInvariant c _ hK, t, hz, hcz ▸ hz.conj c⟩
  exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (mem_dstarComp_of_twin_gen hΩ hK hL)

theorem p23_sigmaStarNorm_eq_top
    (hc : P23Cfg n Y R S t K' W u e g)
    (hTwo : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤)
    (hlayer : ∀ c ∈ Subgroup.centralizer ({u} : Set Y),
      conjSub c (conjSub g (tightCore R)) ∈ dstarComp (Om R) (tightCore R)) :
    sigmaStarNorm (Om R) (tightCore R) = ⊤ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  refine eq_top_iff.mpr ?_
  rw [← hTwo]
  refine sup_le ?_ (centralizer_t_le_sigmaStarNorm hc)
  intro c hcu
  have h1 : g ∈ sigmaStarNorm (Om R) (tightCore R) :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (by simpa using hlayer 1 (Subgroup.one_mem _))
  have h2 : c * g ∈ sigmaStarNorm (Om R) (tightCore R) :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (by rw [conjSub_mul]; exact hlayer c hcu)
  have := Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1)
  simpa using this

theorem p23_sigmaStarNorm_eq_top_of_layer
    (hc : P23Cfg n Y R S t K' W u e g)
    (hTwo : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤)
    (hlay : ∀ J ∈ tqMembers3 (Om R) u, J ∈ dstarComp (Om R) (tightCore R)) :
    sigmaStarNorm (Om R) (tightCore R) = ⊤ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hJ₁ : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u := (p23_innerHyp_u hc).htq
  exact p23_sigmaStarNorm_eq_top hc hTwo fun c hcu =>
    hlay _ (conjSub_mem_tqMembers3 hΩ.conjInvariant hcu hJ₁)

theorem p23_dstarComp_eq_univ (hc : P23Cfg n Y R S t K' W u e g)
    (h : sigmaStarNorm (Om R) (tightCore R) = ⊤) :
    ∀ J ∈ Om R, J ∈ dstarComp (Om R) (tightCore R) := by
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ sigmaStarNorm (Om R) (tightCore R) := by rw [h]; exact Subgroup.mem_top x
  exact (mem_sigmaStarNorm_iff.mp hx (tightCore R)).mp Relation.ReflTransGen.refl

theorem p23_false_of_dstar_proper (hc : P23Cfg n Y R S t K' W u e g)
    (h : sigmaStarNorm (Om R) (tightCore R) = ⊤) {X : Subgroup Y}
    (hX : ∀ J ∈ dstarComp (Om R) (tightCore R), J ≤ X) (hne : X ≠ ⊤) : False := by
  have hC := CoreData.of_S hc.std.perp.core
  have hgen : (⨆ x : Y, conjSub x (tightCore R)) = ⊤ := hC.gen
  apply hne
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun x => hX _ (p23_dstarComp_eq_univ hc h _ ⟨x, rfl⟩)

end Sigma

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.R56
