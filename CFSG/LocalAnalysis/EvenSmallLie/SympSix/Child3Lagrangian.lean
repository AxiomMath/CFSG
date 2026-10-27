module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Setup
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientNode
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCFSp6LagrangianOddLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCHSp6SuzukiAmbientExclusion
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCESp6EvenUnitaryExclusion
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBKSp6LagrangianAlternatingExclusion
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.SteinbergCF
  (standard_binary_symplectic_six_elementary_lagrangian_odd_linear_two_ambient_exclusion)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBI
  (standard_binary_symplectic_six_elementary_lagrangian_even_symplectic_ambient_exclusion)
open LinearMap (BilinForm)
open scoped Pointwise

theorem lieModel_quot_of_center_eq_bot {X : Type} [Group X] (hZ : center X = ⊥) {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSp n p f) :
    CFSG.Blueprint.LieModel (X ⧸ center X) .PSp n p f :=
  CFSG.Blueprint.LieModel.quotient_center hZ h


theorem false_of_lagrangian (hF : Sp6LagrangianFullOddCoreStmt) (hG1 : GapEpsilonOne)
    (hG2 : GapLagrangianSelector) (hTF : InputTwoFactor) (hSR : InputSmallRee)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {T : Sylow 2 (centralizer (L : Set G))}
    {z : G} (hS : Setting L T z)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) : False := by
  have hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1 :=
    lieModel_quot_of_center_eq_bot hS.center_eq hS.model
  have hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) := ⟨T, hS.cyclic⟩
  have htype := evenStandardType_of hQ
  have hexc := not_evenStandardException_of hQ
  have hres := evenStandardResidual_of hS.center_eq hQ
  have hel := hG1 G L T z hS V b hb hnd hV φ e he hfull
  have hsimple := hTF G L T z hS V b hb hnd hV φ e he hfull hel
  have hDs : IsSimpleGroup (sp6Dstar φ he z) := hsimple.1
  have hDn : ∃ x y : sp6Dstar φ he z, x * y ≠ y * x := hsimple.2.1
  rcases hG2 G L T z hS V b hb hnd hV φ e he hfull hel hsimple with
    ⟨n, f, hn, hf, k, _, hk, ⟨η⟩⟩ | ⟨p, f, hp, hpo, hf, hm⟩ | ⟨p, f, hm⟩ | ⟨n, f, hn, hf, hm⟩ |
      ⟨r, f, hr, hf, hm⟩ | ⟨ℓ, f, hm⟩ | ⟨n, hn, ⟨η⟩⟩
  ·
    have h := (standard_binary_symplectic_six_elementary_lagrangian_even_linear_ambient_exclusion
      φ he z hF hS.simple hS.nonab hS.kProper hS.standard hS.core hcyc htype hexc hres
      hS.center_eq hQ T hS.cyclic hS.mem hS.order hb hnd hV hfull).2.2.2.2.2.2.2.2
    exact (h hel hDs hDn n f hn hf k hk).false η
  ·
    have h := (standard_binary_symplectic_six_elementary_lagrangian_odd_linear_two_ambient_exclusion
      hF hS.simple hS.nonab hS.kProper hS.standard hS.core hS.center_eq hQ T hS.cyclic hS.mem
      hS.order hb hnd hV φ e he hfull).2.2.2.2.2.2.2.2.2
    exact h hel hDs hDn p f hp hpo hf hm
  ·
    have h := (standard_binary_symplectic_six_elementary_lagrangian_Suzuki_ambient_exclusion
      hF hS.simple hS.nonab hS.kProper hS.standard hS.core hcyc htype hexc hres hS.center_eq hQ T
      hS.cyclic hS.mem hS.order hb hnd hV φ e he hfull).2.2.2.2.2.2.2.2.2.2.2.2
    exact (h hel hDs hDn p f).1 hm
  ·
    have h := (standard_binary_symplectic_six_elementary_lagrangian_even_unitary_ambient_exclusion
      φ he z hF hS.simple hS.nonab hS.kProper hS.standard hS.core hcyc htype hexc hres
      hS.center_eq hQ T hS.cyclic hS.mem hS.order hb hnd hV hfull).2.2.2.2.2.2.2.2
    exact h hel hDs hDn n f hn hf hm
  ·
    have h :=
      (standard_binary_symplectic_six_elementary_lagrangian_even_symplectic_ambient_exclusion
      hF hS.simple hS.nonab hS.kProper hS.standard hS.core htype hexc hres hS.center_eq hQ T
      hS.cyclic hS.mem hS.order hb hnd hV φ e he hfull).2.2.2.2.2.2.2.2.2.2.2.2
    exact h hel hDs hDn r f hr hf hm
  ·
    exact hSR G L T z hS V b hb hnd hV φ e he hfull hel hDs hDn ℓ f hm
  ·
    have h := (standard_binary_symplectic_six_elementary_lagrangian_alternating_layer_exclusion
      φ he z hF hS.simple hS.nonab hS.kProper hS.standard hS.core hcyc htype hexc hres
      hS.center_eq hQ T hS.cyclic hS.mem hS.order hb hnd hV hfull).2.2.2.2.2.2.2.2.2.2.2.2
    exact (h hel hDs hDn n hn).false η

end CFSG.EvenSmallLie.Child3
