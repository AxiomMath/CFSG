module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag
public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
import CFSG.ClassicalInvolution.Q3.Q3T8B14Core
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.Q3.Q3AMXNOrb
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement MatrixGroups
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Vertex
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem notTrivialOn_layerImg_of_noTri [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hN : Q3AM.NoTriangleAtEdge Ω K J) {t₁ : G}
    (ht1 : t₁ ∈ T8.cenZ (z * t))
    (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t) (hnJ : conjSub t₁ J = J) {J₁ : Subgroup G}
    (hJ₁K : J₁ ∈ omegaNbr Ω K) (hJ₁t : IsUniqueInvolution J₁ t₁) :
    ¬ ∀ kb ∈ Layer.layerImg3 Ω (z * t) J,
      s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hs.stand.hyp.conjInvariant ht1)⟩ kb * kb⁻¹ ∈
          oddCoreOf (Layer.layerImg3 Ω (z * t) J) := by
  intro H₀
  exact hN J₁ hJ₁K (Q3CL.T3.omegaNbr_symm (l6_2) hs.stand.hyp hJ₁K.1 hs.hJ.1
    (mem_omegaNbr_of_trivialOn_layerImg hs ht1 ht1sq hne hnJ hJ₁K.1 hJ₁t H₀))

theorem layer_class_psl4Y [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hN : Q3AM.NoTriangleAtEdge Ω K J) {w : G}
    (hw2 : w * w = 1) (hwz : z * w = w * z) (hwt : t * w = w * t) (hne : w ≠ t)
    {R₀ : Subgroup G} (hR₀ : IsSylow2In R₀ K) (hwR : ∀ r ∈ R₀, r * w = w * r)
    (hnJ : conjSub w J = J) {J₁ : Subgroup G} (hJ₁K : J₁ ∈ omegaNbr Ω K)
    (hJ₁w : IsUniqueInvolution J₁ w)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)))
    (hwN : w ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G)) :
    ∃ (M : Ih8Model 3 1 (Q3T7.layerFam3 Ω (z * t)) .PSL 4 1)
      (D : GL (Fin 4) (GaloisField 3 1)) (y' : SL(4, GaloisField 3 1)),
      M.ψ y' = T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs) ∧ y' * y' = 1 ∧ D * D = 1 ∧
        (∀ g, s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ g) =
          M.ψ (Q3NM.conjSLAut D g)) ∧
        (D : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) *
            (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) =
          (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) * D :=
  layer_class_psl4_of_not hs hw2 hwz hwt hR₀ hwR hdisc hwN fun hwcen =>
    notTrivialOn_layerImg_of_noTri hs hN hwcen hw2 hne hnJ hJ₁K hJ₁w

end Vertex
end T8W
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
