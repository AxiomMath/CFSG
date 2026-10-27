module

public import CFSG.ClassicalInvolution.Q3.Q3T8C274
public import CFSG.ClassicalInvolution.Q3.Q3T8NDef
public import CFSG.ClassicalInvolution.Asc77.AscT8X1
public import CFSG.ClassicalInvolution.Asc77.AscT8YB1
public import CFSG.ClassicalInvolution.Q3.Q3T8N01
import CFSG.ClassicalInvolution.Q3.Q3CLWylA
import CFSG.StronglyEmbedded.UniqueCosetFixedEng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77


end Asc77

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Std
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem stdRepK_K (hs : Std8 Ω K J S R T W z t) : (stdRepK hs).K = K := rfl

theorem stdRepJ_K (hs : Std8 Ω K J S R T W z t) : (stdRepJ hs).K = J := rfl
end Std
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace MuTab
open CFSG.ClassicalInvolution.Asc77.MuTab
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
section Cent
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW

theorem exists_not_conn_at (hnc : ¬ DbarConnected Ω W) (d : ↥(muGroup Ω W)) :
    ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a :=
  Q3CL.Wyl.exists_not_conn_at hP hW hnc d

theorem muIso_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 1 → MuIsoS3 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 2 → MuIsoS4 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 → MuIsoWylD4 Ω W) :=
  Q3CL.Wyl.muIso_of_cent hP hW hnc ρ
end Cent
end MuTab
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.StronglyEmbedded.UniqueCoset
namespace T8X
open CFSG.ClassicalInvolution.Asc77.T8X
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_comm_of_wset (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (h : MuIsoWylD4 Ω W) {W' : Subgroup G}
    (hW' : W' ∈ WSet Ω) :
    ¬ ∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x := by
  intro hc
  obtain ⟨e⟩ := l7_5_2_proved G Ω hΩ W hW W' hW'
  refine not_comm_of_muIsoWylD4 h fun a b => e.injective ?_
  rw [map_mul, map_mul]
  exact Subtype.ext (hc _ (e a).2 _ (e b).2)
variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem fixesUniqueCoset_of_comp [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset (z * t) (T8.H274 Ω K z) := by
  have hmin' := c27_4M_proved G Ω K J S R T W z t hs hdisc
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact T8.mem_H274_of_min hs hcomp hmin' hg

theorem H274_eq_top [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) : T8.H274 Ω K z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact fixesUniqueCoset_of_comp hstd hdisc hcomp
  obtain ⟨z', hz'cl⟩ := hs.stand.modU.classical K hs.stand.mem
  have hz'z : z' = z := by
    rcases hz.unique z' hz'cl.mem hz'cl.mul_self with h | h
    · exact absurd h hz'cl.ne_one
    · exact h
  have hKm : Q3.IsClassicalMember3 K z := hz'z ▸ hz'cl.toQ3 (by norm_num)
  obtain ⟨x, -, y, -, hxy⟩ := hz'cl.exists_noncomm
  exact Q3T8.false_of_uniqueCoset_of_weakMember3 ⟨x, y, hxy⟩ hH hz2 h1 h2' hKm

theorem centralizer_le_sigmaNorm_of_nonabelian [IsSimpleGroup G]
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W)
    (hY : C27_Ysmall3) :
    Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hx ⟨K, hKt⟩
  have hlayer : Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K := by
    by_cases hconn : T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))
    · exact Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt hcomp
        (T8.oddCoreOf_layerJoin_le_of_nonabelian hs hcomp hab) hconn
    · exact hY G Ω K J S R T W z t hs hdisc hE4 hab hconn
  exact Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hs hlayer

theorem false_of_dComp_eq [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hcomp : dComp Ω K = dstarComp Ω K) (hμ : MuIsoWylD4 Ω W)
    (hY : C27_Ysmall3) : False := by
  have hz := hs.hz
  have hle : T8.H274 Ω K z ≤ sigmaNorm Ω K := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz M hM s hs'
    have hW' : W' ∈ WSet Ω := hstd'.hW.1
    have hab' := not_comm_of_wset hs.stand.modU hs.hW.1 hμ hW'
    have hE4' : ¬ MuIsoE4 Ω W' := fun h =>
      hab' fun x hx y hy => by
        obtain ⟨e⟩ := h
        have := e.injective (a₁ := ⟨x, hx⟩ * ⟨y, hy⟩) (a₂ := ⟨y, hy⟩ * ⟨x, hx⟩)
          (by rw [map_mul, map_mul]; exact mul_comm _ _)
        exact congrArg Subtype.val this
    exact centralizer_le_sigmaNorm_of_nonabelian hstd' hdisc hcomp hab' hE4' hY
  have htop : sigmaNorm Ω K = ⊤ := top_le_iff.mp (H274_eq_top hs hdisc hcomp ▸ hle)
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans htop)
end T8X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab
namespace T8X
open CFSG.ClassicalInvolution.Asc77.T8X
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem not_dbarConnected_of_ne (hs : Std8 Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  Q3CL.Wyl.not_dbarConnected_of_ne hs.toStd8Core hne

theorem ncard_cent_eq_four (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 :=
  Q3CL.Wyl.ncard_cent_eq_four hs.toStd8Core hμ hnc ρ

theorem exists_frame (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ σ : Rep Ω W, (σ.K = K ∨ σ.K ∈ omegaNbr Ω K) → ∃ i, σ.K = (ρ i).K :=
  Q3CL.Wyl.exists_frame hs.toStd8Core hμ hnc
end T8X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_frame_closed (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
        ∃ j, σ.K = (ρ j).K :=
  Q3CL.Wyl.exists_frame_closed hs.toStd8Core hμ hnc

theorem mem_W_of_uniqueInvolution (c : Q3CL.Thompson.Ctx Ω W) (σ : Rep Ω W) {v : G}
    (hv : IsUniqueInvolution σ.K v) : v ∈ W :=
  Q3CL.Wyl.mem_W_of_uniqueInvolution c σ hv

theorem rep_comm_frame_prod (c : Q3CL.Thompson.Ctx Ω W) (ρ : Fin 4 → Rep Ω W)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    {zz : Fin 4 → G} (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) (σ : Rep Ω W)
    (i j : Fin 4) : σ.r * (zz i * zz j) = (zz i * zz j) * σ.r :=
  Q3CL.Wyl.rep_comm_frame_prod c ρ hadj hclos hz σ i j

theorem commute_frame_prod_of_mem_DSet (c : Q3CL.Thompson.Ctx Ω W) (ρ : Fin 4 → Rep Ω W)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    {zz : Fin 4 → G} (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) {R'' : Subgroup G}
    (hR : R'' ∈ DSet Ω W) {x : G} (hx : x ∈ R'') (i j : Fin 4) :
    x * (zz i * zz j) = (zz i * zz j) * x :=
  Q3CL.Wyl.commute_frame_prod_of_mem_DSet c ρ hadj hclos hz hR hx i j
end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
