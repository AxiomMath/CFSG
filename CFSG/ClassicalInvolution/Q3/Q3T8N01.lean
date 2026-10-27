module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Sect
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Base
public import CFSG.ClassicalInvolution.Q3.Q3T8L278A
public import CFSG.ClassicalInvolution.Q3.Q3T8L278B
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec
public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarNbr
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRDef
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8Y4
public import CFSG.ClassicalInvolution.Asc77.AscT8V6
import CFSG.ClassicalInvolution.Asc77.AscT8RepEng
import CFSG.ClassicalInvolution.Q3.Q3T8RepHooks

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Rep
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem repElt_eq_iff (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) : repElt ρ = repElt σ ↔ ρ.K = σ.K
    :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem repElt_commute_iff (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    repElt ρ * repElt σ = repElt σ * repElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K :=
  ⟨fun h => c.omega_of_comm ρ σ hne (congrArg Subtype.val h),
    fun h => Subtype.ext (c.comm_of_omega ρ σ h)⟩

theorem repElt_omegaStar (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    σ.K ∈ omegaStarNbr Ω ρ.K :=
  (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK).1
end Rep
section Std
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
end Std
section Klein
variable {Q : Type} [Group Q]
end Klein
section Dichotomy
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_third_of_abelian (hs : Std8 Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ τ : Rep Ω W, τ.K ≠ K ∧ τ.K ≠ J := by
  have hP := partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  by_contra hcon
  push Not at hcon
  set a := repElt (stdRepK hs) with ha
  set b := repElt (stdRepJ hs) with hb
  have hall : ∀ d ∈ muDelta Ω W, d = a ∨ d = b := by
    intro d hd
    obtain ⟨τ, rfl⟩ := Asc77.T8.exists_rep_of_mem_muDelta hd
    by_cases h1 : τ.K = K
    · left
      exact (repElt_eq_iff hc τ (stdRepK hs)).mpr h1
    · right
      exact (repElt_eq_iff hc τ (stdRepJ hs)).mpr (hcon τ h1)
  have haΔ : a ∈ muDelta Ω W := repElt_mem _
  have hbΔ : b ∈ muDelta Ω W := repElt_mem _
  have hne : a ≠ b := fun h =>
    hs.hJ.2.1 ((repElt_eq_iff hc (stdRepK hs) (stdRepJ hs)).mp h).symm
  apply hE4
  refine nonempty_mulEquiv_klein (Thompson.muDelta_mul_self hP.hyp hs.hW.1 haΔ)
    (Thompson.muDelta_mul_self hP.hyp hs.hW.1 hbΔ)
    (Subtype.ext (hab _ a.2 _ b.2)) (muDelta_ne_one hs.hW.1 haΔ) (muDelta_ne_one hs.hW.1 hbΔ) hne
    ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rcases hall d hd with h | h
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
end Dichotomy
section LayerTri
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end LayerTri
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
section Alg
end Alg
section Rel
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem centralizes_of_comm_r (c : Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) {y : G} (hyW : y ∈ W)
    (hry : ρ.r * y = y * ρ.r) : ∀ x ∈ ρ.R, x * y = y * x := by
  exact CFSG.ClassicalInvolution.Asc77.T8V.centralizes_of_comm_rE c.toRepHooks ρ hyW hry

theorem exists_sq_root (c : Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) {z : G} (hz : IsUniqueInvolution
    ρ.K z) :
    ∃ g : G, g ∈ ρ.K ⊓ W ∧ g ∈ ρ.R ∧ g * g = z := by
  obtain ⟨h1, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hzKW : z ∈ ρ.K ⊓ W :=
    Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz
  have hzU : z ∈ ρ.R ⊓ W := h1 ▸ hzKW
  have hU2 : IsPGroup 2 ↥(ρ.R ⊓ W) := (isPGroup_of_mem_WSet c.hW).to_inf_right
  obtain ⟨g, hg, hgg⟩ := exists_mul_self_eq_of_cyclic (ρ.R ⊓ W) hU2 h4 hzU hz.sq hz.ne_one
  exact ⟨g, h1 ▸ hg, hg.1, hgg⟩

theorem centralizes_vg (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z v g : G} (hz : IsUniqueInvolution ρ.K z)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ.K ⊓ W) (hgg : g * g = z) :
    v * g⁻¹ ∈ W ∧ (∀ x ∈ ρ.R, x * (v * g⁻¹) = (v * g⁻¹) * x) ∧
      (v * g⁻¹) * (v * g⁻¹) = z := by
  exact CFSG.ClassicalInvolution.Asc77.T8V.centralizes_vgE c.toRepHooks ρ σ hne hnot hz hv hg hgg

theorem centralizes_mem_inf_W (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω
    ρ.K)
    {g : G} (hg : g ∈ σ.K ⊓ W) : ∀ x ∈ ρ.R, x * g = g * x :=
  centralizes_of_comm_r c ρ hg.2 (c.centralizes ρ σ hnbr hg)

theorem centralizes_inv_of_nbr (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω
    ρ.K)
    {v : G} (hv : IsUniqueInvolution σ.K v) : ∀ x ∈ ρ.R, x * v = v * x := by
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (T8.rep_le_centralizer c ρ σ (Or.inr hnbr) hv hx)

theorem exists_y_left (c : Q3CL.Thompson.Ctx Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ v g : G}
    (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne : ρ₁.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ₁.K)
    (hσ₂ : σ.K ∈ omegaNbr Ω ρ₂.K) (hz : IsUniqueInvolution ρ₁.K z₁)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁) :
    ∃ y ∈ W, y * y = z₁ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧ (∀ x ∈ ρ₂.R, x * y = y * x) := by
  obtain ⟨hyW, hy1, hyy⟩ := centralizes_vg c ρ₁ σ hne hnot hz hv hg hgg
  refine ⟨v * g⁻¹, hyW, hyy, hy1, fun x hx => ?_⟩
  have h1 : Commute x v := centralizes_inv_of_nbr c ρ₂ σ hσ₂ hv x hx
  have h2 : Commute x g := centralizes_mem_inf_W c ρ₂ ρ₁ hn21 hg x hx
  exact (h1.mul_right h2.inv_right)

theorem exists_y_both (c : Q3CL.Thompson.Ctx Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ z₂ v g h : G}
    (hn12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne1 : ρ₁.K ≠ σ.K)
    (hne2 : ρ₂.K ≠ σ.K) (hnot1 : σ.K ∉ omegaNbr Ω ρ₁.K) (hnot2 : σ.K ∉ omegaNbr Ω ρ₂.K)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁)
    (hh : h ∈ ρ₂.K ⊓ W) (hhh : h * h = z₂) :
    ∃ y ∈ W, y = v * g⁻¹ * h⁻¹ ∧ y * y = z₁ * z₂ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧
      (∀ x ∈ ρ₂.R, x * y = y * x) := by
  exact CFSG.ClassicalInvolution.Asc77.T8V.exists_y_bothE c.toRepHooks ρ₁ ρ₂ σ hn12 hn21 hne1 hne2 hnot1 hnot2 hz₁ hz₂ hv
    hg hgg hh hhh
end Rel
end T8V
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Conj
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Conj
section Cases
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_dComp_of_rep (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (ρ : Rep Ω W) : ρ.K ∈ dComp Ω K := by
  have hc := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  rw [hcomp]
  by_cases h : K = ρ.K
  · rw [← h]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨ρ.hK, Or.inl (repElt_omegaStar hc (stdRepK hs) ρ h)⟩

theorem oddCoreOf_layerJoin_le_of_nonabelian (hs : Std8 Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hP := partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨d, hd, e, he, hde⟩ := exists_noncomm_of_not_abelian hab
  obtain ⟨ρ, rfl⟩ := Asc77.T8.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := Asc77.T8.exists_rep_of_mem_muDelta he
  have hKne : ρ.K ≠ σ.K := fun h => hde (by rw [(repElt_eq_iff hc ρ σ).mpr h])
  have hnonbr : σ.K ∉ omegaNbr Ω ρ.K := fun h => hde ((repElt_commute_iff hc ρ σ hKne).mpr h)
  have hstar : σ.K ∈ omegaStarNbr Ω ρ.K := repElt_omegaStar hc ρ σ hKne
  obtain ⟨zρ, hzρ⟩ := hΩ.exists_uniqueInvolution ρ.hK
  obtain ⟨zσ, hzσ⟩ := hΩ.exists_uniqueInvolution σ.hK
  have hzρW : zρ ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 ρ.hK ρ.hR ρ.hRK hzρ).2
  have hzσW : zσ ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 σ.hK σ.hR σ.hRK hzσ).2
  have hzW : z ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hK (stdRepK hs).hR (stdRepK hs).hRK hs.hz).2
  have htW : t ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hs.hJ.1 (stdRepJ hs).hR (stdRepJ hs).hRK
        hs.ht).2
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcomm : zρ * zσ = zσ * zρ := hc.comm_W _ hzρW _ hzσW
  have hzne : zσ ≠ zρ := by
    intro h
    have hj : IsUniqueInvolution σ.K zρ := by rw [← h]; exact hzσ
    exact hKne (hnt _ ρ.hK _ ⟨σ.hK, zρ, hzρ, hj⟩).symm
  have hmρ := mem_dComp_of_rep hs hcomp ρ
  have hmσ := mem_dComp_of_rep hs hcomp σ
  have hKρ : ρ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hKσ : σ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  have hg1 : Subgroup.centralizer ({zρ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant ρ.hK (hnt _ ρ.hK) hzρ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hg2 : Subgroup.centralizer ({zσ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant σ.hK (hnt _ σ.hK) hzσ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  obtain ⟨c, hcmem, hcz⟩ := exists_conj_mul_of_aEmpty (hs.stand.aEmpty ρ.K ρ.hK) hstar hnonbr hzρ
    hzσ hcomm hzne
  have hcN : c ∈ sigmaNorm Ω K := (sup_le hKρ hKσ) hcmem
  have hg3 : Subgroup.centralizer ({zρ * zσ} : Set G) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hcN ?_
    have : c⁻¹ * (zρ * zσ) * c = zρ := by rw [← hcz]; group
    rw [this]
    exact hg1
  exact Layer.oddCoreOf_exactLayer3_le_of_good_pair hΩ.conjInvariant hzρ.sq hzσ.sq hcomm
    hzρ.ne_one hzσ.ne_one (Ne.symm hzne) (mem_cenZ_iff.mpr (hc.comm_W _ hzρW _ haW))
    (mem_cenZ_iff.mpr (hc.comm_W _ hzσW _ haW)) hg1 hg2 hg3

theorem oddCoreOf_layerJoin_le_of_alpha (hs : Std8 Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) :
    oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have ha1 : z * t ≠ 1 := zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have haA : z * t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ hzA htA
  intro x hx
  have hYC : Q3NL.exactLayer3 Ω (z * t) ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [← cenZ_eq_centralizer]
    exact Layer.exactLayer3_le_cenZ Ω (z * t)
  have hxC := oddCoreOf_le_oddCoreOf_of_normalized hYC
    (fun c hc => Layer.exactLayer3_conjSub_eq hΩ.conjInvariant
      (by rw [cenZ_eq_centralizer]; exact hc)) hx
  have hxz : x * z = z * x := oddCoreOf_centralizer_commutes hα haA ha1 hzA x hxC
  exact normalizer_le_sigmaNorm hΩ.conjInvariant hK
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
end Cases
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
section LayerMk
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end LayerMk
section E4
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerMk_mul {x g h : G} (hg : g ∈ Q3NL.exactLayer3 Ω x) (hh : h ∈ Q3NL.exactLayer3 Ω x) :
    layerMk x g hg * layerMk x h hh = layerMk x (g * h) ((Q3NL.exactLayer3 Ω x).mul_mem hg hh) := by
  unfold layerMk
  rw [← map_mul]
  rfl

theorem layerMk_eq_one {x g : G} (hg : g ∈ Q3NL.exactLayer3 Ω x) (h1 : g = 1) :
    layerMk x g hg = 1 := by
  subst h1
  exact map_one (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω x)))

theorem layerMk_z_sq (hs : Std8 Ω K J S R T W z t) :
    layerMk (z * t) z (z_mem_layerJoin hs) * layerMk (z * t) z (z_mem_layerJoin hs) = 1 := by
  rw [layerMk_mul]
  exact layerMk_eq_one _ hs.hz.sq

theorem e4_layer [IsSimpleGroup G] (hE : E4SecNoRoot3) (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) :
    (∀ σ : MulAut (Q3T7.layerQuot3 Ω (z * t)),
      (∀ k ∈ Layer.layerImg3 Ω (z * t) K,
        σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) K)) →
      (∀ k ∈ Layer.layerImg3 Ω (z * t) J,
        σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) J)) →
        σ * σ ≠ MulAut.conj (layerMk (z * t) z (z_mem_layerJoin hs))) ∧
    (∀ e : Q3T7.layerQuot3 Ω (z * t),
      (∀ k ∈ Layer.layerImg3 Ω (z * t) K, ⁅e, k⁆ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) K)) →
      (∀ k ∈ Layer.layerImg3 Ω (z * t) J, ⁅e, k⁆ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) J)) →
        e * e ≠ layerMk (z * t) z (z_mem_layerJoin hs) *
          layerMk (z * t) t (t_mem_layerJoin hs)) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXK := Layer.xMem_zt3 hs
  have hXJ := xMem_J hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hzY := z_mem_layerJoin hs
  have htY := t_mem_layerJoin hs
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hne : Layer.layerImg3 Ω (z * t) K ≠ Layer.layerImg3 Ω (z * t) J :=
    Layer.layerImg3_ne_of_involutions hL hXK hXJ hs.hz hs.ht
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht)
      (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hc : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    have hn21 : K ∈ omegaNbr Ω J :=
      Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
    have h1 : y ∈ Subgroup.centralizer ({z} : Set G) :=
      T8.rep_le_centralizer hc (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz hy
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz h1
  have hAB : Layer.layerImg3 Ω (z * t) J ∈ omegaNbr (Q3T7.layerFam3 Ω (z * t))
      (Layer.layerImg3 Ω (z * t) K) :=
    Layer.layerImg3_omegaNbr hKt hJt hTJ (T_le_cenZ hs) hTN hne
  have hLYK : Q3NL.exactCore3 (z * t) K ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hKt
  have hLYJ : Q3NL.exactCore3 (z * t) J ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hJt
  have hzL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) K) z :=
    Layer.isUniqueInvolution_exactCore3 hXK.2.1 hs.hz
  have htL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) J) t :=
    Layer.isUniqueInvolution_exactCore3 hXJ.2.1 hs.ht
  have hxA : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) K) (layerMk (z * t) z hzY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) J) (layerMk (z * t) t htY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : layerMk (z * t) z hzY * layerMk (z * t) t htY ∈
      Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := layerMk_central hs
  exact hE (Nat.card G) hs.stand.below hs.stand.ih (Q3T7.layerQuot3 Ω (z * t)) hlt
    (Q3T7.layerFam3 Ω (z * t)) (Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0)
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0) (Layer.noTwins_layerFam3 hL hnt) hdisc _
    (Layer.layerImg3_mem hKt) _ hAB _ _ hxA hxB hcen
end E4
end T8V
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
