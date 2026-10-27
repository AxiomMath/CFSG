module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Base
public import CFSG.ClassicalInvolution.Q3.Q3T8L278A
public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarNbr
public import CFSG.ClassicalInvolution.Asc77.AscT8W4
public import CFSG.ClassicalInvolution.Q3.Q3T8C262B
import CFSG.ClassicalInvolution.Asc77.AscT8W1Eng
import CFSG.ClassicalInvolution.Q3.Q3T8RepHooks
import CFSG.ClassicalInvolution.Asc77.AscT8W3Eng
import CFSG.ClassicalInvolution.Asc77.AscT8W6Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups
section SL2Sub
variable {K : Type} [Group K] {F : Type} [Field F] [Finite F] {R : Subgroup K}
end SL2Sub
section Transfer
variable {K G : Type} [Group K] [Group G] {ψ : K →* G}
end Transfer
section Exact
variable {K G : Type} [Group K] [Group G] [Finite G]
end Exact
section GroupLevel
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ih8_nbr_sylow (hΩ : HypOmegaMod Ω) {K J : Subgroup G}
    (hJ : J ∈ omegaNbr Ω K) :
    ∃ A : Subgroup G, IsPGroup 2 A ∧ A ≤ J ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
  obtain ⟨-, -, A, hA, hAJ, hAN⟩ := hJ
  have hA' := hA
  obtain ⟨M, -, P, rfl⟩ := hA
  exact ⟨_, P.isPGroup'.map _, hAJ, hAN, (hΩ.isQuatSub_of_mem_RSet hA').exists_not_commute⟩
end GroupLevel
section NbrModel
variable {K G : Type} [Group K] [Group G]
end NbrModel
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
section Ctx
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW

theorem muTab_commute_iff (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K := by
  have c := muTabCtx hP hW
  constructor
  · intro h
    exact c.omega_of_comm ρ σ hne (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (c.comm_of_omega ρ σ h)
end Ctx
section Realize
variable {ι : Type}
end Realize
end MuTab
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Frames
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A

theorem mem_dstarComp_of_mem_dComp [Finite G] (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hJ : J ∈ dComp Ω K) : J ∈ dstarComp Ω K := by
  induction hJ with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨hbc.1, ?_⟩
    rcases hbc.2 with h | h
    · exact Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ _ h)
    · exact Or.inr (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ _ h)
end T7A
variable [Finite G] [IsSimpleGroup G]
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A
end T7A
end Frames
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem s26_dComp_eq_of_e4 {K J : Subgroup G} {S : Sylow 2 G} {R T : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hE4 : MuIsoE4 Ω W) : dComp Ω K = dstarComp Ω K := by
  by_contra hne
  have hP : PartIHyp Ω := ⟨hs.stand.hyp, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hs.stand.mem hne hW
  exact s26_not_comm_of_muIso (l7_10_proved G Ω hP W hW hnc) (s26_comm_of_muIsoE4 hE4)
end Main
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_oddCoreIn_of_pow {N : Subgroup G} {z : G} (hN : Generic.IsClassicalMember N
    z) {R : Subgroup G}
    (hR : IsSylow2In R N) {a : G} (haN : a ∈ Subgroup.normalizer (N : Set G)) {m : ℕ}
    (ham : a ^ 2 ^ m = 1) (haR : ∀ r ∈ R, a * r = r * a) :
    ∀ x ∈ N, ⁅a, x⁆ ∈ oddCoreIn N := by
  intro x hx
  exact commutator_mem_oddCoreOf_of_pow3 hN.isUniqueInvolution_sl2 hR haN ham haR x hx

end T8V
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
section Indep
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW

theorem muTabElt_ne_mul (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K) : muTabElt ρ₃ ≠ muTabElt ρ₁ * muTabElt ρ₂ := by
  have c := muTabCtx hP hW
  intro heq
  obtain ⟨u, hu⟩ := Thompson.exists_zpowers_eq_inf_W hP.hyp hW ρ₃.hR
  obtain ⟨hRK, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hP.hyp hW ρ₃.hR ρ₃.hK ρ₃.hRK
  have huR : u ∈ ρ₃.R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have huKW : u ∈ ρ₃.K ⊓ W := hRK ▸ huR
  have hord : 4 ≤ orderOf u := by
    rw [← Nat.card_zpowers, hu]
    exact h4
  have hr1N := ρ₁.r_mem_normalizer
  have hr2N := ρ₂.r_mem_normalizer
  have hr3N := ρ₃.r_mem_normalizer
  have himg : piG W ρ₃.r = piG W (ρ₁.r * ρ₂.r) := by
    rw [piG_mul hr1N hr2N, ← muTabElt_coe, ← muTabElt_coe, ← muTabElt_coe]
    exact congrArg Subtype.val heq
  have hx : ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r) ∈ W ⊔ OCW W :=
    (piG_eq_iff hr3N (Subgroup.mul_mem _ hr1N hr2N)).mp himg
  have hcentr : W ⊔ OCW W ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun w hw => ?_) ((OCW_le_centralizer W).trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr huKW.2)))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W u huKW.2 w hw).symm
  have hxu : (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) * u = u * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcentr hx)
  have h1u : ρ₁.r * u = u * ρ₁.r := c.centralizes ρ₁ ρ₃ h13 huKW
  have h2u : ρ₂.r * u = u * ρ₂.r := c.centralizes ρ₂ ρ₃ h23 huKW
  have h3u : ρ₃.r * u * ρ₃.r⁻¹ = u⁻¹ := c.conj_inv ρ₃ huKW
  have h12u : (ρ₁.r * ρ₂.r) * u = u * (ρ₁.r * ρ₂.r) := by
    rw [mul_assoc, h2u, ← mul_assoc, h1u, mul_assoc]
  have e1 : ρ₁.r * ρ₂.r = ρ₃.r * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) := by group
  have e2 : (ρ₁.r * ρ₂.r) * u = u⁻¹ * (ρ₁.r * ρ₂.r) := by
    calc (ρ₁.r * ρ₂.r) * u = ρ₃.r * ((ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) * u) := by
          rw [e1]; group
      _ = ρ₃.r * (u * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r))) := by rw [hxu]
      _ = (ρ₃.r * u * ρ₃.r⁻¹) * (ρ₁.r * ρ₂.r) := by group
      _ = u⁻¹ * (ρ₁.r * ρ₂.r) := by rw [h3u]
  have hinv : u = u⁻¹ := mul_right_cancel (h12u.symm.trans e2)
  have hsq : u * u = 1 := by
    calc u * u = u * u⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel u
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega
end Indep
section Triple
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW
end Triple
section Big10
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW
end Big10
end MuTab
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Eight
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem zt_not_central [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) : ¬ ({z * t} : Set G) ⊆ Subgroup.center G := by
  exact Layer.zt_not_central3 hs

end Eight
end T8
end Asc77

end

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

theorem rep_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W)
    (hσ : σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ρ.R ≤ Subgroup.centralizer ({v} : Set G) := by
  exact CFSG.ClassicalInvolution.Asc77.T8V.rep_le_centralizerE c.toRepHooks ρ σ hσ hv
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
open scoped commutatorElement
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
section Roots
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem comm_mem_oddCoreOf_of_pow (hΩ : HypOmegaMod Ω) {M : Subgroup G} (hM : M ∈ Ω) {R₀ : Subgroup
    G}
    (hR : IsSylow2In R₀ M) {y : G} (hyN : y ∈ Subgroup.normalizer (M : Set G)) {m : ℕ}
    (hym : y ^ 2 ^ m = 1) (hyR : ∀ r ∈ R₀, y * r = r * y) : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hM
  exact commutator_mem_oddCoreOf_of_pow3 hz hR hyN hym hyR

end Roots
end T8V
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Reps
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem no_three_reps_E4 (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h12 : ρ₁.K ≠ ρ₂.K) (h13 : ρ₁.K ≠ ρ₃.K) (h23 : ρ₂.K ≠ ρ₃.K) :
    False := by
  exact CFSG.ClassicalInvolution.Asc77.T8W.no_three_reps_E4E
    (fun ρ => Thompson.muDelta_mul_self hP.hyp hW (MuTab.muTabElt_mem ρ))
    (MuTab.muTabElt_eq_iff hP hW) (MuTab.muTab_commute_iff hP hW) (MuTab.muTabElt_ne_mul hP hW)
    hW hE ρ₁ ρ₂ ρ₃ h12 h13 h23

theorem exists_rep_ne_E4 (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ : Rep Ω W) : ∃ σ : Rep Ω W, σ.K ≠ ρ.K := by
  exact CFSG.ClassicalInvolution.Asc77.T8W.exists_rep_ne_E4E (MuTab.muTabElt_eq_iff hP hW)
    (fun ρ => Thompson.muDelta_mul_self hP.hyp hW (MuTab.muTabElt_mem ρ)) hE ρ
end Reps
section Key
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_unique_member_E4 (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hKX : ¬ K ≤ omegaNbrGen Ω K) :
    ∃ J₂ ∈ omegaNbr Ω K, ∀ L ∈ Ω, L ≤ omegaNbrGen Ω K →
      2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → L = J₂ := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  obtain ⟨η₂, hη₂, hinv₂⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := MuTab.muTabCtx hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    obtain ⟨e⟩ := l7_5_2_proved G Ω hs.stand.modU W₂ hW₂ W hs.hW.1
    exact ⟨e.trans φ⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  have hρKK : ρK.K = K := rfl
  obtain ⟨σ, hσ⟩ := exists_rep_ne_E4 hP hW₂ hE₂ ρK
  have hcomm : ∀ x y : ↥(muGroup Ω W₂), x * y = y * x := by
    obtain ⟨φ⟩ := hE₂
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hnbr : σ.K ∈ omegaNbr Ω K :=
    c₂.omega_of_comm ρK σ (Ne.symm hσ) (by have := congrArg Subtype.val (hcomm
      (MuTab.muTabElt ρK) (MuTab.muTabElt σ)); exact this)
  refine ⟨σ.K, hnbr, fun L hL hLX hcard => ?_⟩
  have h611 : L ⊓ W₂ ∈ η₂ := l6_11_proved G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := hΩ.isPGroup_of_mem_USet hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := c₂.exists_rep_of_involution_mem hs.stand.cls hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_cases hLK : L = K
  · exact absurd (hLK ▸ hLX) hKX
  by_contra hLσ
  exact no_three_reps_E4 hP hW₂ hE₂ ρK σ ρL (Ne.symm hσ) (by rw [hρKK, hρLL]; exact Ne.symm hLK)
    (by rw [hρLL]; exact Ne.symm hLσ)
end Key
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.Assembly.LowTwoRank
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Sec
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem s26XMuZ2_E4_of_data (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    (hX : omegaNbrGen Ω K ≠ ⊤) :
    ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
      MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W' := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨S₂, hRS₂, hS₂X⟩ := exists_sylow_meeting_X hs
  obtain ⟨J₂, hJ₂, hK1⟩ :=
    exists_unique_member_E4 hs hE hRS₂ (T8S2.not_le_omegaNbrGen hs hX)
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  have hJ₂X : J₂ ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J₂ hJ₂
  refine T8S2.exists_muIsoZ2_of_sylow (Λ := restrictFamily Ω X) (Sect.hypOmegaGen_restrict
      hs.stand.modU X)
    ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩ (AscP1Nine3.sylowOfIsSylow2In₉ hS₂X) (J₀ := J₂.subgroupOf X)
    ⟨J₂, hJ₂.1, hJ₂X, rfl⟩ ?_
  rintro _ ⟨L, hL, hLX, rfl⟩ hcard
  have hSH : ((AscP1Nine3.sylowOfIsSylow2In₉ hS₂X : Sylow 2 ↥X) : Subgroup ↥X) =
      ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have hLS : L ⊓ (S₂ : Subgroup G) ≤ X := inf_le_left.trans hLX
  have hinf : L.subgroupOf X ⊓ ((S₂ : Subgroup G) ⊓ X).subgroupOf X =
      (L ⊓ (S₂ : Subgroup G)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hSH, hinf] at hcard
  have hc2 : Nat.card ↥((L ⊓ (S₂ : Subgroup G)).subgroupOf X) =
      Nat.card ↥(L ⊓ (S₂ : Subgroup G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
  rw [hc2] at hcard
  rw [hK1 L hL hLX hcard]

theorem s26XProper_E4 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) : omegaNbrGen Ω K ≠ ⊤ := fun htop => by
  have hle := s26_omegaNbrGen_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
  rw [htop, top_le_iff] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans hle)

theorem s26XEdgeless_E4 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    DEdgeless (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) := by
  obtain ⟨W', hW', hZ2⟩ := s26XMuZ2_E4_of_data hs hE (s26XProper_E4 hs hdisc)
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  exact s26_dEdgeless_of_muIsoZ2 (l7_5_2_proved) hGen.modU
    ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩ hW' hZ2
end Sec
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Sylow
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_sylow_RT (hs : Std8 Ω K J S R T W z t) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧ T ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  exact CFSG.ClassicalInvolution.Asc77.T8W.exists_sylow_RTE (s26_conjSub_omegaNbrGen hΩ) hs.hJ hs.hR.2.1 hs.hR.2.2 hs.hT.2.1
    hs.hT.2.2

theorem eq_J_of_mem_X (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ omegaNbrGen Ω K)
    (hcard : 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G))) : L = J := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  obtain ⟨η₂, hη₂, hinv₂⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := MuTab.muTabCtx hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    obtain ⟨e⟩ := l7_5_2_proved G Ω hs.stand.modU W₂ hW₂ W hs.hW.1
    exact ⟨e.trans φ⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hs.hT.1 hs.hT.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  have hTD : T ∈ DSet Ω W₂ := ⟨hs.hT.1, fun x hx => hSN x (hTS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hTD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let ρJ : Rep Ω W₂ := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  have h611 : L ⊓ W₂ ∈ η₂ := l6_11_proved G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := hΩ.isPGroup_of_mem_USet hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := c₂.exists_rep_of_involution_mem hs.stand.cls hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_cases hLK : L = K
  · exact absurd (hLK ▸ hLX) hKX
  by_contra hLJ
  exact no_three_reps_E4 hP hW₂ hE₂ ρK ρJ ρL (Ne.symm hs.hJ.2.1)
    (by show K ≠ ρL.K; rw [hρLL]; exact Ne.symm hLK)
    (by show J ≠ ρL.K; rw [hρLL]; exact Ne.symm hLJ)

theorem sX_normalizes_J (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {s : G} (hsS : s ∈ (S₂ : Subgroup G))
    (hsX : s ∈ omegaNbrGen Ω K) : conjSub s J = J := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  exact CFSG.ClassicalInvolution.Asc77.T8W.sX_normalizes_JE hΩ.conjInvariant (fun hR => hΩ.eight_le_of_mem_RSet hR) hs.hJ hs.hT.1
    hs.hT.2.1 hTS₂ (fun hL hLX hcard => eq_J_of_mem_X hs hE hRS₂ hTS₂ hKX hL hLX hcard) hsS hsX

theorem sX_centralizes_t (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {s : G} (hsS : s ∈ (S₂ : Subgroup G))
    (hsX : s ∈ omegaNbrGen Ω K) : s * t * s⁻¹ = t :=
  hs.ht.conj_eq (sX_normalizes_J hs hE hRS₂ hTS₂ hKX hsS hsX)
end Sylow
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Lambda
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem commutator_mem_oddCoreOf_lambda [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) :
    ∀ k ∈ K, ∀ x ∈ omegaNbrGen Ω K, ⁅k, x⁆ ∈ oddCoreOf (K ⊔ omegaNbrGen Ω K) := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hn : Generic.CITBelowU (Nat.card G) := hs.stand.below
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  set Λ : Subgroup G := K ⊔ X with hΛdef
  have hKΛ : K ≤ Λ := le_sup_left
  have hXΛ : X ≤ Λ := le_sup_right
  have hΛN : Λ ≤ sigmaNorm Ω K :=
    sup_le (s26_le_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK Relation.ReflTransGen.refl)
      (s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK)
  have hΛp : Λ ≠ ⊤ := fun htop => by
    rw [htop, top_le_iff] at hΛN
    exact hdisc (dConnected_of_sigmaNorm_eq_top hK hs.stand.trans hΛN)
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥Λ)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Λ
  have hlt : Nat.card (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) < Nat.card G := by
    have h1 : Nat.card ↥Λ < Nat.card G :=
      lt_of_le_of_ne (Subgroup.card_le_card_group Λ)
        (fun h => hΛp (Subgroup.eq_top_of_card_eq Λ h))
    exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) h1
  have hL : layerHull Ω Λ = Λ := layerHull_sup_omegaNbrGen Ω hK
  have hK' : K.subgroupOf Λ ∈ restrictFamily Ω Λ := subgroupOf_mem_restrictFamily hK hKΛ
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) with hπ
  have hKb : (K.subgroupOf Λ).map π ∈ oddQuotientFamily (restrictFamily Ω Λ) := ⟨_, hK', rfl⟩
  have hΦ : HypOmega (oddQuotientFamily (restrictFamily Ω Λ)) :=
    Sect.hypOmega_section_of_hull hs.stand.modU hs.stand.aEmpty hn hΛp hL ⟨_, hK'⟩
  have hJX : ∀ J' ∈ omegaNbr Ω K, J' ≤ X := fun J' hJ' =>
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J' hJ'
  have hnbr : ∀ J' ∈ omegaNbr Ω K, (J'.subgroupOf Λ).map π ∈
      omegaNbr (oddQuotientFamily (restrictFamily Ω Λ)) ((K.subgroupOf Λ).map π) := by
    intro J' hJ'
    have hJ'Λ : J' ≤ Λ := (hJX J' hJ').trans hXΛ
    have h1 := C25J.omegaNbr_subgroupOf_gen hΩ hKΛ hJ'Λ hJ'.1 hJ'
    obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hJ'.1
    refine T8S2.omegaNbr_map_odd (Sect.hypOmegaGen_restrict hs.stand.modU Λ) hNodd h1 ?_
    refine T8S2.map_ne_of_noTwins (Sect.hypOmegaGen_restrict hs.stand.modU Λ) hNodd
      (isUniqueInvolution_subgroupOf hs.hz hKΛ) (isUniqueInvolution_subgroupOf hzJ hJ'Λ)
      h1 ?_
    rintro ⟨-, z', hz'K, hz'J⟩
    have hJK : J' ∈ twinSet Ω K :=
      ⟨hJ'.1, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hKΛ,
        isUniqueInvolution_of_subgroupOf hz'J hJ'Λ⟩
    rw [hs.noTwins J' hJK]
  have hcomm : ∀ J' ∈ omegaNbr Ω K,
      Commutes ((K.subgroupOf Λ).map π) ((J'.subgroupOf Λ).map π) := fun J' hJ' =>
    Q3T7E9.commutes_of_mem_omegaNbr3 hΦ.toModU hΦ.exact hKb (hnbr J' hJ')
  
  have hXC : X ≤ ((Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))).comap
      π).map Λ.subtype := by
    refine iSup₂_le fun J' hJ' j hj => ?_
    have hJ'Λ : J' ≤ Λ := (hJX J' hJ').trans hXΛ
    refine ⟨⟨j, hJ'Λ hj⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm J' hJ' b hb _
      ⟨⟨j, hJ'Λ hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  intro k hk x hx
  have hkΛ : k ∈ Λ := hKΛ hk
  have hxΛ : x ∈ Λ := hXΛ hx
  have hxC : π ⟨x, hxΛ⟩ ∈ Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) := by
    obtain ⟨y, hy, hyx⟩ := hXC hx
    have hyeq : y = ⟨x, hxΛ⟩ := Subtype.ext hyx
    rw [hyeq] at hy
    exact hy
  have hcomm2 : π ⟨k, hkΛ⟩ * π ⟨x, hxΛ⟩ = π ⟨x, hxΛ⟩ * π ⟨k, hkΛ⟩ :=
    Subgroup.mem_centralizer_iff.mp hxC _
      ⟨⟨k, hkΛ⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hmem1 : π ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm2
  have hmem2 : ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ ∈ classicalInvolutionOddCore ↥Λ :=
    (QuotientGroup.eq_one_iff _).mp hmem1
  exact ⟨_, hmem2, by simp [commutatorElement_def]⟩

theorem commute_of_mem_two_subgroup [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) {P : Subgroup G} (hP : IsPGroup 2 ↥P) {k x : G} (hk : k ∈ K)
    (hx : x ∈ omegaNbrGen Ω K) (hkP : k ∈ P) (hxP : x ∈ P) : k * x = x * k := by
  have h1 := commutator_mem_oddCoreOf_lambda hs hdisc k hk x hx
  have hmemP : ⁅k, x⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hkP hxP) (P.inv_mem hkP)) (P.inv_mem hxP)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅k, x⁆) := hP.to_le (Subgroup.zpowers_le.mpr hmemP)
  have h2 : ⁅k, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1 hpg
  exact commutatorElement_eq_one_iff_mul_comm.mp h2
end Lambda
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section ZStar
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_zStar_conj [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) (h1 : C26_1)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hS₂X : IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K)) :
    ∃ g ∈ omegaNbrGen Ω K, g⁻¹ * t * g ∈ (S₂ : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hKX : ¬ K ≤ omegaNbrGen Ω K :=
    T8S2.not_le_omegaNbrGen hs (s26XProper_E4 hs hdisc)
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htJ : t ∈ J := hs.ht.mem
  have htX : t ∈ X := hJX htJ
  have htT : t ∈ (S₂ : Subgroup G) := by
    
    have hTsyl : IsSylow2In T J :=
      Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
    have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hs.hT.1
    exact hTS₂ (T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTsyl.2.1 (by omega))
  
  let SH : Sylow 2 ↥X := AscP1Nine3.sylowOfIsSylow2In₉ hS₂X
  have hSH : (SH : Subgroup ↥X) = ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have htSH : (⟨t, htX⟩ : ↥X) ∈ (SH : Subgroup ↥X) := by
    rw [hSH, Subgroup.mem_subgroupOf]
    exact ⟨htT, htX⟩
  let zt : ↥(SH : Subgroup ↥X) := ⟨⟨t, htX⟩, htSH⟩
  have hzZ : zt ∈ Subgroup.center ↥(SH : Subgroup ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsmem : (s : ↥X) ∈ ((S₂ : Subgroup G) ⊓ X).subgroupOf X := s.2
    rw [Subgroup.mem_subgroupOf] at hsmem
    have h := sX_centralizes_t hs hE hRS₂ hTS₂ hKX hsmem.1 hsmem.2
    apply Subtype.ext
    apply Subtype.ext
    show (s : ↥X).1 * t = t * (s : ↥X).1
    calc (s : ↥X).1 * t = ((s : ↥X).1 * t * (s : ↥X).1⁻¹) * (s : ↥X).1 := by group
      _ = t * (s : ↥X).1 := by rw [h]
  have ht2 : t * t = 1 := hs.ht.sq
  have hzo : orderOf zt = 2 := by
    have h2 : orderOf (t : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) hs.ht.ne_one
    have h3 : orderOf (⟨t, htX⟩ : ↥X) = 2 := (Subgroup.orderOf_mk t htX).trans h2
    exact (Subgroup.orderOf_mk _ htSH).trans h3
  have hwc : ∀ g : ↥X, g⁻¹ * (zt : ↥X) * g ∈ (SH : Subgroup ↥X) → g⁻¹ * (zt : ↥X) * g = zt := by
    intro g hg
    have hg' : g⁻¹ * (zt : ↥X) * g ∈ ((S₂ : Subgroup G) ⊓ X).subgroupOf X := hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have := hcon g.1 g.2 hg'.1
    apply Subtype.ext
    show g.1⁻¹ * t * g.1 = t
    exact this
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar SH zt hzZ hzo hwc
  
  set N : Subgroup ↥X := classicalInvolutionOddCore ↥X with hNdef
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  set π := QuotientGroup.mk' N with hπ
  have hcen' : π ⟨t, htX⟩ ∈ Subgroup.center (↥X ⧸ N) := hcen
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  have hDE := s26XEdgeless_E4 hs hdisc hE
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := s26_top_notMem_of_c26_1 h1 hs hdisc
  have hJΦ : (J.subgroupOf X).map π ∈ oddQuotientFamily (restrictFamily Ω X) :=
    ⟨_, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩
  have hzJ := isUniqueInvolution_subgroupOf hs.ht hJX
  have hzJb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd (J.subgroupOf X)) hzJ
  have hall : ∀ M ∈ oddQuotientFamily (restrictFamily Ω X), M = (J.subgroupOf X).map π := by
    intro M hM
    by_contra hne
    have hc : M ≤ Subgroup.centralizer ({π ⟨t, htX⟩} : Set (↥X ⧸ N)) := by
      intro m _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hcen' m)
    have hnbr := AscE186.mem_omegaNbr_of_le_centralizer hGen.modU hJΦ hM hne hzJb hc
    exact hDE _ hJΦ _ hM (Or.inl hnbr)
  apply htop
  have hgen := hGen.gen
  have : omegaGen (oddQuotientFamily (restrictFamily Ω X)) = (J.subgroupOf X).map π := by
    refine le_antisymm (iSup₂_le fun L hL => ?_) (le_omegaGen hJΦ)
    rw [hall L hL]
  rw [← hgen, this]
  exact hJΦ
end ZStar
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section SixTwoGen
variable {H : Type} [Group H] [Finite H]

theorem isConj_or_mem_omegaNbr_gen {Λ : Set (Subgroup H)} (hΩ : HypOmegaMod Λ) {K : Subgroup H} (hK
    : K ∈ Λ) (hAE : AEmpty Λ K)
    (hnt : ∀ K' ∈ twinSet Λ K, K' = K) {z : H} (hz : IsUniqueInvolution K z) {g : H}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Λ K := by
  exact CFSG.ClassicalInvolution.Asc77.T8W.isConj_or_mem_omegaNbr_genE hΩ.conjInvariant
    (fun hM hR hRM => Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR hRM)
    (fun hR => hΩ.eight_le_of_mem_RSet hR) hK hAE hnt hz (l6_2 H Λ hΩ K hK z hz) hne hcomm
end SixTwoGen
section Conj
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_conj_mul_E4 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) {g : G} (hgX : g ∈ omegaNbrGen Ω K)
    (hne : g⁻¹ * t * g ≠ t) (hcomm : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t) :
    ∃ y ∈ omegaNbrGen Ω K, y * t * y⁻¹ = t * (g⁻¹ * t * g) := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  have hΛ : HypOmegaMod (restrictFamily Ω X) := Sect.hypOmegaGen_restrict hs.stand.modU X
  have hKXΛ : J.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJΩ hJX
  have hA : AEmpty (restrictFamily Ω X) (J.subgroupOf X) :=
    AEmpty.restrict hs.stand.modU hJX (hs.stand.aEmpty J hJΩ)
  have hntJ : ∀ M' ∈ twinSet Ω J, M' = J :=
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hJΩ
  have hnt : ∀ K' ∈ twinSet (restrictFamily Ω X) (J.subgroupOf X), K' = J.subgroupOf X := by
    rintro _ ⟨⟨L, hL, hLX, rfl⟩, w, hwK, hwK'⟩
    have h1 := isUniqueInvolution_of_subgroupOf hwK hJX
    have h2 := isUniqueInvolution_of_subgroupOf hwK' hLX
    rw [hntJ L ⟨hL, (w : G), h1, h2⟩]
  have hz := isUniqueInvolution_subgroupOf hs.ht hJX
  set zt : ↥X := ⟨t, htX⟩ with hztdef
  set gX : ↥X := ⟨g, hgX⟩ with hgXdef
  have hne' : gX⁻¹ * zt * gX ≠ zt := fun h => hne (congrArg Subtype.val h)
  have hcomm' : zt * (gX⁻¹ * zt * gX) = gX⁻¹ * zt * gX * zt := Subtype.ext hcomm
  rcases isConj_or_mem_omegaNbr_gen hΛ hKXΛ hA hnt hz hne' hcomm' with hconj | hnbr
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
  · exfalso
    have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥X
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
    have hb : IsUniqueInvolution (conjSub gX⁻¹ (J.subgroupOf X)) (gX⁻¹ * zt * gX) := by
      have := hz.conj gX⁻¹
      rwa [inv_inv] at this
    have hconjΛ : conjSub gX⁻¹ (J.subgroupOf X) ∈ restrictFamily Ω X :=
      hΛ.conjInvariant gX⁻¹ _ hKXΛ
    have himg := T8S2.map_ne_of_noTwins hΛ hNodd hz hb hnbr (fun h => hnt _ h)
    have hnbr' := T8S2.omegaNbr_map_odd hΛ hNodd hnbr himg
    have hDE := s26XEdgeless_E4 hs hdisc hE
    exact hDE _ ⟨_, hKXΛ, rfl⟩ _ ⟨_, hconjΛ, rfl⟩ (Or.inl hnbr')
end Conj
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Good
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_good_involution_E4 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    ∃ t₁ : G, t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₁ ≠ t ∧ t * t₁ = t₁ * t ∧ z * t₁ = t₁ * z ∧
      t₁ ∈ omegaNbrGen Ω K ∧ (∀ r ∈ R, r * t₁ = t₁ * r) ∧ conjSub t₁ J = J ∧
      Subgroup.centralizer ({t₁} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({t * t₁} : Set G) ≤ sigmaNorm Ω K ∧
      ∃ J₁ : Subgroup G, J₁ ∈ Ω ∧ J₁ ≤ omegaNbrGen Ω K ∧ IsUniqueInvolution J₁ t₁ := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hKX : ¬ K ≤ omegaNbrGen Ω K := T8S2.not_le_omegaNbrGen hs (s26XProper_E4 hs hdisc)
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  obtain ⟨S₂, hRS₂, hTS₂, hS₂X⟩ := exists_sylow_RT hs
  obtain ⟨g, hgX, hgS, hgne⟩ := exists_zStar_conj hs hdisc hE (T8R.c26_1) hRS₂ hTS₂ hS₂X
  have hgiX : g⁻¹ ∈ X := X.inv_mem hgX
  have ht1X : g⁻¹ * t * g ∈ X := X.mul_mem (X.mul_mem hgiX htX) hgX
  
  have hct : g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹ = t :=
    sX_centralizes_t hs hE hRS₂ hTS₂ hKX hgS ht1X
  have htt1 : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
    calc t * (g⁻¹ * t * g) = (g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
          rw [hct]
      _ = g⁻¹ * t * g * t := by group
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hs.hR.1; omega)
  have hS₂2 : IsPGroup 2 ↥(S₂ : Subgroup G) := S₂.isPGroup'
  have hcommK : ∀ r ∈ R, r * (g⁻¹ * t * g) = g⁻¹ * t * g * r := fun r hr =>
    commute_of_mem_two_subgroup hs hdisc hS₂2 (hs.hR.2.1 hr) ht1X (hRS₂ hr) hgS
  have hzt1 : z * (g⁻¹ * t * g) = g⁻¹ * t * g * z := hcommK z hzR
  have ht1sq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have ht1ne : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply hs.ht.ne_one
    have := congrArg (fun y => g * y * g⁻¹) h
    simpa [mul_assoc] using this
  
  have hgN : g ∈ sigmaNorm Ω K := s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK hgX
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  
  have hJ1mem : conjSub g⁻¹ J ∈ dComp Ω K := ((sigmaNorm Ω K).inv_mem hgN J).mp hJmem
  have hb : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hs.ht.conj g⁻¹
    rwa [inv_inv] at this
  have hJ1Ω : conjSub g⁻¹ J ∈ Ω := hΩ.conjInvariant g⁻¹ J hJΩ
  have hC1 : Subgroup.centralizer ({g⁻¹ * t * g} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJ1Ω (hnt _ hJ1Ω) hb).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJ1mem)
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  obtain ⟨y, hyX, hy⟩ := exists_conj_mul_E4 hs hdisc hE hgX hgne htt1
  have hyN : y ∈ sigmaNorm Ω K := s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK hyX
  have hC2 : Subgroup.centralizer ({t * (g⁻¹ * t * g)} : Set G) ≤ sigmaNorm Ω K := by
    refine T8.centralizer_le_of_conj hyN ?_
    have : y⁻¹ * (t * (g⁻¹ * t * g)) * y = t := by rw [← hy]; group
    rw [this]
    exact hCt
  have hnJ : conjSub (g⁻¹ * t * g) J = J :=
    sX_normalizes_J hs hE hRS₂ hTS₂ hKX (s := g⁻¹ * t * g) hgS ht1X
  have hJ1X : conjSub g⁻¹ J ≤ X := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ J := by simpa using mem_conjSub_iff.mp hy
    have h2 : g * y * g⁻¹ ∈ X := hJX h1
    have := X.mul_mem (X.mul_mem hgiX h2) hgX
    simpa [mul_assoc] using this
  exact ⟨g⁻¹ * t * g, ht1sq, ht1ne, hgne, htt1, hzt1, ht1X, hcommK, hnJ, hC1, hC2,
    conjSub g⁻¹ J, hJ1Ω, hJ1X, hb⟩
end Good
end T8W
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
