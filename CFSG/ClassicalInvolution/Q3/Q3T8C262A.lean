module

public import CFSG.ClassicalInvolution.Q3.Q3T8Sect
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8C261
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Sec
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VMu
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VProper
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Key
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A02
import CFSG.ClassicalInvolution.Asc77.AscT8S2OddEng
import CFSG.ClassicalInvolution.Asc77.AscT8S26UTopEng
import CFSG.ClassicalInvolution.Asc77.AscT8S26UActEng
import CFSG.ClassicalInvolution.Asc77.AscT8S2SecEng
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace MuTab
open CFSG.ClassicalInvolution.Asc77.MuTab
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muTabCtx (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) : Q3CL.Thompson.Ctx Ω W :=
  ⟨hP.hyp, hW, Q3CL.thompsonKey hP W hW, hP.aEmpty⟩

noncomputable def mkRep (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K) : Rep Ω W :=
  have h := Q3CL.Thompson.exists_not_mem_of_mem_D hP.hyp hW hR
  ⟨K, R, h.choose, hK, hR, hRK, h.choose_spec.1, h.choose_spec.2⟩
section Ctx
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW

theorem muTabElt_eq_iff (ρ σ : Rep Ω W) : muTabElt ρ = muTabElt σ ↔ ρ.K = σ.K := by
  have c := muTabCtx hP hW
  constructor
  · intro h
    exact c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (c.img_eq_of_K_eq ρ σ h)
end Ctx
section Realize
variable {ι : Type}

theorem exists_rep_of_member_sylow (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) (K R : ι → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hR : ∀ i, IsSylow2In (R i) (K i)) (Q : Subgroup G)
    (hQ : IsPGroup 2 ↥Q) (hRQ : ∀ i, R i ≤ Q) :
    ∃ g : G, ∀ i, ∃ ρ : Rep Ω W, ρ.K = conjSub g (K i) := by
  obtain ⟨S₀, hS₀⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := Thompson.exists_conj_mem_DSet_gen hP.hyp hW S₀
  refine ⟨g, fun i => ?_⟩
  have hRi : R i ≤ (S₀ : Subgroup G) := (hRQ i).trans hS₀
  have hD : conjSub g (R i) ∈ DSet Ω W :=
    hg (R i) (mem_RSet_of_isSylow2In (hK i) (hR i)) hRi
  exact ⟨mkRep hP hW (hP.hyp.conjInvariant g (K i) (hK i)) hD ((hR i).conj g), rfl⟩
end Realize
end MuTab
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_rep_of_involution_mem (hcl :
    Q3CL.ClassicalClause Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {t : G}
    (ht : IsUniqueInvolution J t) (htW : t ∈ W) : ∃ ρ : Rep Ω W, ρ.K = J := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet c.hW
  have hWC : W ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw t htW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ J) J :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hcl.isSubnormal_of_uniqueInvolution hJ ht)
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hRD : T ⊓ J ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW (hWT.trans hTS) (mem_RSet_of_isSylow2In hJ hR)
      (inf_le_left.trans hTS)
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep c.hΩ c.hW hJ hR hRD
  exact ⟨ρ, hρK⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_involution_of_noncomm (σ ρ : Rep
    Ω W) (hnc : σ.img * ρ.img ≠ ρ.img * σ.img)
    {zσ j : G} (hz : IsUniqueInvolution σ.K zσ) (hj : IsUniqueInvolution ρ.K j) :
    σ.r * j * σ.r⁻¹ = zσ * j := by
  have hne : σ.K ≠ ρ.K := fun h => hnc (by rw [c.img_eq_of_K_eq σ ρ h])
  have hnot : ρ.K ∉ omegaNbr Ω σ.K := fun h => hnc (c.comm_of_omega σ ρ h)
  exact c.conj_involution σ ρ hne hnot hz hj
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}
end Frame
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
namespace T8S2
open CFSG.ClassicalInvolution.Asc77.T8S2
section Odd
variable {H : Type} [Group H] [Finite H]

theorem omegaNbr_map_odd {Λ : Set (Subgroup H)} (hΛ : HypOmegaMod Λ)
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H}
    (hJ : J ∈ omegaNbr Λ K)
    (hne : J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N)) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Λ N) (K.map (QuotientGroup.mk' N)) := by
  exact CFSG.ClassicalInvolution.Asc77.T8S2.omegaNbr_map_oddE
    (fun hL hR hRL =>
      Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΛ hL hR hRL) hN hJ hne

theorem map_ne_of_noTwins {Λ : Set (Subgroup H)} (hΛ : HypOmegaMod Λ)
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H} {z t : H}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJ : J ∈ omegaNbr Λ K)
    (hnt : J ∈ twinSet Λ K → J = K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := by
  exact CFSG.ClassicalInvolution.Asc77.T8S2.map_ne_of_noTwinsE hN hz ht hJ
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΛ hz hJ ht) hnt
end Odd
end T8S2
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

theorem exists_rep (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ g : G, ∃ ρ : Rep Ω W, ρ.K = conjSub g K := by
  obtain ⟨R, hR⟩ := exists_sylow2In K
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow (ι := Unit) hP hW (fun _ => K) (fun _ => R)
    (fun _ => hK) (fun _ => hR) R hR.2.1 (fun _ => le_rfl)
  obtain ⟨ρ, hρ⟩ := hg ()
  exact ⟨g, ρ, hρ⟩
section Shapes
variable (hP : Asc77.PartIHyp Ω) (hW : W ∈ Asc77.WSet Ω)
include hP hW
end Shapes
end MuTab
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Third
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem s26Elt_eq_iff (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) : s26Elt ρ = s26Elt σ ↔ ρ.K = σ.K
    :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem s26_exists_third {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) :
    ∃ P ∈ DSet Ω W, ∃ M ∈ Ω, IsSylow2In P M ∧ M ≠ K ∧ M ≠ J ∧ M ∉ omegaNbr Ω J := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp Ω := ⟨hΩ, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hRΩ hRK
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hRD
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  let ρ : Rep Ω W := ⟨K, R, r, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  have hTT := Thompson.isTT_muDelta hΩ hW (Q3CL.thompsonCube hP W hW)
  have hTT' := T7A.isTT_map_equiv hTT φ
  have hρσ : s26Elt ρ ≠ s26Elt σ := fun h => hs.hJ.2.1 ((s26Elt_eq_iff c ρ σ).mp h).symm
  have hcomm : s26Elt ρ * s26Elt σ = s26Elt σ * s26Elt ρ :=
    Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  
  have hex : ∃ P ∈ DSet Ω W, ∃ M ∈ Ω, IsSylow2In P M ∧ M ≠ K ∧ M ≠ J := by
    by_contra hno
    push Not at hno
    have hsub : ∀ d ∈ muDelta Ω W, d = s26Elt ρ ∨ d = s26Elt σ := by
      rintro d ⟨R', hR', r', hr', hr'W, hd⟩
      obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'.1
      let ρ' : Rep Ω W := ⟨M, R', r', hM, hR', hR'M, hr', hr'W⟩
      have hdρ' : d = s26Elt ρ' := Subtype.ext hd
      by_cases hMK : M = K
      · left
        rw [hdρ']
        exact (s26Elt_eq_iff c ρ' ρ).mpr hMK
      · right
        have hMJ : M = J := hno R' hR' M hM hR'M hMK
        rw [hdρ']
        exact (s26Elt_eq_iff c ρ' σ).mpr hMJ
    obtain ⟨τ, hτT, hτ1, hτ2⟩ := s26_perm4_third (φ (s26Elt ρ)) (φ (s26Elt σ))
    have hτΔ : τ ∈ φ '' muDelta Ω W := (s26_tt_iff hTT' τ).mpr hτT
    obtain ⟨d, hd, rfl⟩ := hτΔ
    rcases hsub d hd with rfl | rfl
    · exact hτ1 rfl
    · exact hτ2 rfl
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ⟩ := hex
  refine ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, fun hnbr => ?_⟩
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hcommP : s26Elt σ * s26Elt ρP = s26Elt ρP * s26Elt σ :=
    Subtype.ext (c.comm_of_omega σ ρP hnbr)
  have hPρ : s26Elt ρP ≠ s26Elt ρ := fun h => hMK ((s26Elt_eq_iff c ρP ρ).mp h)
  have hPσ : s26Elt ρP ≠ s26Elt σ := fun h => hMJ ((s26Elt_eq_iff c ρP σ).mp h)
  have hmem : ∀ ρ' : Rep Ω W, s26IsTransp (φ (s26Elt ρ')) := fun ρ' =>
    (s26_tt_iff hTT' (φ (s26Elt ρ'))).mp ⟨s26Elt ρ', s26Elt_mem ρ', rfl⟩
  have hρT := hmem ρ
  have hσT := hmem σ
  have hPT := hmem ρP
  have hρσ' : φ (s26Elt ρ) ≠ φ (s26Elt σ) := fun h => hρσ (φ.injective h)
  have hc' : φ (s26Elt ρ) * φ (s26Elt σ) = φ (s26Elt σ) * φ (s26Elt ρ) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hPρ' : φ (s26Elt ρP) ≠ φ (s26Elt ρ) := fun h => hPρ (φ.injective h)
  have hPσ' : φ (s26Elt ρP) ≠ φ (s26Elt σ) := fun h => hPσ (φ.injective h)
  have := (s26_perm4_comm _ _ _ hρT (hσT) hρσ' hc' hPT hPρ' hPσ').2
  apply this
  rw [← map_mul, ← map_mul, ← hcommP]
end Third

theorem c26_2_of_u (h : C26_2_u) : C26_2 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨φ⟩ := hS4
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hP : PartIHyp Ω := ⟨hΩ, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, hnot⟩ := s26_exists_third hs φ
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hMΩ
  have hcent := h G Ω K J S R T W z t hs hdisc ⟨φ⟩ P hPD M hMΩ hPM.1 hMK hMJ u hu
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hrel : σ.r * u * σ.r⁻¹ = t * u :=
    c.conj_involution σ ρP (fun h => hMJ h.symm) hnot hs.ht hu
  have hcomm : σ.r * u = u * σ.r := hcent t' ht'
  have hcu : σ.r * u * σ.r⁻¹ = u := by
    rw [hcomm]
    group
  rw [hcu] at hrel
  apply hs.ht.ne_one
  have : t * u = 1 * u := by rw [← hrel, one_mul]
  exact mul_right_cancel this
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

theorem c26_2_u_of_act (h : S26Act) : C26_2_u := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  have hPsyl : IsSylow2In P M := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ
      hPD.1 hPM
  have huW : u ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hMΩ hPD hPsyl hu).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  exact CFSG.ClassicalInvolution.Asc77.c26_2_u_of_actE hs.hJ hTJ hTS hWS hs.ht huW htW
    (h G Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu)
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8S2
open CFSG.ClassicalInvolution.Asc77.T8S2
section Lift
variable {H : Type} [Group H] [Finite H]
end Lift
section Member
variable {H : Type} [Group H] [Finite H]

theorem eq_image_of_mem_USet_le_sylow {Λ : Set (Subgroup H)}
    (hΛ : HypOmegaMod Λ) (hΦ : HypOmegaMod (oddQuotientFamily Λ)) (S : Sylow 2 H)
    (J₀ : Subgroup H)
    (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀)
    {M : Subgroup (H ⧸ classicalInvolutionOddCore H)} (hM : M ∈ oddQuotientFamily Λ)
    {Ub : Subgroup (H ⧸ classicalInvolutionOddCore H)}
    (hUb : Ub ∈ USet (oddQuotientFamily Λ)) (hUbM : Ub ≤ M)
    (hUbS : Ub ≤ (S : Subgroup H).map (QuotientGroup.mk' (classicalInvolutionOddCore H))) :
    M = J₀.map (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
  set N := classicalInvolutionOddCore H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card H
  obtain ⟨J, hJ, rfl⟩ := hM
  obtain ⟨U, hU, hUJ, hUmap⟩ := C25J.exists_lift_USet_gen hΦ hN hJ hUb hUbM
  have hUSN : U ≤ (S : Subgroup H) ⊔ N := by
    intro u hu
    have h1 : QuotientGroup.mk' N u ∈ (S : Subgroup H).map (QuotientGroup.mk' N) :=
      hUbS (hUmap ▸ Subgroup.mem_map_of_mem _ hu)
    have h2 : u ∈ Subgroup.comap (QuotientGroup.mk' N) ((S : Subgroup H).map
        (QuotientGroup.mk' N)) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hU2 : IsPGroup 2 U := hΛ.isPGroup_of_mem_USet hU
  obtain ⟨n, hn, hUn⟩ := exists_conj_le_of_le_sup_odd hN S.isPGroup' hU2 hUSN
  have hJ' : conjSub n⁻¹ J ∈ Λ := hΛ.conjInvariant _ J hJ
  have hU4 : 4 ≤ Nat.card U := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΛ.exists_data_of_mem_USet hU
    exact h4
  have hle : conjSub n⁻¹ U ≤ conjSub n⁻¹ J ⊓ (S : Subgroup H) := by
    refine le_inf (conjSub_mono (n := n⁻¹) hUJ) ?_
    have := conjSub_mono (n := n⁻¹) hUn
    rwa [conjSub_inv_conjSub] at this
  have hcard : 2 < Nat.card ↥(conjSub n⁻¹ J ⊓ (S : Subgroup H)) := by
    have h1 := Subgroup.card_le_of_le hle
    rw [natCard_conjSub_eq] at h1
    omega
  have hJeq : conjSub n⁻¹ J = J₀ := hK1 _ hJ' hcard
  have hJn : J = conjSub n J₀ := by
    rw [← hJeq, conjSub_conjSub_inv]
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  rw [hJn, AscQuot.map_conjSub, hnN, conjSub_one]
end Member
section Z2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muIsoZ2_of_unique_member (hP : PartIHyp Ω) (hW : W ∈ WSet Ω) {J₀ : Subgroup G}
    (hJ₀ : J₀ ∈ Ω) (h : ∀ ρ : Rep Ω W, ρ.K = J₀) : MuIsoZ2 Ω W := by
  exact CFSG.ClassicalInvolution.Asc77.T8S2.muIsoZ2_of_unique_memberE (MuTab.muTabElt_eq_iff hP hW)
    (fun ρ => Thompson.muDelta_mul_self hP.hyp hW (MuTab.muTabElt_mem ρ)) hW
    (by
      obtain ⟨g₀, ρ₀, hρ₀⟩ := MuTab.exists_rep hP hW hJ₀
      exact ⟨ρ₀⟩) h
end Z2
section Main
variable {H : Type} [Group H] [Finite H]

theorem exists_muIsoZ2_of_sylow {Λ : Set (Subgroup H)}
    (hΛ : HypOmegaMod Λ) (hP : PartIHyp (oddQuotientFamily Λ)) (S : Sylow 2 H)
    {J₀ : Subgroup H} (hJ₀ : J₀ ∈ Λ)
    (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀) :
    ∃ W' ∈ WSet (oddQuotientFamily Λ), MuIsoZ2 (oddQuotientFamily Λ) W' := by
  have hΦ : HypOmegaMod (oddQuotientFamily Λ) := hP.hyp
  set N := classicalInvolutionOddCore H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set S' : Sylow 2 (H ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S with hS'def
  have hS' : (S' : Subgroup (H ⧸ N)) = (S : Subgroup H).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨η, hη, hinv⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΦ S'
  have hηG : η ∈ etaG (oddQuotientFamily Λ) := ⟨S', hη, hinv⟩
  set W' : Subgroup (H ⧸ N) := ⨆ U ∈ η, U with hW'def
  have hW' : W' ∈ WSet (oddQuotientFamily Λ) := ⟨η, hηG, rfl⟩
  refine ⟨W', hW', ?_⟩
  refine muIsoZ2_of_unique_member hP hW' (J₀ := J₀.map π) ⟨J₀, hJ₀, rfl⟩ fun ρ => ?_
  have hW2 : IsPGroup 2 W' := isPGroup_of_mem_WSet hW'
  have hR2 : IsPGroup 2 ρ.R := ρ.hRK.2.1
  have hRN : ρ.R ≤ Subgroup.normalizer (W' : Set (H ⧸ N)) := ρ.hR.2
  have hRW : IsPGroup 2 ↥(ρ.R ⊔ W') := hR2.to_sup_of_normal_right' hW2 hRN
  obtain ⟨S'', hS''⟩ := hRW.exists_le_sylow
  have hηS'' : ∀ V ∈ η, V ≤ (S'' : Subgroup (H ⧸ N)) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans (le_sup_right.trans hS'')
  have hcard : 2 < Nat.card ↥(ρ.K ⊓ (S'' : Subgroup (H ⧸ N))) := by
    have h8 := hΦ.eight_le_of_mem_RSet ρ.hR.1
    have h1 := Subgroup.card_le_of_le (le_inf ρ.hRK.1 (le_sup_left.trans hS''))
    omega
  have h611 := l6_11_proved (H ⧸ N) (oddQuotientFamily Λ) hΦ S'' η hηG hηS'' ρ.K ρ.hK
    hcard
  have hV := hη.1 h611
  exact eq_image_of_mem_USet_le_sylow hΛ hΦ S J₀ hK1 ρ.hK hV.1 inf_le_left
    (hS' ▸ hV.2)
end Main
end T8S2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups
section Basic
variable {G : Type} [Group G]
end Basic
section Setup
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem s26_setup {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) {P M : Subgroup G} (hPD : P ∈ DSet Ω W) (hMΩ : M ∈ Ω)
    (hPM : P ≤ M) (hMK : M ≠ K) (hMJ : M ≠ J) {u : G} (hu : IsUniqueInvolution M u) :
    ∃ (b c : G) (n : ℕ), 1 ≤ n ∧ orderOf b = 2 ^ (n + 1) ∧ orderOf c = 2 ^ (n + 1) ∧
      b ^ 2 ^ n = u ∧ c ^ 2 ^ n = t ∧ b ∈ W ∧ c ∈ W ∧ c ∈ T ∧ conjSub b K = K ∧
      conjSub b J = J ∧ b * c = c * b ∧ u ∈ W ∧ t ∈ W ∧
      (Nat.card SL(2, GaloisField 3 1)).factorization 2 = n + 2 := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hRΩ hRK
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  have hPsyl : IsSylow2In P M := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ
      hPD.1 hPM
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  
  obtain ⟨hPW, -, hPcyc, hP4, hPcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hPD hMΩ hPsyl
  obtain ⟨-, -, hTcyc, hT4, hTcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hTD hJΩ hTsyl
  have hPT : Nat.card P = Nat.card T := by
    exact Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hMΩ hJΩ hPsyl hTsyl
  have hcardUT : Nat.card ↥(T ⊓ W) = Nat.card ↥(P ⊓ W) := by omega
  obtain ⟨b, n, hn, hbU, hbo, hbcard⟩ := s26_exists_gen hPcyc hW2.to_inf_right hP4
  obtain ⟨c, n', hn', hcU, hco, hccard⟩ := s26_exists_gen hTcyc hW2.to_inf_right hT4
  have hnn : n' = n := by
    rw [hccard, hbcard] at hcardUT
    have := Nat.pow_right_injective (le_refl 2) hcardUT
    omega
  subst hnn
  have hbW : b ∈ W := hbU.2
  have hcW : c ∈ W := hcU.2
  have hbM : b ∈ M := hPM hbU.1
  have hbu : b ^ 2 ^ n' = u := s26_pow_eq_of_uniqueInvolution hu hbM hbo
  have hct : c ^ 2 ^ n' = t := s26_pow_eq_of_uniqueInvolution hs.ht (hTJ hcU.1) hco
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hK hRD hRsyl hs.hz).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hbp2 : IsPGroup 2 (Subgroup.zpowers b) := hW2.to_le (Subgroup.zpowers_le.mpr hbW)
  
  have hnc : ¬ ∀ w ∈ M, b * w = w * b := by
    intro hcen
    obtain ⟨r, hrP, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
    have hinv : r * b * r⁻¹ = b⁻¹ :=
      Q3CL.Thompson.conj_eq_inv_of_mem_inf_W hΩ hW hMΩ hPD hPsyl hrP hrW (hPW ▸ hbU)
    have h1 : r * b * r⁻¹ = b := by
      rw [← hcen r (hPM hrP)]
      group
    have h2 : b * b = 1 := by
      have : b = b⁻¹ := h1.symm.trans hinv
      calc b * b = b * b⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel b
    have h3 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hbo] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have h4 : 2 ^ 2 ≤ 2 ^ (n' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbNK : b ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK M hMΩ (Ne.symm hMK) z hs.hz b hbM hnc hbp2 (hWab b hbW z hzW)
  have hbNJ : b ∈ Subgroup.normalizer (J : Set G) :=
    hΩ.omega5 J hJΩ M hMΩ (Ne.symm hMJ) t hs.ht b hbM hnc hbp2 (hWab b hbW t htW)
  have hfac : (Nat.card SL(2, GaloisField 3 1)).factorization 2 = n' + 2 := by
    have h1 : Nat.card P = 2 ^ (Nat.card SL(2, GaloisField 3 1)).factorization 2 :=
      Sect.natCard_isSylow2In_of_member hs.stand.modU hMΩ hPsyl
    have h2 : Nat.card P = 2 ^ (n' + 2) := by
      rw [hPcard, hbcard]
      ring
    rw [h1] at h2
    exact Nat.pow_right_injective (le_refl 2) h2
  exact ⟨b, c, n', hn, hbo, hco, hbu, hct, hbW, hcW, hcU.1, conjSub_eq_of_mem_normalizer hbNK,
    conjSub_eq_of_mem_normalizer hbNJ, hWab b hbW c hcW, hbu ▸ W.pow_mem hbW _,
    htW, hfac⟩
end Setup
section Normalizer
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Normalizer
section Dichotomy
end Dichotomy
section Main
end Main
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups
section Order
variable {Y : Type} [Group Y] [Finite Y]
end Order
section Section
variable {G : Type} [Group G]
end Section
section Top

theorem s26_top_notMem_of_c26_1 (h1 : C26_1) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) :
    (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
      oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)) := by
  have hc : ∀ L'' ∈ restrictFamily Ω (omegaNbrGen Ω K),
      Nat.card (↥L'' ⧸ classicalInvolutionOddCore ↥L'') = Nat.card SL(2, GaloisField 3 1) := by
    intro L'' hL''
    obtain ⟨z', hz'⟩ :=
      (Q3T6.hypOmegaModU_restrict hs.stand.modU (omegaNbrGen Ω K)).classical L'' hL''
    exact Sect.natCard_quot_member hz'
  exact CFSG.ClassicalInvolution.Asc77.s26_top_notMem_ofE hs.hJ (h1 G Ω K J S R T W z t hs hdisc)
    (fun hL hJ' htop => s26_map_top_of_card hc hL hJ' htop)
end Top
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
section Claims
end Claims

theorem s26XTop_of_c26_1 (h1 : C26_1) : S26XTop := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc _
  exact s26_top_notMem_of_c26_1 h1 hs hdisc
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Edgeless

theorem s26_dEdgeless_of_muIsoZ2 (h752 : L7_5_2) {H : Type} [Group H] [Finite H]
    {Φ : Set (Subgroup H)} (hM : Q3T7M.HM Φ) (hP : PartIHyp Φ)
    {W' : Subgroup H} (hW' : W' ∈ WSet Φ) (hZ : MuIsoZ2 Φ W') :
    DEdgeless Φ := by
  have hΦ : HypOmegaMod Φ := hP.hyp
  have hA : ∀ L ∈ Φ, AEmpty Φ L := hP.aEmpty
  have key : ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, False := by
    intro K hK J hJ
    obtain ⟨R, T, hRsyl, hTsyl, -, hRT⟩ := AscE186.exists_commuting_sylow_pair hM hK hJ
    have hJΦ : J ∈ Φ := hJ.1
    have hKJ : K ≠ J := hJ.2.1.symm
    have hR2 : IsPGroup 2 ↥R := hRsyl.2.1
    have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
    have hTnR : T ≤ Subgroup.normalizer (R : Set H) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 : x * t = t * x := hRT x hx t ht
        have : t * x * t⁻¹ = x := by rw [← h1]; group
        rw [this]
        exact hx
      · intro hy
        have h1 : (t * x * t⁻¹) * t = t * (t * x * t⁻¹) := hRT _ hy t ht
        have e : x = t * x * t⁻¹ := by
          calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
            _ = t⁻¹ * ((t * x * t⁻¹) * t) := by rw [mul_assoc]
            _ = t⁻¹ * (t * (t * x * t⁻¹)) := by rw [h1]
            _ = t * x * t⁻¹ := by group
        rw [e]
        exact hy
    have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hR2 hTnR
    obtain ⟨S, hS⟩ := hTR2.exists_le_sylow
    have hTS : T ≤ (S : Subgroup H) := le_sup_left.trans hS
    have hRS : R ≤ (S : Subgroup H) := le_sup_right.trans hS
    obtain ⟨η, hη, hηinv⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΦ S
    obtain ⟨W₁, hW₁, hSN⟩ : ∃ W₁ : Subgroup H, W₁ ∈ WSet Φ ∧
        ∀ s ∈ (S : Subgroup H), s ∈ Subgroup.normalizer (W₁ : Set H) :=
      ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hηinv⟩, rfl⟩, fun s hs =>
        mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hηinv hs)⟩
    have hRD : R ∈ DSet Φ W₁ := ⟨mem_RSet_of_isSylow2In hK hRsyl, fun x hx => hSN x (hRS hx)⟩
    have hTD : T ∈ DSet Φ W₁ := ⟨mem_RSet_of_isSylow2In hJΦ hTsyl, fun x hx => hSN x (hTS hx)⟩
    have hTT := Thompson.isTT_muDelta hΦ hW₁ (Q3CL.thompsonCube hP W₁ hW₁)
    obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΦ hW₁ hRD
    obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΦ hW₁ hTD
    obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
    obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hTD ht' htW
    have hac : a ≠ c := fun e =>
      piG_ne_of_ne_members_gen hΦ hW₁ hRD hTD hK hJΦ hRsyl hTsyl hKJ hr ht' htW
        (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
    obtain ⟨e'⟩ := h752 H Φ hM W₁ hW₁ W' hW'
    obtain ⟨e⟩ := hZ
    have e2 := e'.trans e
    have h1 : e2 a ≠ 1 := fun h => hTT.ne_one a ha (e2.injective (by rw [h, map_one]))
    have h2 : e2 c ≠ 1 := fun h => hTT.ne_one c hc (e2.injective (by rw [h, map_one]))
    exact hac (e2.injective (s26_z2_eq _ _ h1 h2))
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J h
  · exact key J hJ K h
end Edgeless
section Section
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Section

theorem s26XEdgeless_of_muZ2 (h752 : L7_5_2) (hZ : S26XMuZ2) : S26XEdgeless := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hdisc hS4
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  exact s26_dEdgeless_of_muIsoZ2 h752 hGen.modU ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩ hW' hZ2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26XProper_proved : S26XProper := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc _ htop
  have hle := s26_omegaNbrGen_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
  rw [htop, top_le_iff] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans hle)
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8S2
open CFSG.ClassicalInvolution.Asc77.T8S2
section Key
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_unique_member (hs : Std8 Ω K J S R T W z t)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) :
    ∃ J₂ ∈ omegaNbr Ω K, ∀ L ∈ Ω, L ≤ omegaNbrGen Ω K →
      2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → L = J₂ := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨η₂, hη₂, hinv₂⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := MuTab.muTabCtx hP hW₂
  let φ₂ : ↥(muGroup Ω W₂) ≃* Equiv.Perm (Fin 4) :=
    ((l7_5_2_proved G Ω hs.stand.modU W₂ hW₂ W hs.hW.1).some).trans φ
  have hTT : Star3T.IsTT (muDelta Ω W₂) :=
    Thompson.isTT_muDelta hΩ hW₂ (Q3CL.thompsonCube hP W₂ hW₂)
  have hTT' := T7A.isTT_map_equiv hTT φ₂
  have hmem : ∀ ρ : Rep Ω W₂, s26IsTransp (φ₂ (MuTab.muTabElt ρ)) := fun ρ =>
    (s26_tt_iff hTT' _).mp ⟨_, MuTab.muTabElt_mem ρ, rfl⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  have hρKK : ρK.K = K := rfl
  have hρKR : ρK.R = R := rfl
  obtain ⟨b, hbT, hba, hab⟩ := s26_perm4_partner _ (hmem ρK)
  obtain ⟨d, hd, hdb⟩ : b ∈ φ₂ '' muDelta Ω W₂ := (s26_tt_iff hTT' b).mpr hbT
  obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
  have hne : ρK.K ≠ σ.K := fun h =>
    hba (by rw [← hdb, (MuTab.muTabElt_eq_iff hP hW₂ σ ρK).mpr h.symm])
  have hcomm : MuTab.muTabElt ρK * MuTab.muTabElt σ = MuTab.muTabElt σ * MuTab.muTabElt ρK := by
    apply φ₂.injective
    rw [map_mul, map_mul, hdb]
    exact hab
  have hnbr : σ.K ∈ omegaNbr Ω ρK.K :=
    c₂.omega_of_comm ρK σ hne (by have := congrArg Subtype.val hcomm; exact this)
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
  have hrLX : ρL.r ∈ X := by
    have h1 : ρL.r ∈ ρL.K := ρL.hRK.1 ρL.hr
    rw [hρLL] at h1
    exact hLX h1
  have hRXc : conjSub ρK.r X = X :=
    s26_conjSub_omegaNbrGen hΩ (conjSub_eq_self_of_mem (hs.hR.2.1 ρK.hr))
  by_cases hcm : MuTab.muTabElt ρK * MuTab.muTabElt ρL = MuTab.muTabElt ρL * MuTab.muTabElt ρK
  · by_cases hKL : ρL.K = ρK.K
    ·
      exfalso
      have hLK : L = K := by rw [← hρL, hKL]
      exact hKX (hLK ▸ hLX)
    ·
      have hc : φ₂ (MuTab.muTabElt ρL) = b := by
        refine s26_perm4_eq_of_comm (hmem ρK) hbT (hmem ρL) hba hab ?_ ?_
        · intro h
          exact hKL ((MuTab.muTabElt_eq_iff hP hW₂ ρL ρK).mp (φ₂.injective h))
        · rw [← map_mul, ← map_mul, hcm]
      have hLσ : MuTab.muTabElt ρL = MuTab.muTabElt σ := φ₂.injective (hc.trans hdb.symm)
      rw [← hρL]
      exact (MuTab.muTabElt_eq_iff hP hW₂ ρL σ).mp hLσ
  ·
    exfalso
    have hnc : ρK.img * ρL.img ≠ ρL.img * ρK.img := fun h => hcm (Subtype.ext h)
    have hnc' : ρL.img * ρK.img ≠ ρK.img * ρL.img := fun h => hnc h.symm
    have hconj : ρK.r * zL * ρK.r⁻¹ = z * zL :=
      c₂.conj_involution_of_noncomm ρK ρL hnc hs.hz (by rw [hρL]; exact hzL)
    have hconj' : ρL.r * z * ρL.r⁻¹ = zL * z :=
      c₂.conj_involution_of_noncomm ρL ρK hnc' (by rw [hρL]; exact hzL) hs.hz
    have hsq : (z * zL) * (z * zL) = 1 := by
      rw [← hconj]
      calc ρK.r * zL * ρK.r⁻¹ * (ρK.r * zL * ρK.r⁻¹) = ρK.r * (zL * zL) * ρK.r⁻¹ := by group
        _ = 1 := by rw [hzL.sq]; group
    have hcz : zL * z = z * zL := by
      have h5 : (z * zL)⁻¹ = z * zL := inv_eq_of_mul_eq_one_right hsq
      rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hs.hz.sq,
        inv_eq_of_mul_eq_one_right hzL.sq] at h5
    have hM1 : IsUniqueInvolution (conjSub ρL.r K) (z * zL) := by
      have := hs.hz.conj ρL.r
      rwa [hconj', hcz] at this
    have hM2 : IsUniqueInvolution (conjSub ρK.r L) (z * zL) := by
      have := hzL.conj ρK.r
      rwa [hconj] at this
    have hnt := T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins
      (hΩ.conjInvariant ρL.r K hK)
    have hM : conjSub ρK.r L = conjSub ρL.r K :=
      hnt _ ⟨hΩ.conjInvariant ρK.r L hL, z * zL, hM1, hM2⟩
    have h6 : conjSub ρL.r K ≤ X := by
      rw [← hM]
      have := conjSub_mono (n := ρK.r) hLX
      rwa [hRXc] at this
    apply hKX
    have h7 := conjSub_mono (n := ρL.r⁻¹) h6
    rw [conjSub_inv_conjSub, conjSub_eq_self_of_mem (X.inv_mem hrLX)] at h7
    exact h7
end Key
end T8S2
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
