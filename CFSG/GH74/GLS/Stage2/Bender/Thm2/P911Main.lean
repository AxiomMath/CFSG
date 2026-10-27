module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Hyp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Red
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Diag
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Layer
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ZJ
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Cores

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem prop9_11core_of_leaves (hCF : CF911) (h913a : Lemma913a) (hEnd : End911)
    (h512 : IG_5_12) : Prop9_11Core := by
  intro G _ _ z k S M p hC X V N hXP hX0 hzX hXc hN hXN hV hVe hV2 hv hFm hEm
  have hH : Hyp911 z k S M p X V N :=
    ⟨hC, hXP, hX0, hzX, hXc, hN, hXN, hV, hVe, hV2, hv, hFm, hEm⟩
  have hp := hC.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hC.odd
  have hzN : z ∈ N := hXN hzX
  have hVN : V ≤ N := (hV.trans inf_le_left).trans inf_le_right
  have hVP : V ≤ Op p M := (hV.trans inf_le_left).trans inf_le_left
  have hXE : X ≤ centralizer (Em N : Set G) := h913a G z k S M p X V N hH
  obtain ⟨J, hJ, -⟩ := exists_component_not_le (N := N) (M := ⊥) (fun h => hEm (le_bot_iff.mp h))
  have hNtop : N ≠ ⊤ := hN.1
  set V' : Subgroup ↥N := V.subgroupOf N with hV'
  set z' : ↥N := ⟨z, hzN⟩ with hz'
  set O : Subgroup G := Op p M ⊓ N ⊓ Cen z with hO
  have hOle : O ≤ N := inf_le_left.trans inf_le_right
  set O' : Subgroup ↥N := O.subgroupOf N with hO'
  have hOp : IsPGroup p ↥O := hC.P_pgroup.to_le (inf_le_left.trans inf_le_left)
  have hVe' : IsElementaryAbelian p ↥V' := IsElementaryAbelian.subgroupOf hVN
  have hVc' : Nat.card ↥V' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv]; exact hV2
  have hzz' : z' * z' = 1 := Subtype.ext hC.z_mul_z
  have hVO' : V' ≤ O' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hV (Subgroup.mem_subgroupOf.mp hx))
  have hOp' : IsPGroup p ↥O' :=
    hOp.of_injective (Subgroup.subgroupOfEquivOfLe hOle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hOle).injective
  have hOz' : ∀ o ∈ O', o * z' = z' * o := by
    intro o ho
    have h1 : (o : G) ∈ Cen z := (Subgroup.mem_subgroupOf.mp ho).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h1)
  have hON' : ∀ c : ↥N, c * z' = z' * c → ∀ o ∈ O', c * o * c⁻¹ ∈ O' := by
    intro c hc o ho
    have hcz : (c : G) ∈ Cen z :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
    have hcM : (c : G) ∈ M := hC.cen_le hcz
    have hoO : (o : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
    refine Subgroup.mem_subgroupOf.mpr ⟨⟨?_, ?_⟩, ?_⟩
    · exact (mem_normalizer_iff.mp (le_normalizer_Op' p M hcM) (o : G)).mp hoO.1.1
        |> fun h => by simpa using h
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hoO.1.2) (Subgroup.inv_mem _ c.2)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcz hoO.2) (Subgroup.inv_mem _ hcz)
  have hcard : Nat.card (CFSG.LocalCores.ComponentIndex ↥N) ≤ 2 :=
    card_componentIndex_le_two (SectionalTwoRankLE.subgroup N hC.ctx.std.gen4)
  have hodd_norm : ∀ A : Subgroup ↥N, Odd (Nat.card ↥A) → A ≤ normalizer (J : Set ↥N) := by
    intro A hA a ha
    exact mem_normalizer_of_odd_orderOf hcard
      (Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha)) hJ
  have hVodd : Odd (Nat.card ↥V') := by rw [hVc']; exact hodd.pow
  have hVn : V' ≤ normalizer (J : Set ↥N) := hodd_norm V' hVodd
  have hJW : J.map N.subtype ≤ centralizer (X : Set G) := by
    have h1 : J.map N.subtype ≤ Em N := by
      rw [Em_def]
      exact Subgroup.map_mono (le_sSup hJ)
    exact h1.trans (Subgroup.le_centralizer_iff.mp hXE)
  have hH2 : ∀ v ∈ V', v ≠ 1 → layer ↥(J ⊓ centralizer ({v} : Set ↥N)) = ⊥ := by
    intro v hvV' hv1
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hvV'
    have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvN : (v : G) ∈ N := v.2
    have hvP : (v : G) ∈ Op p M := hVP hvV
    have hY : NN z p ⊤ (zpowers (v : G)) :=
      ⟨le_top, (hv (v : G) hvV hv1').2.1, (hv (v : G) hvV hv1').2.2.1,
        (hv (v : G) hvV hv1').2.2.2⟩
    have hW : IsPGroup p ↥(X ⊔ zpowers (v : G)) :=
      hC.P_pgroup.to_le (sup_le hXP (Subgroup.zpowers_le.mpr hvP))
    obtain ⟨-, hEm'⟩ := lemma_9_3 h512 G z k S M p hC N X (zpowers (v : G)) hN hXN
      (Subgroup.zpowers_le.mpr hvN) hY hW
    exact layer_comp_inf_cent_eq_bot hJ hvN hJW hEm'
  have hfaith : ∀ v ∈ V', v ≠ 1 → ¬ J ≤ centralizer ({v} : Set ↥N) :=
    fun v hv hv1 => not_le_centralizer_of_layer_eq_bot hJ (hH2 v hv hv1)
  have hV'1 : V' ≠ ⊥ := by
    intro hb
    have : Nat.card ↥V' = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hVc'] at this
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hzn : z' ∈ normalizer (J : Set ↥N) :=
    mem_normalizer_of_diagonal hJ hp hzz' hVO' hOp' hOz' hON' hVn hfaith hV'1
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥J)) :=
    odd_card_center_of_component hp hodd hFm hJ
  have hGH : GHList (↥J ⧸ center ↥J) := by
    let J' : Subgroup G := J.map N.subtype
    have hJtop : J' ≠ ⊤ := fun hJ' => hNtop (top_le_iff.mp (hJ' ▸ Subgroup.map_subtype_le J))
    let e₁ : ↥J ≃* ↥J' := J.equivMapOfInjective N.subtype N.subtype_injective
    let f : ↥J' →* ↥J ⧸ center ↥J := (QuotientGroup.mk' (center ↥J)).comp e₁.symm.toMonoidHom
    have hf : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp e₁.symm.surjective
    exact Generic.ghList_of_surjection hC.ctx.std.kgh hJtop f hf hJ.1.2.1 hJ.1.2.2
  by_cases hL34 : LieModel (↥J ⧸ center ↥J) .PSL 3 2 2
  · exact hEnd G z k S M p X V N hH hXE J hJ hL34
  · exact hCF ↥N J hJ ⟨hGH, hL34⟩ p hp hodd V' O' z' hVe' hVc' hzz' hVO' hOp' hOz' hON' hVn hzn
      hZodd hH2

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
