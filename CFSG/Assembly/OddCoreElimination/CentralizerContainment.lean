module

public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentPreferred
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GroupTheory.QuasiDihedralFusion.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open scoped commutatorElement

namespace CFSG.Assembly.Dichotomy

namespace CentralizerContainment

variable {G : Type*} [Group G]

private theorem not_isCyclic_of_elemAbelian_two {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcard : 4 ≤ Nat.card B) : ¬ IsCyclic B := by
  intro hcyc
  let : IsCyclic B := hcyc
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := B)
  have hbpow : b ^ 2 = 1 := Subtype.ext (hB.2 b.val b.property)
  have hdvd : Nat.card B ∣ 2 := hb ▸ orderOf_dvd_of_pow_eq_one hbpow
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

private theorem isPGroup_of_elemAbelian_two {B : Subgroup G} (hB : IsElemAbelian 2 B) :
    IsPGroup 2 B := CFSG.Open.IsElemAbelian.isPGroup hB

private theorem conj_mem_involutionOddCore {u a h : G}
    (ha : a ∈ Subgroup.centralizer ({u} : Set G)) (hh : h ∈ involutionOddCore u) :
    a * h * a⁻¹ ∈ involutionOddCore u := by
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  exact ⟨⟨a, ha⟩ * h₀ * ⟨a, ha⟩⁻¹,
    (CFSG.Assembly.oddCore_normal _).conj_mem h₀ hh₀ ⟨a, ha⟩, rfl⟩

variable [Finite G]

private theorem le_of_inf_centralizer_le {U Y W : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUcard : 4 ≤ Nat.card U) (hY : Odd (Nat.card Y))
    (hUY : U ≤ Subgroup.normalizer (Y : Set G))
    (hle : ∀ a ∈ U, a ≠ 1 → ∀ y ∈ Y, y ∈ Subgroup.centralizer ({a} : Set G) → y ∈ W) :
    Y ≤ W := by
  let : IsMulCommutative U := hU.1
  let : CommGroup U := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 U) := ⟨isPGroup_of_elemAbelian_two hU⟩
  let : MulDistribMulAction U Y := MulDistribMulAction.compHom Y (Subgroup.inclusion hUY)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Y) (A := U) 2 (by simpa only [Nat.coprime_two_left] using hY)
    (not_isCyclic_of_elemAbelian_two hU hUcard)
  have hle' : (⨆ (a : U) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Y) ≤
      W.comap Y.subtype := by
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro r hr
    change ∀ c : Subgroup.zpowers a, c • r = r at hr
    have hafix := hr ⟨a, Subgroup.mem_zpowers a⟩
    have hc : a.val * r.val * a.val⁻¹ = r.val := congrArg Subtype.val hafix
    have hcomm : r.val ∈ Subgroup.centralizer ({a.val} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r.val * a.val = a.val * r.val * a.val⁻¹ * a.val := by rw [hc]
        _ = a.val * r.val := by rw [inv_mul_cancel_right]
    exact hle a.val a.property (fun h => ha (Subtype.ext h)) r.val r.property hcomm
  intro y hy
  have hmem : (⟨y, hy⟩ : Y) ∈
      (⨆ (a : U) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Y) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

private theorem mem_of_mem_inf_centralizer {U Y W : Subgroup G} (hU2 : IsPGroup 2 U)
    (hY : Odd (Nat.card Y)) (hUY : U ≤ Subgroup.normalizer (Y : Set G)) {u : G}
    (hUu : U ≤ Subgroup.centralizer ({u} : Set G))
    (hcomm : ∀ y ∈ Y, y ∈ Subgroup.centralizer ({u} : Set G) → ∀ a ∈ U,
      ⁅y, a⁆ ∈ involutionOddCore u)
    (hfixed : ∀ c ∈ Y, (∀ a ∈ U, a * c * a⁻¹ = c) → c ∈ W)
    (hcore : involutionOddCore u ≤ W)
    {y : G} (hy : y ∈ Y) (hyu : y ∈ Subgroup.centralizer ({u} : Set G)) : y ∈ W := by
  let H := Y ⊓ involutionOddCore u
  have hHodd : ¬ 2 ∣ Nat.card H := by
    have hodd : Odd (Nat.card H) := Odd.of_dvd_nat hY (Subgroup.card_dvd_of_le inf_le_left)
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  let α : U →* MulAut G := MulAut.conj.comp U.subtype
  have hα (a : U) (x : G) : α a x = (a : G) * x * (a : G)⁻¹ := rfl
  have hinv : ∀ a : U, ∀ x : G, x * y⁻¹ ∈ H → α a x * y⁻¹ ∈ H := by
    intro a x hx
    obtain ⟨hxY, hxO⟩ := Subgroup.mem_inf.mp hx
    have haY := hUY a.2
    have h1 : (a : G) * (x * y⁻¹) * (a : G)⁻¹ ∈ H :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp haY _).mp hxY,
        conj_mem_involutionOddCore (hUu a.2) hxO⟩
    have h2 : (a : G) * y * (a : G)⁻¹ * y⁻¹ ∈ H := by
      refine Subgroup.mem_inf.mpr ⟨Y.mul_mem ((Subgroup.mem_normalizer_iff.mp haY y).mp hy)
        (Y.inv_mem hy), ?_⟩
      have h3 := (involutionOddCore u).inv_mem (hcomm y hy hyu a a.2)
      rwa [commutatorElement_inv, commutatorElement_def] at h3
    have h4 : α a x * y⁻¹ =
        ((a : G) * (x * y⁻¹) * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹ * y⁻¹) := by
      rw [hα]
      group
    rw [h4]
    exact H.mul_mem h1 h2
  obtain ⟨c, hc, hcfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hU2 α H hHodd y).1 hinv
  obtain ⟨hcY', hcO⟩ := Subgroup.mem_inf.mp hc
  have hcY : c ∈ Y := by
    have hcy : c = (c * y⁻¹) * y := by group
    rw [hcy]
    exact Y.mul_mem hcY' hy
  have hcW : c ∈ W := hfixed c hcY fun a ha => (hα ⟨a, ha⟩ c).symm.trans (hcfix ⟨a, ha⟩)
  have hyc : y = (c * y⁻¹)⁻¹ * c := by group
  rw [hyc]
  exact W.mul_mem (W.inv_mem (hcore hcO)) hcW

private theorem twoCore_le_map_sylow_inf {X : Type*} [Group X] [Finite X] (SX : Sylow 2 X) :
    pCore 2 (X ⧸ oddCore X) ≤ ((SX : Subgroup X) ⊓
      (pCore 2 (X ⧸ oddCore X)).comap (QuotientGroup.mk' (oddCore X))).map
        (QuotientGroup.mk' (oddCore X)) := by
  intro q hq
  have h := IsPGroup.le_sylow_of_normal (pCore_isPGroup_assembly 2 _)
    (SX.mapSurjective (QuotientGroup.mk'_surjective (oddCore X)))
  rw [Sylow.coe_mapSurjective] at h
  obtain ⟨s, hs, rfl⟩ := h hq
  exact ⟨s, Subgroup.mem_inf.mpr ⟨hs, hq⟩, rfl⟩

private theorem normalizer_sylow_inf_sup_eq_top {X : Type*} [Group X] [Finite X]
    (SX : Sylow 2 X) (F : Subgroup X) [F.Normal] :
    Subgroup.normalizer (((SX : Subgroup X) ⊓ F : Subgroup X) : Set X) ⊔ F = ⊤ := by
  have h := Sylow.normalizer_sup_eq_top (CFSG.QuasiDihedralFusion.sylowInfNormal SX F)
  rwa [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype] at h

end CentralizerContainment

open CentralizerContainment

theorem centralInvolutionCentralizer : CentralInvolutionCentralizerStatement := by
  intro G _ _ hcomp S U hUS hSU hU hUcard hpref z hz hzo W hWodd hSW hcore
  obtain ⟨hzU, hzZ⟩ := Subgroup.mem_inf.mp hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hzo
  set C := Subgroup.centralizer ({z} : Set G)
  have hSC : (S : Subgroup G) ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 s hs)
  obtain ⟨hUC, hUF, -, -⟩ :=
    preferred_normal_four_core_containment hcomp S hUS hSU hU hUcard hpref hzU hz1
  have hchar : dichotomyCharP 2 (C ⧸ oddCore C) :=
    (CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two G hcomp z hzo).1
  let SC : Sylow 2 C := S.subtype hSC
  let π := QuotientGroup.mk' (oddCore C)
  let F : Subgroup C := twoCorePreimage z
  have hFnormal : F.Normal := Subgroup.Normal.comap (pCore_normal_assembly 2 _) π
  let R : Subgroup C := (SC : Subgroup C) ⊓ F
  have hRS : ∀ r ∈ R, (r : G) ∈ (S : Subgroup G) := fun r hr => by
    have h := (Subgroup.mem_inf.mp hr).1
    rwa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h
  have hQR : pCore 2 (C ⧸ oddCore C) ≤ R.map π := twoCore_le_map_sylow_inf SC
  have hfrattini : Subgroup.normalizer (R : Set C) ⊔ F = ⊤ :=
    normalizer_sylow_inf_sup_eq_top SC F
  have hOW : involutionOddCore z ≤ W := hcore z hzU hz1
  have hWN : W ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer
  have hU2 : IsPGroup 2 U := fun b =>
    ⟨1, by simpa only [pow_one] using Subtype.ext (hU.2 b.val b.property)⟩
  let M : Subgroup C := (Subgroup.normalizer (W : Set G)).subgroupOf C
  have hFM : F ≤ M := by
    intro f hf
    obtain ⟨r, hr, hrf⟩ := hQR (mem_twoCorePreimage.mp hf)
    have ho : r⁻¹ * f ∈ oddCore C := QuotientGroup.eq.mp hrf
    have hfr : f = r * (r⁻¹ * f) := by group
    rw [hfr]
    exact M.mul_mem (Subgroup.mem_subgroupOf.mpr (hSW (hRS r hr)))
      (Subgroup.mem_subgroupOf.mpr (hWN (hOW ⟨_, ho, rfl⟩)))
  have hNM : Subgroup.normalizer (R : Set C) ≤ M := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    set g := (n : G)
    have hgR : g ∈ Subgroup.normalizer ((R.map C.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map C.subtype ⟨n, hn, rfl⟩
    have hRS' : ∀ r ∈ R.map C.subtype, r ∈ (S : Subgroup G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact hRS r hr
    let Y : Subgroup G := W.map (MulAut.conj g).toMonoidHom
    have hmemY : ∀ h : G, h ∈ Y ↔ g⁻¹ * h * g ∈ W := by
      intro h
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hgw : g⁻¹ * ((MulAut.conj g).toMonoidHom w) * g = w := by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [hgw]
        exact hw
      · intro hh
        refine ⟨g⁻¹ * h * g, hh, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hYcard : Nat.card Y = Nat.card W :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hYodd : Odd (Nat.card Y) := hYcard ▸ hWodd
    have hRY : ∀ r ∈ R.map C.subtype, r ∈ Subgroup.normalizer (Y : Set G) := by
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R.map C.subtype := (Subgroup.mem_normalizer_iff''.mp hgR r).mp hr
      have hrW := hSW (hRS' _ hr')
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [hmemY, hmemY]
      have hconj : g⁻¹ * (r * h * r⁻¹) * g =
          (g⁻¹ * r * g) * (g⁻¹ * h * g) * (g⁻¹ * r * g)⁻¹ := by group
      rw [hconj]
      exact Subgroup.mem_normalizer_iff.mp hrW _
    have hUR : ∀ a ∈ U, a ∈ R.map C.subtype := fun a ha =>
      ⟨⟨a, hUC ha⟩, Subgroup.mem_inf.mpr ⟨by
        rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
        exact hUS ha, hUF (Subgroup.mem_subgroupOf.mpr ha)⟩, rfl⟩
    have hUY : U ≤ Subgroup.normalizer (Y : Set G) := fun a ha => hRY a (hUR a ha)
    have hYz : ∀ y ∈ Y, y ∈ C → y ∈ W := by
      intro y hy hyC
      let y₀ : C := ⟨y, hyC⟩
      have hcent : π y₀ ∈
          Subgroup.centralizer (pCore 2 (C ⧸ oddCore C) : Set (C ⧸ oddCore C)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        obtain ⟨r, hr, rfl⟩ := hQR hq
        have hrQ : π r ∈ pCore 2 (C ⧸ oddCore C) :=
          mem_twoCorePreimage.mp (Subgroup.mem_inf.mp hr).2
        have hyr : ⁅y, (r : G)⁆ ∈ Y := by
          have h1 : (r : G) * y⁻¹ * (r : G)⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.mp (hRY r ⟨r, hr, rfl⟩) y⁻¹).mp (Y.inv_mem hy)
          have h2 : ⁅y, (r : G)⁆ = y * ((r : G) * y⁻¹ * (r : G)⁻¹) := by
            rw [commutatorElement_def]
            group
          rw [h2]
          exact Y.mul_mem hy h1
        have hπ : π ⁅y₀, r⁆ ∈ pCore 2 (C ⧸ oddCore C) := by
          rw [map_commutatorElement, commutatorElement_def]
          exact mul_mem ((pCore_normal_assembly 2 _).conj_mem _ hrQ _) (inv_mem hrQ)
        have hodd : Odd (orderOf (π ⁅y₀, r⁆)) := by
          refine Odd.of_dvd_nat (odd_orderOf_of_mem hYodd hyr) ((orderOf_map_dvd π _).trans ?_)
          exact dvd_of_eq (Subgroup.orderOf_coe ⁅y₀, r⁆).symm
        have h1 := eq_one_of_mem_of_odd_orderOf (pCore_isPGroup_assembly 2 _) hπ hodd
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      have hQ : π y₀ ∈ pCore 2 (C ⧸ oddCore C) := hchar hcent
      have hodd : Odd (orderOf (π y₀)) := by
        refine Odd.of_dvd_nat (odd_orderOf_of_mem hYodd hy) ((orderOf_map_dvd π _).trans ?_)
        exact dvd_of_eq (Subgroup.orderOf_coe y₀).symm
      have h1 := eq_one_of_mem_of_odd_orderOf (pCore_isPGroup_assembly 2 _) hQ hodd
      exact hOW ⟨y₀, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    have hYu : ∀ u ∈ U, u ≠ 1 → ∀ y ∈ Y, y ∈ Subgroup.centralizer ({u} : Set G) → y ∈ W := by
      intro u hu hu1 y hy hyu
      obtain ⟨hUCu, -, -, hcommu⟩ :=
        preferred_normal_four_core_containment hcomp S hUS hSU hU hUcard hpref hu hu1
      refine mem_of_mem_inf_centralizer hU2 hYodd hUY hUCu (hcommu Y hYodd hUY) ?_
        (hcore u hu hu1) hy hyu
      intro c hc hfix
      refine hYz c hc (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      have hzc := hfix z hzU
      calc c * z = z * c * z⁻¹ * z := by rw [hzc]
        _ = z * c := by rw [inv_mul_cancel_right]
    have hYW : Y ≤ W := le_of_inf_centralizer_le hU hUcard.ge hYodd hUY hYu
    have hYeq : Y = W := Subgroup.eq_of_le_of_card_ge hYW hYcard.ge
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hYeq
  have htop : M = ⊤ := by
    rw [eq_top_iff, ← hfrattini]
    exact sup_le hNM hFM
  exact Subgroup.subgroupOf_eq_top.mp htop

end CFSG.Assembly.Dichotomy
