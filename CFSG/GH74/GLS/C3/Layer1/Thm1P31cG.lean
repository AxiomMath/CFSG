module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Shape
public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2 CFSG.GH74.GLS.EvenSelP
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section PumpG

variable {G : Type} [Group G] [Finite G]

theorem inC2_of_center_ne_bot (hF : E2ComponentFacts) {X : Type} [Group X] [Finite X]
    (hgen : Gen4 X) {K : Subgroup X} (hcomp : InC2 ↥K ∨ InU2 ↥K) (hcen : center ↥K ≠ ⊥) :
    InC2 ↥K := by
  rcases hcomp with hC | hU
  · exact hC
  · exfalso
    obtain ⟨hq, hmod⟩ := hU
    rcases hmod with hL2 | hA7 | ⟨hL34, hel, -⟩
    · exact hcen (Stage1.Thm6.Glue.center_eq_bot_of_isL2Model
        (Stage1.Thm6.Glue.isL2Model_of_hasL2Model (Bk.B810.hasL2Model_gt_three' hL2)))
    · exact hcen (Stage1.Thm6.Glue.center_eq_bot_of_isA7Model hA7)
    · have hexp : Monoid.exponent ↥(center ↥K) ≠ 4 := by
        intro h
        have := IsElementaryAbelian.exponent_dvd_p 2 ↥(center ↥K)
        rw [h] at this
        omega
      exact hF.l34_cover ↥K hq (IsElementaryAbelian.isPGroup 2 _) hL34 hcen hexp
        (Gen4.subgroup K hgen)

structure PumpHyp (x w z b p : G) (K Λ : Subgroup G) : Prop where
  hx2 : orderOf x = 2
  hw2 : orderOf w = 2
  hz2 : orderOf z = 2
  hxw : x * w = w * x
  hbw : b * w = w * b
  hΛ : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({w} : Set G)) Λ
  hzΛ : z ∈ Λ
  hb : b * z * b⁻¹ = w * z
  hΛcen : Subgroup.center (kBar Λ) = ⊥
  hΛU : HasL2Model (kBar Λ) Odd
  hp : p * w * p⁻¹ = x * w
  hwx : w ≠ x
  huniq : ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K
  hKcen : Subgroup.center (kBar K) = ⊥

variable {x w z b p : G} {K Λ : Subgroup G}

omit [Finite G] in
theorem PumpHyp.hxY (H : PumpHyp x w z b p K Λ) : x ∈ centralizer ({w} : Set G) :=
  mem_centralizer_singleton_iff.2 H.hxw

omit [Finite G] in
theorem PumpHyp.hΛW (H : PumpHyp x w z b p K Λ) :
    Λ ≤ centralizer ({x} : Set G) ⊓ centralizer ({w} : Set G) :=
  (isPCompIn_two_iff.1 H.hΛ).1

omit [Finite G] in
theorem PumpHyp.hΛY (H : PumpHyp x w z b p K Λ) : Λ ≤ centralizer ({w} : Set G) :=
  H.hΛW.trans inf_le_right

omit [Finite G] in
theorem PumpHyp.hsO (H : PumpHyp x w z b p K Λ) :
    orderOf (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G))) = 2 :=
  orderOf_mk_centralizer H.hxY H.hx2

@[expose] def wY (w : G) : ↥(centralizer ({w} : Set G)) := ⟨w, mem_centralizer_singleton_iff.2 rfl⟩

theorem exists_lift_component {w : G} {L : Subgroup (barQ ↥(centralizer ({w} : Set G)))}
    (hL : CFSG.IsComponent L) :
    ∃ L' : Subgroup G, IsPCompIn 2 (centralizer ({w} : Set G)) L' ∧ bar w L' = L := by
  obtain ⟨LY, hLY, hLYmap⟩ := Thm1.exists_pComponent_of_quotient_component
    (X := ↥(centralizer ({w} : Set G))) hL
  have hL'Y : (LY.map (centralizer ({w} : Set G)).subtype).subgroupOf (centralizer ({w} : Set G)) = LY :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({w} : Set G)).subtype_injective LY
  refine ⟨LY.map (centralizer ({w} : Set G)).subtype, isPCompIn_two_iff.2 ⟨Subgroup.map_subtype_le LY, ?_⟩, ?_⟩
  · rw [hL'Y]
    exact (CatalogueBAlternating.pComponent_two_iff _).1 hLY
  · show ((LY.map (centralizer ({w} : Set G)).subtype).subgroupOf (centralizer ({w} : Set G))).map
      (barMk ↥(centralizer ({w} : Set G))) = L
    rw [hL'Y]
    exact hLYmap

theorem PumpHyp.diag_false (H : PumpHyp x w z b p K Λ) (hF : E2ComponentFacts) (hC2 : C2Facts)
    (hG : C3Hyp G) {L : Subgroup (barQ ↥(centralizer ({w} : Set G)))} (hL : CFSG.IsComponent L)
    (hne : conjSub (barMk ↥(centralizer ({w} : Set G)) ⟨x, H.hxY⟩)⁻¹ L ≠ L)
    (hAB : ⁅L, conjSub (barMk ↥(centralizer ({w} : Set G)) ⟨x, H.hxY⟩)⁻¹ L⁆ = ⊥)
    (hΛΔ : bar w Λ ≤ (swapDiag hAB).range) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY := H.hxY
  have hso := H.hsO
  have hs2 : orderOf (sbar x hxY) = 2 := orderOf_sbar H.hx2 hxY
  have hsinv : (barMk ↥(centralizer ({w} : Set G)) ⟨x, hxY⟩)⁻¹ = barMk ↥(centralizer ({w} : Set G)) ⟨x, hxY⟩ := inv_eq_self_of_orderOf_eq_two hs2
  by_cases hcL : Subgroup.center ↥L = ⊥
  ·
    obtain ⟨L', hL'c, hbarL'⟩ := exists_lift_component hL
    have hq : CFSG.IsQuasisimple (kBar L') := isQuasisimple_hat hL'c
    obtain ⟨e⟩ := kBar_equiv_bar hL'c
    have hcenL' : Subgroup.center (kBar L') = ⊥ := by
      let e' : kBar L' ≃* ↥L := e.trans (MulEquiv.subgroupCongr hbarL')
      have h1 : (Subgroup.center (kBar L')).map e'.toMonoidHom = Subgroup.center ↥L :=
        Subgroup.map_center_eq e'
      rw [hcL] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).1 h1
    have hnorm : x ∈ normalizer (L' : Set G) :=
      PumpGen.mem_normalizer_of_centerless hG.pRank_eq_four ⟨H.hw2, hL'c⟩ hq hcenL' hxY
    have hstab := map_conj_bar_of_normalizes (u := w) (X := L') hxY hnorm
    rw [hbarL'] at hstab
    apply hne
    rw [hsinv]
    exact hstab
  ·
    have hC : InC2 ↥L :=
      inC2_of_center_ne_bot hF (gen4_barQ hG.gen4 w) (hG.lt2o.2 w H.hw2 L hL) hcL
    have hP : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hG.gen4 H.hw2) L
    have hΛC := le_centralizer_mk H.hΛW hxY
    have hΛ2 := isTwoComponent_centralizer_mk H.hΛ hxY
    have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
    obtain ⟨-, hΔC, -, -, -, hΔq, -, -, -, -, -, ⟨eΔ⟩⟩ :=
      swapped_quasisimple_fixed_central_product (t := barMk ↥(centralizer ({w} : Set G)) ⟨x, hxY⟩) hs2
        (assembly_isQuasisimple_of_isComponent hL) hAB
    have hΔcent : (swapDiag hAB).range ≤ centralizer ({sbar x hxY} : Set _) :=
      hΔC.trans inf_le_right
    have hsubC : ((bar w Λ).subgroupOf (centralizer ({sbar x hxY} : Set _))).IsSubnormal :=
      Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top
    have hsubΔ := isSubnormal_inf_subgroupOf hsubC hΔcent
    have hΔq' : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).1 hΔq
    have hperfY : ⁅Λ.subgroupOf (centralizer ({w} : Set G)), Λ.subgroupOf (centralizer ({w} : Set G))⁆ = Λ.subgroupOf (centralizer ({w} : Set G)) :=
      commutator_self_of_isTwoComponent hΛC hΛ2
    have hperf : ⁅bar w Λ, bar w Λ⁆ = bar w Λ := by
      unfold bar
      rw [← Subgroup.map_commutator, hperfY]
    have hne' : bar w Λ ≠ ⊥ := map_barMk_ne_bot_of_perfect hperfY (ne_bot_of_isTwoComponent hΛ2)
    have hEq : bar w Λ = (swapDiag hAB).range :=
      eq_of_perfect_subnormal hΛΔ hΔq' hperf hne' hsubΔ
    obtain ⟨φ, hφs, -, -⟩ := exists_phi (le_refl Λ) H.hΛY
      (fun k hk => ⟨k, hk, 1, (pPrimeCoreOf 2 Λ).one_mem, (mul_one k).symm⟩)
    have hqΛ : CFSG.IsQuasisimple ↥(bar w Λ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hΔq'
    obtain ⟨p₂, f₂, hp₂, hf₂, hodd₂, hL₂⟩ := H.hΛU
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd₂
      have : 2 ∣ 2 ^ f₂ := dvd_pow_self 2 (by omega)
      omega
    have hJs : IsSimpleGroup (kBar Λ) := isSimpleGroup_of_lieModel' hp₂ hp₂2 hL₂
    obtain ⟨eJ⟩ := equiv_quotient_center_of_surjective hqΛ hJs φ hφs
    have hΛU2 : InU2 (kBar Λ) := ⟨isQuasisimple_hat H.hΛ, Or.inl ⟨p₂, f₂, hp₂, hf₂, hodd₂, hL₂⟩⟩
    have hΛno : ¬ IsL34Quotient (kBar Λ) := not_isL34Quotient_of_lieModel hp₂ hp₂2 hL₂
    refine hC2.centre ↥L hP hC hcL (kBar Λ) hΛU2 hΛno ⟨eJ.trans ?_⟩
    exact (GH74.E2.centerQuotientEquiv (MulEquiv.subgroupCongr hEq)).trans eΔ

end PumpG

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
