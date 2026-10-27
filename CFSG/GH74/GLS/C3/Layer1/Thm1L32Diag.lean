module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cG
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cEnv

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2 CFSG.GH74.GLS.EvenSelP
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.Thm1P31c

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

section Diag

variable {G : Type} [Group G] [Finite G]

theorem diag_false' (hF : E2ComponentFacts) (hC2 : C2Facts) (hG : C3Hyp G)
    {x f : G} (hx2 : orderOf x = 2) (hf2 : orderOf f = 2) (hxf : x * f = f * x)
    {Λ : Subgroup G} (hΛ : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ)
    (hΛU : HasL2Model (kBar Λ) Odd)
    {L : Subgroup (barQ ↥(centralizer ({f} : Set G)))} (hL : CFSG.IsComponent L)
    (hne : conjSub (barMk ↥(centralizer ({f} : Set G)) ⟨x, mem_centralizer_singleton_iff.2 hxf⟩)⁻¹ L ≠ L)
    (hAB : ⁅L, conjSub (barMk ↥(centralizer ({f} : Set G)) ⟨x, mem_centralizer_singleton_iff.2 hxf⟩)⁻¹ L⁆ = ⊥)
    (hΛΔ : bar f Λ ≤ (swapDiag hAB).range) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY : x ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.2 hxf
  have hΛW : Λ ≤ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) := (isPCompIn_two_iff.1 hΛ).1
  have hΛY : Λ ≤ centralizer ({f} : Set G) := hΛW.trans inf_le_right
  have hso : orderOf (⟨x, hxY⟩ : ↥(centralizer ({f} : Set G))) = 2 := orderOf_mk_centralizer hxY hx2
  have hs2 : orderOf (sbar x hxY) = 2 := orderOf_sbar hx2 hxY
  have hsinv : (barMk ↥(centralizer ({f} : Set G)) ⟨x, hxY⟩)⁻¹ = barMk ↥(centralizer ({f} : Set G)) ⟨x, hxY⟩ := inv_eq_self_of_orderOf_eq_two hs2
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
      PumpGen.mem_normalizer_of_centerless hG.pRank_eq_four ⟨hf2, hL'c⟩ hq hcenL' hxY
    have hstab := map_conj_bar_of_normalizes (u := f) (X := L') hxY hnorm
    rw [hbarL'] at hstab
    apply hne
    rw [hsinv]
    exact hstab
  ·
    have hC : InC2 ↥L :=
      inC2_of_center_ne_bot hF (gen4_barQ hG.gen4 f) (hG.lt2o.2 f hf2 L hL) hcL
    have hP : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hG.gen4 hf2) L
    have hΛC := le_centralizer_mk hΛW hxY
    have hΛ2 := isTwoComponent_centralizer_mk hΛ hxY
    have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
    obtain ⟨-, hΔC, -, -, -, hΔq, -, -, -, -, -, ⟨eΔ⟩⟩ :=
      swapped_quasisimple_fixed_central_product (t := barMk ↥(centralizer ({f} : Set G)) ⟨x, hxY⟩) hs2
        (assembly_isQuasisimple_of_isComponent hL) hAB
    have hΔcent : (swapDiag hAB).range ≤ centralizer ({sbar x hxY} : Set _) :=
      hΔC.trans inf_le_right
    have hsubC : ((bar f Λ).subgroupOf (centralizer ({sbar x hxY} : Set _))).IsSubnormal :=
      Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top
    have hsubΔ := isSubnormal_inf_subgroupOf hsubC hΔcent
    have hΔq' : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).1 hΔq
    have hperfY : ⁅Λ.subgroupOf (centralizer ({f} : Set G)), Λ.subgroupOf (centralizer ({f} : Set G))⁆ = Λ.subgroupOf (centralizer ({f} : Set G)) :=
      commutator_self_of_isTwoComponent hΛC hΛ2
    have hperf : ⁅bar f Λ, bar f Λ⁆ = bar f Λ := by
      unfold bar
      rw [← Subgroup.map_commutator, hperfY]
    have hne' : bar f Λ ≠ ⊥ := map_barMk_ne_bot_of_perfect hperfY (ne_bot_of_isTwoComponent hΛ2)
    have hEq : bar f Λ = (swapDiag hAB).range :=
      eq_of_perfect_subnormal hΛΔ hΔq' hperf hne' hsubΔ
    obtain ⟨φ, hφs, -, -⟩ := exists_phi (le_refl Λ) hΛY
      (fun k hk => ⟨k, hk, 1, (pPrimeCoreOf 2 Λ).one_mem, (mul_one k).symm⟩)
    have hqΛ : CFSG.IsQuasisimple ↥(bar f Λ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hΔq'
    obtain ⟨p₂, f₂, hp₂, hf₂, hodd₂, hL₂⟩ := hΛU
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd₂
      have : 2 ∣ 2 ^ f₂ := dvd_pow_self 2 (by omega)
      omega
    have hJs : IsSimpleGroup (kBar Λ) := isSimpleGroup_of_lieModel' hp₂ hp₂2 hL₂
    obtain ⟨eJ⟩ := equiv_quotient_center_of_surjective hqΛ hJs φ hφs
    have hΛU2 : InU2 (kBar Λ) := ⟨isQuasisimple_hat hΛ, Or.inl ⟨p₂, f₂, hp₂, hf₂, hodd₂, hL₂⟩⟩
    have hΛno : ¬ IsL34Quotient (kBar Λ) := not_isL34Quotient_of_lieModel hp₂ hp₂2 hL₂
    refine hC2.centre ↥L hP hC hcL (kBar Λ) hΛU2 hΛno ⟨eJ.trans ?_⟩
    exact (GH74.E2.centerQuotientEquiv (MulEquiv.subgroupCongr hEq)).trans eΔ

end Diag

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
