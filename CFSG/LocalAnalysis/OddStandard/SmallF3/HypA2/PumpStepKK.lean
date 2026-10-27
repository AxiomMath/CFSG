module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.GH74.GLS
open CFSG.GH74.GLS.C3.Layer1
open CFSG.GH74.GLS.C3.Layer1.PumpCalc
open CFSG.LocalAnalysis.ComponentInitial

private theorem bar_map_conj {G : Type} [Group G] [Finite G] {u z : G}
    (hz : z ∈ centralizer ({u} : Set G)) {X : Subgroup G}
    (hX : X ≤ centralizer ({u} : Set G)) :
    bar u (X.map (MulAut.conj z).toMonoidHom) =
      (bar u X).map (MulAut.conj (sbar z hz)).toMonoidHom := by
  let Y : Subgroup G := centralizer ({u} : Set G)
  have hXY : X ≤ Y := hX
  ext w
  constructor
  · intro hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hm)
    have hm_eq : m = (⟨z, hz⟩ : ↥Y) * (⟨k, hXY hk⟩ : ↥Y) * (⟨z, hz⟩ : ↥Y)⁻¹ := by
      apply Subtype.ext
      show (m : G) = z * k * z⁻¹
      rw [← hkz]
      exact MulAut.conj_apply z k
    refine ⟨TwoThin.barMk ↥Y ⟨k, hXY hk⟩,
      Subgroup.mem_map.mpr ⟨⟨k, hXY hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, ?_⟩
    rw [hm_eq, map_mul, map_mul, map_inv]
    rfl
  · intro hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hm
    have hkX : (k : G) ∈ X := Subgroup.mem_subgroupOf.mp hk
    refine ⟨(⟨z, hz⟩ : ↥Y) * k * (⟨z, hz⟩ : ↥Y)⁻¹,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(k : G), hkX, ?_⟩), ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
    · rw [← hkz, map_mul, map_mul, map_inv]
      rfl

private theorem le_of_bar_le {G : Type} [Group G] [Finite G] {u : G}
    (hbot : pPrimeCore 2 ↥(centralizer ({u} : Set G)) = ⊥)
    {X X' : Subgroup G} (hX : X ≤ centralizer ({u} : Set G))
    (h : bar u X ≤ bar u X') : X ≤ X' := by
  have hinj : Function.Injective (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
    rw [← MonoidHom.ker_eq_bot_iff, TwoThin.ker_barMk]
    exact hbot
  have h1 : X.subgroupOf (centralizer ({u} : Set G)) ≤
      X'.subgroupOf (centralizer ({u} : Set G)) :=
    (Subgroup.map_le_map_iff_of_injective hinj).1 h
  intro a ha
  have hmem : (⟨a, hX ha⟩ : ↥(centralizer ({u} : Set G))) ∈
      X.subgroupOf (centralizer ({u} : Set G)) := Subgroup.mem_subgroupOf.mpr ha
  exact Subgroup.mem_subgroupOf.mp (h1 hmem)

theorem a2Config_of_pumpUpLT {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {x x' : G} {K K' : Subgroup G} (h : PumpUpLT 2 x K x' K') : A2Config G x x' K K' := by
  have hx2 : orderOf x = 2 := h.1.1
  have hx'2 : orderOf x' = 2 := h.2.1.1
  have hxx' : x * x' = x' * x := (Subgroup.mem_centralizer_singleton_iff.mp h.2.2.1).symm
  have hxY : x ∈ centralizer ({x'} : Set G) := TwoThin.mem_centralizer_symm h.2.2.1
  have hKcomp : IsComponent (K.subgroupOf (centralizer ({x} : Set G))) :=
    Omega.isComponent_of_isPComponent_two_of_oddCore_eq_bot (hbal x hx2) h.1.2.2.2
  have hKq : IsQuasisimple ↥K :=
    IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1.2.2.1).symm hKcomp.1
  have hOddK : CFSG.oddCore ↥K = ⊥ :=
    oddCore_eq_bot_of_isComponentIn (hbal x hx2) ⟨h.1.2.2.1, hKcomp⟩
  have hCoreK : pPrimeCore 2 ↥K = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two ↥K]; exact hOddK
  have hCoreOfK : pPrimeCoreOf 2 K = ⊥ := by
    show (pPrimeCore 2 ↥K).map K.subtype = ⊥
    rw [hCoreK, Subgroup.map_bot]
  have hKx' : K ≤ centralizer ({x'} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := h.2.2.2.1.2.2 k hk
    rw [hCoreOfK, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  obtain ⟨Λ, hΛ, hK'c, ⟨L, hL, himg, hcases⟩, -, -, -⟩ := PumpRigid.step_core h hxY
  have hKpcK : IsPCompIn 2 (K ⊓ centralizer ({x'} : Set G)) K := by
    have hsub : (K.subgroupOf (K ⊓ centralizer ({x'} : Set G))).IsSubnormal := by
      have htop : K.subgroupOf (K ⊓ centralizer ({x'} : Set G)) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]; exact inf_le_left
      rw [htop]; exact Subgroup.IsSubnormal.top
    exact CFSG.GH74.Generic.S3.isPCompIn_of_subnormal_block (le_inf le_rfl hKx') hsub hKq
  have hKΛ : K = Λ := hΛ.uniq K hKpcK
  have hX_le : K ≤ centralizer ({x, x'} : Set G) := by
    rw [centralizer_pair_eq_inf]
    exact le_inf h.1.2.2.1 hKx'
  have hX_comp : IsPComponent 2 (K.subgroupOf (centralizer ({x, x'} : Set G))) := by
    rw [centralizer_pair_eq_inf, hKΛ]
    exact hΛ.pcW.2
  have hK'xY : K'.map (MulAut.conj x).toMonoidHom ≤ centralizer ({x'} : Set G) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    change x * k * x⁻¹ ∈ centralizer ({x'} : Set G)
    exact mul_mem (mul_mem hxY (hK'c.1 hk)) (inv_mem hxY)
  have hbotY : pPrimeCore 2 ↥(centralizer ({x'} : Set G)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two ↥(centralizer ({x'} : Set G))]
    exact hbal x' hx'2
  have hs2 : orderOf (sbar x hxY) = 2 := orderOf_sbar hx2 hxY
  have hsinv : (sbar x hxY)⁻¹ = sbar x hxY := inv_eq_self_of_orderOf_eq_two hs2
  have hbar_sup : bar x' (K' ⊔ K'.map (MulAut.conj x).toMonoidHom) =
      bar x' K' ⊔ bar x' (K'.map (MulAut.conj x).toMonoidHom) := by
    show ((K' ⊔ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (centralizer ({x'} : Set G))).map (TwoThin.barMk ↥(centralizer ({x'} : Set G))) =
      (K'.subgroupOf (centralizer ({x'} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({x'} : Set G))) ⊔
        ((K'.map (MulAut.conj x).toMonoidHom).subgroupOf
          (centralizer ({x'} : Set G))).map (TwoThin.barMk ↥(centralizer ({x'} : Set G)))
    rw [Subgroup.subgroupOf_sup hK'c.1 hK'xY, Subgroup.map_sup]
  have hbar_conj : bar x' (K'.map (MulAut.conj x).toMonoidHom) =
      (bar x' K').map (MulAut.conj (sbar x hxY)).toMonoidHom :=
    bar_map_conj hxY hK'c.1
  have hbar_rhs : bar x' (K' ⊔ K'.map (MulAut.conj x).toMonoidHom) =
      bar x' K' ⊔ (bar x' K').map (MulAut.conj (sbar x hxY)).toMonoidHom := by
    rw [hbar_sup, hbar_conj]
  have hbar_le : bar x' K ≤ bar x' (K' ⊔ K'.map (MulAut.conj x).toMonoidHom) := by
    rw [hKΛ, hbar_rhs]
    rcases hcases with ⟨hstab, hleL⟩ | ⟨hne, hAB, hleD⟩
    · have hbarK' : bar x' K' = L := by
        rcases himg with h' | h'
        · exact h'
        · rw [h', hstab]
      exact (hleL.trans hbarK'.ge).trans le_sup_left
    · have hEq : L ⊔ conjSub (sbar x hxY)⁻¹ L =
          bar x' K' ⊔ (bar x' K').map (MulAut.conj (sbar x hxY)).toMonoidHom := by
        rcases himg with h' | h'
        · rw [h', hsinv]
        · rw [h']
          change L ⊔ conjSub (sbar x hxY)⁻¹ L =
            conjSub (sbar x hxY)⁻¹ L ⊔ conjSub (sbar x hxY) (conjSub (sbar x hxY)⁻¹ L)
          rw [conjSub_conjSub_inv, sup_comm]
      have hrange : (swapDiag hAB).range ≤ L ⊔ conjSub (sbar x hxY)⁻¹ L := by
        rintro _ ⟨w, rfl⟩
        exact swapDiag_mem_sup hAB w
      exact hleD.trans (hrange.trans hEq.le)
  refine ⟨hx2, hx'2, hxx', hX_le, hX_comp, hK'c.1, hK'c.2, ?_⟩
  exact le_of_bar_le hbotY hKx' hbar_le

end CFSG.OddStandard.SmallF3.HypA2
