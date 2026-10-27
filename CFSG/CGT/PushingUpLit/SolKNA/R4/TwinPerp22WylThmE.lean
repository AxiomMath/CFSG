module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylHyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylMem

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp22Wyl

section Odd

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCore_le_of_alpha {A : Subgroup Y} (hA2 : IsPGroup 2 A) {cc z : Y} (hcc : cc ∈ A)
    (hcc1 : cc ≠ 1) (hz : z ∈ A) (hAC : A ≤ Subgroup.centralizer ({cc} : Set Y))
    {H : Subgroup Y} (hαH : alphaOf A ≤ H) (hCz : Subgroup.centralizer ({z} : Set Y) ≤ H) :
    oddCoreIn (Subgroup.centralizer ({cc} : Set Y)) ≤ H := by
  intro o ho
  have hAN : A ≤ Subgroup.normalizer (oddCoreIn (Subgroup.centralizer ({cc} : Set Y)) : Set Y) :=
    hAC.trans (normalizer_oddCoreIn _)
  obtain ⟨p, hp, q, hq, rfl⟩ := Lemma54Proof.exists_mul_of_mem hA2 hAN (odd_card_oddCoreIn _) ho
  refine H.mul_mem (hαH (Perp24.commutator_le_alphaOf hcc hcc1 hp)) (hCz ?_)
  have := Subgroup.mem_centralizer_iff.mp hq.2 z hz
  exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

end Odd

namespace WylFrame

section Pair


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}
  (h : PerpHypR r n Y R S t) (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
  (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

include h F c hc

theorem pair_facts {i j : Fin 4} (hij : i ≠ j) {cc : Y}
    (hcc : cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) :
    cc * cc = 1 ∧ cc ≠ 1 ∧ cc ≠ t ∧ cc ∈ W := by
  obtain ⟨h1, h2⟩ := F.a_mul_ne c hc hij
  rcases hcc with rfl | rfl
  · exact ⟨F.a_mul_sq c hc i j, h1, h2, F.a_mul_mem_W c hc i j⟩
  · exact ⟨mul_sq_of_mem_W h F c hc (F.z_mem_W c) (F.a_mul_mem_W c hc i j) F.z_sq
      (F.a_mul_sq c hc i j), F.z_mul_ne_one h c hc h2, (F.z_ne_z_mul h c hc h1).symm,
      W.mul_mem (F.z_mem_W c) (F.a_mul_mem_W c hc i j)⟩

theorem alpha_pair (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) {i j : Fin 4} (hij : i ≠ j)
    {cc : Y} (hcc : cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) :
    alphaOf (Subgroup.closure ({cc, t} : Set Y)) = alphaOf F.E := by
  obtain ⟨hsq, hc1, hct, hccW⟩ := F.pair_facts h c hc hij hcc
  obtain ⟨π, h0, h1⟩ : ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧ π 1 = j :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧ π 1 = j) i j hij
  set F' := F.perm hc π with hF'
  have hB' := F'.hyp51_B h c hc h4 hT
  have ha0 : F'.a 0 = F.a i := by
    show F.a (π 0) = F.a i
    rw [h0]
  have ha1 : F'.a 1 = F.a j := by
    show F.a (π 1) = F.a j
    rw [h1]
  have hcc' : cc = F'.a 0 * F'.a 1 ∨ cc = t * (F'.a 0 * F'.a 1) := by
    rw [ha0, ha1]
    exact hcc
  have hccB : cc ∈ F'.B := by
    rcases hcc' with rfl | rfl
    · exact F'.u_mem_B h c hc
    · exact F'.B.mul_mem (F'.z_mem_B h c hc) (F'.u_mem_B h c hc)
  have htB : t ∈ F'.B := F'.z_mem_B h c hc
  have hAB : Subgroup.closure ({cc, t} : Set Y) ≤ F'.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hccB
    · rw [Set.mem_singleton_iff.mp hx]; exact htB
  have hcomm : cc * t = t * cc := hc _ hccW _ (F.z_mem_W c)
  have hA4 : IsElemAbelian2 (Subgroup.closure ({cc, t} : Set Y)) 2 :=
    ⟨by rw [S28B.card_closure_pair_eq_four hsq F.z_sq hcomm hc1 F.z_ne_one hct.symm]; norm_num,
      Perp24.closure_pair_sq hsq F.z_sq hcomm⟩
  have hEB : F'.E ≤ F'.B := by
    rw [WylFrame.E, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact htB
    · rw [Set.mem_singleton_iff.mp hx]; exact F'.t'_mem_B h c hc
  have hE4 : IsElemAbelian2 F'.E 2 :=
    ⟨by rw [F'.E_card c hc]; norm_num, F'.E_sq c hc⟩
  exact (lemma54_odd_and_eq hB' hEB hE4).2 _ hAB hA4

end Pair

section Apply


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}
  (h : PerpHypR r n Y R S t) (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
  (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

include h F c hc

theorem mgrp_le_of {H : Subgroup Y} (hCz : Subgroup.centralizer ({t} : Set Y) ≤ H)
    (hy : (F.ρ 0).r * F.σ.r * (F.ρ 0).r⁻¹ ∈ H)
    (hg : (F.ρ 0).r * ((F.ρ 0).r * F.σ.r * (F.ρ 0).r⁻¹) ∈ H) : MGrp (CoreAssembly.conjClass (tightCore R)) W ≤ H := by
  obtain ⟨h1, -, h3, -⟩ := F.swap_k c hc 0
  refine F.mgrp_le c hc h.partIHypG.cls F.hnc hCz (centralizer_le_of_conj hCz hy h1) ?_
  refine centralizer_le_of_conj hCz hg ?_
  rw [h3, F.zt' c hc]

theorem thmE_apply (hr : 4 ≤ r) (hE : TwinThmER r n) {H : Subgroup Y}
    (hCz : Subgroup.centralizer ({t} : Set Y) ≤ H) (hM : MGrp (CoreAssembly.conjClass (tightCore R)) W ≤ H)
    (hu : ∀ i j : Fin 4, i ≠ j → ∀ cc : Y, (cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) →
      Subgroup.centralizer ({cc} : Set Y) ≤ H) : H = ⊤ := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hKΩ : (F.ρ 0).K ∈ (CoreAssembly.conjClass (tightCore R)) := (F.ρ 0).hK
  have hz : IsUniqueInvolution (F.ρ 0).K t := F.hz 0
  have hperp : KPerp (CoreAssembly.conjClass (tightCore R)) (F.ρ 0).K = twinSet (CoreAssembly.conjClass (tightCore R)) (F.ρ 0).K := h.kPerp_datum hKΩ hz
  have h16 := h16_of_perpHypR hr h
  have hzW : t ∈ W := F.z_mem_W c
  have htr := Perp23.Two.trans_of_mgrp hΩ h16 hKΩ hz c.hW hzW hCz hM
    (fun σ => F.exists_conj_rep c h.partIHypG.cls σ)
  have hstd : StdCentW (CoreAssembly.conjClass (tightCore R)) (F.ρ 0).K W H t := by
    refine ⟨hCz, ?_, ?_⟩
    · intro L hL J hJ z' hz'J hzz _
      exfalso
      have hJp : J ∈ KPerp (CoreAssembly.conjClass (tightCore R)) L := Set.mem_insert_of_mem _ hJ
      rw [A7T22.kPerp_eq_of_twin hΩ hKΩ hL, hperp] at hJp
      obtain ⟨-, w, hw, hwJ⟩ := hJp
      have hwt : w = t := (hz.eq hw).symm
      rw [hwt] at hwJ
      exact hzz (hz'J.eq hwJ)
    · intro L hL L' hL' hLL' R₁ R₂ hR₁ hR₂ hcomm x hx y hy ox oy hxyW
      have hLt : IsUniqueInvolution L t := isUniqueInvolution_of_mem_twinSet hz hL
      have hL't : IsUniqueInvolution L' t := isUniqueInvolution_of_mem_twinSet hz hL'
      obtain ⟨i, hi⟩ := F.hcover L hL.1 hLt
      obtain ⟨j, hj⟩ := F.hcover L' hL'.1 hL't
      have hij : i ≠ j := fun e => hLL' (by rw [hj, hi, e])
      have hx2 : x * x = t := T7B.mul_self_eq_of_orderOf_four hLt (hR₁.1 hx) ox
      have hy2 : y * y = t := T7B.mul_self_eq_of_orderOf_four hL't (hR₂.1 hy) oy
      have hxy : x * y = y * x := hcomm x hx y hy
      have hxy2 : (x * y) * (x * y) = 1 := by
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx2, hy2]; exact hz.sq
      have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
        Sec6Gen.card_le_two_of_le_inf hΩ hL.1 hL'.1 hLL'.symm (hR₁.2.1.to_le inf_le_left)
          (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
      have hnot : x ∉ R₂ := by
        intro hxR₂
        have hle : Subgroup.zpowers x ≤ R₁ ⊓ R₂ := Subgroup.zpowers_le.mpr ⟨hx, hxR₂⟩
        have := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, ox] at this
        omega
      have hxy1 : x * y ≠ 1 := fun h1 => hnot (by
        have : x = y⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact R₂.inv_mem hy)
      have hxyt : x * y ≠ t := fun h1 => hnot (by
        have hyx : y = x := by
          calc y = x⁻¹ * (x * y) := by group
            _ = x⁻¹ * t := by rw [h1]
            _ = x⁻¹ * (x * x) := by rw [hx2]
            _ = x := by group
        rw [← hyx]
        exact hy)
      have hxyK : x * y ∈ (F.ρ i).K ⊔ (F.ρ j).K := by
        rw [← hi, ← hj]
        exact (L ⊔ L').mul_mem (Subgroup.mem_sup_left (hR₁.1 hx))
          (Subgroup.mem_sup_right (hR₂.1 hy))
      have hK'tw : (F.ρ j).K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (F.ρ i).K := ⟨(F.ρ j).hK, t, F.hz i, F.hz j⟩
      have hcases := Q3T8.Asc77.T7E.involution_cases_of hΩ (F.ρ i).hK hK'tw
        (F.hne j i (Ne.symm hij)) (F.hz i) (F.ρ i).hRK (F.ρ j).hRK (F.hρS i) (F.hρS j)
        (F.ha i).1.1 (F.ha j).1.1 (F.ha i).2 (F.ha j).2 hxyK (F.hWS hxyW) hxy2 hxy1 hxyt
        (hc _ hxyW _ (F.a_mem_W i)) (hc _ hxyW _ (F.a_mem_W j))
      exact hu i j hij (x * y) hcases
  have hcent := centralizersSylowPairsW_of_stdCentW hΩ hz hzW hstd
  have hWnorm : ∀ s ∈ (F.S₀ : Subgroup Y), conjSub s W = W := fun s hs =>
    mem_normalizer_iff_conjSub_eq.mp
      (WTool.le_normalizer_of_le_isPGroup hΩ h16 c.hW F.S₀.isPGroup' F.hWS hs)
  have hK1 : (F.ρ 1).K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (F.ρ 0).K := ⟨(F.ρ 1).hK, t, hz, F.hz 1⟩
  have hprinted : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) (F.ρ 0).K W :=
    ⟨F.S₀, (F.ρ 0).R, (F.ρ 0).hRK, F.hρS 0, c.hW, F.hWS, hWnorm, (F.ρ 1).K, hK1,
      F.hne 1 0 (by decide), (F.ρ 1).R, mem_RSet_of_isSylow2In (F.ρ 1).hK (F.ρ 1).hRK,
      (F.ρ 1).hRK.1, F.hρS 1⟩
  exact hE Y R S t h.core (F.ρ 0).K H W hKΩ hprinted ⟨htr, hcent⟩

end Apply

end WylFrame

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
