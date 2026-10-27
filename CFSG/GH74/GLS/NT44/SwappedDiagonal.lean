module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements

import CFSG.GH74.GLS.Bg.Pu5.BalADiag
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Bg.Pu5.LPTPAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Pu5 CFSG.GH74.GLS.Bg.Pu5.BalA CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem swapped_diagonal_involution_mem_layer_not_mem_core
    {G : Type 0} [Group G] [Finite G]
    {x y u : G} {K T : Subgroup G}
    (hK : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) K)
    (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2)
    (hxy : x * y = y * x)
    (hT2 : IsPGroup 2 T)
    (hyT : y ∈ T)
    (huT : u ∈ T)
    (huK : u ∈ K)
    (hu2 : orderOf u = 2)
    (huZ : u ∉ zStar K)
    (hyK : y ∉ Subgroup.normalizer (K : Set G)) :
    let z0 : G := u * (y * u * y⁻¹)
    orderOf z0 = 2 ∧
      z0 ∈ pLayerOf 2 (Subgroup.centralizer ({y} : Set G)) ∧
      z0 ∉ CFSG.GH74.GLS.Stage1.Thm2.Recip.O22
        (Subgroup.centralizer ({y} : Set G)) ∧
      u * y * u⁻¹ = y * z0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Cy : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCy
  set D : Subgroup G := Cx ⊓ Cy with hD
  set z0 : G := u * (y * u * y⁻¹) with hz0def
  set v : G := y * u * y⁻¹ with hvdef
  have hysq : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy2
  have husq : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hysq
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right husq
  have hyCx : y ∈ Cx := by
    rw [hCx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have huCx : u ∈ Cx := hK.1 huK
  have hxCy : x ∈ Cy := by
    rw [hCy]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxy
  have hvT : v ∈ T := by
    rw [hvdef]
    exact T.mul_mem (T.mul_mem hyT huT) (T.inv_mem hyT)
  have hvCx : v ∈ Cx := by
    rw [hvdef]
    exact Cx.mul_mem (Cx.mul_mem hyCx huCx) (Cx.inv_mem hyCx)
  have hvcmap : v ∈ cmap y K := by
    rw [hvdef]
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom huK)
  have hconj_eq : conjugate K y = cmap y K := by
    rw [show conjugate K y = cmap y⁻¹ K from rfl, hyinv]
  have hvconj : v ∈ conjugate K y := by
    rw [hconj_eq]
    exact hvcmap
  have hK' : IsPCompIn 2 Cx (conjugate K y) := isPCompIn_conjugate hxy hK
  have hne : K ≠ conjugate K y := (conjugate_ne_of_not_mem_normalizer hyK).symm
  have hlecs : conjugate K y ≤ cSec K :=
    le_cSec_of_ne hK' hK hne.symm
  have huv : u * v = v * u :=
    comm_of_mem_cSec hT2 huT hvT huK (hlecs hvconj)
  have hv2 : orderOf v = 2 := by
    rw [hvdef, orderOf_conj_eq' y u, hu2]
  have hvsq : v * v = 1 := mul_self_eq_one_of_orderOf_eq_two hv2
  have hz0eq : z0 = u * v := by
    rw [hz0def, hvdef]
  have hz0sq : z0 * z0 = 1 := by
    rw [hz0eq]
    calc (u * v) * (u * v) = u * ((v * u) * v) := by group
      _ = u * ((u * v) * v) := by rw [← huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [husq, hvsq, one_mul]
  have hyv : y * v * y⁻¹ = u := by
    rw [hvdef]
    calc y * (y * u * y⁻¹) * y⁻¹ = (y * y) * u * (y⁻¹ * y⁻¹) := by group
      _ = u := by rw [hyinv, hysq]; group
  have hz0fix : y * z0 * y⁻¹ = z0 := by
    rw [hz0eq]
    calc y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
      _ = v * u := by rw [show y * u * y⁻¹ = v from hvdef.symm, hyv]
      _ = u * v := huv.symm
  have hz0comm : z0 * y = y * z0 := by
    have h' : y * z0 = z0 * y := by
      calc y * z0 = (y * z0 * y⁻¹) * y := by group
        _ = z0 * y := by rw [hz0fix]
    exact h'.symm
  have hz0memCy : z0 ∈ Cy := by
    rw [hCy]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hz0comm
  have hz0memKsup : z0 ∈ K ⊔ cmap y K := by
    rw [hz0eq]
    exact Subgroup.mul_mem_sup huK hvcmap
  have hz0I : z0 ∈ IDiag y K := by
    refine diag_two_elt hy2 hxy hK hyK ⟨hz0memKsup, hz0memCy⟩ ?_ ?_
    · exact ⟨1, by simpa [pow_two] using hz0sq⟩
    · exact ⟨u, huK, 1, one_mem _, by rw [hz0eq, hvdef, mul_one]⟩
  have hIcomp : IsPCompIn 2 D (IDiag y K) := by
    rw [hD]
    exact IG_i_gen hy2 hxy hK hyK
  have hIDCx : IDiag y K ≤ Cx := hIcomp.1.trans inf_le_left
  have hIDCy : IDiag y K ≤ Cy := hIcomp.1.trans inf_le_right
  have hz0D : z0 ∈ D := hIcomp.1 hz0I
  have hz0Cx : z0 ∈ Cx := hIDCx hz0I
  have hz0Layer : z0 ∈ pLayerOf 2 Cy := by
    have hIcomp' : IsPCompIn 2 (Cx ⊓ Cy) (IDiag y K) := by
      rw [← hD]
      exact hIcomp
    exact le_pLayerOf_of_isPCompIn_inf hx2 hxCy hIcomp' hz0I
  have hz0notO22 : z0 ∉ CFSG.GH74.GLS.Stage1.Thm2.Recip.O22 Cy := by
    intro hzO
    change z0 ∈ (pPrimePCore 2 ↥Cy).map Cy.subtype at hzO
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzO
    have hw_eq : w = (⟨z0, hz0memCy⟩ : ↥Cy) := Subtype.ext hwz
    have hz0PC : (⟨z0, hz0memCy⟩ : ↥Cy) ∈ pPrimePCore 2 ↥Cy := hw_eq ▸ hw
    let A : Subgroup ↥Cy := D.subgroupOf Cy
    let zA : ↥A := ⟨⟨z0, hz0memCy⟩, by exact hz0D⟩
    have hzAOp : zA ∈ (Op_p'p 2 ↥Cy).subgroupOf A := hz0PC
    have hzAOpA : zA ∈ Op_p'p 2 ↥A :=
      CFSG.Wreathed.OriginalAllPrime.Op_p'p_subgroupOf_le 2 A hzAOp
    have hzApc : zA ∈ pPrimePCore 2 ↥A := hzAOpA
    let e : ↥A ≃* ↥D := Subgroup.subgroupOfEquivOfLe (inf_le_right : D ≤ Cy)
    have hpcD : pPrimePCore 2 ↥D = (pPrimePCore 2 ↥A).map e.toMonoidHom :=
      (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.pPrimePCore_map_iso 2 e).symm
    let zD : ↥D := e zA
    have hzDpc : zD ∈ pPrimePCore 2 ↥D := by
      rw [hpcD]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hzApc
    have hz0O22D : z0 ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.O22 D := by
      change z0 ∈ (pPrimePCore 2 ↥D).map D.subtype
      refine Subgroup.mem_map.mpr ⟨zD, hzDpc, ?_⟩
      show (zD : G) = z0
      rfl
    have hz0cSecI : z0 ∈ cSec (IDiag y K) :=
      O22_le_cSec hIcomp hz0O22D
    let π : ↥Cx →* TwoThin.barQ ↥Cx := TwoThin.barMk ↥Cx
    let Abar : Subgroup (TwoThin.barQ ↥Cx) := (K.subgroupOf Cx).map π
    obtain ⟨hAB, hbar⟩ := IG_bar_gen hy2 hxy hK hyK hyCx
    have hbar' : ((IDiag y K).subgroupOf Cx).map π = (swapDiag hAB).range := hbar
    have hAb : CFSG.IsComponent Abar :=
      TwoThin.isComponent_map_barMk ((TwoThin.isPCompIn_two_iff.mp hK).2)
    have hAq : CFSG.Assembly.IsQuasisimple Abar :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Abar).2 hAb.1
    have hΔq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        (swapDiag hAB).range).1 (isQuasisimple_range_swapDiag hAB hAq)
    let gbar : TwoThin.barQ ↥Cx := π ⟨z0, hz0Cx⟩
    have hDelta_mem : gbar ∈ (swapDiag hAB).range := by
      have hmem : gbar ∈ ((IDiag y K).subgroupOf Cx).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hz0I)
      rwa [hbar'] at hmem
    have hDelta_norm : gbar ∈ Subgroup.normalizer ((swapDiag hAB).range :
        Set (TwoThin.barQ ↥Cx)) := Subgroup.le_normalizer hDelta_mem
    let ψ : ↥(IDiag y K) →* TwoThin.barQ ↥Cx :=
      π.comp (Subgroup.inclusion hIDCx)
    let M : Subgroup (TwoThin.barQ ↥Cx) := (pPrimeCore 2 ↥(IDiag y K)).map ψ
    have hcard : Nat.card (pPrimeCoreOf 2 (IDiag y K)) =
        Nat.card ↥(pPrimeCore 2 ↥(IDiag y K)) := by
      unfold pPrimeCoreOf
      rw [Subgroup.card_map_of_injective (IDiag y K).subtype_injective]
    have hModd : Odd (Nat.card ↥M) := by
      have hdvd : Nat.card ↥M ∣ Nat.card (pPrimeCoreOf 2 (IDiag y K)) := by
        rw [hcard]
        exact Subgroup.card_map_dvd _ _
      exact (TwoThin.card_pPrimeCoreOf_odd (IDiag y K)).of_dvd_nat hdvd
    have hcomm : ∀ q ∈ (swapDiag hAB).range, ⁅q, gbar⁆ ∈ M := by
      intro q hq
      have hqI : q ∈ ((IDiag y K).subgroupOf Cx).map π := by
        rw [hbar']
        exact hq
      obtain ⟨c, hc, rfl⟩ := hqI
      have hcI : (c : G) ∈ IDiag y K := Subgroup.mem_subgroupOf.mp hc
      have hcO : ⁅(c : G), z0⁆ ∈ pPrimeCoreOf 2 (IDiag y K) :=
        hz0cSecI.2.2 (c : G) hcI
      obtain ⟨o, ho, hoz⟩ := Subgroup.mem_map.mp
        (show ⁅(c : G), z0⁆ ∈ (pPrimeCore 2 ↥(IDiag y K)).map (IDiag y K).subtype from hcO)
      have hmemM : ψ o ∈ M := Subgroup.mem_map_of_mem ψ ho
      have hcommI : ⁅(c : G), z0⁆ ∈ IDiag y K :=
        TwoThin.pPrimeCoreOf_le (IDiag y K) hcO
      have hψ : ψ o = ⁅π c, gbar⁆ := by
        have h1 : (⟨(o : G), hIDCx o.2⟩ : ↥Cx) =
            ⟨⁅(c : G), z0⁆, hIDCx hcommI⟩ := Subtype.ext hoz
        calc ψ o = π (⟨(o : G), hIDCx o.2⟩ : ↥Cx) := rfl
          _ = π (⟨⁅(c : G), z0⁆, hIDCx hcommI⟩ : ↥Cx) := congrArg π h1
          _ = π (⁅c, (⟨z0, hz0Cx⟩ : ↥Cx)⁆) :=
              congrArg π (Subtype.ext rfl)
          _ = ⁅π c, π ⟨z0, hz0Cx⟩⁆ := by rw [map_commutatorElement]
          _ = ⁅π c, gbar⁆ := rfl
      rwa [hψ] at hmemM
    have hcentΔ : ∀ q ∈ (swapDiag hAB).range, q * gbar = gbar * q :=
      commute_of_odd_commutators hΔq hDelta_norm hModd hcomm
    have hcentA : ∀ q ∈ Abar, q * gbar = gbar * q :=
      (commute_of_mem_range_swapDiag hAB hAb.1 hDelta_mem hcentΔ).1
    have hbarA : gbar = π ⟨u, huCx⟩ * π ⟨v, hvCx⟩ := by
      rw [show gbar = π (⟨u, huCx⟩ * ⟨v, hvCx⟩) from by
        apply congrArg π
        exact Subtype.ext hz0eq]
      rw [map_mul]
    have hs_sq : π (⟨y, hyCx⟩ : ↥Cx) * π (⟨y, hyCx⟩ : ↥Cx) = 1 := by
      rw [← map_mul]
      exact congrArg π (Subtype.ext hysq)
    have hs_inv : (π (⟨y, hyCx⟩ : ↥Cx))⁻¹ = π (⟨y, hyCx⟩ : ↥Cx) :=
      inv_eq_of_mul_eq_one_right hs_sq
    have hAv : π (⟨u, huCx⟩ : ↥Cx) ∈ Abar :=
      Subgroup.mem_map_of_mem π huK
    have hBv : π (⟨v, hvCx⟩ : ↥Cx) ∈
        conjSub (π (⟨y, hyCx⟩ : ↥Cx))⁻¹ Abar := by
      have h1 : (⟨v, hvCx⟩ : ↥Cx) = (⟨y, hyCx⟩ : ↥Cx) * ⟨u, huCx⟩ *
          (⟨y, hyCx⟩ : ↥Cx)⁻¹ := by
        apply Subtype.ext
        change v = y * u * y⁻¹
        exact hvdef
      have h2 : π (⟨v, hvCx⟩ : ↥Cx) =
          (π (⟨y, hyCx⟩ : ↥Cx))⁻¹ * π (⟨u, huCx⟩ : ↥Cx) *
            π (⟨y, hyCx⟩ : ↥Cx) := by
        rw [h1, map_mul, map_mul, map_inv]
        simp [hs_inv]
      rw [h2]
      exact conj_mem_conjSub hAv
    have hBcomm : ∀ b ∈ conjSub (π (⟨y, hyCx⟩ : ↥Cx))⁻¹ Abar,
        ∀ q ∈ Abar, b * q = q * b := by
      intro b hb q hq
      have hc := Subgroup.commutator_mem_commutator hq hb
      rw [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
    have hπu_comm : ∀ q ∈ Abar, q * π (⟨u, huCx⟩ : ↥Cx) =
        π (⟨u, huCx⟩ : ↥Cx) * q := by
      intro q hq
      have h1 : q * gbar = gbar * q := hcentA q hq
      have hbq : π (⟨v, hvCx⟩ : ↥Cx) * q = q * π (⟨v, hvCx⟩ : ↥Cx) :=
        hBcomm _ hBv q hq
      rw [hbarA] at h1
      have h2 : q * π (⟨u, huCx⟩ : ↥Cx) * π (⟨v, hvCx⟩ : ↥Cx) =
          (π (⟨u, huCx⟩ : ↥Cx) * q) * π (⟨v, hvCx⟩ : ↥Cx) := by
        calc q * π (⟨u, huCx⟩ : ↥Cx) * π (⟨v, hvCx⟩ : ↥Cx)
            = q * (π (⟨u, huCx⟩ : ↥Cx) * π (⟨v, hvCx⟩ : ↥Cx)) := by group
          _ = (π (⟨u, huCx⟩ : ↥Cx) * π (⟨v, hvCx⟩ : ↥Cx)) * q := h1
          _ = π (⟨u, huCx⟩ : ↥Cx) * (π (⟨v, hvCx⟩ : ↥Cx) * q) := by group
          _ = π (⟨u, huCx⟩ : ↥Cx) * (q * π (⟨v, hvCx⟩ : ↥Cx)) := by rw [hbq]
          _ = (π (⟨u, huCx⟩ : ↥Cx) * q) * π (⟨v, hvCx⟩ : ↥Cx) := by group
      exact mul_right_cancel h2
    have hπu : ∀ m ∈ K.subgroupOf Cx,
        π ((⟨u, huCx⟩ : ↥Cx) * m * (⟨u, huCx⟩ : ↥Cx)⁻¹) = π m := by
      intro m hm
      have hmK : (m : G) ∈ K := Subgroup.mem_subgroupOf.mp hm
      have hq : π m ∈ Abar := Subgroup.mem_map_of_mem π hm
      have hcommq : π m * π (⟨u, huCx⟩ : ↥Cx) =
          π (⟨u, huCx⟩ : ↥Cx) * π m := hπu_comm (π m) hq
      have hpusq : π (⟨u, huCx⟩ : ↥Cx) * π (⟨u, huCx⟩ : ↥Cx) = 1 := by
        rw [← map_mul]
        exact congrArg π (Subtype.ext husq)
      have huinv : (π (⟨u, huCx⟩ : ↥Cx))⁻¹ = π (⟨u, huCx⟩ : ↥Cx) :=
        inv_eq_of_mul_eq_one_right hpusq
      calc π ((⟨u, huCx⟩ : ↥Cx) * m * (⟨u, huCx⟩ : ↥Cx)⁻¹)
          = π (⟨u, huCx⟩ : ↥Cx) * π m * (π (⟨u, huCx⟩ : ↥Cx))⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = π (⟨u, huCx⟩ : ↥Cx) * π m * π (⟨u, huCx⟩ : ↥Cx) := by rw [huinv]
        _ = π m := by
            calc π (⟨u, huCx⟩ : ↥Cx) * π m * π (⟨u, huCx⟩ : ↥Cx)
                = (π m * π (⟨u, huCx⟩ : ↥Cx)) * π (⟨u, huCx⟩ : ↥Cx) := by
                    rw [hcommq.symm]
              _ = π m := by rw [mul_assoc, hpusq, mul_one]
    have hucs : u ∈ cSec K :=
      TwoThin.mem_centralizerSection_of_map_eq hK.1 ((TwoThin.isPCompIn_two_iff.mp hK).2)
        huCx hπu
    exact huZ ⟨huK, hucs⟩
  have hz0ne : z0 ≠ 1 := by
    intro h1
    apply hz0notO22
    rw [h1]
    exact (CFSG.GH74.GLS.Stage1.Thm2.Recip.O22 Cy).one_mem
  have hz0ord : orderOf z0 = 2 :=
    orderOf_eq_two_of_mul_self_eq_one hz0sq hz0ne
  have hconj : u * y * u⁻¹ = y * z0 := by
    calc u * y * u⁻¹ = u * y * u := by rw [huinv]
      _ = z0 * y := by rw [hz0def, hvdef]; group
      _ = y * z0 := hz0comm
  exact ⟨hz0ord, hz0Layer, hz0notO22, hconj⟩

end CFSG.GH74.GLS.NT44

end
