module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylLift
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

namespace Perp22Wyl

section Cent


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem e2_at (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) (h : PerpHypR r n Y R S t)
    {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    {J J' : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) (hne : J' ≠ J)
    (hcJ : c ∈ trivialOnQuot J) (hcJ' : c ∈ trivialOnQuot J') :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set Y)))
      (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set Y)))) := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hStd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hStd₀⟩ := hStd.core
  have hRc : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc]
    exact hJ.1
  have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hU hJ
  obtain ⟨SJ, hStdJ⟩ := exists_datum_atR hStd₀ hRc hJΩ hzJ
  have hRcJ : tightCore J = J := TwinVtx.tightCore_eq_of_mem hRc hJΩ
  have hcm : c ∈ centralizerModOdd ⊤ J :=
    ⟨Subgroup.mem_top _, hcJ.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer hcJ.1,
      fun l hl => hcJ.2 l hl⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, TwinVtx.conjClass_eq_of_mem hJ.1, twinSet_eq_of_mem_twinSet hU hJ]
    exact hJ'
  exact inO2_cent_of_twin_R h4 hT hStdJ hRcJ h.center_eq_bot hc2 hc1 hcm htc hJ'tw
    (by rwa [hRcJ]) hcJ'

end Cent

section CentPair


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem hquat_of_perpHypR (h : PerpHypR r n Y R S t) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hq : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.core.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.core.quat.some)
  exact fun M hM => forall_sylow_iso_of_exists (hq M hM)

theorem cent_pair (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : PerpHypR r n Y R S t) (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {i j : Fin 4} (hij : i ≠ j) {cc : Y}
    (hcc : cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) :
    Subgroup.centralizer ({cc} : Set Y) ≤ MGrp (CoreAssembly.conjClass (tightCore R)) W ⊔
      oddCoreIn (Subgroup.centralizer ({cc} : Set Y)) ⊔ Subgroup.centralizer ({t} : Set Y) := by
  classical
  obtain ⟨hsq, hc1, hct, hccW⟩ := F.pair_facts h c hc hij hcc
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj⟩ : ∃ k l : Fin 4, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ k l : Fin 4, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j) i j hij
  have hclC := h.partIHypG.cls
  have htq : ∀ m : Fin 4, m ≠ i → m ≠ j → cc ∈ trivialOnQuot (F.ρ m).K := by
    intro m hmi hmj
    rcases hcc with e | e
    · rw [e]; exact F.tq_prod h c hc (Ne.symm hmi) (Ne.symm hmj)
    · rw [e]
      exact (trivialOnQuot (F.ρ m).K).mul_mem (F.tq_z h c hc m)
        (F.tq_prod h c hc (Ne.symm hmi) (Ne.symm hmj))
  have htC : t ∈ Subgroup.centralizer ({cc} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hc t (F.z_mem_W c) cc hccW)
  have hrk : ∀ m : Fin 4, m ≠ i → m ≠ j → (F.ρ m).R ≤ Subgroup.centralizer ({cc} : Set Y) := by
    intro m hmi hmj
    refine c.rep_le_centralizer (F.ρ m) hccW ?_
    have hai : (F.ρ m).r * F.a i = F.a i * (F.ρ m).r :=
      c.centralizes (F.ρ m) (F.ρ i) (F.hadj m i hmi) ⟨F.a_mem_K i, F.a_mem_W i⟩
    have haj : (F.ρ m).r * F.a j = F.a j * (F.ρ m).r :=
      c.centralizes (F.ρ m) (F.ρ j) (F.hadj m j hmj) ⟨F.a_mem_K j, F.a_mem_W j⟩
    have hrt : (F.ρ m).r * t = t * (F.ρ m).r :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (isUniqueInvolution_le_centralizer (F.hz m) ((F.ρ m).hRK.1 (F.ρ m).hr))
    have hu : (F.ρ m).r * (F.a i * F.a j) = (F.a i * F.a j) * (F.ρ m).r := by
      calc (F.ρ m).r * (F.a i * F.a j) = ((F.ρ m).r * F.a i) * F.a j := by group
        _ = (F.a i * (F.ρ m).r) * F.a j := by rw [hai]
        _ = F.a i * ((F.ρ m).r * F.a j) := by group
        _ = F.a i * (F.a j * (F.ρ m).r) := by rw [haj]
        _ = (F.a i * F.a j) * (F.ρ m).r := by group
    rcases hcc with e | e
    · rw [e]; exact hu
    · rw [e]
      calc (F.ρ m).r * (t * (F.a i * F.a j)) = ((F.ρ m).r * t) * (F.a i * F.a j) := by group
        _ = (t * (F.ρ m).r) * (F.a i * F.a j) := by rw [hrt]
        _ = t * ((F.ρ m).r * (F.a i * F.a j)) := by group
        _ = t * ((F.a i * F.a j) * (F.ρ m).r) := by rw [hu]
        _ = (t * (F.a i * F.a j)) * (F.ρ m).r := by group
  have hE2 := e2_at h4 hT h hsq hc1 htC (F.mem_twinSet h c hc k) (F.mem_twinSet h c hc l)
    (F.hne l k (Ne.symm hkl)) (htq k hki hkj) (htq l hli hlj)
  have hin : TightInO2 (centBarMk cc htC) := tightInO2_top hE2
  have hlift := exists_lift_to_D hr h.core.hyp
    (fun M hM => Perp23.isPGroup_quot_of_member h hM) (hquat_of_perpHypR h) h.aEmpty_all
    (h16_of_perpHypR hr h) c.hW hc hsq hc1 hccW (F.ρ k) (F.hz k) htC (htq k hki hkj)
    (hrk k hki hkj) hin
  intro g hg
  obtain ⟨o, ho, P, hPD, hPJ⟩ := hlift g hg
  have hJ : conjSub (o * g) (F.ρ k).K ∈ CoreAssembly.conjClass (tightCore R) :=
    h.core.hyp.conjInvariant _ _ (F.ρ k).hK
  let ρ' : Rep (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.mkRep h.partIHypG c.hW hJ hPD hPJ
  have hρ'K : ρ'.K = conjSub (o * g) (F.ρ k).K := rfl
  obtain ⟨m', hm', hm'K⟩ := F.exists_conj_rep c hclC ρ'
  obtain ⟨mk, hmk, hmkK⟩ := F.exists_conj_rep c hclC (F.ρ k)
  set n' : Y := m'⁻¹ * (o * g * mk) with hn'
  have hnK : conjSub n' (F.ρ 0).K = (F.ρ 0).K := by
    rw [hn', conjSub_mul, conjSub_mul, hmkK, ← hρ'K, ← hm'K, conjSub_inv_conjSub]
  have hnt : n' * t * n'⁻¹ = t := (F.hz 0).conj_eq hnK
  have hnC : n' ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n' * t = (n' * t * n'⁻¹) * n' := by group
      _ = t * n' := by rw [hnt]
  have e : g = o⁻¹ * (m' * n' * mk⁻¹) := by rw [hn']; group
  rw [e]
  have hM₁ : ∀ x ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W,
      x ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W ⊔
        oddCoreIn (Subgroup.centralizer ({cc} : Set Y)) ⊔ Subgroup.centralizer ({t} : Set Y) :=
    fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
    ((oddCoreIn _).inv_mem ho))) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hM₁ m' hm')
      (Subgroup.mem_sup_right hnC)) (hM₁ _ ((MGrp _ W).inv_mem hmk)))

end CentPair

section Top


theorem wylD4ExclR_of_thmE {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (hE : TwinThmER r n)
    (h4s : Thm4TwinSupplyR r n) : Perp22.WylD4ExclR r n := by
  intro Y _ _ R S t h h3 K K' K₃ u₁ u₂ u₃ d hWyl
  have hT : Thm1RTwinInO2 r n := thm1RTwinInO2_of_below hr hNo h.core.twinBelow
  have h4 : Thm4RTwinBelow r n := h4s h.core.below h.core.tbelow h.core.twinBelow
  have hperp := h.kPerp_datum d.mem d.hz
  have hcard := Perp22.ncard_twins_eq_four h.partIHypG d hperp hWyl
  obtain ⟨W, hW, ⟨F⟩⟩ := exists_wylFrame h.partIHypG d hperp hcard hWyl
  have c := Q3CL.T8.ctxOf h.partIHypG hW
  have hc := WTool.comm_of_mem_wSet h.core.hyp hW
  exact F.false_of_frame h c hc hr hE h4 hT
    (fun i j hij cc hcc => cent_pair hr h4 hT h F c hc hij hcc)

end Top

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
