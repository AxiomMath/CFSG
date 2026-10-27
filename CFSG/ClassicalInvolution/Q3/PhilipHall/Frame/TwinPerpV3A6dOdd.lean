module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Closure

variable {Y : Type} [Group Y]

theorem conjSub_le_of_mem_of_le {X A : Subgroup Y} {m : Y} (hm : m ∈ X) (hA : A ≤ X) :
    conjSub m A ≤ X := by
  intro x hx
  have h1 : m⁻¹ * x * m ∈ A := mem_conjSub_iff.mp hx
  have h2 : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
  rw [h2]
  exact X.mul_mem (X.mul_mem hm (hA h1)) (X.inv_mem hm)

theorem conjSub_iSup_le {M : Subgroup Y} (A : Subgroup Y) {m : Y} (hm : m ∈ M) :
    conjSub m (⨆ m' : ↥M, conjSub (m' : Y) A) ≤ ⨆ m' : ↥M, conjSub (m' : Y) A := by
  rw [conjSub_iSup]
  refine iSup_le fun m' => ?_
  rw [← conjSub_mul]
  exact le_iSup (fun m'' : ↥M => conjSub (m'' : Y) A) ⟨m * m', M.mul_mem hm m'.2⟩

variable (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y)

theorem ae6E_le_rLayer : ae6E Ω u ≤ rLayer Ω u := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem ae6D_le_ae6I : ae6D Ω W u ≤ ae6I Ω W u :=
  iSup_le fun m => conjSub_le_of_mem_of_le (M_le_ae6I Ω W u m.2)
    ((ae6E_le_rLayer Ω u).trans (rLayer_le_ae6I Ω W u))

end Closure


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

section Orbit

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
include H

theorem ae6I_eq_iSup :
    ae6I Ω[R] W (u₁ * u₂) =
      ⨆ m : ↥(MGrp Ω[R] W), conjSub (m : Y) (rLayer Ω[R] (u₁ * u₂)) := by
  set M := MGrp Ω[R] W with hM
  set Yu := rLayer Ω[R] (u₁ * u₂) with hYu
  have hmem : ∀ m : ↥M, conjSub (m : Y) Yu ≤ ae6I Ω[R] W (u₁ * u₂) := fun m =>
    conjSub_le_of_mem_of_le (M_le_ae6I _ _ _ m.2) (rLayer_le_ae6I _ _ _)
  refine le_antisymm (sup_le ?_ ?_) (iSup_le hmem)
  · have hK : K ≤ ⨆ m : ↥M, conjSub (m : Y) Yu := by
      obtain ⟨m₃, hm₃, hmK⟩ := exists_M_conj_of_mem_D H H.hK₃
      have e : K = conjSub m₃⁻¹ K₃ := by rw [← hmK, conjSub_inv_conjSub]
      rw [e]
      exact (conjSub_mono (K₃_le_rLayer H)).trans
        (le_iSup (fun m : ↥M => conjSub (m : Y) Yu) ⟨m₃⁻¹, M.inv_mem hm₃⟩)
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨m, hm, rfl⟩ := exists_M_conj_of_mem_D H hJ
    exact (conjSub_mono hK).trans (conjSub_iSup_le Yu hm)
  · exact le_iSup_of_le ⟨1, M.one_mem⟩ (le_of_eq (conjSub_one Yu).symm)

theorem conjSub_ae6I_eq {c : Y}
    (hc : ∀ m ∈ MGrp Ω[R] W, c * (m * (u₁ * u₂) * m⁻¹) = (m * (u₁ * u₂) * m⁻¹) * c) :
    conjSub c (ae6I Ω[R] W (u₁ * u₂)) = ae6I Ω[R] W (u₁ * u₂) := by
  have hΩ := hypOf H
  have inner : ∀ (c m : Y), m ∈ MGrp Ω[R] W →
      c * (m * (u₁ * u₂) * m⁻¹) = (m * (u₁ * u₂) * m⁻¹) * c →
        conjSub c (conjSub m (rLayer Ω[R] (u₁ * u₂))) = conjSub m (rLayer Ω[R] (u₁ * u₂)) := by
    intro c m hm h
    have hm' : m⁻¹ * c * m ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m⁻¹ * c * m * (u₁ * u₂)
          = m⁻¹ * (c * (m * (u₁ * u₂) * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * (u₁ * u₂) * m⁻¹) * c) * m := by rw [h]
        _ = (u₁ * u₂) * (m⁻¹ * c * m) := by group
    have e : c * m = m * (m⁻¹ * c * m) := by group
    rw [← conjSub_mul, e, conjSub_mul, TwinMu.Pf3.conjSub_rLayer hΩ hm']
  have key : ∀ c : Y,
      (∀ m ∈ MGrp Ω[R] W, c * (m * (u₁ * u₂) * m⁻¹) = (m * (u₁ * u₂) * m⁻¹) * c) →
        conjSub c (ae6I Ω[R] W (u₁ * u₂)) ≤ ae6I Ω[R] W (u₁ * u₂) := by
    intro c hc
    rw [ae6I_eq_iSup H, conjSub_iSup]
    refine iSup_le fun m => ?_
    rw [inner c m m.2 (hc m m.2)]
    exact le_iSup (fun m' : ↥(MGrp Ω[R] W) => conjSub (m' : Y) (rLayer Ω[R] (u₁ * u₂))) m
  refine le_antisymm (key c hc) ?_
  have hc' : ∀ m ∈ MGrp Ω[R] W,
      c⁻¹ * (m * (u₁ * u₂) * m⁻¹) = (m * (u₁ * u₂) * m⁻¹) * c⁻¹ := fun m hm =>
    ((Commute.inv_left (show Commute c (m * (u₁ * u₂) * m⁻¹) from hc m hm))).eq
  have h2 := conjSub_mono (n := c) (key c⁻¹ hc')
  rwa [conjSub_conjSub_inv] at h2

theorem conjSub_ae6I_of_orbit
    (horb : ∀ m ∈ MGrp Ω[R] W, ∃ x, (x = 1 ∨ x = t ∨ x = a₁ * a₂ * a₃ * a₄ ∨
        x = a₁ * a₂ * a₃ * a₄ * t) ∧ m * (a₁ * a₂) * m⁻¹ = a₁ * a₂ * x)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {c : Y}
    (hcP : ∀ p ∈ TwinSecXg.twinJoin Ω[R] K, c * p = p * c) :
    conjSub c (ae6I Ω[R] W (u₁ * u₂)) = ae6I Ω[R] W (u₁ * u₂) := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hKt : K ∈ twinSet Ω[R] K := mem_twinSet_self hd.mem hd.hz
  have hle : ∀ J ∈ twinSet Ω[R] K, J ≤ TwinSecXg.twinJoin Ω[R] K := fun J hJ =>
    TwinSecXg.le_twinJoin hJ
  set P := TwinSecXg.twinJoin Ω[R] K with hP
  have ha₁ : a₁ ∈ P := hle K hKt fr.h₁.1
  have ha₂ : a₂ ∈ P := hle K' hd.hK' fr.h₂.1
  have ha₃ : a₃ ∈ P := hle K₃ hd.hK₃ fr.h₃.1
  have ha₄ : a₄ ∈ P := hle K₄ hF.1 fr.h₄.1
  have htP : t ∈ P := hle K hKt hd.hz.mem
  have hτP : a₁ * a₂ * a₃ * a₄ ∈ P := P.mul_mem (P.mul_mem (P.mul_mem ha₁ ha₂) ha₃) ha₄
  refine conjSub_ae6I_eq H fun m hm => ?_
  obtain ⟨x, hx, hmx⟩ := horb m hm
  have hxP : x ∈ P := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact htP
    · exact hτP
    · exact P.mul_mem hτP htP
  have hmu : m * (u₁ * u₂) * m⁻¹ ∈ P := by
    rw [← fr.hu, hmx]
    exact P.mul_mem (P.mul_mem ha₁ ha₂) hxP
  exact hcP _ hmu

end Orbit

section Odd

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
include H

theorem oddCoreOf_ae6I_eq_bot
    (hDsq : ∀ d ∈ ae6D Ω[R] W (u₁ * u₂), d * d = 1)
    (hYuN : rLayer Ω[R] (u₁ * u₂) ≤ Subgroup.normalizer (ae6D Ω[R] W (u₁ * u₂) : Set Y))
    (hEu : u₁ * u₂ ∈ ae6E Ω[R] (u₁ * u₂)) (hEt : t ∈ ae6E Ω[R] (u₁ * u₂))
    (hIc : ∀ c : Y, c ∈ Subgroup.centralizer ({t} : Set Y) →
      (∀ p ∈ TwinSecXg.twinJoin Ω[R] K, c * p = p * c) →
        conjSub c (ae6I Ω[R] W (u₁ * u₂)) = ae6I Ω[R] W (u₁ * u₂)) :
    oddCoreOf (ae6I Ω[R] W (u₁ * u₂)) = ⊥ := by
  classical
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hΩ := hypOf H
  have h2g := h2Of H
  have hq8 := h8Of H
  have hV := TwinPerpV3.twinSet_four hStd hF
  set Ω : Set (Subgroup Y) := Ω[R] with hΩdef
  set u : Y := u₁ * u₂ with hu
  set I : Subgroup Y := ae6I Ω W u with hIdef
  set D : Subgroup Y := ae6D Ω W u with hDdef
  set Ct : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCtdef
  set N : Subgroup Y := oddCoreOf I with hN
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn I
  have hNI : N ≤ I := oddCoreOf_le_self I
  have hNnormI : ∀ y ∈ I, ∀ x ∈ N, y * x * y⁻¹ ∈ N := fun y hy x hx =>
    Balance.conj_mem_oddCoreIn hy hx
  have hD2 : IsPGroup 2 ↥D := isPGroup_two_of_sq_eq_one hDsq
  have hIN : I ≤ Subgroup.normalizer (D : Set Y) := ae6I_le_normalizer_ae6D Ω W u hYuN
  have hDI : ∀ x ∈ I, ∀ d ∈ D, x * d * x⁻¹ ∈ D := fun x hx d hd' =>
    (Subgroup.mem_normalizer_iff.mp (hIN hx) d).mp hd'
  have hDle : D ≤ I := ae6D_le_ae6I Ω W u
  have htD : t ∈ D := ae6E_le_ae6D Ω W u hEt
  have huD : u ∈ D := ae6E_le_ae6D Ω W u hEu
  have hND : ∀ x ∈ N, ∀ d ∈ D, x * d = d * x := fun x hx =>
    A6b.comm_of_odd_of_le_two hNodd hD2 le_rfl hx (hDI x (hNI hx))
      (fun j hj n hn => hNnormI j (hDle hj) n hn)
  have hxt : ∀ x ∈ N, x * t = t * x := fun x hx => hND x hx t htD
  have hxu : ∀ x ∈ N, x * u = u * x := fun x hx => hND x hx u huD
  have hxCt : ∀ x ∈ N, x ∈ Ct := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hxt x hx)
  have hxC : ∀ x ∈ N, x ∈ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxu x hx)
  obtain ⟨hK₃Y, hK₄Y⟩ := A6b.members_le_rLayer hStd hF h2g
  have hK₃I : K₃ ≤ I := hK₃Y.trans (rLayer_le_ae6I Ω W u)
  have hK₄I : K₄ ≤ I := hK₄Y.trans (rLayer_le_ae6I Ω W u)
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 Ct) :=
    RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 Ct
  have hK₃Q : K₃ ≤ pCoreOf 2 Ct :=
    RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 (hd.subn K₃ hd.hK₃)
      (h2g K₃ hd.hK₃.1)
  have hK₄Q : K₄ ≤ pCoreOf 2 Ct :=
    RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 (hd.subn K₄ hF.1)
      (h2g K₄ hF.1.1)
  have hx3 : ∀ x ∈ N, ∀ j ∈ K₃, x * j = j * x := fun x hx =>
    A6b.comm_of_odd_of_le_two hNodd hQ2 hK₃Q hx
      (fun q hq => CGT.PushingUpLit.SolK.pCoreOf_normalized Ct (hxCt x hx) hq)
      (fun j hj n hn => hNnormI j (hK₃I hj) n hn)
  have hx4 : ∀ x ∈ N, ∀ j ∈ K₄, x * j = j * x := fun x hx =>
    A6b.comm_of_odd_of_le_two hNodd hQ2 hK₄Q hx
      (fun q hq => CGT.PushingUpLit.SolK.pCoreOf_normalized Ct (hxCt x hx) hq)
      (fun j hj n hn => hNnormI j (hK₄I hj) n hn)
  have hcent : ∀ x ∈ N, ∀ J ∈ twinSet Ω K, ∀ j ∈ J, x * j = j * x := fun x hx =>
    A6b.centralizes_twins_of_odd hΩ hd hF.2.1 hF.2.2.1 hV hF.1 h2g hq8 (hxCt x hx) (hxC x hx)
      (A6b.odd_orderOf_of_mem hNodd hx) (hx3 x hx) (hx4 x hx)
  set P : Subgroup Y := TwinSecXg.twinJoin Ω K with hP
  set C₁ : Subgroup Y := Ct ⊓ Subgroup.centralizer (P : Set Y) with hC₁
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hd.hz
  have hNC₁ : N ≤ C₁ := by
    intro x hx
    refine ⟨hxCt x hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    have hPle : P ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine iSup₂_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent x hx J hJ j hj).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hp)
  have hC₁norm : ∀ g ∈ Ct, conjSub g C₁ = C₁ := by
    have hle : ∀ g ∈ Ct, conjSub g C₁ ≤ C₁ := by
      intro g hg y hy
      rw [mem_conjSub_iff] at hy
      have hgi : g⁻¹ ∈ Ct := Ct.inv_mem hg
      have hyCt : y ∈ Ct := by
        have : g * (g⁻¹ * y * g) * g⁻¹ ∈ Ct := Ct.mul_mem (Ct.mul_mem hg hy.1) hgi
        simpa [mul_assoc] using this
      refine ⟨hyCt, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro p hp
      have hp' : g⁻¹ * p * g ∈ P := by
        have := TwinSecXg.twinJoin_normalized hΩ hd.hz g⁻¹ hgi p hp
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ hp'
      calc p * y = g * ((g⁻¹ * p * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = y * p := by group
    intro g hg
    refine le_antisymm (hle g hg) ?_
    have h2 := conjSub_mono (n := g) (hle g⁻¹ (Ct.inv_mem hg))
    rwa [conjSub_conjSub_inv] at h2
  have hNnormC₁ : ∀ g ∈ C₁, conjSub g N = N := by
    intro g hg
    have hgI : conjSub g I = I := hIc g hg.1 fun p hp =>
      (Subgroup.mem_centralizer_iff.mp hg.2 p hp).symm
    rw [hN, ← AscE184Sect.oddCoreOf_conjSub, hgI]
  have hNn : C₁ ≤ Subgroup.normalizer (N : Set Y) := fun g hg =>
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (hNnormC₁ g hg)
  have hNO : N ≤ oddCoreOf C₁ := Balance.le_oddCoreIn_of_normalizes hNC₁ hNn hNodd
  have hOle : oddCoreOf C₁ ≤ oddCoreOf Ct :=
    TwinDisc.oddCoreOf_le_of_normalizes inf_le_left hC₁norm
  have hOCt : oddCoreOf Ct = ⊥ := by
    show (classicalInvolutionOddCore ↥Ct).map Ct.subtype = ⊥
    rw [H.oddC]
    exact Subgroup.map_bot _
  exact le_antisymm ((hNO.trans hOle).trans hOCt.le) bot_le

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
