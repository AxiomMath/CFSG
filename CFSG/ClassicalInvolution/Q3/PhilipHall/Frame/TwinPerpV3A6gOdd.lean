module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gCand
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gOddAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cOrbit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

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

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (ae6E_le_ae6D)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1 (ae6_card8 le_ae6L)
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

theorem oddCoreOf_V_eq_bot (hE3 : V3AE6E3 n) (hL : V3AE6L n)
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h) {Lj A : Subgroup Y}
    (C : Cand Ω[R] W (u₁ * u₂) K t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) Lj A) :
    oddCoreOf (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ⊔ Lj) = ⊥ := by
  classical
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hΩ := A6d.hypOf H
  have h2g := A6d.h2Of H
  have hinvΩ := conjInvariant_conjClass (tightCore R)
  set Ω : Set (Subgroup Y) := Ω[R] with hΩdef
  set τ : Y := y * t * y⁻¹ with hτdef
  set xe : Y := h * τ * h⁻¹ with hxedef
  set L : Subgroup Y := ae6L Ω t τ xe with hLdef
  set I : Subgroup Y := ae6I Ω W (u₁ * u₂) with hIdef
  set E₃ : Subgroup Y := Subgroup.closure ({t, τ, xe} : Set Y) with hE₃def
  set V : Subgroup Y := L ⊔ Lj with hVdef
  set Ct : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCtdef
  set N : Subgroup Y := oddCoreOf V with hN
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn V
  have hNV : N ≤ V := oddCoreOf_le_self V
  have hNnorm : ∀ z ∈ V, ∀ w ∈ N, z * w * z⁻¹ ∈ N := fun z hz w hw => Balance.conj_mem_oddCoreIn hz hw
  have hAV : V ≤ Subgroup.normalizer (A : Set Y) := sup_le C.L_norm C.Lj_norm
  have hA2 : IsPGroup 2 A := IsPGroup.of_card C.elem.1
  have hAL : A ≤ L := C.A_le_L
  have hNA : ∀ w ∈ N, ∀ a ∈ A, w * a = a * w := fun w hw =>
    A6b.comm_of_odd_of_le_two hNodd hA2 le_rfl hw
      (fun q hq => (Subgroup.mem_normalizer_iff.mp (hAV (hNV hw)) q).mp hq)
      (fun j hj m hm => hNnorm j ((le_sup_left : L ≤ V) (hAL hj)) m hm)
  have htE₃ : t ∈ E₃ := Subgroup.subset_closure (by simp)
  have hτE₃ : τ ∈ E₃ := Subgroup.subset_closure (by simp)
  have hxE₃ : xe ∈ E₃ := Subgroup.subset_closure (by simp)
  have hE₃A : E₃ ≤ A := C.E3_le
  have hNt : ∀ w ∈ N, w * t = t * w := fun w hw => hNA w hw t (hE₃A htE₃)
  have hNCt : ∀ w ∈ N, w ∈ Ct := fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hNt w hw)
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 Ct) := RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 Ct
  have hcent : ∀ w ∈ N, ∀ J ∈ twinSet Ω K, ∀ j ∈ J, w * j = j * w := by
    intro w hw J hJ j hj
    have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hd.hz hJ
    have hJL : J ≤ L := le_ae6L (Or.inl (Or.inl ⟨hJ.1, hzJ⟩))
    have hJQ : J ≤ pCoreOf 2 Ct :=
      RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 (hd.subn J hJ)
        (h2g J hJ.1)
    exact A6b.comm_of_odd_of_le_two hNodd hQ2 hJQ hw
      (fun q hq => CGT.PushingUpLit.SolK.pCoreOf_normalized Ct (hNCt w hw) hq)
      (fun j' hj' m hm => hNnorm j' ((le_sup_left : L ≤ V) (hJL hj')) m hm) j hj
  set P : Subgroup Y := TwinSecXg.twinJoin Ω K with hP
  set C₁ : Subgroup Y := Ct ⊓ Subgroup.centralizer (P : Set Y) with hC₁
  have hNC₁ : N ≤ C₁ := by
    intro w hw
    refine ⟨hNCt w hw, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    have hPle : P ≤ Subgroup.centralizer ({w} : Set Y) := by
      refine iSup₂_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent w hw J hJ j hj).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hp)
  have hC₁norm : ∀ g ∈ Ct, conjSub g C₁ = C₁ := by
    have hle : ∀ g ∈ Ct, conjSub g C₁ ≤ C₁ := by
      intro g hg z hz
      rw [mem_conjSub_iff] at hz
      have hgi : g⁻¹ ∈ Ct := Ct.inv_mem hg
      have hzCt : z ∈ Ct := by
        have : g * (g⁻¹ * z * g) * g⁻¹ ∈ Ct := Ct.mul_mem (Ct.mul_mem hg hz.1) hgi
        simpa [mul_assoc] using this
      refine ⟨hzCt, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro p hp
      have hp' : g⁻¹ * p * g ∈ P := by
        have := TwinSecXg.twinJoin_normalized hΩ hd.hz g⁻¹ hgi p hp
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hp'
      calc p * z = g * ((g⁻¹ * p * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = z * p := by group
    intro g hg
    refine le_antisymm (hle g hg) ?_
    have h2 := conjSub_mono (n := g) (hle g⁻¹ (Ct.inv_mem hg))
    rwa [conjSub_conjSub_inv] at h2
  obtain ⟨hE3el, hE3P, -⟩ := hE3 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hE₃P : E₃ ≤ P := by
    refine hE3P.trans ?_
    refine iSup₂_le fun J hJ => ?_
    exact TwinSecXg.le_twinJoin ⟨hJ.1, t, hd.hz, hJ.2⟩
  have hC₁cE : ∀ g ∈ C₁, ∀ e ∈ E₃, g * e * g⁻¹ = e := by
    intro g hg e he
    have := Subgroup.mem_centralizer_iff.mp hg.2 e (hE₃P he)
    rw [← this]
    group
  have hC₁L : ∀ g ∈ C₁, conjSub g L = L := fun g hg =>
    conjSub_ae6L_eq hinvΩ (hC₁cE g hg t htE₃) (hC₁cE g hg τ hτE₃) (hC₁cE g hg xe hxE₃)
  have horb := A6c.orbit_mem H fr
  have hC₁I : ∀ g ∈ C₁, conjSub g I = I := fun g hg =>
    A6d.conjSub_ae6I_of_orbit H horb fr (fun p hp => (Subgroup.mem_centralizer_iff.mp hg.2 p hp).symm)
  obtain ⟨hLnorm, -, hLspan, B, hBker⟩ := hL Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hnormE₃ : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃ :=
    fun l hl e he => (Subgroup.mem_normalizer_iff.mp (hLnorm hl) e).mp he
  have h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8 := by
    rintro J ⟨g, -, rfl⟩
    exact ae6_card8 H _ (hinvΩ g K hd.mem)
  set 𝒪 : Set (Subgroup Y) := {Q | Q ≤ L ∧ IsElemAbelian2 Q 6 ∧ E₃ ≤ Q} with h𝒪
  have h𝒪3 : 𝒪.ncard ≤ 3 := lside_ncard_le_three (B := B) (hspan := hLspan) hBker h8 hd.hz hnormE₃ htE₃
  have hmaps : ∀ g ∈ C₁, ∀ Q ∈ 𝒪, conjSub g Q ∈ 𝒪 := by
    rintro g hg Q ⟨hQL, hQ, hEQ⟩
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · exact (conjSub_mono hQL).trans (hC₁L g hg).le
    · rw [A6h1.natCard_conjSub, hQ.1]
    · intro z hz
      have hz' : g⁻¹ * z * g ∈ Q := mem_conjSub_iff.mp hz
      have := hQ.2 _ hz'
      calc z * z = g * ((g⁻¹ * z * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    · intro e he
      rw [mem_conjSub_iff]
      have h1 := hC₁cE g hg e he
      have h2 : g * e = e * g := by
        calc g * e = (g * e * g⁻¹) * g := by group
          _ = e * g := by rw [h1]
      have h3 : g⁻¹ * e * g = e := by
        calc g⁻¹ * e * g = g⁻¹ * (e * g) := by group
          _ = g⁻¹ * (g * e) := by rw [h2]
          _ = e := by group
      rw [h3]
      exact hEQ he
  have hA𝒪 : A ∈ 𝒪 := ⟨hAL, C.elem, hE₃A⟩
  have hNfixA : ∀ w ∈ N, conjSub w A = A := by
    intro w hw
    have hcomm' : ∀ a ∈ A, w * a * w⁻¹ = a := fun a ha => by
      have h1 := hNA w hw a ha
      calc w * a * w⁻¹ = (a * w) * w⁻¹ := by rw [h1]
        _ = a := by group
    ext z
    rw [mem_conjSub_iff]
    constructor
    · intro hz
      have e : z = w * (w⁻¹ * z * w) * w⁻¹ := by group
      rw [e, hcomm' _ hz]
      exact hz
    · intro hz
      have e : w⁻¹ * z * w = z := by
        have := hcomm' z hz
        calc w⁻¹ * z * w = w⁻¹ * (w * z * w⁻¹) * w := by rw [this]
          _ = z := by group
      rw [e]
      exact hz
  have hfixN : ∀ w ∈ N, ∀ Q ∈ 𝒪, conjSub w Q = Q := fun w hw =>
    odd_fixes_all h𝒪3 (A6b.odd_orderOf_of_mem hNodd hw) (hmaps w (hNC₁ hw)) hA𝒪 (hNfixA w hw)
  set K'' : Subgroup Y := fixSub C₁ 𝒪 with hK''
  have hNK' : N ≤ K'' := fun w hw => mem_fixSub.mpr ⟨hNC₁ hw, hfixN w hw⟩
  have hK'C₁ : K'' ≤ C₁ := fixSub_le C₁ 𝒪
  have hK'norm : ∀ g ∈ C₁, conjSub g K'' = K'' := fun g hg => conjSub_fixSub hmaps hg
  have hcLj : ∀ c ∈ K'', conjSub c Lj ≤ Lj := by
    intro c hc z hz
    obtain ⟨hcC₁, hcQ⟩ := mem_fixSub.mp hc
    have hcA : conjSub c A = A := hcQ A hA𝒪
    have hA1 : ∀ b, c⁻¹ * b * c ∈ A ↔ b ∈ A := fun b => by rw [← mem_conjSub_iff, hcA]
    have hA2 : ∀ b, c * b * c⁻¹ ∈ A ↔ b ∈ A := fun b =>
      (hA1 (c * b * c⁻¹)).symm.trans (by rw [show c⁻¹ * (c * b * c⁻¹) * c = b by group])
    have hz' : c⁻¹ * z * c ∈ Lj := mem_conjSub_iff.mp hz
    have hz'I : c⁻¹ * z * c ∈ I := C.le_I hz'
    have hzI : z ∈ I := by
      have : z ∈ conjSub c I := mem_conjSub_iff.mpr hz'I
      rwa [hC₁I c hcC₁] at this
    have hz'n := Subgroup.mem_normalizer_iff.mp (C.Lj_norm hz')
    refine C.Lj_eq z hzI (Subgroup.mem_normalizer_iff.mpr fun a => ?_)
    have e : z * a * z⁻¹ = c * ((c⁻¹ * z * c) * (c⁻¹ * a * c) * (c⁻¹ * z * c)⁻¹) * c⁻¹ := by group
    rw [e, hA2]
    exact ((hA1 a).symm.trans (hz'n _)).symm.symm
  have hK'V : ∀ c ∈ K'', conjSub c V = V := by
    have hle : ∀ c ∈ K'', conjSub c V ≤ V := by
      intro c hc
      have hsup : conjSub c V = conjSub c L ⊔ conjSub c Lj := Subgroup.map_sup _ _ _
      rw [hsup, hC₁L c (hK'C₁ hc)]
      exact sup_le_sup_left (hcLj c hc) _
    intro c hc
    refine le_antisymm (hle c hc) ?_
    have h2 := conjSub_mono (n := c) (hle c⁻¹ (K''.inv_mem hc))
    rwa [conjSub_conjSub_inv] at h2
  have hNn : K'' ≤ Subgroup.normalizer (N : Set Y) := fun c hc =>
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (by rw [hN, ← AscE184Sect.oddCoreOf_conjSub, hK'V c hc])
  have hNO : N ≤ oddCoreOf K'' := Balance.le_oddCoreIn_of_normalizes hNK' hNn hNodd
  have hO1 : oddCoreOf K'' ≤ oddCoreOf C₁ := TwinDisc.oddCoreOf_le_of_normalizes hK'C₁ hK'norm
  have hO2 : oddCoreOf C₁ ≤ oddCoreOf Ct := TwinDisc.oddCoreOf_le_of_normalizes inf_le_left hC₁norm
  have hOCt : oddCoreOf Ct = ⊥ := by
    show (classicalInvolutionOddCore ↥Ct).map Ct.subtype = ⊥
    rw [H.oddC]
    exact Subgroup.map_bot _
  exact le_antisymm (hNO.trans (hO1.trans (hO2.trans hOCt.le))) bot_le

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
