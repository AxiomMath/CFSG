module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gThmD
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bMain

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

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (aeBar8 E8Pkg)
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

theorem fourTwins_of_M_le (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {X : Subgroup Y}
    (hMX : MGrp Ω[R] W ≤ X) : A6d.FourTwins (ae6ConjIn X K) t K K' K₃ K₄ := by
  have hd := H.ex.1.datum
  have hF := H.ex.2.1
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have mem : ∀ {J : Subgroup Y}, J ∈ DSet Ω[R] W → J ∈ ae6ConjIn X K := by
    intro J hJ
    obtain ⟨m, hm, rfl⟩ := A6d.exists_M_conj_of_mem_D H hJ
    exact A6d.conjSub_mem_ae6ConjIn (hMX hm)
  exact ⟨A6d.mem_ae6ConjIn_self, mem H.hK', mem H.hK₃, mem (A6d.K₄_mem_D H), hd.hz, hd.hzK', hd.hzK₃,
    hz₄, hd.hne.symm, hd.hK₃K.symm, hF.2.1.symm, hd.hK₃K'.symm, hF.2.2.1.symm, hF.2.2.2.1.symm⟩

theorem aeIdent_of_cand (hP : TL4.TightBelowRPlus 3 n) (hE3 : V3AE6E3 n) (hL : V3AE6L n)
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h) {Lj A : Subgroup Y}
    (C : Cand Ω[R] W (u₁ * u₂) K t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) Lj A) :
    ∃ B : AEIdent (ae6ConjIn (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ⊔ Lj) K) 8,
      pSpan (ae6ConjIn (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ⊔ Lj) K) =
        ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ⊔ Lj ∧ B.φ.ker = ⊥ ∧
      pCoreOf 2 (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ⊔ Lj) = A := by
  classical
  have hStd := H.ex.1
  have hd := hStd.datum
  have hΩ := A6d.hypOf H
  have h2g := A6d.h2Of H
  have h8g := A6d.h8Of H
  have hAE := A6d.aEmptyOf H
  have hinvΩ := conjInvariant_conjClass (tightCore R)
  have hodd0 := oddCoreOf_V_eq_bot hE3 hL H fr hx C
  set Ω : Set (Subgroup Y) := Ω[R] with hΩdef
  set τ : Y := y * t * y⁻¹ with hτdef
  set xe : Y := h * τ * h⁻¹ with hxedef
  set L : Subgroup Y := ae6L Ω t τ xe with hLdef
  set E₃ : Subgroup Y := Subgroup.closure ({t, τ, xe} : Set Y) with hE₃def
  set V : Subgroup Y := L ⊔ Lj with hVdef
  obtain ⟨hLnorm, -, hLspan, B, hBker⟩ := hL Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hKM : K ≤ MGrp Ω W := A6d.K_le_M H
  have hKV : K ≤ V := (hKM.trans C.M_le).trans le_sup_right
  have hQP : ae6ConjIn L K ⊆ ae6ConjIn V K := by
    rintro J ⟨g, hg, rfl⟩
    exact ⟨g, (le_sup_left : L ≤ V) hg, rfl⟩
  have hQP' : ae6ConjIn Lj K ⊆ ae6ConjIn V K := by
    rintro J ⟨g, hg, rfl⟩
    exact ⟨g, (le_sup_right : Lj ≤ V) hg, rfl⟩
  have hspan : pSpan (ae6ConjIn V K) = V := by
    refine le_antisymm (A6d.pSpan_ae6ConjIn_le hKV) (sup_le ?_ ?_)
    · have : pSpan (ae6ConjIn L K) ≤ pSpan (ae6ConjIn V K) :=
        pSpan_le fun J hJ => le_pSpan (hQP hJ)
      rw [hLspan] at this
      exact this
    · exact C.gen.trans (pSpan_le fun J hJ => le_pSpan (hQP' hJ))
  have hodd : classicalInvolutionOddCore ↥(pSpan (ae6ConjIn V K)) = ⊥ := by
    have h1 : classicalInvolutionOddCore ↥V = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp hodd0
    rw [hspan]
    exact h1
  have hPΩ : ae6ConjIn V K ⊆ Ω := A6d.ae6ConjIn_subset hinvΩ hd.mem
  have hinv : ∀ L' ∈ ae6ConjIn V K, ∀ g ∈ pSpan (ae6ConjIn V K), conjSub g L' ∈ ae6ConjIn V K :=
    fun L' hL' g hg => A6d.conjSub_mem_of_mem_ae6ConjIn (by rw [← hspan]; exact hg) hL'
  have htrans : ∀ L₁ ∈ ae6ConjIn V K, ∀ L₂ ∈ ae6ConjIn V K,
      ∃ g ∈ pSpan (ae6ConjIn V K), conjSub g L₁ = L₂ := by
    intro L₁ hL₁ L₂ hL₂
    obtain ⟨g, hg, hgL⟩ := A6d.exists_conj_of_mem_ae6ConjIn hL₁ hL₂
    exact ⟨g, by rw [hspan]; exact hg, hgL⟩
  have hAV : V ≤ Subgroup.normalizer (A : Set Y) := sup_le C.L_norm C.Lj_norm
  have hA2 : IsPGroup 2 A := IsPGroup.of_card C.elem.1
  have hAVle : A ≤ V := C.A_le_L.trans le_sup_left
  have htA : t ∈ A := C.E3_le (Subgroup.subset_closure (by simp))
  have hDinv : ∀ L' ∈ ae6ConjIn V K, ∀ u : Y, IsUniqueInvolution L' u → u ∈ A := by
    rintro L' ⟨g, hg, rfl⟩ u hu
    rw [hu.eq (hd.hz.conj g)]
    exact (Subgroup.mem_normalizer_iff.mp (hAV hg) t).mp htA
  have he2 : ∀ L' ∈ ae6ConjIn V K, ∀ u : Y, IsUniqueInvolution L' u → ∃ Q : Subgroup Y,
      Q ≤ pSpan (ae6ConjIn V K) ∧ (∀ g ∈ pSpan (ae6ConjIn V K), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧
        IsPGroup 2 Q ∧ u ∈ Q := by
    intro L' hL' u hu
    refine ⟨A, hAVle.trans hspan.symm.le, fun g hg q hq => ?_, hA2, hDinv L' hL' u hu⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAV (hspan ▸ hg)) q).mp hq
  have hxe1 : xe ≠ 1 := by
    intro e
    apply hd.hz.ne_one
    have h1 : τ = 1 := by
      have := congrArg (fun z => h⁻¹ * z * h) e
      simpa [hxedef, mul_assoc] using this
    have := congrArg (fun z => y⁻¹ * z * y) h1
    simpa [hτdef, mul_assoc] using this
  have hVtop : V ≠ ⊤ := by
    intro htop
    have hn : A.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hAV))
    haveI := hStd.perp.core.simple
    have hbot := eq_bot_of_normal_isPGroup hStd.perp.core.nonab hn hA2
    apply hxe1
    have hxA : xe ∈ A := C.E3_le (Subgroup.subset_closure (by simp))
    simpa [hbot] using hxA
  have hlt : Nat.card ↥(pSpan (ae6ConjIn V K)) < n := by
    rw [hspan, ← hStd.perp.core.card]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
      hVtop ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have hDabs : ThmDAbsAt 3 ↥(pSpan (ae6ConjIn V K)) := hP.thmD.d2 _ hlt
  have F := fourTwins_of_M_le H (X := V) (C.M_le.trans le_sup_right)
  have hnormE₃ : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃ :=
    fun l hl e he => (Subgroup.mem_normalizer_iff.mp (hLnorm hl) e).mp he
  have hL8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8 := by
    rintro J ⟨g, -, rfl⟩
    exact A6h1.ae6_card8 H _ (hinvΩ g K hd.mem)
  have htE₃ : t ∈ E₃ := Subgroup.subset_closure (by simp)
  have hthin : ∀ L' ∈ ae6ConjIn V K, ∀ u : Y, IsUniqueInvolution L' u → ∀ Q : Subgroup Y,
      Q ≤ pSpan (ae6ConjIn V K) → (∀ g ∈ pSpan (ae6ConjIn V K), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) →
        IsPGroup 2 Q → ∀ z ∈ L', z ∈ Q → z = 1 ∨ z = u := by
    rintro L' ⟨g, hg, rfl⟩ u hu Q hQle hQn hQ2 z hz hzQ
    have hgV : g ∈ pSpan (ae6ConjIn V K) := by rw [hspan]; exact hg
    have hz₀ : g⁻¹ * z * g ∈ K := mem_conjSub_iff.mp hz
    have hzQ₀ : g⁻¹ * z * g ∈ Q := by
      have := hQn g⁻¹ ((pSpan (ae6ConjIn V K)).inv_mem hgV) z hzQ
      simpa using this
    have hQV : ∀ g' ∈ V, ∀ q ∈ Q, g' * q * g'⁻¹ ∈ Q := fun g' hg' q hq =>
      hQn g' (by rw [hspan]; exact hg') q hq
    have hu' : u = g * t * g⁻¹ := hu.eq (hd.hz.conj g)
    rcases thin_of_lside (B := B) (hspan := hLspan) (le_sup_left : L ≤ V) hBker hd.hz hL8 hQV hQ2
      hz₀ hzQ₀ with h1 | h1
    · left
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, h1]
      group
    · right
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [hu', this, h1]
  have hno64 : IsEmpty (AEIdentOn (ae6ConjIn V K) 7 e64Sets e64Sub) :=
    ⟨fun I => false_of_four_twins_on (by norm_num) (by norm_num) hΩ h2g h8g hPΩ I
      (I.toLabel.isPGroup_ker hodd) F⟩
  have hno29 : IsEmpty (AEIdentOn (ae6ConjIn V K) 8 e29Sets e29Sub) :=
    ⟨fun I₀ => no_e29_of_far hΩ h2g hPΩ I₀ (I₀.toLabel.isPGroup_ker hodd) B hd.hz hnormE₃ htE₃
      C.far⟩
  obtain ⟨I₀⟩ := aeIdent8_of_thmD' hΩ h2g h8g hAE hPΩ htrans hinv hodd he2 hDabs F hthin hno64 hno29
  have hk : IsPGroup 2 I₀.φ.ker := I₀.isPGroup_ker hodd
  obtain ⟨hH, hker⟩ := A6d.ker_eq_bot_of_twins hΩ h2g h8g hPΩ hinv htrans I₀ hk F
  refine ⟨I₀, hspan, hker, le_antisymm ?_ ?_⟩
  · have := A6d.pCoreOf_le_of_involutions I₀ hH hDinv
    rwa [hspan] at this
  · exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 A V hAVle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAVle).mpr hAV) hA2

theorem v3AE6I23_of {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hC : V3AE6EComm n) (hDN : V3AE6DNorm n)
    (hI : V3AE6I n) (hE3 : V3AE6E3 n) (hL : V3AE6L n) (hPar : A6h1.AE6ModelPar) : V3AE6I23 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hD : V3AE6D n := v3AE6D_of A6b.v3AE6E_proved hC
  obtain ⟨A, hspan, hker, hcore, hxI, ht, hτ, hperm⟩ := exists_std hD hDN hI H fr hx
  let SD : SData (ae6I Ω[R] W (u₁ * u₂)) (ae6D Ω[R] W (u₁ * u₂))
      (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) :=
    ⟨A, hspan, hker, hcore, hxI, ht, hτ, hperm⟩
  have hxx : (h * (y * t * y⁻¹) * h⁻¹) * (h * (y * t * y⁻¹) * h⁻¹) = 1 := by
    have h1 : t * t = 1 := H.ex.1.datum.hz.sq
    calc (h * (y * t * y⁻¹) * h⁻¹) * (h * (y * t * y⁻¹) * h⁻¹)
        = h * y * (t * t) * y⁻¹ * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hy₀ : SD.pkg.ph (h * (y * t * y⁻¹) * h⁻¹) ∈ aeBar8 := SD.pkg.ph_mem hxI
  have hp₀ : permQ 8 (SD.pkg.ph (h * (y * t * y⁻¹) * h⁻¹)) = σ₀ := hperm
  have hsq₀ : SD.pkg.ph (h * (y * t * y⁻¹) * h⁻¹) * SD.pkg.ph (h * (y * t * y⁻¹) * h⁻¹) = 1 := by
    rw [← SD.pkg.ph_mul hxI hxI, hxx, SD.pkg.ph_one]
  obtain ⟨E₂, hG₂⟩ := goodPair_X2 hy₀ hp₀ hsq₀
  obtain ⟨E₃', hG₃⟩ := goodPair_X3 hy₀ hp₀ hsq₀
  have C₂ := cand_of_goodPair hD hE3 hL hPar H fr hx SD hG₂
  have C₃ := cand_of_goodPair hD hE3 hL hPar H fr hx SD hG₃
  obtain ⟨B₃, hB₃span, hB₃ker, hB₃core⟩ := aeIdent_of_cand hP hE3 hL H fr hx C₃
  obtain ⟨B₂, hB₂span, hB₂ker, hB₂core⟩ := aeIdent_of_cand hP hE3 hL H fr hx C₂
  have hxA₂ : h * (y * t * y⁻¹) * h⁻¹ ∈ preim SD.pkg E₃' :=
    C₃.E3_le (Subgroup.subset_closure (by simp))
  have hxA₃ : h * (y * t * y⁻¹) * h⁻¹ ∈ preim SD.pkg E₂ :=
    C₂.E3_le (Subgroup.subset_closure (by simp))
  refine ⟨preim SD.pkg e29Sub, preim SD.pkg X3, preim SD.pkg E₃', preim SD.pkg E₂,
    C₂.M_le, C₃.M_le, C₂.le_I, C₃.le_I, fun heq => e29Sub_ne_X3 (preim_inj SD.pkg hG₂.X_le hG₃.X_le heq),
    hxA₂, hxA₃, C₃.elem, C₂.elem, ?_, ?_, C₃.L_norm, C₂.L_norm, C₃.Lj_norm, C₂.Lj_norm,
    ⟨B₃, hB₃span, hB₃ker, hB₃core⟩, ⟨B₂, hB₂span, hB₂ker, hB₂core⟩⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ C₃.A_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer C₃.A_le).mpr C₃.Lj_norm)
      (IsPGroup.of_card C₃.elem.1)
  · exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ C₂.A_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer C₂.A_le).mpr C₂.Lj_norm)
      (IsPGroup.of_card C₂.elem.1)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
