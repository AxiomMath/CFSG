module

public import CFSG.GH74.Generic.BProg.B3.S3T3E8A
public import CFSG.GH74.Generic.BProg.B3.S3T3E8B
public import CFSG.GH74.Generic.BProg.B3.S3Sec29Tail
public import CFSG.GH74.Generic.BProg.B3.S3Sec29I2
public import CFSG.GH74.Generic.BProg.B3.S3Sec29A3
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B3.S3Boot293
public import CFSG.GH74.Generic.BProg.B3.S3BootObs52
public import CFSG.GH74.Generic.BProg.B3.S3Sec29A1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.ComponentClassification
open scoped commutatorElement

namespace S3T3

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_inf_of_comp {y u : G} {J Λ : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hΛ : IsPCompIn 2 (J ⊓ centralizer ({u} : Set G)) Λ) :
    IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({u} : Set G)) Λ := by
  set W := centralizer ({y} : Set G) ⊓ centralizer ({u} : Set G) with hW
  have hXW : J ⊓ centralizer ({u} : Set G) ≤ W := inf_le_inf_right _ hJ.1
  refine isPCompIn_two_iff.mpr ⟨hΛ.1.trans hXW, ?_⟩
  have hJsub : (J.subgroupOf (centralizer ({y} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hJ).2.1
      Subgroup.IsSubnormal.top
  have hsub : ((J ⊓ centralizer ({u} : Set G)).subgroupOf W).IsSubnormal := by
    have h1 := TwoThin.isSubnormal_inf_subgroupOf hJsub (inf_le_left : W ≤ _)
    have h2 : (J ⊓ centralizer ({u} : Set G)).subgroupOf W = J.subgroupOf W := by
      ext a
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp a.2).2⟩⟩
    rwa [h2]
  exact TwoComponentTransport.extend_nested Λ _ W hΛ.1 hXW hsub (isPCompIn_two_iff.mp hΛ).2

omit [Finite G] in
theorem perfect_pLayerOf (H : Subgroup G) :
    ⁅pLayerOf 2 H, pLayerOf 2 H⁆ = pLayerOf 2 H := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sSup_le fun L hL => ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  calc L = ⁅L, L⁆ := (TwoThin.commutator_self_of_isTwoComponent hL.1
        (isPCompIn_two_iff.mp hL).2).symm
    _ ≤ ⁅pLayerOf 2 H, pLayerOf 2 H⁆ := Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)

omit [Finite G] in
theorem comm_bar_pLayerOf {u : G} {H M : Subgroup G} (hHu : H ≤ centralizer ({u} : Set G))
    (h : ∀ L, IsPCompIn 2 H L → ⁅PumpCalc.bar u L, PumpCalc.bar u M⁆ = ⊥) :
    ⁅PumpCalc.bar u (pLayerOf 2 H), PumpCalc.bar u M⁆ = ⊥ := by
  set Z : Subgroup ↥(centralizer ({u} : Set G)) :=
    (Subgroup.centralizer ((PumpCalc.bar u M : Subgroup _) : Set _)).comap
      (barMk ↥(centralizer ({u} : Set G))) with hZ
  have hle : pLayerOf 2 H ≤ Z.map (centralizer ({u} : Set G)).subtype := by
    refine sSup_le fun L hL => fun l hl => ?_
    have hlu : l ∈ centralizer ({u} : Set G) := hHu (hL.1 hl)
    refine ⟨⟨l, hlu⟩, ?_, rfl⟩
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h L hL)
    exact hc ⟨⟨l, hlu⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨g', hg', hgg'⟩ := hle (Subgroup.mem_subgroupOf.1 hg)
  have : g' = g := Subtype.ext hgg'
  rw [← this]
  exact hg'

theorem qShape3_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3 A) :
    QShape3 B := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  refine ⟨p, f, hp, hp2, hq, ?_⟩
  rcases h with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)

end S3T3

theorem finalE8_proved (G : Type) [Group G] [Finite G] : FinalE8 G := by
  intro x a y u K A D J₀ B Q J hc hB hJ hJA7 hBN hu hu2 hJu
  obtain ⟨huB, huK⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hAB, hxB, -, hBel, -, -, -⟩ := hB.ext
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 hB.y_mem
  have hyB : y ∈ B := hAB hyA
  have hr4 : pRank 2 G = 4 := by
    have h1 := Gen4.pRank_two_le hB.hyp.gen4
    have h2 := pRank_le_top' B
    have h3 := hB.rankB
    omega
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hB.circ.1.1.1.2.2
  have hterm : IsTwoTerminal x K := hB.circ.1.2.2
  have hKcen : CenterlessBar K := fun a ha =>
    (B1.PilotS3.center_trivial_of_shape3 hKc hB.shape.qShape3) a (fun g => (ha g).symm)
  have hux : u ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hBc u huB x hxB)
  have hBu : B ≤ centralizer ({u} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hBc g hg u huB)
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    have := C3.Layer1.Back.pRank_mono' hBu
    have h3 := hB.rankB
    omega
  obtain ⟨M, hlt, -, ⟨e⟩, -, hKuN, ΛK, hΛK, hΛKM⟩ :=
    S3Sec29A1.exists_Ku hr4 hterm hKc hu2 hux huK hR hKcen
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have h3M : QShape3 (↥M ⧸ pPrimeCore 2 ↥M) :=
    S3T3.qShape3_of_equiv e.symm hB.shape.qShape3
  have hyu : y ∈ centralizer ({u} : Set G) := hBu hyB
  have hyM : y ∈ M := hΛKM (hΛK.twoElt y (Subgroup.mem_inf.2 ⟨hyK, hyu⟩)
    ⟨1, by rw [pow_one, pow_two]; exact hBsq y hyB⟩)
  have hyN : y ∈ normalizer (M : Set G) := hKuN y hyu
  set Λ := pLayerOf 2 (J ⊓ centralizer ({u} : Set G)) with hΛdef
  have hΛle : Λ ≤ J ⊓ centralizer ({u} : Set G) := TwoThin.pLayerOf_le 2 _
  have hΛJ : Λ ≤ J := hΛle.trans inf_le_left
  have hΛu : Λ ≤ centralizer ({u} : Set G) := hΛle.trans inf_le_right
  have hcomm : ⁅PumpCalc.bar u Λ, PumpCalc.bar u M⁆ = ⊥ := by
    refine S3T3.comm_bar_pLayerOf inf_le_right fun L hL => ?_
    rcases S3Sec29I2.dichotomy_of_normalizes hB.y_ord hyu (S3T3.isPCompIn_inf_of_comp hJ hL) hMc
      hyN with hle | hc
    · exfalso
      have hLJ : L ≤ J := hL.1.trans inf_le_left
      exact S3T3.not_bar_le hJA7 hLJ
        (TwoThin.commutator_self_of_isTwoComponent hL.1 (isPCompIn_two_iff.mp hL).2)
        (TwoThin.ne_bot_of_isTwoComponent (isPCompIn_two_iff.mp hL).2)
        (hL.1.trans inf_le_right) (hLJ.trans hJ.1) hMc h3M hyM hB.y_ord hle
    · exact hc
  have hΛKbar : PumpCalc.bar u ΛK ≤ PumpCalc.bar u M :=
    Subgroup.map_mono fun g hg => hΛKM hg
  have hcommK : ⁅PumpCalc.bar u ΛK, PumpCalc.bar u Λ⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl hΛKbar).trans hcomm.le)
  have hxN : x ∈ normalizer (Λ : Set G) :=
    S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer
      (TwoThin.mem_normalizer_inf (hBN hxB) (Subgroup.le_normalizer (hBu hxB)))
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  obtain ⟨S, hSx, hSgen, hSel, hS8⟩ := S3T3.exists_E8 hJA7 hΛJ (S3T3.perfect_pLayerOf _) hJu
    (hBsq u huB) hu1 (fun l hl => mem_centralizer_singleton_iff.1 (hΛu hl)) (hBsq x hxB) hxN
    (hBc u huB x hxB)
  have hgenK : zpowers u ⊔ zpowers x ⊔ (Λ ⊓ centralizer ({x} : Set G)) ≤ cSec K := by
    refine sup_le (sup_le (zpowers_le.2 huK) (zpowers_le.2
      (S3Ctx29.mem_cSec_of_le_centralizer hKc.1))) fun w hw => ?_
    obtain ⟨hwΛ, hwx⟩ := Subgroup.mem_inf.1 hw
    exact S3Sec29A3.mem_cSec_of_act_trivial hKc hΛK hwx (hΛu hwΛ)
      (S3Sec29A3.act_trivial_of_comm hcommK (hΛu hwΛ) hwΛ)
  refine ⟨S, le_inf hSx (hSgen.trans hgenK), hSel, ?_⟩
  have := hSel
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two (show Nat.card ↥S = 2 ^ 3 by rw [hS8]; norm_num)]

end CFSG.GH74.Generic.BProg.B3
