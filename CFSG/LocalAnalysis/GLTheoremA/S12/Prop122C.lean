module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122B

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem chev2_J (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) : IsChevSimple 2 (PSimple p J) := by
  by_contra hnc
  have hJ := ky_eq_J h hin
  have hBJ := nbr_norm h hin
  have hcom := hin.l121.common
  have hKx : GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G)) K := by
    have := ky_pcomp_cent h.cfg hcom h.y_mem_D h.y_not_mem
    rwa [hJ] at this
  have hx3 : x ^ p = 1 := h.cfg.elem.2 x h.cfg.xD
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hBJ h.cfg.tri.mem
  have hncx : ¬ CentMod p J x := fun hc => h.not_cent_x hc.2
  rcases hin.i1416 p (Subgroup.centralizer ({y} : Set G)) J K B x h.cfg.prime h.cfg.odd
      (kGroup_centralizer h.cfg.ctx.toS6 h.y_ne_one) h.J_comp hxJ hx3 hncx hKx (std_chev2 h.cfg hcom)
      h.cfg.tri.bmax.1 (std_inner h.cfg hcom) (h.two_le_index hcom) with hch | ⟨hp3, hcat⟩
  · exact hnc hch
  · subst hp3
    rcases catalogIs_or hcat with hA6 | hcat
    · exact not_A6 h.cfg hin.l121 hin.disj hA6
    rcases catalogIs_or hcat with hA8 | hcat
    · exact hnc (chev2_of_A8 h hin rfl hA8)
    rcases catalogIs_or hcat with hG2 | hU42
    ·
      have hyL : y ∈ Subgroup.normalizer (L : Set G) := h.cfg.tri.norm h.yB
      have hnc3 : ¬ CentMod 3 L y := fun hc => h.y_not_mem ((h.cfg.tri.cent h.cfg.ctx y h.yB).1 hc)
      have hKc : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) K :=
        std_pcomp_Ly h.cfg hcom h.y_mem_D h.y_not_mem
      have hidiag : InnDiagOn 3 B L := innDiagOn_of_inner h.cfg.tri.comp (h.cfg.tri.qs h.cfg.ctx) h.cfg.tri.idiag
      have hpow : 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) ≤ Nat.card B := by
        rw [card_B_inf_centMod_L h.cfg, h.cfg.card_B, ← pow_succ]
        exact Nat.pow_le_pow_right (by norm_num) h.cfg.four_le
      exact hin.i141 3 _ L K B y h.cfg.prime h.cfg.odd h.cfg.tri.comp (h.cfg.tri.chev2 h.cfg.ctx)
        h.cfg.tri.bmax.1 h.cfg.tri.norm hidiag hpow h.yB hnc3 hKc hG2
    ·
      rcases lemma121 h.cfg hin.l121 with ⟨hU, -, hd2, hinner, hL⟩ | ⟨hns, -⟩
      · exact hnc (chev2_of_U42 h hin rfl hd2 hL hinner hU)
      · exact hns (Or.inl hU42)

theorem sTriple_of_U42 (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) (hp3 : p = 3) (hd2 : dLevel G p = 2)
    (hL : catalogIs (PSimple p L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod p L b) (hK : U42Type p K) : IsSTriple p B y J := by
  subst hp3
  have hKcy : K ≤ Subgroup.centralizer ({y} : Set G) :=
    h.cfg.K_le_cs.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.y_mem_D))
  obtain ⟨T₀, hT₀c, hT₀2, hT₀B, hT₀ne, hT₀O⟩ := u42_T0 h.cfg.ctx h.cfg.tri.star hd2
  obtain ⟨T, hTK, hT2, hTB, hTc, hT32, hTO⟩ := hin.u42 B x L D K h.cfg.tri.star h.cfg.pow_four_le hL hinner
    h.cfg.pre hK ⟨T₀, hT₀c, hT₀2, hT₀B, hT₀ne, hT₀O⟩
  have hess : IsEssential 3 B y :=
    ⟨h.yB, h.y_ne_one, T, hTK.trans hKcy, hT2, hTB, hTc,
      fun _ => isEmpty_quaternion_of_card_gt hT32⟩
  exact ⟨h.bmax, hess, h.J_comp⟩

theorem qs_J (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) : CFSG.Open.IsQuasisimple ↥J := by
  have hchev := chev2_J h hin
  have hBJ := nbr_norm h hin
  have hcom := hin.l121.common
  have hKJ : K ≤ J := by
    rw [← ky_eq_J h hin]
    exact le_closureIn_self K _
  refine h.cfg.ctx.ctx.stage9.2 B y J h.bmax h.yB h.y_ne_one h.J_comp hBJ h.J_cent hchev ?_
  by_cases hG : IsGB p B J
  · exact Or.inr (Or.inl hG)
  by_cases hS0 : IsS0 p B y J
  · exact Or.inl hS0
  exfalso
  rcases lemma121 h.cfg hin.l121 with ⟨hU, hp3, hd2, hinner, hL⟩ | ⟨hns, hd5, E, hE, hDE, hEL, hEK⟩
  · exact u42_false h hin hp3 hd2 hL hinner hU (sTriple_of_U42 h hin hp3 hd2 hL hinner hU) hS0
  · exact hG ⟨E, hE.1, hE.2.1, hE.2.2, hE.1.trans hBJ, layer_up h.cfg hcom hE hDE hKJ hEK⟩

theorem halfSplit16At_of_marking {J : Subgroup G} {Q : GLAMarkProp J}
    (h : GLAMarking J (fun lab R _ I F θ => GLAHalfSplit16 p lab (Subgroup.center ↥J = ⊥) ∧ Q lab R I F θ)) :
    HalfSplit16At p J := by
  obtain ⟨hJ, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, ⟨hJ, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩, hP.1⟩

@[expose] def Half122 (p : ℕ) (B : Subgroup G) (x : G) (J : Subgroup G) : Prop :=
  (HalfSplit16At p J ∧ InnerDiagMarking B J) ∨
    (p = 3 ∧ (catalogIs (PSimple 3 J) isD4any ∨ IsTD4 3 J) ∧
      ∃ lab : GLALabel, LabelOf J lab ∧ (lab.tag = .D ∨ lab.tag = .triD4) ∧
        GLAHalfSplit16 p lab (Subgroup.center ↥J = ⊥)) ∨ FieldOn p x J

theorem Half122.halfSplit16At_or_field {p : ℕ} {B : Subgroup G} {x : G} {J : Subgroup G} (h : Half122 p B x J) :
    HalfSplit16At p J ∨ FieldOn p x J := by
  rcases h with ⟨h, -⟩ | ⟨-, -, lab, hlab, -, hhs⟩ | h
  · exact Or.inl h
  · exact Or.inl ⟨lab, hlab, hhs⟩
  · exact Or.inr h

theorem half_J (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) : Half122 p B x J := by
  have hq := qs_J h hin
  have hBJ := nbr_norm h hin
  have hchev := chev2_J h hin
  have hcom := hin.l121.common
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hBJ h.cfg.tri.mem
  have hJ := ky_eq_J h hin
  have hKy := kGroup_centralizer h.cfg.ctx.toS6 h.y_ne_one
  by_cases hInn : InnDiagOn p B J
  · left
    have hIM : InnerDiagMarking B J := inner_of_innDiagOn h.J_comp hq hInn
    obtain ⟨-, hmark⟩ := h.cfg.ctx.stage11 B y J h.bmax h.yB h.y_ne_one h.J_comp hBJ h.J_cent hq hIM
    exact ⟨halfSplit16At_of_marking hmark, hIM⟩
  ·
    have hb : ∃ b ∈ B, ¬ InnDiagOn p (Subgroup.zpowers b) J := by
      by_contra hcon
      push Not at hcon
      exact hInn (hin.l102.aut.innDiag_unif _ J B h.J_comp hchev hBJ hcon)
    obtain ⟨b, hbB, hbn⟩ := hb
    have hbp : b ^ p = 1 := h.cfg.tri.bmax.1.2 b hbB
    have hbN : b ∈ Subgroup.normalizer (J : Set G) := hBJ hbB
    have htri : (p = 3 ∧ (catalogIs (PSimple 3 J) isD4any ∨ IsTD4 3 J)) → Half122 p B x J := by
      rintro ⟨hp3, hD⟩
      subst hp3
      exact Or.inr (Or.inl ⟨rfl, hD, hin.trihalf _ J h.J_comp hq hchev hD⟩)
    rcases hin.i91 h.cfg.prime h.cfg.odd _ J b h.J_comp hchev hbN hbp ⟨hbN, hbn⟩ with hfb | hT
    ·
      have hxnot : ¬ InnDiagOn p (Subgroup.zpowers x) J := by
        intro hxi
        have hbx : b ∉ Subgroup.zpowers x := fun hbx =>
          hbn (innDiagOn_mono hxi (Subgroup.zpowers_le.2 hbx))
        have hKx : GLAPComponent p (closureIn J (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) K := by
          rw [closureIn_eq_self (Subgroup.zpowers_le.2 hxJ)]
          have := ky_pcomp_cent h.cfg hcom h.y_mem_D h.y_not_mem
          rwa [hJ] at this
        have hnc : ¬ CentMod p J x := fun hc => h.not_cent_x hc.2
        rcases hin.l102.i155 h.cfg.prime h.cfg.odd _ J x b hKy h.J_comp hchev
            (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.cfg.elem h.cfg.xD h.y_mem_D))
            (h.cfg.elem.2 x h.cfg.xD) hbp
            (isElemAbelian_commute h.cfg.tri.bmax.1 h.cfg.tri.mem hbB) hbx hbN (fun _ => ⟨hxi, hfb⟩) K hKx
            (B_norm_K h.cfg hbB) with ⟨hNI, -⟩ | ⟨hnot, -⟩
        · exact hNI.2 (innDiagOn_mono (std_inner h.cfg hcom) (Subgroup.zpowers_le.2 hbB))
        · exact hnot ⟨hxJ, hnc⟩
      rcases hin.i91 h.cfg.prime h.cfg.odd _ J x h.J_comp hchev hxJ (h.cfg.elem.2 x h.cfg.xD) ⟨hxJ, hxnot⟩ with
        hfx | hT'
      · exact Or.inr (Or.inr hfx)
      · exact htri hT'
    · exact htri hT

end S12

end CFSG.LocalAnalysis.GLTheoremA
