module

public import CFSG.GH74.Generic.S1.Exo.NbIvk
public import CFSG.GH74.Generic.S1.Exo.NbSingleFuse
public import CFSG.GH74.Generic.S1.Exo.NbSmall
public import CFSG.GH74.Generic.S1.Exo.NbFusionLU
public import CFSG.GH74.Generic.S1.Exo.NbFusionSp
public import CFSG.GH74.Generic.S1.Exo.NbCenterClasses

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Blueprint Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

namespace NbhdHyp

variable {H : Type} [Group H] [Finite H] {q : ℕ} {w y : H} {J₂ J₄ : Subgroup H}

theorem noCommon
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) (h : NbhdHyp H q w y J₂ J₄) :
    NoCommonComponent J₂ J₄ := by
  intro K hK ⟨h2, h4⟩
  have hq : IsQuasisimple ↥K := hK.1
  have hZ : IsPGroup 2 ↥(center ↥K) := nb_isPGroup_center_component h.core hK
  have hgen : Gen4 ↥K := Gen4.subgroup K h.gen4
  have hgh : GHList (↥K ⧸ center ↥K) := h.gh K (center ↥K) hq.2.1 hq.2.2
  let w' : ↥K := ⟨w, h2 h.w_mem⟩
  let y' : ↥K := ⟨y, h4 h.y_mem⟩
  have hw'c : w' ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h.w_central (g : H))
  have hww : w' * w' = 1 := Subtype.ext h.w_sq
  have hyy : y' * y' = 1 := Subtype.ext h.y_sq
  have hw1 : w' ≠ 1 := fun e => h.w_ne_one (congrArg Subtype.val e)
  have hy1 : y' ≠ 1 := fun e => h.y_ne_one (congrArg Subtype.val e)
  have hwy : w' ≠ y' := fun e => h.w_ne_y (congrArg Subtype.val e)
  have hne : center ↥K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hw'c
    exact hw1 hw'c
  let J₂' : Subgroup ↥K := J₂.subgroupOf K
  let J₄' : Subgroup ↥K := J₄.subgroupOf K
  have hsl₂ : HasSL2Model ↥J₂' (fun r => r = q) := by
    obtain ⟨F, _, _, hF', ⟨e⟩⟩ := h.sl₂
    exact ⟨F, inferInstance, inferInstance, hF', ⟨(Subgroup.subgroupOfEquivOfLe h2).trans e⟩⟩
  have hsl₄ : HasSL2Model ↥J₄' (fun r => r = q) := by
    obtain ⟨F, _, _, hF', ⟨e⟩⟩ := h.sl₄
    exact ⟨F, inferInstance, inferInstance, hF', ⟨(Subgroup.subgroupOfEquivOfLe h4).trans e⟩⟩
  have hcomm : ∀ a ∈ J₂', ∀ b ∈ J₄', a * b = b * a := fun a ha b hb =>
    Subtype.ext (h.comm (a : H) ha (b : H) hb)
  have hinf : J₂' ⊓ J₄' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hx2, hx4⟩ := hx
    have hx2' : (x : H) ∈ J₂ := hx2
    have hx4' : (x : H) ∈ J₄ := hx4
    have c2 := h.cent₂ (x : H) hx2' (fun b hb => (h.comm b hb (x : H) hx4').symm)
    have c4 := h.cent₄ (x : H) hx4' (fun b hb => (h.comm (x : H) hx2' b hb))
    apply Subtype.ext
    rcases c4 with e' | e'
    · exact e'
    · rcases c2 with e | e
      · exact e
      · exact absurd (e.symm.trans e') h.w_ne_y
  have hperf₄ : Group.IsPerfect ↥J₄' := by
    have := h.J₄_perf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h4).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h4).symm.surjective
  have hy'J₄ : y' ∈ J₄' := h.y_mem
  have hy'cent : ∀ b ∈ J₄', y' * b = b * y' := fun b hb => Subtype.ext (h.y_cent (b : H) hb)
  have hq5 : 5 ≤ q := h.five
  have hqodd : Odd q := h.odd
  rcases nb_center_classes hG hF hq hZ hgen hgh hne with
    hSL2 | ⟨n, hn7, hn11, hcov⟩ | ⟨hL34, -⟩ | hM12 | hSz | hS1 | ⟨F, _, _, hFodd, ⟨e⟩⟩
  · exact nb_false_of_sl2_model hSL2 hww hyy hw1 hy1 hwy
  · obtain ⟨-, hcard, ⟨eA⟩⟩ := hcov
    have hy_nc : y' ∉ center ↥K := by
      intro hyc
      have huniq := (Nat.card_eq_two_iff' (⟨1, Subgroup.one_mem _⟩ : ↥(center ↥K))).1 hcard
      obtain ⟨u, -, hu⟩ := huniq
      have e1 : (⟨y', hyc⟩ : ↥(center ↥K)) = u := hu _ (fun e => hy1 (congrArg Subtype.val e))
      have e2 : (⟨w', hw'c⟩ : ↥(center ↥K)) = u := hu _ (fun e => hw1 (congrArg Subtype.val e))
      exact hwy (congrArg Subtype.val (e2.trans e1.symm))
    exact nb_false_of_alt_cover hn11 eA hperf₄ hy'J₄ hyy hy_nc hy'cent
  · exact nb_false_of_L34_cover hZ hL34 hq5 hqodd hcomm hinf hsl₂ hsl₄
  · exact nb_false_of_M12_cover hZ hM12.2.2 hq5 hqodd hcomm hinf hsl₂ hsl₄
  · exact nb_false_of_Sz8_cover hZ hSz.2.2 hq5 hqodd hcomm hinf hsl₂ hsl₄
  · obtain ⟨g, hg⟩ := nb_fusion_sl4 hS1 hw'c hw1 hww hyy hy1 hwy.symm
    apply h.not_conj_wy (g : H)
    have := congrArg Subtype.val hg
    simpa using this
  · obtain ⟨g, hg⟩ := nb_fusion_sp hFodd e hw'c hw1 hww hyy hy1 hwy.symm
    apply h.not_conj_wy (g : H)
    have := congrArg Subtype.val hg
    simpa using this

end NbhdHyp

end CFSG.GH74.Generic.S1.Exo
