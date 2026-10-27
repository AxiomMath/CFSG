module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightFixFree
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}

theorem inf_centSec_eq_bot_of_iota {n : ℕ} (hn : 5 ≤ n) (ι : ↥L ≃* alternatingGroup (Fin n))
    {Y₀ Y₁ : Subgroup V} (hL₀ : L ≤ stabSub Y₀) (hL₁ : L ≤ stabSub Y₁)
    (hnc : ¬ IsCentralSec L Y₀ Y₁) : L ⊓ centSec Y₁ Y₀ = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have : IsSimpleGroup ↥L := ι.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (B5.secHom L hL₁ hL₀).ker with h | h
  · rw [eq_bot_iff]
    rintro g ⟨hgL, hgc⟩
    have hk : (⟨g, hgL⟩ : ↥L) ∈ (B5.secHom L hL₁ hL₀).ker := (B5.mem_ker_secHom L hL₁ hL₀ _).2 hgc
    rw [h, Subgroup.mem_bot] at hk
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hk)
  · exfalso
    refine hnc fun l hl y hy => ?_
    have hk : (⟨l, hl⟩ : ↥L) ∈ (B5.secHom L hL₁ hL₀).ker := h ▸ Subgroup.mem_top _
    exact ((B5.mem_ker_secHom L hL₁ hL₀ _).1 hk).2 y hy

theorem autSec_zpowers_eq_zpowers_secHom {Y₀ Y₁ : Subgroup V} (hL₀ : L ≤ stabSub Y₀)
    (hL₁ : L ≤ stabSub Y₁) {x : MulAut V} (hx : x ∈ L) :
    autSec (Subgroup.zpowers x) Y₁ Y₀ = Subgroup.zpowers (B5.secHom L hL₁ hL₀ ⟨x, hx⟩) := by
  rw [← B5.map_secHom_eq_autSec L hL₁ hL₀ (Subgroup.zpowers_le.2 hx)]
  have h1 : (Subgroup.zpowers x).subgroupOf L = Subgroup.zpowers ⟨x, hx⟩ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 hx), MonoidHom.map_zpowers]
    rfl
  rw [h1, MonoidHom.map_zpowers]

theorem fixV_autSec_zpowers_eq_bot_of_card_sec_eq_sixteen (ι : ↥L ≃* alternatingGroup (Fin 8))
    {Y₀ Y₁ : Subgroup V} (hL₀ : L ≤ stabSub Y₀) (hL₁ : L ≤ stabSub Y₁)
    (hnc : ¬ IsCentralSec L Y₀ Y₁) (h16 : Nat.card (Sec Y₁ Y₀) = 16) {x : MulAut V} (hx : x ∈ L)
    (h3 : (ι ⟨x, hx⟩ : Perm (Fin 8)).IsThreeCycle) :
    fixV (autSec (Subgroup.zpowers x) Y₁ Y₀) = ⊥ := by
  have : Finite (Sec Y₁ Y₀) := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
  have hfaith := inf_centSec_eq_bot_of_iota (by norm_num) ι hL₀ hL₁ hnc
  have hxb : B5.secHom L hL₁ hL₀ ⟨x, hx⟩ ∈ autSec L Y₁ Y₀ :=
    (B5.secEquiv L hL₁ hL₀ hfaith ⟨x, hx⟩).2
  have he : (⟨_, hxb⟩ : ↥(autSec L Y₁ Y₀)) = B5.secEquiv L hL₁ hL₀ hfaith ⟨x, hx⟩ := rfl
  have h3' : (((B5.secEquiv L hL₁ hL₀ hfaith).symm.trans ι ⟨_, hxb⟩ : alternatingGroup (Fin 8)) :
      Perm (Fin 8)).IsThreeCycle := by
    rw [MulEquiv.trans_apply, he, MulEquiv.symm_apply_apply]
    exact h3
  rw [autSec_zpowers_eq_zpowers_secHom hL₀ hL₁ hx]
  exact fixV_zpowers_eq_bot_of_card_eq_sixteen h16 _ hxb h3'

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
