module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem IsFlipflopPt.isFlipflopSub {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : IsFlipflopSub σ p :=
  (show IsFlipflopSub σ p ∧ Module.finrank K p = 1 from hp).1

theorem IsFlipflopPt.finrank_eq_one {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : Module.finrank K p = 1 :=
  (show IsFlipflopSub σ p ∧ Module.finrank K p = 1 from hp).2

private theorem flipHerm_eq_zero_of_forall_self_eq_zero (hσ : IsUnitaryInvolution σ)
    {H : Submodule K (Fin n ⊕ Fin n → K)} (hH : ∀ w ∈ H, flipHerm σ w w = 0) :
    ∀ u ∈ H, ∀ v ∈ H, flipHerm σ u v = 0 := by
  intro u hu v hv
  have hS : ∀ s ∈ H.map (toA n K).toLinearMap, herm σ s s = 0 := by
    rintro s ⟨w, hw, rfl⟩
    change herm σ (toA n K w) (toA n K w) = 0
    rw [herm_toA]
    exact hH w hw
  have h := herm_eq_zero_of_forall_isotropic hσ hS
    (Submodule.mem_map_of_mem hu) (Submodule.mem_map_of_mem hv)
  have h' : herm σ (toA n K u) (toA n K v) = 0 := h
  rw [herm_toA] at h'
  exact (flipHerm_eq_zero_iff hσ.invol).mpr h'

theorem IsFlipflopSub.finrank_inf_flipOrth (hσ : ∀ x, σ (σ x) = x)
    {S Y : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S) (hY : Y ≤ S) :
    Module.finrank K ↥(S ⊓ flipOrth σ Y) + Module.finrank K Y = Module.finrank K S := by
  have horth : flipOrth σ Y = qPerp n K (dFlipSub σ Y) := flipOrth_eq_qPerp_dFlipSub hσ Y
  have hdisj : qPerp n K S ⊓ dFlipSub σ Y = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hwq, hwD⟩
    have hyY : dFlip σ w ∈ Y := (mem_dFlipSub hσ).mp hwD
    have hper : ∀ s ∈ S, flipHerm σ (dFlip σ w) s = 0 := by
      intro s hs
      rw [flipHerm_eq_zero_iff hσ]
      rw [flipHerm, dFlip_dFlip hσ w]
      exact (mem_qPerp.mp hwq) s hs
    have hy0 : dFlip σ w = 0 := hS.nondeg (dFlip σ w) (hY hyY) hper
    rw [← dFlip_dFlip hσ w, hy0, dFlip_zero]
  have h1 := finrank_qPerp (n := n) (K := K) S
  have h2 := finrank_qPerp (n := n) (K := K) (qPerp n K S ⊔ dFlipSub σ Y)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (qPerp n K S) (dFlipSub σ Y)
  rw [hdisj, finrank_bot, add_zero] at h3
  have h4 : Module.finrank K ↥(qPerp n K (qPerp n K S ⊔ dFlipSub σ Y)) =
      Module.finrank K ↥(S ⊓ qPerp n K (dFlipSub σ Y)) := by
    rw [qPerp_sup, qPerp_qPerp]
  rw [h4] at h2
  have h5 : Module.finrank K (dFlipSub σ Y) = Module.finrank K Y := finrank_dFlipSub hσ Y
  rw [horth]
  omega

theorem IsFlipflopSub.exists_isFlipflopPt_le (hσ : IsUnitaryInvolution σ)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) (hne : U ≠ ⊥) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ U := by
  obtain ⟨v, hvU, hvh⟩ := exists_anisotropic_of_isFlipflopSub hσ.invol hσ.exists_ne hU hne
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h]; simp)
  exact ⟨K ∙ v, (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hU.total v hvU, hvh⟩,
    (Submodule.span_singleton_le_iff_mem v U).mpr hvU⟩

theorem IsFlipflopSub.exists_isFlipflopPt_le_of_le (hσ : IsUnitaryInvolution σ)
    {S H : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S) (hH : H ≤ S)
    (hd : Module.finrank K S < 2 * Module.finrank K H) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ H := by
  have haniso : ∃ w ∈ H, flipHerm σ w w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero := flipHerm_eq_zero_of_forall_self_eq_zero hσ hcon
    have hle : H ≤ S ⊓ flipOrth σ H := by
      refine le_inf hH ?_
      intro w hw
      rw [mem_flipOrth]
      exact fun u hu => hzero u hu w hw
    have hdim := IsFlipflopSub.finrank_inf_flipOrth hσ.invol hS hH
    have hmono := Submodule.finrank_mono hle
    have hge : 2 * Module.finrank K H ≤ Module.finrank K S := by omega
    exact (not_le.mpr hd) hge
  obtain ⟨w, hwH, hwh⟩ := haniso
  have hw0 : w ≠ 0 := fun h => hwh (by rw [h]; simp)
  exact ⟨K ∙ w, (isFlipflopPt_span_singleton_iff hw0).mpr ⟨hS.total w (hH hwH), hwh⟩,
    (Submodule.span_singleton_le_iff_mem w H).mpr hwH⟩

private theorem finrank_le_three_of_forall_flipHerm_self_eq_zero (hσ : IsUnitaryInvolution σ)
    {S p p' : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S)
    (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p') (hpS : p ≤ S) (hp'S : p' ≤ S)
    (hzero : ∀ w ∈ S ⊓ flipOrth σ (p ⊔ p'), flipHerm σ w w = 0) :
    Module.finrank K S ≤ 3 := by
  classical
  set X : Submodule K (Fin n ⊕ Fin n → K) := p ⊔ p' with hX
  set W : Submodule K (Fin n ⊕ Fin n → K) := S ⊓ flipOrth σ X with hW
  have hXle : X ≤ S := by rw [hX]; exact sup_le hpS hp'S
  have hWle : W ≤ S := by rw [hW]; exact inf_le_left
  have hWX : W ≤ flipOrth σ X := by rw [hW]; exact inf_le_right
  have hzeroW : ∀ w ∈ W, flipHerm σ w w = 0 := by
    intro w hw
    exact hzero w (hW ▸ hw)
  have hrad : ∀ u ∈ W, ∀ v ∈ W, flipHerm σ u v = 0 :=
    flipHerm_eq_zero_of_forall_self_eq_zero hσ hzeroW
  have hWrad : W ≤ flipOrth σ W := by
    intro w hw
    rw [mem_flipOrth]
    exact fun u hu => hrad u hu w hw
  have hWsup : W ≤ S ⊓ flipOrth σ (W ⊔ X) := by
    refine le_inf hWle ?_
    rw [flipOrth_sup]
    exact le_inf hWrad hWX
  have hdimWsup : Module.finrank K ↥(S ⊓ flipOrth σ (W ⊔ X)) +
      Module.finrank K ↥(W ⊔ X) = Module.finrank K S :=
    IsFlipflopSub.finrank_inf_flipOrth hσ.invol hS (sup_le hWle hXle)
  have hwe : Module.finrank K W + Module.finrank K ↥(W ⊔ X) ≤ Module.finrank K S := by
    have hmono := Submodule.finrank_mono hWsup
    omega
  have hwx : Module.finrank K W + Module.finrank K X = Module.finrank K S := by
    have h := IsFlipflopSub.finrank_inf_flipOrth hσ.invol hS hXle
    rwa [← hW] at h
  have hsup : Module.finrank K ↥(W ⊔ X) + Module.finrank K ↥(W ⊓ X) =
      Module.finrank K W + Module.finrank K X :=
    Submodule.finrank_sup_add_finrank_inf_eq W X
  have hx2 : Module.finrank K X ≤ 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq p p'
    rw [hp.finrank_eq_one, hp'.finrank_eq_one] at h
    rw [hX]
    omega
  have hpX : p ≤ X := by rw [hX]; exact le_sup_left
  have hdisj : p ⊓ (X ⊓ flipOrth σ X) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvp, hvX, hvorth⟩
    refine hp.isFlipflopSub.nondeg v hvp fun t ht => ?_
    have h1 : flipHerm σ t v = 0 := (mem_flipOrth.mp hvorth) t (hpX ht)
    exact (flipHerm_eq_zero_iff hσ.invol).mp h1
  have hi1 : Module.finrank K ↥(W ⊓ X) + 1 ≤ Module.finrank K X := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq p (X ⊓ flipOrth σ X)
    rw [hdisj, finrank_bot, hp.finrank_eq_one] at h
    have hmono := Submodule.finrank_mono
      (sup_le hpX inf_le_left : p ⊔ (X ⊓ flipOrth σ X) ≤ X)
    have hinf : Module.finrank K ↥(W ⊓ X) ≤ Module.finrank K ↥(X ⊓ flipOrth σ X) :=
      Submodule.finrank_mono fun v hv => by
        obtain ⟨hvW, hvX⟩ := Submodule.mem_inf.mp hv
        exact Submodule.mem_inf.mpr ⟨hvX, hWX hvW⟩
    omega
  omega

private theorem exists_flipHerm_self_ne_zero_inf_flipOrth_sup (hσ : IsUnitaryInvolution σ)
    {S p p' : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S)
    (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p') (hpS : p ≤ S) (hp'S : p' ≤ S)
    (hd : 4 ≤ Module.finrank K S) :
    ∃ w ∈ S ⊓ flipOrth σ (p ⊔ p'), flipHerm σ w w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hthree := finrank_le_three_of_forall_flipHerm_self_eq_zero hσ hS hp hp' hpS hp'S hcon
  exact absurd hd (by omega)

theorem IsFlipflopSub.exists_flipColl_flipColl (hσ : IsUnitaryInvolution σ)
    {S : Submodule K (Fin n ⊕ Fin n → K)} (hS : IsFlipflopSub σ S) (hd : 4 ≤ Module.finrank K S)
    {p p' : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p')
    (hpS : p ≤ S) (hp'S : p' ≤ S) :
    ∃ z, IsFlipflopPt σ z ∧ z ≤ S ∧ FlipColl σ p z ∧ FlipColl σ z p' := by
  obtain ⟨w, hwW, hwh⟩ :=
    exists_flipHerm_self_ne_zero_inf_flipOrth_sup hσ hS hp hp' hpS hp'S hd
  have hwS : w ∈ S := hwW.1
  have hword : w ∈ flipOrth σ (p ⊔ p') := hwW.2
  have hw0 : w ≠ 0 := fun h => hwh (by rw [h]; simp)
  have hzpt : IsFlipflopPt σ (K ∙ w) :=
    (isFlipflopPt_span_singleton_iff hw0).mpr ⟨hS.total w hwS, hwh⟩
  have hzS : K ∙ w ≤ S := (Submodule.span_singleton_le_iff_mem w S).mpr hwS
  have hSperp : S ≤ qPerp n K S := QSing.le_qPerp (show QSing S from hS.total)
  have hpz : p ≤ qPerp n K (K ∙ w) := le_trans hpS (le_trans hSperp (qPerp_antitone hzS))
  have hzp' : K ∙ w ≤ qPerp n K p' := le_trans hzS (le_trans hSperp (qPerp_antitone hp'S))
  have hporth : p ≤ flipOrth σ (K ∙ w) := by
    intro a ha
    rw [mem_flipOrth_span_singleton]
    exact (flipHerm_eq_zero_iff hσ.invol).mp
      ((mem_flipOrth.mp hword) a (Submodule.mem_sup_left ha))
  have hzorth : K ∙ w ≤ flipOrth σ p' := by
    rw [Submodule.span_singleton_le_iff_mem, mem_flipOrth]
    exact fun b hb => (mem_flipOrth.mp hword) b (Submodule.mem_sup_right hb)
  exact ⟨K ∙ w, hzpt, hzS, flipColl_of_orth hσ.invol hp hzpt hpz hporth,
    flipColl_of_orth hσ.invol hzpt hp' hzp' hzorth⟩

end CFSG.ClassicalInvolution.PhanDn
