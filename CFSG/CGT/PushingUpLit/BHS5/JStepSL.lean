module

public import CFSG.CGT.PushingUpLit.BHS5.JSplit
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixC

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem eq_one_of_trivial_on_commV {E : Subgroup (MulAut V)} (htop : commV E ⊔ fixV E = ⊤)
    {e : MulAut V} (he : e ∈ E) (h : ∀ w ∈ commV E, e w = w) : e = 1 := by
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ commV E ⊔ fixV E := by rw [htop]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, h w hw, hc e he]
  rfl

omit [Finite V] in
theorem IsSLNatSection.eq_one_of_central {E : Subgroup (MulAut V)} {P Z : Subgroup V} {n : ℕ}
    (h : IsSLNatSection E P Z n) {x : MulAut V} (hx : x ∈ E)
    (hc : ∀ y ∈ E, y * x = x * y) : x = 1 := by
  obtain ⟨-, θ, -⟩ := h
  have hmem : θ ⟨x, hx⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := θ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2)
  rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot] at hmem
  have h1 : (⟨x, hx⟩ : ↥E) = 1 :=
    θ.injective ((Subgroup.mem_bot.1 hmem).trans (map_one θ).symm)
  exact congrArg Subtype.val h1

theorem mem_B_of_agree {E B X : Subgroup (MulAut V)} {W : Subgroup V}
    (hBE : IsSylowOf 2 B E) (hBX : B ≤ X) (hXel : IsElemAbelian2 X)
    (hXst : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W) (hfaith : ∀ e ∈ E, (∀ w ∈ W, e w = w) → e = 1)
    {x e : MulAut V} (hx : x ∈ X) (heE : e ∈ E) (hag : ∀ w ∈ W, e w = x w) : e ∈ B := by
  have hfaith' : ∀ e₁ ∈ E, ∀ e₂ ∈ E, (∀ w ∈ W, e₁ w = e₂ w) → e₁ = e₂ := by
    intro e₁ h₁ e₂ h₂ h
    have : e₁⁻¹ * e₂ = 1 := by
      refine hfaith _ (E.mul_mem (E.inv_mem h₁) h₂) fun w hw => ?_
      show e₁⁻¹ (e₂ w) = w
      rw [← h w hw]
      exact MulAut.inv_apply_self V e₁ w
    exact inv_mul_eq_one.1 this
  have hcomm : ∀ b ∈ B, e * b = b * e := by
    intro b hb
    refine hfaith' _ (E.mul_mem heE (hBE.1 hb)) _ (E.mul_mem (hBE.1 hb) heE) fun w hw => ?_
    have hbw : b w ∈ W := hXst b (hBX hb) w hw
    have h1 : (e * b) w = x (b w) := hag _ hbw
    have h2 : (b * e) w = b (x w) := by
      show b (e w) = b (x w)
      rw [hag w hw]
    have h3 : x (b w) = b (x w) := by
      have := congrArg (fun f : MulAut V => f w) (hXel.1 x hx b (hBX hb))
      exact this
    rw [h1, h2, h3]
  have hsq : e * e = 1 := by
    refine hfaith' _ (E.mul_mem heE heE) 1 E.one_mem fun w hw => ?_
    have hxw : x w ∈ W := hXst x hx w hw
    show e (e w) = w
    rw [hag w hw, hag _ hxw]
    have := congrArg (fun f : MulAut V => f w) (hXel.2 x hx)
    simpa [pow_two] using this
  have hel : IsElemAbelian2 (Subgroup.zpowers e) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.refl e |>.zpow_zpow k l).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have he2 : e ^ 2 = 1 := by rw [pow_two]; exact hsq
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [he2]
  have hZ : IsElemAbelian2 (B ⊔ Subgroup.zpowers e) := by
    refine isElemAbelian2_sup (isElemAbelian2_mono' hXel hBX) hel fun b hb z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (show Commute b e from (hcomm b hb).symm) k).eq
  have hZE : B ⊔ Subgroup.zpowers e ≤ E :=
    sup_le hBE.1 ((Subgroup.zpowers_le).2 heE)
  have hle := Glauberman.le_of_isSylowOf_of_le hBE (isPGroup_of_isElemAbelian2 hZ) le_sup_left hZE
  exact hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))

theorem jSplit_sl (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {P E X B : Subgroup (MulAut V)} (hXP : X ≤ P) (hXoff : IsOff X) (hBX : B ≤ X)
    (hEP : E ≤ P) (hsub : CFSG.Open.IsSubnormal E P)
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n) (htop : commV E ⊔ fixV E = ⊤)
    (hBE : IsSylowOf 2 B E) (hBne : B ≠ ⊥) :
    ∃ X₀ : Subgroup (MulAut V), X₀ ≤ X ∧ X₀ ≠ X ∧ wt X ≤ wt X₀ ∧ X ≤ B ⊔ X₀ := by
  have hXel : IsElemAbelian2 X := hXoff.2.2.1
  have hEX : ⁅E, X⁆ ≠ ⊥ := by
    intro hbot
    apply hBne
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine IsSLNatSection.eq_one_of_central hnat (hBE.1 hb) fun y hy => ?_
    have : ⁅y, b⁆ ∈ ⁅E, X⁆ := Subgroup.commutator_mem_commutator hy (hBX hb)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  obtain ⟨hXN, hXW, -, -, hidx⟩ := two_sixteen_sl hV hn hXoff hXP hEP hsub hnat hEX
  have hXst : X ≤ stabSub (commV E) := hXN.trans (normalizer_commV_le_stabSub E)
  have hXst' : ∀ x ∈ X, ∀ w ∈ commV E, x w ∈ commV E := fun x hx w hw => (hXst hx w).2 hw
  have hdec : ∀ x ∈ X, ∃ b ∈ B, ∀ w ∈ commV E, x w = b w := by
    intro x hx
    have hmem : resHom (commV E) ⟨x, hXst hx⟩ ∈ autSub E (commV E) :=
      hXW (mem_autSub.2 ⟨⟨x, hXst hx⟩, hx, rfl⟩)
    obtain ⟨g, hgE, hg⟩ := mem_autSub.1 hmem
    have hag : ∀ w ∈ commV E, (g : MulAut V) w = x w := fun w hw =>
      congrArg (fun φ : MulAut (commV E) => ((φ ⟨w, hw⟩ : commV E) : V)) hg
    exact ⟨(g : MulAut V), mem_B_of_agree hBE hBX hXel hXst'
      (fun e he h => eq_one_of_trivial_on_commV htop he h) hx hgE hag,
      fun w hw => (hag w hw).symm⟩
  have hB : ∃ b ∈ B, ∃ w ∈ commV E, b w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hBne
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact eq_one_of_trivial_on_commV htop (hBE.1 hb) (hcon b hb)
  exact jSplit_of_cen hXoff hBX hidx hdec hB

end CFSG.CGT.PushingUpLit.BHS5
