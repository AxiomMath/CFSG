module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Fac
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.Background.SmithB51LnSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm Matrix Module

section Transport

variable {V : Type} [CommGroup V] {n : ℕ} {L : Subgroup (MulAut V)} {W Y : Subgroup V}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
  {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem RealM.conj (h : B5.Ln.RealM L W Y π M) (hπ : Function.Bijective π) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) (hgY : g ∈ stabSub Y) :
    B5.Ln.RealM L (W.comap (g⁻¹ : MulAut V).toMonoidHom) Y
      (π.comp (B5.Ln.conjSL hπ hgL hgL').toMonoidHom) M := by
  obtain ⟨-, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  set σ := B5.Ln.conjSL hπ hgL hgL' with hσdef
  have hσ : ∀ γ, (((π.comp σ.toMonoidHom) γ : ↥L) : MulAut V) =
      g * ((π γ : ↥L) : MulAut V) * g⁻¹ := fun γ => B5.Ln.conjSL_spec hπ hgL hgL' γ
  have hgY' : g⁻¹ ∈ stabSub Y := (stabSub Y).inv_mem hgY
  let gres : ↥(W.comap (g⁻¹ : MulAut V).toMonoidHom) →* ↥W :=
    (g⁻¹ : MulAut V).toMonoidHom.subgroupComap W
  have hgres : ∀ y, ((gres y : ↥W) : V) = (g⁻¹ : MulAut V) y := fun _ => rfl
  refine ⟨hπ.2.comp σ.surjective, fun y hy => ?_, fun l w hw => ?_, hLY, β.comp gres,
    fun z => ?_, fun w => ?_, fun γ w hw => ?_⟩
  · show (g⁻¹ : MulAut V) y ∈ W
    exact hYW ((hgY' y).2 hy)
  · show (g⁻¹ : MulAut V) ((l : MulAut V) w) ∈ W
    have h1 := hLW ⟨g⁻¹ * l * g, hgL' l l.2⟩ _ hw
    simpa [MulAut.mul_apply] using h1
  · obtain ⟨w, rfl⟩ := hβs z
    have hgw : (g : MulAut V) w ∈ W.comap (g⁻¹ : MulAut V).toMonoidHom := by
      show (g⁻¹ : MulAut V) (g w) ∈ W
      rw [MulAut.inv_apply_self]
      exact w.2
    refine ⟨⟨_, hgw⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext (MulAut.inv_apply_self _ _ _)
  · rw [MonoidHom.comp_apply, hβk, hgres]
    exact hgY' w
  · have hw' : ((π γ : ↥L) : MulAut V) ((gres w : ↥W) : V) ∈ W := hLW (π γ) _ (gres w).2
    have h1 : gres ⟨_, hw⟩ = ⟨_, hw'⟩ := by
      apply Subtype.ext
      show (g⁻¹ : MulAut V) ((((π.comp σ.toMonoidHom) γ : ↥L) : MulAut V) (w : V)) =
        ((π γ : ↥L) : MulAut V) ((g⁻¹ : MulAut V) (w : V))
      rw [hσ]
      simp [MulAut.mul_apply]
    have h2 := hβe γ (gres w) hw'
    rw [← h1] at h2
    exact h2

theorem RealM.sup {X Y₀ : Subgroup V} (h : B5.Ln.RealM L X Y₀ π M) (hXY : X ⊔ Y = W)
    (hXY' : X ⊓ Y = Y₀) (hLW : ∀ l : ↥L, ∀ w ∈ W, (l : MulAut V) w ∈ W)
    (hLY : ∀ l : ↥L, ∀ y ∈ Y, (l : MulAut V) y ∈ Y) : B5.Ln.RealM L W Y π M := by
  classical
  obtain ⟨hπ, hY₀X, hLX, hLY₀, β, hβs, hβk, hβe⟩ := h
  have hXW : X ≤ W := hXY ▸ le_sup_left
  have hYW : Y ≤ W := hXY ▸ le_sup_right
  have hdec : ∀ w : ↥W, ∃ x : ↥X, ∃ y ∈ Y, (x : V) * y = w := fun w => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 (hXY ▸ w.2 : (w : V) ∈ X ⊔ Y)
    exact ⟨⟨x, hx⟩, y, hy, hxy⟩
  choose dX dY hdY hd using hdec
  have hwd : ∀ (x x' : ↥X) (y y' : V), y ∈ Y → y' ∈ Y → (x : V) * y = x' * y' → β x = β x' := by
    intro x x' y y' hy hy' hxy
    have h1 : ((x * x'⁻¹ : ↥X) : V) = y' * y⁻¹ := by
      have h0 : (x : V) = x' * y' * y⁻¹ := by rw [← hxy, mul_inv_cancel_right]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h0, mul_right_comm _ _ (x' : V)⁻¹,
        mul_right_comm (x' : V) y' (x' : V)⁻¹, mul_inv_cancel, one_mul]
    have h2 : β (x * x'⁻¹) = 1 := by
      rw [hβk, ← hXY']
      exact ⟨(x * x'⁻¹).2, h1 ▸ Y.mul_mem hy' (Y.inv_mem hy)⟩
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2
  let β₂ : ↥W →* Multiplicative (Fin n → ZMod 2) :=
    { toFun := fun w => β (dX w)
      map_one' := by
        rw [← map_one β]
        exact hwd _ 1 _ 1 (hdY 1) (one_mem _) (by rw [hd]; simp)
      map_mul' := fun w₁ w₂ => by
        rw [← map_mul]
        refine hwd _ _ (dY (w₁ * w₂)) (dY w₁ * dY w₂) (hdY _) (mul_mem (hdY w₁) (hdY w₂)) ?_
        rw [hd, Subgroup.coe_mul, Subgroup.coe_mul, mul_mul_mul_comm, hd, hd] }
  have hβ₂ : ∀ w, β₂ w = β (dX w) := fun _ => rfl
  have hβ₂x : ∀ x : ↥X, β₂ ⟨x, hXW x.2⟩ = β x := fun x =>
    hwd _ _ _ 1 (hdY _) (one_mem _) (by rw [hd, mul_one])
  refine ⟨hπ, hYW, hLW, hLY, β₂, fun z => ?_, fun w => ?_, fun γ w hw => ?_⟩
  · obtain ⟨x, rfl⟩ := hβs z
    exact ⟨⟨x, hXW x.2⟩, hβ₂x x⟩
  · rw [hβ₂, hβk]
    constructor
    · intro h1
      have hY₀Y : Y₀ ≤ Y := hXY' ▸ inf_le_right
      rw [← hd w]
      exact Y.mul_mem (hY₀Y h1) (hdY w)
    · intro h1
      have : (dX w : V) = w * (dY w)⁻¹ := by rw [← hd w, mul_inv_cancel_right]
      have h2 : (dX w : V) ∈ X ⊓ Y := ⟨(dX w).2, this ▸ Y.mul_mem h1 (Y.inv_mem (hdY w))⟩
      rwa [hXY'] at h2
  ·
    have hx' : ((π γ : ↥L) : MulAut V) ((dX w : ↥X) : V) ∈ X := hLX (π γ) _ (dX w).2
    have h1 : β₂ ⟨_, hw⟩ = β ⟨_, hx'⟩ := by
      rw [hβ₂]
      refine hwd _ _ (dY ⟨_, hw⟩) (((π γ : ↥L) : MulAut V) (dY w)) (hdY _) (hLY _ _ (hdY w)) ?_
      rw [hd]
      change ((π γ : ↥L) : MulAut V) (w : V) = _
      rw [← hd w, map_mul]
    rw [h1, hβe γ (dX w) hx', hβ₂]

end Transport

section Split

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

omit [Finite V] in
theorem card_altPre_eight (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range) :
    Nat.card ↥(altPre ψ) = 20160 := by
  rw [Nat.card_congr (altPreEquiv hψ hA).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem exists_realM_of_card (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {W Y : Subgroup V} (hYW : Y ≤ W)
    (hLY : altPre ψ ≤ stabSub Y) (hLW : altPre ψ ≤ stabSub W)
    (hnc : ¬ IsCentralSec (altPre ψ) Y W) (h16 : Nat.card (Sec W Y) = 16) :
    ∃ π : ↥(StatedSL 4 (ZMod 2)) →* ↥(altPre ψ), Function.Bijective π ∧
      B5.Ln.RealM (altPre ψ) W Y π B5.Ln.mat := by
  classical
  set L := altPre ψ with hLdef
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := Sec W Y)
    (fun a b => mul_comm a b) (sq_eq_one_sec hV W Y) (n := 4) (by rw [h16]; norm_num)
  let act : ↥L →* MulAut (Sec W Y) := secHom hLY hLW
  have hfaith : L ⊓ centSec W Y = ⊥ := by
    have h := inf_centSec_eq_bot (H := L) (ψ := altPreRes ψ) (by norm_num)
      (altPreRes_injective hψ) (le_range_altPreRes hA) hLY hLW (by rwa [altPre_altPreRes])
    exact h
  have hact : Function.Injective act := secHom_injective hLY hLW hfaith
  let ρ : ↥L →* GL (Fin 4) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp act
  have hρinj : Function.Injective ρ :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp hact
  have hρbij : Function.Bijective ρ := hρinj.bijective_of_nat_card_le
    (by rw [CFSG.GH74.Exceptional.card_GL_four_two, card_altPre_eight hψ hA])
  let ρe := MulEquiv.ofBijective ρ hρbij
  let ι : ↥(StatedSL 4 (ZMod 2)) →* GL (Fin 4) (ZMod 2) := (StatedSL 4 (ZMod 2)).subtype
  have hιbij : Function.Bijective ι := ⟨Subtype.val_injective, fun M => ⟨B5.Ln.ofGL M, rfl⟩⟩
  let π : ↥(StatedSL 4 (ZMod 2)) →* ↥L := ρe.symm.toMonoidHom.comp ι
  have hπbij : Function.Bijective π := ρe.symm.bijective.comp hιbij
  have hρπ : ∀ γ, ρ (π γ) = (γ : GL (Fin 4) (ZMod 2)) := fun γ => ρe.apply_symm_apply _
  refine ⟨π, hπbij, hπbij.2, hYW, fun l w hw => (hLW l.2 w).2 hw, fun l y hy => (hLY l.2 y).2 hy,
    e.toMonoidHom.comp (QuotientGroup.mk' (Y.subgroupOf W)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun w => ?_, fun γ w hw => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (act (π γ)) (QuotientGroup.mk w)
    have h2 : act (π γ) (QuotientGroup.mk w) = QuotientGroup.mk ⟨_, hw⟩ := secHom_mk _ _ _ _
    have h3 : CFSG.SectionRank.Ccomm.elemAutEquivGL e (act (π γ)) =
        (γ : GL (Fin 4) (ZMod 2)) := hρπ γ
    rw [h2, h3] at h1
    exact h1.symm

theorem realM_dmat_of_split (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {Y₀ Y' Y₁ : Subgroup V} {g : MulAut V}
    (hY : IsChiefFac H Y₀ Y₁) (hS : SplitFac H (altPre ψ) Y₀ Y' Y₁ g)
    (h16 : Nat.card (Sec Y' Y₀) = 16) :
    ∃ π : ↥(StatedSL 4 (ZMod 2)) →* ↥(altPre ψ), Function.Bijective π ∧
      B5.Ln.RealM (altPre ψ) Y' Y₀ π B5.Ln.mat ∧ B5.Ln.RealM (altPre ψ) Y₁ Y' π B5.Ln.dmat := by
  set L := altPre ψ with hLdef
  have hLY₀ : L ≤ stabSub Y₀ := altPre_le.trans hY.stab₀
  have hLY₁ : L ≤ stabSub Y₁ := altPre_le.trans hY.stab₁
  obtain ⟨π, hπ, h₁⟩ := exists_realM_of_card hV hψ hA hS.le₀ hLY₀ hS.stab hS.nc₀ h16
  have hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L := fun x hx => conj_mem_altPre hS.memH hx
  have hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L := fun x hx => by
    have := conj_mem_altPre (H.inv_mem hS.memH) hx
    rwa [inv_inv] at this
  set σ := B5.Ln.conjSL hπ hgL hgL' with hσdef
  have h₂ := RealM.conj h₁ hπ hgL hgL' (hY.stab₀ hS.memH)
  have h₃ := RealM.sup h₂ (by rw [sup_comm]; exact hS.sup_eq) (by rw [inf_comm]; exact hS.inf_eq)
    (fun l w hw => (hLY₁ l.2 w).2 hw) (fun l y hy => (hS.stab l.2 y).2 hy)
  refine ⟨π, hπ, h₁, ?_⟩
  obtain ⟨P, hP | hP⟩ := B5.Ln.aut_cases (by norm_num) σ
  ·
    exfalso
    apply hS.notL
    have hσP : ∀ γ, σ γ = B5.Ln.ofGL P * γ * (B5.Ln.ofGL P)⁻¹ := fun γ => by
      apply B5.Ln.mat_injective
      rw [hP γ, B5.Ln.mat_mul, B5.Ln.mat_mul, B5.Ln.mat_ofGL]
      rfl
    set l₀ : MulAut V := ((π (B5.Ln.ofGL P) : ↥L) : MulAut V) with hl₀
    have hl₀L : l₀ ∈ L := (π (B5.Ln.ofGL P)).2
    have hc : ∀ x ∈ L, (l₀⁻¹ * g) * x = x * (l₀⁻¹ * g) := by
      intro x hx
      obtain ⟨γ, hγ⟩ := hπ.2 ⟨x, hx⟩
      have h1 := B5.Ln.conjSL_spec hπ hgL hgL' γ
      rw [← hσdef, hσP, map_mul, map_mul, map_inv, hγ] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← hl₀] at h1
      calc l₀⁻¹ * g * x = l₀⁻¹ * (g * x * g⁻¹) * g := by group
        _ = l₀⁻¹ * (l₀ * x * l₀⁻¹) * g := by rw [h1]
        _ = x * (l₀⁻¹ * g) := by group
    have h1 := eq_one_of_commute_altPre (by norm_num) hψ hA
      (H.mul_mem (H.inv_mem (altPre_le hl₀L)) hS.memH) hc
    have h2 : g = l₀ := by
      have := congrArg (l₀ * ·) h1
      simpa [mul_assoc] using this
    rw [h2]
    exact hl₀L
  ·
    exact h₃.twist σ (fun γ => rfl) (B5.Ln.invT P) fun γ =>
      B5.Ln.twist_of_conj (B5.Ln.dmat_of_dmat_conj hP γ)

theorem card_le_index_mul_index_of_realM {L : Subgroup (MulAut V)} {Y₀ Y' Y₁ : Subgroup V}
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    (h₁ : B5.Ln.RealM L Y' Y₀ π B5.Ln.mat) (h₂ : B5.Ln.RealM L Y₁ Y' π B5.Ln.dmat)
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) (h16 : Nat.card B ≤ 16) :
    Nat.card B ≤ (fixV (autSec B Y' Y₀)).index * (fixV (autSec B Y₁ Y')).index := by
  set B' := B5.Ln.pre π B with hB'
  have hcardB := B5.Ln.card_pre hπ hBL
  have e₁ := h₁.card_fixV_autSec hBL
  have e₂ := h₂.card_fixV_autSec hBL
  rw [B5.Ln.fixM_mat] at e₁
  rw [B5.Ln.fixM_dmat] at e₂
  have s₁ := h₁.card_sec
  have s₂ := h₂.card_sec
  have i₁ := (fixV (autSec B Y' Y₀)).index_mul_card
  have i₂ := (fixV (autSec B Y₁ Y')).index_mul_card
  rw [e₁, s₁] at i₁
  rw [e₂, s₂] at i₂
  have hfd := B5.Ln.finrank_fixD_add B'
  have hbound := B5.Ln.card_le_two_pow_mul B'
  have hc₁ := B5.Ln.finrank_fixN_le B'
  rw [hcardB] at hbound
  generalize finrank (ZMod 2) (B5.Ln.fixN B') = c₁ at hc₁ hbound i₁
  generalize finrank (ZMod 2) (B5.Ln.fixD B') = c₂ at hfd i₂
  generalize finrank (ZMod 2) (B5.Ln.commN B') = d at hfd hbound
  generalize (fixV (autSec B Y' Y₀)).index = x₁ at i₁ ⊢
  generalize (fixV (autSec B Y₁ Y')).index = x₂ at i₂ ⊢
  generalize Nat.card ↥B = b at hbound h16 ⊢
  have hd : d ≤ 4 := by omega
  have hx₁ : x₁ = 2 ^ (4 - c₁) := Nat.eq_of_mul_eq_mul_right (pow_pos two_pos c₁)
    (i₁.trans (by rw [← pow_add, Nat.sub_add_cancel hc₁]))
  have hx₂ : x₂ = 2 ^ d := Nat.eq_of_mul_eq_mul_right (pow_pos two_pos c₂)
    (i₂.trans (by rw [← pow_add, show d + c₂ = 4 by omega]))
  subst hx₁ hx₂
  clear i₁ i₂ hfd
  interval_cases c₁ <;> interval_cases d <;> norm_num at hbound ⊢ <;> omega

theorem card_le_index_fixV_of_split (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {Y₀ Y' Y₁ : Subgroup V} {g : MulAut V}
    (hY : IsChiefFac H Y₀ Y₁) (hS : SplitFac H (altPre ψ) Y₀ Y' Y₁ g)
    (h16 : Nat.card (Sec Y' Y₀) = 16) {B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hel : IsElemAbelian2 B) : Nat.card B ≤ (fixV B).index := by
  have hB16 := card_le_sixteen hψ hBH hel
  by_cases hBL : B ≤ altPre ψ
  · obtain ⟨π, hπ, h₁, h₂⟩ := realM_dmat_of_split hV hψ hA hY hS h16
    have h1 := card_le_index_mul_index_of_realM hπ h₁ h₂ hBL hB16
    have e1 := index_fixV_autSec_mul_relIndex_le hS.le₀ (hBL.trans hS.stab)
    have e2 := index_fixV_autSec_mul_relIndex_le hS.le₁ (hBH.trans hY.stab₁)
    have e3 := relIndex_fixV_le_index B Y₁
    have hpos : 0 < (fixV B).relIndex Y₀ := relIndex_pos_of_finite _ _
    have e4 : (fixV (autSec B Y' Y₀)).index ≤ (fixV B).relIndex Y' :=
      (Nat.le_mul_of_pos_right _ hpos).trans e1
    have e5 := Nat.mul_le_mul_left (fixV (autSec B Y₁ Y')).index e4
    calc Nat.card B ≤ (fixV (autSec B Y' Y₀)).index * (fixV (autSec B Y₁ Y')).index := h1
      _ = (fixV (autSec B Y₁ Y')).index * (fixV (autSec B Y' Y₀)).index := mul_comm _ _
      _ ≤ (fixV (autSec B Y₁ Y')).index * (fixV B).relIndex Y' := e5
      _ ≤ (fixV B).relIndex Y₁ := e2
      _ ≤ (fixV B).index := e3
  · obtain ⟨b, hb, hbL⟩ := Set.not_subset.1 hBL
    have h1 := card_sec_le_index_of_swap hS.le₀ hS.le₁ (hBH.trans hY.stab₀) (hBH.trans hY.stab₁)
      hb (hS.swap b (hBH hb) hbL)
    have e1 := index_fixV_autSec_mul_relIndex_le hY.le (hBH.trans hY.stab₁)
    have e3 := relIndex_fixV_le_index B Y₁
    have hpos : 0 < (fixV B).relIndex Y₀ := relIndex_pos_of_finite _ _
    have e4 := (Nat.le_mul_of_pos_right (fixV (autSec B Y₁ Y₀)).index hpos).trans e1
    omega

theorem exotic_three (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    (hII : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ → ¬ IsCentralSec (altPre ψ) Y₀ Y₁ →
      ¬ NatSec ψ Y₀ Y₁)
    (hrange : ψ.range = ⊤) (B : Subgroup (MulAut V)) (hB : IsFFStarOffender H B) :
    Nat.card V = Nat.card B * Nat.card (fixV B) := by
  set L := altPre ψ with hLdef
  have hLV : ¬ (⊤ : Subgroup V) ≤ fixV L := by
    intro h
    obtain ⟨x, hx, h3⟩ := exists_isThreeCycle_mem (by norm_num) (altPreEquiv hψ hA)
    apply ne_one_of_isThreeCycle (altPreEquiv hψ hA) hx h3
    ext v
    exact h (Subgroup.mem_top v) x hx
  have htop : H ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => by simp only [Subgroup.mem_top]
  obtain ⟨Y₀, Y₁, hY, -, hL⟩ := exists_isChiefFac_altPre (by norm_num) hψ hA htop hLV
  have hle : Nat.card B ≤ (fixV B).index := by
    rcases chief_cases hB42 hV hψ hA hB hY hL with ⟨-, hLH⟩ | hN | ⟨Y', g, hS, h16, -⟩
    · exfalso
      obtain ⟨h, hh⟩ : swap (0 : Fin 8) 1 ∈ ψ.range := hrange ▸ Subgroup.mem_top _
      have h1 : (h : MulAut V) ∈ L := by rw [hLdef, hLH]; exact h.2
      have h2 := coe_mem_altPre_iff.1 h1
      rw [hh, Perm.mem_alternatingGroup, Perm.sign_swap (by decide)] at h2
      exact absurd h2 (by decide)
    · exact absurd hN (hII Y₀ Y₁ hY hL)
    · exact card_le_index_fixV_of_split hV hψ hA hY hS h16 hB.1 hB.2.2.1
  have hv : Nat.card V ≤ Nat.card B * Nat.card (fixV B) := by
    have := hB.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  have h1 := (fixV B).index_mul_card
  have h2 := Nat.mul_le_mul_right (Nat.card (fixV B)) hle
  omega

end Split

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
