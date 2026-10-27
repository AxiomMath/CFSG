module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin

namespace KCut

variable {W : Type} [CommGroup W]

@[expose] def IsKGen (x y : MulAut W) : Prop :=
  y * y = 1 ∧ y ≠ x ∧ y * x = x * y ∧ ∀ w : W, y (x w * w⁻¹) = x w * w⁻¹

@[expose] def Kgrp (L : Subgroup (MulAut W)) (x : MulAut W) : Subgroup (MulAut W) :=
  Subgroup.closure {y | y ∈ L ∧ IsKGen x y}

theorem Kgrp_le (L : Subgroup (MulAut W)) (x : MulAut W) : Kgrp L x ≤ L :=
  (Subgroup.closure_le L).2 fun _ hy => hy.1

theorem Kgrp_le_centralizer (L : Subgroup (MulAut W)) (x : MulAut W) :
    Kgrp L x ≤ Subgroup.centralizer {x} := by
  refine (Subgroup.closure_le _).2 fun y hy => ?_
  exact Subgroup.mem_centralizer_singleton_iff.2 hy.2.2.2.1

theorem Kgrp_le_cent (L : Subgroup (MulAut W)) (x : MulAut W) :
    Kgrp L x ≤ L ⊓ Subgroup.centralizer {x} :=
  le_inf (Kgrp_le L x) (Kgrp_le_centralizer L x)

theorem Kgrp_fixes_disp {L : Subgroup (MulAut W)} {x k : MulAut W} (hk : k ∈ Kgrp L x) (w : W) :
    k (x w * w⁻¹) = x w * w⁻¹ := by
  induction hk using Subgroup.closure_induction with
  | mem y hy => exact hy.2.2.2.2 w
  | one => exact MulAut.one_apply _ _
  | mul a b _ _ ha hb =>
    rw [MulAut.mul_apply, hb, ha]
  | inv a _ ha =>
    have h := congrArg (a⁻¹ : MulAut W) ha
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h
    exact h.symm

theorem IsKGen.conj {x y : MulAut W} (h : IsKGen x y) (g : MulAut W) :
    IsKGen (g * x * g⁻¹) (g * y * g⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, fun w => ?_⟩
  · calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h
    apply h2
    have := mul_left_cancel (mul_right_cancel (h : g * y * g⁻¹ = g * x * g⁻¹))
    exact this
  · calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [h3]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · have e1 : (g * x * g⁻¹) w * w⁻¹ = g (x (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e1]
    have := congrArg g (h4 (g⁻¹ w))
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using this

theorem mem_Kgrp_conj {L : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ L) (x k : MulAut W) :
    k ∈ Kgrp L (g * x * g⁻¹) ↔ g⁻¹ * k * g ∈ Kgrp L x := by
  have key : ∀ (g : MulAut W), g ∈ L → ∀ x k : MulAut W, g⁻¹ * k * g ∈ Kgrp L x →
      k ∈ Kgrp L (g * x * g⁻¹) := by
    intro g hg x k hk
    have hmap : ∀ y ∈ Kgrp L x, g * y * g⁻¹ ∈ Kgrp L (g * x * g⁻¹) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        exact Subgroup.subset_closure ⟨L.mul_mem (L.mul_mem hg hy.1) (L.inv_mem hg),
          hy.2.conj g⟩
      | one => simp
      | mul a b _ _ ha hb =>
        have := (Kgrp L (g * x * g⁻¹)).mul_mem ha hb
        simpa [mul_assoc] using this
      | inv a _ ha =>
        have := (Kgrp L (g * x * g⁻¹)).inv_mem ha
        simpa [mul_assoc] using this
    have := hmap _ hk
    simpa [mul_assoc] using this
  refine ⟨fun h => ?_, key g hg x k⟩
  have h2 := key g⁻¹ (L.inv_mem hg) (g * x * g⁻¹) (g⁻¹ * k * g) (by simpa [mul_assoc] using h)
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem Kgrp_cent_mem {L : Subgroup (MulAut W)} {x c k : MulAut W} (hc : c ∈ L)
    (hcx : c * x = x * c) (hk : k ∈ Kgrp L x) : c * k * c⁻¹ ∈ Kgrp L x := by
  have hx : c * x * c⁻¹ = x := by rw [hcx]; group
  have h := (mem_Kgrp_conj (L := L) hc x (c * k * c⁻¹))
  rw [hx] at h
  refine h.2 ?_
  have e : c⁻¹ * (c * k * c⁻¹) * c = k := by group
  rwa [e]

theorem le_Kgrp_of_quadratic {L E : Subgroup (MulAut W)} (hEL : E ≤ L)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hquad : ∀ a ∈ E, ∀ b ∈ E, ∀ w : W, b (a w * w⁻¹) = a w * w⁻¹) {x f : MulAut W}
    (hx : x ∈ E) (hx1 : x ≠ 1) (hf : f ∈ E) (hf1 : f ≠ 1) (hfx : f ≠ x) : E ≤ Kgrp L x := by
  have hgen : ∀ y ∈ E, y ≠ x → y ∈ Kgrp L x := fun y hy hyx =>
    Subgroup.subset_closure ⟨hEL hy, hsq y hy, hyx, hcomm y hy x hx, fun w => hquad x hx y hy w⟩
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    have h1 : y * f ∈ Kgrp L y := hgen _ (E.mul_mem hy hf) fun h => hf1 (by
      have := mul_left_cancel (h.trans (mul_one y).symm)
      exact this)
    have h2 : f ∈ Kgrp L y := hgen f hf hfx
    have := (Kgrp L y).mul_mem h1 h2
    have e : y * f * f = y := by
      rw [mul_assoc, hsq f hf, mul_one]
    rwa [e] at this
  · exact hgen y hy hyx

theorem quadratic_apply {E : Subgroup (MulAut W)} (hE : IsQuadratic E) {a b : MulAut W}
    (ha : a ∈ E) (hb : b ∈ E) (w : W) : b (a w * w⁻¹) = a w * w⁻¹ :=
  hE (Subgroup.subset_closure ⟨a, ha, w, rfl⟩) b hb

theorem le_Kgrp_of_isQuadratic {L E : Subgroup (MulAut W)} (hEL : E ≤ L) (hel : IsElemAbelian2 E)
    (hq : IsQuadratic E) {x f : MulAut W} (hx : x ∈ E) (hx1 : x ≠ 1) (hf : f ∈ E) (hf1 : f ≠ 1)
    (hfx : f ≠ x) : E ≤ Kgrp L x :=
  le_Kgrp_of_quadratic hEL hel.1 (fun a ha => by rw [← sq]; exact hel.2 a ha)
    (fun a ha b hb w => quadratic_apply hq ha hb w) hx hx1 hf hf1 hfx

omit [CommGroup W] in
theorem sup_induction' {G : Type*} [Group G] {s t : Subgroup G} {p : G → Prop} {x : G}
    (hx : x ∈ s ⊔ t) (hs : ∀ x ∈ s, p x) (ht : ∀ x ∈ t, p x) (h1 : p 1)
    (hmul : ∀ x y, p x → p y → p (x * y)) (hinv : ∀ x, p x → p x⁻¹) : p x := by
  rw [← Subgroup.closure_eq s, ← Subgroup.closure_eq t, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => rcases hy with hy | hy
                · exact hs y hy
                · exact ht y hy
  | one => exact h1
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha => exact hinv a ha

theorem disp_eq_one_of_sup_eq {L : Subgroup (MulAut W)} {u v : MulAut W} (hfix : fixV L = ⊥)
    (hsup : Kgrp L u ⊔ Kgrp L v = L) {w₁ w₂ : W} (h : u w₁ * w₁⁻¹ = v w₂ * w₂⁻¹) :
    u w₁ * w₁⁻¹ = 1 := by
  have hz : u w₁ * w₁⁻¹ ∈ fixV L := by
    intro g hg
    rw [← hsup] at hg
    refine sup_induction' (p := fun g => g (u w₁ * w₁⁻¹) = u w₁ * w₁⁻¹) hg
      (fun k hk => Kgrp_fixes_disp hk w₁) (fun k hk => ?_) (MulAut.one_apply _ _) (fun a b ha hb => ?_)
      (fun a ha => ?_)
    · rw [h]
      exact Kgrp_fixes_disp hk w₂
    · rw [MulAut.mul_apply, hb, ha]
    · have h' := congrArg (a⁻¹ : MulAut W) ha
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h'
      exact h'.symm
  rw [hfix] at hz
  exact hz

theorem exists_fixed_ne_one (hW : ∀ w : W, w * w = 1) [Nontrivial W] {e : MulAut W}
    (he : e * e = 1) : ∃ w : W, w ≠ 1 ∧ e w = w := by
  by_contra hcon
  push Not at hcon
  let φ : W →* W :=
    { toFun := fun w => e w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul, mul_inv_rev]; ac_rfl }
  have hφ : ∀ w, φ w = e w * w⁻¹ := fun w => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [hφ, mul_inv_eq_one] at hw
    by_contra hw1
    exact hcon w hw1 hw
  have hφφ : ∀ w, φ (φ w) = 1 := by
    intro w
    have hee : e (e w) = w := by
      have := congrArg (fun m : MulAut W => m w) he
      simpa [MulAut.mul_apply] using this
    have step : φ (φ w) = (w * (e w)⁻¹) * ((e w)⁻¹ * w) := by
      simp only [hφ, map_mul, map_inv, hee, mul_inv_rev, inv_inv]
      ac_rfl
    rw [step]
    have : w * (e w)⁻¹ * ((e w)⁻¹ * w) = (w * w) * (e w * e w)⁻¹ := by
      rw [mul_inv_rev]; ac_rfl
    rw [this, hW w, hW (e w)]; simp
  obtain ⟨w, hw⟩ := exists_ne (1 : W)
  have h1 : φ w = 1 := hinj (by rw [hφφ, map_one])
  have h2 : e w = w := by rwa [hφ, mul_inv_eq_one] at h1
  exact hcon w hw h2

theorem mem_fixV_zpowers_iff {e : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers e) ↔ e v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem cent_stab {e g : MulAut W} (hg : g * e = e * g) {u : W} (hu : u ∈ fixV (Subgroup.zpowers e)) :
    g u ∈ fixV (Subgroup.zpowers e) := by
  rw [mem_fixV_zpowers_iff] at hu ⊢
  have := congrArg (fun m : MulAut W => m u) hg
  simp only [MulAut.mul_apply] at this
  rw [← this, hu]

theorem exists_fixed_ne_of_max [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {e f : MulAut W} (he2 : e * e = 1) (he1 : e ≠ 1)
    (hgen : (L ⊓ Subgroup.centralizer {e}) ⊔ (L ⊓ Subgroup.centralizer {f}) = L)
    (hcard : Nat.card (fixV (Subgroup.zpowers f)) ≤ Nat.card (fixV (Subgroup.zpowers e))) :
    ∃ w : W, e w = w ∧ f w ≠ w := by
  by_contra hcon
  push Not at hcon
  have hle : fixV (Subgroup.zpowers e) ≤ fixV (Subgroup.zpowers f) := fun v hv =>
    mem_fixV_zpowers_iff.2 (hcon v (mem_fixV_zpowers_iff.1 hv))
  have heq : fixV (Subgroup.zpowers e) = fixV (Subgroup.zpowers f) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  set U := fixV (Subgroup.zpowers e) with hU
  have hinv : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    have hg' : g ∈ (L ⊓ Subgroup.centralizer {e}) ⊔ (L ⊓ Subgroup.centralizer {f}) := by
      rw [hgen]; exact hg
    have key := sup_induction' (p := fun g : MulAut W =>
        (∀ u ∈ U, g u ∈ U) ∧ (∀ u ∈ U, g⁻¹ u ∈ U)) hg'
      (fun g hg => ⟨fun u hu => cent_stab (Subgroup.mem_centralizer_singleton_iff.1 hg.2) hu,
        fun u hu => cent_stab (Subgroup.mem_centralizer_singleton_iff.1
          ((Subgroup.inv_mem_iff _).2 hg).2) hu⟩)
      (fun g hg => ⟨fun u hu => by
          rw [heq] at hu ⊢
          exact cent_stab (Subgroup.mem_centralizer_singleton_iff.1 hg.2) hu,
        fun u hu => by
          rw [heq] at hu ⊢
          exact cent_stab (Subgroup.mem_centralizer_singleton_iff.1
            ((Subgroup.inv_mem_iff _).2 hg).2) hu⟩)
      ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩
      (fun x y hx hy => ⟨fun u hu => by
          rw [MulAut.mul_apply]; exact hx.1 _ (hy.1 u hu),
        fun u hu => by
          rw [mul_inv_rev, MulAut.mul_apply]; exact hy.2 _ (hx.2 u hu)⟩)
      (fun x hx => ⟨hx.2, by simpa using hx.1⟩)
    exact key.1 u hu
  rcases hirr U hinv with h | h
  · obtain ⟨w, hw1, hw⟩ := exists_fixed_ne_one hW he2
    have : w ∈ U := mem_fixV_zpowers_iff.2 hw
    rw [h] at this
    exact hw1 (Subgroup.mem_bot.1 this)
  · apply he1
    ext w
    have : w ∈ U := by rw [h]; trivial
    simpa using mem_fixV_zpowers_iff.1 this

@[expose] def GenPair (L : Subgroup (MulAut W)) (u v : MulAut W) : Prop :=
  (L ⊓ Subgroup.centralizer {u}) ⊔ (L ⊓ Subgroup.centralizer {v}) = L

theorem GenPair.symm {L : Subgroup (MulAut W)} {u v : MulAut W} (h : GenPair L u v) :
    GenPair L v u := by
  unfold GenPair at *
  rw [sup_comm]; exact h

theorem cut_aux [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) {e f : MulAut W} (he2 : e * e = 1) (he1 : e ≠ 1) (hef : e * f = f * e)
    (hgen₁ : GenPair L e f) (hgen₂ : GenPair L f (e * f))
    (hcard : Nat.card (fixV (Subgroup.zpowers f)) ≤ Nat.card (fixV (Subgroup.zpowers e))) :
    Kgrp L f ≠ L ⊓ Subgroup.centralizer {f} ∨
      Kgrp L (e * f) ≠ L ⊓ Subgroup.centralizer {e * f} := by
  obtain ⟨w, hew, hfw⟩ := exists_fixed_ne_of_max hW hirr he2 he1 hgen₁ hcard
  by_contra hcon
  push Not at hcon
  have hsup : Kgrp L f ⊔ Kgrp L (e * f) = L := by
    rw [hcon.1, hcon.2]; exact hgen₂
  have hw2 : f w * w⁻¹ = (e * f) w * w⁻¹ := by
    have : (e * f) w = f w := by
      rw [hef, MulAut.mul_apply, hew]
    rw [this]
  have h1 := disp_eq_one_of_sup_eq hfix hsup hw2
  exact hfw (mul_inv_eq_one.1 h1)

theorem exists_Kgrp_ne_cent [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) {a b : MulAut W} (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) (hne : a ≠ b)
    (hgen₁ : GenPair L a b) (hgen₂ : GenPair L a (a * b)) (hgen₃ : GenPair L b (a * b)) :
    Kgrp L a ≠ L ⊓ Subgroup.centralizer {a} ∨ Kgrp L b ≠ L ⊓ Subgroup.centralizer {b} ∨
      Kgrp L (a * b) ≠ L ⊓ Subgroup.centralizer {a * b} := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hb2)
  have hba : b * a = a * b := hab.symm
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; group
  have hba' : b * a = a * b := hba
  set ca := Nat.card (fixV (Subgroup.zpowers a))
  set cb := Nat.card (fixV (Subgroup.zpowers b))
  set cab := Nat.card (fixV (Subgroup.zpowers (a * b)))
  by_cases h1 : cb ≤ ca ∧ cab ≤ ca
  ·
    rcases cut_aux hW hirr hfix ha2 ha1 hab hgen₁ hgen₃ h1.1 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h2 : ca ≤ cb ∧ cab ≤ cb
    ·
      have hgen₃' : GenPair L a (b * a) := by rw [hba']; exact hgen₂
      rcases cut_aux hW hirr hfix hb2 hb1 hba hgen₁.symm hgen₃' h2.1 with h | h
      · exact Or.inl h
      · rw [hba'] at h
        exact Or.inr (Or.inr h)
    ·
      have hca : ca ≤ cab := by omega
      have hfa : (a * b) * a = b := by
        calc a * b * a = a * (b * a) := by group
          _ = a * (a * b) := by rw [hba]
          _ = (a * a) * b := by group
          _ = b := by rw [ha2]; group
      have hcomm : (a * b) * a = a * (a * b) := by
        rw [hfa]
        calc b = (a * a) * b := by rw [ha2]; group
          _ = a * (a * b) := by group
      have hgen₃' : GenPair L a ((a * b) * a) := by rw [hfa]; exact hgen₁
      rcases cut_aux hW hirr hfix hab2 hab1 hcomm hgen₂.symm hgen₃' (by omega) with h | h
      · exact Or.inl h
      · rw [hfa] at h
        exact Or.inr (Or.inl h)

theorem Kgrp_eq_cent_conj {L : Subgroup (MulAut W)} {g z : MulAut W} (hg : g ∈ L)
    (h : Kgrp L z = L ⊓ Subgroup.centralizer {z}) :
    Kgrp L (g * z * g⁻¹) = L ⊓ Subgroup.centralizer {g * z * g⁻¹} := by
  refine le_antisymm (Kgrp_le_cent L _) fun k hk => ?_
  rw [mem_Kgrp_conj hg, h]
  refine ⟨L.mul_mem (L.mul_mem (L.inv_mem hg) hk.1) hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  calc g⁻¹ * k * g * z = g⁻¹ * (k * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * k) * g := by rw [this]
    _ = z * (g⁻¹ * k * g) := by group

theorem Kgrp_le_of_dichotomy [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV L = ⊥) (A : Set (MulAut W)) (hA2 : ∀ z ∈ A, z * z = 1)
    (hA1 : ∀ z ∈ A, z ≠ 1) (hAconj : ∀ z ∈ A, ∀ z' ∈ A, ∃ g ∈ L, z' = g * z * g⁻¹)
    (Q : MulAut W → Subgroup (MulAut W))
    (hdich : ∀ z ∈ A, Kgrp L z ≤ Q z ∨ Kgrp L z = L ⊓ Subgroup.centralizer {z})
    {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ A) (hab' : a * b ∈ A) (hab : a * b = b * a)
    (hne : a ≠ b) (hgen₁ : GenPair L a b) (hgen₂ : GenPair L a (a * b))
    (hgen₃ : GenPair L b (a * b)) : ∀ z ∈ A, Kgrp L z ≤ Q z := by
  intro z hz
  rcases hdich z hz with h | h
  · exact h
  · exfalso
    have hK : ∀ u ∈ A, Kgrp L u = L ⊓ Subgroup.centralizer {u} := by
      intro u hu
      obtain ⟨g, hg, rfl⟩ := hAconj z hz u hu
      exact Kgrp_eq_cent_conj hg h
    rcases exists_Kgrp_ne_cent hW hirr hfix (hA2 a ha) (hA2 b hb) (hA1 a ha) (hA1 b hb) hab hne
      hgen₁ hgen₂ hgen₃ with h' | h' | h'
    · exact h' (hK a ha)
    · exact h' (hK b hb)
    · exact h' (hK _ hab')

end KCut

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
