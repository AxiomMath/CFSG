module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg2

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

section Aux

variable {V : Type} [CommGroup V]

@[expose] def tr (g : MulAut V) (W : Subgroup V) : Subgroup V := W.map g.toMonoidHom

theorem mem_tr {g : MulAut V} {W : Subgroup V} {v : V} : v ∈ tr g W ↔ ∃ w ∈ W, g w = v :=
  Iff.rfl

theorem apply_mem_tr {g : MulAut V} {W : Subgroup V} {w : V} (hw : w ∈ W) : g w ∈ tr g W :=
  ⟨w, hw, rfl⟩

theorem tr_mono (g : MulAut V) {W W' : Subgroup V} (h : W ≤ W') : tr g W ≤ tr g W' :=
  Subgroup.map_mono h

theorem irr_ginv_sup {A : Subgroup V} {H K : Subgroup (MulAut V)} (hH : GInv H A)
    (hK : GInv K A) : GInv (H ⊔ K) A := by
  have key : ∀ g ∈ H ⊔ K, (∀ a ∈ A, g a ∈ A) ∧ ∀ a ∈ A, g⁻¹ a ∈ A := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact ⟨hH g hg, hH g⁻¹ (H.inv_mem hg)⟩
      · exact ⟨hK g hg, hK g⁻¹ (K.inv_mem hg)⟩
    | one => exact ⟨fun a ha => by simpa using ha, fun a ha => by simpa using ha⟩
    | mul g₁ g₂ _ _ h₁ h₂ =>
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · simpa [MulAut.mul_apply] using h₁.1 _ (h₂.1 a ha)
      · simpa [mul_inv_rev, MulAut.mul_apply] using h₂.2 _ (h₁.2 a ha)
    | inv g _ h => exact ⟨h.2, fun a ha => by simpa using h.1 a ha⟩
  exact fun g hg a ha => (key g hg).1 a ha

theorem cm_invariant {M : Subgroup V} {A : Subgroup (MulAut V)} (hM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M)
    {a : MulAut V} (ha : a ∈ A) {w : V} (hw : w ∈ cm M A) : a w ∈ cm M A := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, m, hm, rfl⟩ := hw
    have h1 : a (b m * m⁻¹) = (a * b * a⁻¹) (a m) * (a m)⁻¹ := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [h1]
    exact mem_cm (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (hM a ha m hm)
  | one => simp [one_mem]
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem cm_le_of_invariant {M : Subgroup V} {A : Subgroup (MulAut V)}
    (hM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M) : cm M A ≤ M := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, ha, m, hm, rfl⟩
  exact mul_mem (hM a ha m hm) (inv_mem hm)

end Aux

section Main

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem cfg_comm_ty (cfg : EndCfg4 G T Y) {t : MulAut V} (ht : t ∈ T) {y : MulAut V}
    (hy : y ∈ Y) : t * y = y * t :=
  Subgroup.mem_centralizer_iff.mp (cfg.adm.hYC hy).2 t ht

omit [Finite V] in
theorem conj_mem_conjClosure {t l : MulAut V} (ht : t ∈ G) (hl : l ∈ CGT6.conjClosure Y G) :
    t * l * t⁻¹ ∈ CGT6.conjClosure Y G :=
  (Subgroup.mem_normalizer_iff.mp (CGT6.le_normalizer_conjClosure ht) l).mp hl

omit [Finite V] in
theorem conj_inv_mem_conjClosure {t l : MulAut V} (ht : t ∈ G)
    (hl : l ∈ CGT6.conjClosure Y G) : t⁻¹ * l * t ∈ CGT6.conjClosure Y G := by
  simpa using conj_mem_conjClosure (Y := Y) (G.inv_mem ht) hl

theorem irr_ginv_of_cfg (cfg : EndCfg4 G T Y) {A : Subgroup V}
    (hL : GInv (CGT6.conjClosure Y G) A) (hT : GInv T A) : GInv G A := by
  have := irr_ginv_sup hL hT
  rwa [cfg.gen] at this

theorem irr_ginv_iSup (cfg : EndCfg4 G T Y) {W : Subgroup V}
    (hW : GInv (CGT6.conjClosure Y G) W) : GInv G (⨆ t : T, tr (t : MulAut V) W) := by
  refine irr_ginv_of_cfg cfg (fun l hl a ha => ?_) (fun t' ht' a ha => ?_)
  · refine Subgroup.iSup_induction (fun t : T => tr (t : MulAut V) W)
      (C := fun a => l a ∈ ⨆ t : T, tr (t : MulAut V) W) ha (fun t b hb => ?_) (by simp)
      (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
    obtain ⟨w, hw, rfl⟩ := mem_tr.mp hb
    have htl := conj_inv_mem_conjClosure (Y := Y) (cfg.adm.hTG t.2) hl
    have e : l ((t : MulAut V) w) = (t : MulAut V) (((t : MulAut V)⁻¹ * l * t) w) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.mem_iSup_of_mem t (apply_mem_tr (hW _ htl w hw))
  · refine Subgroup.iSup_induction (fun t : T => tr (t : MulAut V) W)
      (C := fun a => t' a ∈ ⨆ t : T, tr (t : MulAut V) W) ha (fun t b hb => ?_) (by simp)
      (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
    obtain ⟨w, hw, rfl⟩ := mem_tr.mp hb
    have e : t' ((t : MulAut V) w) = ((t' * t : MulAut V)) w := by simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.mem_iSup_of_mem (⟨t' * t, T.mul_mem ht' t.2⟩ : T) (apply_mem_tr hw)

theorem irreducible_of_cfg (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) {W : Subgroup V}
    (hW : GInv (CGT6.conjClosure Y G) W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  have hsq := simpleQuot_of_cfg hV cfg
  have hgen := commGen_of_perfect cfg.adm.hperf
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hWY : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W := fun y hy => hW y (hYL hy)
  have hWtop : (⨆ t : T, tr (t : MulAut V) W) = ⊤ := by
    rcases cfg.irr _ (irr_ginv_iSup cfg hW) with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      have h1 : w ∈ ⨆ t : T, tr (t : MulAut V) W :=
        Subgroup.mem_iSup_of_mem (⟨1, T.one_mem⟩ : T) ⟨w, hw, by simp⟩
      rw [h] at h1
      exact h1
    · exact h
  have hUB : commV Y ≤ ⨆ t : T, tr (t : MulAut V) (cm W Y) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, hy, v, rfl⟩
    have hv : v ∈ ⨆ t : T, tr (t : MulAut V) W := by rw [hWtop]; exact Subgroup.mem_top v
    refine Subgroup.iSup_induction (fun t : T => tr (t : MulAut V) W)
      (C := fun v => dlt y v ∈ ⨆ t : T, tr (t : MulAut V) (cm W Y)) hv (fun t b hb => ?_)
      (by simp [dlt_apply]) (fun a b ha hb => by rw [map_mul]; exact mul_mem ha hb)
    obtain ⟨w, hw, rfl⟩ := mem_tr.mp hb
    have e : dlt y ((t : MulAut V) w) = (t : MulAut V) (dlt y w) := by
      simp only [dlt_apply, map_mul, map_inv, apply_comm (cfg_comm_ty cfg t.2 hy).symm w]
    rw [e]
    exact Subgroup.mem_iSup_of_mem t (apply_mem_tr (mem_cm hy hw))
  have hNU : ∀ t : T, tr (t : MulAut V) (cm W Y) ≤ commV Y := by
    intro t n hn
    obtain ⟨m, hm, rfl⟩ := mem_tr.mp hn
    exact apply_mem_commV_of_comm (fun y hy => cfg_comm_ty cfg t.2 hy) (cm_le_commV W Y hm)
  have hNinv : ∀ t : T, ∀ y ∈ Y, ∀ n ∈ tr (t : MulAut V) (cm W Y),
      y n ∈ tr (t : MulAut V) (cm W Y) := by
    intro t y hy n hn
    obtain ⟨m, hm, rfl⟩ := mem_tr.mp hn
    exact mem_tr.mpr ⟨y m, cm_invariant hWY hy hm, apply_comm (cfg_comm_ty cfg t.2 hy) m⟩
  have hex : ∃ t : T, commV Y ⊓ fixV Y ⊔ tr (t : MulAut V) (cm W Y) = commV Y := by
    by_contra hcon0
    have hcon : ∀ t : T, commV Y ⊓ fixV Y ⊔ tr (t : MulAut V) (cm W Y) ≠ commV Y :=
      fun t h => hcon0 ⟨t, h⟩
    apply hsq.1
    have hall : ∀ t : T, tr (t : MulAut V) (cm W Y) ≤ commV Y ⊓ fixV Y := by
      intro t
      have hSinv : ∀ y ∈ Y, ∀ n ∈ commV Y ⊓ fixV Y ⊔ tr (t : MulAut V) (cm W Y),
          y n ∈ commV Y ⊓ fixV Y ⊔ tr (t : MulAut V) (cm W Y) := by
        intro y hy n hn
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hn
        rw [map_mul, ha.2 y hy]
        exact Subgroup.mul_mem_sup ha (hNinv t y hy b hb)
      rcases hsq.2 _ hSinv le_sup_left (sup_le inf_le_left (hNU t)) with h | h
      · exact le_sup_right.trans h.le
      · exact absurd h (hcon t)
    exact le_antisymm ((hUB.trans (iSup_le hall))) inf_le_left
  obtain ⟨t, ht⟩ := hex
  have hUN : commV Y ≤ tr (t : MulAut V) (cm W Y) := by
    refine hgen _ fun g hg u hu => ?_
    rw [← ht] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
    have e : g (a * b) * (a * b)⁻¹ = g b * b⁻¹ := by
      rw [map_mul, ha.2 g hg, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [e]
    exact mul_mem (hNinv t g hg b hb) (inv_mem hb)
  have hUW : commV Y ≤ tr (t : MulAut V) W := hUN.trans (tr_mono _ (cm_le_of_invariant hWY))
  have hWt : GInv (CGT6.conjClosure Y G) (tr (t : MulAut V) W) := by
    intro l hl a ha
    obtain ⟨w, hw, rfl⟩ := mem_tr.mp ha
    have htl := conj_inv_mem_conjClosure (Y := Y) (cfg.adm.hTG t.2) hl
    refine ⟨((t : MulAut V)⁻¹ * l * t) w, hW _ htl w hw, ?_⟩
    simp [MulAut.mul_apply]
  have hUne : commV Y ≠ ⊥ := fun h => hsq.1 (by rw [h]; simp)
  have hUL : GInv G (⨆ l : CGT6.conjClosure Y G, tr (l : MulAut V) (commV Y)) := by
    refine irr_ginv_of_cfg cfg (fun l hl a ha => ?_) (fun t' ht' a ha => ?_)
    · refine Subgroup.iSup_induction
        (fun l : CGT6.conjClosure Y G => tr (l : MulAut V) (commV Y))
        (C := fun a => l a ∈ ⨆ l : CGT6.conjClosure Y G, tr (l : MulAut V) (commV Y)) ha
        (fun l₁ b hb => ?_) (by simp)
        (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
      obtain ⟨u, hu, rfl⟩ := mem_tr.mp hb
      have e : l ((l₁ : MulAut V) u) = ((l * l₁ : MulAut V)) u := by simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.mem_iSup_of_mem
        (⟨l * l₁, (CGT6.conjClosure Y G).mul_mem hl l₁.2⟩ : CGT6.conjClosure Y G)
        (apply_mem_tr hu)
    · refine Subgroup.iSup_induction
        (fun l : CGT6.conjClosure Y G => tr (l : MulAut V) (commV Y))
        (C := fun a => t' a ∈ ⨆ l : CGT6.conjClosure Y G, tr (l : MulAut V) (commV Y)) ha
        (fun l₁ b hb => ?_) (by simp)
        (fun x y hx hy => by rw [map_mul]; exact mul_mem hx hy)
      obtain ⟨u, hu, rfl⟩ := mem_tr.mp hb
      have htl := conj_mem_conjClosure (Y := Y) (cfg.adm.hTG ht') l₁.2
      have e : t' ((l₁ : MulAut V) u) = (t' * l₁ * t'⁻¹) (t' u) := by simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.mem_iSup_of_mem
        (⟨t' * l₁ * t'⁻¹, htl⟩ : CGT6.conjClosure Y G)
        (apply_mem_tr (apply_mem_commV_of_comm (fun y hy => cfg_comm_ty cfg ht' hy) hu))
  have hULtop : (⨆ l : CGT6.conjClosure Y G, tr (l : MulAut V) (commV Y)) = ⊤ := by
    rcases cfg.irr _ hUL with h | h
    · exfalso
      refine hUne (eq_bot_iff.mpr fun u hu => ?_)
      have h1 : u ∈ ⨆ l : CGT6.conjClosure Y G, tr (l : MulAut V) (commV Y) :=
        Subgroup.mem_iSup_of_mem (⟨1, (CGT6.conjClosure Y G).one_mem⟩ : CGT6.conjClosure Y G)
          ⟨u, hu, by simp⟩
      rw [h] at h1
      exact h1
    · exact h
  have htW : tr (t : MulAut V) W = ⊤ := by
    rw [eq_top_iff, ← hULtop]
    refine iSup_le fun l => ?_
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_tr.mp ha
    exact hWt l l.2 _ (hUW hu)
  rw [eq_top_iff]
  intro v _
  have hv : (t : MulAut V) v ∈ tr (t : MulAut V) W := by rw [htW]; exact Subgroup.mem_top _
  obtain ⟨w, hw, hwv⟩ := hv
  have : w = v := (t : MulAut V).injective hwv
  rw [← this]
  exact hw

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End3
