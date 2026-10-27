module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {n : ℕ} {s : Setoid (Fin n)}

private structure Good (s : Setoid (Fin n)) (F : Fin n → Prop) : Prop where
  quad : ∀ x, ¬ F x → Nat.card {y // s.r x y} = 4
  inv : ∀ h ∈ partStab s, ∀ x, F (h x) ↔ F x

variable {F : Fin n → Prop}

private theorem exists_partner {x : Fin n} (h : Nat.card {y // s.r x y} = 2) :
    ∃ x', x' ≠ x ∧ s.r x x' ∧ ∀ y, s.r x y → y = x ∨ y = x' := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (⟨x, s.iseqv.refl x⟩ : {y // s.r x y})).1 h
  refine ⟨y.1, fun h => hy (Subtype.ext h), y.2, fun w hw => ?_⟩
  by_cases hwx : w = x
  · exact Or.inl hwx
  · exact Or.inr (congrArg Subtype.val (huniq ⟨w, hw⟩ fun h => hwx (congrArg Subtype.val h)))

private theorem exists_quad {x : Fin n} (h : Nat.card {y // s.r x y} = 4) :
    ∃ y c d, x ≠ y ∧ x ≠ c ∧ x ≠ d ∧ y ≠ c ∧ y ≠ d ∧ c ≠ d ∧ s.r x y ∧ s.r x c ∧ s.r x d := by
  classical
  have h1 : (Finset.univ.filter (s.r x)).card = 4 := by
    rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hx : x ∈ Finset.univ.filter (s.r x) := by simp
  have h2 : ((Finset.univ.filter (s.r x)).erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hx, h1]
  obtain ⟨y, c, d, hyc, hyd, hcd, he⟩ := Finset.card_eq_three.1 h2
  have hmem : ∀ w, w ∈ ({y, c, d} : Finset (Fin n)) → x ≠ w ∧ s.r x w := fun w hw => by
    rw [← he] at hw
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨hw.1.symm, hw.2⟩
  obtain ⟨hxy, ry⟩ := hmem y (by simp)
  obtain ⟨hxc, rc⟩ := hmem c (by simp)
  obtain ⟨hxd, rd⟩ := hmem d (by simp)
  exact ⟨y, c, d, hxy, hxc, hxd, hyc, hyd, hcd, ry, rc, rd⟩

private theorem mem_four {a b c d w : Fin n} (h : Nat.card {y // s.r a y} = 4) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (rb : s.r a b)
    (rc : s.r a c) (rd : s.r a d) (hw : s.r a w) : w = a ∨ w = b ∨ w = c ∨ w = d := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hwa, hwb, hwc, hwd⟩ := hcon
  have hsub : ({a, b, c, d, w} : Finset (Fin n)) ⊆ Finset.univ.filter (s.r a) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with rfl | rfl | rfl | rfl | rfl
    exacts [s.iseqv.refl _, rb, rc, rd, hw]
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.filter (s.r a)).card = 4 := by
    rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h3 : ({a, b, c, d, w} : Finset (Fin n)).card = 5 := by
    have : [a, b, c, d, w].Nodup := by simp [*, Ne.symm]
    simpa using List.toFinset_card_of_nodup this
  omega

private theorem rel_swap {a a' : Fin n} (h : s.r a a') (w : Fin n) : s.r (swap a a' w) w := by
  by_cases h1 : w = a
  · rw [h1, swap_apply_left]; exact s.iseqv.symm h
  · by_cases h2 : w = a'
    · rw [h2, swap_apply_right]; exact h
    · rw [swap_apply_of_ne_of_ne h1 h2]

private theorem rel_congr {a a' b b' : Fin n} (ha : s.r a a') (hb : s.r b b') :
    s.r a b ↔ s.r a' b' :=
  ⟨fun h => s.iseqv.trans (s.iseqv.trans (s.iseqv.symm ha) h) hb,
    fun h => s.iseqv.trans (s.iseqv.trans ha h) (s.iseqv.symm hb)⟩

private theorem dt_apply {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a b * swap c d) a = b ∧ (swap a b * swap c d) b = a ∧ (swap a b * swap c d) c = d ∧
      (swap a b * swap c d) d = c ∧
      ∀ w, w ≠ a → w ≠ b → w ≠ c → w ≠ d → (swap a b * swap c d) w = w := by
  simp only [Perm.mul_apply, swap_apply_def]
  refine ⟨?_, ?_, ?_, ?_, fun w h1 h2 h3 h4 => ?_⟩ <;> grind

private theorem sq_of_tables {σ : Perm (Fin n)} {a b c d : Fin n} (σa : σ a = b) (σb : σ b = a)
    (σc : σ c = d) (σd : σ d = c) (σf : ∀ w, w ≠ a → w ≠ b → w ≠ c → w ≠ d → σ w = w) :
    σ * σ = 1 := by
  refine Perm.ext fun y => ?_
  rw [Perm.mul_apply, Perm.one_apply]
  grind

private theorem comm_of_tables {σ τ : Perm (Fin n)} {a b c d p q r t : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hpq : p ≠ q)
    (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t)
    (ha : a = p ∨ a = q ∨ a = r ∨ a = t) (hb : b = p ∨ b = q ∨ b = r ∨ b = t)
    (hc : c = p ∨ c = q ∨ c = r ∨ c = t) (hd : d = p ∨ d = q ∨ d = r ∨ d = t)
    (σa : σ a = b) (σb : σ b = a) (σc : σ c = d) (σd : σ d = c)
    (σf : ∀ w, w ≠ a → w ≠ b → w ≠ c → w ≠ d → σ w = w)
    (τp : τ p = q) (τq : τ q = p) (τr : τ r = t) (τt : τ t = r)
    (τf : ∀ w, w ≠ p → w ≠ q → w ≠ r → w ≠ t → τ w = w) : σ * τ = τ * σ := by
  refine Perm.ext fun y => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  grind

private def Dt (s : Setoid (Fin n)) (F : Fin n → Prop) : Set (Perm (Fin n)) :=
  {g | ∃ a b c d, ¬ F a ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    s.r a b ∧ s.r a c ∧ s.r a d ∧ g = swap a b * swap c d}

private theorem Dt_sq {σ : Perm (Fin n)} (hσ : σ ∈ Dt s F) : σ * σ = 1 := by
  obtain ⟨a, b, c, d, -, hab, hac, had, hbc, hbd, hcd, -, -, -, rfl⟩ := hσ
  obtain ⟨σa, σb, σc, σd, σf⟩ := dt_apply hab hac had hbc hbd hcd
  exact sq_of_tables σa σb σc σd σf

private theorem rel_of_ne {a b c d y : Fin n} (rb : s.r a b) (rc : s.r a c) (rd : s.r a d)
    (hy : (swap a b * swap c d) y ≠ y) : s.r a y := by
  by_contra h
  refine hy ?_
  have h1 : y ≠ a := fun e => h (e ▸ s.iseqv.refl a)
  have h2 : y ≠ b := fun e => h (e ▸ rb)
  have h3 : y ≠ c := fun e => h (e ▸ rc)
  have h4 : y ≠ d := fun e => h (e ▸ rd)
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

private theorem Dt_comm (G : Good s F) {σ τ : Perm (Fin n)} (hσ : σ ∈ Dt s F)
    (hτ : τ ∈ Dt s F) : σ * τ = τ * σ := by
  obtain ⟨a, b, c, d, hFa, hab, hac, had, hbc, hbd, hcd, rb, rc, rd, rfl⟩ := hσ
  obtain ⟨p, q, r, t, hFp, hpq, hpr, hpt, hqr, hqt, hrt, rq, rr, rt, rfl⟩ := hτ
  by_cases hap : s.r a p
  · have e : ∀ w, s.r p w → w = p ∨ w = q ∨ w = r ∨ w = t := fun w h =>
      mem_four (G.quad p hFp) hpq hpr hpt hqr hqt hrt rq rr rt h
    have hpa := s.iseqv.symm hap
    obtain ⟨σa, σb, σc, σd, σf⟩ := dt_apply hab hac had hbc hbd hcd
    obtain ⟨τp, τq, τr, τt, τf⟩ := dt_apply hpq hpr hpt hqr hqt hrt
    exact comm_of_tables hab hac had hbc hbd hcd hpq hpr hpt hqr hqt hrt (e a hpa)
      (e b (s.iseqv.trans hpa rb)) (e c (s.iseqv.trans hpa rc)) (e d (s.iseqv.trans hpa rd))
      σa σb σc σd σf τp τq τr τt τf
  · refine Perm.Disjoint.commute fun y => ?_
    by_contra hcon
    rw [not_or] at hcon
    exact hap (s.iseqv.trans (rel_of_ne rb rc rd hcon.1)
      (s.iseqv.symm (rel_of_ne rq rr rt hcon.2)))

private abbrev Yp (s : Setoid (Fin n)) : Subgroup (Perm (Fin n)) :=
  partStab s ⊓ alternatingGroup (Fin n)

private theorem Dt_le {σ : Perm (Fin n)} (hσ : σ ∈ Dt s F) : σ ∈ Yp s := by
  obtain ⟨a, b, c, d, -, hab, -, -, -, -, hcd, rb, rc, rd, rfl⟩ := hσ
  have rcd : s.r c d := s.iseqv.trans (s.iseqv.symm rc) rd
  have hw : ∀ w, s.r ((swap a b * swap c d) w) w := fun w =>
    s.iseqv.trans (rel_swap rb _) (rel_swap rcd w)
  have hA : swap a b * swap c d ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hcd]
    decide
  exact ⟨fun x y => rel_congr (hw x) (hw y), hA⟩

private theorem Dt_conj (G : Good s F) {h σ : Perm (Fin n)} (hh : h ∈ partStab s)
    (hσ : σ ∈ Dt s F) : h * σ * h⁻¹ ∈ Dt s F := by
  obtain ⟨a, b, c, d, hFa, hab, hac, had, hbc, hbd, hcd, rb, rc, rd, rfl⟩ := hσ
  have e : h * (swap a b * swap c d) * h⁻¹ = swap (h a) (h b) * swap (h c) (h d) := by
    rw [swap_apply_apply, swap_apply_apply]
    group
  rw [e]
  exact ⟨h a, h b, h c, h d, fun hF => hFa ((G.inv h hh a).1 hF), h.injective.ne hab,
    h.injective.ne hac, h.injective.ne had, h.injective.ne hbc, h.injective.ne hbd,
    h.injective.ne hcd, (hh a b).2 rb, (hh a c).2 rc, (hh a d).2 rd, rfl⟩

private theorem closure_Dt_conj (G : Good s F) {h y : Perm (Fin n)} (hh : h ∈ partStab s)
    (hy : y ∈ closure (Dt s F)) : h * y * h⁻¹ ∈ closure (Dt s F) := by
  induction hy using Subgroup.closure_induction with
  | mem σ hσ => exact subset_closure (Dt_conj G hh hσ)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ by group]
    exact inv_mem ha

private theorem closure_Dt_sq (G : Good s F) {g : Perm (Fin n)} (hg : g ∈ closure (Dt s F)) :
    g * g = 1 := by
  have hc : ∀ x y, x ∈ closure (Dt s F) → y ∈ closure (Dt s F) → Commute x y := by
    intro x y hx hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · exact fun x y hx hy => Dt_comm G hx hy
    · exact fun x _ => Commute.one_left x
    · exact fun x _ => Commute.one_right x
    · exact fun x y z _ _ _ h1 h2 => h1.mul_left h2
    · exact fun y z x _ _ _ h1 h2 => h1.mul_right h2
    · exact fun x y _ _ h => h.inv_left
    · exact fun x y _ _ h => h.inv_right
  induction hg using Subgroup.closure_induction with
  | mem σ hσ => exact Dt_sq hσ
  | one => exact one_mul 1
  | mul a b ha hb iha ihb =>
    rw [← pow_two, (hc a b ha hb).mul_pow, pow_two, iha, pow_two, ihb, one_mul]
  | inv a _ ih => rw [← mul_inv_rev, ih, inv_one]

private theorem Dt_le_pCoreOf (G : Good s F) : Dt s F ⊆ pCoreOf 2 (Yp s) := by
  have hle : closure (Dt s F) ≤ Yp s := (closure_le _).2 fun _ h => Dt_le h
  refine fun σ hσ => CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hle
    (fun h hh y hy => closure_Dt_conj G hh.1 hy) ?_ (subset_closure hσ)
  intro g
  refine ⟨1, ?_⟩
  ext1
  simpa [pow_two] using closure_Dt_sq G g.2

private theorem apply_swap_of_comm {x : Perm (Fin n)} {a b c d : Fin n} (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hx : (swap a b * swap c d) * x = x * (swap a b * swap c d)) (hxa : x a = b) : x b = a := by
  have h := Perm.congr_fun hx a
  simp only [Perm.mul_apply] at h
  rw [swap_apply_of_ne_of_ne hac had, swap_apply_left, hxa, swap_apply_of_ne_of_ne hbc hbd,
    swap_apply_right] at h
  exact h.symm

private theorem mem_of_comm_swap {x : Perm (Fin n)} {z z' l l' : Fin n} (hzz : z ≠ z')
    (hzl : z ≠ l) (hzl' : z ≠ l')
    (hx : (swap z z' * swap l l') * x = x * (swap z z' * swap l l')) :
    x z = z ∨ x z = z' ∨ x z = l ∨ x z = l' := by
  have h2 := Perm.congr_fun hx z
  simp only [Perm.mul_apply] at h2
  rw [swap_apply_of_ne_of_ne hzl hzl', swap_apply_left] at h2
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨c1, c2, c3, c4⟩ := hcon
  rw [swap_apply_of_ne_of_ne c3 c4, swap_apply_of_ne_of_ne c1 c2] at h2
  exact hzz (x.injective h2)

private theorem apply_apply_of_comm (G : Good s F) {x : Perm (Fin n)}
    (hx : ∀ σ ∈ Dt s F, σ * x = x * σ) {z : Fin n} (hz : ¬ F z) : x (x z) = z := by
  obtain ⟨y, c, d, hzy, hzc, hzd, hyc, hyd, hcd, ry, rc, rd⟩ := exists_quad (G.quad z hz)
  have h1 := hx _ ⟨z, y, c, d, hz, hzy, hzc, hzd, hyc, hyd, hcd, ry, rc, rd, rfl⟩
  have h2 := hx _ ⟨z, c, y, d, hz, hzc, hzy, hzd, hyc.symm, hcd, hyd, rc, ry, rd, rfl⟩
  have h3 := hx _ ⟨z, d, y, c, hz, hzd, hzy, hzc, hyd.symm, hcd.symm, hyc, rd, ry, rc, rfl⟩
  rcases mem_of_comm_swap hzy hzc hzd h1 with h | h | h | h
  · rw [h, h]
  · rw [h]; exact apply_swap_of_comm hzc hzd hyc hyd h1 h
  · rw [h]; exact apply_swap_of_comm hzy hzd hyc.symm hcd h2 h
  · rw [h]; exact apply_swap_of_comm hzy hzc hyd.symm hcd.symm h3 h

private def Zq (s : Setoid (Fin n)) (F : Fin n → Prop) : Subgroup (Perm (Fin n)) :=
  Yp s ⊓ centralizer (Dt s F)

private theorem Zq_normal (G : Good s F) {h x : Perm (Fin n)} (hh : h ∈ Yp s) (hx : x ∈ Zq s F) :
    h * x * h⁻¹ ∈ Zq s F := by
  have h1 : h * x * h⁻¹ ∈ Yp s := mul_mem (mul_mem hh hx.1) (inv_mem hh)
  refine ⟨h1, mem_centralizer_iff.2 fun σ hσ => ?_⟩
  have hc := mem_centralizer_iff.1 hx.2 _ (Dt_conj G (inv_mem hh.1) hσ)
  calc σ * (h * x * h⁻¹) = h * ((h⁻¹ * σ * h⁻¹⁻¹) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * σ * h⁻¹⁻¹)) * h⁻¹ := by rw [hc]
    _ = (h * x * h⁻¹) * σ := by group

private theorem Zq_le_pCoreOf (G : Good s F) (hF : ∀ x ∈ partStab s, ∀ z, F z → x (x z) = z) :
    Zq s F ≤ pCoreOf 2 (Yp s) := by
  refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf inf_le_left
    (fun h hh y hy => Zq_normal G hh hy) ?_
  intro x
  refine ⟨1, ?_⟩
  ext1
  have hx := x.2
  have : (x : Perm (Fin n)) * x = 1 := Perm.ext fun w => by
    by_cases hw : F w
    · exact hF _ hx.1.1 w hw
    · exact apply_apply_of_comm G (fun σ hσ => mem_centralizer_iff.1 hx.2 σ hσ) hw
  simpa [pow_two] using this

private abbrev Cc (s : Setoid (Fin n)) : Subgroup (Perm (Fin n)) :=
  Yp s ⊓ centralizer (pCoreOf 2 (Yp s) : Set (Perm (Fin n)))

private theorem Cc_le_Zq (G : Good s F) : Cc s ≤ Zq s F := fun _ hx =>
  ⟨hx.1, mem_centralizer_iff.2 fun σ hσ => mem_centralizer_iff.1 hx.2 σ (Dt_le_pCoreOf G hσ)⟩

private theorem mem_Cc (G : Good s F) {x : Perm (Fin n)} (hx : x ∈ Cc s) :
    x ∈ partStab s ∧ x ∈ alternatingGroup (Fin n) ∧ ∀ z, ¬ F z → x (x z) = z :=
  ⟨hx.1.1, hx.1.2, fun _ hz => apply_apply_of_comm G (fun σ hσ =>
    mem_centralizer_iff.1 (Cc_le_Zq G hx).2 σ hσ) hz⟩

private theorem good_class {b : Fin n} {k : ℕ} (hk : k ≠ 4) (hb : Nat.card {y // s.r b y} = k)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) : Good s (s.r b) where
  quad := hs
  inv h hh x := by
    have hbh : s.r b (h b) := by
      by_contra hc
      exact hk (hb.symm.trans
        ((Nat.card_congr (Equiv.subtypeEquiv h fun y => (hh b y).symm)).trans (hs _ hc)))
    rw [← hh b x]
    exact ⟨fun hx => s.iseqv.trans (s.iseqv.symm hbh) hx, fun hx => s.iseqv.trans hbh hx⟩

private theorem apply_apply_of_two {b z : Fin n} {g : Perm (Fin n)}
    (hb : Nat.card {y // s.r b y} = 2) (h0 : s.r b z) (h1 : s.r b (g z))
    (h2 : s.r b (g (g z))) : g (g z) = z := by
  obtain ⟨b', hne, -, hcl⟩ := exists_partner hb
  have hinj : g (g z) = g z → g z = z := fun e => g.injective e
  have := hcl z h0
  have := hcl (g z) h1
  have := hcl (g (g z)) h2
  grind

theorem charTwo_partStab_inf_quads (hs : ∀ x, Nat.card {y // s.r x y} = 4) :
    CharTwo (partStab s ⊓ alternatingGroup (Fin n)) := by
  have G : Good s (fun _ => False) := ⟨fun x _ => hs x, fun _ _ _ => Iff.rfl⟩
  exact fun x hx => Zq_le_pCoreOf G (fun _ _ _ h => h.elim) (Cc_le_Zq G hx)

theorem charTwo_partStab_inf_quadsPair {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 2) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) :
    CharTwo (partStab s ⊓ alternatingGroup (Fin n)) := by
  have G := good_class (by omega : 2 ≠ 4) hb hs
  exact fun x hx => Zq_le_pCoreOf G (fun g hg z hz => apply_apply_of_two hb hz
    ((G.inv g hg z).2 hz) ((G.inv g hg (g z)).2 ((G.inv g hg z).2 hz))) (Cc_le_Zq G hx)

private theorem eq_one_of_fix {g : Perm (Fin n)} {u v : Fin n} (hs : sign g = 1)
    (hfix : ∀ w, w ≠ u → w ≠ v → g w = w) : g = 1 := by
  have hsub : g.support ⊆ {u, v} := fun w hw => by
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    exact Perm.mem_support.1 hw (hfix w hcon.1 hcon.2)
  have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
  rcases (by omega : g.support.card = 0 ∨ g.support.card = 1 ∨ g.support.card = 2) with h | h | h
  · exact Perm.card_support_eq_zero.1 h
  · exact absurd h (Perm.card_support_ne_one g)
  · have := (Perm.card_support_eq_two.1 h).sign_eq
    rw [hs] at this
    exact absurd this (by decide)

private theorem eq_one_of_fix3 {u v t : Fin n} {g : Perm (Fin n)} (hs : sign g = 1)
    (hu : g u = u) (hfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → g w = w) : g = 1 :=
  eq_one_of_fix (u := v) (v := t) hs fun w hv ht => by
    by_cases hw : w = u
    · rw [hw]; exact hu
    · exact hfix w hw hv ht

private theorem swap_mul_swap_apply {u v t w : Fin n} (h1 : w ≠ u) (h2 : w ≠ v) (h3 : w ≠ t) :
    (swap u v * swap u t) w = w := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]

private theorem mem_zpowers_of_fix {u v t : Fin n} (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t)
    {g : Perm (Fin n)} (hs : sign g = 1) (hfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → g w = w) :
    g ∈ zpowers (swap u v * swap u t) := by
  set z := swap u v * swap u t with hz
  have hzs : sign z = 1 := by rw [hz, map_mul, sign_swap huv, sign_swap hut]; decide
  have hzfix : ∀ w, w ≠ u → w ≠ v → w ≠ t → z w = w := fun w h1 h2 h3 =>
    swap_mul_swap_apply h1 h2 h3
  have hzu : z u = t := by
    rw [hz, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hut.symm hvt.symm]
  have hzv : z v = u := by
    rw [hz, Perm.mul_apply, swap_apply_of_ne_of_ne huv.symm hvt, swap_apply_right]
  have hgu : g u = u ∨ g u = v ∨ g u = t := by
    by_contra hcon
    simp only [not_or] at hcon
    exact hcon.1 (g.injective (hfix _ hcon.1 hcon.2.1 hcon.2.2 : g (g u) = g u))
  rcases hgu with h | h | h
  · rw [eq_one_of_fix3 hs h hfix]; exact one_mem _
  · have h1 : z * g = 1 := eq_one_of_fix3 (u := u) (v := v) (t := t)
      (by rw [map_mul, hs, hzs, mul_one]) (by rw [Perm.mul_apply, h, hzv])
      fun w a b c => by rw [Perm.mul_apply, hfix w a b c, hzfix w a b c]
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (mem_zpowers z)
  · have h1 : z⁻¹ * g = 1 := eq_one_of_fix3 (u := u) (v := v) (t := t)
      (by rw [map_mul, hs, sign_inv, hzs, mul_one])
      (by rw [Perm.mul_apply, h, Perm.inv_eq_iff_eq, hzu])
      fun w a b c => by
        rw [Perm.mul_apply, hfix w a b c, Perm.inv_eq_iff_eq, hzfix w a b c]
    rw [← inv_mul_eq_one.1 h1]
    exact mem_zpowers z

private theorem le_normalizer_inf {G : Type*} [Group G] {C A : Subgroup G}
    (h : ∀ c ∈ C, ∀ y ∈ A, c * y * c⁻¹ ∈ A) : C ≤ normalizer ((C ⊓ A : Subgroup G) : Set G) := by
  have key : ∀ c ∈ C, ∀ y ∈ C ⊓ A, c * y * c⁻¹ ∈ C ⊓ A := fun c hc y hy =>
    ⟨C.mul_mem (C.mul_mem hc hy.1) (C.inv_mem hc), h c hc y hy.2⟩
  intro c hc
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => key c hc y hy, fun hy => ?_⟩
  simpa [mul_assoc] using key c⁻¹ (inv_mem hc) _ hy

theorem twoResidual_le_partStab_inf_quadsTriple {b : Fin n}
    (hb : Nat.card {y // s.r b y} = 3) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) :
    ∃ z : Perm (Fin n), z.IsThreeCycle ∧
      twoResidual ((partStab s ⊓ alternatingGroup (Fin n)) ⊓
        centralizer (pCoreOf 2 (partStab s ⊓ alternatingGroup (Fin n)) : Set (Perm (Fin n)))) ≤
        zpowers z := by
  classical
  have G := good_class (by omega : 3 ≠ 4) hb hs
  obtain ⟨u, v, t, huv, hut, hvt, hΔ⟩ := Finset.card_eq_three.1
    (by rw [← hb, Nat.card_eq_fintype_card, Fintype.card_subtype] :
      (Finset.univ.filter (s.r b)).card = 3)
  have hout : ∀ w, ¬ s.r b w ↔ w ≠ u ∧ w ≠ v ∧ w ≠ t := fun w => by
    simpa [not_or] using not_congr (Finset.ext_iff.1 hΔ w)
  have hzA : swap u v * swap u t ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap huv, sign_swap hut]; decide
  refine ⟨swap u v * swap u t, isThreeCycle_swap_mul_swap_same huv hut hvt, ?_⟩
  refine (twoResidual_le_of_isTwoQuotient (N := Cc s ⊓ zpowers (swap u v * swap u t)) inf_le_left
    (le_normalizer_inf fun c hc y hy => ?_) fun x hx => ⟨1, ?_⟩).trans inf_le_right
  · obtain ⟨hcY, hcA, -⟩ := mem_Cc G hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow]
    refine zpow_mem (mem_zpowers_of_fix huv hut hvt (mem_alternatingGroup.1
      (mul_mem (mul_mem hcA hzA) (inv_mem hcA))) fun w h1 h2 h3 => ?_) k
    have hw := (hout _).1 fun h => (hout w).2 ⟨h1, h2, h3⟩ ((G.inv _ (inv_mem hcY) w).1 h)
    show c ((swap u v * swap u t) (c⁻¹ w)) = w
    rw [swap_mul_swap_apply hw.1 hw.2.1 hw.2.2]
    exact c.apply_symm_apply w
  · obtain ⟨-, hxA, hxr⟩ := mem_Cc G hx
    rw [show x ^ 2 ^ 1 = x * x by rw [pow_one, pow_two]]
    exact ⟨mul_mem hx hx, mem_zpowers_of_fix huv hut hvt (mem_alternatingGroup.1 (mul_mem hxA hxA))
      fun w h1 h2 h3 => hxr w ((hout w).2 ⟨h1, h2, h3⟩)⟩

end CFSG.GroupTheory.AltCore
