module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.AS81.OstromWagner

open CFSG.Fischer Equiv

@[expose] def val : Option F4 → F4 × F4 → F4
  | none, p => p.1
  | some l, p => l * p.1 + p.2

@[expose] def lineSet (L : Option F4 × F4) : Set (F4 × F4) := {p | val L.1 p = L.2}

@[expose] def agLines : Set (Set (F4 × F4)) := Set.range lineSet

theorem mem_lineSet {L : Option F4 × F4} {p : F4 × F4} : p ∈ lineSet L ↔ val L.1 p = L.2 :=
  Iff.rfl

theorem val_add : ∀ (s : Option F4) (p q : F4 × F4), val s (p + q) = val s p + val s q := by
  decide

theorem val_smul : ∀ (s : Option F4) (l : F4) (p : F4 × F4), val s (l • p) = l * val s p := by
  decide

theorem eq_of_val_eq_val : ∀ s s' : Option F4, s ≠ s' → ∀ p q : F4 × F4, val s p = val s q →
    val s' p = val s' q → p = q := by
  decide

theorem exists_val_eq_val : ∀ s s' : Option F4, s ≠ s' → ∀ c c' : F4,
    ∃ p : F4 × F4, val s p = c ∧ val s' p = c' := by
  decide

theorem exists_val_eq : ∀ (s : Option F4) (c : F4), ∃ p : F4 × F4, val s p = c := by
  decide

theorem lineSet_injective : Function.Injective lineSet := by
  have key : ∀ L L' : Option F4 × F4, (∀ p, val L.1 p = L.2 ↔ val L'.1 p = L'.2) → L = L' := by
    decide
  intro L L' h
  exact key L L' fun p => Set.ext_iff.1 h p

theorem eq_or_disjoint (s : Option F4) (c c' : F4) :
    lineSet (s, c) = lineSet (s, c') ∨ Disjoint (lineSet (s, c)) (lineSet (s, c')) := by
  by_cases h : c = c'
  · exact Or.inl (h ▸ rfl)
  · exact Or.inr (Set.disjoint_left.2 fun p hp hp' => h (hp.symm.trans hp'))

theorem slope_eq {L L' : Option F4 × F4}
    (h : lineSet L = lineSet L' ∨ Disjoint (lineSet L) (lineSet L')) : L.1 = L'.1 := by
  by_contra hne
  obtain ⟨p, hp, hp'⟩ := exists_val_eq_val L.1 L'.1 hne L.2 L'.2
  rcases h with h | h
  · exact hne (congrArg Prod.fst (lineSet_injective h))
  · exact Set.disjoint_left.1 h hp hp'

@[expose] def coll : Subgroup (Perm (F4 × F4)) where
  carrier := {g | ∀ ℓ ∈ agLines, (g : F4 × F4 → F4 × F4) '' ℓ ∈ agLines ∧
    ((g⁻¹ : Perm (F4 × F4)) : F4 × F4 → F4 × F4) '' ℓ ∈ agLines}
  mul_mem' {g h} hg hh ℓ hℓ := by
    refine ⟨?_, ?_⟩
    · rw [Perm.coe_mul, Set.image_comp]
      exact (hg _ (hh ℓ hℓ).1).1
    · rw [mul_inv_rev, Perm.coe_mul, Set.image_comp]
      exact (hh _ (hg ℓ hℓ).2).2
  one_mem' ℓ hℓ := by
    rw [inv_one, Perm.coe_one, Set.image_id]
    exact ⟨hℓ, hℓ⟩
  inv_mem' {g} hg ℓ hℓ := by
    rw [inv_inv]
    exact ⟨(hg ℓ hℓ).2, (hg ℓ hℓ).1⟩

theorem mem_coll {g : Perm (F4 × F4)} : g ∈ coll ↔ ∀ ℓ ∈ agLines,
    (g : F4 × F4 → F4 × F4) '' ℓ ∈ agLines ∧
      ((g⁻¹ : Perm (F4 × F4)) : F4 × F4 → F4 × F4) '' ℓ ∈ agLines :=
  Iff.rfl

@[expose] noncomputable def imgCode (g : Perm (F4 × F4)) (L : Option F4 × F4) : Option F4 × F4 :=
  if h : ∃ L', lineSet L' = (g : F4 × F4 → F4 × F4) '' lineSet L then h.choose else L

theorem lineSet_imgCode {g : Perm (F4 × F4)} (hg : g ∈ coll) (L : Option F4 × F4) :
    lineSet (imgCode g L) = (g : F4 × F4 → F4 × F4) '' lineSet L := by
  have h : ∃ L', lineSet L' = (g : F4 × F4 → F4 × F4) '' lineSet L := (hg _ ⟨L, rfl⟩).1
  rw [imgCode, dite_eq_left h]
  exact h.choose_spec

theorem slope_imgCode {g : Perm (F4 × F4)} (hg : g ∈ coll) (s : Option F4) (c c' : F4) :
    (imgCode g (s, c)).1 = (imgCode g (s, c')).1 := by
  apply slope_eq
  rw [lineSet_imgCode hg, lineSet_imgCode hg]
  rcases eq_or_disjoint s c c' with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr ((Set.disjoint_image_iff g.injective).2 h)

theorem imgCode_mul {g h : Perm (F4 × F4)} (hg : g ∈ coll) (hh : h ∈ coll)
    (L : Option F4 × F4) : imgCode (g * h) L = imgCode g (imgCode h L) := by
  apply lineSet_injective
  rw [lineSet_imgCode (mul_mem hg hh), lineSet_imgCode hg, lineSet_imgCode hh, Perm.coe_mul,
    Set.image_comp]

theorem imgCode_one (L : Option F4 × F4) : imgCode 1 L = L := by
  apply lineSet_injective
  rw [lineSet_imgCode (one_mem _), Perm.coe_one, Set.image_id]

@[expose] noncomputable def slopeMap (g : Perm (F4 × F4)) (s : Option F4) : Option F4 :=
  (imgCode g (s, 0)).1

theorem slopeMap_mul {g h : Perm (F4 × F4)} (hg : g ∈ coll) (hh : h ∈ coll) (s : Option F4) :
    slopeMap (g * h) s = slopeMap g (slopeMap h s) := by
  rw [slopeMap, slopeMap, slopeMap, imgCode_mul hg hh]
  exact slope_imgCode hg _ _ _

theorem slopeMap_one (s : Option F4) : slopeMap 1 s = s := by
  rw [slopeMap, imgCode_one]

@[expose] noncomputable def slopePerm : coll →* Perm (Option F4) where
  toFun g :=
    { toFun := slopeMap g
      invFun := slopeMap (g⁻¹ : Perm (F4 × F4))
      left_inv := fun s => by
        rw [← slopeMap_mul (inv_mem g.2) g.2, inv_mul_cancel, slopeMap_one]
      right_inv := fun s => by
        rw [← slopeMap_mul g.2 (inv_mem g.2), mul_inv_cancel, slopeMap_one] }
  map_one' := Perm.ext fun s => slopeMap_one s
  map_mul' g h := Perm.ext fun s => slopeMap_mul g.2 h.2 s

theorem slopePerm_apply (g : coll) (s : Option F4) : slopePerm g s = slopeMap g s := rfl

theorem val_eq_val_of_slopePerm_eq_one {g : coll} (hg : slopePerm g = 1) (s : Option F4)
    {p q : F4 × F4} (hpq : val s p = val s q) :
    val s ((g : Perm (F4 × F4)) p) = val s ((g : Perm (F4 × F4)) q) := by
  have hs : (imgCode g (s, val s p)).1 = s := by
    rw [slope_imgCode g.2 s (val s p) 0]
    exact congrArg (fun σ : Perm (Option F4) => σ s) hg
  have h := lineSet_imgCode g.2 (s, val s p)
  have hp : (g : Perm (F4 × F4)) p ∈ lineSet (imgCode g (s, val s p)) := h ▸ ⟨p, rfl, rfl⟩
  have hq : (g : Perm (F4 × F4)) q ∈ lineSet (imgCode g (s, val s p)) := h ▸ ⟨q, hpq.symm, rfl⟩
  rw [mem_lineSet, hs] at hp hq
  exact hp.trans hq.symm

theorem F4_cases : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by
  decide

theorem eq_mul_of_additive {A : F4 → F4} (hadd : ∀ x y, A (x + y) = A x + A y)
    (hω : ∀ x, A (F4.ω * x) = F4.ω * A x) (x : F4) : A x = A 1 * x := by
  have h0 : A 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have key : ∀ a : F4, a = a + a → a = 0 := by decide
    exact key _ h
  have hω1 : A F4.ω = F4.ω * A 1 := by simpa only [mul_one] using hω 1
  rcases F4_cases x with rfl | rfl | rfl | rfl
  · rw [h0, mul_zero]
  · rw [mul_one]
  · rw [hω1, mul_comm]
  · rw [hω, hω1]
    ring

theorem exists_eq_smul_add_of_val {f : F4 × F4 → F4 × F4} (hf : Function.Injective f)
    (hv : ∀ s p q, val s p = val s q → val s (f p) = val s (f q)) :
    ∃ l : F4, l ≠ 0 ∧ ∀ p, f p = l • p + f 0 := by
  have h1 : ∀ x y : F4, (f (x, y)).1 = (f (x, 0)).1 := fun x y => hv none (x, y) (x, 0) rfl
  have h2 : ∀ x y : F4, (f (x, y)).2 = (f (0, y)).2 := fun x y => by
    simpa [val] using hv (some 0) (x, y) (0, y) (by simp [val])
  have h3 : ∀ x y : F4, (f (x, 0)).1 + (f (0, y)).2 = (f (0, 0)).1 + (f (0, x + y)).2 := by
    intro x y
    have h := hv (some 1) (x, y) (0, x + y) (by simp [val])
    simp only [val, one_mul] at h
    rwa [h1 x y, h2 x y, h1 0 (x + y)] at h
  have h4 : ∀ x : F4, F4.ω * (f (x, 0)).1 + (f (0, 0)).2 =
      F4.ω * (f (0, 0)).1 + (f (0, F4.ω * x)).2 := by
    intro x
    have h := hv (some F4.ω) (x, 0) (0, F4.ω * x) (by simp [val])
    simp only [val] at h
    rwa [h2 x 0, h1 0 (F4.ω * x)] at h
  obtain ⟨A, hA⟩ : ∃ A : F4 → F4, ∀ x, A x = (f (x, 0)).1 + (f (0, 0)).1 := ⟨_, fun _ => rfl⟩
  have hβ : ∀ y : F4, (f (0, y)).2 = A y + (f (0, 0)).2 := by
    intro y
    have h := h3 y 0
    rw [add_zero] at h
    have key : ∀ a b c d e : F4, a + b = c + d → e = a + c → d = e + b := by decide
    exact key _ _ _ _ _ h (hA y)
  have hadd : ∀ x y, A (x + y) = A x + A y := by
    intro x y
    have h := h3 x y
    rw [hβ y, hβ (x + y), ← add_assoc, ← add_assoc, add_left_inj] at h
    have key : ∀ a b c d e : F4, a + b = c + d → e = a + c → d = e + b := by decide
    exact key _ _ _ _ _ h (hA x)
  have hω : ∀ x, A (F4.ω * x) = F4.ω * A x := by
    intro x
    have h := h4 x
    rw [hβ (F4.ω * x), ← add_assoc, add_left_inj] at h
    have key : ∀ a c d e : F4, F4.ω * a = F4.ω * c + d → e = a + c → d = F4.ω * e := by decide
    exact key _ _ _ _ h (hA x)
  have hlin := eq_mul_of_additive hadd hω
  have key : ∀ a b c : F4, a = b + c → b = a + c := by decide
  refine ⟨A 1, fun h0 => ?_, fun p => Prod.ext ?_ ?_⟩
  · have hf10 : f (1, 0) = f (0, 0) := by
      refine Prod.ext ?_ ?_
      · rw [key _ _ _ (hA 1), h0, zero_add]
      · rw [h2 1 0]
    exact absurd (hf (hf10)) (by decide)
  · rw [← Prod.mk.eta (p := p), h1, key _ _ _ (hA p.1), hlin]
    rfl
  · rw [← Prod.mk.eta (p := p), h2, hβ, hlin]
    rfl

theorem exists_eq_smul_add {g : coll} (hg : slopePerm g = 1) :
    ∃ l : F4, l ≠ 0 ∧ ∀ p, (g : Perm (F4 × F4)) p = l • p + (g : Perm (F4 × F4)) 0 :=
  exists_eq_smul_add_of_val (g : Perm (F4 × F4)).injective fun s _ _ h =>
    val_eq_val_of_slopePerm_eq_one hg s h

@[expose] def transGroup : Subgroup (Perm (F4 × F4)) where
  carrier := Set.range Equiv.addRight
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨w + v, Equiv.ext fun p => (add_assoc p w v).symm⟩
  one_mem' := ⟨0, Equiv.ext fun p => add_zero p⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨-v, Equiv.ext fun p => rfl⟩

theorem mem_transGroup {t : Perm (F4 × F4)} : t ∈ transGroup ↔ ∃ v, Equiv.addRight v = t :=
  Iff.rfl

theorem addRight_apply' (v p : F4 × F4) : Equiv.addRight v p = p + v := rfl

theorem perm_apply_inv (f : Perm (F4 × F4)) (p : F4 × F4) : f (f⁻¹ p) = p :=
  f.apply_symm_apply p

theorem perm_inv_apply (f : Perm (F4 × F4)) (p : F4 × F4) : f⁻¹ (f p) = p :=
  f.symm_apply_apply p

theorem neg_eq_self : ∀ v : F4 × F4, -v = v := by
  decide

theorem image_addRight_lineSet (v : F4 × F4) (L : Option F4 × F4) :
    (Equiv.addRight v : F4 × F4 → F4 × F4) '' lineSet L = lineSet (L.1, L.2 + val L.1 v) := by
  ext q
  rw [Equiv.image_eq_preimage_symm]
  simp only [Set.mem_preimage, Equiv.coe_addRight, Equiv.addRight_symm, mem_lineSet]
  rw [val_add, neg_eq_self]
  constructor
  · intro h
    rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · intro h
    rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem addRight_mem_coll (v : F4 × F4) : Equiv.addRight v ∈ coll := by
  rintro _ ⟨L, rfl⟩
  refine ⟨⟨_, (image_addRight_lineSet v L).symm⟩, ?_⟩
  rw [Perm.inv_def, Equiv.addRight_symm]
  exact ⟨_, (image_addRight_lineSet (-v) L).symm⟩

theorem slopePerm_addRight (v : F4 × F4) :
    slopePerm ⟨Equiv.addRight v, addRight_mem_coll v⟩ = 1 := by
  refine Perm.ext fun s => ?_
  rw [slopePerm_apply, Perm.one_apply, slopeMap]
  have h := lineSet_imgCode (addRight_mem_coll v) (s, 0)
  rw [image_addRight_lineSet] at h
  exact congrArg Prod.fst (lineSet_injective h)

theorem fixed_smul_add : ∀ l : F4, l ≠ 1 → ∀ u : F4 × F4,
    l • ((l + 1)⁻¹ • u) + u = (l + 1)⁻¹ • u := by
  decide

theorem conj_mem_transGroup {g : Perm (F4 × F4)} (hg : g ∈ coll) {t : Perm (F4 × F4)}
    (ht : t ∈ transGroup) : g * t * g⁻¹ ∈ transGroup := by
  obtain ⟨v, rfl⟩ := ht
  set k : coll := ⟨g, hg⟩ * ⟨Equiv.addRight v, addRight_mem_coll v⟩ * ⟨g, hg⟩⁻¹ with hk
  have hk1 : slopePerm k = 1 := by
    rw [hk, map_mul, map_mul, slopePerm_addRight, mul_one, map_inv, mul_inv_cancel]
  have hkc : (k : Perm (F4 × F4)) = g * Equiv.addRight v * g⁻¹ := rfl
  obtain ⟨l, -, hl⟩ := exists_eq_smul_add hk1
  rw [← hkc]
  by_cases hv : v = 0
  · refine ⟨0, Equiv.ext fun p => ?_⟩
    rw [hkc, hv, Perm.mul_apply, Perm.mul_apply, addRight_apply', addRight_apply', add_zero,
      add_zero, perm_apply_inv]
  have hfix : ∀ p, (k : Perm (F4 × F4)) p ≠ p := by
    intro p hp
    rw [hkc, Perm.mul_apply, Perm.mul_apply, ← Perm.eq_inv_iff_eq, addRight_apply'] at hp
    exact hv (by simpa using hp)
  have hl1 : l = 1 := by
    by_contra hl1
    exact hfix ((l + 1)⁻¹ • (k : Perm (F4 × F4)) 0) (by rw [hl]; exact fixed_smul_add l hl1 _)
  refine ⟨(k : Perm (F4 × F4)) 0, Equiv.ext fun p => ?_⟩
  rw [hl p, hl1, one_smul, addRight_apply']

theorem addRight_injective : Function.Injective (Equiv.addRight : F4 × F4 → Perm (F4 × F4)) :=
  fun v w h => by simpa using congrArg (fun t : Perm (F4 × F4) => t 0) h

theorem card_transGroup : Nat.card transGroup = 16 := by
  have h : Nat.card transGroup = Nat.card (F4 × F4) :=
    (Nat.card_congr (Equiv.ofInjective _ addRight_injective)).symm
  rw [h, Nat.card_eq_fintype_card, Fintype.card_prod, F4.card]

theorem add_self_eq_zero' : ∀ v : F4 × F4, v + v = 0 := by
  decide

theorem transGroup_comm {s t : Perm (F4 × F4)} (hs : s ∈ transGroup) (ht : t ∈ transGroup) :
    s * t = t * s := by
  obtain ⟨v, rfl⟩ := hs
  obtain ⟨w, rfl⟩ := ht
  refine Equiv.ext fun p => ?_
  rw [Perm.mul_apply, Perm.mul_apply, addRight_apply', addRight_apply', addRight_apply',
    addRight_apply']
  exact add_right_comm p w v

theorem transGroup_sq {t : Perm (F4 × F4)} (ht : t ∈ transGroup) : t ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := ht
  refine Equiv.ext fun p => ?_
  rw [sq, Perm.mul_apply, addRight_apply', addRight_apply', add_assoc, add_self_eq_zero',
    add_zero, Perm.one_apply]

theorem exists_transGroup_apply_eq (p q : F4 × F4) : ∃ t ∈ transGroup, t p = q :=
  ⟨Equiv.addRight (q - p), ⟨_, rfl⟩, by rw [addRight_apply', add_sub_cancel]⟩

theorem pow_three_smul_add : ∀ l : F4, l ≠ 0 → l ≠ 1 → ∀ p u : F4 × F4,
    l • (l • (l • p + u) + u) + u = p := by
  decide

theorem transGroup_le {G : Subgroup (Perm (F4 × F4))} (hG : G ≤ coll)
    (h2 : ∀ p₁ p₂ q₁ q₂ : F4 × F4, p₁ ≠ p₂ → q₁ ≠ q₂ → ∃ g ∈ G, g p₁ = q₁ ∧ g p₂ = q₂) :
    transGroup ≤ G := by
  have h16 : 2 ^ 4 ∣ Nat.card G := by
    have horb : MulAction.orbit G (0 : F4 × F4) = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ?_
      by_cases hq : q = 0
      · exact ⟨1, by simp [hq]⟩
      obtain ⟨g, hg, hg1, -⟩ := h2 0 q q 0 (Ne.symm hq) hq
      exact ⟨⟨g, hg⟩, hg1⟩
    have h := (MulAction.stabilizer G (0 : F4 × F4)).index_mul_card
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_prod, F4.card] at h
    exact ⟨_, h.symm⟩
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16
  set ψ : G →* Perm (Option F4) := slopePerm.comp (Subgroup.inclusion hG) with hψ
  have hR : Nat.card (S.map ψ) ≤ 8 := by
    have h1 : Nat.card (S.map ψ) ∣ 16 := by
      have h := Subgroup.card_map_dvd S ψ
      rwa [hS] at h
    have h120 : Nat.card (Perm (Option F4)) = 120 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_option, F4.card]
      rfl
    have h2 : Nat.card (S.map ψ) ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card (S.map ψ)
    exact Nat.le_of_dvd (by norm_num) (Nat.dvd_gcd h1 h2)
  obtain ⟨x, y, hψxy, hxy⟩ : ∃ x y : S, ψ x = ψ y ∧ x ≠ y := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective
        (fun s : S => (⟨ψ s, Subgroup.mem_map_of_mem ψ s.2⟩ : S.map ψ)) :=
      fun x y h => hcon x y (congrArg Subtype.val h)
    have h := Nat.card_le_card_of_injective _ hinj
    rw [hS] at h
    omega
  set δ : S := x * y⁻¹ with hδ
  have hδ1 : δ ≠ 1 := fun h => hxy (mul_inv_eq_one.1 h)
  have hψδ : slopePerm ⟨((δ : G) : Perm (F4 × F4)), hG (δ : G).2⟩ = 1 := by
    have : ψ δ = 1 := by
      rw [hδ, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hψxy, mul_inv_cancel]
    exact this
  obtain ⟨l, hl0, hl⟩ := exists_eq_smul_add hψδ
  have hδp : ∀ p, ((δ : G) : Perm (F4 × F4)) p = l • p + ((δ : G) : Perm (F4 × F4)) 0 := hl
  have hl1 : l = 1 := by
    by_contra hl1
    apply hδ1
    have h3 : δ ^ 3 = 1 := by
      refine Subtype.ext (Subtype.ext (Equiv.ext fun p => ?_))
      simp only [SubgroupClass.coe_pow, Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
        Function.comp_apply, id_eq, Subgroup.coe_one, Perm.one_apply]
      rw [hδp, hδp, hδp]
      exact pow_three_smul_add l hl0 hl1 p _
    have h16' : δ ^ 2 ^ 4 = 1 := hS ▸ pow_card_eq_one'
    have hord : orderOf δ ∣ Nat.gcd 3 (2 ^ 4) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h16')
    rwa [show Nat.gcd 3 (2 ^ 4) = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at hord
  set u := ((δ : G) : Perm (F4 × F4)) 0 with hu
  have hδu : ((δ : G) : Perm (F4 × F4)) = Equiv.addRight u :=
    Equiv.ext fun p => by rw [hδp, hl1, one_smul, Equiv.coe_addRight]
  have hu0 : u ≠ 0 := by
    intro h
    apply hδ1
    refine Subtype.ext (Subtype.ext ?_)
    rw [hδu, h]
    exact Equiv.ext fun p => add_zero p
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = 0
  · rw [hw]
    exact (show Equiv.addRight (0 : F4 × F4) = 1 from Equiv.ext fun p => add_zero p) ▸ G.one_mem
  obtain ⟨g, hg, hg0, hgu⟩ := h2 0 u 0 w (Ne.symm hu0) (Ne.symm hw)
  have hmem : g * Equiv.addRight u * g⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem hg (hδu ▸ (δ : G).2)) (G.inv_mem hg)
  obtain ⟨w', hw'⟩ := conj_mem_transGroup (hG hg) (⟨u, rfl⟩ : Equiv.addRight u ∈ transGroup)
  have hw'w : w' = w := by
    have h := congrArg (fun t : Perm (F4 × F4) => t 0) hw'
    simp only [Equiv.coe_addRight, zero_add, Perm.mul_apply] at h
    rw [h, ← hg0, perm_inv_apply, zero_add, hgu]
  rw [← hw'w, hw']
  exact hmem

theorem le_normalizer_transGroup {G : Subgroup (Perm (F4 × F4))} (hG : G ≤ coll) :
    G ≤ Subgroup.normalizer (transGroup : Set (Perm (F4 × F4))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨conj_mem_transGroup (hG hg), fun ht => ?_⟩
  have h := conj_mem_transGroup (hG (G.inv_mem hg)) ht
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at h

end CFSG.ComponentClassification.AS81.OstromWagner
