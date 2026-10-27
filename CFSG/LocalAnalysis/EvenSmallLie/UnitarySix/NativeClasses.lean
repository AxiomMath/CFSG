
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClassesBase

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModel
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Fischer
open CFSG.ComponentClassification.M12Cover
open scoped Pointwise

open Classical in
noncomputable def tpart
    (s : Equiv.Perm (Fin 693)) : Equiv.Perm (Fin 693) :=
  if h : ∃ b ∈ uT, s * b⁻¹ ∈ uA then h.choose else 1

theorem o1_mem :
    o1 ∈ T46 := u62W_mem _

theorem o2_mem :
    o2 ∈ T46 := u62W_mem _

theorem card_inter_le
    {X : Subgroup (Equiv.Perm (Fin 693))} {P : Equiv.Perm (Fin 693) → Prop}
    (hP : ∀ x, x ∈ X ∧ x ∈ uA → P x) :
    Nat.card {x // x ∈ X ∧ x ∈ uA} ≤ Nat.card {a : uA // P a} :=
  Nat.card_le_card_of_injective (fun x => ⟨⟨x.1, x.2.2⟩, hP x.1 x.2⟩) fun _ _ h =>
    Subtype.ext (congrArg (fun z : {a : uA // P a} => ((z.1 : uA) : Equiv.Perm (Fin 693))) h)

theorem orbit_facts :
    (∀ a ∈ uA, a ≠ 1 → a ∈ conjClass uK j1 ∨ a ∈ conjClass uK j2 ∨ a ∈ conjClass uK j3) ∧
      (conjClass uK j1).ncard = 21 ∧ (conjClass uK j2).ncard = 210 ∧
      (conjClass uK j3).ncard = 280 ∧
      orderOf j1 = 2 ∧ orderOf j2 = 2 ∧ orderOf j3 = 2 ∧
      {p : Fin 693 | j1 p = p}.ncard = 181 ∧ {p : Fin 693 | j2 p = p}.ncard = 53 ∧
      {p : Fin 693 | j3 p = p}.ncard = 21 := by
  rw [uA_eq, uK_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := orbit_check
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem uK_conj_mem
    {c : Equiv.Perm (Fin 693)} (hc : c ∈ uK) {h : Equiv.Perm (Fin 693)}
    (hh : h ∈ uA) : c * h * c⁻¹ ∈ uA :=
  (Subgroup.mem_normalizer_iff.1 (uK_le_normalizer hc) h).1 hh

theorem conjClass_facts
    {r : Equiv.Perm (Fin 693)} (hr : r ∈ uA) (hr1 : r ≠ 1) :
    ∀ x ∈ conjClass uK r, (x ∈ uA ∧ x ≠ 1) ∧
      {p : Fin 693 | x p = p}.ncard = {p : Fin 693 | r p = p}.ncard := by
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨⟨uK_conj_mem hc hr, fun h => hr1 ?_⟩, ncard_fixed_conj c r⟩
  have := congrArg (fun x => c⁻¹ * x * c) h
  simpa [mul_assoc] using this

theorem korbits :
    (∀ a ∈ uA, a ≠ 1 → a ∈ conjClass uK j1 ∨ a ∈ conjClass uK j2 ∨ a ∈ conjClass uK j3) ∧
      (conjClass uK j1).ncard = 21 ∧ (conjClass uK j2).ncard = 210 ∧
      (conjClass uK j3).ncard = 280 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := orbit_facts
  exact ⟨h1, h2, h3, h4⟩

theorem not_isConj_j
    : ¬ IsConj j1 j2 ∧ ¬ IsConj j1 j3 ∧ ¬ IsConj j2 j3 := by
  obtain ⟨-, -, -, -, -, -, -, hf1, hf2, hf3⟩ := orbit_facts
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := ncard_fixed_of_isConj h
    rw [hf1, hf2] at this
    exact absurd this (by norm_num)
  · have := ncard_fixed_of_isConj h
    rw [hf1, hf3] at this
    exact absurd this (by norm_num)
  · have := ncard_fixed_of_isConj h
    rw [hf2, hf3] at this
    exact absurd this (by norm_num)

theorem j1_ne_one
    : j1 ≠ 1 := fun h => by
  have := orbit_facts.2.2.2.2.1
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem card_uS_subgroupOf :
    Nat.card (uS.subgroupOf T46) = 32768 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe uS_le_T46).toEquiv, card_uS]

theorem index_uS :
    (uS.subgroupOf T46).index = 280665 := by
  have h := (uS.subgroupOf T46).card_mul_index
  rw [card_uS_subgroupOf, card_T46_eq] at h
  omega

theorem uS_isPGroup :
    IsPGroup 2 (uS.subgroupOf T46) :=
  IsPGroup.of_card (n := 15) (by rw [card_uS_subgroupOf]; norm_num)

theorem not_two_dvd_index_uS :
    ¬ 2 ∣ (uS.subgroupOf T46).index := by
  rw [index_uS]
  norm_num

theorem exists_conj_mem_uS
    {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) (ho : orderOf t = 2) :
    ∃ g ∈ T46, g * t * g⁻¹ ∈ uS := by
  obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.exists_conj_mem_of_sylow (uS.subgroupOf T46)
    uS_isPGroup not_two_dvd_index_uS (u := (⟨t, ht⟩ : T46))
    (by rw [Subgroup.orderOf_mk]; exact ho)
  exact ⟨c, c.2, by simpa using Subgroup.mem_subgroupOf.1 hc⟩

theorem sylow_facts :
    (∀ u ∈ uS, orderOf u = 2 → ∃ r ∈ sReps, ∃ c ∈ uS, u = c * r * c⁻¹) ∧
      (∀ r ∈ sReps, orderOf r = 2) ∧
      (∀ p ∈ List.zip sConjs sReps, p.1 * p.2 * p.1⁻¹ ∈ uA) ∧
      (∀ g ∈ sGens, j1 * g = g * j1) ∧
      (∀ x ∈ uS, (∀ g ∈ sGens, x * g = g * x) → x = 1 ∨ x = j1) ∧
      ∀ r ∈ sReps, ({p : Fin 693 | r p = p}.ncard = 53 → 2 ≤ (conjClass uS r).ncard) ∧
        ({p : Fin 693 | r p = p}.ncard = 21 → 8 ≤ (conjClass uS r).ncard) := by
  rw [uS_closure, uA_eq]
  exact sylow_check

theorem conj_into_uA
    {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) (ho : orderOf t = 2) :
    ∃ g ∈ T46, g * t * g⁻¹ ∈ uA := by
  obtain ⟨g, hg, hgS⟩ := exists_conj_mem_uS ht ho
  obtain ⟨h1, -, h3, -, -, -⟩ := sylow_facts
  have ho' : orderOf (g * t * g⁻¹) = 2 :=
    (MulEquiv.orderOf_eq (MulAut.conj g) t).trans ho
  obtain ⟨r, hr, c, hc, hcr⟩ := h1 _ hgS ho'
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
  have hlen : sConjs.length = sReps.length := by simp [sConjs, sReps, sConjWords, sRepWords]
  have hi' : i < sConjs.length := by rw [hlen]; exact hi
  have hpair : (sConjs[i]'hi', r) ∈ List.zip sConjs sReps := by
    rw [← hri, List.mem_iff_getElem]
    exact ⟨i, by simp [hlen, hi], by simp⟩
  have hd := h3 _ hpair
  set d := sConjs[i]'hi'
  have hdT : d ∈ T46 := by
    have hd' : d ∈ sConjs := List.getElem_mem _
    obtain ⟨w, -, hw⟩ := List.mem_map.1 hd'
    rw [← hw]
    exact u62W_mem w
  refine ⟨d * c⁻¹ * g, T46.mul_mem (T46.mul_mem hdT (T46.inv_mem (uS_le_T46 hc))) hg, ?_⟩
  have e : d * c⁻¹ * g * t * (d * c⁻¹ * g)⁻¹ = d * (c⁻¹ * (g * t * g⁻¹) * c) * d⁻¹ := by group
  rw [e, hcr]
  have e2 : c⁻¹ * (c * r * c⁻¹) * c = r := by group
  rw [e2]
  exact hd

theorem involution_classes
    {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) (ho : orderOf t = 2) :
    ∃ g ∈ T46, g * t * g⁻¹ = j1 ∨ g * t * g⁻¹ = j2 ∨ g * t * g⁻¹ = j3 := by
  obtain ⟨g, hg, hgA⟩ := conj_into_uA ht ho
  have hne : g * t * g⁻¹ ≠ 1 := fun h => by
    have h' : t = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using this
    rw [h', orderOf_one] at ho
    exact absurd ho (by norm_num)
  have key : ∀ j, g * t * g⁻¹ ∈ conjClass uK j → ∃ g' ∈ T46, g' * t * g'⁻¹ = j := by
    rintro j ⟨c, hc, hcj⟩
    refine ⟨c⁻¹ * g, T46.mul_mem (T46.inv_mem (uK_le_T46 hc)) hg, ?_⟩
    have e : c⁻¹ * g * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by group
    rw [e, hcj]
    group
  rcases korbits.1 _ hgA hne with h | h | h
  · obtain ⟨g', hg', e⟩ := key j1 h
    exact ⟨g', hg', Or.inl e⟩
  · obtain ⟨g', hg', e⟩ := key j2 h
    exact ⟨g', hg', Or.inr (Or.inl e)⟩
  · obtain ⟨g', hg', e⟩ := key j3 h
    exact ⟨g', hg', Or.inr (Or.inr e)⟩

theorem j1_comm_uS
    : ∀ s ∈ uS, j1 * s = s * j1 := by
  have hle : uS ≤ Subgroup.centralizer {j1} := by
    rw [uS_closure, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (sylow_facts.2.2.2.1 g hg).symm
  intro s hs
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hs)).symm

theorem center_uS
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ uS) :
    (∀ s ∈ uS, x * s = s * x) ↔ x = 1 ∨ x = j1 := by
  refine ⟨fun hc => sylow_facts.2.2.2.2.1 x hx fun a ha => hc a (sGens_mem a ha), ?_⟩
  rintro (rfl | rfl)
  · intro s _
    rw [one_mul, mul_one]
  · exact j1_comm_uS

theorem uS_decomp
    {s : Equiv.Perm (Fin 693)} (hs : s ∈ uS) : ∃ b ∈ uT, s * b⁻¹ ∈ uA := by
  have hs' : s ∈ ((uA ⊔ uT : Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) := by
    rw [← uS_eq]
    exact hs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left uA uT uT_le_normalizer] at hs'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hs'
  exact ⟨b, hb, by rw [mul_inv_cancel_right]; exact ha⟩

theorem tpart_spec
    {s : Equiv.Perm (Fin 693)} (hs : s ∈ uS) :
    tpart s ∈ uT ∧ s * (tpart s)⁻¹ ∈ uA := by
  have h := uS_decomp hs
  rw [tpart, dite_eq_left h]
  exact h.choose_spec

theorem tpart_eq
    {s b : Equiv.Perm (Fin 693)} (hs : s ∈ uS) (hb : b ∈ uT)
    (hsb : s * b⁻¹ ∈ uA) : tpart s = b := by
  obtain ⟨h1, h2⟩ := tpart_spec hs
  have hA : tpart s * b⁻¹ ∈ uA := by
    have e : tpart s * b⁻¹ = (s * (tpart s)⁻¹)⁻¹ * (s * b⁻¹) := by group
    rw [e]
    exact uA.mul_mem (uA.inv_mem h2) hsb
  have hT : tpart s * b⁻¹ ∈ uT := uT.mul_mem h1 (uT.inv_mem hb)
  have hAT : tpart s * b⁻¹ ∈ uA ⊓ uT := ⟨hA, hT⟩
  rw [uA_inf_uT, Subgroup.mem_bot] at hAT
  exact mul_inv_eq_one.1 hAT

theorem tpart_mul
    {s s' : Equiv.Perm (Fin 693)} (hs : s ∈ uS) (hs' : s' ∈ uS) :
    tpart (s * s') = tpart s * tpart s' := by
  obtain ⟨h1, h2⟩ := tpart_spec hs
  obtain ⟨h1', h2'⟩ := tpart_spec hs'
  refine tpart_eq (uS.mul_mem hs hs') (uT.mul_mem h1 h1') ?_
  have e : s * s' * (tpart s * tpart s')⁻¹ =
      (s * (tpart s)⁻¹) * (tpart s * (s' * (tpart s')⁻¹) * (tpart s)⁻¹) := by group
  rw [e]
  exact uA.mul_mem h2 ((Subgroup.mem_normalizer_iff.1 (uT_le_normalizer h1) _).1 h2')

theorem mem_uA_of_tpart
    {s : Equiv.Perm (Fin 693)} (hs : s ∈ uS) (h : tpart s = 1) :
    s ∈ uA := by
  have := (tpart_spec hs).2
  rwa [h, inv_one, mul_one] at this

theorem mul_inv_mem_uA
    {s s' : Equiv.Perm (Fin 693)} (hs : s ∈ uS) (hs' : s' ∈ uS)
    (h : tpart s = tpart s') : s * s'⁻¹ ∈ uA := by
  have e : s * s'⁻¹ = (s * (tpart s)⁻¹) * (s' * (tpart s')⁻¹)⁻¹ := by
    rw [h]
    group
  rw [e]
  exact uA.mul_mem (tpart_spec hs).2 (uA.inv_mem (tpart_spec hs').2)

theorem card_le_mul_tpart
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : X ≤ uS) :
    Nat.card X ≤ Nat.card {x // x ∈ X ∧ x ∈ uA} *
      Nat.card (tpart '' (X : Set (Equiv.Perm (Fin 693)))) := by
  classical
  let pre : Equiv.Perm (Fin 693) → Equiv.Perm (Fin 693) := fun b =>
    if h : ∃ e ∈ X, tpart e = b then h.choose else 1
  have hpre : ∀ e ∈ X, pre (tpart e) ∈ X ∧ tpart (pre (tpart e)) = tpart e := by
    intro e he
    have h : ∃ e' ∈ X, tpart e' = tpart e := ⟨e, he, rfl⟩
    simp only [pre, dite_eq_left h]
    exact h.choose_spec
  let f : X → {x // x ∈ X ∧ x ∈ uA} × (tpart '' (X : Set (Equiv.Perm (Fin 693)))) := fun e =>
    (⟨(e : Equiv.Perm (Fin 693)) * (pre (tpart e))⁻¹,
      X.mul_mem e.2 (X.inv_mem (hpre e e.2).1),
      mul_inv_mem_uA (hX e.2) (hX (hpre e e.2).1) (hpre e e.2).2.symm⟩,
      ⟨tpart e, e, e.2, rfl⟩)
  have hf : Function.Injective f := by
    intro e e' h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := congrArg Subtype.val h2
    simp only at h2'
    rw [h2'] at h1
    exact Subtype.ext (mul_right_cancel h1)
  calc Nat.card X ≤ Nat.card ({x // x ∈ X ∧ x ∈ uA} ×
        (tpart '' (X : Set (Equiv.Perm (Fin 693))))) := Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

theorem thompson_facts :
    (∀ x ∈ uT, (∀ g ∈ tGens, x * g = g * x) ∨
      Nat.card {y : uT // (y : Equiv.Perm (Fin 693)) * x = x * y} ≤ 16) ∧
    Nat.card {x : uT // ∀ g ∈ tGens, (x : Equiv.Perm (Fin 693)) * g = g * x} ≤ 16 ∧
    (∀ x ∈ uT, x ≠ 1 → Nat.card {a : uA // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 32) ∧
    (∀ x ∈ uT, x * x ≠ 1 →
      Nat.card {a : uA // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 16) ∧
    ∀ b ∈ uT, ∀ c ∈ uT, b ≠ c → b ≠ 1 → c ≠ 1 → b * b = 1 → c * c = 1 → b * c = c * b →
      Nat.card {a : uA // (a : Equiv.Perm (Fin 693)) * b = b * a ∧ (a : Equiv.Perm (Fin 693)) *
        c = c * a} ≤ 16 := by
  exact thompson_check

theorem abelian_le_uS
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : X ≤ uS)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 512 ∧ (Nat.card X = 512 → X = uA) := by
  obtain ⟨F1, F2, F3, F4, F5⟩ := thompson_facts
  have hle := card_le_mul_tpart hX
  set B := tpart '' (X : Set (Equiv.Perm (Fin 693))) with hB
  have hBT : ∀ b ∈ B, b ∈ uT := by
    rintro _ ⟨e, he, rfl⟩
    exact (tpart_spec (hX he)).1
  have hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← tpart_mul (hX he) (hX he'), ← tpart_mul (hX he') (hX he), hcomm e he e' he']
  have hBcent : ∀ x, x ∈ X ∧ x ∈ uA → ∀ b ∈ B, x * b = b * x := by
    rintro x ⟨hxX, hxA⟩ _ ⟨e, he, rfl⟩
    have h2 := (tpart_spec (hX he)).2
    set a := e * (tpart e)⁻¹ with ha
    have e1 : tpart e = a⁻¹ * e := by
      rw [ha]
      group
    have hax := uA_comm x hxA _ (uA.inv_mem h2)
    have hxe := hcomm x hxX e he
    rw [e1]
    calc x * (a⁻¹ * e) = (x * a⁻¹) * e := by group
      _ = (a⁻¹ * x) * e := by rw [hax]
      _ = a⁻¹ * (x * e) := by group
      _ = a⁻¹ * (e * x) := by rw [hxe]
      _ = a⁻¹ * e * x := by group
  by_cases hB1 : ∀ b ∈ B, b = 1
  · have hXA : X ≤ uA := fun x hx => mem_uA_of_tpart (hX hx) (hB1 _ ⟨x, hx, rfl⟩)
    have hcard : Nat.card X ≤ 512 := card_uA ▸ Subgroup.card_le_of_le hXA
    exact ⟨hcard, fun h => Subgroup.eq_of_le_of_card_ge hXA (by rw [h, card_uA])⟩
  push Not at hB1
  obtain ⟨b, hbB, hb1⟩ := hB1
  have hB16 : Nat.card B ≤ 16 := by
    by_cases hc : ∀ x ∈ B, ∀ g ∈ tGens, x * g = g * x
    · refine le_trans (Nat.card_le_card_of_injective
        (fun x => (⟨⟨x.1, hBT x.1 x.2⟩, hc x.1 x.2⟩ :
          {x : uT // ∀ g ∈ tGens, (x : Equiv.Perm (Fin 693)) * g = g * x})) ?_) F2
      intro x y h
      exact Subtype.ext (congrArg (fun z : {x : uT // ∀ g ∈ tGens,
        (x : Equiv.Perm (Fin 693)) * g = g * x} => ((z.1 : uT) : Equiv.Perm (Fin 693))) h)
    · push Not at hc
      obtain ⟨x, hxB, g, hg, hxg⟩ := hc
      have hxC := (F1 x (hBT x hxB)).resolve_left fun h => hxg (h g hg)
      refine le_trans (Nat.card_le_card_of_injective
        (fun y => (⟨⟨y.1, hBT y.1 y.2⟩, hBcomm y.1 y.2 x hxB⟩ :
          {y : uT // (y : Equiv.Perm (Fin 693)) * x = x * y})) ?_) hxC
      intro y z h
      exact Subtype.ext (congrArg (fun w : {y : uT // (y : Equiv.Perm (Fin 693)) * x = x * y} =>
        ((w.1 : uT) : Equiv.Perm (Fin 693))) h)
  have h256 : Nat.card X ≤ 256 := by
    by_cases hsq : ∃ y ∈ B, y * y ≠ 1
    · obtain ⟨y, hyB, hy⟩ := hsq
      have h1 : Nat.card {x // x ∈ X ∧ x ∈ uA} ≤ 16 :=
        (card_inter_le (P := fun a => a * y = y * a) fun x hx => hBcent x hx y hyB).trans
          (F4 y (hBT y hyB) hy)
      calc Nat.card X ≤ _ := hle
        _ ≤ 16 * 16 := Nat.mul_le_mul h1 hB16
        _ = 256 := by norm_num
    push Not at hsq
    by_cases hc : ∃ c ∈ B, c ≠ 1 ∧ c ≠ b
    · obtain ⟨c, hcB, hc1, hcb⟩ := hc
      have h1 : Nat.card {x // x ∈ X ∧ x ∈ uA} ≤ 16 :=
        (card_inter_le (P := fun a => a * b = b * a ∧ a * c = c * a) fun x hx =>
          ⟨hBcent x hx b hbB, hBcent x hx c hcB⟩).trans
          (F5 b (hBT b hbB) c (hBT c hcB) (Ne.symm hcb) hb1 hc1 (hsq b hbB) (hsq c hcB)
            (hBcomm b hbB c hcB))
      calc Nat.card X ≤ _ := hle
        _ ≤ 16 * 16 := Nat.mul_le_mul h1 hB16
        _ = 256 := by norm_num
    push Not at hc
    have hB2 : Nat.card B ≤ 2 := by
      have hsub : B ⊆ {1, b} := fun c hcB => by
        by_cases hc1 : c = 1
        · exact Set.mem_insert_iff.2 (Or.inl hc1)
        · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 (hc c hcB hc1)))
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub).trans ((Set.ncard_insert_le 1 {b}).trans
        (le_of_eq (by rw [Set.ncard_singleton])))
    have h1 : Nat.card {x // x ∈ X ∧ x ∈ uA} ≤ 32 :=
      (card_inter_le (P := fun a => a * b = b * a) fun x hx => hBcent x hx b hbB).trans
        (F3 b (hBT b hbB) hb1)
    calc Nat.card X ≤ _ := hle
      _ ≤ 32 * 2 := Nat.mul_le_mul h1 hB2
      _ ≤ 256 := by norm_num
  exact ⟨by omega, fun h => absurd h (by omega)⟩

theorem square_facts :
    orderOf o1 = 3 ∧ orderOf o2 = 3 ∧ o1 * j1 = j1 * o1 ∧ o2 * j1 = j1 * o2 ∧
      (o1 * o2) ^ 2 = j1 ∧ y2 ^ 2 = j2 ∧
      ∀ k ∈ uK, k * j3 = j3 * k → ∀ a ∈ uA, (a * k) ^ 2 ≠ j3 := by
  rw [uA_eq, uK_eq]
  exact square_check

theorem sq_j1
    : ∃ u ∈ T46, ∃ v ∈ T46, orderOf u = 3 ∧ orderOf v = 3 ∧ u * j1 = j1 * u ∧
    v * j1 = j1 * v ∧ (u * v) ^ 2 = j1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := square_facts
  exact ⟨o1, o1_mem, o2, o2_mem, h1, h2, h3, h4, h5⟩

theorem sq_j2
    : y2 ∈ uP ∧ y2 ^ 2 = j2 :=
  ⟨evalCodes_mem _ (fun g hg => by rw [uP_closure]; exact Subgroup.subset_closure hg) _,
    square_facts.2.2.2.2.2.1⟩

theorem not_sq_j3 :
    ∀ g ∈ T46, g ^ 2 ≠ j3 := by
  intro g hg hsq
  have hgj : g * j3 = j3 * g := by
    rw [← hsq]
    exact (Commute.self_pow g 2).eq
  have hgP : g ∈ uP := mem_uP_of_smul hg (smul_fixed_of_comm hgj)
  rw [uP_eq] at hgP
  have hgP' : g ∈ ((uA ⊔ uK : Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) :=
    hgP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left uA uK uK_le_normalizer] at hgP'
  obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.1 hgP'
  have hkj : k * j3 = j3 * k := by
    have ha' := uA_comm a ha j3 j3_mem
    calc k * j3 = a⁻¹ * ((a * k) * j3) := by group
      _ = a⁻¹ * (j3 * (a * k)) := by rw [hgj]
      _ = a⁻¹ * (j3 * a) * k := by group
      _ = a⁻¹ * (a * j3) * k := by rw [ha']
      _ = j3 * k := by group
  exact square_facts.2.2.2.2.2.2 k hk hkj a ha hsq

end CFSG.EvenSmallLie.UnitarySix
