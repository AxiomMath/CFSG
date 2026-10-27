module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Counting

theorem card_le_card_inf_mul_ncard {G Y : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (φ : G → Y) {T : Set Y} (hT : T.Finite) (hφT : ∀ x ∈ H, φ x ∈ T)
    (hφ : ∀ x ∈ H, ∀ y ∈ H, φ x = φ y → x⁻¹ * y ∈ N) :
    Nat.card H ≤ Nat.card (H ⊓ N : Subgroup G) * T.ncard := by
  classical
  have := Fintype.ofFinite G
  have hcard : ∀ M : Subgroup G, Nat.card M = (Finset.univ.filter (· ∈ M)).card := by
    intro M
    rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
    congr 1
    ext x
    simp
  rw [hcard H, hcard (H ⊓ N), Set.ncard_eq_toFinset_card T hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := φ) (t := hT.toFinset) (fun x hx => ?_) _
    fun v _ => ?_
  · rw [Finset.mem_filter] at hx
    simpa using hφT x hx.2
  · rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun x => x ∈ H ∧ φ x = v) with he | hne
    · have : (Finset.univ.filter (· ∈ H)).filter (fun x => φ x = v) =
          Finset.univ.filter fun x => x ∈ H ∧ φ x = v := by
        ext x
        simp
      rw [this, he, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨x₀, hx₀⟩ := hne
      have hx₀ : x₀ ∈ H ∧ φ x₀ = v := (Finset.mem_filter.1 hx₀).2
      refine Finset.card_le_card_of_injOn (fun y => x₀⁻¹ * y) (fun y hy => ?_)
        (fun y _ y' _ e => mul_left_cancel e)
      have hy' : y ∈ H ∧ φ y = v := by simpa using hy
      have hmem : x₀⁻¹ * y ∈ H ⊓ N :=
        ⟨H.mul_mem (H.inv_mem hx₀.1) hy'.1, hφ x₀ hx₀.1 y hy'.1 (hx₀.2.trans hy'.2.symm)⟩
      simpa using hmem

end Counting

section Coordinates

variable [CharP K 2]

theorem miyamotoXGL_mem_A1_iff_of_mem_P {a b c d : K} (hx : miyamotoXGL h a b c d ∈ miyamotoP h) :
    miyamotoXGL h a b c d ∈ miyamotoA1 h ↔ a = 0 := by
  obtain ⟨hb, hd⟩ := (miyamotoXGL_mem_P h).1 hx
  refine ⟨fun hA => ((miyamotoXGL_mem_A1 h).1 hA).1, fun ha => ?_⟩
  subst ha
  exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩

omit [CharP K 2] in
theorem miyamotoXGL_mem_A2_iff_of_mem_P {a b c d : K} (hx : miyamotoXGL h a b c d ∈ miyamotoP h) :
    miyamotoXGL h a b c d ∈ miyamotoA2 h ↔ b = 0 := by
  obtain ⟨-, hd⟩ := (miyamotoXGL_mem_P h).1 hx
  exact ⟨fun hA => ((miyamotoXGL_mem_A2 h).1 hA).1, fun hb => (miyamotoXGL_mem_A2 h).2 ⟨hb, hd⟩⟩

theorem inv_mul_mem_A1_of_coord {x y : GL (Fin 4) K} (hx : x ∈ miyamotoP h) (hy : y ∈ miyamotoP h)
    (e : (x : Matrix (Fin 4) (Fin 4) K) 1 0 = (y : Matrix (Fin 4) (Fin 4) K) 1 0) :
    x⁻¹ * y ∈ miyamotoA1 h := by
  obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hx
  obtain ⟨a', b', c', d', hb', -, rfl⟩ := (mem_P h).1 hy
  have hxy : (miyamotoXGL h a b c d)⁻¹ * miyamotoXGL h a' b' c' d' ∈ miyamotoP h :=
    mul_mem (inv_mem hx) hy
  simp only [coe_miyamotoXGL, miyamotoX_one_zero] at e
  subst e
  rw [miyamotoXGL_inv h hb, miyamotoXGL_mul h hb] at hxy ⊢
  rw [miyamotoXGL_mem_A1_iff_of_mem_P h hxy]
  exact CharTwo.add_self_eq_zero a

theorem ncard_trace_mul_eq_zero {a : K} (ha : a ≠ 0) :
    {c : K | h.bar a * c + a * h.bar c = 0}.ncard = 2 ^ f := by
  have hbar : h.bar a ≠ 0 := by simpa using ha
  have hset : {c : K | h.bar a * c + a * h.bar c = 0} =
      (fun t => (h.bar a)⁻¹ * t) '' {d : K | h.bar d = d} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hc
      refine ⟨h.bar a * c, ?_, by field_simp⟩
      rw [← add_bar_eq_zero_iff h, map_mul, h.bar_bar]
      linear_combination hc
    · rintro ⟨t, ht, rfl⟩
      rw [map_mul, map_inv₀, h.bar_bar, ht]
      field_simp
      linear_combination t * CharTwo.two_eq_zero (R := K)
  rw [hset, Set.ncard_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hbar)), ncard_fixed]

end Coordinates

section ModZ

variable [CharP K 2]

theorem miyamotoXGL_mul_self_mem_Z_iff {a b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h a b c d * miyamotoXGL h a b c d ∈ miyamotoZ h ↔ a * b = 0 := by
  rw [miyamotoXGL_mul_self h hb, miyamotoXGL_mem_Z]
  refine ⟨fun e => e.2.2.1, fun e => ⟨rfl, rfl, e, ?_⟩⟩
  simp only [map_add, map_mul, h.bar_bar, hb]
  ring

theorem mem_A1_or_mem_A2_of_mul_self_mem_Z {x : GL (Fin 4) K} (hx : x ∈ miyamotoP h)
    (hx2 : x * x ∈ miyamotoZ h) : x ∈ miyamotoA1 h ∨ x ∈ miyamotoA2 h := by
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hx
  rw [miyamotoXGL_mem_A1_iff_of_mem_P h hx, miyamotoXGL_mem_A2_iff_of_mem_P h hx]
  exact mul_eq_zero.1 ((miyamotoXGL_mul_self_mem_Z_iff h hb).1 hx2)

theorem mem_A1_of_commutator_mem_Z {x y : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h)
    (hxA : x ∉ miyamotoA2 h) (hy : y ∈ miyamotoP h) (hxy : ⁅x, y⁆ ∈ miyamotoZ h) :
    y ∈ miyamotoA1 h := by
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
  obtain ⟨a', b', c', d', hb', hd', rfl⟩ := (mem_P h).1 hy
  have hb0 : b ≠ 0 := fun e => hxA ((miyamotoXGL_mem_A2_iff_of_mem_P h
    (miyamotoA1_le_P h hx)).2 e)
  rw [miyamotoXGL_commutator h hb hb', miyamotoXGL_mem_Z] at hxy
  have : b * a' = 0 := by simpa using hxy.2.2.1
  exact (miyamotoXGL_mem_A1_iff_of_mem_P h hy).2 ((mul_eq_zero.1 this).resolve_left hb0)

theorem le_A1_or_le_A2_of_mod_Z {E : Subgroup (GL (Fin 4) K)} (hE : E ≤ miyamotoP h)
    (hsq : ∀ x ∈ E, x * x ∈ miyamotoZ h) (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ miyamotoZ h) :
    E ≤ miyamotoA1 h ∨ E ≤ miyamotoA2 h := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hxE, hxA2⟩ := Set.not_subset.1 hne.2
  have hxA1 : x ∈ miyamotoA1 h :=
    (mem_A1_or_mem_A2_of_mul_self_mem_Z h (hE hxE) (hsq x hxE)).resolve_right hxA2
  exact hne.1 fun y hy => mem_A1_of_commutator_mem_Z h hxA1 hxA2 (hE hy) (hcomm x hxE y hy)

theorem miyamotoA2_mod_Z : (∀ x ∈ miyamotoA2 h, x * x ∈ miyamotoZ h) ∧
    ∀ x ∈ miyamotoA2 h, ∀ y ∈ miyamotoA2 h, ⁅x, y⁆ ∈ miyamotoZ h := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 hx
    exact (miyamotoXGL_mul_self_mem_Z_iff h (map_zero _)).2 (mul_zero a)
  · rw [← commutator_miyamotoA2 h]
    exact commutator_mem_commutator hx hy

theorem card_le_and_eq_A2_of_mod_Z {E : Subgroup (GL (Fin 4) K)} (hE : E ≤ miyamotoP h)
    (hsq : ∀ x ∈ E, x * x ∈ miyamotoZ h) (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ miyamotoZ h) :
    Nat.card E ≤ (2 ^ f) ^ 5 ∧ ((2 ^ f) ^ 5 ≤ Nat.card E → E = miyamotoA2 h) := by
  have := h.finite
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.one_le; omega)
  have h45 : (2 ^ f) ^ 4 < (2 ^ f) ^ 5 := Nat.pow_lt_pow_right hq (by norm_num)
  rcases le_A1_or_le_A2_of_mod_Z h hE hsq hcomm with hEA | hEA
  · have hc := (card_le_of_le hEA).trans_eq (card_miyamotoA1 h)
    exact ⟨hc.trans h45.le, fun hge => absurd (hge.trans hc) (not_le.2 h45)⟩
  · have hc := (card_le_of_le hEA).trans_eq (card_miyamotoA2 h)
    exact ⟨hc, fun hge => eq_of_le_of_card_ge hEA (by rw [card_miyamotoA2]; exact hge)⟩

end ModZ

section Centralizers

variable [CharP K 2]

theorem mem_A1_inf_centralizer_iff {a b c d : K} (hb : h.bar b = b) (ha : a ≠ 0)
    {y : GL (Fin 4) K} : y ∈ miyamotoA1 h ⊓ centralizer ({miyamotoXGL h a b c d} : Set _) ↔
      ∃ c' d' : K, h.bar d' = d' ∧ h.bar a * c' + a * h.bar c' = 0 ∧
        y = miyamotoXGL h 0 0 c' d' := by
  constructor
  · rintro ⟨hyA, hyC⟩
    obtain ⟨b', c', d', hb', hd', rfl⟩ := (mem_A1 h).1 hyA
    have e : ⁅miyamotoXGL h a b c d, miyamotoXGL h 0 b' c' d'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hyC).symm
    rw [miyamotoXGL_commutator h hb hb', ← miyamotoXGL_zero h, miyamotoXGL_inj] at e
    have hb0 : b' = 0 := by
      have : b' * a = 0 := by simpa using e.2.2.1
      exact (mul_eq_zero.1 this).resolve_right ha
    subst hb0
    exact ⟨c', d', hd', by simpa using e.2.2.2, rfl⟩
  · rintro ⟨c', d', hd', hc', rfl⟩
    refine ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hd'⟩,
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [← commutatorElement_eq_one_iff_mul_comm, miyamotoXGL_commutator h (map_zero _) hb,
      ← miyamotoXGL_zero h, miyamotoXGL_inj]
    exact ⟨rfl, rfl, by ring, by simpa using hc'⟩

theorem card_A1_inf_centralizer_le {x : GL (Fin 4) K} (hx : x ∈ miyamotoP h)
    (hxA : x ∉ miyamotoA1 h) :
    Nat.card (miyamotoA1 h ⊓ centralizer ({x} : Set (GL (Fin 4) K)) : Subgroup _) ≤
      (2 ^ f) ^ 2 := by
  have := h.finite
  obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hx
  have ha : a ≠ 0 := fun e => hxA ((miyamotoXGL_mem_A1_iff_of_mem_P h hx).2 e)
  set T : Set (K × K) := {c' | h.bar a * c' + a * h.bar c' = 0} ×ˢ {d' | h.bar d' = d'}
  have hT : T.ncard = (2 ^ f) ^ 2 := by
    rw [Set.ncard_prod, ncard_trace_mul_eq_zero h ha, ncard_fixed, sq]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hT]
  refine Set.ncard_le_ncard_of_injOn (fun y : GL (Fin 4) K =>
    ((y : Matrix (Fin 4) (Fin 4) K) 2 0, (y : Matrix (Fin 4) (Fin 4) K) 3 0)) ?_ ?_
    (Set.toFinite T)
  · intro y hy
    obtain ⟨c', d', hd', hc', rfl⟩ := (mem_A1_inf_centralizer_iff h hb ha).1 hy
    exact ⟨by simpa using hc', by simpa using hd'⟩
  · intro y hy y' hy' e
    obtain ⟨c', d', -, -, rfl⟩ := (mem_A1_inf_centralizer_iff h hb ha).1 hy
    obtain ⟨c₂, d₂, -, -, rfl⟩ := (mem_A1_inf_centralizer_iff h hb ha).1 hy'
    simp only [coe_miyamotoXGL, miyamotoX_two_zero, miyamotoX_three_zero, Prod.mk.injEq] at e
    rw [e.1, e.2]

omit [CharP K 2] in
theorem ncard_fixed_mul {a : K} (ha : a ≠ 0) :
    ((· * a) '' {t : K | h.bar t = t}).ncard = 2 ^ f := by
  rw [Set.ncard_image_of_injective _ (mul_left_injective₀ ha), ncard_fixed]

theorem card_P_inf_centralizer_le {x : GL (Fin 4) K} (hx : x ∈ miyamotoP h)
    (hxA1 : x ∉ miyamotoA1 h) (hxA2 : x ∉ miyamotoA2 h) :
    Nat.card (miyamotoP h ⊓ centralizer ({x} : Set (GL (Fin 4) K)) : Subgroup _) ≤
      (2 ^ f) ^ 3 := by
  have := h.finite
  obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hx
  have ha : a ≠ 0 := fun e => hxA1 ((miyamotoXGL_mem_A1_iff_of_mem_P h hx).2 e)
  have hb0 : b ≠ 0 := fun e => hxA2 ((miyamotoXGL_mem_A2_iff_of_mem_P h hx).2 e)
  have key := card_le_card_inf_mul_ncard (H := miyamotoP h ⊓ centralizer
    ({miyamotoXGL h a b c d} : Set (GL (Fin 4) K))) (N := miyamotoA1 h)
    (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K) 1 0)
    (T := (· * a) '' {t : K | h.bar t = t}) (Set.toFinite _) ?_
    (fun y hy y' hy' e => inv_mul_mem_A1_of_coord h hy.1 hy'.1 e)
  · have hinf : miyamotoP h ⊓ centralizer ({miyamotoXGL h a b c d} : Set (GL (Fin 4) K)) ⊓
        miyamotoA1 h = miyamotoA1 h ⊓ centralizer ({miyamotoXGL h a b c d} : Set _) := by
      rw [inf_comm, ← inf_assoc, inf_eq_left.2 (miyamotoA1_le_P h)]
    rw [hinf, ncard_fixed_mul h ha] at key
    calc _ ≤ _ := key
      _ ≤ (2 ^ f) ^ 2 * 2 ^ f :=
        Nat.mul_le_mul_right _ (card_A1_inf_centralizer_le h hx hxA1)
      _ = (2 ^ f) ^ 3 := by ring
  · rintro y ⟨hyP, hyC⟩
    obtain ⟨a', b', c', d', hb', -, rfl⟩ := (mem_P h).1 hyP
    have e : ⁅miyamotoXGL h a b c d, miyamotoXGL h a' b' c' d'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hyC).symm
    rw [miyamotoXGL_commutator h hb hb', ← miyamotoXGL_zero h, miyamotoXGL_inj] at e
    have e2 : b * a' = b' * a := by
      linear_combination e.2.2.1 - b' * a * CharTwo.two_eq_zero (R := K)
    refine ⟨b' * b⁻¹, ?_, ?_⟩
    · change h.bar (b' * b⁻¹) = b' * b⁻¹
      rw [map_mul, map_inv₀, hb, hb']
    · simp only [coe_miyamotoXGL, miyamotoX_one_zero]
      field_simp
      linear_combination -e2

theorem le_or_le_of_forall_mem_or_mem {G : Type*} [Group G] {A B E : Subgroup G}
    (hE : ∀ x ∈ E, x ∈ A ∨ x ∈ B) : E ≤ A ∨ E ≤ B := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hxE, hxA⟩ := Set.not_subset.1 hne.1
  obtain ⟨y, hyE, hyB⟩ := Set.not_subset.1 hne.2
  have hxB := (hE x hxE).resolve_left hxA
  have hyA := (hE y hyE).resolve_right hyB
  rcases hE (x * y) (mul_mem hxE hyE) with hxy | hxy
  · exact hxA (by simpa using mul_mem hxy (inv_mem hyA))
  · exact hyB (by simpa using mul_mem (inv_mem hxB) hxy)

theorem trace_eq_zero_of_mem_Z2_of_commute {a c d c'' d'' : K}
    (hcomm : miyamotoXGL h 0 0 c'' d'' * miyamotoXGL h a 0 c d =
      miyamotoXGL h a 0 c d * miyamotoXGL h 0 0 c'' d'') :
    h.bar a * c'' + a * h.bar c'' = 0 := by
  have e : ⁅miyamotoXGL h a 0 c d, miyamotoXGL h 0 0 c'' d''⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
  rw [miyamotoXGL_commutator_A2, ← miyamotoXGL_zero h, miyamotoXGL_inj] at e
  simpa using e.2.2.2

theorem card_le_of_le_A2 {B : Subgroup (GL (Fin 4) K)} (hB : B ≤ miyamotoA2 h)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBA : ¬ B ≤ miyamotoA1 h) :
    Nat.card B ≤ (2 ^ f) ^ 3 := by
  have := h.finite
  have hbb := h.bar_bar
  obtain ⟨x, hxB, hxA⟩ := Set.not_subset.1 hBA
  obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 (hB hxB)
  have ha : a ≠ 0 := fun e => hxA ((miyamotoXGL_mem_A1_iff_of_mem_P h
    (miyamotoA2_le_P h (hB hxB))).2 e)
  have hBP : B ≤ miyamotoP h := hB.trans (miyamotoA2_le_P h)
  have hBA1 : ∀ z ∈ B ⊓ miyamotoA1 h, ∃ c'' d'' : K, h.bar d'' = d'' ∧
      z = miyamotoXGL h 0 0 c'' d'' := fun z hz =>
    (mem_Z2 h).1 ((miyamotoA1_inf_miyamotoA2 h).le ⟨hz.2, hB hz.1⟩)
  by_cases hT : ∀ y ∈ B, (y : Matrix (Fin 4) (Fin 4) K) 1 0 ∈ (· * a) '' {t : K | h.bar t = t}
  ·
    have key := card_le_card_inf_mul_ncard (H := B) (N := miyamotoA1 h)
      (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K) 1 0) (Set.toFinite _) hT
      (fun y hy y' hy' e => inv_mul_mem_A1_of_coord h (hBP hy) (hBP hy') e)
    rw [ncard_fixed_mul h ha] at key
    have hcard : Nat.card (B ⊓ miyamotoA1 h : Subgroup _) ≤ (2 ^ f) ^ 2 := by
      set T : Set (K × K) := {c' | h.bar a * c' + a * h.bar c' = 0} ×ˢ {d' | h.bar d' = d'}
      have hTc : T.ncard = (2 ^ f) ^ 2 := by
        rw [Set.ncard_prod, ncard_trace_mul_eq_zero h ha, ncard_fixed, sq]
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hTc]
      refine Set.ncard_le_ncard_of_injOn (fun y : GL (Fin 4) K =>
        ((y : Matrix (Fin 4) (Fin 4) K) 2 0, (y : Matrix (Fin 4) (Fin 4) K) 3 0)) ?_ ?_
        (Set.toFinite T)
      · intro z hz
        obtain ⟨c'', d'', hd'', rfl⟩ := hBA1 z hz
        have h1 := trace_eq_zero_of_mem_Z2_of_commute h (hcomm _ hz.1 _ hxB)
        exact ⟨by simpa using h1, by simpa using hd''⟩
      · intro z hz z' hz' e
        obtain ⟨c'', d'', -, rfl⟩ := hBA1 z hz
        obtain ⟨c₂, d₂, -, rfl⟩ := hBA1 z' hz'
        simp only [coe_miyamotoXGL, miyamotoX_two_zero, miyamotoX_three_zero,
          Prod.mk.injEq] at e
        rw [e.1, e.2]
    calc _ ≤ _ := key
      _ ≤ (2 ^ f) ^ 2 * 2 ^ f := Nat.mul_le_mul_right _ hcard
      _ = (2 ^ f) ^ 3 := by ring
  ·
    push Not at hT
    obtain ⟨y, hyB, hyT⟩ := hT
    obtain ⟨a', c', d', -, rfl⟩ := (mem_A2 h).1 (hB hyB)
    simp only [coe_miyamotoXGL, miyamotoX_one_zero] at hyT
    have hle : B ⊓ miyamotoA1 h ≤ miyamotoZ h := by
      intro z hz
      obtain ⟨c'', d'', hd'', rfl⟩ := hBA1 z hz
      have h1 := trace_eq_zero_of_mem_Z2_of_commute h (hcomm _ hz.1 _ hxB)
      have h2 := trace_eq_zero_of_mem_Z2_of_commute h (hcomm _ hz.1 _ hyB)
      refine (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, ?_, hd''⟩
      by_contra hc
      have hbc : h.bar c'' ≠ 0 := by simpa using hc
      apply hyT
      refine ⟨a' * a⁻¹, ?_, by field_simp⟩
      change h.bar (a' * a⁻¹) = a' * a⁻¹
      have hbar : h.bar a ≠ 0 := by simpa using ha
      rw [map_mul, map_inv₀]
      have key2 : (h.bar a' * a - a' * h.bar a) * c'' = 0 := by
        linear_combination a * h2 - a' * h1
      have key3 := (mul_eq_zero.1 key2).resolve_right hc
      field_simp
      linear_combination key3
    have key := card_le_card_inf_mul_ncard (H := B) (N := miyamotoA1 h)
      (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K) 1 0) (T := Set.univ)
      (Set.toFinite _) (fun _ _ => Set.mem_univ _)
      (fun y hy y' hy' e => inv_mul_mem_A1_of_coord h (hBP hy) (hBP hy') e)
    rw [Set.ncard_univ, h.card_eq_sq] at key
    calc _ ≤ _ := key
      _ ≤ 2 ^ f * (2 ^ f) ^ 2 :=
        Nat.mul_le_mul_right _ ((card_le_of_le hle).trans_eq (card_miyamotoZ h))
      _ = (2 ^ f) ^ 3 := by ring

end Centralizers

section Abelian

variable [CharP K 2]

theorem card_le_of_commute_of_not_le_A1 {B : Subgroup (GL (Fin 4) K)} (hB : B ≤ miyamotoP h)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBA : ¬ B ≤ miyamotoA1 h) :
    Nat.card B ≤ (2 ^ f) ^ 3 := by
  have := h.finite
  by_cases hx : ∃ x ∈ B, x ∉ miyamotoA1 h ∧ x ∉ miyamotoA2 h
  · obtain ⟨x, hxB, hxA1, hxA2⟩ := hx
    have hle : B ≤ miyamotoP h ⊓ centralizer ({x} : Set (GL (Fin 4) K)) := fun y hy =>
      ⟨hB hy, mem_centralizer_singleton_iff.2 (hcomm x hxB y hy).symm⟩
    exact (card_le_of_le hle).trans (card_P_inf_centralizer_le h (hB hxB) hxA1 hxA2)
  · push Not at hx
    rcases le_or_le_of_forall_mem_or_mem (A := miyamotoA1 h) (B := miyamotoA2 h) (E := B)
      (fun x hxB => or_iff_not_imp_left.2 (hx x hxB)) with hle | hle
    · exact absurd hle hBA
    · exact card_le_of_le_A2 h hle hcomm hBA

theorem card_le_and_eq_A1_of_commute {B : Subgroup (GL (Fin 4) K)} (hB : B ≤ miyamotoP h)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ (2 ^ f) ^ 4 ∧ ((2 ^ f) ^ 4 ≤ Nat.card B → B = miyamotoA1 h) := by
  have := h.finite
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.one_le; omega)
  have h34 : (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
  by_cases hBA : B ≤ miyamotoA1 h
  · have hc := (card_le_of_le hBA).trans_eq (card_miyamotoA1 h)
    exact ⟨hc, fun hge => eq_of_le_of_card_ge hBA (by rw [card_miyamotoA1]; exact hge)⟩
  · have hc := card_le_of_commute_of_not_le_A1 h hB hcomm hBA
    exact ⟨hc.trans h34.le, fun hge => absurd (hge.trans hc) (not_le.2 h34)⟩

theorem card_le_and_eq_A1_of_isElementaryAbelian {E : Subgroup (GL (Fin 4) K)}
    (hE : E ≤ miyamotoP h) [CFSG.IsElementaryAbelian 2 E] :
    Nat.card E ≤ (2 ^ f) ^ 4 ∧ ((2 ^ f) ^ 4 ≤ Nat.card E → E = miyamotoA1 h) :=
  card_le_and_eq_A1_of_commute h hE fun x hx y hy => by
    simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)

end Abelian

section PullRank

variable [CharP K 2] {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem card_le_and_eq_A1G_of_commute {B : Subgroup G} (hB : B ≤ miyamotoPG h L η)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ (2 ^ f) ^ 4 ∧ ((2 ^ f) ^ 4 ≤ Nat.card B → B = miyamotoA1G h L η) := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_miyamotoPull h L η (hB.trans (miyamotoPull_le h L η _))
  have hMP : M ≤ miyamotoP h := (miyamotoPull_le_miyamotoPull_iff h L η hM).1 hB
  have key := card_le_and_eq_A1_of_commute h hMP ((commute_miyamotoPull_iff h L η hM).1 hcomm)
  rw [card_miyamotoPull h L η hM]
  exact ⟨key.1, fun hge => by rw [key.2 hge]⟩

end PullRank

end CFSG.LocalAnalysis.EvenBN.U4
