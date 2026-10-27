module

public import Certificates.Data.Kernel.A7Rad.Checks
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Positivity

public section

namespace CFSG.KC.A7Rad

open Equiv Finset CFSG.KC.Ord CFSG.KC.LQT.P

local notation "A7'" => alternatingGroup (Fin 7)

@[expose] def cd (x : A7') : ℕ := code (x : Perm (Fin 7))

theorem cd_mul (x y : A7') : cd (x * y) = mul 7 (cd x) (cd y) := (code_mul (by norm_num) _ _).symm

theorem cd_one : cd 1 = one 7 := code_one.symm

theorem cd_inv (x : A7') : cd x⁻¹ = inv 7 (cd x) := (code_inv (by norm_num) _).symm

theorem cd_pow (x : A7') (k : ℕ) : cd (x ^ k) = pow 7 (cd x) k := by
  rw [cd, cd, Subgroup.coe_pow, code_pow (by norm_num)]

theorem cd_conj (g x : A7') : cd (g * x * g⁻¹) = conj 7 (cd g) (cd x) :=
  (conj_code (by norm_num) _ _).symm

theorem cd_inj {x y : A7'} (h : cd x = cd y) : x = y := Subtype.ext (code_inj (by norm_num) h)

variable {L n : ℕ}

theorem memP_iff {c : ℕ} : memP L n c = true ↔ ∃ k < n, fld L k = c := by
  rw [memP, anyN_iff]
  simp only [beq_iff]

theorem closedB_iff : closedB L n = true ↔ memP L n (one 7) = true ∧
    (∀ i < n, ∀ j < n, memP L n (mul 7 (fld L i) (fld L j)) = true) ∧
    ∀ i < n, memP L n (inv 7 (fld L i)) = true := by
  simp only [closedB, andB_iff, allN_iff]

theorem validB_iff : validB L n = true ↔ (∀ i < n, ∀ j < i, fld L i ≠ fld L j) ∧
    ∀ k < n, permK 7 (fld L k) = true ∧ even 7 (fld L k) = true := by
  simp only [validB, nodupB, andB_iff, allN_iff, notB_iff, beq_iff]

theorem exists_of_valid (hv : validB L n = true) {k : ℕ} (hk : k < n) : ∃ x : A7', cd x = fld L k := by
  obtain ⟨hp, he⟩ := (validB_iff.1 hv).2 k hk
  obtain ⟨σ, hσ⟩ := exists_of_permK hp
  rw [← hσ, even_code (by norm_num)] at he
  exact ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 he⟩, hσ⟩

@[expose] def subP (L n : ℕ) (h : closedB L n = true) : Subgroup A7' where
  carrier := {x | memP L n (cd x) = true}
  one_mem' := by
    change memP L n (cd 1) = true
    rw [cd_one]
    exact (closedB_iff.1 h).1
  mul_mem' := by
    intro a b ha hb
    change memP L n (cd (a * b)) = true
    obtain ⟨i, hi, ei⟩ := memP_iff.1 ha
    obtain ⟨j, hj, ej⟩ := memP_iff.1 hb
    rw [cd_mul, ← ei, ← ej]
    exact (closedB_iff.1 h).2.1 i hi j hj
  inv_mem' := by
    intro a ha
    change memP L n (cd a⁻¹) = true
    obtain ⟨i, hi, ei⟩ := memP_iff.1 ha
    rw [cd_inv, ← ei]
    exact (closedB_iff.1 h).2.2 i hi

theorem card_of_iff (hv : validB L n = true) {P : Subgroup A7'}
    (hP : ∀ x, x ∈ P ↔ memP L n (cd x) = true) : Nat.card P = n := by
  classical
  obtain ⟨hd, -⟩ := validB_iff.1 hv
  let S : Finset A7' := univ.filter fun x => memP L n (cd x) = true
  have hS : ∀ x, x ∈ P ↔ x ∈ S := fun x => by simp [S, hP]
  have e1 : Nat.card P = S.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hS), Nat.card_eq_fintype_card, Fintype.card_coe]
  have e2 : S.image cd = (range n).image (fld L) := by
    ext c
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range, S]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact memP_iff.1 hx
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨x, hx⟩ := exists_of_valid hv hk
      exact ⟨x, memP_iff.2 ⟨k, hk, hx.symm⟩, hx⟩
  have hinj : Set.InjOn (fld L) (range n : Finset ℕ) := by
    intro i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact absurd e.symm (hd j hj i hij)
    · exact hij
    · exact absurd e (hd i hi j hij)
  rw [e1, ← card_image_of_injective S (fun a b e => cd_inj e), e2, card_image_of_injOn hinj,
    card_range]

theorem card_subP (h : closedB L n = true) (hv : validB L n = true) : Nat.card (subP L n h) = n :=
  card_of_iff hv fun _ => Iff.rfl

theorem pow4_sound (h4 : pow4B L n = true) {x : A7'} (hx : memP L n (cd x) = true) : x ^ 4 = 1 := by
  obtain ⟨k, hk, e⟩ := memP_iff.1 hx
  apply cd_inj
  rw [cd_pow, cd_one, ← e]
  exact beq_iff.1 ((allN_iff _ _).1 h4 k hk)

theorem sub_sound {M m c : ℕ} (hs : subB L n M m = true) (hc : memP L n c = true) :
    memP M m c = true := by
  obtain ⟨k, hk, rfl⟩ := memP_iff.1 hc
  exact (allN_iff _ _).1 hs k hk

theorem nonab_sound (hv : validB L n = true) (h : nonabB L n = true) :
    ∃ a b : A7', memP L n (cd a) = true ∧ memP L n (cd b) = true ∧ a * b ≠ b * a := by
  obtain ⟨i, hi, h⟩ := (anyN_iff _ _).1 h
  obtain ⟨j, hj, h⟩ := (anyN_iff _ _).1 h
  obtain ⟨a, ea⟩ := exists_of_valid hv hi
  obtain ⟨b, eb⟩ := exists_of_valid hv hj
  refine ⟨a, b, memP_iff.2 ⟨i, hi, ea.symm⟩, memP_iff.2 ⟨j, hj, eb.symm⟩, fun hab => ?_⟩
  rw [← ea, ← eb, notB_iff] at h
  exact h ((comm_code (by norm_num) _ _).2 (congrArg Subtype.val hab))

theorem conj_sound {T m : ℕ} (h : conjB T m L n = true) {t x : A7'} (ht : memP T m (cd t) = true)
    (hx : memP L n (cd x) = true) : memP L n (cd (t * x * t⁻¹)) = true := by
  obtain ⟨i, hi, ei⟩ := memP_iff.1 ht
  obtain ⟨j, hj, ej⟩ := memP_iff.1 hx
  rw [cd_conj, ← ei, ← ej]
  exact (allN_iff _ _).1 ((allN_iff _ _).1 h i hi) j hj

theorem ex_sound {T m : ℕ} (hv : validB T m = true) (h : exB T m L n = true) :
    ∃ t : A7', memP T m (cd t) = true ∧ ¬ memP L n (cd t) = true := by
  obtain ⟨i, hi, h⟩ := (anyN_iff _ _).1 h
  obtain ⟨t, et⟩ := exists_of_valid hv hi
  rw [notB_iff, ← et] at h
  exact ⟨t, memP_iff.2 ⟨i, hi, et.symm⟩, h⟩

theorem norm_sound {T m z : ℕ} (hv : validB L n = true) (h : normB L n T m z = true) (g : A7')
    (hg : ∀ x : A7', memP L n (cd x) = true → memP L n (cd (g * x * g⁻¹)) = true) {t : A7'}
    (ht : memP T m (cd t) = true) : memP T m (cd (g * t * g⁻¹)) = true := by
  rw [normB, invU, andB_iff, andB_iff, andB_iff, beq_iff, allN_iff] at h
  obtain ⟨⟨hz, hzz, hu⟩, hC⟩ := h
  obtain ⟨k0, hk0, e0⟩ := memP_iff.1 hz
  obtain ⟨ζ, hζ⟩ := exists_of_valid hv hk0
  rw [e0] at hζ
  subst hζ
  have hζ2 : ζ * ζ = 1 := cd_inj (by rw [cd_mul, cd_one, hzz])
  have hfix : g * ζ * g⁻¹ = ζ := by
    by_cases h1 : g * ζ * g⁻¹ = 1
    · have : ζ = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) h1
        simpa [mul_assoc] using this
      rw [h1, this]
    · obtain ⟨k, hk, ek⟩ := memP_iff.1 (hg ζ hz)
      have := hu k hk
      rw [letB_eq, impB_iff, andB_iff, notB_iff, beq_iff, beq_iff, beq_iff, ek] at this
      refine cd_inj (this ⟨fun e => h1 (cd_inj (e.trans cd_one.symm)), ?_⟩)
      have hw : g * ζ * g⁻¹ * (g * ζ * g⁻¹) = 1 := by
        calc g * ζ * g⁻¹ * (g * ζ * g⁻¹) = g * (ζ * ζ) * g⁻¹ := by group
          _ = 1 := by rw [hζ2, mul_one, mul_inv_cancel]
      rw [← cd_mul, ← cd_one, hw]
  have hcomm : (g : Perm (Fin 7)) * ζ = ζ * g := by
    have : g * ζ = ζ * g := by
      calc g * ζ = g * ζ * g⁻¹ * g := by group
        _ = ζ * g := by rw [hfix]
    exact congrArg Subtype.val this
  have hf := (allC_iff (by norm_num) (ζ : Perm (Fin 7)) _).1 hC g hcomm
  rw [impB_iff, impB_iff, allN_iff, allN_iff] at hf
  have hev : even 7 (code (g : Perm (Fin 7))) = true :=
    (even_code (by norm_num) _).2 (Equiv.Perm.mem_alternatingGroup.1 g.2)
  have hP : ∀ i < n, memP L n (conj 7 (code (g : Perm (Fin 7))) (fld L i)) = true := by
    intro i hi
    obtain ⟨x, ex⟩ := exists_of_valid hv hi
    rw [← ex]
    exact (cd_conj g x) ▸ hg x (memP_iff.2 ⟨i, hi, ex.symm⟩)
  obtain ⟨j, hj, ej⟩ := memP_iff.1 ht
  have := hf hev hP j hj
  rw [ej] at this
  rw [cd_conj]
  exact this

theorem three_sound {W : ℕ} (hv : validB L n = true) (h : threeB L n W = true) {x : A7'}
    (hx : memP L n (cd x) = true) (hx1 : x ≠ 1) {y : A7'} (hy : memP L n (cd y) = true) :
    ∃ a b c : A7', memP L n (cd a) = true ∧ memP L n (cd b) = true ∧ memP L n (cd c) = true ∧
      y = a * x * a⁻¹ * (b * x * b⁻¹) * (c * x * c⁻¹) := by
  obtain ⟨i, hi, ei⟩ := memP_iff.1 hx
  obtain ⟨j, hj, ej⟩ := memP_iff.1 hy
  have hrow := (allN_iff _ _).1 h i hi
  simp only [letB_eq, impB_iff, notB_iff, beq_iff, allN_iff, andB_iff, blt_iff] at hrow
  rw [ei] at hrow
  obtain ⟨ha, hb, hc, e⟩ := hrow (fun e => hx1 (cd_inj (e.trans cd_one.symm))) j hj
  obtain ⟨a, ea⟩ := exists_of_valid hv ha
  obtain ⟨b, eb⟩ := exists_of_valid hv hb
  obtain ⟨c, ec⟩ := exists_of_valid hv hc
  refine ⟨a, b, c, memP_iff.2 ⟨_, ha, ea.symm⟩, memP_iff.2 ⟨_, hb, eb.symm⟩,
    memP_iff.2 ⟨_, hc, ec.symm⟩, cd_inj ?_⟩
  rw [← ej, e, ← ea, ← eb, ← ec, cd_mul, cd_mul, cd_conj, cd_conj, cd_conj]

theorem simple_sound {W : ℕ} (h : closedB L n = true) (hv : validB L n = true)
    (hn : nonabB L n = true) (h3 : threeB L n W = true) : IsSimpleGroup ↥(subP L n h) := by
  rw [Subgroup.isSimpleGroup_iff]
  refine ⟨?_, ?_⟩
  · intro hbot
    obtain ⟨a, b, ha, -, hab⟩ := nonab_sound hv hn
    have h1 : a ∈ subP L n h := ha
    rw [hbot, Subgroup.mem_bot] at h1
    exact hab (by rw [h1]; simp)
  · intro H' hH' hN
    by_cases hbot : H' = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨⟨x, hxH'⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      have hx1 : x ≠ 1 := fun e => hne (Subtype.ext e)
      have hxS : memP L n (cd x) = true := hH' hxH'
      have hconj : ∀ a, memP L n (cd a) = true → a * x * a⁻¹ ∈ H' := fun a ha =>
        (Subgroup.normal_subgroupOf_iff hH').1 hN x a hxH' ha
      refine le_antisymm hH' fun y hy => ?_
      obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := three_sound hv h3 hxS hx1 hy
      exact H'.mul_mem (H'.mul_mem (hconj a ha) (hconj b hb)) (hconj c hc)

theorem bitB_iff (m k : ℕ) : bitB m k = true ↔ m / 2 ^ k % 2 = 1 := by
  rw [bitB, beq_iff]
  change (m >>> k) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem mkM_succ (b : ℕ → Bool) (K : ℕ) :
    mkM b (K + 1) = mkM b K + (if b K = true then 1 else 0) * 2 ^ K := by
  change Nat.add (mkM b K) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 K) (b K)) = _
  rcases b K with _ | _
  · simp
  · simp [Nat.shiftLeft_eq]

theorem mkM_lt (b : ℕ → Bool) (K : ℕ) : mkM b K < 2 ^ K := by
  induction K with
  | zero => exact Nat.zero_lt_one
  | succ K ih =>
    rw [mkM_succ, pow_succ]
    split_ifs <;> omega

theorem mkM_digit (b : ℕ → Bool) {K k : ℕ} (hk : k < K) :
    mkM b K / 2 ^ k % 2 = if b k = true then 1 else 0 := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [mkM_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have e : (if b K = true then 1 else 0) * 2 ^ K =
          ((if b K = true then 1 else 0) * 2 ^ (K - k - 1)) * 2 * 2 ^ k := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
        congr 2
        omega
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact ih hk
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (mkM_lt b _), zero_add]
      split_ifs <;> rfl

theorem bitB_mkM (b : ℕ → Bool) {K k : ℕ} (hk : k < K) : bitB (mkM b K) k = true ↔ b k = true := by
  rw [bitB_iff, mkM_digit b hk]
  split_ifs with h <;> simp [h]

variable {D d : ℕ}

theorem lat_sound {ms : List ℕ} (hl : latB D d ms = true) (hD : closedB D d = true)
    {Q : Subgroup A7'} (hQ : Q ≤ subP D d hD) :
    ∃ m ∈ ms, ∀ k < d, bitB m k = true ↔ ∃ x ∈ Q, cd x = fld D k := by
  classical
  let b : ℕ → Bool := fun k => decide (∃ x ∈ Q, cd x = fld D k)
  have hb : ∀ k < d, bitB (mkM b d) k = true ↔ ∃ x ∈ Q, cd x = fld D k := fun k hk => by
    rw [bitB_mkM b hk]
    simp [b]
  have hmem : ∀ x ∈ Q, ∃ k < d, bitB (mkM b d) k = true ∧ fld D k = cd x := fun x hx => by
    obtain ⟨k, hk, e⟩ := memP_iff.1 (hQ hx)
    exact ⟨k, hk, (hb k hk).2 ⟨x, hx, e.symm⟩, e⟩
  have hc : closedM D d (mkM b d) = true := by
    simp only [closedM, andB_iff, anyN_iff, allN_iff, impB_iff, beq_iff]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨k, hk, hbk, e⟩ := hmem 1 Q.one_mem
      exact ⟨k, hk, hbk, e.trans cd_one⟩
    · intro i hi hbi j hj hbj
      obtain ⟨x, hx, ex⟩ := (hb i hi).1 hbi
      obtain ⟨y, hy, ey⟩ := (hb j hj).1 hbj
      obtain ⟨k, hk, hbk, e⟩ := hmem _ (Q.mul_mem hx hy)
      exact ⟨k, hk, hbk, by rw [e, cd_mul, ex, ey]⟩
    · intro i hi hbi
      obtain ⟨x, hx, ex⟩ := (hb i hi).1 hbi
      obtain ⟨k, hk, hbk, e⟩ := hmem _ (Q.inv_mem hx)
      exact ⟨k, hk, hbk, by rw [e, cd_inv, ex]⟩
  have hlt : mkM b d < Nat.shiftLeft 1 d := by
    change mkM b d < 1 <<< d
    rw [Nat.one_shiftLeft]
    exact mkM_lt b d
  have := (allN_iff _ _).1 hl _ hlt
  rw [impB_iff] at this
  obtain ⟨m, hm, e⟩ := (anyL_iff _ _).1 (this hc)
  rw [beq_iff] at e
  exact ⟨m, hm, e ▸ hb⟩

theorem mem_of_mask {G nG : ℕ} (hD : closedB D d = true) {Q : Subgroup A7'} (hQ : Q ≤ subP D d hD)
    (hs : subB G nG D d = true)
    (hm : ∀ k < d, bitB (maskOf D d G nG) k = true ↔ ∃ x ∈ Q, cd x = fld D k) (x : A7') :
    x ∈ Q ↔ memP G nG (cd x) = true := by
  have hb : ∀ k < d, bitB (maskOf D d G nG) k = true ↔ memP G nG (fld D k) = true :=
    fun k hk => bitB_mkM _ hk
  constructor
  · intro hx
    obtain ⟨k, hk, e⟩ := memP_iff.1 (hQ hx)
    rw [← e]
    exact (hb k hk).1 ((hm k hk).2 ⟨x, hx, e.symm⟩)
  · intro hx
    obtain ⟨k, hk, e⟩ := memP_iff.1 (sub_sound hs hx)
    obtain ⟨y, hy, e'⟩ := (hm k hk).1 ((hb k hk).2 (e ▸ hx))
    rwa [cd_inj (e'.trans e)] at hy

end CFSG.KC.A7Rad

end
