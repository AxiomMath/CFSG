module

public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1
public import CFSG.ClassicalInvolution.Solomon73.YamakiTables
public import CFSG.ClassicalInvolution.Solomon73.YamakiZRig
public import Certificates.Certificate550821

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

section Checks


theorem a0EnumCheck_holds : a0EnumCheck () = true := Certificates.certificate550821.1

theorem a0AbelCheck_holds : a0AbelCheck () = true := Certificates.certificate550821.2.1

theorem hhatAlphaCheck_holds : hhatAlphaCheck () = true :=
  Certificates.certificate550821.2.2.1

theorem fourCheck_holds : fourCheck () = true := Certificates.certificate550821.2.2.2

theorem a0EnumCheck_spec :
    enumOK (enumA0 ()) (gA0 ()) = true ∧ (enumA0 ()).elems.size = 64 ∧
      (enumS0 ()).elems.size = 512 := by
  have h := a0EnumCheck_holds
  simp only [a0EnumCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Checks

section Words


theorem yword_nil : yword [] = 1 := by
  simp only [yword, List.map_nil, List.prod_nil]

theorem yword_cons (i : ℕ) (w : List ℕ) : yword (i :: w) = ysp i * yword w := by
  simp only [yword, List.map_cons, List.prod_cons]

theorem yword_append (v w : List ℕ) : yword (v ++ w) = yword v * yword w := by
  simp only [yword, List.map_append, List.prod_append]

theorem ysp_eq (i : Fin 12) : ysp i.val = yamakiSp i := by
  rw [ysp, dif_pos i.2]

theorem ysp_mul_self (i : ℕ) : ysp i * ysp i = 1 := by
  unfold ysp
  split_ifs
  · exact yamakiSp_mul_self _
  · exact mul_one 1

theorem yword_reverse_mul (w : List ℕ) : yword w.reverse * yword w = 1 := by
  induction w with
  | nil => rw [List.reverse_nil, yword_nil, mul_one]
  | cons i w ih =>
    rw [List.reverse_cons, yword_append, yword_cons, yword_cons, yword_nil, mul_one, mul_assoc,
      ← mul_assoc (ysp i), ysp_mul_self, one_mul, ih]

theorem inv_yword (w : List ℕ) : (yword w)⁻¹ = yword w.reverse :=
  (eq_inv_of_mul_eq_one_left (yword_reverse_mul w)).symm

theorem yword_conjWord (c x : List ℕ) :
    yword (conjWord c x) = yword c * yword x * (yword c)⁻¹ := by
  rw [conjWord, yword_append, yword_append, inv_yword]

theorem lt_of_mem_conjWord {c x : List ℕ} (hc : ∀ i ∈ c, i < 12) (hx : ∀ i ∈ x, i < 12) :
    ∀ i ∈ conjWord c x, i < 12 := by
  intro i hi
  simp only [conjWord, List.mem_append, List.mem_reverse] at hi
  rcases hi with (hi | hi) | hi
  · exact hc i hi
  · exact hx i hi
  · exact hc i hi

theorem yword_pi12 : yword [4] = pi12 := by
  rw [yword_cons, yword_nil, mul_one]
  exact ysp_eq 4

theorem yword_pi3 : yword [5, 4] = pi3 := by
  rw [yword_cons, yword_pi12]
  exact congrArg (· * pi12) (ysp_eq 5)

theorem code_alpha : code alpha = (genA ())[5]! := code_yamakiSp 5

end Words

section Enum

theorem exists_lt_of_lookup {E : Enum} {x : StatedSp 3 (ZMod 2)}
    (h : (E.lookup (code x)).isSome) : ∃ i < E.elems.size, E.elems[i]! = code x := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  exact ⟨i, (Enum.lookup_spec hi).1, (Enum.lookup_spec hi).2⟩


@[expose] def a0Gen (j : ℕ) : StatedSp 3 (ZMod 2) := ysp (j + 3)

theorem size_gA0 : (gA0 ()).size = 6 := by
  simp only [gA0, Array.size_ofFn]

theorem gA0_get : ∀ j < (gA0 ()).size, (gA0 ())[j]! = code (a0Gen j) := by
  intro j hj
  rw [size_gA0] at hj
  rw [a0Gen, code_ysp (show j + 3 < 12 by omega)]
  simp only [gA0]
  rw [getElem!_ofFn_nat _ hj]

theorem A0_eq_closure : A0 = Subgroup.closure (a0Gen '' Set.Iio (gA0 ()).size) := by
  rw [size_gA0, A0]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Iio]
  constructor
  · rintro ⟨i, ⟨h₁, h₂⟩, rfl⟩
    refine ⟨i.val - 3, by omega, ?_⟩
    rw [a0Gen, ysp, dif_pos (show i.val - 3 + 3 < 12 by omega)]
    exact congrArg yamakiSp (Fin.ext (show i.val - 3 + 3 = i.val by omega))
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j + 3, by omega⟩, ⟨show 3 ≤ j + 3 by omega, show j + 3 ≤ 8 by omega⟩,
      by rw [a0Gen, ysp, dif_pos (show j + 3 < 12 by omega)]⟩

end Enum

section EnumA0


theorem mem_A0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ A0 ↔ ((enumA0 ()).lookup (code x)).isSome := by
  rw [A0_eq_closure]
  exact mem_closure_iff_isSome gA0_get a0EnumCheck_spec.1 x

theorem exists_lt_of_mem_A0 {x : StatedSp 3 (ZMod 2)} (hx : x ∈ A0) :
    ∃ i < (enumA0 ()).elems.size, (enumA0 ()).elems[i]! = code x :=
  exists_lt_of_lookup ((mem_A0_iff_isSome x).mp hx)

theorem card_A0 : Nat.card A0 = 64 := by
  rw [A0_eq_closure, card_closure_eq gA0_get a0EnumCheck_spec.1, a0EnumCheck_spec.2.1]

theorem isE64_A0 : IsE64 A0 := by
  have hab := a0AbelCheck_holds
  simp only [a0AbelCheck, allLt_iff, Bool.and_eq_true, decide_eq_true_eq] at hab
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, card_A0⟩
  · obtain ⟨i, hi, hia⟩ := exists_lt_of_mem_A0 ha
    obtain ⟨j, hj, hjb⟩ := exists_lt_of_mem_A0 hb
    apply code_injective
    rw [code_mul, code_mul, ← hia, ← hjb]
    exact (hab i hi).2 j hj
  · obtain ⟨i, hi, hia⟩ := exists_lt_of_mem_A0 ha
    apply code_injective
    rw [code_mul, ← hia, code_one]
    exact (hab i hi).1

end EnumA0

section EnumS0


theorem mem_S0_iff_isSome (x : StatedSp 3 (ZMod 2)) :
    x ∈ S0 ↔ ((enumS0 ()).lookup (code x)).isSome := by
  rw [S0_eq_closure]
  exact mem_closure_iff_isSome gS0_get enumS0_ok_holds x

theorem exists_lt_of_mem_S0 {x : StatedSp 3 (ZMod 2)} (hx : x ∈ S0) :
    ∃ i < (enumS0 ()).elems.size, (enumS0 ()).elems[i]! = code x :=
  exists_lt_of_lookup ((mem_S0_iff_isSome x).mp hx)

theorem card_S0 : Nat.card S0 = 512 := by
  rw [S0_eq_closure, card_closure_eq gS0_get enumS0_ok_holds, a0EnumCheck_spec.2.2]

end EnumS0

section Centralizer


theorem Hhat_le_centralizer_alpha :
    Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))) := by
  have h := hhatAlphaCheck_holds
  simp only [hhatAlphaCheck, List.all_eq_true, decide_eq_true_eq] at h
  rw [Hhat, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply code_injective
  rw [code_mul, code_mul, code_alpha, code_yamakiSp]
  exact h i.val (mem_idxHhat hi)

end Centralizer

section Four

theorem exists_four_of_commute {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    ∃ D : Subgroup G, (D : Set G) = {1, x, y, x * y} ∧ Nat.card D = 4 := by
  have hxyx : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have hxyy : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyxy : y * (x * y) = x := by rw [hxy, ← mul_assoc, hy, one_mul]
  have hxyxy : x * y * (x * y) = 1 := by rw [← mul_assoc, hxyx, hy]
  have hmul : ∀ a ∈ ({1, x, y, x * y} : Set G), ∀ b ∈ ({1, x, y, x * y} : Set G),
      a * b ∈ ({1, x, y, x * y} : Set G) := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, hx, hy, hxyx, hxyy, hxxy, hyxy, hxyxy, ← hxy,
        eq_self_iff_true, true_or, or_true]
  have hsq : ∀ a ∈ ({1, x, y, x * y} : Set G), a * a = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact hx
    · exact hy
    · exact hxyxy
  let D : Subgroup G :=
    { carrier := {1, x, y, x * y}
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := Set.mem_insert 1 _
      inv_mem' := fun {a} ha => by
        rw [inv_eq_of_mul_eq_one_right (hsq a ha)]
        exact ha }
  refine ⟨D, rfl, ?_⟩
  have hxy1 : x * y ≠ 1 := fun h => hne (by rw [eq_inv_of_mul_eq_one_left h,
    inv_eq_of_mul_eq_one_right hy])
  have hxxy' : x ≠ x * y := fun h => hy1 (by
    have := congrArg (x⁻¹ * ·) h
    simpa only [inv_mul_cancel, inv_mul_cancel_left] using this.symm)
  have hyxy' : y ≠ x * y := fun h => hx1 (by
    have := congrArg (· * y⁻¹) h
    simpa only [mul_inv_cancel, mul_inv_cancel_right] using this.symm)
  have h1 : (1 : G) ∉ ({x, y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1⟩
  have h2 : x ∉ ({y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hxxy'⟩
  change Nat.card ↥({1, x, y, x * y} : Set G) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1 (Set.toFinite _),
    Set.ncard_insert_of_notMem h2 (Set.toFinite _), Set.ncard_pair hyxy']


theorem exists_four_of_fourOK {xw c₁ c₂ : List ℕ} (hok : fourOK xw c₁ c₂ = true)
    (hxw : ∀ i ∈ xw, i ∈ idxHhat) (hxx : yword xw * yword xw = 1) :
    ∃ D : Subgroup (StatedSp 3 (ZMod 2)), D ≤ Hhat ∧ Nat.card D = 4 ∧
      (∀ d ∈ D, d * d = 1) ∧ ∀ d ∈ D, d ≠ 1 → ∃ c ∈ Hhat, c * yword xw * c⁻¹ = d := by
  simp only [fourOK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hw, hx1⟩, hyx⟩, hcomm⟩, hc₂⟩ := hok
  have hws := mem_of_wordsIn hw
  have hc₁H : ∀ i ∈ c₁, i ∈ idxHhat := hws c₁ (by simp)
  have hc₂H : ∀ i ∈ c₂, i ∈ idxHhat := hws c₂ (by simp)
  have hlt : ∀ {w : List ℕ}, (∀ i ∈ w, i ∈ idxHhat) → ∀ i ∈ w, i < 12 :=
    fun h i hi => (idxHhat_spec (h i hi)).1
  have hxH : yword xw ∈ Hhat := yword_mem_Hhat hxw
  have hc₁mem : yword c₁ ∈ Hhat := yword_mem_Hhat hc₁H
  have hc₂mem : yword c₂ ∈ Hhat := yword_mem_Hhat hc₂H
  have hcx : code (yword xw) = wordA (genA ()) xw := code_yword (hlt hxw)
  have hcz : code (yword c₂ * yword xw * (yword c₂)⁻¹) = wordA (genA ()) (conjWord c₂ xw) := by
    rw [← yword_conjWord, code_yword (lt_of_mem_conjWord (hlt hc₂H) (hlt hxw))]
  obtain ⟨y, hyd⟩ : ∃ y, yword c₁ * yword xw * (yword c₁)⁻¹ = y := ⟨_, rfl⟩
  have hcy : code y = wordA (genA ()) (conjWord c₁ xw) := by
    rw [← hyd, ← yword_conjWord, code_yword (lt_of_mem_conjWord (hlt hc₁H) (hlt hxw))]
  have hyH : y ∈ Hhat :=
    hyd ▸ Hhat.mul_mem (Hhat.mul_mem hc₁mem hxH) (Hhat.inv_mem hc₁mem)
  generalize yword xw = x at hcx hxx hyd hcz hxH ⊢
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [← hcx, h, code_one])
  have hyx' : y ≠ x := fun h => hyx (by rw [← hcy, ← hcx, h])
  have hxy : x * y = y * x :=
    code_injective (by rw [code_mul x y, code_mul y x, hcx, hcy]; exact hcomm)
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1'
    rwa [h, mul_inv_eq_one, mul_eq_left] at hyd
  have hyy : y * y = 1 := by
    rw [← hyd, show yword c₁ * x * (yword c₁)⁻¹ * (yword c₁ * x * (yword c₁)⁻¹) =
      yword c₁ * (x * x) * (yword c₁)⁻¹ by group, hxx, mul_one, mul_inv_cancel]
  have hz : yword c₂ * x * (yword c₂)⁻¹ = x * y :=
    code_injective (by rw [hcz, code_mul x y, hcx, hcy]; exact hc₂)
  obtain ⟨D, hD, hcard⟩ := exists_four_of_commute hxx hyy hxy hx1' hy1 (Ne.symm hyx')
  have hmem : ∀ d ∈ D, d = 1 ∨ d = x ∨ d = y ∨ d = x * y := by
    intro d hd
    have : d ∈ (D : Set (StatedSp 3 (ZMod 2))) := hd
    rw [hD] at this
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  refine ⟨D, fun d hd => ?_, hcard, fun d hd => ?_, fun d hd hd1 => ?_⟩
  · rcases hmem d hd with rfl | rfl | rfl | rfl
    · exact Hhat.one_mem
    · exact hxH
    · exact hyH
    · exact Hhat.mul_mem hxH hyH
  · rcases hmem d hd with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact hxx
    · exact hyy
    · rw [show x * y * (x * y) = x * (y * x) * y by group, ← hxy,
        show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, mul_one]
  · rcases hmem d hd with rfl | rfl | rfl | rfl
    · exact absurd rfl hd1
    · exact ⟨1, Hhat.one_mem, by rw [one_mul, inv_one, mul_one]⟩
    · exact ⟨yword c₁, hc₁mem, hyd⟩
    · exact ⟨yword c₂, hc₂mem, hz⟩


private theorem pi12_mul_self : pi12 * pi12 = 1 := yamakiSp_mul_self 4

private theorem pi3_mul_self : pi3 * pi3 = 1 := by
  have h : alpha * pi12 = pi12 * alpha :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Hhat_le_centralizer_alpha (S0_le_Hhat pi12_mem_S0))).symm
  rw [pi3, show alpha * pi12 * (alpha * pi12) = alpha * (pi12 * alpha) * pi12 by group, ← h,
    show alpha * (alpha * pi12) * pi12 = (alpha * alpha) * (pi12 * pi12) by group,
    pi12_mul_self, mul_one]
  exact yamakiSp_mul_self 5

theorem exists_four_conj {x : StatedSp 3 (ZMod 2)} (hx : x = pi12 ∨ x = pi3) :
    ∃ D : Subgroup (StatedSp 3 (ZMod 2)), D ≤ Hhat ∧ Nat.card D = 4 ∧ (∀ d ∈ D, d * d = 1) ∧
      ∀ d ∈ D, d ≠ 1 → ∃ c ∈ Hhat, c * x * c⁻¹ = d := by
  have h := fourCheck_holds
  simp only [fourCheck, Bool.and_eq_true] at h
  rcases hx with rfl | rfl
  · rw [← yword_pi12]
    exact exists_four_of_fourOK h.1 (by decide) (by rw [yword_pi12]; exact pi12_mul_self)
  · rw [← yword_pi3]
    exact exists_four_of_fourOK h.2 (by decide) (by rw [yword_pi3]; exact pi3_mul_self)

end Four

end CFSG.ClassicalInvolution.Sp62Rec
