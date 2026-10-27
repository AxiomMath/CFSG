module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace M12Model

open CFSG.Sporadic.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.M12Cover.SylowTable

@[expose] def letter {G : Type*} [Group G] (x y : G) (k : ℕ) : G :=
  if k = 0 then x else if k = 1 then y else y⁻¹

@[expose] def word {G : Type*} [Group G] (x y : G) (w : List ℕ) : G := (w.map (letter x y)).prod

theorem map_word {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) (w : List ℕ) :
    f (word x y w) = word (f x) (f y) w := by
  induction w with
  | nil => simp [word]
  | cons k w ih =>
    simp only [word, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    unfold letter
    split_ifs <;> simp

@[expose] def idC : List ℕ := List.range 12

theorem isCode_idC : IsCode idC 1 := isCode_one

@[expose] def lc (xc yc yic : List ℕ) (k : ℕ) : List ℕ :=
  if k = 0 then xc else if k = 1 then yc else yic

@[expose] def wc (xc yc yic : List ℕ) (w : List ℕ) : List ℕ :=
  w.foldr (fun k c => comp (lc xc yc yic k) c) idC

theorem isCode_word {xc yc yic : List ℕ} {x y : Equiv.Perm (Fin 12)} (hx : IsCode xc x)
    (hy : IsCode yc y) (hyi : IsCode yic y⁻¹) :
    ∀ w : List ℕ, IsCode (wc xc yc yic w) (word x y w)
  | [] => isCode_idC
  | k :: w => by
    change IsCode (comp (lc xc yc yic k) (wc xc yc yic w)) (letter x y k * word x y w)
    refine IsCode.mul ?_ (isCode_word hx hy hyi w)
    unfold lc letter
    split_ifs
    exacts [hx, hy, hyi]

@[expose] def aC : List ℕ := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def bC : List ℕ := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def biC : List ℕ := [8, 3, 1, 2, 10, 6, 9, 0, 7, 5, 11, 4]

theorem isCode_a : IsCode aC m12gA := ⟨rfl, by decide⟩

theorem isCode_ai : IsCode aC m12gA⁻¹ := ⟨rfl, by decide⟩

theorem isCode_b : IsCode bC m12gB := ⟨rfl, by decide⟩

theorem isCode_bi : IsCode biC m12gB⁻¹ := ⟨rfl, by decide⟩

@[expose] def abC (w : List ℕ) : List ℕ := wc aC bC biC w

@[expose] def wM (w : List ℕ) : NativeSporadic.M12 := word m12a m12b w

theorem coe_wM (w : List ℕ) : ((wM w : NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
    word m12gA m12gB w :=
  map_word NativeSporadic.M12.subtype m12a m12b w

theorem isCode_wM (w : List ℕ) : IsCode (abC w) (wM w : Equiv.Perm (Fin 12)) := by
  rw [coe_wM]
  exact isCode_word isCode_a isCode_b isCode_bi w

@[expose] def fixPts (σ : Equiv.Perm (Fin 12)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

@[expose] def codeFix (c : List ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin 12 => nth 0 c i = i).card

theorem fixPts_conj (g σ : Equiv.Perm (Fin 12)) : fixPts (g * σ * g⁻¹) = fixPts σ := by
  unfold fixPts
  refine Finset.card_equiv g.symm fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
  rw [Equiv.eq_symm_apply]

theorem fixPts_eq_codeFix {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ) :
    fixPts σ = codeFix c := by
  unfold fixPts codeFix
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  rw [h.2 i, Fin.ext_iff]

@[expose] def fp (q : NativeSporadic.M12) : ℕ := fixPts q

theorem fp_conj (g q : NativeSporadic.M12) : fp (g * q * g⁻¹) = fp q := by
  unfold fp
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact fixPts_conj _ _

section Codes

variable {c d e : List ℕ} {u v w : NativeSporadic.M12}

theorem isCode_mul (hu : IsCode c u) (hv : IsCode d v) :
    IsCode (comp c d) ((u * v : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
  rw [Subgroup.coe_mul]
  exact hu.mul hv

theorem eq_of_code (hu : IsCode c u) (hv : IsCode c v) : u = v :=
  Subtype.ext (hu.perm_eq hv)

theorem eq_one_of_code (hu : IsCode idC u) : u = 1 :=
  Subtype.ext (hu.perm_eq isCode_idC)

theorem mul_eq_of_code (hu : IsCode c u) (hv : IsCode d v) (hw : IsCode e w)
    (h : comp c d = e) : u * v = w :=
  eq_of_code (h ▸ isCode_mul hu hv) hw

theorem mul_eq_one_of_code (hu : IsCode c u) (hv : IsCode d v) (h : comp c d = idC) :
    u * v = 1 :=
  eq_one_of_code (h ▸ isCode_mul hu hv)

theorem ne_one_of_code (hu : IsCode c u) (h : c ≠ idC) : u ≠ 1 := by
  rintro rfl
  exact h (hu.code_eq isCode_idC)

theorem comm_of_code (hu : IsCode c u) (hv : IsCode d v) (h : comp c d = comp d c) :
    u * v = v * u :=
  eq_of_code (h ▸ isCode_mul hu hv) (isCode_mul hv hu)

theorem fp_of_code (hu : IsCode c u) : fp u = codeFix c := fixPts_eq_codeFix hu

theorem code_ne_of_ne_one (hu : IsCode c u) (h : u ≠ 1) : c ≠ idC := by
  rintro rfl
  exact h (eq_one_of_code hu)

theorem comp_eq_idC_of (hu : IsCode c u) (hv : IsCode d v) (h : u * v = 1) : comp c d = idC :=
  (isCode_mul hu hv).code_eq (by rw [h]; exact isCode_idC)

theorem comp_comm_of (hu : IsCode c u) (hv : IsCode d v) (h : u * v = v * u) :
    comp c d = comp d c :=
  (isCode_mul hu hv).code_eq (by rw [h]; exact isCode_mul hv hu)

theorem code_eq_of_eq (hu : IsCode c u) (hv : IsCode d v) (h : u = v) : c = d :=
  hu.code_eq (h ▸ hv)

end Codes

@[expose] def eltM (x : ℕ) : NativeSporadic.M12 := ⟨elt x, S_le_M12 (elt x).2⟩

theorem coe_eltM (x : ℕ) : ((eltM x : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = elt x := by
  unfold eltM
  rfl

theorem isCode_eltM {x : ℕ} (hx : x < 64) : IsCode (code x) (eltM x : Equiv.Perm (Fin 12)) := by
  rw [coe_eltM]
  exact isCode_elt x hx

theorem exists_eltM {s : NativeSporadic.M12} (hs : (s : Equiv.Perm (Fin 12)) ∈ S) :
    ∃ x < 64, eltM x = s := by
  obtain ⟨x, hx, hxe⟩ := exists_elt hs
  exact ⟨x, hx, Subtype.ext ((coe_eltM x).trans hxe)⟩

theorem mem_S_eltM (x : ℕ) : ((eltM x : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
  rw [coe_eltM]
  exact (elt x).2

theorem eltM_injective {x x' : ℕ} (hx : x < 64) (hx' : x' < 64) (h : eltM x = eltM x') :
    x = x' := by
  have h1 := congrArg Subtype.val h
  rw [coe_eltM, coe_eltM] at h1
  exact elt_injective hx hx' (Subtype.ext h1)

theorem eltM_mulIdx {x x' : ℕ} (hx : x < 64) (hx' : x' < 64) :
    mulIdx x x' < 64 ∧ eltM (mulIdx x x') = eltM x * eltM x' := by
  obtain ⟨h1, h2⟩ := mulIdx_spec hx hx'
  refine ⟨h1, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_eltM, coe_eltM, coe_eltM, h2, Subgroup.coe_mul]

theorem eltM_invIdx {x : ℕ} (hx : x < 64) : invIdx x < 64 ∧ (eltM x)⁻¹ = eltM (invIdx x) := by
  obtain ⟨h1, h2⟩ := elt_inv hx
  refine ⟨h1, Subtype.ext ?_⟩
  rw [Subgroup.coe_inv, coe_eltM, coe_eltM, ← h2, Subgroup.coe_inv]

theorem eltM_zero : eltM 0 = 1 := by
  apply Subtype.ext
  rw [coe_eltM, elt_zero, Subgroup.coe_one, Subgroup.coe_one]

theorem eltM_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 64) :
    gen x < 3 ∧ par x < x ∧ eltM x = eltM (gen x + 1) * eltM (par x) := by
  obtain ⟨hp, hg, -⟩ := tree_spec hx0 hx
  refine ⟨hg, hp, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_eltM, coe_eltM, coe_eltM, elt_cons hx0 hx, elt_succ hg,
    Subgroup.coe_mul]

theorem exists_conj_mem_S_of_isPGroup
    {H : Subgroup NativeSporadic.M12} (hH : IsPGroup 2 H) :
    ∃ g : NativeSporadic.M12, ∀ h ∈ H,
      ((g⁻¹ * h * g : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.M12 sylow P
  refine ⟨g, fun h hh => ?_⟩
  have hqP : h ∈ (P : Subgroup NativeSporadic.M12) := hP hh
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hqP
  obtain ⟨s, hs, rfl⟩ := hqP
  rw [coe_sylow, Subgroup.mem_subgroupOf] at hs
  rw [MulAut.smul_def, MulAut.conj_apply]
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hs

theorem exists_conj_eltM {k : NativeSporadic.M12} {n : ℕ}
    (hk : orderOf k = 2 ^ n) : ∃ g : NativeSporadic.M12, ∃ x < 64, g⁻¹ * k * g = eltM x := by
  have hp : IsPGroup 2 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hk])
  obtain ⟨g, hg⟩ := exists_conj_mem_S_of_isPGroup hp
  obtain ⟨x, hx, hxe⟩ := exists_eltM (hg k (Subgroup.mem_zpowers k))
  exact ⟨g, x, hx, hxe.symm⟩

theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {x : G} (h2 : x * x = 1) (h1 : x ≠ 1) :
    orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h2) h1

theorem orderOf_conj_inv {G : Type*} [Group G] (g k : G) : orderOf (g⁻¹ * k * g) = orderOf k := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) k
  rwa [MulAut.conj_apply, inv_inv] at h

@[expose] def conjData : List (ℕ × List ℕ × Bool) :=
  [(1, [], false), (2, [2,0,2,0,2,0,2,0,2,0,1,0,1,0], false), (3, [0,1,0,1,0,2,0,2,0], true),
   (10, [0,1,0,2,0,2,0,2,0,2,0], false), (12, [0,2,0,2,0,1,0,1,0,2], true),
   (14, [1,0,1,0,1,0,2,0,2,0,2], false), (17, [0,1,0,2,0,1,0,2,0,1,0], true),
   (19, [0,1,0,2,0,1,0,2,0,2,0,2,0,1], false), (21, [2,0,2,0,1,0,1,0,1,0,2,0,1], false),
   (22, [], true), (29, [1,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0], false), (34, [1,0,2,0,2,0,1,0], false),
   (36, [2,0,1,0,1], true), (42, [0,1,0,2,0,2,0,2,0,1], true), (44, [1,0,2,0,2,0,1,0,1,0], true),
   (45, [1,0,2,0,1,0,2,0,2], true), (46, [0,2,0,2,0,1,0,1,0,1,0,1,0,1], true),
   (47, [0,1,0,2,0], true), (50, [0,1,0,1,0,2,0,2,0,2,0], true),
   (51, [1,0,2,0,1,0,2,0,2,0,1,0,1,0], false), (52, [0,1,0,1,0,2,0,2,0,2,0,1,0,1], true),
   (53, [0,1,0,1,0,1,0,2,0,2,0], true), (54, [0,1,0,2,0,2,0,1,0,1], true),
   (58, [2,0,2,0,1,0,1,0,2], false), (59, [0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,1,0], false),
   (60, [2,0,2,0,1], true), (63, [0,1,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0], false)]

@[expose] def classCheck : Bool :=
  (List.range 64).all fun x =>
    code x == idC || comp (code x) (code x) != idC ||
      conjData.any fun d => d.1 == x &&
        comp (abC d.2.1) (code x) == comp (bif d.2.2 then code 22 else code 1) (abC d.2.1)

theorem classCheck_eq : classCheck = true := by decide +kernel

theorem exists_conj_of_lt {x : ℕ} (hx : x < 64) (h2 : eltM x * eltM x = 1) (h1 : eltM x ≠ 1) :
    ∃ c : NativeSporadic.M12, c * eltM x * c⁻¹ = eltM 22 ∨ c * eltM x * c⁻¹ = eltM 1 := by
  have hc := isCode_eltM hx
  have h := List.all_eq_true.1 classCheck_eq x (List.mem_range.2 hx)
  have hne : (code x == idC) = false := by
    rw [beq_eq_false_iff_ne]
    exact code_ne_of_ne_one hc h1
  have hsq : (comp (code x) (code x) != idC) = false := by
    rw [bne_eq_false_iff_eq]
    exact comp_eq_idC_of hc hc h2
  rw [hne, hsq, Bool.false_or, Bool.false_or, List.any_eq_true] at h
  obtain ⟨⟨x', w, b⟩, -, hd⟩ := h
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hd
  have key : ∀ r, r < 64 → comp (abC w) (code x) = comp (code r) (abC w) →
      wM w * eltM x * (wM w)⁻¹ = eltM r := by
    intro r hr he
    have : wM w * eltM x = eltM r * wM w :=
      eq_of_code (he ▸ isCode_mul (isCode_wM w) hc) (isCode_mul (isCode_eltM hr) (isCode_wM w))
    rw [this]
    group
  refine ⟨wM w, ?_⟩
  cases b
  · exact Or.inr (key 1 (by norm_num) hd.2)
  · exact Or.inl (key 22 (by norm_num) hd.2)

theorem fp_eltM {x : ℕ} (hx : x < 64) : fp (eltM x) = codeFix (code x) :=
  fp_of_code (isCode_eltM hx)

theorem fp_eltM_22 : fp (eltM 22) = 4 := by
  rw [fp_eltM (by norm_num)]
  decide +kernel

theorem fp_eltM_1 : fp (eltM 1) = 0 := by
  rw [fp_eltM (by norm_num)]
  decide +kernel

theorem inv_conj (q : NativeSporadic.M12) (h2 : q * q = 1)
    (h1 : q ≠ 1) : (∃ g : NativeSporadic.M12, g * eltM 22 * g⁻¹ = q) ∨
      ∃ g : NativeSporadic.M12, g * eltM 1 * g⁻¹ = q := by
  obtain ⟨g, x, hx, hgx⟩ := exists_conj_eltM (n := 1)
    (by rw [pow_one]; exact orderOf_eq_two_of_mul_self h2 h1)
  have hq : q = g * eltM x * g⁻¹ := by rw [← hgx]; group
  have hx2 : eltM x * eltM x = 1 := by
    rw [← hgx]
    calc g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g := by group
      _ = 1 := by rw [h2]; group
  have hx1 : eltM x ≠ 1 := by
    intro h
    apply h1
    rw [hq, h, mul_one, mul_inv_cancel]
  obtain ⟨c, hc | hc⟩ := exists_conj_of_lt hx hx2 hx1
  · exact Or.inl ⟨g * c⁻¹, by rw [← hc, hq]; group⟩
  · exact Or.inr ⟨g * c⁻¹, by rw [← hc, hq]; group⟩

theorem fp_inv (q : NativeSporadic.M12) (h2 : q * q = 1)
    (h1 : q ≠ 1) : fp q = 4 ∨ fp q = 0 := by
  rcases inv_conj q h2 h1 with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl (by rw [fp_conj, fp_eltM_22])
  · exact Or.inr (by rw [fp_conj, fp_eltM_1])

theorem conj_of_fp_eq {u v : NativeSporadic.M12}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hv2 : v * v = 1) (hv1 : v ≠ 1) (h : fp u = fp v) :
    ∃ x : NativeSporadic.M12, x * u * x⁻¹ = v := by
  rcases inv_conj u hu2 hu1 with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
    rcases inv_conj v hv2 hv1 with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * g⁻¹, by group⟩
  · rw [fp_conj, fp_conj, fp_eltM_22, fp_eltM_1] at h
    exact absurd h (by norm_num)
  · rw [fp_conj, fp_conj, fp_eltM_22, fp_eltM_1] at h
    exact absurd h (by norm_num)
  · exact ⟨k * g⁻¹, by group⟩

theorem mul_self_ne_one_of_orderOf_four {G : Type*} [Group G] {k : G} (hk : orderOf k = 4) :
    k * k ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one (show k ^ 2 = 1 by rw [sq]; exact h)
  rw [hk] at this
  norm_num at this

theorem mul_self_mul_self_of_orderOf_four {G : Type*} [Group G] {k : G} (hk : orderOf k = 4) :
    k * k * (k * k) = 1 := by
  have h : k ^ 4 = 1 := hk ▸ pow_orderOf_eq_one k
  calc k * k * (k * k) = k ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h

@[expose] def sqCheck : Bool :=
  (List.range 64).all fun x =>
    comp (code x) (code x) == idC ||
      comp (comp (code x) (code x)) (comp (code x) (code x)) != idC ||
      codeFix (comp (code x) (code x)) == 4

theorem sqCheck_eq : sqCheck = true := by decide +kernel

theorem code_sq_of_orderOf_four {x : ℕ} (hx : x < 64) (hk : orderOf (eltM x) = 4) :
    (comp (code x) (code x) == idC) = false ∧
      (comp (comp (code x) (code x)) (comp (code x) (code x)) != idC) = false := by
  have hc := isCode_eltM hx
  refine ⟨?_, ?_⟩
  · rw [beq_eq_false_iff_ne]
    exact code_ne_of_ne_one (isCode_mul hc hc) (mul_self_ne_one_of_orderOf_four hk)
  · rw [bne_eq_false_iff_eq]
    exact comp_eq_idC_of (isCode_mul hc hc) (isCode_mul hc hc)
      (mul_self_mul_self_of_orderOf_four hk)

theorem fp_sq (k : NativeSporadic.M12) (hk : orderOf k = 4) :
    fp (k * k) = 4 := by
  obtain ⟨g, x, hx, hgx⟩ := exists_conj_eltM (n := 2) (by rw [hk]; norm_num)
  have hxk : orderOf (eltM x) = 4 := by rw [← hgx, orderOf_conj_inv, hk]
  obtain ⟨h1, h2⟩ := code_sq_of_orderOf_four hx hxk
  have h := List.all_eq_true.1 sqCheck_eq x (List.mem_range.2 hx)
  rw [h1, h2, Bool.false_or, Bool.false_or, beq_iff_eq] at h
  have hk' : k * k = g * (eltM x * eltM x) * g⁻¹ := by
    have : k = g * eltM x * g⁻¹ := by rw [← hgx]; group
    rw [this]
    group
  rw [hk', fp_conj, fp_of_code (isCode_mul (isCode_eltM hx) (isCode_eltM hx)), h]

theorem eltM_mul_eq {x y z : ℕ} (hx : x < 64) (hy : y < 64) (hz : z < 64)
    (h : comp (code x) (code y) = code z) : eltM x * eltM y = eltM z :=
  mul_eq_of_code (isCode_eltM hx) (isCode_eltM hy) (isCode_eltM hz) h

theorem eltM_mul_eq_one {x y : ℕ} (hx : x < 64) (hy : y < 64)
    (h : comp (code x) (code y) = idC) : eltM x * eltM y = 1 :=
  mul_eq_one_of_code (isCode_eltM hx) (isCode_eltM hy) h

theorem eltM_ne_one {x : ℕ} (hx : x < 64) (h : code x ≠ idC) : eltM x ≠ 1 :=
  ne_one_of_code (isCode_eltM hx) h

theorem eltM_four_sq : eltM 4 * eltM 4 = eltM 22 :=
  eltM_mul_eq (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

theorem eltM_22_sq : eltM 22 * eltM 22 = 1 :=
  eltM_mul_eq_one (by norm_num) (by norm_num) (by decide +kernel)

theorem eltM_22_ne_one : eltM 22 ≠ 1 := eltM_ne_one (by norm_num) (by decide +kernel)

theorem orderOf_eltM_four : orderOf (eltM 4) = 4 := by
  have h1 : ¬eltM 4 ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, eltM_four_sq]
    exact eltM_22_ne_one
  have h2 : eltM 4 ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    calc eltM 4 ^ 4 = eltM 4 * eltM 4 * (eltM 4 * eltM 4) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [eltM_four_sq, eltM_22_sq]
  exact orderOf_eq_prime_pow h1 h2

theorem exists_sq_of_fp {u : NativeSporadic.M12} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (h4 : fp u = 4) : ∃ k : NativeSporadic.M12, orderOf k = 4 ∧ k * k = u := by
  obtain ⟨g, rfl⟩ := conj_of_fp_eq eltM_22_sq eltM_22_ne_one hu2 hu1 (by rw [fp_eltM_22, h4])
  refine ⟨g * eltM 4 * g⁻¹, ?_, ?_⟩
  · have h := MulEquiv.orderOf_eq (MulAut.conj g) (eltM 4)
    rw [MulAut.conj_apply] at h
    rw [h, orderOf_eltM_four]
  · rw [← eltM_four_sq]
    group

theorem exists_sq_iff {u : NativeSporadic.M12} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : (∃ k : NativeSporadic.M12, orderOf k = 4 ∧ k * k = u) ↔ fp u = 4 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact fp_sq k hk
  · exact exists_sq_of_fp hu2 hu1

theorem conj_sq_of_fp {k u : NativeSporadic.M12}
    (hk : orderOf k = 4) (hu2 : u * u = 1) (hu1 : u ≠ 1) (h4 : fp u = 4) :
    ∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = u :=
  conj_of_fp_eq (mul_self_mul_self_of_orderOf_four hk) (mul_self_ne_one_of_orderOf_four hk) hu2
    hu1 (by rw [fp_sq k hk, h4])

@[expose] def isB (c : List ℕ) : Bool := c != idC && comp c c == idC && codeFix c == 4

@[expose] def prodCheck : Bool :=
  (List.range 64).all fun x => !isB (code x) ||
    (List.range 64).all fun y => !isB (code y) || code x == code y ||
      comp (code x) (code y) != comp (code y) (code x) || codeFix (comp (code x) (code y)) == 4

theorem prodCheck_eq : prodCheck = true := by decide +kernel

theorem isB_eq_true {x : ℕ} (hx : x < 64) (h2 : eltM x * eltM x = 1) (h1 : eltM x ≠ 1)
    (h4 : fp (eltM x) = 4) : isB (code x) = true := by
  have hc := isCode_eltM hx
  unfold isB
  rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, beq_iff_eq]
  exact ⟨⟨code_ne_of_ne_one hc h1, comp_eq_idC_of hc hc h2⟩, by rw [← fp_of_code hc, h4]⟩

theorem conj_mul_self {G : Type*} [Group G] (g w : G) (hw : w * w = 1) :
    g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
  calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
    _ = 1 := by rw [hw]; group

theorem conj_ne_one {G : Type*} [Group G] (g w : G) (hw : w ≠ 1) : g⁻¹ * w * g ≠ 1 :=
  fun h => hw (by
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)

theorem fp_conj_inv (g w : NativeSporadic.M12) : fp (g⁻¹ * w * g) = fp w := by
  have := fp_conj g⁻¹ w
  rwa [inv_inv] at this

@[expose] def fourData : List (ℕ × List ℕ) :=
  [(4, [0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1]),
   (6, [0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1]),
   (7, [0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,1,0,1,0,1,0,1]),
   (9, [0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,1,0,1,0,1,0,1]),
   (23, [1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,0,1,0,2,0,2,0,1,0,1]),
   (24, [0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0]),
   (26, [2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,1,0,1]),
   (27, [0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1]),
   (28, [0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0]),
   (31, [2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,1,0,1]),
   (37, [1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,0,1,0,2,0,2,0,1,0,1]),
   (38, [0,2,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,2]),
   (39, [0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1]),
   (41, [0,2,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,2]),
   (48, [0,1,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,2,0,1]),
   (55, [0,1,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,2,0,1]),
   (56, [1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2]),
   (57, [1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2]),
   (61, [1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2]),
   (62, [1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2])]

@[expose] def fourCheck : Bool :=
  (List.range 64).all fun x =>
    comp (code x) (code x) == idC ||
      comp (comp (code x) (code x)) (comp (code x) (code x)) != idC ||
      fourData.any fun d => d.1 == x && (abC d.2 != idC && comp (abC d.2) (abC d.2) == idC &&
        codeFix (abC d.2) == 0 && comp (abC d.2) (code x) == comp (code x) (abC d.2))

theorem fourCheck_eq : fourCheck = true := by decide +kernel

theorem exists_w_comm {x : ℕ} (hx : x < 64) (hk : orderOf (eltM x) = 4) :
    ∃ u : NativeSporadic.M12, u * u = 1 ∧ u ≠ 1 ∧ fp u = 0 ∧ u * eltM x = eltM x * u := by
  obtain ⟨h1, h2⟩ := code_sq_of_orderOf_four hx hk
  have h := List.all_eq_true.1 fourCheck_eq x (List.mem_range.2 hx)
  rw [h1, h2, Bool.false_or, Bool.false_or, List.any_eq_true] at h
  obtain ⟨⟨x', w⟩, -, hd⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
  obtain ⟨-, ⟨⟨hw1, hw2⟩, hw0⟩, hwc⟩ := hd
  refine ⟨wM w, mul_eq_one_of_code (isCode_wM w) (isCode_wM w) hw2,
    ne_one_of_code (isCode_wM w) hw1, ?_, comm_of_code (isCode_wM w) (isCode_eltM hx) hwc⟩
  rw [fp_of_code (isCode_wM w), hw0]

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Certificates in
theorem rep1_class :
    (conjClosure 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹) (toTable m12Rep1)
      1000).1.size ≤ (conjClass NativeSporadic.M12 m12Rep1).ncard := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m12_oddcore_cover
  rw [m12InvReps_eq] at hok
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  obtain ⟨h1, h2, -⟩ := m12_rep_data1
  obtain ⟨h1', h2', -⟩ := m12_rep_data2
  have h := exists_conj_of_repsOK hn m12Certificate m12Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m12Rep1, m12Rep2] (fun r hr => by
      rw [inv_one, one_mul]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨h1, h2⟩
      · exact ⟨h1', h2'⟩) 1000 hok
  rw [m12Certificate_originalSubgroup] at h
  exact h.2 _ (by simp)

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Certificates in
theorem card_centralizerIn_rep1 :
    Nat.card (centralizerIn NativeSporadic.M12 m12Rep1) = 192 := by
  obtain ⟨-, -, hK, hKc, -⟩ := m12_rep_data1
  obtain ⟨-, hsz, -⟩ := m12_oddcore_cover
  rw [m12InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m12Certificate_originalSubgroup] at hK
  rw [centralizerIn_eq_of_le _ _ hK rep1_class (by rw [hsz.1, hKc, card_M12]), hKc]

theorem fixPts_rep1 : fixPts CFSG.Sporadic.Schreier.m12Rep1 = 4 := by decide +kernel

theorem card_centralizer_conj {G : Type*} [Group G] (g u : G) :
    Nat.card (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  refine (Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  constructor
  · intro h
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [h]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  · intro h
    calc x * u = g⁻¹ * (g * x * g⁻¹ * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
      _ = u * x := by group

open CFSG.Sporadic.Schreier in
theorem card_centralizer_z0 :
    Nat.card (Subgroup.centralizer ({eltM 22} : Set NativeSporadic.M12)) = 192 := by
  obtain ⟨h1, h2, -⟩ := m12_rep_data1
  rw [m12Certificate_originalSubgroup] at h1
  set r : NativeSporadic.M12 := ⟨m12Rep1, h1⟩
  have hro : orderOf r = 2 := by rw [Subgroup.orderOf_mk, h2]
  have hr2 : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hro, sq] at h
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hro
    exact absurd hro (by norm_num)
  obtain ⟨g, hg⟩ := conj_of_fp_eq hr2 hr1 eltM_22_sq eltM_22_ne_one
    (by rw [fp_eltM_22]; exact fixPts_rep1)
  rw [← hg, card_centralizer_conj, ← card_centralizerIn_rep1,
    ← map_centralizer_subtype NativeSporadic.M12 r,
    Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective]

@[expose] def d0Word : List ℕ := [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0]

@[expose] def d0 : NativeSporadic.M12 := wM d0Word

@[expose] def dPow (j : ℕ) : List ℕ :=
  if j = 0 then idC else if j = 1 then [11, 1, 3, 6, 0, 5, 2, 7, 10, 8, 9, 4]
  else [4, 1, 6, 2, 11, 5, 3, 7, 9, 10, 8, 0]

theorem isCode_d0 : IsCode (dPow 1) (d0 : Equiv.Perm (Fin 12)) := by
  have h := isCode_wM d0Word
  rwa [show abC d0Word = dPow 1 by decide +kernel] at h

theorem isCode_dPow {j : ℕ} (hj : j < 3) :
    IsCode (dPow j) ((d0 ^ j : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
  interval_cases j
  · rw [pow_zero]
    exact isCode_idC
  · rw [pow_one]
    exact isCode_d0
  · rw [sq]
    have h := isCode_mul isCode_d0 isCode_d0
    rwa [show comp (dPow 1) (dPow 1) = dPow 2 by decide +kernel] at h

@[expose] def czCheck : Bool :=
  (List.range 64).all (fun x => comp (code 22) (code x) == comp (code x) (code 22) &&
      code x != dPow 1 && code x != dPow 2) &&
    comp (code 22) (dPow 1) == comp (dPow 1) (code 22) && comp (dPow 1) (dPow 2) == idC

theorem czCheck_eq : czCheck = true := by decide +kernel

theorem czCheck_spec :
    (∀ x < 64, comp (code 22) (code x) = comp (code x) (code 22) ∧ code x ≠ dPow 1 ∧
      code x ≠ dPow 2) ∧ comp (code 22) (dPow 1) = comp (dPow 1) (code 22) ∧
      comp (dPow 1) (dPow 2) = idC := by
  have h := czCheck_eq
  simp only [czCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  exact ⟨fun x hx => ⟨(h.1.1 x hx).1.1, (h.1.1 x hx).1.2, (h.1.1 x hx).2⟩, h.1.2, h.2⟩

theorem d0_cube : d0 ^ 3 = 1 := by
  have h := mul_eq_one_of_code (isCode_dPow (j := 1) (by norm_num))
    (isCode_dPow (j := 2) (by norm_num)) czCheck_spec.2.2
  rwa [← pow_add] at h

theorem d0_comm : eltM 22 * d0 = d0 * eltM 22 :=
  comm_of_code (isCode_eltM (x := 22) (by norm_num)) isCode_d0 czCheck_spec.2.1

theorem eltM_comm_22 {x : ℕ} (hx : x < 64) : eltM x * eltM 22 = eltM 22 * eltM x :=
  (comm_of_code (isCode_eltM (x := 22) (by norm_num)) (isCode_eltM hx)
    (czCheck_spec.1 x hx).1).symm

theorem not_mem_S_dPow {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    ((d0 ^ j : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∉ S := by
  intro hS
  obtain ⟨x, hx, hxe⟩ := exists_eltM hS
  have hc := code_eq_of_eq (isCode_eltM hx) (isCode_dPow hj) hxe
  have := czCheck_spec.1 x hx
  interval_cases j
  · exact absurd rfl hj0
  · exact this.2.1 hc
  · exact this.2.2 hc

theorem cz_injective {i i' j j' : ℕ} (hi : i < 64) (hi' : i' < 64) (hj : j < 3) (hj' : j' < 3)
    (h : eltM i * d0 ^ j = eltM i' * d0 ^ j') : i = i' ∧ j = j' := by
  have key : (eltM i')⁻¹ * eltM i = d0 ^ j' * (d0 ^ j)⁻¹ := by
    calc (eltM i')⁻¹ * eltM i = (eltM i')⁻¹ * (eltM i * d0 ^ j) * (d0 ^ j)⁻¹ := by group
      _ = (eltM i')⁻¹ * (eltM i' * d0 ^ j') * (d0 ^ j)⁻¹ := by rw [h]
      _ = d0 ^ j' * (d0 ^ j)⁻¹ := by group
  have hS : (((eltM i')⁻¹ * eltM i : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact S.mul_mem (S.inv_mem (mem_S_eltM i')) (mem_S_eltM i)
  rw [key] at hS
  have hjj : j = j' := by
    have hinv : (d0 ^ j)⁻¹ = d0 ^ (2 * j) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add, show 2 * j + j = 3 * j by ring, pow_mul,
        d0_cube, one_pow]
    by_contra hne
    rw [hinv, ← pow_add] at hS
    have hmod : d0 ^ (j' + 2 * j) = d0 ^ ((j' + 2 * j) % 3) := by
      conv_lhs => rw [← Nat.div_add_mod (j' + 2 * j) 3, pow_add, pow_mul, d0_cube, one_pow,
        one_mul]
    rw [hmod] at hS
    exact not_mem_S_dPow (Nat.mod_lt _ (by norm_num)) (by omega) hS
  subst hjj
  exact ⟨eltM_injective hi hi' (mul_right_cancel h), rfl⟩

theorem mem_cz0
    (x : NativeSporadic.M12) (hx : x * eltM 22 = eltM 22 * x) :
    ∃ i < 64, ∃ j < 3, x = eltM i * d0 ^ j := by
  have hmem : ∀ p : Fin 64 × Fin 3, eltM p.1 * d0 ^ (p.2 : ℕ) ∈
      Subgroup.centralizer ({eltM 22} : Set NativeSporadic.M12) := by
    intro p
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := eltM_comm_22 p.1.2
    have h2 : d0 ^ (p.2 : ℕ) * eltM 22 = eltM 22 * d0 ^ (p.2 : ℕ) :=
      (Commute.pow_left (show Commute d0 (eltM 22) from d0_comm.symm) _).eq
    calc eltM p.1 * d0 ^ (p.2 : ℕ) * eltM 22 = eltM p.1 * (d0 ^ (p.2 : ℕ) * eltM 22) := by group
      _ = eltM p.1 * (eltM 22 * d0 ^ (p.2 : ℕ)) := by rw [h2]
      _ = eltM p.1 * eltM 22 * d0 ^ (p.2 : ℕ) := by group
      _ = eltM 22 * eltM p.1 * d0 ^ (p.2 : ℕ) := by rw [h1]
      _ = eltM 22 * (eltM p.1 * d0 ^ (p.2 : ℕ)) := by group
  let f : Fin 64 × Fin 3 → Subgroup.centralizer ({eltM 22} : Set NativeSporadic.M12) :=
    fun p => ⟨_, hmem p⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    obtain ⟨h1, h2⟩ := cz_injective i.2 i'.2 j.2 j'.2 (congrArg Subtype.val h)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hcard : Nat.card (Subgroup.centralizer ({eltM 22} : Set NativeSporadic.M12)) ≤
      Nat.card (Fin 64 × Fin 3) := by
    rw [card_centralizer_z0, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin]
  obtain ⟨⟨i, j⟩, hp⟩ := (hf.bijective_of_nat_card_le hcard).2
    ⟨x, Subgroup.mem_centralizer_singleton_iff.2 hx⟩
  exact ⟨i, i.2, j, j.2, (congrArg Subtype.val hp).symm⟩

@[expose] def czCode (i j : ℕ) : List ℕ := comp (code i) (dPow j)

theorem isCode_czCode {i j : ℕ} (hi : i < 64) (hj : j < 3) :
    IsCode (czCode i j) ((eltM i * d0 ^ j : NativeSporadic.M12) : Equiv.Perm (Fin 12)) :=
  isCode_mul (isCode_eltM hi) (isCode_dPow hj)

@[expose] def noTwelveCheck : Bool :=
  (List.range 64).all fun i => (List.range 3).all fun j =>
    comp (czCode i j) (czCode i j) != code 22 || (List.range 64).all fun i' =>
      (List.range 3).all fun j' =>
        czCode i' j' == idC || comp (czCode i' j') (comp (czCode i' j') (czCode i' j')) != idC ||
          comp (czCode i j) (czCode i' j') != comp (czCode i' j') (czCode i j)

theorem noTwelveCheck_eq : noTwelveCheck = true := by decide +kernel

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Certificates in
theorem card_pairs :
    Nat.card {p : NativeSporadic.M12 × NativeSporadic.M12 // orderOf p.1 = 2 ∧
      orderOf p.2 = 3 ∧ WordsRel m12AutWords p.1 p.2} = 190080 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, -, -⟩ := m12_oddcore_cover
  obtain ⟨-, -, -, htot⟩ := m12_oddcore_aut
  rw [m12InvReps_eq] at hok htot
  obtain ⟨hr1, hro1, -, -, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hpos : ∀ p ∈ m12AutWords, 0 < p.2 := by decide
  have hrepsA : ∀ r ∈ [m12Rep1, m12Rep2],
      r ∈ m12Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  have hcount := card_pairs_eq_repsTotal hn m12Certificate hQ (mx := 2) (my := 3) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [m12Rep1, m12Rep2] hrepsA 1000 hok
  rw [htot, m12Certificate_originalSubgroup] at hcount
  exact hcount

@[expose] def pc (c : List ℕ) : ℕ → List ℕ
  | 0 => idC
  | n + 1 => comp c (pc c n)

theorem isCode_pow {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ) :
    ∀ n, IsCode (pc c n) (σ ^ n)
  | 0 => by rw [pow_zero]; exact isCode_idC
  | n + 1 => by rw [pow_succ']; exact h.mul (isCode_pow h n)

@[expose] def ordC (c : List ℕ) (n : ℕ) : Bool :=
  pc c n == idC && (List.range n).all fun m => m == 0 || pc c m != idC

theorem orderOf_of_ordC {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ) {n : ℕ}
    (hn : 0 < n) (hc : ordC c n = true) : orderOf σ = n := by
  unfold ordC at hc
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  rw [orderOf_eq_iff hn]
  refine ⟨(isCode_pow h n).perm_eq (hc.1 ▸ isCode_idC), fun m hm hm0 he => ?_⟩
  have := hc.2 m (List.mem_range.2 hm)
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at this
  rcases this with h0 | hne
  · omega
  · exact hne ((isCode_pow h m).code_eq (he ▸ isCode_idC))

@[expose] def ewc (xc yc xic yic : List ℕ) (w : List ℕ) : List ℕ :=
  w.foldr (fun l c => comp (if l = 0 then xc else if l = 1 then yc else if l = 2 then xic
    else yic) c) idC

theorem isCode_evalW {xc yc xic yic : List ℕ} {x y : Equiv.Perm (Fin 12)} (hx : IsCode xc x)
    (hy : IsCode yc y) (hxi : IsCode xic x⁻¹) (hyi : IsCode yic y⁻¹) :
    ∀ w : List ℕ, IsCode (ewc xc yc xic yic w) (CFSG.Sporadic.Schreier.evalW x y w)
  | [] => isCode_idC
  | l :: w => by
    change IsCode (comp (if l = 0 then xc else if l = 1 then yc else if l = 2 then xic else yic)
      (ewc xc yc xic yic w)) (CFSG.Sporadic.Schreier.letterW x y l *
        CFSG.Sporadic.Schreier.evalW x y w)
    refine IsCode.mul ?_ (isCode_evalW hx hy hxi hyi w)
    unfold CFSG.Sporadic.Schreier.letterW
    split_ifs
    exacts [hx, hy, hxi, hyi]

@[expose] def bpWord : List ℕ :=
  [1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]

@[expose] def mbp : NativeSporadic.M12 := wM bpWord

@[expose] def bpC : List ℕ := [5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6]

@[expose] def bpiC : List ℕ := [3, 2, 8, 5, 9, 0, 11, 4, 1, 7, 6, 10]

theorem isCode_bp : IsCode bpC (mbp : Equiv.Perm (Fin 12)) := by
  have h := isCode_wM bpWord
  rwa [show abC bpWord = bpC by decide +kernel] at h

theorem mbp_inv : mbp⁻¹ = mbp * mbp :=
  (eq_inv_of_mul_eq_one_right (mul_eq_one_of_code isCode_bp (isCode_mul isCode_bp isCode_bp)
    (by decide +kernel))).symm

theorem isCode_bpi : IsCode bpiC (mbp : Equiv.Perm (Fin 12))⁻¹ := by
  rw [← Subgroup.coe_inv, mbp_inv]
  have h := isCode_mul isCode_bp isCode_bp
  rwa [show comp bpC bpC = bpiC by decide +kernel] at h

theorem coe_word (x y : NativeSporadic.M12) (w : List ℕ) :
    ((word x y w : NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
      word (x : Equiv.Perm (Fin 12)) (y : Equiv.Perm (Fin 12)) w :=
  map_word NativeSporadic.M12.subtype x y w

@[expose] def abpC (w : List ℕ) : List ℕ := wc aC bpC bpiC w

theorem isCode_word_bp (w : List ℕ) :
    IsCode (abpC w) ((word m12a mbp w : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
  rw [coe_word]
  exact isCode_word isCode_a isCode_bp isCode_bpi w

theorem isCode_word_b (w : List ℕ) :
    IsCode (abC w) ((word m12a m12b w : NativeSporadic.M12) : Equiv.Perm (Fin 12)) :=
  isCode_wM w

theorem hpos_autWords : ∀ p ∈ CFSG.Sporadic.Schreier.m12AutWords, 0 < p.2 := by decide

theorem wordsRel_of_codes {y : NativeSporadic.M12} {yc yic : List ℕ}
    (hy : IsCode yc (y : Equiv.Perm (Fin 12))) (hyi : IsCode yic (y : Equiv.Perm (Fin 12))⁻¹)
    (h : (CFSG.Sporadic.Schreier.m12AutWords.all fun p => ordC (ewc aC yc aC yic p.1) p.2) =
      true) : CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords m12a y := by
  rw [← CFSG.Sporadic.Schreier.wordsRel_coe]
  intro p hp
  exact orderOf_of_ordC (isCode_evalW isCode_a hy isCode_ai hyi p.1) (hpos_autWords p hp)
    (List.all_eq_true.1 h p hp)

theorem mem_pairs_ab : orderOf m12a = 2 ∧ orderOf m12b = 3 ∧
    CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords m12a m12b := by
  refine ⟨?_, ?_, wordsRel_of_codes isCode_b isCode_bi (by decide +kernel)⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_of_ordC isCode_a (by norm_num) (by decide +kernel)
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_of_ordC isCode_b (by norm_num) (by decide +kernel)

theorem mem_pairs_abp : orderOf m12a = 2 ∧ orderOf mbp = 3 ∧
    CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords m12a mbp := by
  refine ⟨mem_pairs_ab.1, ?_, wordsRel_of_codes isCode_bp isCode_bpi (by decide +kernel)⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_of_ordC isCode_bp (by norm_num) (by decide +kernel)

@[expose] def bOf (β : Bool) : NativeSporadic.M12 := bif β then mbp else m12b

theorem mem_pairs_bOf (β : Bool) : orderOf m12a = 2 ∧ orderOf (bOf β) = 3 ∧
    CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords m12a (bOf β) := by
  cases β
  · exact mem_pairs_ab
  · exact mem_pairs_abp

theorem mem_pairs_conj (g : NativeSporadic.M12) {x y : NativeSporadic.M12}
    (h : orderOf x = 2 ∧ orderOf y = 3 ∧
      CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords x y) :
    orderOf (g * x * g⁻¹) = 2 ∧ orderOf (g * y * g⁻¹) = 3 ∧
      CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords (g * x * g⁻¹)
        (g * y * g⁻¹) := by
  have e : ∀ z : NativeSporadic.M12, g * z * g⁻¹ = MulAut.conj g z :=
    fun z => (MulAut.conj_apply g z).symm
  rw [e, e, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, CFSG.Sporadic.Schreier.wordsRel_map]
  exact h

@[expose] noncomputable def pairOf (p : NativeSporadic.M12 × Bool) :
    {q : NativeSporadic.M12 × NativeSporadic.M12 // orderOf q.1 = 2 ∧ orderOf q.2 = 3 ∧
      CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords q.1 q.2} :=
  ⟨(p.1 * m12a * p.1⁻¹, p.1 * bOf p.2 * p.1⁻¹), mem_pairs_conj p.1 (mem_pairs_bOf p.2)⟩

theorem eq_one_of_comm_ab
    {c : NativeSporadic.M12} (ha : c * m12a = m12a * c) (hb : c * m12b = m12b * c) : c = 1 := by
  have htop : Subgroup.closure ({m12a, m12b} : Set NativeSporadic.M12) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top m12_eq _ _
  have hle : Subgroup.closure ({m12a, m12b} : Set NativeSporadic.M12) ≤
      Subgroup.centralizer {c} := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 ha.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hb.symm
  rw [htop] at hle
  have hc : c ∈ Subgroup.center NativeSporadic.M12 := Subgroup.mem_center_iff.2 fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  rw [CFSG.Sporadic.Schreier.m12_center_eq_bot', Subgroup.mem_bot] at hc
  exact hc

theorem conj_word_eq {c x y x' y' : NativeSporadic.M12} (hx : c * x * c⁻¹ = x')
    (hy : c * y * c⁻¹ = y') (w : List ℕ) : c * word x y w * c⁻¹ = word x' y' w := by
  have h := map_word (MulAut.conj c).toMonoidHom x y w
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [h, hx, hy]

@[expose] def bWord : List ℕ :=
  [1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]

theorem m12b_eq_word : m12b = word m12a mbp bWord :=
  eq_of_code isCode_b ((show abpC bWord = bC by decide +kernel) ▸ isCode_word_bp bWord)

@[expose] def distWord : List ℕ := [0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2]

theorem fp_dist_b : fp (word m12a m12b distWord) = 4 := by
  rw [fp_of_code (isCode_word_b distWord)]
  decide +kernel

theorem fp_dist_bp : fp (word m12a mbp distWord) = 0 := by
  rw [fp_of_code (isCode_word_bp distWord)]
  decide +kernel

theorem pairOf_injective :
    Function.Injective pairOf := by
  rintro ⟨g, β⟩ ⟨h, γ⟩ he
  have h1 := congrArg (fun q => q.1.1) he
  have h2 := congrArg (fun q => q.1.2) he
  simp only [pairOf] at h1 h2
  set c := h⁻¹ * g with hcdef
  have hca : c * m12a * c⁻¹ = m12a := by
    rw [hcdef]
    calc h⁻¹ * g * m12a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * m12a * g⁻¹) * h := by group
      _ = h⁻¹ * (h * m12a * h⁻¹) * h := by rw [h1]
      _ = m12a := by group
  have hcb : c * bOf β * c⁻¹ = bOf γ := by
    rw [hcdef]
    calc h⁻¹ * g * bOf β * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * bOf β * g⁻¹) * h := by group
      _ = h⁻¹ * (h * bOf γ * h⁻¹) * h := by rw [h2]
      _ = bOf γ := by group
  have hcomm : ∀ x : NativeSporadic.M12, c * x * c⁻¹ = x → c * x = x * c := fun x hx => by
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [hx]
  have hgh : c = 1 → (g, β).1 = (h, γ).1 := fun h1' => by
    have : g = h := by
      calc g = h * (h⁻¹ * g) := by group
        _ = h := by rw [← hcdef, h1', mul_one]
    exact this
  cases β <;> cases γ
  · exact Prod.ext (hgh (eq_one_of_comm_ab (hcomm _ hca) (hcomm _ hcb))) rfl
  · exfalso
    change c * m12b * c⁻¹ = mbp at hcb
    have h3 := fp_conj c (word m12a m12b distWord)
    rw [conj_word_eq hca hcb distWord, fp_dist_b, fp_dist_bp] at h3
    exact absurd h3 (by norm_num)
  · exfalso
    change c * mbp * c⁻¹ = m12b at hcb
    have h3 := fp_conj c (word m12a mbp distWord)
    rw [conj_word_eq hca hcb distWord, fp_dist_b, fp_dist_bp] at h3
    exact absurd h3 (by norm_num)
  · refine Prod.ext (hgh (eq_one_of_comm_ab (hcomm _ hca) ?_)) rfl
    have hbp : c * mbp = mbp * c := hcomm _ hcb
    have := conj_word_eq hca hcb bWord
    change c * word m12a mbp bWord * c⁻¹ = word m12a mbp bWord at this
    rw [← m12b_eq_word] at this
    exact hcomm _ this

theorem exists_conj_bp
    (σ : MulAut NativeSporadic.M12)
    (hσ : σ ∉ inner NativeSporadic.M12) :
    ∃ g : NativeSporadic.M12, σ m12a = g * m12a * g⁻¹ ∧ σ m12b = g * mbp * g⁻¹ := by
  have hcard : Nat.card {q : NativeSporadic.M12 × NativeSporadic.M12 // orderOf q.1 = 2 ∧
      orderOf q.2 = 3 ∧ CFSG.Sporadic.Schreier.WordsRel CFSG.Sporadic.Schreier.m12AutWords q.1 q.2} ≤
      Nat.card (NativeSporadic.M12 × Bool) := by
    rw [card_pairs, Nat.card_prod, card_M12, Nat.card_eq_fintype_card (α := Bool),
      Fintype.card_bool]
  have hmem := mem_pairs_ab
  obtain ⟨⟨g, β⟩, hg⟩ := (pairOf_injective.bijective_of_nat_card_le hcard).2
    ⟨(σ m12a, σ m12b), by
      rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, CFSG.Sporadic.Schreier.wordsRel_map]
      exact hmem⟩
  have h1 := congrArg (fun q => q.1.1) hg
  have h2 := congrArg (fun q => q.1.2) hg
  simp only [pairOf] at h1 h2
  cases β
  · exfalso
    apply hσ
    refine ⟨g, MulEquiv.ext fun x => ?_⟩
    have htop : Subgroup.closure ({m12a, m12b} : Set NativeSporadic.M12) = ⊤ :=
      CFSG.Sporadic.Mathieu.closure_pair_eq_top m12_eq _ _
    have heq : Set.EqOn ((MulAut.conj g).toMonoidHom : NativeSporadic.M12 → NativeSporadic.M12)
        σ.toMonoidHom {m12a, m12b} := by
      intro z hz
      rcases hz with rfl | rfl
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact h1
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact h2
    have := MonoidHom.eqOn_closure heq
    rw [htop] at this
    exact this (Subgroup.mem_top x)
  · exact ⟨g, h1.symm, h2.symm⟩

theorem exists_conj_normalizes (σ : MulAut NativeSporadic.M12)
    (hσ2 : σ * σ = 1) : ∃ c : NativeSporadic.M12, ∀ s : NativeSporadic.M12,
      (s : Equiv.Perm (Fin 12)) ∈ S →
        ((c⁻¹ * σ (c * s * c⁻¹) * c : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
  have hH : IsPGroup 2 (Subgroup.zpowers σ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hσ2)
  obtain ⟨P, hP⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 NativeSporadic.M12)
    (not_dvd_card_sylow 2 NativeSporadic.M12)
  have hσP : σ • P = P := by
    have := hP ⟨σ, Subgroup.mem_zpowers σ⟩
    rwa [Subgroup.smul_def] at this
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq NativeSporadic.M12 sylow P
  refine ⟨c, fun s hs => ?_⟩
  have hs' : s ∈ (sylow : Subgroup NativeSporadic.M12) := by
    rw [coe_sylow, Subgroup.mem_subgroupOf]
    exact hs
  have h1 : c * s * c⁻¹ ∈ (P : Subgroup NativeSporadic.M12) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul s (MulAut.conj c)
      (sylow : Subgroup NativeSporadic.M12) hs'
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  have h2 : σ (c * s * c⁻¹) ∈ (P : Subgroup NativeSporadic.M12) := by
    have := Subgroup.smul_mem_pointwise_smul _ σ (P : Subgroup NativeSporadic.M12) h1
    rw [MulAut.smul_def, ← Sylow.pointwise_smul_def, hσP] at this
    exact this
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨t, ht, hte⟩ := h2
  rw [MulAut.smul_def, MulAut.conj_apply] at hte
  rw [← hte, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
  rw [coe_sylow, Subgroup.mem_subgroupOf] at ht
  exact ht

@[expose] def yWord (k : ℕ) : List ℕ :=
  if k = 0 then [1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2]
  else if k = 1 then [0,2,0,2,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,1]
  else [0,2,0,1,0,2,0,1,0,2,0,2,0,2,0,2,0,1,0,2,0,1,0,1,0,1,0,1]

@[expose] def jIdx (k : ℕ) : ℕ := if k = 0 then 63 else if k = 1 then 10 else 52

@[expose] def g0Word : List ℕ := [0, 2, 0, 2, 0, 1, 0, 1, 0, 2]

@[expose] def g0iWord : List ℕ := [1, 0, 2, 0, 2, 0, 1, 0, 1, 0]

@[expose] def rhoT : List ℕ :=
  [0,63,10,52,48,20,55,31,11,26,2,35,44,8,29,33,5,45,32,59,25,21,22,24,37,16,7,62,23,14,18,9,43,
   49,19,13,60,28,57,61,15,56,12,30,47,3,50,42,4,40,54,34,17,46,53,6,38,41,58,51,36,27,39,1]

@[expose] def rho (x : ℕ) : ℕ := nth 0 rhoT x

@[expose] def rhoCheck : Bool :=
  comp (abC g0Word) (abC g0iWord) == idC &&
    ((List.range 3).all fun k => code (k + 1) == abC (yWord k) &&
      comp (comp (abC g0Word) (abpC (yWord k))) (abC g0iWord) == code (jIdx k)) &&
    rho 0 == 0 && rho 22 == 22 && rho 45 == 3 &&
    (List.range 64).all fun x => decide (rho x < 64) &&
      (x == 0 || rho x == mulIdx (jIdx (gen x)) (rho (par x)))

theorem rhoCheck_eq : rhoCheck = true := by decide +kernel

theorem rhoCheck_spec :
    comp (abC g0Word) (abC g0iWord) = idC ∧
      (∀ k < 3, code (k + 1) = abC (yWord k) ∧
        comp (comp (abC g0Word) (abpC (yWord k))) (abC g0iWord) = code (jIdx k)) ∧
      rho 0 = 0 ∧ rho 22 = 22 ∧ rho 45 = 3 ∧
      ∀ x < 64, rho x < 64 ∧ (x ≠ 0 → rho x = mulIdx (jIdx (gen x)) (rho (par x))) := by
  have h := rhoCheck_eq
  simp only [rhoCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun k hk => h2 k hk, h3, h4, h5, fun x hx => ⟨(h6 x hx).1, fun hx0 => ?_⟩⟩
  rcases (h6 x hx).2 with h | h
  · exact absurd h hx0
  · exact h

theorem jIdx_lt {k : ℕ} : jIdx k < 64 := by
  unfold jIdx
  split_ifs <;> norm_num

@[expose] def centerCheck : Bool :=
  (List.range 64).all fun w => w == 0 || w == 22 ||
    comp (code w) (code 1) != comp (code 1) (code w) ||
    comp (code w) (code 2) != comp (code 2) (code w) ||
    comp (code w) (code 3) != comp (code 3) (code w)

theorem centerCheck_eq : centerCheck = true := by decide +kernel

@[expose] def normCheck : Bool :=
  (List.range 64).all fun y => code y != comp (comp (dPow 1) (code 3)) (dPow 2) &&
    code y != comp (comp (dPow 2) (code 3)) (dPow 1)

theorem normCheck_eq : normCheck = true := by decide +kernel

@[expose] def sIdx (i p : ℕ) : ℕ := mulIdx (mulIdx i (rho p)) (invIdx i)

@[expose] def outerFixWit : List (ℕ × ℕ) :=
  [(0, 3), (2, 3), (3, 1), (7, 2), (9, 2), (10, 3), (12, 2), (17, 1), (21, 3), (22, 3), (23, 2),
   (24, 1), (26, 1), (27, 1), (28, 1), (31, 1), (36, 3), (37, 2), (39, 1), (42, 1), (44, 1),
   (45, 2), (46, 1), (47, 2), (50, 1), (52, 2), (53, 1), (54, 1), (58, 3), (60, 3), (61, 1),
   (62, 1)]

@[expose] def outerFixCheck : Bool :=
  (List.range 64).all fun i => (sIdx i 22 == 22 && sIdx i 36 == 36) ||
    outerFixWit.any fun d => d.1 == i && sIdx i (sIdx i d.2) != d.2

theorem outerFixCheck_eq : outerFixCheck = true := by decide +kernel

theorem eltM_sIdx {i p : ℕ} (hi : i < 64) (hp : p < 64) :
    sIdx i p < 64 ∧ eltM (sIdx i p) = eltM i * eltM (rho p) * (eltM i)⁻¹ := by
  have hr := (rhoCheck_spec.2.2.2.2.2 p hp).1
  obtain ⟨h1, h2⟩ := eltM_mulIdx hi hr
  obtain ⟨h3, h4⟩ := eltM_invIdx hi
  obtain ⟨h5, h6⟩ := eltM_mulIdx h1 h3
  exact ⟨h5, by rw [sIdx, h6, h2, h4]⟩

theorem mul_apply_self {σ : MulAut NativeSporadic.M12} (hσ2 : σ * σ = 1) (x : NativeSporadic.M12) :
    σ (σ x) = x := by
  have := congrArg (fun τ : MulAut NativeSporadic.M12 => τ x) hσ2
  simpa only [MulAut.mul_apply, MulAut.one_apply] using this

theorem fixes_of_normalizes
    (σ : MulAut NativeSporadic.M12) (hσ2 : σ * σ = 1)
    (hσ : σ ∉ inner NativeSporadic.M12)
    (hS : ∀ s : NativeSporadic.M12, (s : Equiv.Perm (Fin 12)) ∈ S →
      ((σ s : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S) :
    σ (eltM 22) = eltM 22 ∧ σ (eltM 36) = eltM 36 := by
  obtain ⟨hg0, hgen, hr0, hr22, hr45, htree⟩ := rhoCheck_spec
  obtain ⟨g, hga, hgb⟩ := exists_conj_bp σ hσ
  set g₀ := wM g0Word with hg₀
  have hg0i : wM g0iWord = g₀⁻¹ :=
    eq_inv_of_mul_eq_one_right (mul_eq_one_of_code (isCode_wM _) (isCode_wM _) hg0)
  have hσw : ∀ w, σ (word m12a m12b w) = g * word m12a mbp w * g⁻¹ := fun w => by
    rw [conj_word_eq hga.symm hgb.symm w]
    have := map_word σ.toMonoidHom m12a m12b w
    simpa only [MulEquiv.coe_toMonoidHom] using this
  set n := g * g₀⁻¹ with hn
  have hgens : ∀ k < 3, σ (eltM (k + 1)) = n * eltM (jIdx k) * n⁻¹ := by
    intro k hk
    obtain ⟨h1, h2⟩ := hgen k hk
    have e1 : eltM (k + 1) = wM (yWord k) := eq_of_code (isCode_eltM (by omega))
      (h1 ▸ isCode_wM (yWord k))
    have e2 : eltM (jIdx k) = g₀ * word m12a mbp (yWord k) * wM g0iWord :=
      eq_of_code (isCode_eltM jIdx_lt)
        (h2 ▸ isCode_mul (isCode_mul (isCode_wM g0Word) (isCode_word_bp (yWord k)))
          (isCode_wM g0iWord))
    rw [e1, wM, hσw, e2, hg0i, hn]
    group
  have hσS : ∀ x < 64, σ (eltM x) = n * eltM (rho x) * n⁻¹ := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx
      by_cases hx0 : x = 0
      · subst hx0
        rw [hr0, eltM_zero, map_one]
        group
      · obtain ⟨hgl, hpl, he⟩ := eltM_cons hx0 hx
        obtain ⟨hrl, hrx⟩ := htree x hx
        obtain ⟨-, hm⟩ := eltM_mulIdx (jIdx_lt (k := gen x)) (htree _ (hpl.trans hx)).1
        rw [he, map_mul, hgens _ hgl, ih _ hpl (hpl.trans hx), hrx hx0, hm]
        group
  have hz : σ (eltM 22) = eltM 22 := by
    obtain ⟨w, hw, hwe⟩ := exists_eltM (hS _ (mem_S_eltM 22))
    have hcomm : ∀ k < 3, eltM w * eltM (k + 1) = eltM (k + 1) * eltM w := by
      intro k hk
      obtain ⟨t, ht, hte⟩ := exists_eltM (hS _ (mem_S_eltM (k + 1)))
      have h1 : σ (eltM t) = eltM (k + 1) := by rw [hte, mul_apply_self hσ2]
      have h2 := congrArg σ (eltM_comm_22 ht)
      rw [map_mul, map_mul, h1, ← hwe] at h2
      exact h2.symm
    have h := List.all_eq_true.1 centerCheck_eq w (List.mem_range.2 hw)
    have hc1 := comp_comm_of (isCode_eltM hw) (isCode_eltM (x := 1) (by norm_num)) (hcomm 0 (by norm_num))
    have hc2 := comp_comm_of (isCode_eltM hw) (isCode_eltM (x := 2) (by norm_num)) (hcomm 1 (by norm_num))
    have hc3 := comp_comm_of (isCode_eltM hw) (isCode_eltM (x := 3) (by norm_num)) (hcomm 2 (by norm_num))
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hc1, hc2, hc3, not_true_eq_false,
      or_false] at h
    rcases h with rfl | rfl
    · exfalso
      rw [eltM_zero] at hwe
      exact eltM_22_ne_one ((map_eq_one_iff σ σ.injective).1 hwe.symm)
    · exact hwe.symm
  have hnz : n * eltM 22 = eltM 22 * n := by
    have := hσS 22 (by norm_num)
    rw [hr22, hz] at this
    calc n * eltM 22 = n * eltM 22 * n⁻¹ * n := by group
      _ = eltM 22 * n := by rw [← this]
  obtain ⟨i, hi, j, hj, hnij⟩ := mem_cz0 n hnz
  have hj0 : j = 0 := by
    by_contra hj0
    have hmem := hS _ (mem_S_eltM 45)
    rw [hσS 45 (by norm_num), hr45, hnij] at hmem
    have hmem' : ((d0 ^ j * eltM 3 * (d0 ^ j)⁻¹ : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
      have e : d0 ^ j * eltM 3 * (d0 ^ j)⁻¹ =
          (eltM i)⁻¹ * (eltM i * d0 ^ j * eltM 3 * (eltM i * d0 ^ j)⁻¹) * eltM i := by group
      rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact S.mul_mem (S.mul_mem (S.inv_mem (mem_S_eltM i)) hmem) (mem_S_eltM i)
    obtain ⟨y, hy, hye⟩ := exists_eltM hmem'
    have hn := List.all_eq_true.1 normCheck_eq y (List.mem_range.2 hy)
    rw [Bool.and_eq_true, bne_iff_ne, bne_iff_ne] at hn
    have hd3 := d0_cube
    interval_cases j
    · exact hj0 rfl
    · have hinv : (d0 ^ 1)⁻¹ = d0 ^ 2 := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add]
        exact hd3
      rw [hinv] at hye
      exact hn.1 (code_eq_of_eq (isCode_eltM hy) (isCode_mul (isCode_mul (isCode_dPow (by norm_num))
        (isCode_eltM (x := 3) (by norm_num))) (isCode_dPow (by norm_num))) hye)
    · have hinv : (d0 ^ 2)⁻¹ = d0 ^ 1 := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add]
        exact hd3
      rw [hinv] at hye
      exact hn.2 (code_eq_of_eq (isCode_eltM hy) (isCode_mul (isCode_mul (isCode_dPow (by norm_num))
        (isCode_eltM (x := 3) (by norm_num))) (isCode_dPow (by norm_num))) hye)
  subst hj0
  rw [pow_zero, mul_one] at hnij
  have hσi : ∀ p < 64, σ (eltM p) = eltM (sIdx i p) := fun p hp => by
    rw [hσS p hp, hnij, (eltM_sIdx hi hp).2]
  have hinvo : ∀ p < 64, sIdx i (sIdx i p) = p := fun p hp => by
    have hs := (eltM_sIdx hi hp).1
    have h := mul_apply_self hσ2 (eltM p)
    rw [hσi p hp, hσi _ hs] at h
    exact eltM_injective (eltM_sIdx hi hs).1 hp h
  have h := List.all_eq_true.1 outerFixCheck_eq i (List.mem_range.2 hi)
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨⟨i', p⟩, hd, hdp⟩
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    exact ⟨hz, by rw [hσi 36 (by norm_num), h.2]⟩
  · exfalso
    rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hdp
    have hp : p < 64 := by
      simp only [outerFixWit, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hd
      omega
    exact hdp.2 (hinvo p hp)

theorem eltM_36_sq : eltM 36 * eltM 36 = 1 :=
  eltM_mul_eq_one (by norm_num) (by norm_num) (by decide +kernel)

theorem eltM_36_ne_one : eltM 36 ≠ 1 := eltM_ne_one (by norm_num) (by decide +kernel)

theorem fp_eltM_36 : fp (eltM 36) = 4 := by
  rw [fp_eltM (by norm_num)]
  decide +kernel

theorem eltM_22_36 : eltM 22 * eltM 36 = eltM 60 :=
  eltM_mul_eq (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

theorem eltM_60_sq : eltM 60 * eltM 60 = 1 :=
  eltM_mul_eq_one (by norm_num) (by norm_num) (by decide +kernel)

theorem eltM_60_ne_one : eltM 60 ≠ 1 := eltM_ne_one (by norm_num) (by decide +kernel)

theorem fp_eltM_60 : fp (eltM 60) = 4 := by
  rw [fp_eltM (by norm_num)]
  decide +kernel

end M12Model

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_commute_conj_of_orderOf_four
    (y k : NativeSporadic.M12) (hy : y * y = 1)
    (hk : orderOf k = 4) : ∃ x : NativeSporadic.M12, y * (x * k * x⁻¹) = x * k * x⁻¹ * y := by
  by_cases hy1 : y = 1
  · exact ⟨1, by rw [hy1]; group⟩
  rcases fp_inv y hy hy1 with h4 | h0
  · obtain ⟨g, hg⟩ := conj_sq_of_fp hk hy hy1 h4
    refine ⟨g, ?_⟩
    rw [← hg]
    group
  · obtain ⟨h, x, hx, hhx⟩ := exists_conj_eltM (n := 2) (by rw [hk]; norm_num)
    have hxk : orderOf (eltM x) = 4 := by rw [← hhx, orderOf_conj_inv, hk]
    obtain ⟨u, hu2, hu1, hu0, huc⟩ := exists_w_comm hx hxk
    obtain ⟨g, hg⟩ := conj_of_fp_eq hu2 hu1 hy hy1 (by rw [hu0, h0])
    refine ⟨g * h⁻¹, ?_⟩
    have hk' : k = h * eltM x * h⁻¹ := by rw [← hhx]; group
    rw [hk', ← hg]
    calc g * u * g⁻¹ * (g * h⁻¹ * (h * eltM x * h⁻¹) * (g * h⁻¹)⁻¹)
        = g * (u * eltM x) * g⁻¹ := by group
      _ = g * (eltM x * u) * g⁻¹ := by rw [huc]
      _ = g * h⁻¹ * (h * eltM x * h⁻¹) * (g * h⁻¹)⁻¹ * (g * u * g⁻¹) := by group

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_sq_mul_sq_conj
    (k k' : NativeSporadic.M12) (hk : orderOf k = 4) (hk' : orderOf k' = 4)
    (hne : k' * k' ≠ k * k) (hc : k * k * (k' * k') = k' * k' * (k * k)) :
    ∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = k * k * (k' * k') := by
  set z := k * k with hzdef
  set z' := k' * k' with hz'def
  have hz2 : z * z = 1 := mul_self_mul_self_of_orderOf_four hk
  have hz1 : z ≠ 1 := mul_self_ne_one_of_orderOf_four hk
  have hz'2 : z' * z' = 1 := mul_self_mul_self_of_orderOf_four hk'
  have hz'1 : z' ≠ 1 := mul_self_ne_one_of_orderOf_four hk'
  have hz4 : fp z = 4 := fp_sq k hk
  have hz'4 : fp z' = 4 := fp_sq k' hk'
  have hpz : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, orderOf_eq_two_of_mul_self hz2 hz1, pow_one])
  have hpz' : IsPGroup 2 (Subgroup.zpowers z') := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, orderOf_eq_two_of_mul_self hz'2 hz'1, pow_one])
  have hmem : z ∈ Subgroup.centralizer (Subgroup.zpowers z' : Set NativeSporadic.M12) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute z' z from hc.symm) n).eq
  have hH := hpz.to_sup_of_normal_right' hpz'
    ((Subgroup.zpowers_le.2 hmem).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨g, hg⟩ := exists_conj_mem_S_of_isPGroup hH
  obtain ⟨x, hx, hxz⟩ := exists_eltM (hg z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
  obtain ⟨y, hy, hyz⟩ := exists_eltM (hg z' (Subgroup.mem_sup_right (Subgroup.mem_zpowers z')))
  have hBx : isB (code x) = true := isB_eq_true hx (by rw [hxz]; exact conj_mul_self g z hz2)
    (by rw [hxz]; exact conj_ne_one g z hz1) (by rw [hxz, fp_conj_inv, hz4])
  have hBy : isB (code y) = true := isB_eq_true hy (by rw [hyz]; exact conj_mul_self g z' hz'2)
    (by rw [hyz]; exact conj_ne_one g z' hz'1) (by rw [hyz, fp_conj_inv, hz'4])
  have hxy : (code x == code y) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    apply hne
    have h1 : eltM x = eltM y := eq_of_code (isCode_eltM hx) (he ▸ isCode_eltM hy)
    rw [hxz, hyz] at h1
    calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  have hcxy : eltM x * eltM y = eltM y * eltM x := by
    rw [hxz, hyz]
    calc g⁻¹ * z * g * (g⁻¹ * z' * g) = g⁻¹ * (z * z') * g := by group
      _ = g⁻¹ * (z' * z) * g := by rw [hc]
      _ = g⁻¹ * z' * g * (g⁻¹ * z * g) := by group
  have hcomm : (comp (code x) (code y) != comp (code y) (code x)) = false := by
    rw [bne_eq_false_iff_eq]
    exact comp_comm_of (isCode_eltM hx) (isCode_eltM hy) hcxy
  have key := List.all_eq_true.1 prodCheck_eq x (List.mem_range.2 hx)
  rw [hBx, Bool.not_true, Bool.false_or, List.all_eq_true] at key
  have key2 := key y (List.mem_range.2 hy)
  rw [hBy, Bool.not_true, Bool.false_or, hxy, Bool.false_or, hcomm, Bool.false_or,
    beq_iff_eq] at key2
  have hfp : fp (z * z') = 4 := by
    have h1 : z * z' = g * (eltM x * eltM y) * g⁻¹ := by rw [hxz, hyz]; group
    rw [h1, fp_conj, fp_of_code (isCode_mul (isCode_eltM hx) (isCode_eltM hy)), key2]
  have hzz2 : z * z' * (z * z') = 1 := by
    calc z * z' * (z * z') = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [hc]
      _ = z * z * (z' * z') := by group
      _ = 1 := by rw [hz2, hz'2, one_mul]
  have hzz1 : z * z' ≠ 1 := by
    intro h
    apply hne
    calc z' = z⁻¹ * (z * z') := by group
      _ = z := by rw [h, mul_one, inv_eq_of_mul_eq_one_right hz2]
  exact conj_of_fp_eq hz2 hz1 hzz2 hzz1 (by rw [hz4, hfp])

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_involution_conj
    (u v : NativeSporadic.M12) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (h : (∃ k : NativeSporadic.M12, orderOf k = 4 ∧ k * k = u) ↔
      ∃ k : NativeSporadic.M12, orderOf k = 4 ∧ k * k = v) :
    ∃ x : NativeSporadic.M12, x * u * x⁻¹ = v := by
  rw [exists_sq_iff hu2 hu1, exists_sq_iff hv2 hv1] at h
  refine conj_of_fp_eq hu2 hu1 hv2 hv1 ?_
  rcases fp_inv u hu2 hu1 with hu | hu <;> rcases fp_inv v hv2 hv1 with hv | hv
  · rw [hu, hv]
  · exact absurd (h.1 hu) (by rw [hv]; norm_num)
  · exact absurd (h.2 hv) (by rw [hu]; norm_num)
  · rw [hu, hv]

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_outer_fixes_four
    (σ : MulAut NativeSporadic.M12) (hσ2 : σ * σ = 1)
    (hσ : σ ∉ inner NativeSporadic.M12) (k : NativeSporadic.M12) (hk : orderOf k = 4) :
    ∃ a b : NativeSporadic.M12, σ a = a ∧ σ b = b ∧ a * b = b * a ∧
      (∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = a) ∧
      (∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = b) ∧
      (∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = a * b) := by
  obtain ⟨c, hc⟩ := exists_conj_normalizes σ hσ2
  set σ' : MulAut NativeSporadic.M12 := (MulAut.conj c)⁻¹ * σ * MulAut.conj c with hσ'
  have hσ'a : ∀ s, σ' s = c⁻¹ * σ (c * s * c⁻¹) * c := fun s => by
    rw [hσ']
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hσ'2 : σ' * σ' = 1 := by
    calc σ' * σ' = (MulAut.conj c)⁻¹ * (σ * σ) * MulAut.conj c := by rw [hσ']; group
      _ = 1 := by rw [hσ2]; group
  have hσ'o : σ' ∉ inner NativeSporadic.M12 := by
    intro h
    apply hσ
    have := (inner_normal NativeSporadic.M12).conj_mem σ' h (MulAut.conj c)
    rwa [hσ', show MulAut.conj c * ((MulAut.conj c)⁻¹ * σ * MulAut.conj c) * (MulAut.conj c)⁻¹ = σ
      by group] at this
  obtain ⟨h22, h36⟩ := fixes_of_normalizes σ' hσ'2 hσ'o fun s hs => by rw [hσ'a]; exact hc s hs
  have hfix : ∀ e : NativeSporadic.M12, σ' e = e → σ (c * e * c⁻¹) = c * e * c⁻¹ := by
    intro e he
    rw [hσ'a] at he
    calc σ (c * e * c⁻¹) = c * (c⁻¹ * σ (c * e * c⁻¹) * c) * c⁻¹ := by group
      _ = c * e * c⁻¹ := by rw [he]
  have hconj : ∀ e : NativeSporadic.M12, (∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = e) →
      ∃ x : NativeSporadic.M12, x * (k * k) * x⁻¹ = c * e * c⁻¹ := by
    rintro e ⟨x, rfl⟩
    exact ⟨c * x, by group⟩
  refine ⟨c * eltM 22 * c⁻¹, c * eltM 36 * c⁻¹, hfix _ h22, hfix _ h36, ?_, ?_, ?_, ?_⟩
  · have h := eltM_comm_22 (x := 36) (by norm_num)
    calc c * eltM 22 * c⁻¹ * (c * eltM 36 * c⁻¹) = c * (eltM 22 * eltM 36) * c⁻¹ := by group
      _ = c * (eltM 36 * eltM 22) * c⁻¹ := by rw [h]
      _ = c * eltM 36 * c⁻¹ * (c * eltM 22 * c⁻¹) := by group
  · exact hconj _ (conj_sq_of_fp hk eltM_22_sq eltM_22_ne_one fp_eltM_22)
  · exact hconj _ (conj_sq_of_fp hk eltM_36_sq eltM_36_ne_one fp_eltM_36)
  · have e : c * eltM 22 * c⁻¹ * (c * eltM 36 * c⁻¹) = c * eltM 60 * c⁻¹ := by
      rw [← eltM_22_36]
      group
    rw [e]
    exact hconj _ (conj_sq_of_fp hk eltM_60_sq eltM_60_ne_one fp_eltM_60)

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_card_centralizer_sq
    (k : NativeSporadic.M12) (hk : orderOf k = 4) :
    Nat.card (Subgroup.centralizer ({k * k} : Set NativeSporadic.M12)) = 192 := by
  obtain ⟨g, hg⟩ := conj_of_fp_eq eltM_22_sq eltM_22_ne_one
    (mul_self_mul_self_of_orderOf_four hk) (mul_self_ne_one_of_orderOf_four hk)
    (by rw [fp_eltM_22, fp_sq k hk])
  rw [← hg, card_centralizer_conj, card_centralizer_z0]

open M12Model CFSG.ComponentClassification.M12Cover.SylowTable in
theorem m12_not_commute_four_three
    (k d : NativeSporadic.M12) (hk : orderOf k = 4)
    (hd : orderOf d = 3) : k * d ≠ d * k := by
  intro hkd
  obtain ⟨g, hg⟩ := conj_of_fp_eq (mul_self_mul_self_of_orderOf_four hk)
    (mul_self_ne_one_of_orderOf_four hk) eltM_22_sq eltM_22_ne_one
    (by rw [fp_eltM_22, fp_sq k hk])
  set k₁ := g * k * g⁻¹ with hk₁
  set d₁ := g * d * g⁻¹ with hd₁
  have hk₁2 : k₁ * k₁ = eltM 22 := by rw [← hg, hk₁]; group
  have hkd₁ : k₁ * d₁ = d₁ * k₁ := by
    rw [hk₁, hd₁]
    calc g * k * g⁻¹ * (g * d * g⁻¹) = g * (k * d) * g⁻¹ := by group
      _ = g * (d * k) * g⁻¹ := by rw [hkd]
      _ = g * d * g⁻¹ * (g * k * g⁻¹) := by group
  have hk₁c : k₁ * eltM 22 = eltM 22 * k₁ := by rw [← hk₁2]; group
  have hd₁c : d₁ * eltM 22 = eltM 22 * d₁ := by
    rw [← hk₁2]
    calc d₁ * (k₁ * k₁) = k₁ * d₁ * k₁ := by rw [← mul_assoc, ← hkd₁]
      _ = k₁ * (k₁ * d₁) := by rw [mul_assoc, hkd₁]
      _ = k₁ * k₁ * d₁ := by group
  have hd₁3 : d₁ ^ 3 = 1 := by
    rw [hd₁, ← MulAut.conj_apply, ← map_pow, ← hd, pow_orderOf_eq_one, map_one]
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    have : orderOf d₁ = 1 := by rw [h, orderOf_one]
    rw [hd₁, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hd] at this
    exact absurd this (by norm_num)
  obtain ⟨i, hi, j, hj, hkij⟩ := mem_cz0 k₁ hk₁c
  obtain ⟨i', hi', j', hj', hdij⟩ := mem_cz0 d₁ hd₁c
  have hck := isCode_czCode hi hj
  have hcd := isCode_czCode hi' hj'
  rw [← hkij] at hck
  rw [← hdij] at hcd
  have h := List.all_eq_true.1 noTwelveCheck_eq i (List.mem_range.2 hi)
  have h' := List.all_eq_true.1 h j (List.mem_range.2 hj)
  have e1 : (comp (czCode i j) (czCode i j) != code 22) = false := by
    rw [bne_eq_false_iff_eq]
    exact code_eq_of_eq (isCode_mul hck hck) (isCode_eltM (x := 22) (by norm_num)) hk₁2
  rw [e1, Bool.false_or, List.all_eq_true] at h'
  have h'' := List.all_eq_true.1 (h' i' (List.mem_range.2 hi')) j' (List.mem_range.2 hj')
  have e2 : (czCode i' j' == idC) = false := by
    rw [beq_eq_false_iff_ne]
    exact code_ne_of_ne_one hcd hd₁1
  have e3 : (comp (czCode i' j') (comp (czCode i' j') (czCode i' j')) != idC) = false := by
    rw [bne_eq_false_iff_eq]
    refine comp_eq_idC_of hcd (isCode_mul hcd hcd) ?_
    rw [← hd₁3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e4 : (comp (czCode i j) (czCode i' j') != comp (czCode i' j') (czCode i j)) = false := by
    rw [bne_eq_false_iff_eq]
    exact comp_comm_of hck hcd hkd₁
  rw [e2, e3, e4] at h''
  exact absurd h'' (by decide)

theorem m12_mul_mem_inner
    (φ ψ : MulAut NativeSporadic.M12) (hφ : φ ∉ inner NativeSporadic.M12)
    (hψ : ψ ∉ inner NativeSporadic.M12) : φ * ψ ∈ inner NativeSporadic.M12 := by
  have : Finite NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.1
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have hinj : Function.Injective (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hc : y ∈ Subgroup.center NativeSporadic.M12 := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun α : MulAut NativeSporadic.M12 => α g) hy
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * y = y * g * y⁻¹ * y := by rw [h1]
        _ = y * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have h1 : Nat.card (inner NativeSporadic.M12) = Nat.card NativeSporadic.M12 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 := (inner NativeSporadic.M12).card_mul_index
  have hcard := CFSG.Sporadic.Schreier.m12_mulAut_card
  have hpos : 0 < Nat.card NativeSporadic.M12 := Nat.card_pos
  have hidx : (inner NativeSporadic.M12).index ≤ 2 := by
    rw [h1] at h2
    nlinarith
  have hidx1 : (inner NativeSporadic.M12).index ≠ 1 := fun h =>
    hφ ((Subgroup.index_eq_one.mp h) ▸ Subgroup.mem_top φ)
  have hidx0 : (inner NativeSporadic.M12).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx2 : (inner NativeSporadic.M12).index = 2 := by omega
  exact (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hφ hψ)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
