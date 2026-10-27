module

public import CFSG.GF2Type.Smith1979.CaseI25Weights
public import CFSG.GroupTheory.DiagonalTwentySeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriConf

open CFSG.GF2Type.Smith1979.LemmaW
open CFSG.GroupTheory.DiagonalTwentySeven

variable {X : Type*} [Group X] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

abbrev A3 : Type := Multiplicative (Fin 3 → ZMod 3)

@[expose] def dot3 (f c : Fin 3 → ZMod 3) : ZMod 3 := ∑ i, f i * c i

theorem eprod_single {Y : Type*} [Group Y] (e : Fin 3 → Y) (i : Fin 3) :
    eprod e (Pi.single i 1) = e i := by
  fin_cases i <;> simp [eprod, ZMod.val_one]

@[expose] noncomputable def eprodHom (e : Fin 3 → X) (h3 : ∀ i, e i ^ 3 = 1)
    (hc : ∀ i j, Commute (e i) (e j)) : A3 →* X where
  toFun c := eprod e c.toAdd
  map_one' := by
    show eprod e (1 : A3).toAdd = 1
    rw [toAdd_one, eprod_zero]
  map_mul' c c' := by
    show eprod e (c * c').toAdd = eprod e c.toAdd * eprod e c'.toAdd
    rw [toAdd_mul]
    exact eprod_add e (fun i j => (hc i j).eq) h3 c.toAdd c'.toAdd

theorem eprodHom_apply (e : Fin 3 → X) (h3 : ∀ i, e i ^ 3 = 1)
    (hc : ∀ i j, Commute (e i) (e j)) (c : A3) :
    eprodHom e h3 hc c = eprod e c.toAdd := rfl

theorem eprodHom_single (e : Fin 3 → X) (h3 : ∀ i, e i ^ 3 = 1)
    (hc : ∀ i j, Commute (e i) (e j)) (i : Fin 3) :
    eprodHom e h3 hc (Multiplicative.ofAdd (Pi.single i 1)) = e i := by
  rw [eprodHom_apply, toAdd_ofAdd, eprod_single]

@[expose] noncomputable def rhoA (ρ : Representation (ZMod 2) X W) (e : Fin 3 → X)
    (h3 : ∀ i, e i ^ 3 = 1) (hc : ∀ i j, Commute (e i) (e j)) :
    Representation (ZMod 2) A3 W := ρ.comp (eprodHom e h3 hc)

theorem rhoA_apply (ρ : Representation (ZMod 2) X W) (e : Fin 3 → X)
    (h3 : ∀ i, e i ^ 3 = 1) (hc : ∀ i j, Commute (e i) (e j)) (c : A3) :
    rhoA ρ e h3 hc c = ρ (eprod e c.toAdd) := rfl

private theorem card_A3 : Nat.card A3 = 27 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod]
  norm_num

theorem pow_three_eq_one_of_A3 (c : A3) : c ^ 3 = 1 := by
  revert c
  decide

private theorem index_hyperplane (H : Subgroup A3) (hH : H.index = 3) : Nat.card H = 9 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  have hidx : Nat.card (A3 ⧸ H) = 3 := hH
  rw [card_A3, hidx] at hc
  omega

private theorem orderOf_eq_three (c : A3) (hc : c ≠ 1) : orderOf c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (pow_three_eq_one_of_A3 c) hc

@[expose] def flipC (i : Fin 3) (c : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun j => if j = i then -c j else c j

theorem flipC_invol (i : Fin 3) (c : Fin 3 → ZMod 3) : flipC i (flipC i c) = c := by
  funext j
  by_cases h : j = i
  · simp only [flipC, h, if_true]
    exact neg_neg (c i)
  · simp only [flipC, h, if_false]

theorem flipC_add (i : Fin 3) (c c' : Fin 3 → ZMod 3) :
    flipC i (c + c') = flipC i c + flipC i c' := by
  funext j
  by_cases h : j = i
  · simp only [flipC, h, if_true, Pi.add_apply]
    exact neg_add (c i) (c' i)
  · simp only [flipC, h, if_false, Pi.add_apply]

@[expose] def flipAdd (i : Fin 3) : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3) where
  toFun := flipC i
  invFun := flipC i
  left_inv := flipC_invol i
  right_inv := flipC_invol i
  map_add' := flipC_add i

@[expose] def flipMul (i : Fin 3) : A3 ≃* A3 := (flipAdd i).toMultiplicative

theorem flipMul_toAdd (i : Fin 3) (c : A3) : (flipMul i c).toAdd = flipC i c.toAdd := rfl

theorem flipMul_apply_apply (i : Fin 3) (c : A3) : flipMul i (flipMul i c) = c := by
  apply Multiplicative.toAdd.injective
  rw [flipMul_toAdd, flipMul_toAdd, flipC_invol]

theorem flipMul_sq (i : Fin 3) : flipMul i * flipMul i = 1 := by
  refine MulEquiv.ext fun c => ?_
  show flipMul i (flipMul i c) = c
  exact flipMul_apply_apply i c

theorem eprod_flip (e l : Fin 3 → X) (h3 : ∀ i, e i ^ 3 = 1)
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) (i : Fin 3) (c : Fin 3 → ZMod 3) :
    l i * eprod e c * (l i)⁻¹ = eprod e (flipC i c) := by
  simp only [eprod]
  have hneg : ∀ j, e j ^ ((-c j).val) = ((e j) ^ (c j).val)⁻¹ := by
    intro j
    have h := pow_add_zmod3 (e j) (h3 j) (c j) (-c j)
    rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [show l i * (e 0 ^ (c 0).val * e 1 ^ (c 1).val * e 2 ^ (c 2).val) * (l i)⁻¹
      = (l i * e 0 ^ (c 0).val * (l i)⁻¹) * (l i * e 1 ^ (c 1).val * (l i)⁻¹) *
        (l i * e 2 ^ (c 2).val * (l i)⁻¹) by group]
  have hc0 : l i * e 0 ^ (c 0).val * (l i)⁻¹ = e 0 ^ ((flipC i c) 0).val := by
    by_cases h : i = 0
    · rw [h]
      simp only [flipC, if_true]
      rw [← conj_pow, hinv 0, inv_pow, ← hneg 0]
    · simp only [flipC, if_neg h, if_neg (Ne.symm h)]
      rw [← conj_pow, hfix i 0 h]
  have hc1 : l i * e 1 ^ (c 1).val * (l i)⁻¹ = e 1 ^ ((flipC i c) 1).val := by
    by_cases h : i = 1
    · rw [h]
      simp only [flipC, if_true]
      rw [← conj_pow, hinv 1, inv_pow, ← hneg 1]
    · simp only [flipC, if_neg h, if_neg (Ne.symm h)]
      rw [← conj_pow, hfix i 1 h]
  have hc2 : l i * e 2 ^ (c 2).val * (l i)⁻¹ = e 2 ^ ((flipC i c) 2).val := by
    by_cases h : i = 2
    · rw [h]
      simp only [flipC, if_true]
      rw [← conj_pow, hinv 2, inv_pow, ← hneg 2]
    · simp only [flipC, if_neg h, if_neg (Ne.symm h)]
      rw [← conj_pow, hfix i 2 h]
  rw [hc0, hc1, hc2]

private theorem rhoA_injective (ρ : Representation (ZMod 2) X W) (e : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0) :
    Function.Injective (rhoA ρ e he3 hec) := by
  intro c c' h
  have hc' : (c')⁻¹ = c' ^ 2 := by
    have h3 : c' * c' ^ 2 = 1 := by
      have h := pow_three_eq_one_of_A3 c'
      rw [pow_succ, pow_two] at h
      rwa [pow_two, ← mul_assoc]
    exact (eq_inv_of_mul_eq_one_right h3).symm
  have h1 : rhoA ρ e he3 hec (c * c'⁻¹) = 1 := by
    rw [map_mul, hc', map_pow, h]
    calc rhoA ρ e he3 hec c' * (rhoA ρ e he3 hec c') ^ 2
        = (rhoA ρ e he3 hec c') ^ (1 + 2) := by rw [pow_add, pow_one]
      _ = (rhoA ρ e he3 hec c') ^ 3 := by norm_num
      _ = 1 := by rw [← map_pow, pow_three_eq_one_of_A3 c', map_one]
  have h2 : (c * c'⁻¹).toAdd = 0 := hfaith (c * c'⁻¹).toAdd h1
  have h3 : c * c'⁻¹ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one, h2]
  exact mul_inv_eq_one.mp h3

private theorem fixedSpace_rhoA_eq_bot (ρ : Representation (ZMod 2) X W) (e : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0) :
    fixedSpace (rhoA ρ e he3 hec) ⊤ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  apply hCY v
  intro i
  have h1 := hv (Multiplicative.ofAdd (Pi.single i 1)) (Subgroup.mem_top _)
  rw [rhoA_apply, toAdd_ofAdd, eprod_single] at h1
  exact h1

@[expose] noncomputable def linForm (f : Fin 3 → ZMod 3) : A3 →* Multiplicative (ZMod 3) where
  toFun z := Multiplicative.ofAdd (dot3 f z.toAdd)
  map_one' := by
    rw [toAdd_one]
    show Multiplicative.ofAdd (dot3 f 0) = 1
    rw [show dot3 f 0 = 0 from by simp [dot3]]
    simp
  map_mul' z z' := by
    rw [toAdd_mul]
    show Multiplicative.ofAdd (dot3 f (z.toAdd + z'.toAdd)) =
      Multiplicative.ofAdd (dot3 f z.toAdd) * Multiplicative.ofAdd (dot3 f z'.toAdd)
    rw [show dot3 f (z.toAdd + z'.toAdd) = dot3 f z.toAdd + dot3 f z'.toAdd from by
      simp [dot3, mul_add, Finset.sum_add_distrib]]
    exact ofAdd_add _ _

@[expose] noncomputable def kerH (f : Fin 3 → ZMod 3) : Subgroup A3 := (linForm f).ker

theorem mem_kerH {f : Fin 3 → ZMod 3} {z : A3} : z ∈ kerH f ↔ dot3 f z.toAdd = 0 := by
  rw [kerH, MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa [linForm] using this
  · intro h
    show linForm f z = 1
    rw [show linForm f z = Multiplicative.ofAdd (dot3 f z.toAdd) from rfl, h]
    rfl

theorem dot3_add (f c c' : Fin 3 → ZMod 3) : dot3 f (c + c') = dot3 f c + dot3 f c' := by
  simp [dot3, mul_add, Finset.sum_add_distrib]

theorem dot3_single (f : Fin 3 → ZMod 3) (i : Fin 3) (x : ZMod 3) :
    dot3 f (Pi.single i x) = f i * x := by
  rw [dot3, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem card_mult_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private theorem linForm_surjective (f : Fin 3 → ZMod 3) (hf : f ≠ 0) :
    Function.Surjective (linForm f) := by
  intro t
  have hex : ∃ i : Fin 3, f i ≠ 0 := by
    by_contra h
    apply hf
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨Multiplicative.ofAdd (Pi.single i ((f i)⁻¹ * t.toAdd)), ?_⟩
  show Multiplicative.ofAdd (dot3 f (Pi.single i ((f i)⁻¹ * t.toAdd))) = t
  rw [dot3_single]
  rw [mul_inv_cancel_left₀ hi]
  rfl

theorem index_kerH (f : Fin 3 → ZMod 3) (hf : f ≠ 0) : (kerH f).index = 3 := by
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := linForm f)
    (linForm_surjective f hf)
  have hcard' : Nat.card (kerH f) * 3 = 27 := by
    change Nat.card ↥(linForm f).ker * 3 = 27
    rwa [card_mult_zmod_three, card_A3] at hcard
  have hcard9 : Nat.card (kerH f) = 9 := by omega
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (kerH f)
  rw [card_A3, hcard9] at hc
  have hidx : (kerH f).index = Nat.card (A3 ⧸ kerH f) := rfl
  rw [hidx]
  omega

private theorem eq_gen_mul : ∀ x : A3,
    x = (Multiplicative.ofAdd (Pi.single 0 1)) ^ (x.toAdd 0).val *
      (Multiplicative.ofAdd (Pi.single 1 1)) ^ (x.toAdd 1).val *
      (Multiplicative.ofAdd (Pi.single 2 1)) ^ (x.toAdd 2).val := by
  decide

theorem exists_functional (H : Subgroup A3) (hH : H.index = 3) :
    ∃ f : Fin 3 → ZMod 3, f ≠ 0 ∧ H = kerH f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (A3 ⧸ H) = 3 := hH
  let e : A3 ⧸ H ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hcard card_mult_zmod_three
  let χ : A3 →* Multiplicative (ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' H)
  have hχ : ∀ x : A3, χ x = 1 ↔ x ∈ H := fun x => by
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let f : Fin 3 → ZMod 3 := fun i => (χ (Multiplicative.ofAdd (Pi.single i 1))).toAdd
  have hf : ∀ x : A3, (χ x).toAdd = dot3 f x.toAdd := by
    intro x
    conv_lhs => rw [eq_gen_mul x]
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, f,
      dot3, Fin.sum_univ_three]
    ring
  refine ⟨f, ?_, ?_⟩
  · intro h0
    have hall : ∀ x : A3, x ∈ H := fun x => by
      rw [← hχ]
      apply Multiplicative.toAdd.injective
      rw [hf x, h0, toAdd_one]
      simp [dot3]
    have htop : H = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hH
    omega
  · ext x
    rw [mem_kerH]
    constructor
    · intro hx
      rw [← hf x, (hχ x).mpr hx, toAdd_one]
    · intro hx
      rw [← hχ]
      apply Multiplicative.toAdd.injective
      rw [hf x, hx, toAdd_one]

@[expose] def Lfun : Fin 4 → Fin 3 → ZMod 3
  | 0 => ![1, 1, 1]
  | 1 => ![1, 1, 2]
  | 2 => ![1, 2, 1]
  | 3 => ![1, 2, 2]

theorem Lfun_ne_zero : ∀ j : Fin 4, Lfun j ≠ 0 := by decide

theorem Lfun_coord_ne_zero : ∀ (j : Fin 4) (i : Fin 3), Lfun j i ≠ 0 := by decide

theorem Lfun_ker_inj : ∀ j k : Fin 4,
    (∀ z : Fin 3 → ZMod 3, dot3 (Lfun j) z = 0 ↔ dot3 (Lfun k) z = 0) → j = k := by
  decide

private theorem exists_Lfun_ker : ∀ f : Fin 3 → ZMod 3, (∀ i, f i ≠ 0) →
    ∃ j : Fin 4, ∀ z : Fin 3 → ZMod 3, (dot3 f z = 0 ↔ dot3 (Lfun j) z = 0) := by
  decide

private theorem eq_smul_of_dot3 : ∀ f g : Fin 3 → ZMod 3,
    (∀ z : Fin 3 → ZMod 3, (dot3 f z = 0 ↔ dot3 g z = 0)) → f ≠ 0 →
    ∃ c : ZMod 3, c ≠ 0 ∧ ∀ j, g j = c * f j := by
  decide

private theorem two_exists_Lfun_ker : ∀ c : Fin 3 → ZMod 3,
    ((c 0 ≠ 0 ∧ c 1 ≠ 0) ∨ (c 0 ≠ 0 ∧ c 2 ≠ 0) ∨ (c 1 ≠ 0 ∧ c 2 ≠ 0)) →
    ∃ j : Fin 4, dot3 (Lfun j) c = 0 := by
  decide

private theorem eq_zero_of_all_Lfun : ∀ c : Fin 3 → ZMod 3,
    (∀ j : Fin 4, dot3 (Lfun j) c = 0) → c = 0 := by
  decide

private theorem exists_single_of_not_two : ∀ c : Fin 3 → ZMod 3, ¬(c 0 ≠ 0 ∧ c 1 ≠ 0) →
    ¬(c 0 ≠ 0 ∧ c 2 ≠ 0) → ¬(c 1 ≠ 0 ∧ c 2 ≠ 0) → ∃ i, ∀ j, j ≠ i → c j = 0 := by
  intro c h01 h02 h12
  by_cases h0 : c 0 = 0
  · by_cases h1 : c 1 = 0
    · refine ⟨2, fun j hj => ?_⟩
      fin_cases j
      · exact h0
      · exact h1
      · exact absurd rfl hj
    · refine ⟨1, fun j hj => ?_⟩
      fin_cases j
      · exact h0
      · exact absurd rfl hj
      · by_contra h
        exact h12 ⟨h1, h⟩
  · have h1 : c 1 = 0 := by
      by_contra h
      exact h01 ⟨h0, h⟩
    have h2 : c 2 = 0 := by
      by_contra h
      exact h02 ⟨h0, h⟩
    refine ⟨0, fun j hj => ?_⟩
    fin_cases j
    · exact absurd rfl hj
    · exact h1
    · exact h2

@[expose] noncomputable def Kfun (j : Fin 4) : Hyperplane A3 :=
  ⟨kerH (Lfun j), index_kerH (Lfun j) (Lfun_ne_zero j)⟩

theorem mem_Kfun (j : Fin 4) (z : A3) : z ∈ (Kfun j).1 ↔ dot3 (Lfun j) z.toAdd = 0 :=
  mem_kerH

theorem Kfun_injective : Function.Injective Kfun := by
  intro j k h
  apply Lfun_ker_inj j k
  intro z
  have h' : (Kfun j).1 = (Kfun k).1 := congrArg Subtype.val h
  have h1 : Multiplicative.ofAdd z ∈ (Kfun j).1 ↔ dot3 (Lfun j) z = 0 := by
    rw [mem_Kfun, toAdd_ofAdd]
  have h2 : Multiplicative.ofAdd z ∈ (Kfun k).1 ↔ dot3 (Lfun k) z = 0 := by
    rw [mem_Kfun, toAdd_ofAdd]
  rw [← h1, ← h2, h']



@[expose] noncomputable def flipH (i : Fin 3) (H : Hyperplane A3) : Hyperplane A3 :=
  ⟨H.1.map (flipMul i).toMonoidHom, by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact H.2⟩

@[expose] noncomputable def bflip (ρ : Representation (ZMod 2) X W) (l : Fin 3 → X)
    (hl2 : ∀ i, l i * l i = 1) (i : Fin 3) : W ≃ₗ[ZMod 2] W where
  toFun := ρ (l i)
  invFun := ρ (l i)
  map_add' := (ρ (l i)).map_add
  map_smul' := (ρ (l i)).map_smul
  left_inv v := by
    have h : ρ (l i) * ρ (l i) = 1 := by rw [← map_mul, hl2 i, map_one]
    exact congrArg (fun f : Module.End (ZMod 2) W => f v) h
  right_inv v := by
    have h : ρ (l i) * ρ (l i) = 1 := by rw [← map_mul, hl2 i, map_one]
    exact congrArg (fun f : Module.End (ZMod 2) W => f v) h

private theorem rhoA_flipMul_bflip (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) (i : Fin 3) :
    ∀ a v, rhoA ρ e he3 hec (flipMul i a) (bflip ρ l hl2 i v) =
      bflip ρ l hl2 i (rhoA ρ e he3 hec a v) := by
  intro a v
  have hsq : ρ (l i) * ρ (l i) = 1 := by rw [← map_mul, hl2 i, map_one]
  have hflip : rhoA ρ e he3 hec (flipMul i a) =
      ρ (l i) * ρ (eprod e a.toAdd) * ρ (l i) := by
    rw [rhoA_apply, flipMul_toAdd, ← eprod_flip e l he3 hinv hfix i a.toAdd]
    simp only [map_mul]
    rw [show (l i)⁻¹ = l i from (eq_inv_of_mul_eq_one_right (hl2 i)).symm]
  rw [hflip]
  show (ρ (l i) * ρ (eprod e a.toAdd) * ρ (l i)) (ρ (l i) v) =
    ρ (l i) (ρ (eprod e a.toAdd) v)
  simp only [Module.End.mul_apply]
  have h2 : ρ (l i) (ρ (l i) v) = v := by
    have := congrArg (fun f : Module.End (ZMod 2) W => f v) hsq
    simpa using this
  rw [h2]

theorem weightSpace_flip (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) (i : Fin 3) (H : Hyperplane A3) :
    (weightSpace (rhoA ρ e he3 hec) H.1).map (bflip ρ l hl2 i : W →ₗ[ZMod 2] W) =
      weightSpace (rhoA ρ e he3 hec) (flipH i H).1 := by
  have h := map_weightSpace (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (rhoA_flipMul_bflip ρ e l he3 hec hl2 hinv hfix i) H.1
  simpa [flipH, MulEquiv.toMonoidHom_eq_coe] using h

theorem weightSpace_flip_ne_bot (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) (i : Fin 3) (H : Hyperplane A3)
    (hH : weightSpace (rhoA ρ e he3 hec) H.1 ≠ ⊥) :
    weightSpace (rhoA ρ e he3 hec) (flipH i H).1 ≠ ⊥ := by
  intro hbot
  apply hH
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hmem : (bflip ρ l hl2 i) x ∈ weightSpace (rhoA ρ e he3 hec) (flipH i H).1 := by
    rw [← weightSpace_flip ρ e l he3 hec hl2 hinv hfix i H]
    exact Submodule.mem_map_of_mem hx
  rw [hbot] at hmem
  have h0 : (bflip ρ l hl2 i) x = 0 := by simpa using hmem
  exact (bflip ρ l hl2 i).injective (by rw [h0, map_zero])

private theorem sup_zpowers_eq_top_of_index_three {A : Type*} [Group A] {H : Subgroup A}
    (hH : H.index = 3) {c : A} (hc : c ∉ H) : H ⊔ Subgroup.zpowers c = ⊤ := by
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ Subgroup.zpowers c)
  rw [hH] at h1
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ h1) with h | h
  · exact Subgroup.index_eq_one.mp h
  · rw [h] at h1
    have h2 : H.relIndex (H ⊔ Subgroup.zpowers c) = 1 := by omega
    exact absurd (Subgroup.relIndex_eq_one.mp h2
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))) hc

theorem weightSpace_eq_zero_of_fixed_of_not_mem (ρA : Representation (ZMod 2) A3 W)
    (hA3 : ∀ a : A3, a ^ 3 = 1) {H : Hyperplane A3} {c : A3} (hc : c ∉ H.1)
    {v : W} (hv : v ∈ weightSpace ρA H.1) (hcv : ρA c v = v) : v = 0 := by
  have hsup : H.1 ⊔ Subgroup.zpowers c = ⊤ := sup_zpowers_eq_top_of_index_three H.2 hc
  have hprod : eSub H.1 * eSub (Subgroup.zpowers c) = eSub (⊤ : Subgroup A3) :=
    eSub_mul_eSub_of_sup hA3 hsup
  have hH : ρA.asAlgebraHom (eSub H.1) v = v :=
    asAlgebraHom_eSub_apply_of_mem ρA hA3 ((mem_weightSpace_iff ρA hA3 H.1 v).mp hv).1
  have hKmem : v ∈ fixedSpace ρA (Subgroup.zpowers c) := by
    intro u hu
    have hu' : u ∈ Subgroup.closure ({c} : Set A3) := by
      rwa [Subgroup.zpowers_eq_closure] at hu
    refine Subgroup.closure_induction (p := fun x _ => ρA x v = v) ?_ ?_ ?_ ?_ hu'
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hcv
    · simp
    · intro x y _ _ hpx hpy
      rw [map_mul, Module.End.mul_apply, hpy, hpx]
    · intro x _ hpx
      have hxinv : ρA x (ρA x⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have h2 : ρA x⁻¹ * ρA x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      calc ρA x⁻¹ v = (ρA x⁻¹ * ρA x) (ρA x⁻¹ v) := by rw [h2]; rfl
        _ = ρA x⁻¹ (ρA x (ρA x⁻¹ v)) := rfl
        _ = ρA x⁻¹ (ρA x v) := by rw [hxinv, hpx]
        _ = (ρA x⁻¹ * ρA x) v := rfl
        _ = v := by rw [h2]; rfl
  have hK : ρA.asAlgebraHom (eSub (Subgroup.zpowers c)) v = v :=
    asAlgebraHom_eSub_apply_of_mem ρA hA3 hKmem
  have hzero : ρA.asAlgebraHom (eSub (⊤ : Subgroup A3)) v = 0 :=
    ((mem_weightSpace_iff ρA hA3 H.1 v).mp hv).2
  have hcalc : ρA.asAlgebraHom (eSub (⊤ : Subgroup A3)) v = v := by
    rw [← hprod, map_mul, Module.End.mul_apply, hK, hH]
  rw [hcalc] at hzero
  exact hzero


private noncomputable def proj (ρA : Representation (ZMod 2) A3 W) (H : Hyperplane A3) :
    Module.End (ZMod 2) W := ρA.asAlgebraHom (eSub H.1 - eSub ⊤)

private theorem proj_mem (ρA : Representation (ZMod 2) A3 W) (H : Hyperplane A3) (x : W) :
    proj ρA H x ∈ weightSpace ρA H.1 :=
  LinearMap.mem_range.mpr ⟨x, rfl⟩

private theorem proj_apply_self (ρA : Representation (ZMod 2) A3 W) (hA3 : ∀ a : A3, a ^ 3 = 1)
    (H : Hyperplane A3) {x : W} (hx : x ∈ weightSpace ρA H.1) : proj ρA H x = x := by
  obtain ⟨y, rfl⟩ := (LinearMap.mem_range).mp hx
  have hid : proj ρA H * proj ρA H = proj ρA H := by
    simpa only [proj, eps, IsIdempotentElem]
      using (orthogonalIdempotents_asAlgebraHom_eps ρA hA3).idem (some H)
  exact congrArg (fun f : Module.End (ZMod 2) W => f y) hid

private theorem proj_apply_eq_zero (ρA : Representation (ZMod 2) A3 W) (hA3 : ∀ a : A3, a ^ 3 = 1)
    {H K : Hyperplane A3} (hHK : H ≠ K) {x : W} (hx : x ∈ weightSpace ρA K.1) :
    proj ρA H x = 0 := by
  obtain ⟨y, rfl⟩ := (LinearMap.mem_range).mp hx
  have hne : (some H : Option (Hyperplane A3)) ≠ some K := fun h => hHK (Option.some.inj h)
  have horth : proj ρA H * proj ρA K = 0 := by
    simpa only [proj, eps] using (orthogonalIdempotents_asAlgebraHom_eps ρA hA3).ortho hne
  exact congrArg (fun f : Module.End (ZMod 2) W => f y) horth

private theorem sum_proj_eq_one (ρA : Representation (ZMod 2) A3 W) (hA3 : ∀ a : A3, a ^ 3 = 1)
    (hbot : fixedSpace ρA ⊤ = ⊥) : ∑ H : Hyperplane A3, proj ρA H = 1 := by
  have hsum := sum_asAlgebraHom_eps ρA hA3
  rw [Fintype.sum_option] at hsum
  have hnone : ρA.asAlgebraHom (eps A3 none) = 0 := by
    refine LinearMap.range_eq_bot.mp ?_
    rw [show eps A3 none = eSub (⊤ : Subgroup A3) from rfl,
      show LinearMap.range (ρA.asAlgebraHom (eSub (⊤ : Subgroup A3))) = fixedSpace ρA ⊤ from
        range_asAlgebraHom_eSub ρA hA3 ⊤, hbot]
  rw [hnone, zero_add] at hsum
  simpa only [proj, eps] using hsum

private theorem apply_eq_sum_proj (ρA : Representation (ZMod 2) A3 W) (hA3 : ∀ a : A3, a ^ 3 = 1)
    (hbot : fixedSpace ρA ⊤ = ⊥) (v : W) :
    v = ∑ H : Hyperplane A3, proj ρA H v := by
  have h := congrArg (fun f : Module.End (ZMod 2) W => f v) (sum_proj_eq_one ρA hA3 hbot)
  rw [LinearMap.sum_apply, Module.End.one_apply] at h
  exact h.symm

private theorem proj_apply_eq_zero_of_mem_sup {ρA : Representation (ZMod 2) A3 W}
    (hA3 : ∀ a : A3, a ^ 3 = 1) {ι : Type*} {K : ι → Hyperplane A3} {H : Hyperplane A3}
    (hHK : ∀ i, K i ≠ H) {v : W} (hv : v ∈ ⨆ i, weightSpace ρA (K i).1) :
    proj ρA H v = 0 := by
  refine Submodule.iSup_induction (fun i => weightSpace ρA (K i).1)
    (motive := fun v => proj ρA H v = 0) hv ?_ ?_ ?_
  · intro i x hx
    exact proj_apply_eq_zero ρA hA3 (fun h => hHK i h.symm) hx
  · simp
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

private theorem eq_zero_of_forall_proj_eq_zero {ρA : Representation (ZMod 2) A3 W}
    (hA3 : ∀ a : A3, a ^ 3 = 1) (hbot : fixedSpace ρA ⊤ = ⊥) {v : W}
    (h : ∀ H : Hyperplane A3, proj ρA H v = 0) : v = 0 := by
  rw [apply_eq_sum_proj ρA hA3 hbot v]
  exact Finset.sum_eq_zero fun H _ => h H

private theorem sub_one_sq {T : W →ₗ[ZMod 2] W} (hT : T * T = 1) : (T - 1) * (T - 1) = 0 := by
  ext x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  rw [map_sub]
  have hTx : T (T x) = x := by
    have := congrArg (fun f : W →ₗ[ZMod 2] W => f x) hT
    simpa using this
  rw [hTx]
  have h2 : ∀ y : W, y + y = 0 := by
    intro y
    have h := two_smul (ZMod 2) y
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  calc (x - T x) - (T x - x) = (x + x) - (T x + T x) := by abel
    _ = 0 := by rw [h2, h2, sub_zero]

private theorem inf_ker_ne_bot {T : W →ₗ[ZMod 2] W} (hT : T * T = 1) {P : Submodule (ZMod 2) W}
    (hP : P ≠ ⊥) (hmap : ∀ x ∈ P, T x ∈ P) : P ⊓ LinearMap.ker (T - 1) ≠ ⊥ := by
  intro hbot
  apply hP
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxQ : x ∈ P ⊓ LinearMap.ker (T - 1) := by
    refine ⟨hx, ?_⟩
    show (T - 1) x = 0
    by_contra hne
    have hmem : (T - 1) x ∈ P ⊓ LinearMap.ker (T - 1) := by
      refine ⟨Submodule.sub_mem P (hmap x hx) hx, ?_⟩
      show (T - 1) ((T - 1) x) = 0
      rw [← Module.End.mul_apply, sub_one_sq hT]
      rfl
    rw [hbot] at hmem
    exact hne (by simpa using hmem)
  rw [hbot] at hxQ
  simpa using hxQ

private theorem exists_fixed_of_invariant (ρ : Representation (ZMod 2) X W) (l : Fin 3 → X)
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    {P : Submodule (ZMod 2) W} (hP : P ≠ ⊥)
    (hmap : ∀ i, ∀ x ∈ P, ρ (l i) x ∈ P) :
    ∃ v ∈ P, v ≠ 0 ∧ ∀ i, ρ (l i) v = v := by
  have hsq : ∀ i, ρ (l i) * ρ (l i) = 1 := fun i => by rw [← map_mul, hl2 i, map_one]
  have hcomm : ∀ i j, ρ (l i) * ρ (l j) = ρ (l j) * ρ (l i) := fun i j => by
    rw [← map_mul, ← map_mul, (hlc i j).eq]
  have h1 : P ⊓ LinearMap.ker (ρ (l 0) - 1) ≠ ⊥ :=
    inf_ker_ne_bot (hsq 0) hP (hmap 0)
  have hinv1 : ∀ x ∈ P ⊓ LinearMap.ker (ρ (l 0) - 1),
      ρ (l 1) x ∈ P ⊓ LinearMap.ker (ρ (l 0) - 1) := by
    intro x hx
    refine ⟨hmap 1 x hx.1, ?_⟩
    show (ρ (l 0) - 1) (ρ (l 1) x) = 0
    have hc := congrArg (fun f : Module.End (ZMod 2) W => f x) (hcomm 0 1)
    simp only [Module.End.mul_apply] at hc
    calc (ρ (l 0) - 1) (ρ (l 1) x) = ρ (l 1) ((ρ (l 0) - 1) x) := by
          simp only [LinearMap.sub_apply, Module.End.one_apply, hc, map_sub]
      _ = 0 := by rw [hx.2, map_zero]
  have h2 : P ⊓ LinearMap.ker (ρ (l 0) - 1) ⊓ LinearMap.ker (ρ (l 1) - 1) ≠ ⊥ :=
    inf_ker_ne_bot (hsq 1) h1 (fun x hx => hinv1 x hx)
  have hinv2 : ∀ x ∈ P ⊓ LinearMap.ker (ρ (l 0) - 1) ⊓ LinearMap.ker (ρ (l 1) - 1),
      ρ (l 2) x ∈ P ⊓ LinearMap.ker (ρ (l 0) - 1) ⊓ LinearMap.ker (ρ (l 1) - 1) := by
    intro x hx
    refine ⟨⟨hmap 2 x hx.1.1, ?_⟩, ?_⟩
    · show (ρ (l 0) - 1) (ρ (l 2) x) = 0
      have hc := congrArg (fun f : Module.End (ZMod 2) W => f x) (hcomm 0 2)
      simp only [Module.End.mul_apply] at hc
      calc (ρ (l 0) - 1) (ρ (l 2) x) = ρ (l 2) ((ρ (l 0) - 1) x) := by
            simp only [LinearMap.sub_apply, Module.End.one_apply, hc, map_sub]
        _ = 0 := by rw [hx.1.2, map_zero]
    · show (ρ (l 1) - 1) (ρ (l 2) x) = 0
      have hc := congrArg (fun f : Module.End (ZMod 2) W => f x) (hcomm 1 2)
      simp only [Module.End.mul_apply] at hc
      calc (ρ (l 1) - 1) (ρ (l 2) x) = ρ (l 2) ((ρ (l 1) - 1) x) := by
            simp only [LinearMap.sub_apply, Module.End.one_apply, hc, map_sub]
        _ = 0 := by rw [hx.2, map_zero]
  have h3 : P ⊓ LinearMap.ker (ρ (l 0) - 1) ⊓ LinearMap.ker (ρ (l 1) - 1) ⊓
      LinearMap.ker (ρ (l 2) - 1) ≠ ⊥ :=
    inf_ker_ne_bot (hsq 2) h2 (fun x hx => hinv2 x hx)
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ P ⊓ LinearMap.ker (ρ (l 0) - 1) ⊓
      LinearMap.ker (ρ (l 1) - 1) ⊓ LinearMap.ker (ρ (l 2) - 1), v ≠ 0 := by
    by_contra h
    push Not at h
    exact h3 ((Submodule.eq_bot_iff _).mpr fun x hx => h x hx)
  refine ⟨v, hv.1.1.1, hv0, fun i => ?_⟩
  fin_cases i
  · have h := (LinearMap.mem_ker).mp hv.1.1.2
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  · have h := (LinearMap.mem_ker).mp hv.1.2
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  · have h := (LinearMap.mem_ker).mp hv.2
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h

private def flipEps (ε : Fin 3 → ZMod 2) (f : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun j => if ε j = 0 then f j else -f j

private theorem flipEps_add (ε δ : Fin 3 → ZMod 2) (f : Fin 3 → ZMod 3) :
    flipEps (ε + δ) f = flipEps ε (flipEps δ f) := by
  funext j
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (ε j) with hε | hε <;> rcases h2 (δ j) with hδ | hδ
  · simp [flipEps, Pi.add_apply, hε, hδ]
  · simp [flipEps, Pi.add_apply, hε, hδ]
  · simp [flipEps, Pi.add_apply, hε, hδ]
  · simp [flipEps, Pi.add_apply, hε, hδ,
      show (1 : ZMod 2) + 1 = 0 from by decide]

private theorem flipEps_single (i : Fin 3) (ε : Fin 3 → ZMod 2) (f : Fin 3 → ZMod 3) :
    flipEps (ε + Pi.single i 1) f = flipC i (flipEps ε f) := by
  funext j
  by_cases hj : j = i
  · subst hj
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h2 (ε j) with h | h
    · simp [flipEps, flipC, Pi.single_eq_same, Pi.add_apply, h]
    · simp [flipEps, flipC, Pi.single_eq_same, Pi.add_apply, h,
        show (1 : ZMod 2) + 1 = 0 from by decide]
  · simp [flipEps, flipC, Pi.add_apply, Pi.single_eq_of_ne, hj]

private theorem flipEps_ne_zero {f : Fin 3 → ZMod 3} (hf : f ≠ 0) (ε : Fin 3 → ZMod 2) :
    flipEps ε f ≠ 0 := by
  intro h
  apply hf
  funext j
  have hj := congrFun h j
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (ε j) with he | he <;> simpa [flipEps, he] using hj

theorem flipC_ne_zero {f : Fin 3 → ZMod 3} (hf : f ≠ 0) (i : Fin 3) : flipC i f ≠ 0 := by
  intro h
  apply hf
  funext j
  have := congrFun h j
  by_cases hj : j = i
  · subst hj
    simp only [flipC, if_true] at this
    exact neg_eq_zero.mp this
  · simpa [flipC, hj] using this

private theorem dot3_smul (c : ZMod 3) (f z : Fin 3 → ZMod 3) :
    dot3 (c • f) z = c * dot3 f z := by
  rw [dot3, dot3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

private noncomputable def hypOf (f : Fin 3 → ZMod 3) (hf : f ≠ 0) : Hyperplane A3 :=
  ⟨kerH f, index_kerH f hf⟩

private theorem mem_hypOf (f : Fin 3 → ZMod 3) (hf : f ≠ 0) (z : A3) :
    z ∈ (hypOf f hf).1 ↔ dot3 f z.toAdd = 0 := mem_kerH

theorem map_kerH (i : Fin 3) (f : Fin 3 → ZMod 3) :
    (kerH f).map (flipMul i).toMonoidHom = kerH (flipC i f) := by
  have key : ∀ y : A3, dot3 (flipC i f) ((flipMul i) y).toAdd = dot3 f y.toAdd := by
    intro y
    rw [flipMul_toAdd, dot3, dot3, Finset.sum_congr rfl (fun j _ => ?_)]
    by_cases hj : j = i
    · subst hj
      simp only [flipC, if_true]
      rw [neg_mul, mul_neg, neg_neg]
    · simp only [flipC, if_neg hj]
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_map).mp hz
    rw [mem_kerH] at hy ⊢
    change dot3 (flipC i f) ((flipMul i) y).toAdd = 0
    rwa [key y]
  · intro hz
    rw [Subgroup.mem_map]
    refine ⟨flipMul i z, ?_, flipMul_apply_apply i z⟩
    rw [mem_kerH]
    have hkey := key (flipMul i z)
    rw [flipMul_apply_apply] at hkey
    rw [← hkey]
    exact (mem_kerH).mp hz

private theorem flipH_hypOf (i : Fin 3) (f : Fin 3 → ZMod 3) (hf : f ≠ 0) :
    flipH i (hypOf f hf) = hypOf (flipC i f) (flipC_ne_zero hf i) := by
  apply Subtype.ext
  exact map_kerH i f

private theorem weightSpace_flip_eq (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j) (i : Fin 3)
    {f : Fin 3 → ZMod 3} (hf : f ≠ 0) :
    Submodule.map (bflip ρ l hl2 i : W →ₗ[ZMod 2] W)
        (weightSpace (rhoA ρ e he3 hec) (kerH f)) =
      weightSpace (rhoA ρ e he3 hec) (kerH (flipC i f)) := by
  have h := weightSpace_flip ρ e l he3 hec hl2 hinv hfix i (hypOf f hf)
  rw [show (hypOf f hf).1 = kerH f from rfl, flipH_hypOf] at h
  exact h

private noncomputable def orbitSum (ρA : Representation (ZMod 2) A3 W) (f : Fin 3 → ZMod 3)
    (hf : f ≠ 0) : Submodule (ZMod 2) W :=
  ⨆ ε : Fin 3 → ZMod 2, weightSpace ρA (kerH (flipEps ε f))

private theorem orbitSum_ne_bot (ρA : Representation (ZMod 2) A3 W) {f : Fin 3 → ZMod 3}
    (hf : f ≠ 0)
    (h : weightSpace ρA (kerH f) ≠ ⊥) : orbitSum ρA f hf ≠ ⊥ := by
  intro hbot
  apply h
  have h0 : flipEps (0 : Fin 3 → ZMod 2) f = f := by
    funext j
    simp [flipEps]
  have hle : weightSpace ρA (kerH f) ≤ orbitSum ρA f hf := by
    calc weightSpace ρA (kerH f) = weightSpace ρA (kerH (flipEps 0 f)) := by rw [h0]
      _ ≤ orbitSum ρA f hf :=
        le_iSup (fun ε : Fin 3 → ZMod 2 => weightSpace ρA (kerH (flipEps ε f))) 0
  rw [hbot] at hle
  exact le_bot_iff.mp hle

private theorem orbitSum_map (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    {f : Fin 3 → ZMod 3} (hf : f ≠ 0) (i : Fin 3) :
    ∀ x ∈ orbitSum (rhoA ρ e he3 hec) f hf, ρ (l i) x ∈ orbitSum (rhoA ρ e he3 hec) f hf := by
  intro x hx
  refine Submodule.iSup_induction
    (fun ε : Fin 3 → ZMod 2 => weightSpace (rhoA ρ e he3 hec) (kerH (flipEps ε f)))
    (motive := fun x => ρ (l i) x ∈ orbitSum (rhoA ρ e he3 hec) f hf) hx ?_ ?_ ?_
  · intro ε y hy
    have hy' : (bflip ρ l hl2 i) y ∈ Submodule.map (bflip ρ l hl2 i : W →ₗ[ZMod 2] W)
        (weightSpace (rhoA ρ e he3 hec) (kerH (flipEps ε f))) :=
      Submodule.mem_map_of_mem hy
    rw [weightSpace_flip_eq ρ e l he3 hec hl2 hinv hfix i (flipEps_ne_zero hf ε)] at hy'
    rw [← flipEps_single] at hy'
    exact le_iSup (fun ε : Fin 3 → ZMod 2 =>
      weightSpace (rhoA ρ e he3 hec) (kerH (flipEps ε f))) (ε + Pi.single i 1) hy'
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [show ρ (l i) (a + b) = ρ (l i) a + ρ (l i) b from map_add (ρ (l i)) a b]
    exact Submodule.add_mem (orbitSum (rhoA ρ e he3 hec) f hf) ha hb

private theorem exists_fixed_in_orbitSum (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    {f : Fin 3 → ZMod 3} (hf : f ≠ 0)
    (hH : weightSpace (rhoA ρ e he3 hec) (kerH f) ≠ ⊥) :
    ∃ v ∈ orbitSum (rhoA ρ e he3 hec) f hf, v ≠ 0 ∧ ∀ i, ρ (l i) v = v :=
  exists_fixed_of_invariant ρ l hl2 hlc (orbitSum_ne_bot _ hf hH)
    (fun i x hx => orbitSum_map ρ e l he3 hec hl2 hinv hfix hf i x hx)

private def supp (f : Fin 3 → ZMod 3) : Finset (Fin 3) :=
  Finset.univ.filter fun i => f i ≠ 0

private theorem supp_flipEps (ε : Fin 3 → ZMod 2) (f : Fin 3 → ZMod 3) :
    supp (flipEps ε f) = supp f := by
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (ε i) with h | h <;> simp [flipEps, h, neg_eq_zero]

private theorem supp_eq_of_ker_eq {f g : Fin 3 → ZMod 3}
    (h : ∀ z : Fin 3 → ZMod 3, dot3 f z = 0 ↔ dot3 g z = 0) (hf : f ≠ 0) :
    supp f = supp g := by
  obtain ⟨c, hc, hg⟩ := eq_smul_of_dot3 f g h hf
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hg i]
  constructor
  · intro h0 h1
    exact h0 ((mul_eq_zero.mp h1).resolve_left hc)
  · intro h0 h1
    exact h0 (by rw [h1, mul_zero])

private theorem same_support (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hCLA : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    {f f' : Fin 3 → ZMod 3} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hH : weightSpace (rhoA ρ e he3 hec) (kerH f) ≠ ⊥)
    (hH' : weightSpace (rhoA ρ e he3 hec) (kerH f') ≠ ⊥) :
    supp f = supp f' := by
  by_contra hne
  obtain ⟨v, hv, hv0, hvfix⟩ :=
    exists_fixed_in_orbitSum ρ e l he3 hec hl2 hlc hinv hfix hf hH
  obtain ⟨v', hv', hv'0, hv'fix⟩ :=
    exists_fixed_in_orbitSum ρ e l he3 hec hl2 hlc hinv hfix hf' hH'
  have hvv : v = v' := hCLA v v' hv0 hv'0 hvfix hv'fix
  have hfam : ∀ (ε δ : Fin 3 → ZMod 2),
      hypOf (flipEps ε f) (flipEps_ne_zero hf ε) ≠
        hypOf (flipEps δ f') (flipEps_ne_zero hf' δ) := by
    intro ε δ hEq
    apply hne
    have h1 : supp (flipEps ε f) = supp (flipEps δ f') := by
      apply supp_eq_of_ker_eq _ (flipEps_ne_zero hf ε)
      intro z
      have h2 : (Multiplicative.ofAdd z) ∈ (hypOf (flipEps ε f) (flipEps_ne_zero hf ε)).1 ↔
          (Multiplicative.ofAdd z) ∈ (hypOf (flipEps δ f') (flipEps_ne_zero hf' δ)).1 := by
        rw [hEq]
      simpa [mem_hypOf, toAdd_ofAdd] using h2
    rwa [supp_flipEps, supp_flipEps] at h1
  have hall : ∀ H : Hyperplane A3, proj (rhoA ρ e he3 hec) H v = 0 := by
    intro H
    by_cases hHf : ∃ ε : Fin 3 → ZMod 2, H = hypOf (flipEps ε f) (flipEps_ne_zero hf ε)
    · obtain ⟨ε, rfl⟩ := hHf
      refine proj_apply_eq_zero_of_mem_sup (hA3 := pow_three_eq_one_of_A3)
        (K := fun δ => hypOf (flipEps δ f') (flipEps_ne_zero hf' δ)) ?_ ?_
      · intro δ hEq
        exact hfam ε δ hEq.symm
      · rw [hvv]
        exact hv'
    · push Not at hHf
      exact proj_apply_eq_zero_of_mem_sup (hA3 := pow_three_eq_one_of_A3)
        (K := fun ε => hypOf (flipEps ε f) (flipEps_ne_zero hf ε))
        (fun ε h => hHf ε h.symm) hv
  exact hv0 (eq_zero_of_forall_proj_eq_zero pow_three_eq_one_of_A3
    (fixedSpace_rhoA_eq_bot ρ e he3 hec hCY) hall)


private theorem ofAdd_single_ne_one (k : Fin 3) :
    (Multiplicative.ofAdd (Pi.single k 1) : A3) ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_one, toAdd_ofAdd] at h'
  have hk : (1 : ZMod 3) = 0 := by
    have h1 := congrFun h' k
    simpa using h1
  exact one_ne_zero hk

instance nontrivial_A3 : Nontrivial A3 :=
  ⟨Multiplicative.ofAdd (Pi.single 0 1), 1, ofAdd_single_ne_one 0⟩

private theorem supp_eq_univ_of_weightSpace_ne_bot (ρ : Representation (ZMod 2) X W)
    (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w)
    {f : Fin 3 → ZMod 3} (hf : f ≠ 0)
    (hH : weightSpace (rhoA ρ e he3 hec) (kerH f) ≠ ⊥) : supp f = Finset.univ := by
  obtain ⟨H0, hH0⟩ := exists_hyperplane_weightSpace_ne_bot (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (rhoA_injective ρ e he3 hec hfaith)
  obtain ⟨f0, hf0, hH0eq⟩ := exists_functional H0.1 H0.2
  have hH0' : weightSpace (rhoA ρ e he3 hec) (kerH f0) ≠ ⊥ := by
    rw [← hH0eq]
    exact hH0
  have hsupp : supp f = supp f0 :=
    same_support ρ e l he3 hec hl2 hlc hinv hfix hCL hCY hf hf0 hH hH0'
  rw [hsupp]
  by_contra hne
  have hex : ∃ k : Fin 3, k ∉ supp f0 := by
    by_contra h
    apply hne
    apply Finset.eq_univ_of_forall
    intro k
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  have hmem : Multiplicative.ofAdd (Pi.single k 1) ∈
      (⨅ H : {H : Hyperplane A3 // weightSpace (rhoA ρ e he3 hec) H.1 ≠ ⊥}, H.1.1) := by
    refine Subgroup.mem_iInf.mpr ?_
    rintro ⟨H, hHne⟩
    obtain ⟨g, hg, hHeq⟩ := exists_functional H.1 H.2
    have hgne : weightSpace (rhoA ρ e he3 hec) (kerH g) ≠ ⊥ := by
      rw [← hHeq]
      exact hHne
    have hgs : supp g = supp f0 :=
      same_support ρ e l he3 hec hl2 hlc hinv hfix hCL hCY hg hf0 hgne hH0'
    have hk' : k ∉ supp g := by rw [hgs]; exact hk
    have hgk : g k = 0 := by
      by_contra h
      exact hk' (by simpa [supp] using h)
    rw [hHeq, mem_kerH, toAdd_ofAdd, dot3_single, hgk]
    simp
  rw [iInf_hyperplane_weightSpace_ne_bot (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (rhoA_injective ρ e he3 hec hfaith)] at hmem
  exact ofAdd_single_ne_one k (Subgroup.mem_bot.mp hmem)

private def flipIdx0 : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

private def flipIdx1 : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

private theorem scale0 : ∀ j : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
    Lfun (flipIdx0 j) = c • flipC 0 (Lfun j) := by decide

private theorem scale1 : ∀ j : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
    Lfun (flipIdx1 j) = c • flipC 1 (Lfun j) := by decide

private theorem flipIdx0_invol (j : Fin 4) : flipIdx0 (flipIdx0 j) = j := by
  revert j
  decide

private theorem flipIdx1_invol (j : Fin 4) : flipIdx1 (flipIdx1 j) = j := by
  revert j
  decide

private theorem flipIdx0_injective : Function.Injective flipIdx0 := by
  intro j k h
  have := congrArg flipIdx0 h
  rwa [flipIdx0_invol, flipIdx0_invol] at this

private theorem flipIdx1_injective : Function.Injective flipIdx1 := by
  intro j k h
  have := congrArg flipIdx1 h
  rwa [flipIdx1_invol, flipIdx1_invol] at this

private theorem reach (j0 k : Fin 4) :
    k = j0 ∨ k = flipIdx0 j0 ∨ k = flipIdx1 j0 ∨ k = flipIdx1 (flipIdx0 j0) := by
  revert j0 k
  decide

private theorem flipKfun0 (j : Fin 4) : flipH 0 (Kfun j) = Kfun (flipIdx0 j) := by
  apply Subtype.ext
  show (kerH (Lfun j)).map (flipMul 0).toMonoidHom = kerH (Lfun (flipIdx0 j))
  rw [map_kerH]
  obtain ⟨c, hc, hscale⟩ := scale0 j
  apply Subgroup.ext
  intro z
  rw [mem_kerH, mem_kerH, hscale, dot3_smul]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc

private theorem flipKfun1 (j : Fin 4) : flipH 1 (Kfun j) = Kfun (flipIdx1 j) := by
  apply Subtype.ext
  show (kerH (Lfun j)).map (flipMul 1).toMonoidHom = kerH (Lfun (flipIdx1 j))
  rw [map_kerH]
  obtain ⟨c, hc, hscale⟩ := scale1 j
  apply Subgroup.ext
  intro z
  rw [mem_kerH, mem_kerH, hscale, dot3_smul]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc

theorem Kfun_ne_bot (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w)
    (j : Fin 4) : weightSpace (rhoA ρ e he3 hec) (Kfun j).1 ≠ ⊥ := by
  obtain ⟨H0, hH0⟩ := exists_hyperplane_weightSpace_ne_bot (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (rhoA_injective ρ e he3 hec hfaith)
  obtain ⟨f0, hf0, hH0eq⟩ := exists_functional H0.1 H0.2
  have hH0' : weightSpace (rhoA ρ e he3 hec) (kerH f0) ≠ ⊥ := by
    rw [← hH0eq]
    exact hH0
  have hfull : supp f0 = Finset.univ :=
    supp_eq_univ_of_weightSpace_ne_bot ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL hf0 hH0'
  obtain ⟨j0, hj0⟩ := exists_Lfun_ker f0 (fun i => by
    have hi : i ∈ supp f0 := by rw [hfull]; exact Finset.mem_univ i
    simpa [supp] using hi)
  have h0 : weightSpace (rhoA ρ e he3 hec) (kerH (Lfun j0)) ≠ ⊥ := by
    have hker : kerH f0 = kerH (Lfun j0) :=
      Subgroup.ext fun z => by rw [mem_kerH, mem_kerH]; exact hj0 z.toAdd
    rwa [hker] at hH0'
  have hstep0 : weightSpace (rhoA ρ e he3 hec) (kerH (Lfun (flipIdx0 j0))) ≠ ⊥ := by
    change weightSpace (rhoA ρ e he3 hec) (Kfun (flipIdx0 j0)).1 ≠ ⊥
    rw [← flipKfun0 j0]
    exact weightSpace_flip_ne_bot ρ e l he3 hec hl2 hinv hfix 0 (Kfun j0) h0
  have hstep1 : weightSpace (rhoA ρ e he3 hec) (kerH (Lfun (flipIdx1 j0))) ≠ ⊥ := by
    change weightSpace (rhoA ρ e he3 hec) (Kfun (flipIdx1 j0)).1 ≠ ⊥
    rw [← flipKfun1 j0]
    exact weightSpace_flip_ne_bot ρ e l he3 hec hl2 hinv hfix 1 (Kfun j0) h0
  rcases reach j0 j with rfl | rfl | rfl | rfl
  · exact h0
  · exact hstep0
  · exact hstep1
  · change weightSpace (rhoA ρ e he3 hec) (Kfun (flipIdx1 (flipIdx0 j0))).1 ≠ ⊥
    rw [← flipKfun1 (flipIdx0 j0)]
    exact weightSpace_flip_ne_bot ρ e l he3 hec hl2 hinv hfix 1 (Kfun (flipIdx0 j0)) hstep0

theorem weightSpace_ne_bot_iff (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w)
    (H : Hyperplane A3) :
    weightSpace (rhoA ρ e he3 hec) H.1 ≠ ⊥ ↔ ∃ j : Fin 4, H = Kfun j := by
  constructor
  · intro hH
    obtain ⟨f, hf, hHeq⟩ := exists_functional H.1 H.2
    have hH' : weightSpace (rhoA ρ e he3 hec) (kerH f) ≠ ⊥ := by
      rw [← hHeq]
      exact hH
    have hfull : supp f = Finset.univ :=
      supp_eq_univ_of_weightSpace_ne_bot ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL hf hH'
    obtain ⟨j, hj⟩ := exists_Lfun_ker f (fun i => by
      have hi : i ∈ supp f := by rw [hfull]; exact Finset.mem_univ i
      simpa [supp] using hi)
    refine ⟨j, ?_⟩
    apply Subtype.ext
    rw [hHeq]
    show kerH f = kerH (Lfun j)
    exact Subgroup.ext fun z => by rw [mem_kerH, mem_kerH]; exact hj z.toAdd
  · rintro ⟨j, rfl⟩
    exact Kfun_ne_bot ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL j


private theorem rhoA_commute_proj {ρ : Representation (ZMod 2) X W} {e l : Fin 3 → X}
    {he3 : ∀ i, e i ^ 3 = 1} {hec : ∀ i j, Commute (e i) (e j)} (c : A3) (H : Hyperplane A3) :
    rhoA ρ e he3 hec c * proj (rhoA ρ e he3 hec) H =
      proj (rhoA ρ e he3 hec) H * rhoA ρ e he3 hec c := by
  rw [show rhoA ρ e he3 hec c =
      (rhoA ρ e he3 hec).asAlgebraHom (MonoidAlgebra.of (ZMod 2) A3 c) from
    (Representation.asAlgebraHom_of _ _).symm]
  rw [proj, ← map_mul, ← map_mul]
  congr 1
  exact mul_comm _ _

private theorem sum_proj_Kfun_eq_one (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) :
    ∑ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) = 1 := by
  classical
  have h := sum_proj_eq_one (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (fixedSpace_rhoA_eq_bot ρ e he3 hec hCY)
  have hsub : ∑ H ∈ (Finset.univ.image Kfun), proj (rhoA ρ e he3 hec) H =
      ∑ H : Hyperplane A3, proj (rhoA ρ e he3 hec) H := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro H _ hH
    have hbot : weightSpace (rhoA ρ e he3 hec) H.1 = ⊥ := by
      by_contra hne
      obtain ⟨j, hj⟩ :=
        (weightSpace_ne_bot_iff ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL H).mp hne
      exact hH (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩)
    refine LinearMap.range_eq_bot.mp ?_
    rw [show LinearMap.range (proj (rhoA ρ e he3 hec) H) =
      weightSpace (rhoA ρ e he3 hec) H.1 from rfl, hbot]
  rw [← Finset.sum_image]
  · rw [hsub, h]
  · intro j _ k _ hjk
    exact Kfun_injective hjk

private theorem apply_eq_sum_proj_Kfun (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (v : W) :
    v = ∑ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) v := by
  have h := congrArg (fun f : Module.End (ZMod 2) W => f v)
    (sum_proj_Kfun_eq_one ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL)
  rw [LinearMap.sum_apply, Module.End.one_apply] at h
  exact h.symm

private theorem proj_Kfun_eq_of_sum_eq {ρA : Representation (ZMod 2) A3 W}
    (hA3 : ∀ a : A3, a ^ 3 = 1) {x y : Fin 4 → W}
    (hx : ∀ j, x j ∈ weightSpace ρA (Kfun j).1)
    (hy : ∀ j, y j ∈ weightSpace ρA (Kfun j).1)
    (h : ∑ j : Fin 4, x j = ∑ j : Fin 4, y j) : ∀ j, x j = y j := by
  intro k
  have hx' : proj ρA (Kfun k) (∑ j : Fin 4, x j) = x k := by
    rw [map_sum, Finset.sum_eq_single k]
    · exact proj_apply_self ρA hA3 _ (hx k)
    · intro j _ hjk
      exact proj_apply_eq_zero (H := Kfun k) (K := Kfun j) ρA hA3
        (fun hEq => hjk (Kfun_injective hEq.symm)) (hx j)
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hy' : proj ρA (Kfun k) (∑ j : Fin 4, y j) = y k := by
    rw [map_sum, Finset.sum_eq_single k]
    · exact proj_apply_self ρA hA3 _ (hy k)
    · intro j _ hjk
      exact proj_apply_eq_zero (H := Kfun k) (K := Kfun j) ρA hA3
        (fun hEq => hjk (Kfun_injective hEq.symm)) (hy j)
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [h, hy'] at hx'
  exact hx'.symm

private theorem proj_Kfun_flip_of {ρ : Representation (ZMod 2) X W} {e l : Fin 3 → X}
    {he3 : ∀ i, e i ^ 3 = 1} {hec : ∀ i j, Commute (e i) (e j)}
    {hl2 : ∀ i, l i * l i = 1} {hlc : ∀ i j, Commute (l i) (l j)}
    {hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹}
    {hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j}
    {hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0}
    {hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0}
    {hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w}
    (i : Fin 3) (idx : Fin 4 → Fin 4) (hinvol : ∀ j, idx (idx j) = j)
    (hinj : Function.Injective idx) (hflip : ∀ j, flipH i (Kfun j) = Kfun (idx j))
    (a : W) (ha : ρ (l i) a = a) (k : Fin 4) :
    proj (rhoA ρ e he3 hec) (Kfun k) a =
      ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) := by
  have hsum1 := apply_eq_sum_proj_Kfun ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a
  have hsum3 : (∑ j : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun j) a)) =
      ∑ k : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) := by
    refine Finset.sum_bij (fun k _ => idx k) ?_ ?_ ?_ ?_
    · intro k _
      exact Finset.mem_univ _
    · intro a1 _ a2 _ h
      exact hinj h
    · intro b _
      exact ⟨idx b, Finset.mem_univ _, hinvol b⟩
    · intro k _
      simp only [hinvol k]
  have hsum2 : a = ∑ k : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) := by
    calc a = ρ (l i) a := ha.symm
      _ = ρ (l i) (∑ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) a) :=
        congrArg (fun x => ρ (l i) x) hsum1
      _ = ∑ j : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun j) a) := by rw [map_sum]
      _ = ∑ k : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) := hsum3
  have hx : ∀ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) a ∈
      weightSpace (rhoA ρ e he3 hec) (Kfun j).1 := fun j => proj_mem _ _ _
  have hy : ∀ k : Fin 4, ρ (l i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) ∈
      weightSpace (rhoA ρ e he3 hec) (Kfun k).1 := by
    intro k
    have hm : (bflip ρ l hl2 i) (proj (rhoA ρ e he3 hec) (Kfun (idx k)) a) ∈
        Submodule.map (bflip ρ l hl2 i : W →ₗ[ZMod 2] W)
          (weightSpace (rhoA ρ e he3 hec) (Kfun (idx k)).1) :=
      Submodule.mem_map_of_mem (proj_mem _ _ _)
    rw [weightSpace_flip ρ e l he3 hec hl2 hinv hfix i (Kfun (idx k))] at hm
    rw [hflip (idx k), hinvol k] at hm
    exact hm
  exact proj_Kfun_eq_of_sum_eq pow_three_eq_one_of_A3 hx hy (by rw [← hsum1, ← hsum2]) k

private theorem proj_Kfun_flip0 (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (a : W) (ha : ρ (l 0) a = a) (k : Fin 4) :
    proj (rhoA ρ e he3 hec) (Kfun k) a =
      ρ (l 0) (proj (rhoA ρ e he3 hec) (Kfun (flipIdx0 k)) a) :=
  proj_Kfun_flip_of (ρ := ρ) (e := e) (l := l) (he3 := he3) (hec := hec) (hl2 := hl2)
    (hlc := hlc) (hinv := hinv) (hfix := hfix) (hfaith := hfaith) (hCY := hCY) (hCL := hCL)
    0 flipIdx0 flipIdx0_invol flipIdx0_injective flipKfun0 a ha k

private theorem proj_Kfun_flip1 (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (a : W) (ha : ρ (l 1) a = a) (k : Fin 4) :
    proj (rhoA ρ e he3 hec) (Kfun k) a =
      ρ (l 1) (proj (rhoA ρ e he3 hec) (Kfun (flipIdx1 k)) a) :=
  proj_Kfun_flip_of (ρ := ρ) (e := e) (l := l) (he3 := he3) (hec := hec) (hl2 := hl2)
    (hlc := hlc) (hinv := hinv) (hfix := hfix) (hfaith := hfaith) (hCY := hCY) (hCL := hCL)
    1 flipIdx1 flipIdx1_invol flipIdx1_injective flipKfun1 a ha k

theorem fpf_e (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (i : Fin 3) (w : W) (hw : ρ (e i) w = w) : w = 0 := by
  have hw' : rhoA ρ e he3 hec (Multiplicative.ofAdd (Pi.single i 1)) w = w := by
    rw [rhoA_apply, toAdd_ofAdd, eprod_single]
    exact hw
  have hproj : ∀ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) w = 0 := by
    intro j
    have hcomm := rhoA_commute_proj (ρ := ρ) (e := e) (l := l) (he3 := he3) (hec := hec)
      (Multiplicative.ofAdd (Pi.single i 1)) (Kfun j)
    have hfixw : rhoA ρ e he3 hec (Multiplicative.ofAdd (Pi.single i 1))
        (proj (rhoA ρ e he3 hec) (Kfun j) w) = proj (rhoA ρ e he3 hec) (Kfun j) w := by
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hw']
    exact weightSpace_eq_zero_of_fixed_of_not_mem (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
      (by
        rw [show (Kfun j).1 = kerH (Lfun j) from rfl, mem_kerH, toAdd_ofAdd, dot3_single]
        simpa using Lfun_coord_ne_zero j i)
      (proj_mem _ _ _) hfixw
  have hsum := apply_eq_sum_proj_Kfun ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL w
  rw [hsum]
  exact Finset.sum_eq_zero fun j _ => hproj j

theorem eq_single_of_fpf (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (c : Fin 3 → ZMod 3) (hc : c ≠ 0)
    (hfpf : ∀ w : W, ρ (eprod e c) w = w → w = 0) :
    ∃ i, ∀ j, j ≠ i → c j = 0 := by
  have hcontra : ¬((c 0 ≠ 0 ∧ c 1 ≠ 0) ∨ (c 0 ≠ 0 ∧ c 2 ≠ 0) ∨ (c 1 ≠ 0 ∧ c 2 ≠ 0)) := by
    rintro (h | h | h)
    · obtain ⟨j, hj⟩ := two_exists_Lfun_ker c (Or.inl h)
      exact hfpf_contra j hj
    · obtain ⟨j, hj⟩ := two_exists_Lfun_ker c (Or.inr (Or.inl h))
      exact hfpf_contra j hj
    · obtain ⟨j, hj⟩ := two_exists_Lfun_ker c (Or.inr (Or.inr h))
      exact hfpf_contra j hj
  exact exists_single_of_not_two c (fun h => hcontra (Or.inl h))
    (fun h => hcontra (Or.inr (Or.inl h))) (fun h => hcontra (Or.inr (Or.inr h)))
where
  hfpf_contra : ∀ (j : Fin 4), dot3 (Lfun j) c = 0 → False := by
    intro j hy
    have hmem : Multiplicative.ofAdd c ∈ (Kfun j).1 := by
      rw [show (Kfun j).1 = kerH (Lfun j) from rfl, mem_kerH, toAdd_ofAdd]
      exact hy
    have hne : weightSpace (rhoA ρ e he3 hec) (Kfun j).1 ≠ ⊥ :=
      Kfun_ne_bot ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL j
    obtain ⟨w, hw, hw0⟩ : ∃ w ∈ weightSpace (rhoA ρ e he3 hec) (Kfun j).1, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Submodule.eq_bot_iff _).mpr hcon)
    have hfixw : rhoA ρ e he3 hec (Multiplicative.ofAdd c) w = w :=
      ((mem_weightSpace_iff (rhoA ρ e he3 hec) pow_three_eq_one_of_A3 (Kfun j).1 w).mp hw).1 _ hmem
    have hcw : ρ (eprod e c) w = w := by
      have h := hfixw
      rwa [rhoA_apply, toAdd_ofAdd] at h
    exact hw0 (hfpf w hcw)

theorem eq_zero_of_fix (ρ : Representation (ZMod 2) X W) (e l : Fin 3 → X)
    (he3 : ∀ i, e i ^ 3 = 1) (hec : ∀ i j, Commute (e i) (e j))
    (hl2 : ∀ i, l i * l i = 1) (hlc : ∀ i j, Commute (l i) (l j))
    (hinv : ∀ i, l i * e i * (l i)⁻¹ = (e i)⁻¹)
    (hfix : ∀ i j, i ≠ j → l i * e j * (l i)⁻¹ = e j)
    (hfaith : ∀ c : Fin 3 → ZMod 3, ρ (eprod e c) = 1 → c = 0)
    (hCY : ∀ w : W, (∀ i, ρ (e i) w = w) → w = 0)
    (hCL : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ i, ρ (l i) v = v) → (∀ i, ρ (l i) w = w) →
      v = w) (a : W) (ha : a ≠ 0) (haL : ∀ i, ρ (l i) a = a) (c : Fin 3 → ZMod 3)
    (hc : ρ (eprod e c) a = a) : c = 0 := by
  have hca : rhoA ρ e he3 hec (Multiplicative.ofAdd c) a = a := by
    rw [rhoA_apply, toAdd_ofAdd]
    exact hc
  have hcomp : ∀ k : Fin 4, proj (rhoA ρ e he3 hec) (Kfun k) a ≠ 0 := by
    intro k
    by_contra hk
    have hzero : ∀ j : Fin 4, proj (rhoA ρ e he3 hec) (Kfun j) a = 0 := by
      intro j
      rcases reach k j with h | h | h | h
      · rw [h]
        exact hk
      · rw [h]
        rw [proj_Kfun_flip0 ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a (haL 0)
          (flipIdx0 k)]
        rw [flipIdx0_invol, hk, map_zero]
      · rw [h]
        rw [proj_Kfun_flip1 ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a (haL 1)
          (flipIdx1 k)]
        rw [flipIdx1_invol, hk, map_zero]
      · rw [h]
        rw [proj_Kfun_flip1 ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a (haL 1)
          (flipIdx1 (flipIdx0 k))]
        rw [flipIdx1_invol]
        rw [proj_Kfun_flip0 ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a (haL 0)
          (flipIdx0 k)]
        rw [flipIdx0_invol, hk, map_zero, map_zero]
    have hzero2 : a = 0 := by
      rw [apply_eq_sum_proj_Kfun ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL a]
      exact Finset.sum_eq_zero fun j _ => hzero j
    exact ha hzero2
  have hcJ : ∀ k : Fin 4, Multiplicative.ofAdd c ∈ (Kfun k).1 := by
    intro k
    by_contra hck
    have hcomm := rhoA_commute_proj (ρ := ρ) (e := e) (l := l) (he3 := he3) (hec := hec)
      (Multiplicative.ofAdd c) (Kfun k)
    have hfixc : rhoA ρ e he3 hec (Multiplicative.ofAdd c)
        (proj (rhoA ρ e he3 hec) (Kfun k) a) = proj (rhoA ρ e he3 hec) (Kfun k) a := by
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hca]
    exact hcomp k (weightSpace_eq_zero_of_fixed_of_not_mem (rhoA ρ e he3 hec)
      pow_three_eq_one_of_A3 hck (proj_mem _ _ _) hfixc)
  have hmem : Multiplicative.ofAdd c ∈
      (⨅ H : {H : Hyperplane A3 // weightSpace (rhoA ρ e he3 hec) H.1 ≠ ⊥}, H.1.1) := by
    refine Subgroup.mem_iInf.mpr ?_
    rintro ⟨H, hHne⟩
    obtain ⟨j, rfl⟩ :=
      (weightSpace_ne_bot_iff ρ e l he3 hec hl2 hlc hinv hfix hfaith hCY hCL H).mp hHne
    exact hcJ j
  rw [iInf_hyperplane_weightSpace_ne_bot (rhoA ρ e he3 hec) pow_three_eq_one_of_A3
    (rhoA_injective ρ e he3 hec hfaith)] at hmem
  have h1 : Multiplicative.ofAdd c = 1 := Subgroup.mem_bot.mp hmem
  apply Multiplicative.toAdd.injective
  have h2 := congrArg Multiplicative.toAdd h1
  rwa [toAdd_ofAdd, toAdd_one] at h2

end CFSG.GF2Type.Smith1979.TriConf

end
