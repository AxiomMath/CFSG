module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Facts
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

open CFSG.Open Matrix

section Ppow

variable {M N : Type*} [Group M] [Group N]

@[expose] def ppowN (c : Fin 4 → M) (n : Fin 4 → ℕ) : M := (List.ofFn fun i => c i ^ n i).prod

@[expose] def ppow {m : ℕ} (c : Fin 4 → M) (n : Fin 4 → ZMod m) : M := ppowN c fun i => (n i).val

theorem ppowN_def (c : Fin 4 → M) (n : Fin 4 → ℕ) :
    ppowN c n = c 0 ^ n 0 * (c 1 ^ n 1 * (c 2 ^ n 2 * c 3 ^ n 3)) := by
  simp [ppowN, List.ofFn_succ]

theorem map_ppowN (f : M →* N) (c : Fin 4 → M) (n : Fin 4 → ℕ) :
    f (ppowN c n) = ppowN (fun i => f (c i)) n := by
  simp [ppowN_def]

theorem ppowN_zero (c : Fin 4 → M) : ppowN c 0 = 1 := by simp [ppowN_def]

theorem ppowN_add (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j)) (n n' : Fin 4 → ℕ) :
    ppowN c (n + n') = ppowN c n * ppowN c n' := by
  classical
  let A : Subgroup M := Subgroup.closure (Set.range c)
  have : IsMulCommutative A := Subgroup.isMulCommutative_closure
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  let c' : Fin 4 → A := fun i => ⟨c i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have key : ∀ n, ppowN c n = A.subtype (ppowN c' n) := fun n => by rw [map_ppowN]; rfl
  rw [key, key, key, ← map_mul]
  congr 1
  simp only [ppowN, List.prod_ofFn, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem ppowN_smul (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j)) (k : ℕ) (n : Fin 4 → ℕ) :
    ppowN c (k • n) = ppowN c n ^ k := by
  induction k with
  | zero => simp [ppowN_zero]
  | succ k ih => rw [succ_nsmul, ppowN_add c hc, ih, pow_succ]

theorem ppowN_congr_mod {m : ℕ} (c : Fin 4 → M) (hm : ∀ i, c i ^ m = 1) {n n' : Fin 4 → ℕ}
    (h : ∀ i, n i % m = n' i % m) : ppowN c n = ppowN c n' := by
  simp only [ppowN_def]
  rw [pow_eq_pow_mod (n 0) (hm 0), pow_eq_pow_mod (n 1) (hm 1), pow_eq_pow_mod (n 2) (hm 2),
    pow_eq_pow_mod (n 3) (hm 3), pow_eq_pow_mod (n' 0) (hm 0), pow_eq_pow_mod (n' 1) (hm 1),
    pow_eq_pow_mod (n' 2) (hm 2), pow_eq_pow_mod (n' 3) (hm 3), h 0, h 1, h 2, h 3]

section ZMod

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
theorem ppow_def (c : Fin 4 → M) (n : Fin 4 → ZMod m) :
    ppow c n = c 0 ^ (n 0).val * (c 1 ^ (n 1).val * (c 2 ^ (n 2).val * c 3 ^ (n 3).val)) :=
  ppowN_def c _

omit [NeZero m] in
theorem map_ppow (f : M →* N) (c : Fin 4 → M) (n : Fin 4 → ZMod m) :
    f (ppow c n) = ppow (fun i => f (c i)) n := map_ppowN f c _

omit [NeZero m] in
theorem ppow_zero (c : Fin 4 → M) : ppow c (0 : Fin 4 → ZMod m) = 1 := by
  simp [ppow, ppowN_def]

theorem ppow_add (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j)) (hm : ∀ i, c i ^ m = 1)
    (n n' : Fin 4 → ZMod m) : ppow c (n + n') = ppow c n * ppow c n' := by
  unfold ppow
  rw [← ppowN_add c hc]
  exact ppowN_congr_mod c hm fun i => by simp [ZMod.val_add]

omit [NeZero m] in
theorem ppow_smul (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j)) (hm : ∀ i, c i ^ m = 1)
    (a : ZMod m) (w : Fin 4 → ZMod m) : ppow c (a • w) = ppow c w ^ a.val := by
  unfold ppow
  rw [← ppowN_smul c hc]
  exact ppowN_congr_mod c hm fun i => by simp [ZMod.val_mul]

omit [NeZero m] in
theorem ppow_single [Fact (1 < m)] (c : Fin 4 → M) (i : Fin 4) :
    ppow c (Pi.single i 1 : Fin 4 → ZMod m) = c i := by
  fin_cases i <;> simp [ppow_def, ZMod.val_one]

theorem ppow_vecMul (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j)) (hm : ∀ i, c i ^ m = 1)
    (U : Matrix (Fin 4) (Fin 4) (ZMod m)) (v : Fin 4 → ZMod m) :
    ppow (fun i => ppow c (U i)) v = ppow c (v ᵥ* U) := by
  have h : v ᵥ* U = ∑ i, v i • U i := by
    ext j; simp [vecMul, dotProduct, Finset.sum_apply]
  rw [h, Fin.sum_univ_four, ppow_add c hc hm, ppow_add c hc hm, ppow_add c hc hm,
    ppow_smul c hc hm, ppow_smul c hc hm, ppow_smul c hc hm, ppow_smul c hc hm, ppow_def]
  simp only [mul_assoc]

end ZMod

end Ppow

section VecE

variable {G : Type*} [Group G]

@[expose] def vecE (e : Fin 4 → G) (v : Vec) : G := (List.ofFn fun i => e i ^ (v i).val).prod

theorem vecE_eq_ppow (e : Fin 4 → G) (v : Vec) : vecE e v = ppow e v := rfl

structure IsBasisFam (e : Fin 4 → G) : Prop where
  comm : ∀ i j, Commute (e i) (e j)
  sq : ∀ i, e i ^ 2 = 1

variable {e : Fin 4 → G}

theorem vecE_zero : vecE e 0 = 1 := ppow_zero e

theorem vecE_add (he : IsBasisFam e) (v w : Vec) : vecE e (v + w) = vecE e v * vecE e w :=
  ppow_add e he.comm he.sq v w

theorem vecE_smul (he : IsBasisFam e) (a : ZMod 2) (w : Vec) : vecE e (a • w) = vecE e w ^ a.val :=
  ppow_smul e he.comm he.sq a w

theorem vecE_single (i : Fin 4) : vecE e (Pi.single i 1) = e i := ppow_single e i

theorem vecE_vecMul (he : IsBasisFam e) (U : Mat) (v : Vec) :
    vecE e (v ᵥ* U) = ppow (fun i => vecE e (U i)) v :=
  (ppow_vecMul e he.comm he.sq U v).symm

theorem vecE_sq (he : IsBasisFam e) (v : Vec) : vecE e v * vecE e v = 1 := by
  rw [← vecE_add he, ← vecE_zero (e := e)]
  congr 1
  ext i
  simp [CharTwo.add_self_eq_zero]

theorem vecE_inv (he : IsBasisFam e) (v : Vec) : (vecE e v)⁻¹ = vecE e v :=
  inv_eq_of_mul_eq_one_right (vecE_sq he v)

theorem map_vecE {H : Type*} [Group H] (f : G →* H) (e : Fin 4 → G) (v : Vec) :
    f (vecE e v) = vecE (fun i => f (e i)) v := map_ppow f e v

theorem hom_vecE (he : IsBasisFam e) (f : G →* G) (ρ : Mat) (hf : ∀ i, f (e i) = vecE e (ρ i))
    (v : Vec) : f (vecE e v) = vecE e (v ᵥ* ρ) := by
  rw [map_vecE, vecE_vecMul he]
  simp only [hf]
  rfl

section Basis

variable {E : Subgroup G}

theorem isBasisFam_of (hE : E = Subgroup.closure (Set.range e)) (hEab : IsElemAbelian 2 E) :
    IsBasisFam e := by
  have hmem : ∀ i, e i ∈ E := fun i => hE ▸ Subgroup.subset_closure ⟨i, rfl⟩
  refine ⟨fun i j => ?_, fun i => hEab.2 _ (hmem i)⟩
  have : IsMulCommutative E := hEab.1
  have := (mul_comm' (⟨e i, hmem i⟩ : E) ⟨e j, hmem j⟩)
  exact congrArg Subtype.val this

theorem vecE_mem (hE : E = Subgroup.closure (Set.range e)) (v : Vec) : vecE e v ∈ E := by
  have hmem : ∀ i, e i ∈ E := fun i => hE ▸ Subgroup.subset_closure ⟨i, rfl⟩
  unfold vecE
  refine E.list_prod_mem fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact E.pow_mem (hmem i) _

theorem exists_vecE (hE : E = Subgroup.closure (Set.range e)) (hEab : IsElemAbelian 2 E)
    {a : G} (ha : a ∈ E) : ∃ v, a = vecE e v := by
  have he := isBasisFam_of hE hEab
  let T : Subgroup G :=
    { carrier := Set.range (vecE e)
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v + w, vecE_add he v w⟩
      one_mem' := ⟨0, vecE_zero⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        exact ⟨v, (vecE_inv he v).symm⟩ }
  have : E ≤ T := by
    rw [hE, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, vecE_single i⟩
  obtain ⟨v, hv⟩ := this ha
  exact ⟨v, hv.symm⟩

theorem vecE_injective (hE : E = Subgroup.closure (Set.range e)) (hEab : IsElemAbelian 2 E)
    (hcard : Nat.card E = 16) : Function.Injective (vecE e) := by
  let f : Vec → E := fun v => ⟨vecE e v, vecE_mem hE v⟩
  have hf : Function.Bijective f := by
    refine (Nat.bijective_iff_surjective_and_card f).2 ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨v, hv⟩ := exists_vecE hE hEab ha
      exact ⟨v, Subtype.ext hv.symm⟩
    · rw [hcard]; simp [Nat.card_eq_fintype_card]
  intro v w h
  exact hf.1 (Subtype.ext h)

end Basis

end VecE

section Class2

variable {M : Type*} [Group M]

@[expose] def cm (x y : M) : M := x * y * x⁻¹ * y⁻¹

theorem cm_one_left (y : M) : cm 1 y = 1 := by simp [cm]
theorem cm_one_right (x : M) : cm x 1 = 1 := by simp [cm]
theorem cm_self (x : M) : cm x x = 1 := by simp [cm]
theorem cm_swap (x y : M) : cm x y = (cm y x)⁻¹ := by simp only [cm]; group

theorem cm_eq_one_iff {x y : M} : cm x y = 1 ↔ x * y = y * x := by
  unfold cm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem cm_mul_left_aux (a b c : M) (h : ∀ z, cm b c * z = z * cm b c) :
    cm (a * b) c = cm a c * cm b c := by
  have h1 : cm (a * b) c = a * cm b c * a⁻¹ * cm a c := by simp only [cm]; group
  have h2 : a * cm b c * a⁻¹ = cm b c := by rw [← h a]; simp
  rw [h1, h2, h]

theorem cm_mul_right_aux (a b c : M) (h : ∀ z, cm a c * z = z * cm a c) :
    cm a (b * c) = cm a b * cm a c := by
  have h1 : cm a (b * c) = cm a b * (b * cm a c * b⁻¹) := by simp only [cm]; group
  have h2 : b * cm a c * b⁻¹ = cm a c := by rw [← h b]; simp
  rw [h1, h2]

theorem sq_mul_aux (a b : M) (h : ∀ z, cm b a * z = z * cm b a) :
    (a * b) * (a * b) = a * a * (b * b) * cm b a := by
  have e : b * a = cm b a * (a * b) := by simp only [cm]; group
  have h1 : (a * b) * (a * b) = cm b a * (a * a * (b * b)) := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (cm b a * (a * b)) * b := by rw [e]
      _ = (a * cm b a) * (a * b * b) := by group
      _ = (cm b a * a) * (a * b * b) := by rw [h a]
      _ = cm b a * (a * a * (b * b)) := by group
  rw [h1, h]

def cmL (hc : ∀ x y z : M, cm x y * z = z * cm x y) (y : M) : M →* M where
  toFun x := cm x y
  map_one' := cm_one_left y
  map_mul' a b := cm_mul_left_aux a b y (hc b y)

def cmR (hc : ∀ x y z : M, cm x y * z = z * cm x y) (x : M) : M →* M where
  toFun y := cm x y
  map_one' := cm_one_right x
  map_mul' a b := cm_mul_right_aux x a b (hc x b)

theorem cm_ppow (hc : ∀ x y z : M, cm x y * z = z * cm x y) {m n : ℕ} [NeZero m] [NeZero n]
    (κ κ' : Fin 4 → M) (a : Fin 4 → ZMod m) (b : Fin 4 → ZMod n) :
    cm (ppow κ a) (ppow κ' b) =
      ppow (fun i => ppow (fun j => cm (κ i) (κ' j)) b) a := by
  have h1 : cm (ppow κ a) (ppow κ' b) = cmL hc (ppow κ' b) (ppow κ a) := rfl
  rw [h1, map_ppow]
  congr 1
  funext i
  have h2 : cmL hc (ppow κ' b) (κ i) = cmR hc (κ i) (ppow κ' b) := rfl
  rw [h2, map_ppow]
  rfl

end Class2

section TwoBit

variable {Q : Type*} [Group Q]

def tp (τ : Q) (b : ZMod 2) : Q := τ ^ b.val

structure TauData (τ : Q) : Prop where
  central : ∀ z, τ * z = z * τ
  sq : τ * τ = 1
  ne : τ ≠ 1

section tp

variable {τ : Q} (hτ : TauData τ)
include hτ

omit hτ in
theorem tp_zero : tp τ 0 = 1 := by simp [tp]

omit hτ in
theorem tp_one : tp τ 1 = τ := by simp [tp, ZMod.val_one]

theorem tp_add (a b : ZMod 2) : tp τ (a + b) = tp τ a * tp τ b := by
  unfold tp
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ (by rw [pow_two]; exact hτ.sq)).symm

theorem tp_inj {a b : ZMod 2} (h : tp τ a = tp τ b) : a = b := by
  have h0 : tp τ 0 = 1 := tp_zero
  have h1 : tp τ 1 = τ := tp_one
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases this a with rfl | rfl <;> rcases this b with rfl | rfl
  · rfl
  · rw [h0, h1] at h; exact absurd h.symm hτ.ne
  · rw [h0, h1] at h; exact absurd h hτ.ne
  · rfl

theorem tp_mul_self (b : ZMod 2) : tp τ b * tp τ b = 1 := by
  rw [← tp_add hτ, CharTwo.add_self_eq_zero, tp_zero]

theorem tp_inv (b : ZMod 2) : (tp τ b)⁻¹ = tp τ b :=
  inv_eq_of_mul_eq_one_right (tp_mul_self hτ b)

theorem tp_central (b : ZMod 2) (z : Q) : tp τ b * z = z * tp τ b :=
  (Commute.pow_left (hτ.central z) _).eq

omit hτ in
theorem tp_pow (a b : ZMod 2) : tp τ b ^ a.val = tp τ (a * b) := by
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases this a with rfl | rfl
  · simp [tp_zero]
  · simp [ZMod.val_one]

omit hτ in
theorem map_tp (s : Q →* Q) (hs : s τ = τ) (b : ZMod 2) : s (tp τ b) = tp τ b := by
  simp [tp, hs]

end tp

structure BitData (τ : Q) (sb : Q → ZMod 2) (cb : Q → Q → ZMod 2) : Prop where
  tau : TauData τ
  hsb : ∀ x, x * x = tp τ (sb x)
  hcb : ∀ x y, cm x y = tp τ (cb x y)

section bits

variable {τ : Q} {sb : Q → ZMod 2} {cb : Q → Q → ZMod 2} (hB : BitData τ sb cb)
include hB

theorem BitData.hc (x y z : Q) : cm x y * z = z * cm x y := by
  rw [hB.hcb]; exact tp_central hB.tau _ _

theorem cb_mul_left (a b c : Q) : cb (a * b) c = cb a c + cb b c := by
  apply tp_inj hB.tau
  rw [← hB.hcb, tp_add hB.tau, ← hB.hcb, ← hB.hcb]
  exact cm_mul_left_aux a b c (hB.hc b c)

theorem cb_symm (a b : Q) : cb a b = cb b a := by
  apply tp_inj hB.tau
  rw [← hB.hcb, cm_swap, hB.hcb, tp_inv hB.tau]

theorem cb_self (a : Q) : cb a a = 0 := by
  apply tp_inj hB.tau
  rw [← hB.hcb, cm_self, tp_zero]

theorem cb_tp_mul (b : ZMod 2) (x y : Q) : cb (tp τ b * x) y = cb x y := by
  rw [cb_mul_left hB]
  have : cb (tp τ b) y = 0 := by
    apply tp_inj hB.tau
    rw [← hB.hcb, tp_zero, cm_eq_one_iff]
    exact tp_central hB.tau _ _
  rw [this, zero_add]

theorem cb_mul_tp (b : ZMod 2) (x y : Q) : cb x (tp τ b * y) = cb x y := by
  rw [cb_symm hB, cb_tp_mul hB, cb_symm hB]

theorem sb_mul (a b : Q) : sb (a * b) = sb a + sb b + cb b a := by
  apply tp_inj hB.tau
  rw [← hB.hsb, sq_mul_aux a b (hB.hc b a), tp_add hB.tau, tp_add hB.tau, ← hB.hsb,
    ← hB.hsb, ← hB.hcb]

theorem sb_one : sb 1 = 0 := by
  apply tp_inj hB.tau
  rw [← hB.hsb, tp_zero, mul_one]

theorem sb_tp_mul (b : ZMod 2) (x : Q) : sb (tp τ b * x) = sb x := by
  rw [sb_mul hB]
  have h1 : sb (tp τ b) = 0 := by
    apply tp_inj hB.tau
    rw [← hB.hsb, tp_zero, tp_mul_self hB.tau]
  have h2 : cb x (tp τ b) = 0 := by
    apply tp_inj hB.tau
    rw [← hB.hcb, tp_zero, cm_eq_one_iff]
    exact (tp_central hB.tau _ _).symm
  rw [h1, h2]; simp

theorem sb_map (s : Q →* Q) (hs : s τ = τ) (x : Q) : sb (s x) = sb x := by
  apply tp_inj hB.tau
  rw [← hB.hsb (s x), ← map_mul, hB.hsb, map_tp s hs]

theorem cb_map (s : Q →* Q) (hs : s τ = τ) (x y : Q) : cb (s x) (s y) = cb x y := by
  apply tp_inj hB.tau
  rw [← hB.hcb (s x) (s y)]
  have : cm (s x) (s y) = s (cm x y) := by simp [cm]
  rw [this, hB.hcb, map_tp s hs]

theorem cb_one_left (y : Q) : cb 1 y = 0 := by
  have := cb_mul_left hB 1 1 y
  simpa using this

theorem sb_pw (x : Q) (a : ZMod 2) : sb (x ^ a.val) = a * sb x := by
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases this a with rfl | rfl
  · simp [sb_one hB]
  · simp [ZMod.val_one]

theorem cb_pw (x y : Q) (a b : ZMod 2) : cb (x ^ a.val) (y ^ b.val) = a * b * cb x y := by
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h1 : ∀ y, cb y 1 = 0 := fun y => by rw [cb_symm hB, cb_one_left hB]
  rcases this a with rfl | rfl <;> rcases this b with rfl | rfl <;>
    simp [cb_one_left hB, h1, ZMod.val_one]

end bits

theorem ppow_tp {τ : Q} (hτ : TauData τ) (g b : Fin 4 → ZMod 2) :
    ppow (fun n => tp τ (g n)) b = tp τ (∑ n, b n * g n) := by
  rw [ppow_def]
  simp only [tp_pow, Fin.sum_univ_four, tp_add hτ, add_assoc]

section bits2

variable {τ : Q} {sb : Q → ZMod 2} {cb : Q → Q → ZMod 2} (hB : BitData τ sb cb)
include hB

theorem cb_ppow (κ κ' : Fin 4 → Q) (a b : Fin 4 → ZMod 2) :
    cb (ppow κ a) (ppow κ' b) = ∑ m, a m * ∑ n, b n * cb (κ m) (κ' n) := by
  apply tp_inj hB.tau
  rw [← hB.hcb, cm_ppow hB.hc]
  simp only [hB.hcb, ppow_tp hB.tau]

theorem sb_ppow (κ : Fin 4 → Q) (a : Fin 4 → ZMod 2) :
    sb (ppow κ a) = ∑ m, a m * sb (κ m) +
      ∑ m, ∑ n, (if m < n then a m * a n * cb (κ m) (κ n) else 0) := by
  rw [ppow_def]
  simp only [sb_mul hB, cb_mul_left hB, sb_pw hB, cb_pw hB]
  have s10 := cb_symm hB (κ 1) (κ 0)
  have s20 := cb_symm hB (κ 2) (κ 0)
  have s30 := cb_symm hB (κ 3) (κ 0)
  have s21 := cb_symm hB (κ 2) (κ 1)
  have s31 := cb_symm hB (κ 3) (κ 1)
  have s32 := cb_symm hB (κ 3) (κ 2)
  simp [Fin.sum_univ_four, s10, s20, s30, s21, s31, s32]
  ring

end bits2

end TwoBit

section Gamma

open Subgroup

variable {Γ : Type*} [Group Γ]

structure Data (E : Subgroup Γ) (t : Γ) (e : Fin 4 → Γ) : Prop where
  hE : E = Subgroup.closure (Set.range e)
  hEab : IsElemAbelian 2 E
  hE16 : Nat.card E = 16
  hEc : ∀ a ∈ E, ∀ b, a * b = b * a
  ht2 : t * t = 1
  htE : t ∉ E
  hKt : ∀ k, k * t = t * k → k ∈ zpowers t ⊔ E
  hφ : ∀ k, cm k t ∈ E
  hφs : ∀ a ∈ E, ∃ k, cm k t = a

variable {E : Subgroup Γ} {t : Γ} {e : Fin 4 → Γ}

theorem Data.basis (D : Data E t e) : IsBasisFam e := isBasisFam_of D.hE D.hEab

theorem Data.normal (D : Data E t e) : E.Normal :=
  ⟨fun n hn g => by
    have h := D.hEc n hn g
    have : g * n * g⁻¹ = n := by rw [← h]; simp
    rw [this]; exact hn⟩

theorem Data.sq_E (D : Data E t e) {u : Γ} (hu : u ∈ E) : u * u = 1 := by
  have := D.hEab.2 u hu
  rwa [pow_two] at this

theorem Data.mem_X (D : Data E t e) {x : Γ} : x ∈ zpowers t ⊔ E ↔ x ∈ E ∨ ∃ u ∈ E, x = t * u := by
  have := D.normal
  constructor
  · intro hx
    have hx' : x ∈ ((zpowers t ⊔ E : Subgroup Γ) : Set Γ) := hx
    rw [Subgroup.mul_normal] at hx'
    obtain ⟨a, ha, u, hu, rfl⟩ := hx'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ha
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact D.ht2
    rw [zpow_eq_zpow_emod n h2]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [h]; simpa using hu
    · right; exact ⟨u, hu, by rw [h]; simp⟩
  · rintro (hx | ⟨u, hu, rfl⟩)
    · exact mem_sup_right hx
    · exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hu)

@[expose] def Data.phi (D : Data E t e) : Γ →* Γ where
  toFun k := cm k t
  map_one' := cm_one_left t
  map_mul' a b := cm_mul_left_aux a b t (fun z => D.hEc _ (D.hφ b) z)

theorem Data.phi_apply (D : Data E t e) (k : Γ) : D.phi k = cm k t := rfl

theorem Data.phi_mem (D : Data E t e) (k : Γ) : D.phi k ∈ E := D.hφ k

theorem Data.mem_X_of_phi (D : Data E t e) {k : Γ} (h : D.phi k = 1) : k ∈ zpowers t ⊔ E :=
  D.hKt k (cm_eq_one_iff.1 h)

theorem Data.phi_of_mem_E (D : Data E t e) {u : Γ} (hu : u ∈ E) : D.phi u = 1 :=
  cm_eq_one_iff.2 (D.hEc u hu t)

theorem Data.phi_cm (D : Data E t e) (a b : Γ) : D.phi (cm a b) = 1 := by
  have : D.phi (cm a b) = cm (D.phi a) (D.phi b) := by simp [cm]
  rw [this]
  exact cm_eq_one_iff.2 (D.hEc _ (D.phi_mem a) _)

theorem Data.phi_sq (D : Data E t e) (a : Γ) : D.phi (a * a) = 1 := by
  rw [map_mul]
  exact D.sq_E (D.phi_mem a)

theorem Data.exists_vecE (D : Data E t e) {a : Γ} (ha : a ∈ E) : ∃ v, a = vecE e v :=
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2.exists_vecE D.hE D.hEab ha

theorem Data.phi_ppow (D : Data E t e) {k : Fin 4 → Γ} (hk : ∀ i, cm (k i) t = e i) (v : Vec) :
    D.phi (ppow k v) = vecE e v := by
  rw [map_ppow]
  simp only [Data.phi_apply, hk]
  rfl

theorem Data.exists_NF (D : Data E t e) {k : Fin 4 → Γ} (hk : ∀ i, cm (k i) t = e i) {a : Γ}
    {v : Vec} (hv : D.phi a = vecE e v) : ∃ x ∈ zpowers t ⊔ E, a = x * ppow k v := by
  refine ⟨a * (ppow k v)⁻¹, D.mem_X_of_phi ?_, by simp⟩
  rw [map_mul, map_inv, hv, D.phi_ppow hk, mul_inv_cancel]

theorem Data.stage1 [Finite Γ] (D : Data E t e) {k : Fin 4 → Γ} (hk : ∀ i, cm (k i) t = e i)
    (ρ : Fin 2 → Mat) (hQ : QuadRigid ρ) (σ : Fin 2 → Γ →* Γ) (hσt : ∀ j, σ j t = t)
    (hσe : ∀ j i, σ j (e i) = vecE e (ρ j i)) :
    (∀ a b, cm a b ∈ E) ∧ (∀ a, a * a ∈ E) := by
  have := D.normal
  have he := D.basis
  let π : Γ →* Γ ⧸ E := QuotientGroup.mk' E
  have hπ : ∀ a, π a = 1 ↔ a ∈ E := fun a => QuotientGroup.eq_one_iff a
  set τ : Γ ⧸ E := π t with hτdef
  have hτ : TauData τ := by
    refine ⟨fun z => ?_, ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      have : t * g = cm t g * (g * t) := by simp only [cm]; group
      have hm : cm t g ∈ E := by
        rw [cm_swap]; exact E.inv_mem (D.hφ g)
      change π t * π g = π g * π t
      rw [← map_mul, ← map_mul, this, map_mul, (hπ _).2 hm, one_mul]
    · rw [hτdef, ← map_mul, D.ht2, map_one]
    · rw [hτdef, Ne, hπ]; exact D.htE
  have hX : ∀ x ∈ zpowers t ⊔ E, ∃ b, π x = tp τ b := by
    intro x hx
    rcases D.mem_X.1 hx with hx | ⟨u, hu, rfl⟩
    · exact ⟨0, by rw [(hπ _).2 hx, tp_zero]⟩
    · exact ⟨1, by rw [map_mul, (hπ _).2 hu, mul_one, tp_one]⟩
  have hcm : ∀ x y : Γ ⧸ E, ∃ b, cm x y = tp τ b := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨c, hc⟩ := hX (cm a b) (D.mem_X_of_phi (D.phi_cm a b))
    exact ⟨c, by simpa [cm, π] using hc⟩
  have hsq : ∀ x : Γ ⧸ E, ∃ b, x * x = tp τ b := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨c, hc⟩ := hX (a * a) (D.mem_X_of_phi (D.phi_sq a))
    exact ⟨c, by simpa [π] using hc⟩
  choose cb hcb using hcm
  choose sb hsb using hsq
  have hB : BitData τ sb cb := ⟨hτ, hsb, hcb⟩
  have hle : ∀ j, E ≤ E.comap (σ j) := by
    intro j u hu
    obtain ⟨v, rfl⟩ := D.exists_vecE hu
    rw [mem_comap, hom_vecE he (σ j) (ρ j) (hσe j)]
    exact vecE_mem D.hE _
  let σb : Fin 2 → (Γ ⧸ E →* Γ ⧸ E) := fun j => QuotientGroup.map E E (σ j) (hle j)
  have hσb : ∀ j a, σb j (π a) = π (σ j a) := fun j a => rfl
  have hσbτ : ∀ j, σb j τ = τ := fun j => by rw [hτdef, hσb, hσt]
  let κ : Fin 4 → Γ ⧸ E := fun i => π (k i)
  have hκ : ∀ v : Vec, π (ppow k v) = ppow κ v := fun v => map_ppow π k v
  have hs : ∀ j i, ∃ b, σb j (κ i) = tp τ b * ppow κ (ρ j i) := by
    intro j i
    have hphi : D.phi (σ j (k i)) = vecE e (ρ j i) := by
      have : cm (σ j (k i)) t = σ j (cm (k i) t) := by simp [cm, hσt]
      rw [D.phi_apply, this, hk, hσe]
    obtain ⟨x, hx, hxe⟩ := D.exists_NF hk hphi
    obtain ⟨b, hb⟩ := hX x hx
    refine ⟨b, ?_⟩
    show π (σ j (k i)) = _
    rw [hxe, map_mul, hb, hκ]
  choose ε hε using hs
  have hδγ := hQ (fun i => sb (κ i)) (fun i l => cb (κ i) (κ l)) (fun i => cb_self hB _)
    (fun i l => cb_symm hB _ _) (fun j i => by
      have h1 := sb_map hB (σb j) (hσbτ j) (κ i)
      rw [hε j i, sb_tp_mul hB, sb_ppow hB] at h1
      exact h1.symm) (fun j i l => by
      have h1 := cb_map hB (σb j) (hσbτ j) (κ i) (κ l)
      rw [hε j i, hε j l, cb_tp_mul hB, cb_mul_tp hB, cb_ppow hB] at h1
      rw [← h1]
      simp [Finset.mul_sum, mul_assoc])
  obtain ⟨hδ0, hγ0⟩ := hδγ
  have hδ0' : ∀ m, sb (κ m) = 0 := fun m => congrFun hδ0 m
  have hγ0' : ∀ m n, cb (κ m) (κ n) = 0 := fun m n => congrFun (congrFun hγ0 m) n
  have hgen : ∀ x : Γ ⧸ E, ∃ (b : ZMod 2) (v : Vec), x = tp τ b * ppow κ v := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, hv⟩ := D.exists_vecE (D.phi_mem a)
    obtain ⟨x₀, hx₀, hxe⟩ := D.exists_NF hk hv
    obtain ⟨b, hb⟩ := hX x₀ hx₀
    exact ⟨b, v, by
      show π a = _
      rw [hxe, map_mul, hb, hκ]⟩
  have hsb0 : ∀ x, sb x = 0 := by
    intro x
    obtain ⟨b, v, rfl⟩ := hgen x
    rw [sb_tp_mul hB, sb_ppow hB]
    simp [hδ0', hγ0']
  have hcb0 : ∀ x y, cb x y = 0 := by
    intro x y
    obtain ⟨b, v, rfl⟩ := hgen x
    obtain ⟨b', w, rfl⟩ := hgen y
    rw [cb_tp_mul hB, cb_mul_tp hB, cb_ppow hB]
    simp [hγ0']
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · rw [← hπ]
    have h1 := hB.hcb (π a) (π b)
    rw [hcb0, tp_zero] at h1
    simpa [cm] using h1
  · rw [← hπ]
    have h1 := hB.hsb (π a)
    rw [hsb0, tp_zero] at h1
    simpa using h1

theorem cm_pt {M : Type*} [Group M] (hc : ∀ x y z : M, cm x y * z = z * cm x y) (t P P' : M)
    (a b : ZMod 2) :
    cm (P * t ^ a.val) (P' * t ^ b.val) = cm P P' * cm P t ^ b.val * cm t P' ^ a.val := by
  have h1 : cm (P * t ^ a.val) (P' * t ^ b.val) =
      cm P (P' * t ^ b.val) * cm (t ^ a.val) (P' * t ^ b.val) :=
    cm_mul_left_aux _ _ _ (hc _ _)
  have h2 : cm P (P' * t ^ b.val) = cm P P' * cm P t ^ b.val := by
    rw [cm_mul_right_aux P P' _ (hc _ _)]
    congr 1
    exact map_pow (cmR hc P) t b.val
  have h3 : cm (t ^ a.val) (P' * t ^ b.val) = cm t P' ^ a.val := by
    have : cm (t ^ a.val) (P' * t ^ b.val) = cmL hc (P' * t ^ b.val) (t ^ a.val) := rfl
    rw [this, map_pow]
    show cm t (P' * t ^ b.val) ^ a.val = _
    rw [cm_mul_right_aux t P' _ (hc _ _)]
    have : cm t (t ^ b.val) = 1 := cm_eq_one_iff.2 ((Commute.refl t).pow_right _).eq
    rw [this, mul_one]
  rw [h1, h2, h3]

theorem Data.cm_pt_vec (D : Data E t e) (hc : ∀ x y z : Γ, cm x y * z = z * cm x y)
    {P P' : Γ} {p p' c : Vec} (hP : cm P t = vecE e p) (hP' : cm P' t = vecE e p')
    (hPP : cm P P' = vecE e c) (a b : ZMod 2) :
    cm (P * t ^ a.val) (P' * t ^ b.val) = vecE e (c + b • p + a • p') := by
  have he := D.basis
  rw [cm_pt hc, cm_swap t P', hP', hPP, hP, vecE_inv he, vecE_add he, vecE_add he, vecE_smul he,
    vecE_smul he]

theorem Data.cm_ppow_vecE (D : Data E t e) (hc : ∀ x y z : Γ, cm x y * z = z * cm x y)
    {k : Fin 4 → Γ} {β : Fin 4 → Fin 4 → Vec} (hβ : ∀ m n, cm (k m) (k n) = vecE e (β m n))
    (a b : Vec) :
    cm (ppow k a) (ppow k b) = vecE e (∑ m, ∑ n, (a m * b n) • β m n) := by
  have he := D.basis
  rw [cm_ppow hc]
  simp only [hβ]
  have h1 : ∀ m, ppow (fun n => vecE e (β m n)) b = vecE e (b ᵥ* Matrix.of (β m)) := fun m =>
    (vecE_vecMul he (Matrix.of (β m)) b).symm
  simp only [h1]
  have h2 := vecE_vecMul he (Matrix.of fun m => b ᵥ* Matrix.of (β m)) a
  rw [show (ppow (fun m => vecE e (b ᵥ* Matrix.of (β m))) a) = _ from h2.symm]
  congr 1
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_assoc]

theorem Data.exists_NF' (D : Data E t e) {k : Fin 4 → Γ} (hk : ∀ i, cm (k i) t = e i) {a : Γ}
    {v : Vec} (hv : D.phi a = vecE e v) : ∃ x ∈ zpowers t ⊔ E, a = ppow k v * x := by
  refine ⟨(ppow k v)⁻¹ * a, D.mem_X_of_phi ?_, by simp⟩
  rw [map_mul, map_inv, hv, D.phi_ppow hk, inv_mul_cancel]

theorem Data.tauData [E.Normal] (D : Data E t e) : TauData (QuotientGroup.mk t : Γ ⧸ E) := by
  let π : Γ →* Γ ⧸ E := QuotientGroup.mk' E
  have hπ : ∀ a, π a = 1 ↔ a ∈ E := fun a => QuotientGroup.eq_one_iff a
  refine ⟨fun z => ?_, ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have : t * g = cm t g * (g * t) := by simp only [cm]; group
    have hm : cm t g ∈ E := by
      rw [cm_swap]; exact E.inv_mem (D.hφ g)
    change π t * π g = π g * π t
    rw [← map_mul, ← map_mul, this, map_mul, (hπ _).2 hm, one_mul]
  · change π t * π t = 1
    rw [← map_mul, D.ht2, map_one]
  · change π t ≠ 1
    rw [Ne, hπ]; exact D.htE

theorem cm_mul_central_left {M : Type*} [Group M] (hc : ∀ x y z : M, cm x y * z = z * cm x y)
    {u : M} (hu : ∀ z, u * z = z * u) (y z : M) : cm (y * u) z = cm y z := by
  rw [cm_mul_left_aux y u z (hc u z), cm_eq_one_iff.2 (hu z), mul_one]

theorem cm_mul_central_right {M : Type*} [Group M] (hc : ∀ x y z : M, cm x y * z = z * cm x y)
    {u : M} (hu : ∀ z, u * z = z * u) (y z : M) : cm y (z * u) = cm y z := by
  rw [cm_mul_right_aux y z u (hc y u), cm_eq_one_iff.2 (hu y).symm, mul_one]

theorem ppowN_mul_cg {M : Type*} [CommGroup M] (c d : Fin 4 → M) (n : Fin 4 → ℕ) :
    ppowN (fun i => c i * d i) n = ppowN c n * ppowN d n := by
  simp only [ppowN, List.prod_ofFn, mul_pow, Finset.prod_mul_distrib]

theorem Data.stage2 (D : Data E t e) {k : Fin 4 → Γ} (hk : ∀ i, cm (k i) t = e i)
    (S1a : ∀ a b, cm a b ∈ E) (ρ : Fin 2 → Mat) (hS : SplitRigid ρ) (σ : Fin 2 → Γ →* Γ)
    (hσt : ∀ j, σ j t = t) (hσe : ∀ j i, σ j (e i) = vecE e (ρ j i)) :
    ∃ k' : Fin 4 → Γ, (∀ i, cm (k' i) t = e i) ∧ (∀ i l, cm (k' i) (k' l) = 1) ∧
      (∀ j i, ∃ u ∈ E, σ j (k' i) = ppow k' (ρ j i) * u) := by
  have := D.normal
  have he := D.basis
  have inj := vecE_injective D.hE D.hEab D.hE16
  have hc : ∀ x y z : Γ, cm x y * z = z * cm x y := fun x y z => D.hEc _ (S1a x y) z
  have hβ0 : ∀ i l, ∃ w, cm (k i) (k l) = vecE e w := fun i l => by
    obtain ⟨w, hw⟩ := D.exists_vecE (S1a (k i) (k l)); exact ⟨w, hw⟩
  choose β hβ using hβ0
  have hβ_diag : ∀ i, β i i = 0 := fun i => inj (by rw [← hβ, cm_self, vecE_zero])
  have hβ_symm : ∀ i l, β i l = β l i := fun i l => inj (by
    rw [← hβ, cm_swap, hβ, vecE_inv he])
  have hPt : ∀ v : Vec, cm (ppow k v) t = vecE e v := fun v => D.phi_ppow hk v
  have hNF : ∀ j i, ∃ (b : ZMod 2) (u : Γ), u ∈ E ∧
      σ j (k i) = ppow k (ρ j i) * t ^ b.val * u := by
    intro j i
    have hphi : D.phi (σ j (k i)) = vecE e (ρ j i) := by
      have : cm (σ j (k i)) t = σ j (cm (k i) t) := by simp [cm, hσt]
      rw [D.phi_apply, this, hk, hσe]
    obtain ⟨x, hx, hxe⟩ := D.exists_NF' hk hphi
    rcases D.mem_X.1 hx with hx | ⟨u, hu, rfl⟩
    · exact ⟨0, x, hx, by rw [hxe]; simp⟩
    · exact ⟨1, u, hu, by rw [hxe]; simp [ZMod.val_one, mul_assoc]⟩
  choose ε u hu hσk using hNF
  have key : ∀ j i l, β i l ᵥ* ρ j =
      ∑ m, ∑ n, (ρ j i m * ρ j l n) • β m n + ε j l • (Pi.single i 1 ᵥ* ρ j) +
        ε j i • (Pi.single l 1 ᵥ* ρ j) := by
    intro j i l
    have h1 : σ j (cm (k i) (k l)) = cm (σ j (k i)) (σ j (k l)) := by simp [cm]
    rw [hβ, hom_vecE he (σ j) (ρ j) (hσe j), hσk j i, hσk j l,
      cm_mul_central_left hc (D.hEc _ (hu j i)), cm_mul_central_right hc (D.hEc _ (hu j l)),
      D.cm_pt_vec hc (hPt (ρ j i)) (hPt (ρ j l)) (D.cm_ppow_vecE hc hβ (ρ j i) (ρ j l))] at h1
    have h2 := inj h1
    have r1 : ∀ i, (Pi.single i 1 : Vec) ᵥ* ρ j = ρ j i := fun i => by
      ext c; simp [vecMul, dotProduct, Pi.single_apply]
    rw [r1, r1, h2]
  obtain ⟨f, hfε, hfβ⟩ := hS (fun j i => ε j i) β hβ_diag hβ_symm key
  have h2 : ∀ x : ZMod 2, x + x = 0 := CharTwo.add_self_eq_zero
  have hphik : ∀ i, cm (k i * t ^ (f i).val) t = e i := fun i => by
    rw [cm_mul_left_aux _ _ _ (by
      rw [cm_eq_one_iff.2 ((Commute.refl t).pow_left _).eq]; intro z; simp), hk,
      cm_eq_one_iff.2 ((Commute.refl t).pow_left _).eq, mul_one]
  refine ⟨fun i => k i * t ^ (f i).val, hphik, fun i l => ?_, ?_⟩
  · have := D.cm_pt_vec hc (P := k i) (P' := k l) (p := Pi.single i 1) (p' := Pi.single l 1)
      (c := β i l) (by rw [hk, vecE_single]) (by rw [hk, vecE_single]) (hβ i l) (f i) (f l)
    rw [this, ← vecE_zero (e := e)]
    congr 1
    ext c
    have := hfβ i l
    simp only [this, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination h2 (f i * (Pi.single l 1 : Vec) c) + h2 (f l * (Pi.single i 1 : Vec) c)
  · intro j i
    have hQc : ∀ x y : Γ ⧸ E, x * y = y * x := by
      intro x y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have h : ((cm a b : Γ) : Γ ⧸ E) = 1 := (QuotientGroup.eq_one_iff _).2 (S1a a b)
      have h' : cm (a : Γ ⧸ E) (b : Γ ⧸ E) = 1 := by simpa [cm] using h
      exact cm_eq_one_iff.1 h'
    let : CommGroup (Γ ⧸ E) := { (inferInstance : Group (Γ ⧸ E)) with mul_comm := hQc }
    let π : Γ →* Γ ⧸ E := QuotientGroup.mk' E
    have hπ1 : ∀ a ∈ E, π a = 1 := fun a ha => (QuotientGroup.eq_one_iff a).2 ha
    have hτ : TauData (π t) := D.tauData
    have hL : π (σ j (k i * t ^ (f i).val)) =
        π (ppow k (ρ j i)) * tp (π t) (ε j i) * tp (π t) (f i) := by
      rw [map_mul, map_pow, hσt, hσk j i, map_mul, map_mul, map_pow, hπ1 _ (hu j i), mul_one]
      rfl
    have hR : π (ppow (fun i => k i * t ^ (f i).val) (ρ j i)) =
        π (ppow k (ρ j i)) * tp (π t) (∑ n, ρ j i n * f n) := by
      rw [map_ppow, ← ppow_tp hτ]
      have : (fun m => π (k m * t ^ (f m).val)) = fun m => π (k m) * tp (π t) (f m) := by
        funext m; rw [map_mul, map_pow]; rfl
      rw [this, map_ppow]
      exact ppowN_mul_cg _ _ _
    have heq : π (ppow (fun i => k i * t ^ (f i).val) (ρ j i)) =
        π (σ j (k i * t ^ (f i).val)) := by
      rw [hL, hR, mul_assoc, ← tp_add hτ]
      congr 2
      rw [hfε j i]
      linear_combination -h2 (f i)
    refine ⟨(ppow (fun i => k i * t ^ (f i).val) (ρ j i))⁻¹ * σ j (k i * t ^ (f i).val),
      QuotientGroup.eq.1 heq, by simp⟩

theorem ppow_mem {m : ℕ} [NeZero m] (H : Subgroup Γ) {c : Fin 4 → Γ} (hc : ∀ i, c i ∈ H)
    (n : Fin 4 → ZMod m) : ppow c n ∈ H := by
  unfold ppow ppowN
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact H.pow_mem (hc i) _

@[expose] def Wsub (E : Subgroup Γ) (k' : Fin 4 → Γ) : Subgroup Γ :=
  Subgroup.closure ((E : Set Γ) ∪ Set.range k')

theorem Wsub.E_le (k' : Fin 4 → Γ) : E ≤ Wsub E k' := fun _ hx =>
  Subgroup.subset_closure (Or.inl hx)

theorem Wsub.k_mem (k' : Fin 4 → Γ) (i : Fin 4) : k' i ∈ Wsub E k' :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem Wsub.comm (D : Data E t e) {k' : Fin 4 → Γ} (hcomm : ∀ i l, cm (k' i) (k' l) = 1) :
    ∀ x ∈ Wsub E k', ∀ y ∈ Wsub E k', x * y = y * x := by
  have hp : ((E : Set Γ) ∪ Set.range k').Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ⟨i, rfl⟩
    · exact D.hEc a ha b
    · rcases hb with hb | ⟨l, rfl⟩
      · exact (D.hEc b hb _).symm
      · exact cm_eq_one_iff.1 (hcomm i l)
  have : IsMulCommutative (Wsub E k') := Subgroup.isMulCommutative_closure hp
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Wsub E k') ⟨y, hy⟩)

theorem Wsub.normalized (S1a : ∀ a b : Γ, cm a b ∈ E) (k' : Fin 4 → Γ) (g : Γ) {w : Γ}
    (hw : w ∈ Wsub E k') : g * w * g⁻¹ ∈ Wsub E k' := by
  have : g * w * g⁻¹ = cm g w * w := by simp only [cm]; group
  rw [this]
  exact mul_mem (Wsub.E_le k' (S1a g w)) hw

theorem Wsub.stable [Finite Γ] (D : Data E t e) {k' : Fin 4 → Γ} (ρ : Fin 2 → Mat)
    (σ : Fin 2 → Γ →* Γ) (hσe : ∀ j i, σ j (e i) = vecE e (ρ j i))
    (hσk' : ∀ j i, ∃ u ∈ E, σ j (k' i) = ppow k' (ρ j i) * u) (j : Fin 2) :
    ∀ w ∈ Wsub E k', σ j w ∈ Wsub E k' := by
  have he := D.basis
  have h : Wsub E k' ≤ (Wsub E k').comap (σ j) := by
    rw [Wsub, Subgroup.closure_le]
    rintro _ (hu | ⟨i, rfl⟩)
    · obtain ⟨v, rfl⟩ := D.exists_vecE hu
      rw [SetLike.mem_coe, Subgroup.mem_comap, hom_vecE he (σ j) (ρ j) (hσe j)]
      exact Wsub.E_le k' (vecE_mem D.hE _)
    · obtain ⟨u, hu, h⟩ := hσk' j i
      rw [SetLike.mem_coe, Subgroup.mem_comap, h]
      exact mul_mem (ppow_mem _ (fun i => Wsub.k_mem k' i) _) (Wsub.E_le k' hu)
  exact fun w hw => h hw

theorem Data.e_ne_one (D : Data E t e) (i : Fin 4) : e i ≠ 1 := by
  have inj := vecE_injective D.hE D.hEab D.hE16
  intro h
  have h1 : vecE e (Pi.single i 1) = vecE e 0 := by rw [vecE_single, vecE_zero, h]
  have := congrFun (inj h1) i
  simp at this

theorem Wsub.t_not_mem (D : Data E t e) {k' : Fin 4 → Γ} (hk' : ∀ i, cm (k' i) t = e i)
    (hcomm : ∀ i l, cm (k' i) (k' l) = 1) : t ∉ Wsub E k' := by
  intro ht
  have := Wsub.comm D hcomm (k' 0) (Wsub.k_mem k' 0) t ht
  exact D.e_ne_one 0 (by rw [← hk' 0]; exact cm_eq_one_iff.2 this)

theorem Wsub.card (D : Data E t e) {k' : Fin 4 → Γ} (hk' : ∀ i, cm (k' i) t = e i)
    (hcomm : ∀ i l, cm (k' i) (k' l) = 1) : Nat.card (Wsub E k') = 256 := by
  let f : Wsub E k' →* Γ := D.phi.comp (Wsub E k').subtype
  have hker : f.ker = E.subgroupOf (Wsub E k') := by
    ext ⟨w, hw⟩
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      rcases D.mem_X.1 (D.mem_X_of_phi h) with hE | ⟨u, hu, rfl⟩
      · exact hE
      · exfalso
        apply Wsub.t_not_mem D hk' hcomm
        have : t = (t * u) * u⁻¹ := by simp
        rw [this]
        exact mul_mem hw (inv_mem (Wsub.E_le k' hu))
    · intro h
      exact D.phi_of_mem_E h
  have hrange : f.range = E := by
    apply le_antisymm
    · rintro _ ⟨⟨w, hw⟩, rfl⟩
      exact D.phi_mem w
    · refine D.hE.le.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨k' i, Wsub.k_mem k' i⟩, hk' i⟩
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at h
  have c1 : Nat.card (E.subgroupOf (Wsub E k')) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Wsub.E_le k')).toEquiv]
    exact D.hE16
  rw [c1, D.hE16] at h
  omega

theorem ppowN_sq {M : Type*} [Group M] (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j))
    (n : Fin 4 → ℕ) : ppowN c n * ppowN c n = ppowN (fun i => c i * c i) n := by
  rw [← ppowN_add c hc]
  have h : ∀ (x : M) (m : ℕ), x ^ (m + m) = (x * x) ^ m := by
    intro x m; rw [← two_mul, pow_mul, pow_two]
  simp only [ppowN_def, Pi.add_apply, h]

theorem ppow_sq {M : Type*} [Group M] {m : ℕ} (c : Fin 4 → M) (hc : ∀ i j, Commute (c i) (c j))
    (a : Fin 4 → ZMod m) : ppow c a * ppow c a = ppow (fun i => c i * c i) a :=
  ppowN_sq c hc _

theorem rowMul (A B : Mat) (i : Fin 4) : (A * B) i = A i ᵥ* B := by
  ext c; simp [Matrix.mul_apply, vecMul, dotProduct]

theorem Data.stage3 (D : Data E t e) {k' : Fin 4 → Γ} (hcomm : ∀ i l, cm (k' i) (k' l) = 1)
    (S1b : ∀ a, a * a ∈ E) (ρ : Fin 2 → Mat) (hC : CommRigid ρ) (σ : Fin 2 → Γ →* Γ)
    (hσe : ∀ j i, σ j (e i) = vecE e (ρ j i))
    (hσk' : ∀ j i, ∃ u ∈ E, σ j (k' i) = ppow k' (ρ j i) * u) :
    ∃ s : Fin 4 → Vec, (∀ i, k' i * k' i = vecE e (s i)) ∧
      (Matrix.of s = 0 ∨ Matrix.of s = 1) := by
  have he := D.basis
  have inj := vecE_injective D.hE D.hEab D.hE16
  have hs0 : ∀ i, ∃ w, k' i * k' i = vecE e w := fun i => by
    obtain ⟨w, hw⟩ := D.exists_vecE (S1b (k' i)); exact ⟨w, hw⟩
  choose s hs using hs0
  refine ⟨s, hs, hC (Matrix.of s) fun j => ?_⟩
  ext i c
  have h1 : σ j (k' i * k' i) = σ j (k' i) * σ j (k' i) := map_mul _ _ _
  obtain ⟨u, hu, hσ⟩ := hσk' j i
  have hcomm' : ∀ i l, Commute (k' i) (k' l) := fun i l => cm_eq_one_iff.1 (hcomm i l)
  have h2 : σ j (k' i) * σ j (k' i) = ppow k' (ρ j i) * ppow k' (ρ j i) := by
    rw [hσ]
    have hu2 := D.sq_E hu
    calc ppow k' (ρ j i) * u * (ppow k' (ρ j i) * u)
        = ppow k' (ρ j i) * (u * ppow k' (ρ j i)) * u := by group
      _ = ppow k' (ρ j i) * (ppow k' (ρ j i) * u) * u := by rw [D.hEc u hu]
      _ = ppow k' (ρ j i) * ppow k' (ρ j i) * (u * u) := by group
      _ = _ := by rw [hu2, mul_one]
  rw [ppow_sq k' hcomm'] at h2
  have h3 : ppow (fun m => k' m * k' m) (ρ j i) = vecE e (ρ j i ᵥ* Matrix.of s) := by
    rw [vecE_vecMul he]
    simp only [hs]
    rfl
  rw [hs, hom_vecE he (σ j) (ρ j) (hσe j), h2, h3] at h1
  have h4 := inj h1.symm
  have h5 := congrFun h4 c
  have e1 : (ρ j * Matrix.of s) i = ρ j i ᵥ* Matrix.of s := rowMul _ _ _
  have e2 : (Matrix.of s * ρ j) i = s i ᵥ* ρ j := rowMul _ _ _
  rw [e1, e2]
  exact h5

theorem mat_eq_one_of_vecMul {A : Matrix (Fin 4) (Fin 4) (ZMod 4)} (h : ∀ n, n ᵥ* A = n) :
    A = 1 := by
  ext i c
  have := congrFun (h (Pi.single i 1)) c
  simpa [vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using this

theorem zmod4_red_aux : ∀ a : ZMod 4, ∀ b : ZMod 2, a + a = ((2 * b.val : ℕ) : ZMod 4) →
    ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) a = b := by decide

theorem Data.stage4 (D : Data E t e) {k' : Fin 4 → Γ} (hk' : ∀ i, cm (k' i) t = e i)
    (hcomm : ∀ i l, cm (k' i) (k' l) = 1) (s : Fin 4 → Vec)
    (hs : ∀ i, k' i * k' i = vecE e (s i)) (hs1 : Matrix.of s = 1) (x y : Mat) (hZ : Z4Rigid x y)
    (τ : Fin 2 → Γ →* Γ) (hτ0 : ∀ i, τ 0 (e i) = vecE e (x i))
    (hτ1 : ∀ i, τ 1 (e i) = vecE e (y i)) (hτ2 : ∀ j k, τ j (τ j k) = k)
    (hτ01 : ∀ k, τ 0 (τ 1 (τ 0 (τ 1 k))) = k)
    (hWt : ∀ j, ∀ w ∈ Wsub E k', τ j w ∈ Wsub E k') : False := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  have he := D.basis
  have hcomm' : ∀ i l, Commute (k' i) (k' l) := fun i l => cm_eq_one_iff.1 (hcomm i l)
  have hsq : ∀ i, k' i * k' i = e i := fun i => by
    have : s i = Pi.single i 1 := by
      ext c
      have := congrFun (congrFun hs1 i) c
      simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
    rw [hs, this, vecE_single]
  have hk4 : ∀ i, k' i ^ 4 = 1 := fun i => by
    calc k' i ^ 4 = (k' i * k' i) * (k' i * k' i) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hsq, ← pow_two, he.sq]
  let ω : (Fin 4 → ZMod 4) → Γ := fun n => ppow k' n
  have hωadd : ∀ n n', ω (n + n') = ω n * ω n' := fun n n' => ppow_add k' hcomm' hk4 n n'
  have hω0 : ω 0 = 1 := ppow_zero k'
  have hωmem : ∀ n, ω n ∈ Wsub E k' := fun n => ppow_mem _ (fun i => Wsub.k_mem k' i) n
  have hvecE : ∀ v : Vec, vecE e v = ω (fun i => ((2 * (v i).val : ℕ) : ZMod 4)) := by
    intro v
    have h : ∀ i, e i ^ (v i).val = k' i ^ (((2 * (v i).val : ℕ) : ZMod 4)).val := fun i => by
      have h1 : (v i).val < 2 := ZMod.val_lt (v i)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), pow_mul, ← hsq i, pow_two]
    simp only [vecE_eq_ppow, ω, ppow_def, h]
  have hωsurj : ∀ w ∈ Wsub E k', ∃ n, w = ω n := by
    let R : Subgroup Γ :=
      { carrier := Set.range ω
        mul_mem' := by
          rintro _ _ ⟨n, rfl⟩ ⟨n', rfl⟩
          exact ⟨n + n', hωadd n n'⟩
        one_mem' := ⟨0, hω0⟩
        inv_mem' := by
          rintro _ ⟨n, rfl⟩
          refine ⟨-n, ?_⟩
          have : ω (-n) * ω n = 1 := by rw [← hωadd, neg_add_cancel, hω0]
          exact eq_inv_of_mul_eq_one_left this }
    have hle : Wsub E k' ≤ R := by
      rw [Wsub, Subgroup.closure_le]
      rintro _ (hu | ⟨i, rfl⟩)
      · obtain ⟨v, rfl⟩ := D.exists_vecE hu
        exact ⟨_, (hvecE v).symm⟩
      · exact ⟨Pi.single i 1, ppow_single k' i⟩
    intro w hw
    obtain ⟨n, hn⟩ := hle hw
    exact ⟨n, hn.symm⟩
  have hωinj : Function.Injective ω := by
    let ω' : (Fin 4 → ZMod 4) → Wsub E k' := fun n => ⟨ω n, hωmem n⟩
    have hb : Function.Bijective ω' := by
      refine (Nat.bijective_iff_surjective_and_card ω').2 ⟨?_, ?_⟩
      · rintro ⟨w, hw⟩
        obtain ⟨n, hn⟩ := hωsurj w hw
        exact ⟨n, Subtype.ext hn.symm⟩
      · rw [Wsub.card D hk' hcomm]; simp [Nat.card_eq_fintype_card]
    intro a b h
    exact hb.1 (Subtype.ext h)
  have hXr : ∀ j i, ∃ r : Fin 4 → ZMod 4, τ j (k' i) = ω r := fun j i =>
    hωsurj _ (hWt j _ (Wsub.k_mem k' i))
  choose Xr hXr using hXr
  let Xm : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 4) := fun j => Matrix.of (Xr j)
  have hτω : ∀ j n, τ j (ω n) = ω (n ᵥ* Xm j) := by
    intro j n
    have h1 : τ j (ω n) = ppow (fun i => ω (Xr j i)) n := by
      show τ j (ppow k' n) = _
      rw [map_ppow]; simp only [hXr]
    rw [h1]
    exact ppow_vecMul k' hcomm' hk4 (Xm j) n
  have hXX : ∀ j, Xm j * Xm j = 1 := by
    intro j
    apply mat_eq_one_of_vecMul
    intro n
    apply hωinj
    have := hτ2 j (ω n)
    rwa [hτω, hτω, vecMul_vecMul] at this
  have hYXYX : Xm 1 * Xm 0 * (Xm 1 * Xm 0) = 1 := by
    apply mat_eq_one_of_vecMul
    intro n
    apply hωinj
    have := hτ01 (ω n)
    rw [hτω, hτω, hτω, hτω] at this
    simpa [vecMul_vecMul, mul_assoc] using this
  have hred : ∀ (j : Fin 2) (z : Mat), (∀ i, τ j (e i) = vecE e (z i)) → red (Xm j) = z := by
    intro j z hz
    ext i m
    have h1 : τ j (e i) = ω (Xr j i + Xr j i) := by
      rw [← hsq i, map_mul, hXr, hωadd]
    rw [hz, hvecE] at h1
    have h2 := congrFun (hωinj h1.symm) m
    exact zmod4_red_aux _ _ h2
  have hR0 := hred 0 x hτ0
  have hR1 := hred 1 y hτ1
  apply hZ (Xm 0) (Xm 1) hR0 hR1 (hXX 0) (hXX 1)
  calc Xm 0 * Xm 1 * (Xm 0 * Xm 1)
      = Xm 0 * (Xm 1 * Xm 0 * (Xm 1 * Xm 0)) * Xm 0 := by
        have h0 := hXX 0
        simp only [mul_assoc] at h0 ⊢
        rw [h0, mul_one]
    _ = 1 := by rw [hYXYX, mul_one, hXX 0]

theorem Data.core [Finite Γ] (D : Data E t e) (ρ : Fin 2 → Mat) (x y : Mat)
    (hQ : QuadRigid ρ) (hS : SplitRigid ρ) (hC : CommRigid ρ) (hZ : Z4Rigid x y)
    (σ τ : Fin 2 → Γ →* Γ) (hσt : ∀ j, σ j t = t)
    (hσe : ∀ j i, σ j (e i) = vecE e (ρ j i))
    (hτ0 : ∀ i, τ 0 (e i) = vecE e (x i)) (hτ1 : ∀ i, τ 1 (e i) = vecE e (y i))
    (hτ2 : ∀ j k, τ j (τ j k) = k) (hτ01 : ∀ k, τ 0 (τ 1 (τ 0 (τ 1 k))) = k)
    (hτW : ∀ W : Subgroup Γ, (∀ j, ∀ w ∈ W, σ j w ∈ W) → ∀ j, ∀ w ∈ W, τ j w ∈ W) :
    ∃ W : Subgroup Γ, E ≤ W ∧ t ∉ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 256 ∧
      (∀ j, ∀ w ∈ W, σ j w ∈ W) ∧ (∀ k, ∀ w ∈ W, k * w * k⁻¹ ∈ W) := by
  have hk' : ∀ i, ∃ k : Γ, cm k t = e i := fun i => D.hφs _ (by
    rw [D.hE]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  choose k hk using hk'
  obtain ⟨S1a, S1b⟩ := D.stage1 hk ρ hQ σ hσt hσe
  obtain ⟨k', hk'e, hcomm, hσk'⟩ := D.stage2 hk S1a ρ hS σ hσt hσe
  have hstab := Wsub.stable D ρ σ hσe hσk'
  obtain ⟨s, hs, hS01⟩ := D.stage3 hcomm S1b ρ hC σ hσe hσk'
  rcases hS01 with h0 | h1
  · refine ⟨Wsub E k', Wsub.E_le k', Wsub.t_not_mem D hk'e hcomm, ⟨?_, ?_⟩,
      Wsub.card D hk'e hcomm, hstab, fun g w hw => Wsub.normalized S1a k' g hw⟩
    · have hp := Wsub.comm D hcomm
      exact ⟨⟨fun a b => Subtype.ext (hp a a.2 b b.2)⟩⟩
    · have hs0 : ∀ i, k' i * k' i = 1 := fun i => by
        have : s i = 0 := funext fun c => congrFun (congrFun h0 i) c
        rw [hs, this, vecE_zero]
      intro w hw
      have hp := Wsub.comm D hcomm
      have hw' : w ∈ Subgroup.closure ((E : Set Γ) ∪ Set.range k') := hw
      have hww : w * w = 1 := by
        refine Subgroup.closure_induction (p := fun w _ => w * w = 1) ?_ ?_ ?_ ?_ hw'
        · rintro a (ha | ⟨i, rfl⟩)
          · exact D.sq_E ha
          · exact hs0 i
        · simp
        · intro a b ha hb iha ihb
          have hab : b * a = a * b := hp b hb a ha
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab]
            _ = a * a * (b * b) := by group
            _ = 1 := by rw [iha, ihb, one_mul]
        · intro a ha iha
          have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          rw [this, iha, inv_one]
      rw [pow_two]; exact hww
  · exact (D.stage4 hk'e hcomm s hs h1 x y hZ τ hτ0 hτ1 hτ2 hτ01 (hτW _ hstab)).elim

end Gamma

section Bridge

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_comm {E : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hEt : ∀ a ∈ E, a * t = t * a) {x : G} (hx : x ∈ zpowers t ⊔ E) :
    x ∈ E ∨ ∃ u ∈ E, x = t * u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let T : Subgroup G :=
    { carrier := {x | x ∈ E ∨ ∃ u ∈ E, x = t * u}
      mul_mem' := by
        rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨u', hu', rfl⟩)
        · exact Or.inl (mul_mem ha hb)
        · refine Or.inr ⟨a * u', mul_mem ha hu', ?_⟩
          rw [← mul_assoc, hEt a ha, mul_assoc]
        · exact Or.inr ⟨u * b, mul_mem hu hb, by rw [mul_assoc]⟩
        · refine Or.inl ?_
          have : t * u * (t * u') = u * u' := by
            calc t * u * (t * u') = t * (u * t) * u' := by group
              _ = t * (t * u) * u' := by rw [hEt u hu]
              _ = (t * t) * (u * u') := by group
              _ = u * u' := by rw [ht2, one_mul]
          rw [this]; exact mul_mem hu hu'
      one_mem' := Or.inl E.one_mem
      inv_mem' := by
        rintro a (ha | ⟨u, hu, rfl⟩)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ⟨u⁻¹, inv_mem hu, ?_⟩
          rw [_root_.mul_inv_rev, hti, ← hEt u⁻¹ (inv_mem hu)] }
  have h : zpowers t ⊔ E ≤ T :=
    sup_le (zpowers_le.2 (Or.inr ⟨1, E.one_mem, by simp⟩)) (fun a ha => Or.inl ha)
  exact h hx

theorem mem_normalizer_of_forall_mem [Finite G] (H : Subgroup G) {g : G}
    (hg : ∀ k ∈ H, g * k * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  let f : H → H := fun k => ⟨g * k * g⁻¹, hg k k.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.surjective_of_injective hinj
  intro n
  constructor
  · intro hn; exact hg n hn
  · intro hn
    obtain ⟨k, hk⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
    have := congrArg Subtype.val hk
    simp only [f, mul_left_inj, mul_right_inj] at this
    rw [← this]; exact k.2

@[expose] def conjHom (K : Subgroup G) (g : G) (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : K →* K :=
  MonoidHom.mk' (fun k => ⟨g * k * g⁻¹, hg k k.2⟩) fun a b => Subtype.ext (by
    show g * (a.1 * b.1) * g⁻¹ = g * a.1 * g⁻¹ * (g * b.1 * g⁻¹)
    group)

end Bridge

theorem exists_elemAbelian_complement {G : Type*} [Group G] [Finite G] {E K : Subgroup G} {t : G}
    (e : Fin 4 → G) (h : Fin 2 → G) (r : Fin 2 → G) (ρ : Fin 2 → Mat) (x y : Mat)
    (hQ : QuadRigid ρ) (hS : SplitRigid ρ) (hC : CommRigid ρ) (hZ : Z4Rigid x y)
    (hE : E = Subgroup.closure (Set.range e)) (hEab : IsElemAbelian 2 E) (hE16 : Nat.card E = 16)
    (ht2 : t * t = 1) (htE : t ∉ E) (hEt : ∀ a ∈ E, a * t = t * a)
    (hEK : E ≤ K) (htK : t ∈ K) (hEZ : ∀ a ∈ E, ∀ b ∈ K, a * b = b * a)
    (hKt : ∀ k ∈ K, k * t = t * k → k ∈ Subgroup.zpowers t ⊔ E)
    (hφ : ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ E) (hφs : ∀ a ∈ E, ∃ k ∈ K, k * t * k⁻¹ * t⁻¹ = a)
    (hh : ∀ j, h j * t = t * h j) (hhK : ∀ j, ∀ k ∈ K, h j * k * (h j)⁻¹ ∈ K)
    (hhE : ∀ j i, h j * e i * (h j)⁻¹ = vecE e (ρ j i))
    (hr : ∀ j, r j ∈ Subgroup.closure (Set.range h) ⊔ E)
    (hrE : ∀ i, r 0 * e i * (r 0)⁻¹ = vecE e (x i) ∧ r 1 * e i * (r 1)⁻¹ = vecE e (y i))
    (hr2 : ∀ j, r j * r j ∈ E) (hr01 : r 0 * r 1 * (r 0 * r 1) ∈ E) :
    ∃ W : Subgroup G, E ≤ W ∧ W ≤ K ∧ t ∉ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 256 ∧
      (∀ j, ∀ w ∈ W, h j * w * (h j)⁻¹ ∈ W) ∧ (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) := by
  classical
  open Subgroup in
  have he_mem : ∀ i, e i ∈ E := fun i => by rw [hE]; exact subset_closure ⟨i, rfl⟩
  let e' : Fin 4 → K := fun i => ⟨e i, hEK (he_mem i)⟩
  let t' : K := ⟨t, htK⟩
  let E' : Subgroup K := E.subgroupOf K
  have coe_vecE : ∀ v, ((vecE e' v : K) : G) = vecE e v := fun v => map_vecE K.subtype e' v
  have hE' : E' = Subgroup.closure (Set.range e') := by
    apply le_antisymm
    · intro a ha
      have ha' : a.1 ∈ E := ha
      rw [hE] at ha'
      have : ∃ hK : a.1 ∈ K, (⟨a.1, hK⟩ : K) ∈ Subgroup.closure (Set.range e') := by
        refine Subgroup.closure_induction
          (p := fun g _ => ∃ hK : g ∈ K, (⟨g, hK⟩ : K) ∈ Subgroup.closure (Set.range e'))
          ?_ ?_ ?_ ?_ ha'
        · rintro _ ⟨i, rfl⟩
          exact ⟨(e' i).2, Subgroup.subset_closure ⟨i, rfl⟩⟩
        · exact ⟨K.one_mem, one_mem _⟩
        · rintro a b _ _ ⟨ha, ha2⟩ ⟨hb, hb2⟩
          exact ⟨K.mul_mem ha hb, mul_mem ha2 hb2⟩
        · rintro a _ ⟨ha, ha2⟩
          exact ⟨K.inv_mem ha, inv_mem ha2⟩
      obtain ⟨hK, h2⟩ := this
      exact h2
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact he_mem i
  have hEab' : IsElemAbelian 2 E' := by
    have : IsMulCommutative E := hEab.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · have := mul_comm' (⟨a.1.1, a.2⟩ : E) ⟨b.1.1, b.2⟩
      have h2 : a.1.1 * b.1.1 = b.1.1 * a.1.1 := congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext h2)
    · exact Subtype.ext (by simpa using hEab.2 a.1 ha)
  have hE16' : Nat.card E' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv).trans hE16
  have hD : Data E' t' e' :=
    { hE := hE'
      hEab := hEab'
      hE16 := hE16'
      hEc := fun a ha b => Subtype.ext (hEZ a.1 ha b.1 b.2)
      ht2 := Subtype.ext ht2
      htE := fun hh => htE hh
      hKt := by
        intro k hk
        have hk' : k.1 * t = t * k.1 := congrArg Subtype.val hk
        rcases mem_sup_zpowers_of_comm ht2 hEt (hKt k.1 k.2 hk') with hu | ⟨u, hu, hku⟩
        · exact Subgroup.mem_sup_right hu
        · have : k = t' * ⟨u, hEK hu⟩ := Subtype.ext hku
          rw [this]
          exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t'))
            (Subgroup.mem_sup_right hu)
      hφ := fun k => hφ k.1 k.2
      hφs := fun a ha => by
        obtain ⟨k, hkK, hk⟩ := hφs a.1 ha
        exact ⟨⟨k, hkK⟩, Subtype.ext hk⟩ }
  let σ : Fin 2 → (K →* K) := fun j => conjHom K (h j) (hhK j)
  have hrN : ∀ j, r j ∈ Subgroup.normalizer (K : Set G) := by
    have hh' : ∀ j, h j ∈ Subgroup.normalizer (K : Set G) := fun j =>
      mem_normalizer_of_forall_mem K (hhK j)
    have hsup : Subgroup.closure (Set.range h) ⊔ E ≤ Subgroup.normalizer (K : Set G) :=
      sup_le ((Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact hh' j))
        (hEK.trans Subgroup.le_normalizer)
    exact fun j => hsup (hr j)
  have hrK : ∀ j, ∀ k ∈ K, r j * k * (r j)⁻¹ ∈ K := fun j k hk =>
    (Subgroup.mem_normalizer_iff.1 (hrN j) k).1 hk
  let τ : Fin 2 → (K →* K) := fun j => conjHom K (r j) (hrK j)
  have hσt : ∀ j, σ j t' = t' := fun j => Subtype.ext (by
    show h j * t * (h j)⁻¹ = t
    rw [hh j]; group)
  have hσe : ∀ j i, σ j (e' i) = vecE e' (ρ j i) := fun j i => Subtype.ext (by
    rw [coe_vecE]; exact hhE j i)
  have hτ0 : ∀ i, τ 0 (e' i) = vecE e' (x i) := fun i => Subtype.ext (by
    rw [coe_vecE]; exact (hrE i).1)
  have hτ1 : ∀ i, τ 1 (e' i) = vecE e' (y i) := fun i => Subtype.ext (by
    rw [coe_vecE]; exact (hrE i).2)
  have hτ2 : ∀ j k, τ j (τ j k) = k := fun j k => Subtype.ext (by
    show r j * (r j * k.1 * (r j)⁻¹) * (r j)⁻¹ = k.1
    have hq := hEZ _ (hr2 j) k.1 k.2
    calc r j * (r j * k.1 * (r j)⁻¹) * (r j)⁻¹
        = (r j * r j) * k.1 * (r j * r j)⁻¹ := by group
      _ = k.1 := by rw [hq]; group)
  have hτ01 : ∀ k, τ 0 (τ 1 (τ 0 (τ 1 k))) = k := fun k => Subtype.ext (by
    show r 0 * (r 1 * (r 0 * (r 1 * k.1 * (r 1)⁻¹) * (r 0)⁻¹) * (r 1)⁻¹) * (r 0)⁻¹ = k.1
    have hq := hEZ _ hr01 k.1 k.2
    calc r 0 * (r 1 * (r 0 * (r 1 * k.1 * (r 1)⁻¹) * (r 0)⁻¹) * (r 1)⁻¹) * (r 0)⁻¹
        = (r 0 * r 1 * (r 0 * r 1)) * k.1 * (r 0 * r 1 * (r 0 * r 1))⁻¹ := by group
      _ = k.1 := by rw [hq]; group)
  have hτW : ∀ W : Subgroup K, (∀ j, ∀ w ∈ W, σ j w ∈ W) → ∀ j, ∀ w ∈ W, τ j w ∈ W := by
    intro W hW
    let WG : Subgroup G := W.map K.subtype
    have hN_h : ∀ j, h j ∈ Subgroup.normalizer (WG : Set G) := fun j =>
      mem_normalizer_of_forall_mem WG (by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨σ j w, hW j w hw, rfl⟩)
    have hN_E : E ≤ Subgroup.normalizer (WG : Set G) := fun a ha =>
      mem_normalizer_of_forall_mem WG (by
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨w, hw, ?_⟩
        show w.1 = a * w.1 * a⁻¹
        rw [hEZ a ha w.1 w.2]; group)
    have hsup : Subgroup.closure (Set.range h) ⊔ E ≤ Subgroup.normalizer (WG : Set G) :=
      sup_le ((Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact hN_h j)) hN_E
    intro j w hw
    have h1 := (Subgroup.mem_normalizer_iff.1 (hsup (hr j)) (w : G)).1 ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hw'eq⟩ := h1
    have : w' = τ j w := Subtype.ext hw'eq
    rw [← this]; exact hw'
  obtain ⟨W', hEW', htW', habW', hcardW', hσW', hKW'⟩ :=
    hD.core ρ x y hQ hS hC hZ σ τ hσt hσe hτ0 hτ1 hτ2 hτ01 hτW
  refine ⟨W'.map K.subtype, ?_, Subgroup.map_subtype_le W', ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨⟨a, hEK ha⟩, hEW' ha, rfl⟩
  · rintro ⟨w', hw', hwt⟩
    have : w' = t' := Subtype.ext hwt
    exact htW' (this ▸ hw')
  · have := habW'.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := a.2
      obtain ⟨b', hb', hb'e⟩ := b.2
      have h2 := congrArg (fun z : W' => ((z : K) : G)) (mul_comm' (⟨a', ha'⟩ : W') ⟨b', hb'⟩)
      refine Subtype.ext ?_
      show a.1 * b.1 = b.1 * a.1
      rw [← ha'e, ← hb'e]
      exact h2
    · rintro _ ⟨w', hw', rfl⟩
      simpa using congrArg Subtype.val (habW'.2 w' hw')
  · rw [← Nat.card_congr (W'.equivMapOfInjective K.subtype K.subtype_injective).toEquiv]
    exact hcardW'
  · rintro j _ ⟨w', hw', rfl⟩
    exact ⟨σ j w', hσW' j w' hw', rfl⟩
  · rintro k hk _ ⟨w', hw', rfl⟩
    exact ⟨⟨k, hk⟩ * w' * ⟨k, hk⟩⁻¹, hKW' ⟨k, hk⟩ w' hw', rfl⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
