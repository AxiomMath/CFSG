module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.F3Data
public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponents
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open scoped Matrix

abbrev GL8 : Type := (Matrix (Fin 8) (Fin 8) (ZMod 3))ˣ

@[expose] noncomputable def powHom3 {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 3 = 1) : (Fin r → Multiplicative (ZMod 3)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

theorem powHom3_mulSingle {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 3 = 1) (i : Fin r) :
    powHom3 v hv (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))) = v i := by
  classical
  simp only [powHom3, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same, toAdd_ofAdd]
    exact pow_one (v i)
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, toAdd_one]
    exact pow_zero (v j)
  · intro h
    exact absurd (Finset.mem_univ i) h

open scoped IsMulCommutative in
theorem card_closure_range_of_commuting {G : Type*} [Group G] {r : ℕ} (u : Fin r → G)
    (hpow : ∀ i, u i ^ 3 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 3, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    Nat.card (Subgroup.closure (Set.range u)) = 3 ^ r ∧
      ∀ g ∈ Subgroup.closure (Set.range u),
        ∃ a : Fin r → Fin 3, (List.ofFn fun i => u i ^ (a i : ℕ)).prod = g := by
  classical
  set C := Subgroup.closure (Set.range u) with hC
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 3 = 1 := fun i => Subtype.ext (by simpa [v] using hpow i)
  let φ : (Fin r → Multiplicative (ZMod 3)) →* G := C.subtype.comp (powHom3 v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, powHom3, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
    funext i
    exact Multiplicative.toAdd.injective (congrFun h0 i)
  have hrange : φ.range = C := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact (powHom3 v hv a).2
    · rw [hC, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), ?_⟩
      change ((powHom3 v hv (Pi.mulSingle i (Multiplicative.ofAdd 1)) : C) : G) = u i
      rw [powHom3_mulSingle]
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_eq_fintype_card]
  · rw [← hrange] at hg
    obtain ⟨a, rfl⟩ := hg
    exact ⟨fun i => Multiplicative.toAdd (a i), (hφ a).symm⟩

@[expose] def tAi : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 0, 2, 2, 1, 2, 1, 0;
    0, 1, 1, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 2, 1, 0, 2;
    0, 1, 2, 1, 0, 2, 0, 2;
    0, 0, 2, 2, 1, 1, 1, 1;
    2, 2, 2, 2, 1, 0, 1, 0;
    2, 1, 0, 1, 0, 2, 0, 2;
    1, 1, 0, 1, 1, 1, 2, 1]

@[expose] def tBi : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 2, 0, 2, 1, 0, 0, 1;
    0, 0, 2, 2, 2, 2, 1, 1;
    0, 1, 0, 0, 0, 0, 1, 0;
    2, 1, 0, 0, 2, 0, 0, 0;
    0, 0, 2, 0, 2, 2, 0, 1;
    1, 2, 0, 2, 1, 0, 1, 1;
    0, 2, 0, 0, 2, 2, 2, 0;
    1, 2, 0, 1, 2, 0, 2, 0]

theorem tA_mul_tAi : tA * tAi = 1 := by decide
theorem tAi_mul_tA : tAi * tA = 1 := by decide
theorem tB_mul_tBi : tB * tBi = 1 := by decide
theorem tBi_mul_tB : tBi * tB = 1 := by decide

@[expose] def uA : GL8 := ⟨tA, tAi, tA_mul_tAi, tAi_mul_tA⟩

@[expose] def uB : GL8 := ⟨tB, tBi, tB_mul_tBi, tBi_mul_tB⟩

@[expose] def letterU (l : ℤ) : GL8 :=
  if l = 1 then uA else if l = 2 then uB else if l = -1 then uA⁻¹ else uB⁻¹

@[expose] def letterM (l : ℤ) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  if l = 1 then tA else if l = 2 then tB else if l = -1 then tAi else tBi

theorem val_letterU (l : ℤ) : (letterU l).val = letterM l := by
  unfold letterU letterM
  split_ifs <;> rfl

@[expose] def wordU (w : List ℤ) : GL8 := (w.map letterU).prod

theorem val_wordU (w : List ℤ) : (wordU w).val = (w.map letterM).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordU, List.map_cons, List.prod_cons, Units.val_mul] at ih ⊢
    rw [ih, val_letterU]

theorem letterU_mem (l : ℤ) : letterU l ∈ Subgroup.closure ({uA, uB} : Set GL8) := by
  unfold letterU
  have hA : uA ∈ Subgroup.closure ({uA, uB} : Set GL8) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : uB ∈ Subgroup.closure ({uA, uB} : Set GL8) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  split_ifs
  · exact hA
  · exact hB
  · exact Subgroup.inv_mem _ hA
  · exact Subgroup.inv_mem _ hB

theorem wordU_mem (w : List ℤ) : wordU w ∈ Subgroup.closure ({uA, uB} : Set GL8) := by
  unfold wordU
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (letterU_mem l) ih

@[expose] def sylWord (i : ℕ) : List ℤ :=
  [[-1, -1, -2, -2, -1, -2, -1, -1, -1, 2, 1, -2, -1, 2, -1, 2, 1, -2, -1, -2, 1, -2, -1, -2, 1, 1, -2, -1, -2, -2, 1, 1, 1, 1, 1, -2, -1, -2, -1, -2, -2, 1],
   [-1, -1, -1, -1, -2, -2, -1, 2, -1, -2, 1, -2, 1, 2, -1, -2, 1, -2, -1, 2, 1, 2, -1, -1, 2, 1, 2, -1, 2, 2, -1, -2, 1, 1, 1, 1, 1, -2, -1, -2, -1, -2, -2, 1],
   [-2, -2, 1, -2, -1, -2, 1, 1, -2, -1, 2, 2, -1, -2, 1, 1, 1, 1, -2, 1, 2, 1, 1, 2, 1, 1, 2, 2],
   [1, 1, 1, 1, 2, -1, -1, -1, -1, -1, -1, 2, 1, -2, 1, -2]].getD i []

@[expose] def mU1 : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![2, 2, 1, 2, 1, 0, 0, 1;
    0, 2, 2, 0, 2, 2, 2, 1;
    0, 0, 0, 2, 0, 0, 1, 2;
    1, 2, 2, 0, 2, 2, 0, 1;
    2, 1, 2, 2, 2, 1, 2, 0;
    0, 0, 1, 2, 0, 2, 2, 1;
    0, 0, 1, 2, 1, 1, 1, 0;
    0, 2, 1, 0, 2, 1, 2, 2]
@[expose] def mU2 : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 2, 1, 0, 0, 0, 0, 2;
    2, 2, 1, 0, 2, 0, 1, 1;
    2, 1, 1, 2, 0, 2, 0, 1;
    2, 1, 1, 1, 1, 2, 0, 1;
    0, 0, 2, 2, 2, 2, 2, 0;
    1, 2, 2, 0, 2, 2, 0, 2;
    1, 0, 1, 0, 0, 2, 2, 0;
    2, 2, 1, 1, 1, 1, 2, 0]
@[expose] def mU3 : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 0, 1, 1, 2, 0, 1, 0;
    2, 2, 1, 2, 2, 2, 1, 1;
    2, 1, 0, 0, 0, 2, 0, 1;
    2, 1, 0, 2, 1, 2, 0, 1;
    0, 0, 1, 0, 2, 2, 2, 0;
    1, 2, 0, 2, 2, 2, 0, 2;
    1, 0, 0, 2, 2, 2, 2, 0;
    1, 0, 2, 1, 1, 2, 0, 1]
@[expose] def mU4 : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 2, 0, 1, 2, 2;
    0, 0, 0, 2, 0, 0, 1, 2;
    2, 0, 1, 2, 0, 2, 0, 1;
    0, 2, 2, 1, 1, 2, 2, 2;
    0, 0, 1, 0, 0, 1, 2, 2;
    0, 1, 2, 1, 0, 1, 1, 1;
    2, 2, 0, 0, 0, 1, 2, 0]

set_option maxRecDepth 100000 in
theorem val_sylWord_zero : (wordU (sylWord 0)).val = mU1 := by rw [val_wordU]; decide
set_option maxRecDepth 100000 in
theorem val_sylWord_one : (wordU (sylWord 1)).val = mU2 := by rw [val_wordU]; decide
set_option maxRecDepth 100000 in
theorem val_sylWord_two : (wordU (sylWord 2)).val = mU3 := by rw [val_wordU]; decide
set_option maxRecDepth 100000 in
theorem val_sylWord_three : (wordU (sylWord 3)).val = mU4 := by rw [val_wordU]; decide

theorem mU_pow_three : mU1 ^ 3 = 1 ∧ mU2 ^ 3 = 1 ∧ mU3 ^ 3 = 1 ∧ mU4 ^ 3 = 1 := by decide

theorem mU_comm : mU1 * mU2 = mU2 * mU1 ∧ mU1 * mU3 = mU3 * mU1 ∧ mU2 * mU3 = mU3 * mU2 := by
  decide

set_option maxRecDepth 100000 in
theorem mU_ker : ∀ a : Fin 3 → Fin 3, a ≠ 0 →
    mU1 ^ (a 0 : ℕ) * (mU2 ^ (a 1 : ℕ) * mU3 ^ (a 2 : ℕ)) ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem mU4_ne : ∀ a : Fin 3 → Fin 3, mU1 ^ (a 0 : ℕ) * (mU2 ^ (a 1 : ℕ) * mU3 ^ (a 2 : ℕ)) ≠ mU4 := by
  decide

theorem mU4_conj : mU4 * mU1 * mU4 ^ 2 = mU1 ∧ mU4 * mU2 * mU4 ^ 2 = mU1 * mU2 ∧
    mU4 * mU3 * mU4 ^ 2 = mU1 ^ 2 * (mU2 ^ 2 * mU3) := by decide

@[expose] def sylU (i : ℕ) : GL8 := wordU (sylWord i)

@[expose] def sylV : Fin 3 → GL8 := fun i => sylU i.val

theorem val_sylV (i : Fin 3) : (sylV i).val = ![mU1, mU2, mU3] i := by
  fin_cases i
  · exact val_sylWord_zero
  · exact val_sylWord_one
  · exact val_sylWord_two

theorem val_sylU_three : (sylU 3).val = mU4 := val_sylWord_three

@[expose] def sylA : Subgroup GL8 := Subgroup.closure (Set.range sylV)

theorem sylV_pow (i : Fin 3) : sylV i ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, val_sylV, Units.val_one]
  obtain ⟨h1, h2, h3, -⟩ := mU_pow_three
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

theorem sylV_comm (i j : Fin 3) : Commute (sylV i) (sylV j) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_sylV, val_sylV]
  obtain ⟨h12, h13, h23⟩ := mU_comm
  fin_cases i <;> fin_cases j <;> simp [h12, h13, h23]

theorem val_list_prod_sylV (a : Fin 3 → Fin 3) :
    ((List.ofFn fun i => sylV i ^ (a i : ℕ)).prod).val =
      mU1 ^ (a 0 : ℕ) * (mU2 ^ (a 1 : ℕ) * mU3 ^ (a 2 : ℕ)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Units.val_mul, Units.val_pow_eq_pow_val, val_sylV]
  rfl

theorem sylA_facts : Nat.card sylA = 3 ^ 3 ∧
    ∀ g ∈ sylA, ∃ a : Fin 3 → Fin 3, (List.ofFn fun i => sylV i ^ (a i : ℕ)).prod = g :=
  card_closure_range_of_commuting sylV sylV_pow sylV_comm (fun a ha h => mU_ker a ha (by
    have := congrArg Units.val h
    rwa [val_list_prod_sylV, Units.val_one] at this))

theorem sylU_three_not_mem : sylU 3 ∉ sylA := by
  intro h
  obtain ⟨a, ha⟩ := sylA_facts.2 _ h
  apply mU4_ne a
  have := congrArg Units.val ha
  rwa [val_list_prod_sylV, val_sylU_three] at this

theorem sylU_three_pow : sylU 3 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, val_sylU_three, Units.val_one]
  exact mU_pow_three.2.2.2

theorem sylU_three_ne_one : sylU 3 ≠ 1 := by
  intro h
  apply sylU_three_not_mem
  rw [h]
  exact Subgroup.one_mem _

theorem orderOf_sylU_three : orderOf (sylU 3) = 3 :=
  orderOf_eq_prime sylU_three_pow sylU_three_ne_one

theorem sylU_three_inv : (sylU 3)⁻¹ = sylU 3 ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact sylU_three_pow)

theorem sylV_mem (i : Fin 3) : sylV i ∈ sylA := Subgroup.subset_closure ⟨i, rfl⟩

theorem conj_sylV_mem (i : Fin 3) : sylU 3 * sylV i * (sylU 3)⁻¹ ∈ sylA := by
  rw [sylU_three_inv]
  obtain ⟨h1, h2, h3⟩ := mU4_conj
  have hv := fun j => sylV_mem j
  fin_cases i
  · have : sylU 3 * sylV 0 * sylU 3 ^ 2 = sylV 0 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_sylU_three, val_sylV]
      exact h1
    simpa [this] using hv 0
  · have : sylU 3 * sylV 1 * sylU 3 ^ 2 = sylV 0 * sylV 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_sylU_three, val_sylV]
      exact h2
    simpa [this] using Subgroup.mul_mem _ (hv 0) (hv 1)
  · have : sylU 3 * sylV 2 * sylU 3 ^ 2 = sylV 0 ^ 2 * (sylV 1 ^ 2 * sylV 2) := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_sylU_three, val_sylV]
      exact h3
    simpa [this] using Subgroup.mul_mem _ (Subgroup.pow_mem _ (hv 0) 2)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hv 1) 2) (hv 2))

theorem mem_normalizer_closure_of_conj_mem {G : Type*} [Group G] [Finite G] {S : Set G} {u : G}
    (h : ∀ s ∈ S, u * s * u⁻¹ ∈ Subgroup.closure S) :
    u ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  rw [← CFSG.HardMathSupport.MathTwE6.map_conj_eq_iff_mem_normalizer]
  have hle : (Subgroup.closure S).map (MulAut.conj u).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj u).injective).ge

theorem sylU_three_mem_normalizer : sylU 3 ∈ Subgroup.normalizer (sylA : Set GL8) :=
  mem_normalizer_closure_of_conj_mem (by
    rintro _ ⟨i, rfl⟩
    exact conj_sylV_mem i)

@[expose] def sylH : Subgroup GL8 := sylA ⊔ Subgroup.zpowers (sylU 3)

theorem card_sylH : Nat.card sylH = 3 ^ 4 := by
  have hB : Subgroup.zpowers (sylU 3) ≤ Subgroup.normalizer (sylA : Set GL8) :=
    (Subgroup.zpowers_le).2 sylU_three_mem_normalizer
  have h := CFSG.HardMathSupport.MathTwE6.card_sup_mul_card_inf_of_le_normalizer hB
  have hz : Nat.card (Subgroup.zpowers (sylU 3)) = 3 := by
    rw [Nat.card_zpowers, orderOf_sylU_three]
  have hinf : Nat.card (sylA ⊓ Subgroup.zpowers (sylU 3) : Subgroup GL8) = 1 := by
    have hdvd : Nat.card (sylA ⊓ Subgroup.zpowers (sylU 3) : Subgroup GL8) ∣ 3 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : sylA ⊓ Subgroup.zpowers (sylU 3) ≤ Subgroup.zpowers (sylU 3))
      rwa [hz] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact h1
    · exfalso
      have heq : sylA ⊓ Subgroup.zpowers (sylU 3) = Subgroup.zpowers (sylU 3) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (hz.trans h3.symm))
      apply sylU_three_not_mem
      have : sylU 3 ∈ sylA ⊓ Subgroup.zpowers (sylU 3) := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact this.1
  rw [hinf, mul_one, sylA_facts.1, hz] at h
  rw [sylH, h]
  norm_num

theorem sylH_le : sylH ≤ Subgroup.closure ({uA, uB} : Set GL8) := by
  refine sup_le ?_ ?_
  · rw [sylA, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact wordU_mem _
  · exact (Subgroup.zpowers_le).2 (wordU_mem _)

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
