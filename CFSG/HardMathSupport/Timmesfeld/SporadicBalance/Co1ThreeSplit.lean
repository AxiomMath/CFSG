module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Leaf

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving Timmesfeld.Co1Leaf
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T (vecProd vecProdHom vecProdHom_apply
  exists_dot_eq_zero_imp_mem card_vec)

theorem mem_expVecs_iff {p : ℕ} : ∀ {r : ℕ} {e : List ℕ},
    e ∈ expVecs p r ↔ e.length = r ∧ ∀ x ∈ e, x < p
  | 0, e => by
    simp only [expVecs, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -⟩
      exact List.length_eq_zero_iff.1 h
  | r + 1, e => by
    simp only [expVecs, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨e', he', k, hk, rfl⟩
      obtain ⟨h1, h2⟩ := mem_expVecs_iff.1 he'
      refine ⟨by simp [h1], fun x hx => ?_⟩
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · exact hk
    · rintro ⟨hlen, hlt⟩
      obtain ⟨e', k, rfl⟩ : ∃ e' k, e = e' ++ [k] := by
        rcases List.eq_nil_or_concat' e with h | ⟨e', k, h⟩
        · subst h; simp at hlen
        · exact ⟨e', k, h⟩
      refine ⟨e', mem_expVecs_iff.2 ⟨by simpa using hlen, fun x hx => hlt x (by simp [hx])⟩, k,
        hlt k (by simp), rfl⟩

@[expose] def vecList {k : ℕ} (a : Fin k → ZMod 3) : List ℕ :=
  (List.finRange k).map fun i => (a i).val

@[expose] def listVec (k : ℕ) (l : List ℕ) : Fin k → ZMod 3 := fun i => (l.getD i.val 0 : ZMod 3)

theorem vecList_length {k : ℕ} (a : Fin k → ZMod 3) : (vecList a).length = k := by simp [vecList]

theorem vecList_getD {k : ℕ} (a : Fin k → ZMod 3) (i : Fin k) :
    (vecList a).getD i.val 0 = (a i).val := by
  simp [vecList, List.getD_eq_getElem?_getD]

theorem vecList_mem_expVecs {k : ℕ} (a : Fin k → ZMod 3) : vecList a ∈ expVecs 3 k := by
  refine mem_expVecs_iff.2 ⟨vecList_length a, fun x hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact ZMod.val_lt (a i)

theorem listVec_vecList {k : ℕ} (a : Fin k → ZMod 3) : listVec k (vecList a) = a := by
  funext i
  rw [listVec, vecList_getD, ZMod.natCast_zmod_val]


theorem vecProd_cons {S : Type*} [Group S] {n : ℕ} (d : Fin (n + 1) → S)
    (a : Fin (n + 1) → ZMod 3) :
    vecProd d a = d 0 ^ (a 0).val * vecProd (fun i => d i.succ) (fun i => a i.succ) := by
  simp only [vecProd, List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
  rfl

theorem vecProd_zero' {S : Type*} [Group S] {n : ℕ} (d : Fin n → S) :
    vecProd d (0 : Fin n → ZMod 3) = 1 :=
  Co3T.vecProd_zero d

theorem vecProd_single {S : Type*} [Group S] : ∀ {n : ℕ} (d : Fin n → S) (i : Fin n),
    vecProd d (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) = d i
  | 0, _, i => i.elim0
  | n + 1, d, i => by
    rw [vecProd_cons]
    cases i using Fin.cases with
    | zero =>
      have h0 : (fun j : Fin n =>
          (Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) : Fin (n + 1) → ZMod 3) j.succ) = 0 := by
        funext j
        simp [Fin.succ_ne_zero]
      rw [h0, vecProd_zero', Pi.single_eq_same, ZMod.val_one, pow_one, mul_one]
    | succ i' =>
      have h1 : (fun j : Fin n => (Pi.single i'.succ (1 : ZMod 3) : Fin (n + 1) → ZMod 3) j.succ) =
          (Pi.single i' 1 : Fin n → ZMod 3) := by
        funext j
        simp only [Pi.single_apply, Fin.succ_inj]
      rw [h1, vecProd_single, Pi.single_eq_of_ne (Fin.succ_ne_zero i').symm, ZMod.val_zero,
        pow_zero, one_mul]

theorem pivotIdx_spec {f : List ℕ} (h : ∃ i < f.length, f.getD i 0 ≠ 0) :
    pivotIdx f < f.length ∧ f.getD (pivotIdx f) 0 ≠ 0 := by
  unfold pivotIdx
  cases hf : (List.range f.length).find? (fun i => f.getD i 0 != 0) with
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨i, hi, hne⟩ := h
    have := hf i (List.mem_range.2 hi)
    simp only [bne_iff_ne, ne_eq, not_not] at this
    exact absurd this hne
  | some i =>
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [List.mem_range, bne_iff_ne, ne_eq] at hmem hp
    exact ⟨hmem, hp⟩

theorem mem_normVecs_iff {r : ℕ} {f : List ℕ} :
    f ∈ normVecs 3 r ↔ f ∈ expVecs 3 r ∧ f.getD (pivotIdx f) 0 = 1 := by
  simp [normVecs]

theorem normVecs_pivot {r : ℕ} {f : List ℕ} (hf : f ∈ normVecs 3 r) :
    f.length = r ∧ (∀ x ∈ f, x < 3) ∧ pivotIdx f < r ∧ f.getD (pivotIdx f) 0 = 1 := by
  obtain ⟨he, h1⟩ := mem_normVecs_iff.1 hf
  obtain ⟨hlen, hlt⟩ := mem_expVecs_iff.1 he
  refine ⟨hlen, hlt, ?_, h1⟩
  have hex : ∃ i < f.length, f.getD i 0 ≠ 0 := ⟨pivotIdx f, ?_, by rw [h1]; norm_num⟩
  · exact hlen ▸ (pivotIdx_spec hex).1
  · by_contra hge
    push Not at hge
    rw [List.getD_eq_default _ _ hge] at h1
    exact absurd h1 (by norm_num)

theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x
  decide

theorem exists_normVec {k : ℕ} {f : Fin k → ZMod 3} (hf : f ≠ 0) :
    ∃ fl ∈ normVecs 3 k, ∀ a : Fin k → ZMod 3,
      (∑ i, f i * a i = 0 ↔ ∑ i, listVec k fl i * a i = 0) := by
  have hex : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨i₀, hi₀⟩ := hex
  have hpred : ∀ c : ZMod 3, c ≠ 0 → ∀ i : ℕ,
      ((vecList fun j => c * f j).getD i 0 != 0) = ((vecList f).getD i 0 != 0) := by
    intro c hc i
    by_cases hi : i < k
    · have e1 := vecList_getD (fun j => c * f j) ⟨i, hi⟩
      have e2 := vecList_getD f ⟨i, hi⟩
      simp only at e1 e2
      rw [e1, e2]
      have : (c * f ⟨i, hi⟩).val = 0 ↔ (f ⟨i, hi⟩).val = 0 := by
        rw [ZMod.val_eq_zero, ZMod.val_eq_zero, mul_eq_zero, or_iff_right hc]
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
      exact not_congr this
    · rw [List.getD_eq_default _ _ (by rw [vecList_length]; omega),
        List.getD_eq_default _ _ (by rw [vecList_length]; omega)]
  have hpiv : ∀ c : ZMod 3, c ≠ 0 →
      pivotIdx (vecList fun j => c * f j) = pivotIdx (vecList f) := by
    intro c hc
    unfold pivotIdx
    rw [vecList_length, vecList_length]
    congr 1
    exact List.find?_congr fun i _ => hpred c hc i
  have hspec := pivotIdx_spec (f := vecList f) ⟨i₀.val, by rw [vecList_length]; exact i₀.isLt,
    by rw [vecList_getD]; exact (ZMod.val_ne_zero _).2 hi₀⟩
  set q := pivotIdx (vecList f) with hq
  have hqk : q < k := vecList_length f ▸ hspec.1
  have hfq : f ⟨q, hqk⟩ ≠ 0 := by
    have := hspec.2
    rw [vecList_getD f ⟨q, hqk⟩] at this
    exact (ZMod.val_ne_zero _).1 this
  set c : ZMod 3 := (f ⟨q, hqk⟩)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hfq
  have hcf : c * f ⟨q, hqk⟩ = 1 := inv_mul_cancel₀ hfq
  refine ⟨vecList fun j => c * f j, ?_, fun a => ?_⟩
  · refine mem_normVecs_iff.2 ⟨vecList_mem_expVecs _, ?_⟩
    rw [hpiv c hc0, vecList_getD (fun j => c * f j) ⟨q, hqk⟩]
    simp only [hcf, ZMod.val_one]
  · rw [listVec_vecList]
    simp only [mul_assoc, ← Finset.mul_sum]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h; exact (mul_eq_zero.1 h).resolve_left hc0


@[expose] def kerVec (fl : List ℕ) (j : ℕ) : List ℕ :=
  (List.range fl.length).map fun i =>
    if i == j then 1 else if i == pivotIdx fl then (3 - fl.getD j 0 % 3) % 3 else 0

theorem kerBasis_eq (fl : List ℕ) :
    kerBasis 3 fl = ((List.range fl.length).filter (· != pivotIdx fl)).map (kerVec fl) := rfl

theorem kerVec_length (fl : List ℕ) (j : ℕ) : (kerVec fl j).length = fl.length := by
  simp [kerVec]

theorem kerVec_getD {fl : List ℕ} {i : ℕ} (hi : i < fl.length) (j : ℕ) :
    (kerVec fl j).getD i 0 =
      if i = j then 1 else if i = pivotIdx fl then (3 - fl.getD j 0 % 3) % 3 else 0 := by
  simp [kerVec, List.getD_eq_getElem?_getD, hi]

theorem kerVec_lt (fl : List ℕ) (j : ℕ) : ∀ x ∈ kerVec fl j, x < 3 := by
  intro x hx
  simp only [kerVec, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  split_ifs
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem cast_neg_mod3 (n : ℕ) : (((3 - n % 3) % 3 : ℕ) : ZMod 3) = -(n : ZMod 3) := by
  have h := Nat.mod_lt n (show 0 < 3 by norm_num)
  rw [← ZMod.natCast_mod n 3]
  interval_cases hr : n % 3 <;> decide

theorem mem_kerBasis {fl : List ℕ} {b : List ℕ} (hb : b ∈ kerBasis 3 fl) :
    ∃ j < fl.length, j ≠ pivotIdx fl ∧ b = kerVec fl j := by
  rw [kerBasis_eq, List.mem_map] at hb
  obtain ⟨j, hj, rfl⟩ := hb
  rw [List.mem_filter, List.mem_range, bne_iff_ne] at hj
  exact ⟨j, hj.1, hj.2, rfl⟩

theorem dot_kerVec_eq_zero {k : ℕ} {fl : List ℕ} (hfl : fl ∈ normVecs 3 k) {j : ℕ} (hj : j < k)
    (hjq : j ≠ pivotIdx fl) : ∑ i, listVec k fl i * listVec k (kerVec fl j) i = 0 := by
  obtain ⟨hlen, -, hq, h1⟩ := normVecs_pivot hfl
  have hne : (⟨j, hj⟩ : Fin k) ≠ ⟨pivotIdx fl, hq⟩ := fun e => hjq (congrArg Fin.val e)
  have hval : ∀ i : Fin k, listVec k (kerVec fl j) i =
      if i.val = j then 1 else
        if i.val = pivotIdx fl then -((fl.getD j 0 : ℕ) : ZMod 3) else 0 := by
    intro i
    rw [listVec, kerVec_getD (hlen ▸ i.isLt)]
    split_ifs
    · simp
    · exact cast_neg_mod3 _
    · simp
  rw [Finset.sum_eq_add (⟨j, hj⟩ : Fin k) ⟨pivotIdx fl, hq⟩ hne]
  · rw [hval, hval]
    simp only [↓reduceIte, Ne.symm hjq]
    simp only [listVec, h1, Nat.cast_one, one_mul, mul_one]
    exact add_neg_cancel _
  · intro c _ hc
    rw [hval]
    have h1' : c.val ≠ j := fun e => hc.1 (Fin.ext e)
    have h2' : c.val ≠ pivotIdx fl := fun e => hc.2 (Fin.ext e)
    simp [h1', h2']
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem listVec_kerVec {k : ℕ} {fl : List ℕ} (hlen : fl.length = k) (j : ℕ) (i : Fin k) :
    listVec k (kerVec fl j) i =
      if i.val = j then 1 else
        if i.val = pivotIdx fl then -((fl.getD j 0 : ℕ) : ZMod 3) else 0 := by
  rw [listVec, kerVec_getD (hlen ▸ i.isLt)]
  split_ifs
  · simp
  · exact cast_neg_mod3 _
  · simp

theorem eq_sum_kerVec {k : ℕ} {fl : List ℕ} (hfl : fl ∈ normVecs 3 k) {x : Fin k → ZMod 3}
    (hx : ∑ i, listVec k fl i * x i = 0) :
    x = ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val ≠ pivotIdx fl),
      x j • listVec k (kerVec fl j.val) := by
  obtain ⟨hlen, -, hq, h1⟩ := normVecs_pivot hfl
  set q : Fin k := ⟨pivotIdx fl, hq⟩ with hqdef
  set s := Finset.univ.filter (fun j : Fin k => j.val ≠ pivotIdx fl) with hs
  have hfq : listVec k fl q = 1 := by
    show ((fl.getD (pivotIdx fl) 0 : ℕ) : ZMod 3) = 1
    rw [h1, Nat.cast_one]
  have hqs : q ∉ s := by simp [hs, hqdef]
  have hsum : x q + ∑ j ∈ s, listVec k fl j * x j = 0 := by
    have hu : (Finset.univ : Finset (Fin k)) = insert q s := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, hs, Finset.mem_filter, true_and, true_iff]
      by_cases h : j = q
      · exact Or.inl h
      · exact Or.inr fun e => h (Fin.ext e)
    rw [hu, Finset.sum_insert hqs, hfq, one_mul] at hx
    exact hx
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, listVec_kerVec hlen]
  by_cases hiq : i = q
  · subst hiq
    have hqv : q.val = pivotIdx fl := rfl
    have : ∀ j ∈ s, x j * (if q.val = j.val then 1 else if q.val = pivotIdx fl then
        -((fl.getD j.val 0 : ℕ) : ZMod 3) else 0) = -(listVec k fl j * x j) := by
      intro j hj
      have hj2 : j.val ≠ pivotIdx fl := by
        simp only [hs, Finset.mem_filter] at hj
        exact hj.2
      have hj' : ¬ (q.val = j.val) := fun e => hj2 (by rw [← e])
      have hj'' : ¬ (pivotIdx fl = j.val) := fun e => hj' (by rw [hqv]; exact e)
      simp only [hqv, hj'', ↓reduceIte]
      show x j * -((fl.getD j.val 0 : ℕ) : ZMod 3) = -(((fl.getD j.val 0 : ℕ) : ZMod 3) * x j)
      rw [show x j * -((fl.getD j.val 0 : ℕ) : ZMod 3) = -(x j * ((fl.getD j.val 0 : ℕ) : ZMod 3))
        from mul_neg _ _, show x j * ((fl.getD j.val 0 : ℕ) : ZMod 3) =
          ((fl.getD j.val 0 : ℕ) : ZMod 3) * x j from mul_comm _ _]
    rw [Finset.sum_congr rfl this,
      show (∑ j ∈ s, -(listVec k fl j * x j)) = -∑ j ∈ s, listVec k fl j * x j from
        Finset.sum_neg_distrib _]
    exact eq_neg_of_add_eq_zero_left hsum
  · have his : i ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun e => hiq (Fin.ext e)
    have hiv : i.val ≠ pivotIdx fl := fun e => hiq (Fin.ext e)
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have : ¬ (i.val = j.val) := fun e => hji (Fin.ext e.symm)
      simp [this, hiv]
    · intro h
      exact absurd his h

theorem kerVec_mem_kerBasis {fl : List ℕ} {j : ℕ} (hj : j < fl.length) (hjq : j ≠ pivotIdx fl) :
    kerVec fl j ∈ kerBasis 3 fl := by
  rw [kerBasis_eq, List.mem_map]
  exact ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, bne_iff_ne.2 hjq⟩, rfl⟩

section Hyperplane

variable {S : Type*} [Group S] {k : ℕ} {d : Fin k → S}

theorem exists_normVec_ker_mem (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    (hinj : Function.Injective (vecProdHom d hcomm hpow)) {B : Subgroup S}
    (hB : B ≤ (vecProdHom d hcomm hpow).range)
    (hidx : B.relIndex (vecProdHom d hcomm hpow).range = 3) :
    ∃ fl ∈ normVecs 3 k, ∀ b ∈ kerBasis 3 fl, vecProd d (listVec k b) ∈ B := by
  set φ := vecProdHom d hcomm hpow with hφ
  have hK : Nat.card φ.range = 3 ^ k := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, card_vec]
  have hcard : Nat.card B * 3 = 3 ^ k := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := φ.range)
    rw [hidx, inf_eq_left.2 hB, hK] at h
    rw [mul_comm]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf0, hf⟩ := exists_dot_eq_zero_imp_mem φ hinj hB hcard
  obtain ⟨fl, hfl, hfleq⟩ := exists_normVec hf0
  refine ⟨fl, hfl, fun b hb => ?_⟩
  obtain ⟨j, hj, hjq, rfl⟩ := mem_kerBasis hb
  have hjk : j < k := (normVecs_pivot hfl).1 ▸ hj
  exact hf _ ((hfleq _).2 (dot_kerVec_eq_zero hfl hjk hjq))

theorem mem_closure_of_dot_eq_zero (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    {fl : List ℕ} (hfl : fl ∈ normVecs 3 k) {a : Fin k → ZMod 3}
    (ha : ∑ i, listVec k fl i * a i = 0) :
    vecProdHom d hcomm hpow (Multiplicative.ofAdd a) ∈
      Subgroup.closure {x | ∃ b ∈ kerBasis 3 fl, x = vecProd d (listVec k b)} := by
  rw [eq_sum_kerVec hfl ha, ofAdd_sum]
  refine Finset.prod_induction _ (fun m => vecProdHom d hcomm hpow m ∈ Subgroup.closure
      {x | ∃ b ∈ kerBasis 3 fl, x = vecProd d (listVec k b)})
    (fun m m' hm hm' => by rw [map_mul]; exact Subgroup.mul_mem _ hm hm')
    (by rw [map_one]; exact Subgroup.one_mem _) fun j hj => ?_
  rw [Finset.mem_filter] at hj
  have e : a j • listVec k (kerVec fl j.val) = (a j).val • listVec k (kerVec fl j.val) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id]
  rw [e, ofAdd_nsmul, map_pow]
  refine Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _
  exact ⟨kerVec fl j.val, kerVec_mem_kerBasis ((normVecs_pivot hfl).1 ▸ j.isLt) hj.2, rfl⟩

theorem exists_normVec_eq_closure (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    (hinj : Function.Injective (vecProdHom d hcomm hpow)) {B : Subgroup S}
    (hB : B ≤ (vecProdHom d hcomm hpow).range)
    (hidx : B.relIndex (vecProdHom d hcomm hpow).range = 3) :
    ∃ fl ∈ normVecs 3 k,
      B = Subgroup.closure {x | ∃ b ∈ kerBasis 3 fl, x = vecProd d (listVec k b)} := by
  obtain ⟨fl, hfl, hmem⟩ := exists_normVec_ker_mem hcomm hpow hinj hB hidx
  set φ := vecProdHom d hcomm hpow with hφ
  set K := Subgroup.closure {x | ∃ b ∈ kerBasis 3 fl, x = vecProd d (listVec k b)} with hKdef
  have hKB : K ≤ B := by
    rw [hKdef, Subgroup.closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact hmem b hb
  refine ⟨fl, hfl, le_antisymm ?_ hKB⟩
  intro x hx
  obtain ⟨m, rfl⟩ := hB hx
  set a := Multiplicative.toAdd m with ha
  have hm : m = Multiplicative.ofAdd a := by simp [ha]
  by_cases h0 : ∑ i, listVec k fl i * a i = 0
  · rw [hm]
    exact mem_closure_of_dot_eq_zero hcomm hpow hfl h0
  · exfalso
    obtain ⟨-, -, hq, h1⟩ := normVecs_pivot hfl
    set t := ∑ i, listVec k fl i * a i with ht
    have hall : φ.range ≤ B := by
      rintro _ ⟨z, rfl⟩
      set c : ZMod 3 := (∑ i, listVec k fl i * (Multiplicative.toAdd z) i) * t⁻¹ with hc
      set z' : Fin k → ZMod 3 := fun i => (Multiplicative.toAdd z) i - c * a i with hz'
      have hz'0 : ∑ i, listVec k fl i * z' i = 0 := by
        have : ∀ i, listVec k fl i * z' i =
            listVec k fl i * (Multiplicative.toAdd z) i - c * (listVec k fl i * a i) := by
          intro i; simp only [hz']; ring
        rw [Finset.sum_congr rfl fun i _ => this i,
          show (∑ i, (listVec k fl i * (Multiplicative.toAdd z) i - c * (listVec k fl i * a i))) =
              ∑ i, listVec k fl i * (Multiplicative.toAdd z) i -
                ∑ i, c * (listVec k fl i * a i) from Finset.sum_sub_distrib _ _,
          show (∑ i, c * (listVec k fl i * a i)) = c * ∑ i, listVec k fl i * a i from
            (Finset.mul_sum _ _ _).symm, hc, mul_assoc, ← ht, inv_mul_cancel₀ h0, mul_one,
          sub_self]
      have hz : z = Multiplicative.ofAdd z' * m ^ c.val := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [toAdd_mul, toAdd_pow, toAdd_ofAdd, Pi.add_apply, Pi.smul_apply, ← ha, hz']
        simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id]
        ring
      rw [hz, map_mul, map_pow]
      refine B.mul_mem (hKB (mem_closure_of_dot_eq_zero hcomm hpow hfl hz'0)) (B.pow_mem hx _)
    rw [Subgroup.relIndex_eq_one.2 hall] at hidx
    exact absurd hidx (by norm_num)

end Hyperplane

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

end
