module

public import CFSG.LieType.Universal.Unitary.Extras.Torus
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.HardMathSupport.U4FF.ClassChar
public import CFSG.HardMathSupport.U4FF.ClassDigits

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.HardMathSupport.U4FF

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] {k : Type} [Field k]

@[expose] def bDigit {n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) : ℕ :=
  ∑ r : Fin f, if j ∈ ε r then 2 ^ (r : ℕ) else 0

@[expose] def bExp {n : ℕ} (ε : Fin f → Finset (Fin n)) (a : Fin n) : ℕ :=
  ∑ r : Fin f, 2 ^ (r : ℕ) * ((ε r).filter fun j => a < j).card

theorem sum_fin_two_pow_eq : ∑ r : Fin f, 2 ^ (r : ℕ) = 2 ^ f - 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  have := digits_sum_range_add_one f
  omega

theorem bDigit_lt {n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) : bDigit ε j < 2 ^ f := by
  have hle : bDigit ε j ≤ ∑ r : Fin f, 2 ^ (r : ℕ) :=
    Finset.sum_le_sum fun r _ => by split_ifs <;> simp
  rw [sum_fin_two_pow_eq] at hle
  have h2 : 0 < 2 ^ f := by positivity
  omega

theorem bDigit_eq_zero_iff {n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) :
    bDigit ε j = 0 ↔ ∀ r, j ∉ ε r := by
  rw [bDigit, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp

theorem bDigit_eq_iff {n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) :
    bDigit ε j = 2 ^ f - 1 ↔ ∀ r, j ∈ ε r := by
  constructor
  · intro h r
    by_contra hr
    have hlt : bDigit ε j < 2 ^ f - 1 := by
      have hlt' : (∑ s : Fin f, (if j ∈ ε s then 2 ^ (s : ℕ) else 0)) <
          ∑ s : Fin f, 2 ^ (s : ℕ) := by
        refine Finset.sum_lt_sum (fun s _ => ?_) ⟨r, Finset.mem_univ _, ?_⟩
        · split_ifs <;> simp
        · simp [hr]
      rw [bDigit]
      rwa [sum_fin_two_pow_eq] at hlt'
    omega
  · intro h
    rw [bDigit]
    have hc : ∀ s : Fin f, (if j ∈ ε s then 2 ^ (s : ℕ) else 0) = 2 ^ (s : ℕ) :=
      fun s => if_pos (h s)
    simp only [hc]
    rw [sum_fin_two_pow_eq]

theorem bExp_eq_add {n : ℕ} (ε : Fin f → Finset (Fin n)) {a b : Fin n}
    (hab : (b : ℕ) = (a : ℕ) + 1) : bExp ε a = bExp ε b + bDigit ε b := by
  rw [bExp, bExp, bDigit, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hset : (ε r).filter (fun j : Fin n => a < j) =
      (ε r).filter (fun j : Fin n => b < j) ∪ (if b ∈ ε r then {b} else ∅) := by
    by_cases hb : b ∈ ε r
    · rw [if_pos hb]
      ext j
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, haj⟩
        by_cases hbj : b < j
        · exact Or.inl ⟨hj, hbj⟩
        · right
          exact Fin.ext (by simp only [Fin.lt_def] at haj hbj; omega)
      · rintro (⟨hj, hbj⟩ | hbj)
        · exact ⟨hj, by simp only [Fin.lt_def] at hbj ⊢; omega⟩
        · subst hbj
          exact ⟨hb, by simp only [Fin.lt_def] at hb ⊢; omega⟩
    · rw [if_neg hb, Finset.union_empty]
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, haj⟩
        have hne : j ≠ b := fun h => hb (h ▸ hj)
        refine ⟨hj, ?_⟩
        simp only [Fin.lt_def] at haj hne ⊢
        omega
      · rintro ⟨hj, hbj⟩
        exact ⟨hj, by simp only [Fin.lt_def] at hbj ⊢; omega⟩
  rw [hset]
  have hdisj : Disjoint ((ε r).filter (fun j : Fin n => b < j))
      (if b ∈ ε r then {b} else ∅) := by
    by_cases hb : b ∈ ε r
    · rw [if_pos hb, Finset.disjoint_singleton_right]
      simp
    · rw [if_neg hb]
      exact Finset.disjoint_empty_right _
  rw [Finset.card_union_of_disjoint hdisj]
  by_cases hb : b ∈ ε r
  · simp [hb]
    ring
  · simp [hb]

theorem exists_bDigit_eq {n : ℕ} (d : Fin n → ℕ) (hd : ∀ j, d j < 2 ^ f) :
    ∃ ε : Fin f → Finset (Fin n), ∀ j, bDigit ε j = d j := by
  choose C hC hsum using fun j => exists_set_sum f (d j) (hd j)
  refine ⟨fun r => Finset.univ.filter (fun j => (r : ℕ) ∈ C j), fun j => ?_⟩
  have h1 : bDigit (fun r : Fin f => Finset.univ.filter (fun j => (r : ℕ) ∈ C j)) j =
      ∑ r : Fin f, (if (r : ℕ) ∈ C j then 2 ^ (r : ℕ) else 0) := by
    rw [bDigit]
    exact Finset.sum_congr rfl fun r _ => by simp
  rw [h1, ← Finset.sum_filter]
  have h2 : ∑ r ∈ Finset.univ.filter (fun r : Fin f => (r : ℕ) ∈ C j), 2 ^ (r : ℕ) =
      ∑ m ∈ C j, 2 ^ m := by
    refine Finset.sum_bij (fun r _ => (r : ℕ)) (fun r hr => ?_)
      (fun r₁ r₂ _ _ h => Fin.val_injective h) (fun m hm => ?_) (fun r _ => rfl)
    · exact (Finset.mem_filter.mp hr).2
    · have hm' : m < f := Finset.mem_range.mp (hC j hm)
      exact ⟨⟨m, hm'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  rw [h2, hsum j]

@[expose] noncomputable def chiEps (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n))
    (g : SU (unitaryInvolution F 2 f) n) : k :=
  φ₀ (∏ a, SUExtras.mat (unitaryInvolution F 2 f) n g a a ^ bExp ε a)

theorem chiEps_mul (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n))
    {g h : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ diagSubgroup (unitaryInvolution F 2 f) n)
    (hh : h ∈ diagSubgroup (unitaryInvolution F 2 f) n) :
    chiEps φ₀ ε (g * h) = chiEps φ₀ ε g * chiEps φ₀ ε h := by
  obtain ⟨d, hd⟩ := hg
  obtain ⟨e, he⟩ := hh
  have hd' : SUExtras.mat (unitaryInvolution F 2 f) n g = diagonal d := hd
  have he' : SUExtras.mat (unitaryInvolution F 2 f) n h = diagonal e := he
  have hprod : (∏ a, SUExtras.mat (unitaryInvolution F 2 f) n (g * h) a a ^ bExp ε a) =
      (∏ a, SUExtras.mat (unitaryInvolution F 2 f) n g a a ^ bExp ε a) *
        ∏ a, SUExtras.mat (unitaryInvolution F 2 f) n h a a ^ bExp ε a := by
    rw [map_mul, hd', he', diagonal_mul_diagonal]
    simp only [Matrix.diagonal_apply_eq, mul_pow, Finset.prod_mul_distrib]
  simp only [chiEps]
  rw [hprod, map_mul]

theorem chiEps_one (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n)) :
    chiEps φ₀ ε 1 = 1 := by
  simp [chiEps]

section ProdPow

omit [Finite F] [CharP F 2] in
theorem prod_pow_shortTorusFun {σ : F ≃+* F} {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F}
    (e : Fin n → ℕ) :
    ∏ t, shortTorusFun σ a b c t ^ e t =
      c ^ e a * (c⁻¹) ^ e b * ((σ c)⁻¹) ^ e (Fin.rev a) * (σ c) ^ e (Fin.rev b) := by
  have hsupp : ∀ t ∉ ({a, b, Fin.rev a, Fin.rev b} : Finset (Fin n)),
      shortTorusFun σ a b c t ^ e t = 1 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [SUExtras.shortTorusFun_of_ne ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, one_pow]
  rw [← Finset.prod_subset (Finset.subset_univ _) fun t _ ht => hsupp t ht]
  rw [Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, ha, fun h => hba (by rw [h, Fin.rev_rev])⟩),
    Finset.prod_insert (by simp [hb, hba]),
    Finset.prod_insert (by
      simp only [Finset.mem_singleton]
      exact fun h => hab (Fin.rev_injective h)), Finset.prod_singleton]
  have va : shortTorusFun σ a b c a = c := SUExtras.shortTorusFun_left a b c
  have vb : shortTorusFun σ a b c b = c⁻¹ := SUExtras.shortTorusFun_right hab c
  have vra : shortTorusFun σ a b c (Fin.rev a) = (σ c)⁻¹ := by
    rw [shortTorusFun, if_neg (Ne.symm ha), if_neg (Ne.symm hba), if_pos rfl]
  have vrb : shortTorusFun σ a b c (Fin.rev b) = σ c := by
    rw [shortTorusFun, if_neg (fun h => hba (by rw [← h, Fin.rev_rev])),
      if_neg (Ne.symm hb), if_neg (fun h => hab (Fin.rev_injective h).symm), if_pos rfl]
  rw [va, vb, vra, vrb]
  ac_rfl

omit [Finite F] [CharP F 2] in
theorem prod_pow_longTorusFun {n : ℕ} {b : Fin n} (hb : b ≠ Fin.rev b) {e : F}
    (c : Fin n → ℕ) :
    ∏ t, longTorusFun b e t ^ c t = e ^ c b * (e⁻¹) ^ c (Fin.rev b) := by
  have hsupp : ∀ t ∉ ({b, Fin.rev b} : Finset (Fin n)), longTorusFun b e t ^ c t = 1 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [SUExtras.longTorusFun_of_ne ht.1 ht.2, one_pow]
  rw [← Finset.prod_subset (Finset.subset_univ _) fun t _ ht => hsupp t ht,
    Finset.prod_insert (by simpa using hb), Finset.prod_singleton]
  have vb : longTorusFun b e b = e := SUExtras.longTorusFun_self b e
  have vrb : longTorusFun b e (Fin.rev b) = e⁻¹ := by
    rw [longTorusFun, if_neg (Ne.symm hb), if_pos rfl]
  rw [vb, vrb]

omit [Finite F] [CharP F 2] in
theorem prod_pow_heisTorusFun {σ : F ≃+* F} {n : ℕ} {b mid : Fin n}
    (hm : Fin.rev mid = mid) (huniq : ∀ s, Fin.rev s = s → s = mid) (hb : b ≠ Fin.rev b)
    (hbm : b ≠ mid) (hb'm : Fin.rev b ≠ mid) {t : F} (e : Fin n → ℕ) :
    ∏ s, heisTorusFun σ b t s ^ e s =
      t ^ e b * ((σ t)⁻¹) ^ e (Fin.rev b) * (σ t / t) ^ e mid := by
  have hsupp : ∀ s ∉ ({b, Fin.rev b, mid} : Finset (Fin n)),
      heisTorusFun σ b t s ^ e s = 1 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [SUExtras.heisTorusFun_of_ne hs.1 hs.2.1 (fun h => hs.2.2 (huniq s h)), one_pow]
  rw [← Finset.prod_subset (Finset.subset_univ _) fun s _ hs => hsupp s hs]
  rw [Finset.prod_insert (by simp [hb, hbm]), Finset.prod_insert (by simpa using hb'm),
    Finset.prod_singleton]
  have vb : heisTorusFun σ b t b = t := SUExtras.heisTorusFun_self b t
  have vrb : heisTorusFun σ b t (Fin.rev b) = (σ t)⁻¹ := by
    rw [heisTorusFun, if_neg (Ne.symm hb), if_pos rfl]
  have vmid : heisTorusFun σ b t mid = σ t / t := by
    rw [heisTorusFun, if_neg (Ne.symm hbm), if_neg (Ne.symm hb'm), if_pos hm]
  rw [vb, vrb, vmid, mul_assoc]

end ProdPow

theorem chiEps_of_tFun (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2))
    {x : SU (unitaryInvolution F 2 f) n} {c : F} (hc : c ≠ 0)
    (hx : SUExtras.mat (unitaryInvolution F 2 f) n x =
      diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c)) :
    chiEps φ₀ ε x = φ₀ c ^ bDigit ε ⟨(s : ℕ) + 1, by omega⟩ *
      (if 2 * (s : ℕ) + 2 = n then 1
        else φ₀ (unitaryInvolution F 2 f c) ^ bDigit ε ⟨n - 1 - s, by omega⟩) := by
  have hσc : unitaryInvolution F 2 f c ≠ 0 := (map_ne_zero _).mpr hc
  have key : chiEps φ₀ ε x =
      φ₀ (∏ t, SUExtras.tFun (unitaryInvolution F 2 f) s c t ^ bExp ε t) := by
    simp only [chiEps]
    congr 1
    rw [hx]
    simp only [Matrix.diagonal_apply_eq]
  rw [key]
  by_cases h : s.val + 1 < n / 2
  ·
    rw [SUExtras.tFun, dite_eq_left h]
    have hif : ¬ (2 * (s : ℕ) + 2 = n) := by omega
    have hp : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = lowIdx ⟨s.val + 1, h⟩ := Fin.ext rfl
    have hq' : (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = Fin.rev (lowIdx s) :=
      Fin.ext (by simp only [Fin.val_rev, val_lowIdx]; omega)
    have hmain : ∏ t, shortTorusFun (unitaryInvolution F 2 f) (lowIdx s)
        (lowIdx ⟨s.val + 1, h⟩) c t ^ bExp ε t =
        c ^ bDigit ε (lowIdx ⟨s.val + 1, h⟩) *
          (unitaryInvolution F 2 f c) ^ bDigit ε (Fin.rev (lowIdx s)) := by
      rw [prod_pow_shortTorusFun (σ := unitaryInvolution F 2 f) (a := lowIdx s)
        (b := lowIdx ⟨s.val + 1, h⟩) (lowIdx_ne_succ h)
        (lowIdx_ne_rev s s) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
        (c := c) (e := bExp ε),
        bExp_eq_add ε (a := lowIdx s) (b := lowIdx ⟨s.val + 1, h⟩) rfl,
        bExp_eq_add ε (a := Fin.rev (lowIdx ⟨s.val + 1, h⟩))
          (b := Fin.rev (lowIdx s)) (by
            simp only [Fin.val_rev, val_lowIdx]
            omega),
        pow_add, pow_add, inv_pow, inv_pow]
      have hcB : c ^ bExp ε (lowIdx ⟨s.val + 1, h⟩) ≠ 0 := pow_ne_zero _ hc
      have hσA : (unitaryInvolution F 2 f c) ^ bExp ε (Fin.rev (lowIdx s)) ≠ 0 :=
        pow_ne_zero _ hσc
      field_simp
    rw [hmain, if_neg hif, hp, hq', map_mul, map_pow, map_pow]
  · rw [SUExtras.tFun, dite_eq_right h]
    by_cases hn : Even n
    ·
      rw [ite_eq_left hn]
      have hif : 2 * (s : ℕ) + 2 = n := by
        obtain ⟨k, hk⟩ := hn
        omega
      have hp : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = Fin.rev (lowIdx s) :=
        Fin.ext (by simp only [Fin.val_rev, val_lowIdx]; omega)
      have hmain : ∏ t, longTorusFun (lowIdx s) c t ^ bExp ε t =
          c ^ bDigit ε (Fin.rev (lowIdx s)) := by
        rw [prod_pow_longTorusFun (hb := lowIdx_ne_rev s s) (e := c) (c := bExp ε),
          bExp_eq_add ε (a := lowIdx s) (b := Fin.rev (lowIdx s)) (by
            simp only [Fin.val_rev, val_lowIdx]
            omega),
          pow_add, inv_pow]
        field_simp
      rw [hmain, if_pos hif, hp, map_pow, mul_one]
    ·
      rw [ite_eq_right hn]
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
      have hif : ¬ (2 * (s : ℕ) + 2 = n) := by omega
      have hsk : (s : ℕ) + 1 = n / 2 := by omega
      let mid : Fin n := ⟨n / 2, by omega⟩
      have hmidval : (mid : ℕ) = n / 2 := rfl
      have hmid : Fin.rev mid = mid := by
        refine Fin.ext ?_
        simp only [Fin.val_rev, hmidval]
        omega
      have huniq : ∀ t : Fin n, Fin.rev t = t → t = mid := by
        intro t ht
        have ht' : n - ((t : ℕ) + 1) = (t : ℕ) := by
          have := congrArg (fun x : Fin n => (x : ℕ)) ht
          simpa only [Fin.val_rev] using this
        refine Fin.ext ?_
        simp only [hmidval]
        omega
      have hp : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = mid :=
        Fin.ext (by simp only [hmidval]; omega)
      have hq' : (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = Fin.rev (lowIdx s) :=
        Fin.ext (by simp only [Fin.val_rev, val_lowIdx]; omega)
      have hbm : lowIdx s ≠ mid := by
        refine Fin.ne_of_val_ne ?_
        simp only [val_lowIdx, hmidval]
        omega
      have hb'm : Fin.rev (lowIdx s) ≠ mid := by
        refine Fin.ne_of_val_ne ?_
        simp only [Fin.val_rev, val_lowIdx, hmidval]
        omega
      have hmain : ∏ t, heisTorusFun (unitaryInvolution F 2 f) (lowIdx s) c t ^
          bExp ε t = c ^ bDigit ε mid *
            (unitaryInvolution F 2 f c) ^ bDigit ε (Fin.rev (lowIdx s)) := by
        rw [prod_pow_heisTorusFun (σ := unitaryInvolution F 2 f) (b := lowIdx s)
          (mid := mid) hmid huniq (lowIdx_ne_rev s s) hbm hb'm (e := bExp ε),
          bExp_eq_add ε (a := lowIdx s) (b := mid) (by
            simp only [val_lowIdx, hmidval]
            omega),
          bExp_eq_add ε (a := mid) (b := Fin.rev (lowIdx s)) (by
            simp only [Fin.val_rev, val_lowIdx, hmidval]
            omega),
          pow_add, pow_add, div_pow, inv_pow]
        have hcA : c ^ bExp ε mid ≠ 0 := pow_ne_zero _ hc
        have hσB : (unitaryInvolution F 2 f c) ^ bExp ε (Fin.rev (lowIdx s)) ≠ 0 :=
          pow_ne_zero _ hσc
        field_simp
        ring
      rw [hmain, if_neg hif, hp, hq', map_mul, map_pow, map_pow]

@[expose] def IsFullNode {n : ℕ} (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2)) : Prop :=
  ∀ r, (⟨(s : ℕ) + 1, by omega⟩ : Fin n) ∈ ε r ∧
    (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) ∈ ε r

omit [Finite F] [CharP F 2] in
theorem longTorusFun_rev {n : ℕ} {b : Fin n} (hb : b ≠ Fin.rev b) (e : F) :
    longTorusFun b e (Fin.rev b) = e⁻¹ := by
  rw [longTorusFun, if_neg (Ne.symm hb), if_pos rfl]

omit [Finite F] [CharP F 2] in
theorem pow_sub_one_eq_one_of_pow_eq {x : F} {q : ℕ} (hq : 1 ≤ q) (hx0 : x ≠ 0)
    (hx : x ^ q = x) : x ^ (q - 1) = 1 := by
  have hmul : x ^ (q - 1) * x = 1 * x := by
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq, hx]
  exact mul_right_cancel₀ hx0 hmul

theorem chiEps_eq_one_of_isFullNode (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (ε : Fin f → Finset (Fin n)) {s : Fin (n / 2)} (hs : IsFullNode ε s)
    {t : SU (unitaryInvolution F 2 f) n} (ht : t ∈ levelTorus (unitaryInvolution F 2 f) s) :
    chiEps φ₀ ε t = 1 := by
  obtain ⟨c, hc⟩ := SUExtras.exists_tFun_of_mem_levelTorus ht
  rw [chiEps_of_tFun φ₀ ε s c.ne_zero hc]
  have hd1 : bDigit ε (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = 2 ^ f - 1 :=
    (bDigit_eq_iff ε _).mpr fun r => (hs r).1
  have hd2 : bDigit ε (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = 2 ^ f - 1 :=
    (bDigit_eq_iff ε _).mpr fun r => (hs r).2
  rw [hd1, hd2]
  have hσpow : φ₀ (unitaryInvolution F 2 f (c : F)) = φ₀ (c : F) ^ 2 ^ f := by
    rw [unitaryInvolution_apply, map_pow]
  have hcard : (2 ^ f - 1) + 2 ^ f * (2 ^ f - 1) = Nat.card F - 1 := by
    rw [hF]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow 2 (2 ^ f) (by omega)
    zify [h1, h2]
    ring
  let : Fintype F := Fintype.ofFinite F
  have hcF : (c : F) ^ (Nat.card F - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (c : F) c.ne_zero
    rwa [Nat.card_eq_fintype_card]
  by_cases h : s.val + 1 < n / 2
  · rw [if_neg (by omega : ¬ 2 * (s : ℕ) + 2 = n)]
    rw [hσpow, ← pow_mul, ← pow_add, hcard, ← map_pow, hcF, map_one]
  · by_cases hn : Even n
    ·
      rw [SUExtras.tFun, dite_eq_right h, ite_eq_left hn] at hc
      have hunit := unitary_of_coe_eq_diagonal hc (lowIdx s)
      rw [SUExtras.longTorusFun_self, longTorusFun_rev (lowIdx_ne_rev s s)] at hunit
      have hσc : unitaryInvolution F 2 f (c : F) = c := by
        have := (mul_inv_eq_iff_eq_mul₀ c.ne_zero).mp hunit
        simpa using this
      have hc2 : (c : F) ^ 2 ^ f = c := by
        rw [← unitaryInvolution_apply]
        exact hσc
      have hc1 : (c : F) ^ (2 ^ f - 1) = 1 :=
        pow_sub_one_eq_one_of_pow_eq (Nat.one_le_two_pow (n := f)) c.ne_zero hc2
      rw [if_pos (by
        obtain ⟨k, hk⟩ := hn
        omega : 2 * (s : ℕ) + 2 = n), mul_one, ← map_pow, hc1, map_one]
    · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
      rw [if_neg (by omega : ¬ 2 * (s : ℕ) + 2 = n)]
      rw [hσpow, ← pow_mul, ← pow_add, hcard, ← map_pow, hcF, map_one]

theorem exists_mem_levelTorus_tFun (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (s : Fin (n / 2))
    {c : F} (hc : c ≠ 0) (hne : ¬ (¬ s.val + 1 < n / 2 ∧ Even n)) :
    ∃ g ∈ levelTorus (unitaryInvolution F 2 f) s,
      SUExtras.mat (unitaryInvolution F 2 f) n g =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) := by
  have hσ := unitaryInvolution_involutive hF
  by_cases h : s.val + 1 < n / 2
  · refine ⟨shortTorus (unitaryInvolution F 2 f) hσ (lowIdx_ne_succ h) (lowIdx_ne_rev s s)
      (lowIdx_ne_rev _ _) (↑(Units.mk0 c hc)), shortTorus_mem_levelTorus hσ h (Units.mk0 c hc),
      ?_⟩
    rw [SUExtras.mat_apply,
      coe_shortTorus (unitaryInvolution F 2 f) hσ _ _ _ (lowIdx_ne_rev _ _)
        (Units.mk0 c hc).ne_zero, SUExtras.tFun, dite_eq_left h, Units.val_mk0]
  · have hn : ¬ Even n := fun hn => hne ⟨h, hn⟩
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) (f := f) hF
    have hnorm : ∀ x, unitaryInvolution F 2 f x = x →
        ∃ a, unitaryInvolution F 2 f a * a = x := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨0, by simp⟩
      · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0
    obtain ⟨g, -, hg⟩ :=
      exists_heisGen_mem_rankOne hσ hζ hnorm h hn (Units.mk0 c hc)
    refine ⟨g, heisGen_mem_levelTorus h hn (Units.mk0 c hc) hg, ?_⟩
    rw [SUExtras.mat_apply, hg, Units.val_mk0, SUExtras.tFun, dite_eq_right h,
      ite_eq_right hn]

theorem exists_mem_levelTorus_tFun_even (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    (s : Fin (n / 2)) (h : ¬ s.val + 1 < n / 2) (hn : Even n) {c : F} (hc : c ≠ 0)
    (hσc : unitaryInvolution F 2 f c = c) :
    ∃ g ∈ levelTorus (unitaryInvolution F 2 f) s,
      SUExtras.mat (unitaryInvolution F 2 f) n g =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) (f := f) hF
  refine ⟨longTorus (unitaryInvolution F 2 f) (lowIdx_ne_rev s s) ζ hσc,
    longTorus_mem_levelTorus h hζ (Units.mk0 c hc) hσc, ?_⟩
  rw [SUExtras.mat_apply,
    coe_longTorus (unitaryInvolution F 2 f) (lowIdx_ne_rev s s) hζ hσc hc,
    SUExtras.tFun, dite_eq_right h, ite_eq_left hn]

theorem pow_eq_pow_mod_mul_unitaryInvolution_pow_div (φ₀ : F →+* k) (c : F) (e : ℕ) :
    φ₀ c ^ e = φ₀ c ^ (e % 2 ^ f) * φ₀ (unitaryInvolution F 2 f c) ^ (e / 2 ^ f) := by
  rw [unitaryInvolution_apply, map_pow, ← pow_mul, ← pow_add, Nat.mod_add_div]

omit [Field F] [Finite F] [CharP F 2] in
theorem two_pow_sub_one_add_mul_eq_natCard_sub_one (hF : Nat.card F = (2 ^ f) ^ 2) :
    (2 ^ f - 1) + 2 ^ f * (2 ^ f - 1) = Nat.card F - 1 := by
  rw [hF]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow 2 (2 ^ f) (by omega)
  zify [h1, h2]
  ring

omit [CharP F 2] in
theorem pow_natCard_sub_one_eq_one {c : F} (hc : c ≠ 0) :
    c ^ (Nat.card F - 1) = 1 := by
  let : Fintype F := Fintype.ofFinite F
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [Nat.card_eq_fintype_card]

theorem pow_full_mul_unitaryInvolution_pow_full (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k)
    {c : F} (hc : c ≠ 0) :
    φ₀ c ^ (2 ^ f - 1) * φ₀ (unitaryInvolution F 2 f c) ^ (2 ^ f - 1) = 1 := by
  have hσpow : φ₀ (unitaryInvolution F 2 f c) = φ₀ c ^ 2 ^ f := by
    rw [unitaryInvolution_apply, map_pow]
  rw [hσpow, ← pow_mul, ← pow_add, two_pow_sub_one_add_mul_eq_natCard_sub_one hF, ← map_pow,
    pow_natCard_sub_one_eq_one hc, map_one]

theorem sigma_eq_of_tFun_even {n : ℕ} {s : Fin (n / 2)} (h : ¬ s.val + 1 < n / 2)
    (hn : Even n) {x : SU (unitaryInvolution F 2 f) n} {c : F} (hc : c ≠ 0)
    (hx : SUExtras.mat (unitaryInvolution F 2 f) n x =
      diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c)) :
    unitaryInvolution F 2 f c = c := by
  rw [SUExtras.tFun, dite_eq_right h, ite_eq_left hn] at hx
  have hunit := unitary_of_coe_eq_diagonal hx (lowIdx s)
  rw [SUExtras.longTorusFun_self, longTorusFun_rev (lowIdx_ne_rev s s)] at hunit
  have := (mul_inv_eq_iff_eq_mul₀ hc).mp hunit
  simpa using this

theorem pow_full_eq_one_of_unitaryInvolution_eq (φ₀ : F →+* k) {c : F} (hc : c ≠ 0)
    (hσc : unitaryInvolution F 2 f c = c) :
    φ₀ c ^ (2 ^ f - 1) = 1 := by
  have hc2 : c ^ 2 ^ f = c := by
    rw [← unitaryInvolution_apply]
    exact hσc
  rw [← map_pow, pow_sub_one_eq_one_of_pow_eq (Nat.one_le_two_pow (n := f)) hc hc2, map_one]

theorem exists_node_exponent_ne (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (χ : SU (unitaryInvolution F 2 f) n → k) (hχ1 : χ 1 = 1)
    (hχ : ∀ a ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s,
      ∀ b ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, χ (a * b) = χ a * χ b)
    (s : Fin (n / 2)) (hne : ¬ (¬ s.val + 1 < n / 2 ∧ Even n)) :
    ∃ e : ℕ, e < Nat.card Fˣ ∧ ∀ (x : SU (unitaryInvolution F 2 f) n) (c : F), c ≠ 0 →
      SUExtras.mat (unitaryInvolution F 2 f) n x =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) → χ x = φ₀ c ^ e := by
  let g : Fˣ → SU (unitaryInvolution F 2 f) n :=
    fun u => Classical.choose (exists_mem_levelTorus_tFun hF s u.ne_zero hne)
  have hg_spec : ∀ u : Fˣ, SUExtras.mat (unitaryInvolution F 2 f) n (g u) =
      diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s (u : F)) :=
    fun u => (Classical.choose_spec (exists_mem_levelTorus_tFun hF s u.ne_zero hne)).2
  have hg_mem : ∀ u : Fˣ, g u ∈ levelTorus (unitaryInvolution F 2 f) s :=
    fun u => (Classical.choose_spec (exists_mem_levelTorus_tFun hF s u.ne_zero hne)).1
  let psi : Fˣ → k := fun u => χ (g u)
  have hmul : ∀ u v : Fˣ, psi (u * v) = psi u * psi v := by
    intro u v
    have h2 : SUExtras.mat (unitaryInvolution F 2 f) n (g u * g v) =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s ((u * v : Fˣ) : F)) := by
      rw [map_mul, hg_spec u, hg_spec v, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [Units.val_mul]
      exact (congrFun (SUExtras.tFun_mul (k := s) u.ne_zero v.ne_zero) i).symm
    have heq : g (u * v) = g u * g v :=
      SUExtras.mat_injective ((hg_spec (u * v)).trans h2.symm)
    show χ (g (u * v)) = χ (g u) * χ (g v)
    rw [heq]
    exact hχ _ (Subgroup.mem_iSup_of_mem s (hg_mem u)) _
      (Subgroup.mem_iSup_of_mem s (hg_mem v))
  have hone : psi 1 = 1 := by
    have h1 : g 1 = 1 := by
      refine SUExtras.mat_injective ?_
      rw [hg_spec 1, map_one, Units.val_one, SUExtras.tFun_one]
      exact diagonal_one
    show χ (g 1) = 1
    rw [h1, hχ1]
  let : Algebra F k := φ₀.toAlgebra
  obtain ⟨e, he, hpsi⟩ := exists_char_exponent psi hmul hone
  have he' : e < (2 ^ f) ^ 2 - 1 := by rwa [Nat.card_units, hF] at he
  refine ⟨e, ?_, fun x c hc hx => ?_⟩
  · rwa [Nat.card_units, hF]
  · have hspec : SUExtras.mat (unitaryInvolution F 2 f) n (g (Units.mk0 c hc)) =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) := by
      rw [hg_spec (Units.mk0 c hc), Units.val_mk0]
    have heq : x = g (Units.mk0 c hc) := SUExtras.mat_injective (hx.trans hspec.symm)
    show χ x = φ₀ c ^ e
    rw [heq]
    show psi (Units.mk0 c hc) = φ₀ c ^ e
    rw [hpsi (Units.mk0 c hc), RingHom.algebraMap_toAlgebra φ₀, Units.val_mk0]

theorem exists_node_exponent_even (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (χ : SU (unitaryInvolution F 2 f) n → k) (hχ1 : χ 1 = 1)
    (hχ : ∀ a ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s,
      ∀ b ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, χ (a * b) = χ a * χ b)
    (s : Fin (n / 2)) (h : ¬ s.val + 1 < n / 2) (hn : Even n) :
    ∃ e : ℕ, e < 2 ^ f - 1 ∧ ∀ (x : SU (unitaryInvolution F 2 f) n) (c : F), c ≠ 0 →
      SUExtras.mat (unitaryInvolution F 2 f) n x =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) → χ x = φ₀ c ^ e := by
  have hfix : ∀ u : (fixedSubfield F 2 f)ˣ,
      unitaryInvolution F 2 f (((u : fixedSubfield F 2 f)) : F) = ((u : fixedSubfield F 2 f) : F) :=
    fun u => mem_fixedSubfield.mp (u : fixedSubfield F 2 f).2
  have hne : ∀ u : (fixedSubfield F 2 f)ˣ, ((u : fixedSubfield F 2 f) : F) ≠ 0 :=
    fun u h0 => u.ne_zero (Subtype.ext h0)
  let g : (fixedSubfield F 2 f)ˣ → SU (unitaryInvolution F 2 f) n :=
    fun u => Classical.choose (exists_mem_levelTorus_tFun_even hF s h hn (hne u) (hfix u))
  have hg_spec : ∀ u : (fixedSubfield F 2 f)ˣ,
      SUExtras.mat (unitaryInvolution F 2 f) n (g u) =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s ((u : fixedSubfield F 2 f) : F)) :=
    fun u => (Classical.choose_spec
      (exists_mem_levelTorus_tFun_even hF s h hn (hne u) (hfix u))).2
  have hg_mem : ∀ u : (fixedSubfield F 2 f)ˣ, g u ∈ levelTorus (unitaryInvolution F 2 f) s :=
    fun u => (Classical.choose_spec
      (exists_mem_levelTorus_tFun_even hF s h hn (hne u) (hfix u))).1
  let psi : (fixedSubfield F 2 f)ˣ → k := fun u => χ (g u)
  have hmul : ∀ u v : (fixedSubfield F 2 f)ˣ, psi (u * v) = psi u * psi v := by
    intro u v
    have h2 : SUExtras.mat (unitaryInvolution F 2 f) n (g u * g v) =
        diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s
          (((u * v : (fixedSubfield F 2 f)ˣ) : fixedSubfield F 2 f) : F)) := by
      rw [map_mul, hg_spec u, hg_spec v, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [Units.val_mul]
      exact (congrFun (SUExtras.tFun_mul (k := s) (hne u) (hne v)) i).symm
    have heq : g (u * v) = g u * g v :=
      SUExtras.mat_injective ((hg_spec (u * v)).trans h2.symm)
    show χ (g (u * v)) = χ (g u) * χ (g v)
    rw [heq]
    exact hχ _ (Subgroup.mem_iSup_of_mem s (hg_mem u)) _
      (Subgroup.mem_iSup_of_mem s (hg_mem v))
  have hone : psi 1 = 1 := by
    have h1 : g 1 = 1 := by
      refine SUExtras.mat_injective ?_
      rw [hg_spec 1, map_one, Units.val_one, Subfield.coe_one, SUExtras.tFun_one]
      exact diagonal_one
    show χ (g 1) = 1
    rw [h1, hχ1]
  let phi : fixedSubfield F 2 f →+* k := φ₀.comp (fixedSubfield F 2 f).subtype
  let : Algebra (fixedSubfield F 2 f) k := phi.toAlgebra
  obtain ⟨e, he, hpsi⟩ := exists_char_exponent psi hmul hone
  have he' : e < 2 ^ f - 1 := by
    rw [Nat.card_units, card_fixedSubfield hF] at he
    exact he
  refine ⟨e, he', fun x c hc hx => ?_⟩
  have hσc : unitaryInvolution F 2 f c = c := sigma_eq_of_tFun_even h hn hc hx
  let u : (fixedSubfield F 2 f)ˣ :=
    Units.mk0 ⟨c, mem_fixedSubfield.mpr hσc⟩ (fun h0 => hc (congrArg Subtype.val h0))
  have hu : ((u : fixedSubfield F 2 f) : F) = c := by
    simp only [u, Units.val_mk0]
  have hspec : SUExtras.mat (unitaryInvolution F 2 f) n (g u) =
      diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) := by
    rw [hg_spec u, hu]
  have heq : x = g u := SUExtras.mat_injective (hx.trans hspec.symm)
  show χ x = φ₀ c ^ e
  rw [heq]
  show psi u = φ₀ c ^ e
  rw [hpsi u, RingHom.algebraMap_toAlgebra phi]
  show φ₀ (((u : fixedSubfield F 2 f)) : F) ^ e = φ₀ c ^ e
  rw [hu]

theorem exists_node_exponent (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (χ : SU (unitaryInvolution F 2 f) n → k) (hχ1 : χ 1 = 1)
    (hχ : ∀ a ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s,
      ∀ b ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, χ (a * b) = χ a * χ b)
    (s : Fin (n / 2)) :
    ∃ e : ℕ, e < Nat.card Fˣ ∧ (2 * (s : ℕ) + 2 = n → e < 2 ^ f - 1) ∧
      ∀ (x : SU (unitaryInvolution F 2 f) n) (c : F), c ≠ 0 →
        SUExtras.mat (unitaryInvolution F 2 f) n x =
          diagonal (SUExtras.tFun (unitaryInvolution F 2 f) s c) → χ x = φ₀ c ^ e := by
  by_cases hl : ¬ s.val + 1 < n / 2 ∧ Even n
  · obtain ⟨h, hn⟩ := hl
    obtain ⟨e, he, hform⟩ := exists_node_exponent_even hF φ₀ χ hχ1 hχ s h hn
    refine ⟨e, ?_, fun _ => he, hform⟩
    have he2 : e < (2 ^ f) ^ 2 - 1 := by
      have h1 : 2 ^ f - 1 ≤ (2 ^ f) ^ 2 - 1 := by
        have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have h3 : 2 ^ f ≤ (2 ^ f) ^ 2 := by nlinarith
        omega
      omega
    rwa [Nat.card_units, hF]
  · obtain ⟨e, he, hform⟩ := exists_node_exponent_ne hF φ₀ χ hχ1 hχ s hl
    refine ⟨e, he, fun hP => absurd ⟨?_, ⟨s + 1, by omega⟩⟩ hl, hform⟩
    intro hlt
    have hP' : 2 * ((s : ℕ) + 1) = n := by omega
    omega

theorem exists_eps_eq_chi (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (χ : SU (unitaryInvolution F 2 f) n → k) (hχ1 : χ 1 = 1)
    (hχ : ∀ a ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s,
      ∀ b ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, χ (a * b) = χ a * χ b)
    (full : Fin (n / 2) → Prop)
    (hfull : ∀ s, full s → ∀ t ∈ levelTorus (unitaryInvolution F 2 f) s, χ t = 1) :
    ∃ ε : Fin f → Finset (Fin n),
      (∀ h ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, χ h = chiEps φ₀ ε h) ∧
        ∀ s, IsFullNode ε s ↔ full s := by
  classical
  choose e he heP hform using fun s => exists_node_exponent hF φ₀ χ hχ1 hχ s
  have hf1 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero, one_pow] at hF
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h0
  let a : Fin (n / 2) → ℕ := fun s => if full s then 2 ^ f - 1 else e s % 2 ^ f
  let b : Fin (n / 2) → ℕ := fun s => if full s then 2 ^ f - 1 else e s / 2 ^ f
  have ha_lt : ∀ s, a s < 2 ^ f := by
    intro s
    by_cases hf : full s
    · rw [show a s = 2 ^ f - 1 from by simp [a, hf]]
      have := Nat.one_le_two_pow (n := f)
      omega
    · rw [show a s = e s % 2 ^ f from by simp [a, hf]]
      exact Nat.mod_lt _ (by positivity)
  have hb_lt : ∀ s, b s < 2 ^ f := by
    intro s
    by_cases hf : full s
    · rw [show b s = 2 ^ f - 1 from by simp [b, hf]]
      have := Nat.one_le_two_pow (n := f)
      omega
    · rw [show b s = e s / 2 ^ f from by simp [b, hf]]
      have hee : e s < (2 ^ f) ^ 2 := by
        have := he s
        rw [Nat.card_units, hF] at this
        omega
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0 : ℕ) < 2 ^ f), ← pow_two]
      exact hee
  let d : Fin n → ℕ := fun j =>
    if h0 : (j : ℕ) = 0 then 0
    else if hle : (j : ℕ) ≤ n / 2 then a ⟨(j : ℕ) - 1, by omega⟩
    else b ⟨n - 1 - (j : ℕ), by omega⟩
  have hd_lt : ∀ j, d j < 2 ^ f := by
    intro j
    simp only [d]
    split_ifs with h0 hle
    · exact Nat.one_le_two_pow (n := f)
    · exact ha_lt _
    · exact hb_lt _
  obtain ⟨ε, hε⟩ := exists_bDigit_eq d hd_lt
  have hdp : ∀ s : Fin (n / 2), bDigit ε (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = a s := by
    intro s
    rw [hε]
    simp only [d]
    rw [dif_neg (by omega : ¬ (s : ℕ) + 1 = 0),
      dif_pos (by omega : (s : ℕ) + 1 ≤ n / 2)]
    exact congrArg a (Fin.ext (by simp))
  have hdq : ∀ s : Fin (n / 2), ¬ (2 * (s : ℕ) + 2 = n) →
      bDigit ε (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = b s := by
    intro s hP
    rw [hε]
    simp only [d]
    rw [dif_neg (by omega : ¬ n - 1 - (s : ℕ) = 0),
      dif_neg (by omega : ¬ n - 1 - (s : ℕ) ≤ n / 2)]
    exact congrArg b (Fin.ext (by
      show n - 1 - (n - 1 - (s : ℕ)) = (s : ℕ)
      omega))
  have hnode : ∀ (s : Fin (n / 2)) (x : SU (unitaryInvolution F 2 f) n),
      x ∈ levelTorus (unitaryInvolution F 2 f) s → χ x = chiEps φ₀ ε x := by
    intro s x hx
    obtain ⟨c, hc⟩ := SUExtras.exists_tFun_of_mem_levelTorus hx
    rw [chiEps_of_tFun φ₀ ε s c.ne_zero hc]
    by_cases hP : 2 * (s : ℕ) + 2 = n
    · rw [if_pos hP, mul_one, hdp s]
      by_cases hf : full s
      · have hn : Even n := ⟨s + 1, by omega⟩
        have hlt : ¬ s.val + 1 < n / 2 := by omega
        have hσc : unitaryInvolution F 2 f (c : F) = c :=
          sigma_eq_of_tFun_even hlt hn c.ne_zero hc
        rw [show a s = 2 ^ f - 1 from by simp [a, hf],
          pow_full_eq_one_of_unitaryInvolution_eq φ₀ c.ne_zero hσc, hfull s hf x hx]
      · have he2 : e s < 2 ^ f := by
          have := heP s hP
          omega
        rw [show a s = e s % 2 ^ f from by simp [a, hf], Nat.mod_eq_of_lt he2]
        exact hform s x (c : F) c.ne_zero hc
    · rw [if_neg hP, hdp s, hdq s hP]
      by_cases hf : full s
      · rw [show a s = 2 ^ f - 1 from by simp [a, hf],
          show b s = 2 ^ f - 1 from by simp [b, hf],
          pow_full_mul_unitaryInvolution_pow_full hF φ₀ c.ne_zero, hfull s hf x hx]
      · rw [show a s = e s % 2 ^ f from by simp [a, hf],
          show b s = e s / 2 ^ f from by simp [b, hf],
          hform s x (c : F) c.ne_zero hc]
        exact pow_eq_pow_mod_mul_unitaryInvolution_pow_div φ₀ (c : F) (e s)
  have hH_le_diag : (⨆ s, levelTorus (unitaryInvolution F 2 f) s) ≤
      diagSubgroup (unitaryInvolution F 2 f) n :=
    iSup_le fun s => levelTorus_le_diagSubgroup s
  refine ⟨ε, ?_, fun s => ?_⟩
  · intro h hh
    exact (Subgroup.iSup_induction (levelTorus (unitaryInvolution F 2 f))
      (C := fun x => x ∈ (⨆ s, levelTorus (unitaryInvolution F 2 f) s) ∧
        χ x = chiEps φ₀ ε x) hh
      (fun s x hx => ⟨Subgroup.mem_iSup_of_mem s hx, hnode s x hx⟩)
      ⟨Subgroup.one_mem _, by rw [hχ1, chiEps_one]⟩
      (by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨mul_mem hxH hyH, ?_⟩
        rw [hχ x hxH y hyH, hx, hy,
          chiEps_mul φ₀ ε (hH_le_diag hxH) (hH_le_diag hyH)])).2
  · have hq_eq : ∀ s : Fin (n / 2), 2 * (s : ℕ) + 2 = n →
        (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = ⟨(s : ℕ) + 1, by omega⟩ := by
      intro s hP
      refine Fin.ext ?_
      show n - 1 - (s : ℕ) = (s : ℕ) + 1
      omega
    constructor
    · intro hεs
      by_contra hf
      have hpa : bDigit ε (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = 2 ^ f - 1 :=
        (bDigit_eq_iff ε _).mpr fun r => (hεs r).1
      rw [hdp s] at hpa
      by_cases hP : 2 * (s : ℕ) + 2 = n
      · rw [show a s = e s % 2 ^ f from by simp [a, hf]] at hpa
        have hlt := heP s hP
        have hle := Nat.mod_le (e s) (2 ^ f)
        omega
      · have hqa : bDigit ε (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = 2 ^ f - 1 :=
          (bDigit_eq_iff ε _).mpr fun r => (hεs r).2
        rw [hdq s hP] at hqa
        rw [show a s = e s % 2 ^ f from by simp [a, hf]] at hpa
        rw [show b s = e s / 2 ^ f from by simp [b, hf]] at hqa
        have hee : e s = (2 ^ f - 1) + 2 ^ f * (2 ^ f - 1) := by
          have h := Nat.mod_add_div (e s) (2 ^ f)
          rw [hpa, hqa] at h
          exact h.symm
        have hee' : e s = Nat.card Fˣ := by
          rw [hee, two_pow_sub_one_add_mul_eq_natCard_sub_one hF, Nat.card_units]
        have hs := he s
        rw [hee'] at hs
        exact lt_irrefl _ hs
    · intro hf r
      have ha : a s = 2 ^ f - 1 := by simp [a, hf]
      have hb : b s = 2 ^ f - 1 := by simp [b, hf]
      constructor
      · exact (bDigit_eq_iff ε _).mp (by rw [hdp s, ha]) r
      · by_cases hP : 2 * (s : ℕ) + 2 = n
        · rw [hq_eq s hP]
          exact (bDigit_eq_iff ε _).mp (by rw [hdp s, ha]) r
        · exact (bDigit_eq_iff ε _).mp (by rw [hdq s hP, hb]) r

end CFSG.LieType.Universal.Unitary
