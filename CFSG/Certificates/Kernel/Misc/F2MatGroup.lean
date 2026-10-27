
module

public import CFSG.Certificates.Kernel.Misc.WordPtsGroup

public section

namespace CFSG.KC.F2Mat

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.WordPts CFSG.KC.F2BfsRec CFSG.Quasithin.KGC31

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem bz_false : bz false = 0 := rfl

theorem bit_eq_testBit (X i : ℕ) : bit X i = X.testBit i := by
  apply Bool.eq_iff_iff.mpr
  rw [bit_eq_true_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem testBit_orN (f : ℕ → ℕ) (j : ℕ) :
    ∀ n, (orN n f).testBit j = true ↔ ∃ i < n, (f i).testBit j = true
  | 0 => by
    change (0 : ℕ).testBit j = true ↔ _
    simp
  | n + 1 => by
    change (f n ||| orN n f).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_orN f j n]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem testBit_low_shiftLeft (x r j : ℕ) :
    ((x &&& 1) <<< r).testBit j = (decide (j = r) && x.testBit 0) := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h]
    simp
  · rw [h, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [eq_comm]

theorem testBit_colF (d M i r : ℕ) (hr : r < d) :
    (CFSG.KC.WordPts.colF d M i).testBit r = M.testBit (d * r + i) := by
  apply Bool.eq_iff_iff.mpr
  change (orN d fun r => ((M >>> (d * r + i)) &&& 1) <<< r).testBit r = true ↔ _
  rw [testBit_orN]
  constructor
  · rintro ⟨r', _, h⟩
    rw [testBit_low_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, Nat.testBit_shiftRight] at h
    obtain ⟨rfl, h⟩ := h
    simpa using h
  · intro h
    refine ⟨r, hr, ?_⟩
    rw [testBit_low_shiftLeft, Nat.testBit_shiftRight]
    simpa using h

theorem matOfF_apply (d M : ℕ) (r c : Fin d) : matOfF d M r c = bz (M.testBit (d * r + c)) := by
  rw [← testBit_colF d M c r r.2]
  change ((((CFSG.KC.WordPts.colF d M c) / 2 ^ (r : ℕ)) % 2 : ℕ) : ZMod 2) = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (CFSG.KC.WordPts.colF d M c / 2 ^ (r : ℕ)) with h | h <;>
    simp [h, bz]

theorem testBit_rowF (d M i c : ℕ) :
    (rowF d M i).testBit c = (decide (c < d) && M.testBit (i * d + c)) := by
  change ((M >>> (i * d)) &&& ((1 <<< d) - 1)).testBit c = _
  rw [Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

theorem bz_vmGo (d M v c : ℕ) : ∀ m : ℕ,
    bz ((Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Bool.rec (motive := fun _ => ℕ) acc
      (Nat.xor (rowF d M k) acc) (bit v k)) m : ℕ).testBit c) =
      ∑ k ∈ Finset.range m, bz (v.testBit k) * bz ((rowF d M k).testBit c)
  | 0 => by simp [bz]
  | m + 1 => by
    rw [Finset.sum_range_succ, ← bz_vmGo d M v c m]
    change bz ((Bool.rec (motive := fun _ => ℕ) _ (Nat.xor (rowF d M m) _) (bit v m)).testBit c) = _
    rw [bit_eq_testBit]
    have h0 : bz false = 0 := rfl
    have h1 : bz true = 1 := rfl
    cases v.testBit m
    · rw [h0, zero_mul, add_zero]
    · change bz ((rowF d M m ^^^ _).testBit c) = _
      rw [Nat.testBit_xor, bz_xor, add_comm, h1, one_mul]

theorem bz_vmF (d M v c : ℕ) :
    bz ((vmF d M v).testBit c) =
      ∑ k ∈ Finset.range d, bz (v.testBit k) * bz ((rowF d M k).testBit c) :=
  bz_vmGo d M v c d

theorem testBit_vmF_ge {d M v c : ℕ} (hc : d ≤ c) : (vmF d M v).testBit c = false := by
  apply bz_inj
  rw [bz_vmF, bz_false]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [testBit_rowF]
  simp [bz, Nat.not_lt.mpr hc]

theorem testBit_mulF {d A B r c : ℕ} (hr : r < d) (hc : c < d) :
    (mulF d A B).testBit (d * r + c) = (vmF d B (rowF d A r)).testBit c := by
  apply Bool.eq_iff_iff.mpr
  change (CFSG.KC.Loop.strictN A fun A => CFSG.KC.Loop.strictN B fun B =>
    orN d fun i => (vmF d B (rowF d A i)) <<< (d * i)).testBit (d * r + c) = true ↔ _
  simp only [strictN_eq]
  rw [testBit_orN]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hge, h⟩ := h
    rcases lt_trichotomy i r with hir | rfl | hir
    · have h1 : d * (i + 1) ≤ d * r := Nat.mul_le_mul_left _ hir
      rw [Nat.mul_succ] at h1
      have h2 := testBit_vmF_ge (d := d) (M := B) (v := rowF d A i) (c := d * r + c - d * i)
        (by omega)
      rw [h2] at h
      exact absurd h Bool.false_ne_true
    · simpa using h
    · have h1 : d * (r + 1) ≤ d * i := Nat.mul_le_mul_left _ hir
      rw [Nat.mul_succ] at h1
      omega
  · intro h
    refine ⟨r, hr, ?_⟩
    rw [Nat.testBit_shiftLeft]
    simpa using h

theorem matOfF_mulF (d A B : ℕ) : matOfF d (mulF d A B) = matOfF d A * matOfF d B := by
  ext r c
  rw [matOfF_apply, Matrix.mul_apply, testBit_mulF r.2 c.2, bz_vmF,
    Finset.sum_range (fun k => bz ((rowF d A r).testBit k) * bz ((rowF d B k).testBit c))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [matOfF_apply, matOfF_apply, testBit_rowF, testBit_rowF]
  simp only [k.2, c.2, decide_true, Bool.true_and]
  rw [Nat.mul_comm (r : ℕ) d, Nat.mul_comm (k : ℕ) d]

theorem matOfF_idF (d : ℕ) : matOfF d (idF d) = 1 := by
  ext r c
  rw [matOfF_apply, Matrix.one_apply]
  have key : (idF d).testBit (d * r + c) = decide (r = c) := by
    apply Bool.eq_iff_iff.mpr
    change (orN d fun i => (1 <<< i) <<< (d * i)).testBit (d * r + c) = true ↔ _
    rw [testBit_orN, decide_eq_true_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.and_eq_true,
        decide_eq_true_iff, decide_eq_true_iff] at h
      obtain ⟨hge, h⟩ := h
      have hr := r.2
      have hc := c.2
      rcases lt_trichotomy i r with hir | hir | hir
      · have h1 : d * (i + 1) ≤ d * r := Nat.mul_le_mul_left _ hir
        rw [Nat.mul_succ] at h1
        omega
      · subst hir
        exact Fin.ext (by omega)
      · have h1 : d * (r + 1) ≤ d * i := Nat.mul_le_mul_left _ hir
        rw [Nat.mul_succ] at h1
        omega
    · rintro rfl
      refine ⟨r, r.2, ?_⟩
      rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp
  rw [key]
  by_cases h : r = c <;> simp [h, bz]

theorem matOfF_inj {d X Y : ℕ} (hX : X < 2 ^ (d * d)) (hY : Y < 2 ^ (d * d))
    (h : matOfF d X = matOfF d Y) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d * d
  · have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
    have hr : j / d < d := (Nat.div_lt_iff_lt_mul hd).mpr hj
    have hc : j % d < d := Nat.mod_lt _ hd
    have e : d * (j / d) + j % d = j := Nat.div_add_mod j d
    have := congrFun (congrFun h ⟨j / d, hr⟩) ⟨j % d, hc⟩
    rw [matOfF_apply, matOfF_apply] at this
    simp only [e] at this
    exact bz_inj this
  · have hle : 2 ^ (d * d) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hj)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY hle)]

theorem elemAt_lt (d w lb ng : ℕ) (CF : ℕ → ℕ) (k : ℕ) : elemAt d w lb ng CF k < 2 ^ (d * d) := by
  change recAt d w lb ng CF k &&& ((1 <<< (d * d)) - 1) < _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

variable {K : Type*} [Group K] {d w lb ng N : ℕ} {CF G : ℕ → ℕ}

theorem card_range_of_recK (ψ : K →* Matrix (Fin d) (Fin d) (ZMod 2)) (g : Fin ng → K)
    (hg : ∀ j : Fin ng, ψ (g j) = matOfF d (G j))
    (hgen : Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} = ⊤)
    (hN : 0 < N) (hNw : N < 2 ^ w) (hh : headK d w lb ng CF = true)
    (h : ∀ k < N, recK d w lb ng CF G N k = true) :
    Nat.card (Set.range ψ) = N := by
  obtain ⟨h0, hinj, hcl, hmin⟩ := recK_sound hN hNw hh h
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Matrix (Fin d) (Fin d) (ZMod 2),
      ∀ t, f t = matOfF d (elemAt d w lb ng CF t) := ⟨_, fun _ => rfl⟩
  have hxx : ∀ x : K, ψ x * ψ x⁻¹ = 1 := fun x => by rw [← map_mul, mul_inv_cancel, map_one]
  have hT : Set.range ψ = f '' Set.Iio N := by
    apply Set.Subset.antisymm
    · have key : ∀ x : K, ∀ X ∈ f '' Set.Iio N, X * ψ x ∈ f '' Set.Iio N := by
        intro x
        have hx : x ∈ Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} := by
          rw [hgen]
          exact Subgroup.mem_top x
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with ⟨j, rfl⟩ | h1
          · rintro _ ⟨t, ht, rfl⟩
            obtain ⟨t', ht', he⟩ := hcl t ht j j.2
            exact ⟨t', ht', by rw [hf, hf, he, matOfF_mulF, hg]⟩
          · intro X hX
            rwa [h1, mul_one]
        | one =>
          intro X hX
          rwa [map_one, mul_one]
        | mul x y _ _ ihx ihy =>
          intro X hX
          rw [map_mul, ← mul_assoc]
          exact ihy _ (ihx _ hX)
        | inv x _ ihx =>
          intro X hX
          have hfin : (f '' Set.Iio N).Finite := (Set.finite_Iio N).image f
          have hinjOn : Set.InjOn (fun Y => Y * ψ x) (f '' Set.Iio N) := fun Y _ Z _ hYZ => by
            have hYZ' : Y * ψ x = Z * ψ x := hYZ
            calc Y = Y * ψ x * ψ x⁻¹ := by rw [mul_assoc, hxx, mul_one]
              _ = Z * ψ x * ψ x⁻¹ := by rw [hYZ']
              _ = Z := by rw [mul_assoc, hxx, mul_one]
          obtain ⟨Y, hY, hYX⟩ :=
            ((hfin.injOn_iff_bijOn_of_mapsTo fun Y hY => ihx Y hY).mp hinjOn).surjOn hX
          have hYX' : Y * ψ x = X := hYX
          rw [← hYX', mul_assoc, hxx, mul_one]
          exact hY
      rintro _ ⟨x, rfl⟩
      have h1 : (1 : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ f '' Set.Iio N :=
        ⟨0, hN, by rw [hf, h0, matOfF_idF]⟩
      have := key x 1 h1
      rwa [one_mul] at this
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨x, hx⟩ := hmin (fun X => ∃ x, ψ x = matOfF d X) ⟨1, by rw [map_one, matOfF_idF]⟩
        (fun X j hj ⟨x, hx⟩ => ⟨x * g ⟨j, hj⟩, by rw [map_mul, hx, hg, matOfF_mulF]⟩) t ht
      exact ⟨x, by rw [hx, hf]⟩
  have hinjOn : Set.InjOn f (Set.Iio N) := by
    intro t ht t' ht' he
    rw [hf, hf] at he
    exact hinj t ht t' ht' (matOfF_inj (elemAt_lt _ _ _ _ _ _) (elemAt_lt _ _ _ _ _ _) he)
  rw [hT, Nat.card_image_of_injOn hinjOn, ← Finset.coe_range, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, Finset.card_range]

theorem mem_ker_toHomUnits {M : Type*} [Monoid M] (ψ : K →* M) (x : K) :
    x ∈ ψ.toHomUnits.ker ↔ ψ x = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]

theorem card_eq_card_ker_mul [Finite K] {M : Type*} [Monoid M] (ψ : K →* M) :
    Nat.card K = Nat.card ψ.toHomUnits.ker * Nat.card (Set.range ψ) := by
  rw [← Subgroup.card_mul_index ψ.toHomUnits.ker, Subgroup.index_ker]
  congr 1
  have e : Set.range ψ = Units.val '' (ψ.toHomUnits.range : Set Mˣ) := by
    rw [MonoidHom.coe_range, ← Set.range_comp]
    rfl
  rw [e, Nat.card_image_of_injective Units.val_injective]
  rfl

variable {Γ : Type*} [Group Γ] [Finite Γ] {k m : ℕ} {v : Fin k → Γ}

theorem eSub_le_eNorm (hv : EBasis v) : eSub hv ≤ eNorm hv := Subgroup.le_normalizer

theorem eMat_eq_one_of_mem (hv : EBasis v) {x : Γ} (hx : x ∈ eSub hv) :
    eMat hv ⟨x, eSub_le_eNorm hv hx⟩ = 1 :=
  (eMat_eq_one_iff hv _).mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv y x hy hx)

theorem card_closure_of_recK (hv : EBasis v) (a : Fin m → Γ) (ha : ∀ j, a j ∈ eNorm hv)
    (hcent : ∀ x ∈ Subgroup.closure (Set.range a ∪ Set.range v),
      x ∈ Subgroup.centralizer (eSub hv : Set Γ) → x ∈ eSub hv)
    (hG : ∀ j, eMat hv ⟨a j, ha j⟩ = matOfF k (G j))
    (hN : 0 < N) (hNw : N < 2 ^ w) (hh : headK k w lb m CF = true)
    (h : ∀ t < N, recK k w lb m CF G N t = true) :
    Nat.card (Subgroup.closure (Set.range a ∪ Set.range v)) = 2 ^ k * N := by
  set H := Subgroup.closure (Set.range a ∪ Set.range v) with hH
  have hvH : ∀ i, v i ∈ H := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hHn : H ≤ eNorm hv := (Subgroup.closure_le _).mpr fun x hx => by
    rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
    · exact ha j
    · exact eSub_le_eNorm hv (mem_eSub hv i)
  let ψ : H →* Matrix (Fin k) (Fin k) (ZMod 2) :=
    (Units.coeHom _).comp ((eGL hv).comp (Subgroup.inclusion hHn))
  have hψ : ∀ x : H, ψ x = eMat hv (Subgroup.inclusion hHn x) := fun _ => rfl
  let g : Fin m → H := fun j => ⟨a j, Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)⟩
  have hgen : Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range a ∪ Set.range v)]
    refine Subgroup.closure_mono fun x hx => ?_
    rcases hx with ⟨j, hj⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨j, Subtype.ext hj⟩
    · refine Or.inr ?_
      rw [hψ]
      have hx : (x : Γ) ∈ eSub hv := hi ▸ mem_eSub hv i
      exact eMat_eq_one_of_mem hv hx
  have hrange := card_range_of_recK ψ g (fun j => hG j) hgen hN hNw hh h
  have hker : ψ.toHomUnits.ker.map H.subtype = eSub hv := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_ker_toHomUnits, hψ, eMat_eq_one_iff] at hx
      exact hcent x x.2 hx
    · intro hy
      have hyH : y ∈ H := by
        rw [eSub_eq_closure hv] at hy
        refine (Subgroup.closure_le H).mpr ?_ hy
        rintro _ ⟨i, rfl⟩
        exact hvH i
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      rw [mem_ker_toHomUnits, hψ]
      exact eMat_eq_one_of_mem hv hy
  rw [card_eq_card_ker_mul ψ, ← Subgroup.card_map_of_injective (Subgroup.subtype_injective H),
    hker, card_eSub hv, hrange]

theorem closure_preimage_eq_top {H : Subgroup Γ} {S : Set Γ} (hH : H = Subgroup.closure S) :
    Subgroup.closure ((↑) ⁻¹' S : Set H) = ⊤ := by
  subst hH
  exact Subgroup.closure_closure_coe_preimage

end CFSG.KC.F2Mat

end
