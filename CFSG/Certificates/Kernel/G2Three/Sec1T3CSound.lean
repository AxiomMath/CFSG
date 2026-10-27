module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3ASound
public import CFSG.Certificates.Kernel.G2Three.Sec1T3Corr
public import Certificates.Data.Kernel.G2Three.Sec1T3D

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop Subgroup CFSG.Open
open scoped commutatorElement

theorem recLorL_bit (g : ℕ → ℕ) (k : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor (g t) acc) n).testBit k = true ↔
      ∃ t < n, (g t).testBit k = true
  | 0 => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | n + 1 => by
    change (g n ||| Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor (g t) acc) n).testBit
      k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, recLorL_bit g k n]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inr ⟨t, ht, h⟩
      · exact Or.inl h

theorem shift6_add (h l : ℕ) : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
  change h <<< 6 + l = _
  rw [Nat.shiftLeft_eq]
  ring

theorem nIf_blt_testBit (m i k : ℕ) (v : ℕ) :
    (nIf(Nat.blt i m, v, 0)).testBit k = true ↔ i < m ∧ v.testBit k = true := by
  cases hb : Nat.blt i m
  · have : ¬ i < m := fun h => by rw [← Nat.blt_eq] at h; rw [h] at hb; exact absurd hb (by decide)
    change (0 : ℕ).testBit k = true ↔ _
    simp [this]
  · have : i < m := by rw [← Nat.blt_eq]; exact hb
    change v.testBit k = true ↔ _
    simp [this]

theorem orBelow_bit {m hi : ℕ} (f : ℕ → ℕ) (k : ℕ) (hm : m ≤ 64 * hi) :
    (orBelow m hi f).testBit k = true ↔ ∃ i < m, (f i).testBit k = true := by
  unfold orBelow
  rw [recLorL_bit (fun h => Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.lor ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) k hi]
  simp only [recLorL_bit, shift6_add, nIf_blt_testBit]
  constructor
  · rintro ⟨h, -, l, -, h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨i, hi', h⟩
    refine ⟨i / 64, by omega, i % 64, Nat.mod_lt _ (by decide), ?_⟩
    have e : 64 * (i / 64) + i % 64 = i := Nat.div_add_mod i 64
    rw [e]
    exact ⟨hi', h⟩

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  cases hb : Nat.ble a b
  · have : ¬ a ≤ b := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; exact absurd hb (by decide)
    change a = _
    omega
  · have : a ≤ b := Nat.le_of_ble_eq_true hb
    change b = _
    omega

theorem recMax_spec (g : ℕ → ℕ) : ∀ n,
    (∀ t < n, g t ≤ Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (g t) acc) n) ∧
      (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (g t) acc) n = 0 ∨
        ∃ t < n, g t = Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (g t) acc) n)
  | 0 => ⟨fun t ht => absurd ht (Nat.not_lt_zero t), Or.inl rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := recMax_spec g n
    change (∀ t < n + 1, g t ≤ maxN (g n) (Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => maxN (g t) acc) n)) ∧ (maxN (g n) (Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => maxN (g t) acc) n) = 0 ∨ ∃ t < n + 1, g t = maxN (g n)
        (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (g t) acc) n))
    generalize Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (g t) acc) n = r at h1 h2 ⊢
    rw [maxN_eq]
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact (h1 t ht).trans (le_max_right _ _)
      · exact le_max_left _ _
    · rcases le_total (g n) r with h | h
      · rw [max_eq_right h]
        rcases h2 with h2 | ⟨t, ht, h2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨t, Nat.lt_succ_of_lt ht, h2⟩
      · rw [max_eq_left h]
        exact Or.inr ⟨n, Nat.lt_succ_self n, rfl⟩

theorem nIf_blt_eq (m i v : ℕ) : nIf(Nat.blt i m, v, 0) = if i < m then v else 0 := by
  cases hb : Nat.blt i m
  · have : ¬ i < m := fun h => by rw [← Nat.blt_eq] at h; rw [h] at hb; exact absurd hb (by decide)
    simp only [this, if_false]
  · have : i < m := by rw [← Nat.blt_eq]; exact hb
    simp only [this, if_true]

theorem maxBelow_spec {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    (∀ i < m, f i ≤ maxBelow m hi f) ∧ (maxBelow m hi f = 0 ∨ ∃ i < m, f i = maxBelow m hi f) := by
  unfold maxBelow
  set inner : ℕ → ℕ := fun h => Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      maxN ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64
  obtain ⟨o1, o2⟩ := recMax_spec inner hi
  generalize Nat.rec (motive := fun _ => Nat) 0 (fun t acc => maxN (inner t) acc) hi = M at o1 o2 ⊢
  have hin : ∀ h, (∀ l < 64, (if 64 * h + l < m then f (64 * h + l) else 0) ≤ inner h) ∧
      (inner h = 0 ∨ ∃ l < 64, (if 64 * h + l < m then f (64 * h + l) else 0) = inner h) := by
    intro h
    have := recMax_spec (fun l => (fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l))
      64
    simp only [shift6_add, nIf_blt_eq] at this
    have e : inner h = Nat.rec (motive := fun _ => Nat) 0
        (fun t acc => maxN (if 64 * h + t < m then f (64 * h + t) else 0) acc) 64 := by
      simp only [inner, shift6_add, nIf_blt_eq]
    rw [e]
    exact this
  refine ⟨fun i hi' => ?_, ?_⟩
  · have := (hin (i / 64)).1 (i % 64) (Nat.mod_lt _ (by decide))
    rw [Nat.div_add_mod, if_pos hi'] at this
    exact this.trans (o1 _ (by omega))
  · rcases o2 with o2 | ⟨h, hh, o2⟩
    · exact Or.inl o2
    · rcases (hin h).2 with h3 | ⟨l, hl, h3⟩
      · exact Or.inl (o2 ▸ h3)
      · by_cases hc : 64 * h + l < m
        · rw [if_pos hc] at h3
          exact Or.inr ⟨_, hc, h3.trans o2⟩
        · rw [if_neg hc] at h3
          exact Or.inl (o2 ▸ h3.symm)

theorem allBelow_iff {m hi : ℕ} {f : ℕ → Bool} (hm : m ≤ 64 * hi) :
    allBelow m hi f = true ↔ ∀ i < m, f i = true := by
  refine ⟨fun h => allBelow_spec h hm, fun h => ?_⟩
  refine (recAnd_iff _ hi).2 fun j _ => ?_
  refine (recAnd_iff (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft j 6) l)) 64).2 fun l _ => ?_
  dsimp only
  rw [shift6_add]
  cases hb : Nat.blt (64 * j + l) m
  · rfl
  · exact h _ (by rw [← Nat.blt_eq]; exact hb)

variable {G : Type} [Group G] {elt : ℕ → G}

theorem subM_eq (X Y : ℕ) : subM X Y = true ↔ Nat.land X Y = X := by
  unfold subM
  rw [Nat.beq_eq]

theorem testBit_lt128 {x : ℕ} (hx : x < 2 ^ 128) {i : ℕ} (hi : 128 ≤ i) : x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem subM_iff_subset (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {X Y : ℕ}
    (hX : X < 2 ^ 128) : subM X Y = true ↔ mset elt X ⊆ mset elt Y := by
  rw [subM_eq]
  refine ⟨subset_of_land, fun h => Nat.eq_of_testBit_eq fun i => ?_⟩
  change (X &&& Y).testBit i = X.testBit i
  rw [Nat.testBit_and]
  by_cases hi : i < 128
  · cases hb : X.testBit i
    · rfl
    · have : elt i ∈ mset elt Y := h ⟨i, hi, by rw [hasB_eq]; exact hb, rfl⟩
      rw [mem_mset_iff hinj hi, hasB_eq] at this
      rw [this]
      rfl
  · rw [testBit_lt128 hX (by omega)]
    rfl

theorem lt128_of_testBit {x : ℕ} (h : ∀ i, x.testBit i = true → i < 128) : x < 2 ^ 128 :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    cases hb : x.testBit i
    · rfl
    · exact absurd (h i hb) (by omega)

theorem entL_lt (L k : ℕ) : entL L k < 2 ^ 128 := by
  have h : entL L k ≤ M128 := Nat.and_le_right
  have e : M128 = 2 ^ 128 - 1 := by decide
  omega

theorem entL_eq (L k : ℕ) : entL L k = latM L k := rfl

theorem genAt_lt (g t : ℕ) : genAt g t < 128 := fld127_lt _ _

theorem commE_lt (P C V x y : ℕ) : commE P C V x y < 128 := atR_lt _ _

theorem imgR_lt (r H : ℕ) : imgR r H < 2 ^ 128 :=
  lt128_of_testBit fun i hi => by
    obtain ⟨j, -, -, rfl⟩ := (recMask_bit (hasB H) (atR r) i 128).1 hi
    exact atR_lt _ _

theorem mset_eq_iff_of_lt (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {X Y : ℕ}
    (hX : X < 2 ^ 128) (hY : Y < 2 ^ 128) : mset elt X = mset elt Y ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h1 := (subM_iff_subset hinj hX).2 h.le
  have h2 := (subM_iff_subset hinj hY).2 h.ge
  rw [subM_eq] at h1 h2
  calc X = Nat.land X Y := h1.symm
    _ = Nat.land Y X := Nat.land_comm X Y
    _ = Y := h2

theorem RepM.finite {m : ℕ} {X : Set G} (h : RepM elt m X) : X.Finite :=
  ((Set.finite_Iio 128).image elt).subset fun x hx => by
    obtain ⟨i, hi, rfl⟩ := h.2 x hx
    exact ⟨i, hi, rfl⟩

theorem RepM.eq {m : ℕ} {X Y : Set G} (hX : RepM elt m X) (hY : RepM elt m Y) : X = Y := by
  rw [hX.eq_mset, hY.eq_mset]

section Tables

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

omit hR in
theorem recLorIfB_bit (B : ℕ) (c : ℕ → Bool) (F : ℕ → ℕ) (k : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) B (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n).testBit
      k = true ↔ B.testBit k = true ∨ ∃ b < n, c b = true ∧ (F b).testBit k = true
  | 0 => by
    change B.testBit k = true ↔ _
    simp
  | n + 1 => by
    have ih := recLorIfB_bit B c F k n
    change (nIf(c n, Nat.lor (Nat.rec (motive := fun _ => Nat) B
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n) (F n),
      Nat.rec (motive := fun _ => Nat) B
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n)).testBit k = true ↔ _
    generalize Nat.rec (motive := fun _ => Nat) B
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n = R at ih ⊢
    cases hc : c n
    · change R.testBit k = true ↔ _
      rw [ih]
      constructor
      · rintro (h | ⟨b, hb, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨b, Nat.lt_succ_of_lt hb, h1, h2⟩
      · rintro (h | ⟨b, hb, h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · exact Or.inr ⟨b, hb, h1, h2⟩
          · rw [hc] at h1
            exact absurd h1 (by decide)
    · change (R ||| F n).testBit k = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih]
      constructor
      · rintro ((h | ⟨b, hb, h1, h2⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨b, Nat.lt_succ_of_lt hb, h1, h2⟩
        · exact Or.inr ⟨n, Nat.lt_succ_self n, hc, h⟩
      · rintro (h | ⟨b, hb, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · exact Or.inl (Or.inr ⟨b, hb, h1, h2⟩)
          · exact Or.inr h2

theorem stepM_mset (m M : ℕ) :
    mset elt (stepM C m M) = mset elt M ∪ {y | ∃ g ∈ mset elt m, ∃ x ∈ mset elt M, x * g = y} := by
  have e : stepM C m M = Nat.rec (motive := fun _ => Nat) M (fun g acc =>
      nIf(hasB m g, Nat.lor acc (imgR (rowT C g) M), acc)) 128 := by
    simp only [stepM, strictN_eq]
  ext y
  constructor
  · rintro ⟨k, hk, hb, rfl⟩
    rw [e, hasB_eq, recLorIfB_bit] at hb
    rcases hb with hb | ⟨g, hg, hm, hb⟩
    · exact Or.inl ⟨k, hk, by rw [hasB_eq]; exact hb, rfl⟩
    · have h1 : elt k ∈ mset elt (imgR (rowT C g) M) := ⟨k, hk, by rw [hasB_eq]; exact hb, rfl⟩
      rw [mset_imgR_right hR hg] at h1
      obtain ⟨x, hx, he⟩ := h1
      exact Or.inr ⟨elt g, ⟨g, hg, hm, rfl⟩, x, hx, he⟩
  · rintro (⟨k, hk, hb, rfl⟩ | ⟨_, ⟨g, hg, hm, rfl⟩, x, hx, rfl⟩)
    · refine ⟨k, hk, ?_, rfl⟩
      rw [e, hasB_eq, recLorIfB_bit]
      rw [hasB_eq] at hb
      exact Or.inl hb
    · have h1 : x * elt g ∈ mset elt (imgR (rowT C g) M) := by
        rw [mset_imgR_right hR hg]
        exact ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hb, he⟩ := h1
      refine ⟨k, hk, ?_, he⟩
      rw [e, hasB_eq, recLorIfB_bit]
      rw [hasB_eq] at hb
      exact Or.inr ⟨g, hg, hm, hb⟩

omit hR in
theorem closM_succ (m R : ℕ) : closM C m (R + 1) = stepM C m (closM C m R) := by
  change strictN (closM C m R) (stepM C m) = _
  rw [strictN_eq]

theorem closM_closure {m R : ℕ} (hc : closMOK C m R = true) :
    mset elt (closM C m R) = (Subgroup.closure (mset elt m) : Set G) := by
  set S : Set G := mset elt m
  have hsub : ∀ R, mset elt (closM C m R) ⊆ (Subgroup.closure S : Set G) := by
    intro R
    induction R with
    | zero =>
      change mset elt 1 ⊆ _
      rw [mset_one hR.one]
      rintro _ rfl
      exact (Subgroup.closure S).one_mem
    | succ R ih =>
      rw [closM_succ, stepM_mset hR]
      rintro y (hy | ⟨g, hg, x, hx, rfl⟩)
      · exact ih hy
      · exact (Subgroup.closure S).mul_mem (ih hx) (Subgroup.subset_closure hg)
  have hone : ∀ R, (1 : G) ∈ mset elt (closM C m R) := by
    intro R
    induction R with
    | zero =>
      change (1 : G) ∈ mset elt 1
      rw [mset_one hR.one]
      rfl
    | succ R ih =>
      rw [closM_succ, stepM_mset hR]
      exact Or.inl ih
  set T := mset elt (closM C m R) with hT
  have hfix : stepM C m (closM C m R) = closM C m R := by
    change strictB (closM C m R) (fun M => Nat.beq (stepM C m M) M) = true at hc
    rw [strictB_eq] at hc
    exact Nat.eq_of_beq_eq_true hc
  have hcl : ∀ x ∈ T, ∀ g ∈ S, x * g ∈ T := by
    intro x hx g hg
    have := stepM_mset hR m (closM C m R)
    rw [hfix] at this
    rw [hT, this]
    exact Or.inr ⟨g, hg, x, hx, rfl⟩
  have hfin : T.Finite := by
    refine ((Set.finite_Iio 128).image elt).subset ?_
    rintro _ ⟨i, hi, -, rfl⟩
    exact ⟨i, hi, rfl⟩
  have hinv : ∀ x ∈ T, ∀ g ∈ S, x * g⁻¹ ∈ T := by
    intro x hx g hg
    have himg : (fun y => y * g) '' T = T := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
      · rintro _ ⟨y, hy, rfl⟩
        exact hcl y hy g hg
      · rw [Set.InjOn.ncard_image fun a _ b _ h => mul_right_cancel h]
    rw [← himg] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  refine Set.Subset.antisymm (hsub R) fun x hx => ?_
  refine Subgroup.closure_induction_right (p := fun x _ => x ∈ T) (hone R) ?_ ?_ hx
  · rintro x - g hg hxT
    exact hcl x hxT g hg
  · rintro x - g hg hxT
    exact hinv x hxT g hg

theorem joinK_sound {U R T : ℕ} (h : joinK C U R T = true) :
    mset elt T = (Subgroup.closure (mset elt U) : Set G) := by
  change strictB U (fun U => bAnd(closMOK C U R, Nat.beq (closM C U R) T)) = true at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  rw [← Nat.eq_of_beq_eq_true h.2]
  exact closM_closure hR h.1

end Tables

@[expose] def LatOK (elt : ℕ → G) (L m : ℕ) (G₀ : Subgroup G) : Prop :=
  (∀ k < m, ∃ K : Subgroup G, K ≤ G₀ ∧ RepM elt (entL L k) (K : Set G)) ∧
    ∀ K ≤ G₀, ∃ k < m, RepM elt (entL L k) (K : Set G)

theorem LatOK.le {L m : ℕ} {G₀ : Subgroup G} (hL : LatOK elt L m G₀) {k : ℕ} (hk : k < m)
    {K : Subgroup G} (hK : RepM elt (entL L k) (K : Set G)) : K ≤ G₀ := by
  obtain ⟨K', hK'G, hK'⟩ := hL.1 k hk
  have : K = K' := SetLike.coe_injective (hK.eq hK')
  exact this ▸ hK'G

@[expose] def rgSet (elt : ℕ → G) (RG k : ℕ) : Set G :=
  {x | ∃ t < Nat.land (rgAt RG k) 7, elt (genAt (rgAt RG k) t) = x}

theorem rgK_spec {L RG m : ℕ} (h : rgK L RG m = true) (hm : m ≤ 448) :
    ∀ k < m, Nat.land (rgAt RG k) 7 ≤ 4 ∧ gensIn (entL L k) (rgAt RG k) = true := by
  intro k hk
  have := allBelow_spec h (by omega) k hk
  dsimp only at this
  rw [bAnd_eq, Bool.and_eq_true] at this
  exact ⟨Nat.le_of_ble_eq_true this.1, this.2⟩

theorem outB_spec {H g : ℕ} (h : outB H g = true) :
    ∃ t < Nat.land g 7, hasB H (genAt g t) = false := by
  obtain ⟨t, ht, h⟩ := recOr_of (fun t => Bool.not' (hasB H (genAt g t))) _ h
  rw [not'_eq, Bool.not_eq_true'] at h
  exact ⟨t, ht, h⟩

theorem rgAllK_spec {L OR RG m lo w : ℕ} (h : rgAllK L OR RG m lo w = true) (hm : m ≤ 448)
    (hw : w ≤ 448) : ∀ l < w, ∀ k < m, 2 * ordAt OR k = ordAt OR (lo + l) →
      subM (entL L k) (entL L (lo + l)) = true → outB (entL L k) (rgAt RG (lo + l)) = true := by
  intro l hl k hk ho hs
  have := allBelow_spec h (by omega) l hl
  dsimp only at this
  simp only [strictB_eq] at this
  have h2 := allBelow_spec this (by omega) k hk
  have e : Nat.add lo l = lo + l := rfl
  rw [e] at h2
  have hb : Nat.beq (Nat.mul 2 (ordAt OR k)) (ordAt OR (lo + l)) = true := by
    rw [Nat.beq_eq]
    exact ho
  rw [hb] at h2
  change bIf(subM (entL L k) (entL L (lo + l)), outB (entL L k) (rgAt RG (lo + l)), true) = true
    at h2
  rw [hs] at h2
  exact h2

theorem rg_closure (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {L OR RG m : ℕ}
    {G₀ : Subgroup G} (hL : LatOK elt L m G₀) (h2 : IsPGroup 2 G₀) (hm : m ≤ 448)
    (hrg : rgK L RG m = true) (ho : ∀ k < m, pop (entL L k) = ordAt OR k)
    (hall : ∀ k < m, ∀ h < m, 2 * ordAt OR h = ordAt OR k →
      subM (entL L h) (entL L k) = true → outB (entL L h) (rgAt RG k) = true)
    {k : ℕ} (hk : k < m) {K : Subgroup G} (hK : RepM elt (entL L k) (K : Set G)) :
    Nat.land (rgAt RG k) 7 ≤ 4 ∧ K = Subgroup.closure (rgSet elt RG k) := by
  obtain ⟨h4, hgi⟩ := rgK_spec hrg hm k hk
  refine ⟨h4, ?_⟩
  have hTK : Subgroup.closure (rgSet elt RG k) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact (hK.1 _ (fld127_lt _ _)).1 (gensIn_spec hgi t ht)
  by_contra hne
  have hKG := hL.le hk hK
  have : Finite K := hK.finite.to_subtype
  obtain ⟨M, hTM, hMK, hc⟩ := exists_index_two_ge (h2.to_le hKG) hTK (Ne.symm hne)
  obtain ⟨h, hh, hM⟩ := hL.2 M (hMK.trans hKG)
  have hcard : ∀ {j : ℕ} {J : Subgroup G}, RepM elt (entL L j) (J : Set G) → j < m →
      Nat.card J = ordAt OR j := fun hJ hj => by
    rw [← ho _ hj, ← pop_sound hinj hJ]
    rfl
  have hsub : subM (entL L h) (entL L k) = true := by
    rw [subM_iff_subset hinj (entL_lt L h), ← hM.eq_mset, ← hK.eq_mset]
    exact hMK
  obtain ⟨t, ht, hb⟩ := outB_spec (hall k hk h hh (by rw [← hcard hM hh, ← hcard hK hk, hc]) hsub)
  have hmem : elt (genAt (rgAt RG k) t) ∈ M := hTM (Subgroup.subset_closure ⟨t, ht, rfl⟩)
  rw [← SetLike.mem_coe, ← (hM.1 _ (genAt_lt _ _))] at hmem
  rw [hmem] at hb
  exact absurd hb (by decide)

theorem orBelow_single_bit {m : ℕ} (c : ℕ → Bool) (k : ℕ) (hm : m ≤ 448) :
    (orBelow m 7 fun i => nIf(c i, Nat.shiftLeft 1 i, 0)).testBit k = true ↔
      k < m ∧ c k = true := by
  rw [orBelow_bit _ _ (by omega)]
  have key : ∀ i, (nIf(c i, Nat.shiftLeft 1 i, 0)).testBit k = true ↔ c i = true ∧ i = k := by
    intro i
    cases hc : c i
    · change (0 : ℕ).testBit k = true ↔ _
      simp
    · change (1 <<< i).testBit k = true ↔ _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
      simp
  simp only [key]
  constructor
  · rintro ⟨i, hi, hc, rfl⟩
    exact ⟨hi, hc⟩
  · rintro ⟨hk, hc⟩
    exact ⟨k, hk, hc, rfl⟩

theorem secC_bit {Q L m X N : ℕ} (hm : m ≤ 448) (k : ℕ) :
    hasB (secC Q L m X N) k = true ↔ k < m ∧ subM N (entL L k) = true ∧
      subM (entL L k) X = true ∧ subM (imgR Q (entL L k)) N = true := by
  rw [hasB_eq]
  simp only [secC, strictN_eq]
  rw [orBelow_single_bit _ k hm]
  simp only [bAnd_eq, Bool.and_eq_true]

theorem maxIdx_bit {L Cm m : ℕ} (hm : m ≤ 448) (k : ℕ) :
    hasB (maxIdx L Cm m) k = true ↔ k < m ∧ hasB Cm k = true ∧
      ∀ k' < m, hasB Cm k' = true → subM (entL L k) (entL L k') = true → entL L k = entL L k' := by
  rw [hasB_eq]
  have e : maxIdx L Cm m = orBelow m 7 fun k => nIf(bAnd(hasB Cm k, allBelow m 7 fun k' =>
      bIf(hasB Cm k', bIf(subM (entL L k) (entL L k'), Nat.beq (entL L k) (entL L k'), true),
        true)), Nat.shiftLeft 1 k, 0) := by
    simp only [maxIdx, strictN_eq, strictB_eq]
    congr 1
    funext k
    cases hasB Cm k <;> rfl
  rw [e, orBelow_single_bit _ k hm, bAnd_eq, Bool.and_eq_true, allBelow_iff (by omega)]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun k' _ => ?_
  cases h1 : hasB Cm k'
  · simp
  · cases h2 : subM (entL L k) (entL L k')
    · simp
    · simp only [true_implies]
      rw [Nat.beq_eq]

section Sections

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem sq_subM_iff {K N : ℕ} :
    subM (imgR Q K) N = true ↔ ∀ x ∈ mset elt K, x * x ∈ mset elt N := by
  rw [subM_iff_subset hR.inj (imgR_lt _ _), mset_imgR Q K (fun x => x * x) fun i hi => hR.sq hi]
  exact Set.image_subset_iff

theorem secC_sound {L m Xm Nm : ℕ} (hm : m ≤ 448) (hNb : Nm < 2 ^ 128) (k : ℕ) :
    hasB (secC Q L m Xm Nm) k = true ↔ k < m ∧ mset elt Nm ⊆ mset elt (entL L k) ∧
      mset elt (entL L k) ⊆ mset elt Xm ∧ ∀ x ∈ mset elt (entL L k), x * x ∈ mset elt Nm := by
  rw [secC_bit hm, subM_iff_subset hR.inj hNb, subM_iff_subset hR.inj (entL_lt _ _),
    sq_subM_iff hR]

@[expose] def IsMaxSq (N X K : Subgroup G) : Prop :=
  N ≤ K ∧ K ≤ X ∧ (∀ k ∈ K, k * k ∈ N) ∧
    ∀ K' : Subgroup G, K ≤ K' → K' ≤ X → (∀ k ∈ K', k * k ∈ N) → K' = K

theorem maxIdx_secC {L m Xm Nm : ℕ} {G₀ X N : Subgroup G} (hL : LatOK elt L m G₀) (hm : m ≤ 448)
    (hXG : X ≤ G₀) (hX : RepM elt Xm (X : Set G)) (hN : RepM elt Nm (N : Set G))
    (hNb : Nm < 2 ^ 128) (k : ℕ) :
    hasB (maxIdx L (secC Q L m Xm Nm) m) k = true ↔
      k < m ∧ ∃ K : Subgroup G, RepM elt (entL L k) (K : Set G) ∧ IsMaxSq N X K := by
  rw [maxIdx_bit hm]
  have hsec : ∀ {j : ℕ} {J : Subgroup G}, j < m → RepM elt (entL L j) (J : Set G) →
      (hasB (secC Q L m Xm Nm) j = true ↔ N ≤ J ∧ J ≤ X ∧ ∀ x ∈ J, x * x ∈ N) := by
    intro j J hj hJ
    rw [secC_sound hR hm hNb, ← hJ.eq_mset, ← hX.eq_mset, ← hN.eq_mset]
    simp only [hj, true_and, SetLike.coe_subset_coe, SetLike.mem_coe]
  have hsubJ : ∀ {j j' : ℕ} {J J' : Subgroup G}, RepM elt (entL L j) (J : Set G) →
      RepM elt (entL L j') (J' : Set G) → (subM (entL L j) (entL L j') = true ↔ J ≤ J') := by
    intro j j' J J' hJ hJ'
    rw [subM_iff_subset hR.inj (entL_lt _ _), ← hJ.eq_mset, ← hJ'.eq_mset, SetLike.coe_subset_coe]
  have heqJ : ∀ {j j' : ℕ} {J J' : Subgroup G}, RepM elt (entL L j) (J : Set G) →
      RepM elt (entL L j') (J' : Set G) → (entL L j = entL L j' ↔ J = J') := by
    intro j j' J J' hJ hJ'
    rw [← mset_eq_iff_of_lt hR.inj (entL_lt _ _) (entL_lt _ _), ← hJ.eq_mset, ← hJ'.eq_mset,
      SetLike.coe_set_eq]
  constructor
  · rintro ⟨hk, hc, hmax⟩
    obtain ⟨K, -, hK⟩ := hL.1 k hk
    obtain ⟨h1, h2, h3⟩ := (hsec hk hK).1 hc
    refine ⟨hk, K, hK, h1, h2, h3, fun K' hKK' hK'X hsq => ?_⟩
    obtain ⟨k', hk', hK'⟩ := hL.2 K' (hK'X.trans hXG)
    exact ((heqJ hK hK').1 (hmax k' hk' ((hsec hk' hK').2 ⟨h1.trans hKK', hK'X, hsq⟩)
      ((hsubJ hK hK').2 hKK'))).symm
  · rintro ⟨hk, K, hK, h1, h2, h3, hmax⟩
    refine ⟨hk, (hsec hk hK).2 ⟨h1, h2, h3⟩, fun k' hk' hc hs => ?_⟩
    obtain ⟨K', -, hK'⟩ := hL.1 k' hk'
    obtain ⟨-, h2', h3'⟩ := (hsec hk' hK').1 hc
    exact (heqJ hK hK').2 (hmax K' ((hsubJ hK hK').1 hs) h2' h3').symm

theorem eaMaxK_sound {L m Xm Nm k1 k2 : ℕ} {G₀ X N K₁ K₂ : Subgroup G} (hL : LatOK elt L m G₀)
    (hm : m ≤ 448) (hXG : X ≤ G₀) (hX : RepM elt Xm (X : Set G)) (hN : RepM elt Nm (N : Set G))
    (hNb : Nm < 2 ^ 128) (h : eaMaxK Q L m Xm Nm k1 k2 = true)
    (hK₁ : RepM elt (entL L k1) (K₁ : Set G)) (hK₂ : RepM elt (entL L k2) (K₂ : Set G)) :
    ∀ K : Subgroup G, IsMaxSq N X K ↔ K = K₁ ∨ K = K₂ := by
  change bAnd(Bool.not' (Nat.beq k1 k2), Nat.beq (maxIdx L (secC Q L m Xm Nm) m)
    (Nat.lor (Nat.shiftLeft 1 k1) (Nat.shiftLeft 1 k2))) = true at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hbit : ∀ j, hasB (maxIdx L (secC Q L m Xm Nm) m) j = true ↔ j = k1 ∨ j = k2 := by
    intro j
    rw [Nat.eq_of_beq_eq_true h.2, hasB_eq]
    change (1 <<< k1 ||| 1 <<< k2).testBit j = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact or_congr eq_comm eq_comm
  have hms := maxIdx_secC hR hL hm hXG hX hN hNb
  intro K
  constructor
  · intro hK
    obtain ⟨k, hk, hKk⟩ := hL.2 K (hK.2.1.trans hXG)
    rcases (hbit k).1 ((hms k).2 ⟨hk, K, hKk, hK⟩) with rfl | rfl
    · exact Or.inl (SetLike.coe_injective (hKk.eq hK₁))
    · exact Or.inr (SetLike.coe_injective (hKk.eq hK₂))
  · rintro (rfl | rfl)
    · obtain ⟨-, K, hK, hmax⟩ := (hms k1).1 ((hbit k1).2 (Or.inl rfl))
      rwa [← SetLike.coe_injective (hK.eq hK₁)]
    · obtain ⟨-, K, hK, hmax⟩ := (hms k2).1 ((hbit k2).2 (Or.inr rfl))
      rwa [← SetLike.coe_injective (hK.eq hK₂)]

theorem eaMaxK_quo {L m Xm Nm k1 k2 : ℕ} {G₀ X N K₁ K₂ : Subgroup G} [(N.subgroupOf X).Normal]
    (hL : LatOK elt L m G₀) (hm : m ≤ 448) (hXG : X ≤ G₀) (hNX : N ≤ X)
    (hX : RepM elt Xm (X : Set G)) (hN : RepM elt Nm (N : Set G)) (hNb : Nm < 2 ^ 128)
    (h : eaMaxK Q L m Xm Nm k1 k2 = true)
    (hK₁ : RepM elt (entL L k1) (K₁ : Set G)) (hK₂ : RepM elt (entL L k2) (K₂ : Set G)) :
    {Y : Subgroup (X ⧸ N.subgroupOf X) | Y ≤ ⊤ ∧ IsElemAbelian 2 Y ∧
      ∀ Y' : Subgroup (X ⧸ N.subgroupOf X), Y ≤ Y' → Y' ≤ ⊤ → IsElemAbelian 2 Y' → Y' = Y} =
      {quo X N K₁, quo X N K₂} :=
  maxElemAbelian_quo hNX (eaMaxK_sound hR hL hm hXG hX hN hNb h hK₁ hK₂)

theorem abR_spec {g N : ℕ} (h : abR P C V g N = true) :
    ∀ t < Nat.land g 7, ∀ u < Nat.land g 7,
      ⁅elt (genAt g t), elt (genAt g u)⁆ ∈ mset elt N := by
  intro t ht u hu
  unfold abR at h
  have h1 := (recAnd_iff _ _).1 h t ht
  have h2 := (recAnd_iff _ _).1 h1 u hu
  rw [← commE_elt hR (genAt_lt _ _) (genAt_lt _ _)]
  exact ⟨_, atR_lt _ _, h2, rfl⟩

omit hR in
theorem jC_bit {L RG m X N : ℕ} (hm : m ≤ 448) (k : ℕ) :
    hasB (jC P C V L RG m X N) k = true ↔ k < m ∧ subM N (entL L k) = true ∧
      subM (entL L k) X = true ∧ abR P C V (rgAt RG k) N = true := by
  rw [hasB_eq]
  simp only [jC, strictN_eq]
  rw [orBelow_single_bit _ k hm]
  simp only [bAnd_eq, Bool.and_eq_true]

theorem jC_sound {L RG m Xm Nm : ℕ} {G₀ X N : Subgroup G} (hL : LatOK elt L m G₀) (hm : m ≤ 448)
    (hgen : ∀ k < m, ∀ K : Subgroup G, RepM elt (entL L k) (K : Set G) →
      K = Subgroup.closure (rgSet elt RG k))
    (hX : RepM elt Xm (X : Set G)) (hN : RepM elt Nm (N : Set G)) (hNb : Nm < 2 ^ 128)
    (hn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {k : ℕ} (hk : k < m) {K : Subgroup G}
    (hK : RepM elt (entL L k) (K : Set G)) :
    hasB (jC P C V L RG m Xm Nm) k = true ↔ N ≤ K ∧ K ≤ X ∧ ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N := by
  rw [jC_bit hm, subM_iff_subset hR.inj hNb, subM_iff_subset hR.inj (entL_lt _ _), ← hK.eq_mset,
    ← hX.eq_mset, ← hN.eq_mset, SetLike.coe_subset_coe, SetLike.coe_subset_coe]
  simp only [hk, true_and]
  refine and_congr_right fun hNK => and_congr_right fun hKX => ?_
  have hKc := hgen k hk K hK
  constructor
  · intro h
    have hs := abR_spec hR h
    rw [← hN.eq_mset] at hs
    rw [hKc]
    refine comm_mem_of_gens (fun x hx n hn' => hn x (hKX (by rw [hKc]; exact hx)) n hn') ?_
    rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
    exact hs t ht u hu
  · intro h
    unfold abR
    refine (recAnd_iff _ _).2 fun t ht => (recAnd_iff _ _).2 fun u hu => ?_
    have hgK : ∀ t < Nat.land (rgAt RG k) 7, elt (genAt (rgAt RG k) t) ∈ K := fun t ht => by
      rw [hKc]
      exact Subgroup.subset_closure ⟨t, ht, rfl⟩
    have := h _ (hgK t ht) _ (hgK u hu)
    rw [← commE_elt hR (genAt_lt _ _) (genAt_lt _ _), ← SetLike.mem_coe, hN.eq_mset,
      mem_mset_iff hR.inj (commE_lt _ _ _ _ _)] at this
    exact this

omit hR in
theorem recCount_eq (c : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(c i, Nat.succ acc, acc)) n =
      ((Finset.range n).filter fun i => c i = true).card
  | 0 => rfl
  | n + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert]
    change nIf(c n, Nat.succ (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.succ acc, acc)) n), Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.succ acc, acc)) n) = _
    rw [recCount_eq c n]
    cases hb : c n
    · rfl
    · simp only [if_true]
      rw [Finset.card_insert_of_notMem (by simp)]

theorem omN_eq (K N : ℕ) :
    omN Q K N = {x | x ∈ mset elt K ∧ x * x ∈ mset elt N}.ncard := by
  have e : {x | x ∈ mset elt K ∧ x * x ∈ mset elt N} =
      elt '' ↑((Finset.range 128).filter fun i => bAnd(hasB K i, hasB N (atR Q i)) = true) := by
    ext g
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Set.mem_image, bAnd_eq,
      Bool.and_eq_true]
    constructor
    · rintro ⟨⟨i, hi, hb, rfl⟩, hsq⟩
      refine ⟨i, ⟨hi, hb, ?_⟩, rfl⟩
      rw [← hR.sq hi, mem_mset_iff hR.inj (atR_lt _ _)] at hsq
      exact hsq
    · rintro ⟨i, ⟨hi, hb, hq⟩, rfl⟩
      refine ⟨⟨i, hi, hb, rfl⟩, ?_⟩
      rw [← hR.sq hi]
      exact ⟨_, atR_lt _ _, hq, rfl⟩
  rw [e, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  · exact recCount_eq (fun i => bAnd(hasB K i, hasB N (atR Q i))) 128
  · intro i hi j hj he
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
    exact hR.inj i hi.1 j hj.1 he

end Sections

theorem unionMax_sound {L m Cm : ℕ} (hm : m ≤ 448) (𝒜 : Set (Subgroup G)) (f : Subgroup G → ℕ)
    (s : ℕ → ℕ) (hCm : ∀ k < m, hasB Cm k = true ↔ ∃ K ∈ 𝒜, RepM elt (entL L k) (K : Set G))
    (hcomp : ∀ K ∈ 𝒜, ∃ k < m, RepM elt (entL L k) (K : Set G))
    (hs : ∀ k < m, ∀ K : Subgroup G, RepM elt (entL L k) (K : Set G) → s (entL L k) = f K) :
    mset elt (orBelow m 7 fun k => nIf(hasB Cm k, nIf(Nat.beq (s (entL L k))
        (maxBelow m 7 fun k => nIf(hasB Cm k, s (entL L k), 0)), entL L k, 0), 0)) =
      ⋃ A ∈ {A | A ∈ 𝒜 ∧ ∀ B ∈ 𝒜, f B ≤ f A}, (A : Set G) := by
  obtain ⟨mx1, mx2⟩ := maxBelow_spec (fun k => nIf(hasB Cm k, s (entL L k), 0)) (m := m) (hi := 7)
    (by omega)
  set mx := maxBelow m 7 fun k => nIf(hasB Cm k, s (entL L k), 0) with hmx
  have hval : ∀ k, nIf(hasB Cm k, s (entL L k), 0) = if hasB Cm k = true then s (entL L k) else 0 := by
    intro k
    cases hasB Cm k <;> rfl
  have hbest : ∀ k < m, ∀ A ∈ 𝒜, RepM elt (entL L k) (A : Set G) →
      (s (entL L k) = mx ↔ ∀ B ∈ 𝒜, f B ≤ f A) := by
    intro k hk A hA hAk
    have hAc : hasB Cm k = true := (hCm k hk).2 ⟨A, hA, hAk⟩
    have hsA := hs k hk A hAk
    constructor
    · intro he B hB
      obtain ⟨j, hj, hBj⟩ := hcomp B hB
      have := mx1 j hj
      rw [hval, if_pos ((hCm j hj).2 ⟨B, hB, hBj⟩), hs j hj B hBj] at this
      omega
    · intro hmax
      have h1 := mx1 k hk
      rw [hval, if_pos hAc] at h1
      rcases mx2 with h0 | ⟨j, hj, hjv⟩
      · omega
      · rw [hval] at hjv
        by_cases hjc : hasB Cm j = true
        · rw [if_pos hjc] at hjv
          obtain ⟨B, hB, hBj⟩ := (hCm j hj).1 hjc
          have := hmax B hB
          rw [← hs j hj B hBj, hjv, ← hsA] at this
          omega
        · rw [if_neg hjc] at hjv
          omega
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    rw [hasB_eq, orBelow_bit _ _ (by omega)] at hb
    obtain ⟨k, hk, hb⟩ := hb
    cases hc : hasB Cm k
    · rw [hc] at hb
      change (0 : ℕ).testBit i = true at hb
      exact absurd hb (by simp)
    · rw [hc] at hb
      change (nIf(Nat.beq (s (entL L k)) mx, entL L k, 0)).testBit i = true at hb
      cases he : Nat.beq (s (entL L k)) mx
      · rw [he] at hb
        change (0 : ℕ).testBit i = true at hb
        exact absurd hb (by simp)
      · rw [he] at hb
        obtain ⟨A, hA, hAk⟩ := (hCm k hk).1 hc
        refine ⟨A, ⟨hA, (hbest k hk A hA hAk).1 (Nat.eq_of_beq_eq_true he)⟩, ?_⟩
        exact (hAk.1 i hi).1 (by rw [hasB_eq]; exact hb)
  · rintro ⟨A, ⟨hA, hmax⟩, hx⟩
    obtain ⟨k, hk, hAk⟩ := hcomp A hA
    obtain ⟨i, hi, rfl⟩ := hAk.2 x hx
    refine ⟨i, hi, ?_, rfl⟩
    rw [hasB_eq, orBelow_bit _ _ (by omega)]
    refine ⟨k, hk, ?_⟩
    have he : Nat.beq (s (entL L k)) mx = true := by
      rw [Nat.beq_eq]
      exact (hbest k hk A hA hAk).2 hmax
    rw [(hCm k hk).2 ⟨A, hA, hAk⟩]
    change (nIf(Nat.beq (s (entL L k)) mx, entL L k, 0)).testBit i = true
    rw [he, ← hasB_eq]
    exact (hAk.1 i hi).2 hx

section Unions

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem j0U_sound {L RG m Xm : ℕ} {G₀ X : Subgroup G} (hL : LatOK elt L m G₀) (hm : m ≤ 448)
    (hgen : ∀ k < m, ∀ K : Subgroup G, RepM elt (entL L k) (K : Set G) →
      K = Subgroup.closure (rgSet elt RG k))
    (hXG : X ≤ G₀) (hX : RepM elt Xm (X : Set G)) :
    mset elt (j0U P C V L RG m Xm) = ⋃ A ∈ {A : Subgroup G | (A ≤ X ∧ IsMulCommutative A) ∧
      ∀ B ∈ {B : Subgroup G | B ≤ X ∧ IsMulCommutative B}, Nat.card B ≤ Nat.card A},
        (A : Set G) := by
  have hinj := hR.inj
  have h1 : RepM elt 1 ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_bot, ← mset_one hR.one]
    exact repM_mset hinj 1
  have hab : ∀ K : Subgroup G, (∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ (⊥ : Subgroup G)) ↔
      IsMulCommutative K := by
    intro K
    constructor
    · intro h
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have := h a a.2 b b.2
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · intro h a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mul_comm_of_mem_isMulCommutative K ha hb
  have hCm : ∀ k < m, hasB (jC P C V L RG m Xm 1) k = true ↔
      ∃ K ∈ {B : Subgroup G | B ≤ X ∧ IsMulCommutative B}, RepM elt (entL L k) (K : Set G) := by
    intro k hk
    obtain ⟨K, -, hK⟩ := hL.1 k hk
    rw [jC_sound hR hL hm hgen hX h1 (by decide) (fun x _ n hn => by
      rw [Subgroup.mem_bot] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]) hk hK, hab]
    constructor
    · rintro ⟨-, hKX, hc⟩
      exact ⟨K, ⟨hKX, hc⟩, hK⟩
    · rintro ⟨K', ⟨hKX, hc⟩, hK'⟩
      rw [SetLike.coe_injective (hK.eq hK')]
      exact ⟨bot_le, hKX, hc⟩
  have hu := unionMax_sound hm {B : Subgroup G | B ≤ X ∧ IsMulCommutative B} (fun A => Nat.card A)
    pop hCm (fun K hK => hL.2 K (hK.1.trans hXG)) (fun k _ K hK => by
      rw [← pop_sound hinj hK]
      rfl)
  have e : j0U P C V L RG m Xm = orBelow m 7 fun k => nIf(hasB (jC P C V L RG m Xm 1) k,
      nIf(Nat.beq (pop (entL L k)) (maxBelow m 7 fun k => nIf(hasB (jC P C V L RG m Xm 1) k,
        pop (entL L k), 0)), entL L k, 0), 0) := by
    simp only [j0U, strictN_eq]
  rw [e, hu]
  rfl

theorem jrU_sound {L RG m Xm Nm : ℕ} {G₀ X N : Subgroup G} (hL : LatOK elt L m G₀) (hm : m ≤ 448)
    (hgen : ∀ k < m, ∀ K : Subgroup G, RepM elt (entL L k) (K : Set G) →
      K = Subgroup.closure (rgSet elt RG k))
    (hXG : X ≤ G₀) (hX : RepM elt Xm (X : Set G)) (hN : RepM elt Nm (N : Set G))
    (hNb : Nm < 2 ^ 128) (hn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    mset elt (jrU P C V Q L RG m Xm Nm) = ⋃ A ∈ {A : Subgroup G |
      (N ≤ A ∧ A ≤ X ∧ ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ N) ∧
      ∀ B ∈ {B : Subgroup G | N ≤ B ∧ B ≤ X ∧ ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ N},
        {x | x ∈ B ∧ x * x ∈ N}.ncard ≤ {x | x ∈ A ∧ x * x ∈ N}.ncard}, (A : Set G) := by
  have hCm : ∀ k < m, hasB (jC P C V L RG m Xm Nm) k = true ↔
      ∃ K ∈ {B : Subgroup G | N ≤ B ∧ B ≤ X ∧ ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ N},
        RepM elt (entL L k) (K : Set G) := by
    intro k hk
    obtain ⟨K, -, hK⟩ := hL.1 k hk
    rw [jC_sound hR hL hm hgen hX hN hNb hn hk hK]
    constructor
    · intro h
      exact ⟨K, h, hK⟩
    · rintro ⟨K', h, hK'⟩
      rwa [SetLike.coe_injective (hK.eq hK')]
  have hu := unionMax_sound hm _ (fun A => {x | x ∈ A ∧ x * x ∈ N}.ncard) (fun K => omN Q K Nm) hCm
    (fun K hK => hL.2 K (hK.2.1.trans hXG)) (fun k _ K hK => by
      rw [omN_eq hR, ← hK.eq_mset, ← hN.eq_mset]
      rfl)
  have e : jrU P C V Q L RG m Xm Nm = orBelow m 7 fun k => nIf(hasB (jC P C V L RG m Xm Nm) k,
      nIf(Nat.beq (omN Q (entL L k) Nm) (maxBelow m 7 fun k => nIf(hasB (jC P C V L RG m Xm Nm) k,
        omN Q (entL L k) Nm, 0)), entL L k, 0), 0) := by
    simp only [jrU, strictN_eq]
  rw [e, hu]
  rfl

end Unions

end CFSG.KC.G2Three.Sec1T3
