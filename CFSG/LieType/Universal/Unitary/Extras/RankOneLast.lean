module

public import CFSG.LieType.Universal.Unitary.Extras.RankOne
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem sum_eq_three {M : Type*} [AddCommMonoid M] {f : Fin n → M} (x y z : Fin n) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (h : ∀ s, s ≠ x → s ≠ y → s ≠ z → f s = 0) :
    ∑ s, f s = f x + f y + f z := by
  rw [← Finset.sum_subset (Finset.subset_univ {x, y, z}) (fun s _ hs => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    exact h s hs.1 hs.2.1 hs.2.2)]
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz, add_assoc]

theorem sum_eq_two {M : Type*} [AddCommMonoid M] {f : Fin n → M} (x y : Fin n) (hxy : x ≠ y)
    (h : ∀ s, s ≠ x → s ≠ y → f s = 0) : ∑ s, f s = f x + f y :=
  Finset.sum_eq_add x y hxy (fun s _ hs => h s hs.1 hs.2) (by simp) (by simp)

@[expose] def midIdx (n : ℕ) (hn : ¬Even n) : Fin n :=
  ⟨n / 2, by rw [Nat.not_even_iff_odd] at hn; obtain ⟨r, hr⟩ := hn; omega⟩

theorem rev_midIdx (hn : ¬Even n) : Fin.rev (midIdx n hn) = midIdx n hn := by
  apply Fin.ext
  simp only [Fin.val_rev, midIdx]
  rw [Nat.not_even_iff_odd] at hn
  obtain ⟨r, hr⟩ := hn
  omega

section Last

variable {hσ : ∀ c, σ (σ c) = c} {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2)

@[expose] def blkLast (k : Fin (n / 2)) (s : Fin n) : ℕ :=
  if s = lowIdx k ∨ s = Fin.rev (lowIdx k) ∨ Fin.rev s = s then 1 else 0

omit [Field F] in
theorem blkLast_eq_one_iff (s : Fin n) :
    blkLast k s = 1 ↔ s = lowIdx k ∨ s = Fin.rev (lowIdx k) ∨ Fin.rev s = s := by
  unfold blkLast
  split_ifs with h <;> simp [h]

omit [Field F] in
theorem blkLast_eq_zero_iff (s : Fin n) :
    blkLast k s = 0 ↔ ¬(s = lowIdx k ∨ s = Fin.rev (lowIdx k) ∨ Fin.rev s = s) := by
  unfold blkLast
  split_ifs with h <;> simp [h]

omit [Field F] in
theorem blkLast_eq_one_of_ne_zero {s : Fin n} (h : blkLast k s ≠ 0) : blkLast k s = 1 := by
  unfold blkLast at h ⊢
  split_ifs at h ⊢ <;> simp_all

omit [Field F] in
theorem blkLast_mem {s : Fin n} (hs : s = lowIdx k ∨ s = Fin.rev (lowIdx k) ∨ Fin.rev s = s) :
    blkLast k s = 1 :=
  (blkLast_eq_one_iff s).mpr hs

include hk in
theorem toStd_last_even (he : Even n) : toStd n (Pi.single k 1) = 2 • weight n (lowIdx k) := by
  rw [toStd_single_of_even he hk, weight_lowIdx]

include hk in
theorem toStd_last_odd (he : ¬Even n) : toStd n (Pi.single k 1) = weight n (lowIdx k) := by
  rw [toStd_single_of_odd he hk, weight_lowIdx]

include hk in
theorem toStd_neg_last_even (he : Even n) :
    toStd n (-Pi.single k 1) = 2 • weight n (Fin.rev (lowIdx k)) := by
  rw [toStd_neg, toStd_last_even hk he, weight_rev', smul_neg]

include hk in
theorem toStd_neg_last_odd (he : ¬Even n) :
    toStd n (-Pi.single k 1) = weight n (Fin.rev (lowIdx k)) := by
  rw [toStd_neg, toStd_last_odd hk he, weight_rev']

omit [Field F] in
theorem ne_rev_of_last {i : Fin n} (hi : i = lowIdx k ∨ i = Fin.rev (lowIdx k)) :
    i ≠ Fin.rev i := by
  rcases hi with rfl | rfl
  · exact lowIdx_ne_rev k k
  · exact rev_ne_rev_rev (lowIdx_ne_rev k k)

omit [Field F] in
theorem blkLast_pair {i : Fin n} (hi : i = lowIdx k ∨ i = Fin.rev (lowIdx k)) :
    blkLast k i = 1 ∧ blkLast k (Fin.rev i) = 1 := by
  rcases hi with rfl | rfl
  · exact ⟨blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))⟩
  · rw [Fin.rev_rev]
    exact ⟨blkLast_mem (Or.inr (Or.inl rfl)), blkLast_mem (Or.inl rfl)⟩

theorem blkLast_of_two_smul_weight {i : Fin n} (hi : i = lowIdx k ∨ i = Fin.rev (lowIdx k))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = 2 • weight n i) (a b : Fin n)
    (hab : weight n a - weight n b = toStd n γ ∨ weight n a - weight n b = 2 • toStd n γ) :
    blkLast k a = blkLast k b ∧ blkLast k a ≠ 0 := by
  have hii := ne_rev_of_last hi
  rcases hab with hab | hab
  · rw [hγ] at hab
    obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hii hab
    obtain ⟨h1, h2⟩ := blkLast_pair hi
    rw [h1, h2]
    exact ⟨rfl, one_ne_zero⟩
  · exfalso
    rw [hγ, smul_smul] at hab
    exact weight_ne_zero hii (eq_zero_of_weight_sub_eq_nsmul hab (by norm_num))

theorem blkLast_of_weight {i m : Fin n} (hi : i = lowIdx k ∨ i = Fin.rev (lowIdx k))
    (hm : Fin.rev m = m) {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = weight n i) (a b : Fin n)
    (hab : weight n a - weight n b = toStd n γ ∨ weight n a - weight n b = 2 • toStd n γ) :
    blkLast k a = blkLast k b ∧ blkLast k a ≠ 0 := by
  have hii := ne_rev_of_last hi
  obtain ⟨h1, h2⟩ := blkLast_pair hi
  have hm1 : blkLast k m = 1 := blkLast_mem (Or.inr (Or.inr hm))
  rcases hab with hab | hab
  · rw [hγ] at hab
    rcases eq_of_weight_sub_eq_weight hii hm hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, hm1]
      exact ⟨rfl, one_ne_zero⟩
    · rw [h2, hm1]
      exact ⟨rfl, one_ne_zero⟩
  · rw [hγ] at hab
    obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hii hab
    rw [h1, h2]
    exact ⟨rfl, one_ne_zero⟩

include hk in
theorem isBlk_last_of_mem {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    IsBlk (blkLast k) (mat σ n g) := by
  refine rankOne_induction hσ hg (C := fun g => IsBlk (blkLast k) (mat σ n g)) ?_ ?_ ?_ ?_
  · intro x hx
    by_cases he : Even n
    · exact isBlk_of_mem_rootGroup hσ
        (blkLast_of_two_smul_weight (Or.inl rfl) (toStd_last_even hk he)) hx
    · exact isBlk_of_mem_rootGroup hσ
        (blkLast_of_weight (Or.inl rfl) (rev_midIdx he) (toStd_last_odd hk he)) hx
  · intro y hy
    by_cases he : Even n
    · exact isBlk_of_mem_rootGroup hσ
        (blkLast_of_two_smul_weight (Or.inr rfl) (toStd_neg_last_even hk he)) hy
    · exact isBlk_of_mem_rootGroup hσ
        (blkLast_of_weight (Or.inr rfl) (rev_midIdx he) (toStd_neg_last_odd hk he)) hy
  · rw [map_one]
    exact isBlk_one _
  · intro x y hx hy
    rw [map_mul]
    exact hx.mul hy

include hk in
theorem levelWeyl_col_last {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (r : Fin n) :
    mat σ n (levelWeyl hσ ζ k) r (lowIdx k) =
      if r = Fin.rev (lowIdx k) then -(ζ : F)⁻¹ else 0 := by
  rw [mat_apply, coe_levelWeyl hσ hζ, SpecialLinear.signedPerm_apply]
  have hπ : levelPerm k (lowIdx k) = Fin.rev (lowIdx (n := n) k) := by
    rw [levelPerm, dite_eq_right hk, Equiv.swap_apply_left]
  have hs : levelSign σ (ζ : F) k (lowIdx k) = -(ζ : F)⁻¹ := by
    rw [levelSign, dite_eq_right hk, longSign, ite_eq_left rfl]
  rw [hπ, hs]

include hk in
theorem col_last_of_mem {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) {r : Fin n}
    (hr : ¬(r = lowIdx k ∨ r = Fin.rev (lowIdx k) ∨ Fin.rev r = r)) :
    mat σ n g r (lowIdx k) = 0 := by
  have hr' : r ≠ lowIdx k := fun h => hr (Or.inl h)
  rw [isBlk_last_of_mem hk hg r (lowIdx k) (fun h => ?_), one_apply_ne hr']
  rw [(blkLast_eq_zero_iff r).mpr hr] at h
  exact h.2 rfl

section Even

variable (he : Even n)

include he in
omit [Field F] in
theorem rev_ne_self_of_even (s : Fin n) : Fin.rev s ≠ s := by
  intro h
  obtain ⟨r, hr⟩ := he
  have h1 := congrArg Fin.val h
  have := s.isLt
  simp only [Fin.val_rev] at h1
  omega

include he in
omit [Field F] in
theorem blkLast_hblk_even (c : Fin n) (hc : blkLast k c = blkLast k (lowIdx k)) :
    c = lowIdx k ∨ c = Fin.rev (lowIdx k) := by
  rw [blkLast_mem (Or.inl rfl), blkLast_eq_one_iff] at hc
  rcases hc with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (rev_ne_self_of_even he c)

include hk he in
theorem toBlock_last_of_mem {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    IsBlk (blkLast k) (mat σ n g) ∧
      (toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g)).det = 1 := by
  have hpp := lowIdx_ne_rev (n := n) k k
  refine rankOne_induction hσ hg (C := fun g => IsBlk (blkLast k) (mat σ n g) ∧
    (toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g)).det = 1) ?_ ?_ ?_ ?_
  · intro x hx
    have hne : toStd n (Pi.single k 1) ≠ 0 := by
      rw [toStd_last_even hk he]
      intro h
      exact weight_ne_zero hpp (two_nsmul_injective' (by rw [h, smul_zero]))
    refine ⟨isBlk_of_mem_rootGroup hσ
      (blkLast_of_two_smul_weight (Or.inl rfl) (toStd_last_even hk he)) hx, ?_⟩
    rw [toBlock, Matrix.det_fin_two_of, mat_apply_self_of_mem_rootGroup hσ hne hx,
      mat_apply_self_of_mem_rootGroup hσ hne hx,
      mat_apply_of_weight_sub_eq_neg hσ hne hx (a := Fin.rev (lowIdx k)) (b := lowIdx k)
        (by rw [toStd_last_even hk he, weight_rev']; abel)]
    ring
  · intro y hy
    have hne : toStd n (-Pi.single k 1) ≠ 0 := by
      rw [toStd_neg_last_even hk he]
      intro h
      exact weight_ne_zero (rev_ne_rev_rev hpp) (two_nsmul_injective' (by rw [h, smul_zero]))
    refine ⟨isBlk_of_mem_rootGroup hσ
      (blkLast_of_two_smul_weight (Or.inr rfl) (toStd_neg_last_even hk he)) hy, ?_⟩
    rw [toBlock, Matrix.det_fin_two_of, mat_apply_self_of_mem_rootGroup hσ hne hy,
      mat_apply_self_of_mem_rootGroup hσ hne hy,
      mat_apply_of_weight_sub_eq_neg hσ hne hy (a := lowIdx k) (b := Fin.rev (lowIdx k)) (by
        rw [toStd_neg_last_even hk he, weight_rev']; abel)]
    ring
  · rw [map_one]
    exact ⟨isBlk_one _, by rw [toBlock_one hpp, det_one]⟩
  · intro x y hx hy
    rw [map_mul]
    exact ⟨hx.1.mul hy.1, by
      rw [toBlock_mul hpp (blkLast_hblk_even he) (by
        rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))]) hx.1, det_mul, hx.2,
        hy.2, one_mul]⟩

include hk he in
theorem rankOne_bruhat_last_even {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) (g : SU σ n)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    (∃ h ∈ levelTorus σ k, ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), ∃ h ∈ levelTorus σ k,
        ∃ v ∈ rootGroup σ hσ n (Pi.single k 1), g = u * levelWeyl hσ ζ k * h * v := by
  have hpp := lowIdx_ne_rev (n := n) k k
  have hw2 : 2 • weight n (lowIdx k) = toStd n (Pi.single k 1) := (toStd_last_even hk he).symm
  have hsupp : ∀ g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k, ∀ r,
      r ≠ lowIdx k → r ≠ Fin.rev (lowIdx k) → mat σ n g r (lowIdx k) = 0 :=
    fun g hg r h1 h2 => col_last_of_mem hk hg (by
      rintro (h | h | h)
      exacts [h1 h, h2 h, rev_ne_self_of_even he r h])
  refine bruhat_of_fixCol (p := lowIdx k) le_sup_left (levelWeyl_mem_rankOne hσ ζ k) ?_ ?_ g hg
  ·
    intro g hg hfc
    have hrow := sum_mat_mul_mat g (lowIdx k) (Fin.rev (lowIdx k))
    rw [Finset.sum_eq_single (lowIdx k) (fun s _ hs => by rw [hfc s hs, map_zero, zero_mul])
      (by simp), ite_eq_left rfl] at hrow
    obtain ⟨t, ht⟩ : ∃ t, mat σ n g (lowIdx k) (lowIdx k) = t := ⟨_, rfl⟩
    rw [ht] at hrow
    have ht0 : t ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hrow
      exact zero_ne_one hrow
    obtain ⟨-, hdet⟩ := toBlock_last_of_mem hk he hg
    rw [toBlock, Matrix.det_fin_two_of, ht, hfc _ hpp.symm, mul_zero, sub_zero] at hdet
    have hσt : σ t = t := by
      have h1 : mat σ n g (Fin.rev (lowIdx k)) (Fin.rev (lowIdx k)) ≠ 0 :=
        right_ne_zero_of_mul_eq_one hdet
      exact mul_right_cancel₀ h1 (hrow.trans hdet.symm)
    have hσt' : σ ((Units.mk0 t ht0 : Fˣ) : F) = (Units.mk0 t ht0 : Fˣ) := hσt
    have hh := longTorus_mem_levelTorus hk hζ (Units.mk0 t ht0) hσt'
    have hhL := levelTorus_le_rankOne hσ hζ hnorm k hh
    have hmat : mat σ n (longTorus σ (lowIdx_ne_rev k k) ζ hσt') =
        diagonal (longTorusFun (lowIdx k) t) := coe_longTorus σ _ hζ hσt' ht0
    set h := longTorus σ (lowIdx_ne_rev k k) ζ hσt' with hhdef
    have hd0 : ∀ s, longTorusFun (lowIdx k) t s ≠ 0 := by
      intro s
      simp only [longTorusFun]
      split_ifs <;> simp [ht0]
    have hinv := diagonal_inv_eq hd0 hmat
    have huL : h⁻¹ * g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k :=
      mul_mem (inv_mem hhL) hg
    have hucol : ∀ a, mat σ n (h⁻¹ * g) a (lowIdx k) =
        (1 : Matrix (Fin n) (Fin n) F) a (lowIdx k) := by
      intro a
      rw [map_mul, hinv, diagonal_mul]
      by_cases ha : a = lowIdx k
      · rw [ha, longTorusFun_self, one_apply_eq, ht, inv_mul_cancel₀ ht0]
      · rw [hfc a ha, mul_zero, one_apply_ne ha]
    obtain ⟨hublk, hudet⟩ := toBlock_last_of_mem hk he huL
    have hqq : mat σ n (h⁻¹ * g) (Fin.rev (lowIdx k)) (Fin.rev (lowIdx k)) = 1 := by
      rw [toBlock, Matrix.det_fin_two_of, hucol, hucol, one_apply_eq, one_apply_ne hpp.symm]
        at hudet
      linear_combination hudet
    obtain ⟨β, hβ⟩ : ∃ β, mat σ n (h⁻¹ * g) (lowIdx k) (Fin.rev (lowIdx k)) = β := ⟨_, rfl⟩
    have hcol' : ∀ s, s ≠ lowIdx k → s ≠ Fin.rev (lowIdx k) →
        mat σ n (h⁻¹ * g) s (Fin.rev (lowIdx k)) = 0 := by
      intro s h1 h2
      rw [hublk s _ (fun hs => ?_), one_apply_ne h2]
      rw [blkLast_mem (Or.inr (Or.inl rfl)), blkLast_eq_one_iff] at hs
      rcases hs.1 with h' | h' | h'
      exacts [h1 h', h2 h', rev_ne_self_of_even he s h']
    have hβtr : β + σ β = 0 := by
      have hiso := sum_mat_mul_mat (h⁻¹ * g) (Fin.rev (lowIdx k)) (Fin.rev (lowIdx k))
      rw [ite_eq_right (by rw [Fin.rev_rev]; exact hpp.symm), sum_eq_two (lowIdx k)
        (Fin.rev (lowIdx k)) hpp (fun s h1 h2 => by rw [hcol' s h1 h2, map_zero, zero_mul]),
        Fin.rev_rev, hqq, hβ, map_one, one_mul, mul_one] at hiso
      linear_combination hiso
    have hx := longRootHom_mem hσ hpp hw2 (Multiplicative.ofAdd ⟨β, hβtr⟩)
    have hux : h⁻¹ * g = longRootHom σ hpp (Multiplicative.ofAdd ⟨β, hβtr⟩) := by
      apply mat_injective
      rw [mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd]
      ext a b
      simp only [longRootMatrix, Matrix.add_apply, single_apply]
      by_cases hab : blkLast k a = blkLast k b ∧ blkLast k a ≠ 0
      · have ha1 : blkLast k a = 1 := blkLast_eq_one_of_ne_zero hab.2
        have hb1 : blkLast k b = 1 := hab.1.symm.trans ha1
        have ha := blkLast_hblk_even he a (by rw [ha1, blkLast_mem (Or.inl rfl)])
        have hb := blkLast_hblk_even he b (by rw [hb1, blkLast_mem (Or.inl rfl)])
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · rw [hucol, one_apply_eq]
          simp [Ne.symm hpp]
        · rw [hβ, one_apply_ne hpp]
          simp
        · rw [hucol, one_apply_ne hpp.symm]
          simp [hpp]
        · rw [hqq, one_apply_eq]
          simp [hpp]
      · rw [hublk a b hab]
        have : ¬(lowIdx k = a ∧ Fin.rev (lowIdx k) = b) := by
          rintro ⟨rfl, rfl⟩
          apply hab
          rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))]
          exact ⟨rfl, one_ne_zero⟩
        simp [this]
    exact ⟨h, hh, _, hx, by rw [← hux, mul_inv_cancel_left]⟩
  ·
    intro g hg hnfc
    have hq : mat σ n g (Fin.rev (lowIdx k)) (lowIdx k) ≠ 0 := by
      intro h0
      apply hnfc
      intro r hr
      by_cases hr' : r = Fin.rev (lowIdx k)
      · rw [hr', h0]
      · exact hsupp g hg r hr hr'
    have hiso := sum_mat_mul_mat g (lowIdx k) (lowIdx k)
    rw [ite_eq_right hpp, sum_eq_two (lowIdx k) (Fin.rev (lowIdx k)) hpp
      (fun s h1 h2 => by rw [hsupp g hg s h1 h2, map_zero, zero_mul]), Fin.rev_rev] at hiso
    obtain ⟨c, hc⟩ : ∃ c, c * mat σ n g (Fin.rev (lowIdx k)) (lowIdx k) =
        -mat σ n g (lowIdx k) (lowIdx k) := ⟨_, div_mul_cancel₀ _ hq⟩
    have hctr : c + σ c = 0 := by
      have h1 : σ c * σ (mat σ n g (Fin.rev (lowIdx k)) (lowIdx k)) =
          -σ (mat σ n g (lowIdx k) (lowIdx k)) := by rw [← map_mul, hc, map_neg]
      have h2 : (c + σ c) * (mat σ n g (Fin.rev (lowIdx k)) (lowIdx k) *
          σ (mat σ n g (Fin.rev (lowIdx k)) (lowIdx k))) = 0 := by
        linear_combination σ (mat σ n g (Fin.rev (lowIdx k)) (lowIdx k)) * hc +
          mat σ n g (Fin.rev (lowIdx k)) (lowIdx k) * h1 - hiso
      exact (mul_eq_zero.mp h2).resolve_right (mul_ne_zero hq ((map_ne_zero σ).mpr hq))
    have hx := longRootHom_mem hσ hpp hw2 (Multiplicative.ofAdd ⟨c, hctr⟩)
    refine ⟨_, inv_mem hx, ?_⟩
    rw [inv_inv, mul_assoc]
    refine fixCol_inv_mul (neg_ne_zero.mpr (inv_ne_zero hζ)) (levelWeyl_col_last hk hζ)
      fun r hr => ?_
    rw [map_mul, mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, longRootMatrix,
      Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    by_cases hrp : r = lowIdx k
    · rw [hrp, single_mul_apply_same]
      change _ + c * _ = _
      rw [hc]
      ring
    · rw [single_mul_apply_of_ne (h := hrp), hsupp g hg r hrp hr, add_zero]

include hk he in
theorem eq_one_of_mem_normalizer_last_even {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (u : SU σ n)
    (hu : u ∈ rootGroup σ hσ n (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup σ hσ n (-Pi.single k 1) : Set (SU σ n))) :
    u = 1 := by
  have hpp := lowIdx_ne_rev (n := n) k k
  have hy := longRootHom_mem hσ (rev_ne_rev_rev hpp) (toStd_neg_last_even hk he).symm
    (Multiplicative.ofAdd ζ)
  have hz := (Subgroup.mem_normalizer_iff.mp hn _).mp hy
  have hne : toStd n (Pi.single k 1) ≠ 0 := by
    rw [toStd_last_even hk he]
    intro h
    exact weight_ne_zero hpp (two_nsmul_injective' (by rw [h, smul_zero]))
  have hne' : toStd n (-Pi.single k 1) ≠ 0 := by
    rw [toStd_neg]
    exact neg_ne_zero.mpr hne
  have hzpp := mat_apply_self_of_mem_rootGroup hσ hne' hz (lowIdx k)
  have hUV : mat σ n u * mat σ n u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd,
    longRootMatrix, Fin.rev_rev, conj_one_add_apply hUV, mul_single_mul_apply, one_apply_eq,
    mat_apply_self_of_mem_rootGroup hσ hne (inv_mem hu)] at hzpp
  have hb : mat σ n u (lowIdx k) (Fin.rev (lowIdx k)) = 0 := by
    have : mat σ n u (lowIdx k) (Fin.rev (lowIdx k)) * (ζ : F) = 0 := by
      linear_combination hzpp
    exact (mul_eq_zero.mp this).resolve_right hζ
  refine eq_of_mem_rootGroup hσ hu (one_mem _) fun a b hab => ?_
  rcases hab with hab | hab
  · rw [toStd_last_even hk he] at hab
    obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hpp hab
    rw [hb, map_one, one_apply_ne hpp]
  · exfalso
    rw [toStd_last_even hk he, smul_smul] at hab
    exact weight_ne_zero hpp (eq_zero_of_weight_sub_eq_nsmul hab (by norm_num))

end Even

section Odd

variable (hn : ¬Even n)

include hk in
omit [Field F] in
theorem last_odd_vals :
    (lowIdx (n := n) k).val + 1 = (midIdx n hn).val ∧
      (midIdx n hn).val + 1 = (Fin.rev (lowIdx (n := n) k)).val := by
  have := k.isLt
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
  simp only [val_lowIdx, midIdx, Fin.val_rev]
  omega

include hk in
omit [Field F] in
theorem last_odd_ne :
    lowIdx (n := n) k ≠ midIdx n hn ∧ Fin.rev (lowIdx (n := n) k) ≠ midIdx n hn := by
  obtain ⟨h1, h2⟩ := last_odd_vals hk hn
  exact ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega)⟩

omit [Field F] in
theorem blkLast_odd_iff (s : Fin n) :
    blkLast k s = 1 ↔ s = lowIdx k ∨ s = midIdx n hn ∨ s = Fin.rev (lowIdx k) := by
  rw [blkLast_eq_one_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (middle_unique h (rev_midIdx hn)))
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [h]; exact rev_midIdx hn))
    · exact Or.inr (Or.inl h)

include hk hn in
theorem rankOne_bruhat_last_odd {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) (g : SU σ n)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    (∃ h ∈ levelTorus σ k, ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), ∃ h ∈ levelTorus σ k,
        ∃ v ∈ rootGroup σ hσ n (Pi.single k 1), g = u * levelWeyl hσ ζ k * h * v := by
  have hpp := lowIdx_ne_rev (n := n) k k
  obtain ⟨hpm, hp'm⟩ := last_odd_ne hk hn
  obtain ⟨hv1, hv2⟩ := last_odd_vals hk hn
  have hmid := rev_midIdx hn
  have hXH := heisenberg_le hσ hpp hpm hmid (toStd_last_odd hk hn).symm
  have hsupp : ∀ g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k, ∀ r,
      r ≠ lowIdx k → r ≠ midIdx n hn → r ≠ Fin.rev (lowIdx k) →
        mat σ n g r (lowIdx k) = 0 := by
    intro g hg r h1 h2 h3
    refine col_last_of_mem hk hg (fun h => ?_)
    rcases (blkLast_odd_iff hn r).mp ((blkLast_eq_one_iff r).mpr h) with h' | h' | h'
    exacts [h1 h', h2 h', h3 h']
  refine bruhat_of_fixCol (p := lowIdx k) le_sup_left (levelWeyl_mem_rankOne hσ ζ k) ?_ ?_ g hg
  ·
    intro g hg hfc
    have hrow := sum_mat_mul_mat g (lowIdx k) (Fin.rev (lowIdx k))
    rw [Finset.sum_eq_single (lowIdx k) (fun s _ hs => by rw [hfc s hs, map_zero, zero_mul])
      (by simp), ite_eq_left rfl] at hrow
    obtain ⟨t, ht⟩ : ∃ t, mat σ n g (lowIdx k) (lowIdx k) = t := ⟨_, rfl⟩
    rw [ht] at hrow
    have ht0 : t ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hrow
      exact zero_ne_one hrow
    obtain ⟨h, hhL, hmat⟩ := exists_heisGen_mem_rankOne hσ hζ hnorm hk hn (Units.mk0 t ht0)
    have hh := heisGen_mem_levelTorus hk hn (Units.mk0 t ht0) hmat
    rw [Units.val_mk0] at hmat
    have hd0 : ∀ s, heisTorusFun σ (lowIdx k) t s ≠ 0 := by
      intro s
      have := tFun_ne_zero (σ := σ) k ht0 s
      unfold tFun at this
      rwa [dite_eq_right hk, ite_eq_right hn] at this
    have hinv := diagonal_inv_eq hd0 hmat
    have huL : h⁻¹ * g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k :=
      mul_mem (inv_mem hhL) hg
    have hucol : ∀ a, mat σ n (h⁻¹ * g) a (lowIdx k) =
        (1 : Matrix (Fin n) (Fin n) F) a (lowIdx k) := by
      intro a
      rw [map_mul, hinv, diagonal_mul]
      by_cases ha : a = lowIdx k
      · rw [ha, heisTorusFun_self, one_apply_eq, ht, inv_mul_cancel₀ ht0]
      · rw [hfc a ha, mul_zero, one_apply_ne ha]
    have hurow : ∀ b, mat σ n (h⁻¹ * g) (Fin.rev (lowIdx k)) b =
        (1 : Matrix (Fin n) (Fin n) F) (Fin.rev (lowIdx k)) b := mat_rev_apply_of_col hucol
    have hublk := isBlk_last_of_mem hk huL
    have hlow : ∀ i j : Fin n, j.val < i.val → mat σ n (h⁻¹ * g) i j = 0 := by
      intro i j hji
      by_cases hij : blkLast k i = blkLast k j ∧ blkLast k i ≠ 0
      · have hi1 : blkLast k i = 1 := blkLast_eq_one_of_ne_zero hij.2
        have hj1 : blkLast k j = 1 := hij.1.symm.trans hi1
        rcases (blkLast_odd_iff hn i).mp hi1 with rfl | rfl | rfl <;>
          rcases (blkLast_odd_iff hn j).mp hj1 with rfl | rfl | rfl
        all_goals first
          | (exfalso; omega)
          | (rw [hucol]; exact one_apply_ne (Ne.symm hpm))
          | (rw [hucol]; exact one_apply_ne (Ne.symm hpp))
          | (rw [hurow]; exact one_apply_ne hp'm)
      · rw [hublk i j hij, one_apply_ne (fun h => by rw [h] at hji; omega)]
    have hdiag : ∀ i, i ≠ midIdx n hn → mat σ n (h⁻¹ * g) i i = 1 := by
      intro i hi
      by_cases hip : i = lowIdx k
      · rw [hip, hucol, one_apply_eq]
      by_cases hip' : i = Fin.rev (lowIdx k)
      · rw [hip', hurow, one_apply_eq]
      · rw [hublk i i (fun h => ?_), one_apply_eq]
        rcases (blkLast_odd_iff hn i).mp (blkLast_eq_one_of_ne_zero h.2) with h' | h' | h'
        exacts [hip h', hi h', hip' h']
    have hdet : (mat σ n (h⁻¹ * g)).det = 1 := (h⁻¹ * g).2.1
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => hlow i j hji),
      Finset.prod_eq_single (midIdx n hn) (fun i _ hi => hdiag i hi) (by simp)] at hdet
    obtain ⟨a, ha⟩ : ∃ a, mat σ n (h⁻¹ * g) (lowIdx k) (midIdx n hn) = a := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ : ∃ a', mat σ n (h⁻¹ * g) (midIdx n hn) (Fin.rev (lowIdx k)) = a' :=
      ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, mat σ n (h⁻¹ * g) (lowIdx k) (Fin.rev (lowIdx k)) = b := ⟨_, rfl⟩
    have hcolm : ∀ s, s ≠ lowIdx k → s ≠ midIdx n hn →
        mat σ n (h⁻¹ * g) s (midIdx n hn) = 0 := by
      intro s h1 h2
      by_cases h3 : s = Fin.rev (lowIdx k)
      · rw [h3, hurow, one_apply_ne hp'm]
      · rw [hublk s _ (fun h => ?_), one_apply_ne h2]
        rcases (blkLast_odd_iff hn s).mp (h.1.trans (blkLast_mem (Or.inr (Or.inr hmid))))
          with h' | h' | h'
        exacts [h1 h', h2 h', h3 h']
    have hcolp' : ∀ s, s ≠ lowIdx k → s ≠ midIdx n hn → s ≠ Fin.rev (lowIdx k) →
        mat σ n (h⁻¹ * g) s (Fin.rev (lowIdx k)) = 0 := by
      intro s h1 h2 h3
      rw [hublk s _ (fun h => ?_), one_apply_ne h3]
      rcases (blkLast_odd_iff hn s).mp (h.1.trans (blkLast_mem (Or.inr (Or.inl rfl))))
        with h' | h' | h'
      exacts [h1 h', h2 h', h3 h']
    have h1 := sum_mat_mul_mat (h⁻¹ * g) (midIdx n hn) (Fin.rev (lowIdx k))
    rw [hmid, ite_eq_right hp'm, sum_eq_two (lowIdx k) (midIdx n hn) hpm
      (fun s h1 h2 => by rw [hcolm s h1 h2, map_zero, zero_mul]), hmid, ha, ha', hdet,
      hurow, one_apply_eq, map_one] at h1
    have h2 := sum_mat_mul_mat (h⁻¹ * g) (Fin.rev (lowIdx k)) (Fin.rev (lowIdx k))
    rw [ite_eq_right (by rw [Fin.rev_rev]; exact hpp.symm), sum_eq_three (lowIdx k) (midIdx n hn)
      (Fin.rev (lowIdx k)) hpm hpp (Ne.symm hp'm)
      (fun s h1 h2 h3 => by rw [hcolp' s h1 h2 h3, map_zero, zero_mul]), hmid, Fin.rev_rev, hb,
      ha', hurow, one_apply_eq, map_one] at h2
    have ha'σ : a' = -σ a := by linear_combination h1
    have hrel : b + σ b + σ a * a = 0 := by
      rw [ha'σ, map_neg, hσ] at h2
      linear_combination h2
    have hu : h⁻¹ * g ∈ heisenbergSubgroup σ hσ hpp hpm hmid := by
      refine ⟨a, b, hrel, ?_⟩
      ext i j
      rw [← mat_apply]
      simp only [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, single_apply]
      by_cases hij : blkLast k i = blkLast k j ∧ blkLast k i ≠ 0
      · have hi1 : blkLast k i = 1 := blkLast_eq_one_of_ne_zero hij.2
        have hj1 : blkLast k j = 1 := hij.1.symm.trans hi1
        rcases (blkLast_odd_iff hn i).mp hi1 with rfl | rfl | rfl <;>
          rcases (blkLast_odd_iff hn j).mp hj1 with rfl | rfl | rfl
        · rw [hucol, one_apply_eq]
          simp [Ne.symm hpm, Ne.symm hpp]
        · rw [ha, one_apply_ne hpm]
          simp [Ne.symm hpm, hp'm]
        · rw [hb, one_apply_ne hpp]
          simp [Ne.symm hpm, Ne.symm hp'm]
        · rw [hucol, one_apply_ne (Ne.symm hpm)]
          simp [hpm, Ne.symm hpp]
        · rw [hdet, one_apply_eq]
          simp [hpm, hp'm]
        · rw [ha', ha'σ, one_apply_ne (Ne.symm hp'm)]
          simp [hpm]
        · rw [hurow, one_apply_ne (Ne.symm hpp)]
          simp [hpp, Ne.symm hp'm]
        · rw [hurow, one_apply_ne hp'm]
          simp [hpp, Ne.symm hp'm]
        · rw [hurow, one_apply_eq]
          simp [hpp, Ne.symm hp'm]
      · rw [hublk i j hij]
        have e1 : ¬(lowIdx k = i ∧ midIdx n hn = j) := by
          rintro ⟨rfl, rfl⟩
          exact hij ⟨by rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inr hmid))],
            by rw [blkLast_mem (Or.inl rfl)]; exact one_ne_zero⟩
        have e2 : ¬(midIdx n hn = i ∧ Fin.rev (lowIdx k) = j) := by
          rintro ⟨rfl, rfl⟩
          exact hij ⟨by rw [blkLast_mem (Or.inr (Or.inr hmid)), blkLast_mem (Or.inr (Or.inl rfl))],
            by rw [blkLast_mem (Or.inr (Or.inr hmid))]; exact one_ne_zero⟩
        have e3 : ¬(lowIdx k = i ∧ Fin.rev (lowIdx k) = j) := by
          rintro ⟨rfl, rfl⟩
          exact hij ⟨by rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))],
            by rw [blkLast_mem (Or.inl rfl)]; exact one_ne_zero⟩
        simp [e1, e2, e3]
    exact ⟨h, hh, _, hXH hu, by rw [mul_inv_cancel_left]⟩
  ·
    intro g hg hnfc
    obtain ⟨xp, hxp⟩ : ∃ x, mat σ n g (lowIdx k) (lowIdx k) = x := ⟨_, rfl⟩
    obtain ⟨xm, hxm⟩ : ∃ x, mat σ n g (midIdx n hn) (lowIdx k) = x := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ x, mat σ n g (Fin.rev (lowIdx k)) (lowIdx k) = x := ⟨_, rfl⟩
    have hiso := sum_mat_mul_mat g (lowIdx k) (lowIdx k)
    rw [ite_eq_right hpp, sum_eq_three (lowIdx k) (midIdx n hn) (Fin.rev (lowIdx k)) hpm hpp
      (Ne.symm hp'm) (fun s h1 h2 h3 => by rw [hsupp g hg s h1 h2 h3, map_zero, zero_mul]), hmid,
      Fin.rev_rev, hxp, hxm, hc] at hiso
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero, mul_zero, zero_mul, zero_add, add_zero] at hiso
      have hxm0 : xm = 0 := by
        rcases mul_eq_zero.mp hiso with h' | h'
        · exact (map_eq_zero σ).mp h'
        · exact h'
      apply hnfc
      intro r hr
      by_cases hrm : r = midIdx n hn
      · rw [hrm, hxm, hxm0]
      by_cases hrp' : r = Fin.rev (lowIdx k)
      · rw [hrp', hc, h0]
      · exact hsupp g hg r hr hrm hrp'
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
    set a : F := σ (xm / c) with hadef
    have hσa : σ a = xm / c := by rw [hadef, hσ]
    set b : F := -(xp + a * xm) / c with hbdef
    have hrel : b + σ b + σ a * a = 0 := by
      have hσb : σ b = -(σ xp + σ a * σ xm) / σ c := by
        rw [hbdef, map_div₀, map_neg, map_add, map_mul]
      rw [hσb, hσa, hbdef, hadef, map_div₀]
      field_simp
      linear_combination (-1 : F) * hiso
    have hx := hXH (heisRootElt_mem hσ hpp hpm hmid a b hrel)
    refine ⟨_, inv_mem hx, ?_⟩
    rw [inv_inv, mul_assoc]
    refine fixCol_inv_mul (neg_ne_zero.mpr (inv_ne_zero hζ)) (levelWeyl_col_last hk hζ)
      fun r hr => ?_
    rw [map_mul, mat_apply (heisRootElt _ _ _ _ _ _ _)]
    change (heisenbergMatrix σ (lowIdx k) (midIdx n hn) a b * mat σ n g) r (lowIdx k) = 0
    rw [heisenbergMatrix, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
      Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply]
    by_cases hrp : r = lowIdx k
    · rw [hrp, single_mul_apply_same, single_mul_apply_of_ne (h := hpm), single_mul_apply_same,
        hxp, hxm, hc, hbdef]
      field_simp
      ring
    · rw [single_mul_apply_of_ne (h := hrp), single_mul_apply_of_ne (h := hrp)]
      by_cases hrm : r = midIdx n hn
      · rw [hrm, single_mul_apply_same, hxm, hc, hσa]
        field_simp
        ring
      · rw [single_mul_apply_of_ne (h := hrm), hsupp g hg r hrp hrm hr]
        ring

include hk hn in
theorem eq_one_of_mem_normalizer_last_odd {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (u : SU σ n)
    (hu : u ∈ rootGroup σ hσ n (Pi.single k 1))
    (hnm : u ∈ Subgroup.normalizer (rootGroup σ hσ n (-Pi.single k 1) : Set (SU σ n))) :
    u = 1 := by
  have hpp := lowIdx_ne_rev (n := n) k k
  obtain ⟨hpm, hp'm⟩ := last_odd_ne hk hn
  have hmid := rev_midIdx hn
  have hp' := rev_ne_rev_rev hpp
  have hy := heisenberg_le hσ hp' hp'm hmid (toStd_neg_last_odd hk hn).symm
    (longRootHom_mem_heisenberg hσ hp' hp'm hmid (Multiplicative.ofAdd ζ))
  have hz := (Subgroup.mem_normalizer_iff.mp hnm _).mp hy
  have hne : toStd n (Pi.single k 1) ≠ 0 := by
    rw [toStd_last_odd hk hn]
    exact weight_ne_zero hpp
  have hne' : toStd n (-Pi.single k 1) ≠ 0 := by
    rw [toStd_neg]
    exact neg_ne_zero.mpr hne
  have hzpp := mat_apply_self_of_mem_rootGroup hσ hne' hz (lowIdx k)
  have hUV : mat σ n u * mat σ n u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd,
    longRootMatrix, Fin.rev_rev, conj_one_add_apply hUV, mul_single_mul_apply, one_apply_eq,
    mat_apply_self_of_mem_rootGroup hσ hne (inv_mem hu)] at hzpp
  have hb : mat σ n u (lowIdx k) (Fin.rev (lowIdx k)) = 0 := by
    have : mat σ n u (lowIdx k) (Fin.rev (lowIdx k)) * (ζ : F) = 0 := by
      linear_combination hzpp
    exact (mul_eq_zero.mp this).resolve_right hζ
  have hw : toStd n (Pi.single k 1) = weight n (lowIdx k) := toStd_last_odd hk hn
  have hoff : ∀ a b, weight n a - weight n b ≠ weight n (lowIdx k) →
      weight n a - weight n b ≠ 2 • weight n (lowIdx k) →
        mat σ n u a b = (1 : Matrix (Fin n) (Fin n) F) a b := fun a b h1 h2 =>
    mat_apply_of_mem_rootGroup hσ hu (by rwa [hw]) (by rwa [hw])
  have hwm := weight_eq_zero_of_rev_eq (n := n) hmid
  have hcolp' : ∀ s, s ≠ lowIdx k → s ≠ midIdx n hn → s ≠ Fin.rev (lowIdx k) →
      mat σ n u s (Fin.rev (lowIdx k)) = 0 := by
    intro s h1 h2 h3
    rw [hoff s _ (fun h => ?_) (fun h => ?_), one_apply_ne h3]
    · apply h2
      apply weight_injective
      rw [hwm]
      rw [weight_rev'] at h
      funext c
      have := congrFun h c
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at this ⊢
      omega
    · apply h1
      apply weight_injective
      rw [weight_rev'] at h
      funext c
      have := congrFun h c
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul,
        Nat.cast_ofNat] at this ⊢
      omega
  have hcolm : ∀ s, s ≠ lowIdx k → s ≠ midIdx n hn → mat σ n u s (midIdx n hn) = 0 := by
    intro s h1 h2
    rw [hoff s _ (fun h => ?_) (fun h => ?_), one_apply_ne h2]
    · rw [hwm, sub_zero] at h
      exact h1 (weight_injective h)
    · obtain ⟨-, h'⟩ := eq_rev_of_weight_sub_eq_two_smul h (weight_ne_zero hpp)
      exact h1 (weight_injective h')
  have hpp' := mat_apply_self_of_mem_rootGroup hσ hne hu (Fin.rev (lowIdx k))
  have hmm := mat_apply_self_of_mem_rootGroup hσ hne hu (midIdx n hn)
  have hp'm' : mat σ n u (Fin.rev (lowIdx k)) (midIdx n hn) = 0 := hcolm _ hpp.symm hp'm
  obtain ⟨a, ha⟩ : ∃ a, mat σ n u (lowIdx k) (midIdx n hn) = a := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', mat σ n u (midIdx n hn) (Fin.rev (lowIdx k)) = a' := ⟨_, rfl⟩
  have h1 := sum_mat_mul_mat u (Fin.rev (lowIdx k)) (Fin.rev (lowIdx k))
  rw [ite_eq_right (by rw [Fin.rev_rev]; exact hpp.symm), sum_eq_three (lowIdx k) (midIdx n hn)
    (Fin.rev (lowIdx k)) hpm hpp (Ne.symm hp'm)
    (fun s h1 h2 h3 => by rw [hcolp' s h1 h2 h3, map_zero, zero_mul]), hmid, Fin.rev_rev, hb,
    ha', hpp', map_zero, map_one, zero_mul, one_mul, zero_add, add_zero] at h1
  have ha'0 : a' = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact (map_eq_zero σ).mp h'
    · exact h'
  have h2 := sum_mat_mul_mat u (midIdx n hn) (Fin.rev (lowIdx k))
  rw [hmid, ite_eq_right hp'm, sum_eq_two (lowIdx k) (midIdx n hn) hpm
    (fun s h1 h2 => by rw [hcolm s h1 h2, map_zero, zero_mul]), hmid, ha, ha', ha'0, hmm,
    hpp', map_one, mul_one, one_mul, add_zero] at h2
  have ha0 : a = 0 := (map_eq_zero σ).mp h2
  refine eq_of_mem_rootGroup hσ hu (one_mem _) fun i j hij => ?_
  rw [map_one]
  rw [hw] at hij
  rcases hij with hij | hij
  · rcases eq_of_weight_sub_eq_weight hpp hmid hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ha, ha0, one_apply_ne hpm]
    · rw [ha', ha'0, one_apply_ne (Ne.symm hp'm)]
  · obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hpp hij
    rw [hb, one_apply_ne hpp]

end Odd

end Last

end CFSG.LieType.Universal.Unitary.SUExtras
