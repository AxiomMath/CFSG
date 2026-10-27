module

public import CFSG.LieType.Universal.Spin.Structure.Entries
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Spin.Structure.Levels

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits

section Stab

variable {K : Type} [Field K]

@[expose] noncomputable def stabSub {σ : Type} [Fintype σ] [DecidableEq σ]
    (Q : QuadraticForm K (σ → K)) (W : Submodule K (σ → K)) : Subgroup (spinGroup Q) where
  carrier := {g | ∀ v ∈ W, spinAction Q g v ∈ W}
  mul_mem' := by
    intro g h hg hh v hv
    rw [map_mul, LinearEquiv.mul_apply]
    exact hg _ (hh v hv)
  one_mem' := by
    intro v hv
    rw [map_one]
    exact hv
  inv_mem' := by
    intro g hg v hv
    let f : W →ₗ[K] W :=
      ((spinAction Q g).toLinearMap).restrict (fun w hw => hg w hw)
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      exact (spinAction Q g).injective this
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨v, hv⟩
    have hw' : spinAction Q g (w : σ → K) = v := congrArg Subtype.val hw
    have : spinAction Q g⁻¹ v = w := by
      calc spinAction Q g⁻¹ v
          = spinAction Q g⁻¹ (spinAction Q g (w : σ → K)) := by rw [hw']
        _ = (spinAction Q g⁻¹ * spinAction Q g) (w : σ → K) :=
            (LinearEquiv.mul_apply _ _ _).symm
        _ = w := by rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this]
    exact w.2

theorem mem_stabSub {σ : Type} [Fintype σ] [DecidableEq σ] {Q : QuadraticForm K (σ → K)}
    {W : Submodule K (σ → K)} {g : spinGroup Q} :
    g ∈ stabSub Q W ↔ ∀ v ∈ W, spinAction Q g v ∈ W := Iff.rfl

variable {n : ℕ}

@[expose] def flagIdx (m : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl m
  | false => .inr m

theorem isCoord_plusFrame_flag (hn : 3 ≤ n) :
    (plusFrame n K hn).IsCoord (flagIdx (n := n)) where
  idx_inj {m r m' r'} h := by
    cases r <;> cases r' <;> simp_all [flagIdx]
  vec_eq m r := by cases r <;> rfl
  polar_vec v m r := by
    cases r
    · exact polar_quadPlus_single_inr n K v m
    · exact polar_quadPlus_single_inl n K v m

@[expose] def flagWt (c : Fin n → ℤ) : Fin n ⊕ Fin n → ℤ
  | .inl m => c m
  | .inr m => -c m

theorem flagWt_idx (c : Fin n → ℤ) (m : Fin n) (r : Bool) :
    flagWt c (flagIdx m r) = boolSign r * c m := by
  cases r <;> simp [flagWt, flagIdx]

variable (K) in
@[expose] def flagSpace (c : Fin n → ℤ) : Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {v | ∀ a, v a ≠ 0 → 1 ≤ flagWt c a}
  add_mem' := by
    intro v w hv hw a ha
    by_cases h : v a = 0
    · refine hw a fun h' => ha ?_
      simp [h, h']
    · exact hv a h
  zero_mem' := fun a ha => absurd rfl ha
  smul_mem' := by
    intro r v hv a ha
    exact hv a fun h => ha (by simp [h])

theorem mem_flagSpace_iff (c : Fin n → ℤ) (v : Fin n ⊕ Fin n → K) :
    v ∈ flagSpace K c ↔ ∀ a, v a ≠ 0 → 1 ≤ flagWt c a := Iff.rfl

theorem quadPlus_flagSpace (c : Fin n → ℤ) {v : Fin n ⊕ Fin n → K} (hv : v ∈ flagSpace K c) :
    quadPlus n K v = 0 := by
  rw [quadPlus_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_contra h
  have h1 : v (.inl i) ≠ 0 := left_ne_zero_of_mul h
  have h2 : v (.inr i) ≠ 0 := right_ne_zero_of_mul h
  have a1 := hv _ h1
  have a2 := hv _ h2
  simp only [flagWt] at a1 a2
  omega

theorem flagSpace_ne_bot (c : Fin n → ℤ) {m : Fin n} (hm : 0 < c m) : flagSpace K c ≠ ⊥ := by
  intro h
  have hmem : (Pi.single (.inl m) 1 : Fin n ⊕ Fin n → K) ∈ flagSpace K c := by
    intro a ha
    by_cases hma : a = .inl m
    · subst hma
      simp only [flagWt]
      omega
    · exfalso
      exact ha (by simp [hma])
  rw [h, Submodule.mem_bot] at hmem
  have := congrFun hmem (.inl m)
  simp at this

theorem mem_stabSub_flagSpace_of_spinMat {g : spinGroup (quadPlus n K)} {c : Fin n → ℤ}
    (h : ∀ a b, spinMat (quadPlus n K) g a b ≠ 0 → flagWt c b ≤ flagWt c a) :
    g ∈ stabSub (quadPlus n K) (flagSpace K c) := by
  intro v hv a ha
  have hv' : v = ∑ b, v b • (Pi.single b (1 : K) : Fin n ⊕ Fin n → K) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  have hmv : spinAction (quadPlus n K) g v a = ∑ b, spinMat (quadPlus n K) g a b * v b := by
    conv_lhs => rw [hv']
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, spinMat_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [hmv] at ha
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have h1 : spinMat (quadPlus n K) g a b ≠ 0 := left_ne_zero_of_mul hb
  have h2 : v b ≠ 0 := right_ne_zero_of_mul hb
  exact (hv b h2).trans (h a b h1)

theorem longRoot_mem_stabSub (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (y : K)
    (c : Fin n → ℤ) (hc : 0 ≤ boolSign s * c i + boolSign t * c j) :
    (plusFrame n K hn).longRoot hij s t (.ofAdd y) ∈ stabSub (quadPlus n K) (flagSpace K c) := by
  refine mem_stabSub_flagSpace_of_spinMat fun a b hne => ?_
  rw [(isCoord_plusFrame_flag hn).spinMat_longRoot hij s t y a b] at hne
  by_cases h1 : a = flagIdx i s ∧ b = flagIdx j (!t)
  · obtain ⟨rfl, rfl⟩ := h1
    rw [flagWt_idx, flagWt_idx, boolSign_not]
    linarith
  · by_cases h2 : a = flagIdx j t ∧ b = flagIdx i (!s)
    · obtain ⟨rfl, rfl⟩ := h2
      rw [flagWt_idx, flagWt_idx, boolSign_not]
      linarith
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero] at hne
      by_cases hab : a = b
      · subst hab
        exact le_rfl
      · exact absurd (Matrix.one_apply_ne hab) hne

theorem plusRootGroup_le_stabSub (hn : 3 ≤ n) (c : Fin n → ℤ)
    (hdom : ∀ i j : Fin n, i < j → c j ≤ c i ∧ -c j ≤ c i) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) (hpos : 0 < ht γ) :
    plusRootGroup n K hn γ ≤ stabSub (quadPlus n K) (flagSpace K c) := by
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  rw [hX]
  rintro _ ⟨y, rfl⟩
  rw [← ofAdd_toAdd y]
  refine longRoot_mem_stabSub hn hij s t _ c ?_
  have hht := ht_of_toStdD_eq_add n (by omega) hstd
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hlt' : (i : ℕ) < j := hlt
    have hd := hdom i j hlt
    cases s <;> cases t <;> simp only [boolSign_true, boolSign_false] at hht ⊢
    · omega
    · omega
    · omega
    · omega
  · have hgt' : (j : ℕ) < i := hgt
    have hd := hdom j i hgt
    cases s <;> cases t <;> simp only [boolSign_true, boolSign_false] at hht ⊢
    · omega
    · omega
    · omega
    · omega

theorem torusD_le_stabSub (hn : 3 ≤ n) (c : Fin n → ℤ) (k : Fin n) :
    (torusD K hn k).range ≤ stabSub (quadPlus n K) (flagSpace K c) := by
  rintro _ ⟨τ, rfl⟩
  refine mem_stabSub_flagSpace_of_spinMat fun a b hne => ?_
  by_cases hab : a = b
  · subst hab
    exact le_rfl
  · exfalso
    apply hne
    have hdiag : (spinMat (quadPlus n K) (torusD K hn k τ)).IsDiag := by
      refine isDiag_spinMat fun b => ?_
      rcases b with m | m
      · exact ⟨_, spinAction_torusD K hn k τ m true⟩
      · exact ⟨_, spinAction_torusD K hn k τ m false⟩
    exact hdiag hab

theorem rankOneD_le_stabSub (hn : 3 ≤ n) (c : Fin n → ℤ) (i : Fin n)
    (hi : c (rootIdxD n i) + boolSign (rootSignD n i) * c (rootIdxD' n i) = 0) :
    rankOne (plusRootGroup n K hn) i ≤ stabSub (quadPlus n K) (flagSpace K c) := by
  rw [rankOne, plusRootGroup_single hn i, plusRootGroup_neg_single hn i]
  refine sup_le ?_ ?_
  · rintro _ ⟨y, rfl⟩
    rw [rootD, ← ofAdd_toAdd y]
    refine longRoot_mem_stabSub hn _ _ _ _ c ?_
    rw [boolSign_true]
    linarith
  · rintro _ ⟨y, rfl⟩
    rw [negRootD, ← ofAdd_toAdd y]
    refine longRoot_mem_stabSub hn _ _ _ _ c ?_
    rw [boolSign_not, boolSign_false]
    linarith

theorem borel_le_stabSub (hn : 3 ≤ n) (c : Fin n → ℤ)
    (hdom : ∀ i j : Fin n, i < j → c j ≤ c i ∧ -c j ≤ c i) :
    CFSG.LieType.Steinberg.borel (plusDatum n K hn) (fun k => (torusD K hn k).range) ≤
      stabSub (quadPlus n K) (flagSpace K c) := by
  refine sup_le (iSup_le fun k => torusD_le_stabSub hn c k) ?_
  exact iSup₂_le fun γ hγ => plusRootGroup_le_stabSub hn c hdom hγ.1 hγ.2

end Stab

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
