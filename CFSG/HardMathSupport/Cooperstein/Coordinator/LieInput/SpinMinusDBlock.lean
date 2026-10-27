module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusBlocks
public import CFSG.RankThree.PartOne.CTP.SU4EvenGen
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.MatLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFin

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbedding.LeviBlock

section Partner

@[expose] def partnerM {m : ℕ} : (Fin m ⊕ Fin m ⊕ Fin 2) → (Fin m ⊕ Fin m ⊕ Fin 2)
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr t) => .inr (.inr (Fin.rev t))

theorem epsM_partner (n : ℕ) (hn : 1 ≤ n) (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    epsM n hn (partnerM x) = Fin.rev (epsM n hn x) := by
  rcases x with i | i | t
  · have := epsM_not n hn i true
    simpa [partnerM, minusPos] using this
  · have := epsM_not n hn i false
    simp only [minusPos, Bool.not_false] at this
    simpa [partnerM] using this
  · apply Fin.ext
    have := t.isLt
    fin_cases t <;> simp [partnerM, epsM_apply, epsFun, Fin.val_rev] <;> omega

end Partner


section Embed

variable {n k a : ℕ} (h : a + k = n)

include h

@[expose] def shiftC (c : Fin (k - 1)) : Fin (n - 1) := ⟨a + c.val, by have := c.isLt; omega⟩

theorem shiftC_injective : Function.Injective (shiftC h) := fun c d e => by
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [shiftC] at this
  omega

@[expose] def tauM : (Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) → (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :=
  Sum.map (shiftC h) (Sum.map (shiftC h) id)

theorem tauM_injective : Function.Injective (tauM h) :=
  Sum.map_injective.mpr ⟨shiftC_injective h, Sum.map_injective.mpr ⟨shiftC_injective h, Function.injective_id⟩⟩

theorem tauM_partner (x : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) :
    tauM h (partnerM x) = partnerM (tauM h x) := by
  rcases x with i | i | t <;> rfl

theorem tauM_minusPos (i : Fin (k - 1)) (s : Bool) :
    tauM h (minusPos k i s) = minusPos n (shiftC h i) s := by
  cases s <;> rfl

variable (hk1 : 1 ≤ k) (hn1 : 1 ≤ n)

@[expose] noncomputable def tauF (w : Fin (k + k)) : Fin (n + n) :=
  epsM n hn1 (tauM h ((epsM k hk1).symm w))

theorem tauF_epsM (x : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) :
    tauF h hk1 hn1 (epsM k hk1 x) = epsM n hn1 (tauM h x) := by
  simp [tauF]

theorem tauF_injective : Function.Injective (tauF h hk1 hn1) :=
  (epsM n hn1).injective.comp ((tauM_injective h).comp (epsM k hk1).symm.injective)

theorem tauF_rev (w : Fin (k + k)) : tauF h hk1 hn1 (Fin.rev w) = Fin.rev (tauF h hk1 hn1 w) := by
  obtain ⟨x, rfl⟩ := (epsM k hk1).surjective w
  rw [← epsM_partner k hk1, tauF_epsM, tauF_epsM, tauM_partner, epsM_partner]

end Embed


section DMu

variable {n k a : ℕ} (h : a + k = n) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hk1 : 1 ≤ k) (hn1 : 1 ≤ n)

include h

@[expose] noncomputable def dMu :
    spinGroup (quadMinus k F b c) →* Matrix (Fin (n + n)) (Fin (n + n)) F :=
  (extendHom (F := F) (tauF_injective h hk1 hn1)).comp (matM hk1)

theorem dMu_apply (s : spinGroup (quadMinus k F b c)) :
    dMu h hk1 hn1 s = extendMat (tauF_injective h hk1 hn1) (matM hk1 s) := rfl

theorem dMu_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (dMu (b := b) (c := c) h hk1 hn1) := by
  intro x y hxy
  apply matM_injective hirr hk1
  have := congrArg (fun A => A.submatrix (tauF h hk1 hn1) (tauF h hk1 hn1)) hxy
  simp only [dMu_apply, submatrix_extendMat] at this
  exact this

theorem shift_longRoot {i j : Fin (k - 1)} (hij : i ≠ j) (s t : Bool) (x : F) :
    matM hn1 ((minusFrame n b c).longRoot (fun e => hij (shiftC_injective h e)) s t (.ofAdd x)) =
      dMu h hk1 hn1 ((minusFrame k b c).longRoot hij s t (.ofAdd x)) := by
  rw [dMu_apply, matM_longRoot hk1 hij s t x, extendMat_rootMatrix (tauF_injective h hk1 hn1)
    (tauF_rev h hk1 hn1), matM_longRoot hn1 _ s t x, tauF_epsM, tauF_epsM, tauM_minusPos,
    tauM_minusPos]


theorem planeVec_tauM (p : Fin 2 → F) (x : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) :
    planeVec n p (tauM h x) = planeVec k p x := by
  rcases x with i | i | t <;> rfl

theorem planeVec_of_not_plane (p : Fin 2 → F) {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2}
    (hx : ∀ t, x ≠ .inr (.inr t)) : planeVec n p x = 0 := by
  rcases x with i | i | t
  · rfl
  · rfl
  · exact absurd rfl (hx t)

theorem polarSingle_tauM (p : Fin 2 → F) (x : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) :
    polar (quadMinus n F b c) (Pi.single (tauM h x) 1) (planeVec n p) =
      polar (quadMinus k F b c) (Pi.single x 1) (planeVec k p) := by
  rcases x with i | i | t
  · rw [polar_single_planeVec_of_ne n (fun t => by simp [tauM]) p,
      polar_single_planeVec_of_ne k (fun t => by simp) p]
  · rw [polar_single_planeVec_of_ne n (fun t => by simp [tauM]) p,
      polar_single_planeVec_of_ne k (fun t => by simp) p]
  · simp [polar_quadMinus, tauM, planeVec, Pi.single_apply]

theorem not_range_tauF {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2} (hx : x ∉ Set.range (tauM h)) :
    epsM n hn1 x ∉ Set.range (tauF h hk1 hn1) := by
  rintro ⟨w, hw⟩
  apply hx
  refine ⟨(epsM k hk1).symm w, ?_⟩
  exact (epsM n hn1).injective (by rw [← hw]; rfl)

theorem not_plane_of_not_range {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2}
    (hx : x ∉ Set.range (tauM h)) (t : Fin 2) : x ≠ .inr (.inr t) :=
  fun e => hx ⟨.inr (.inr t), e.symm⟩


theorem shift_shortRoot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (k - 1)) (s : Bool)
    (p : Fin 2 → F) :
    matM hn1 (twShortRoot n hirr (shiftC h i) s (.ofAdd p)) =
      dMu h hk1 hn1 (twShortRoot k hirr i s (.ofAdd p)) := by
  ext u v
  obtain ⟨x1, rfl⟩ := (epsM n hn1).surjective u
  obtain ⟨x2, rfl⟩ := (epsM n hn1).surjective v
  rw [matM_apply, mat_twShortRoot_apply, dMu_apply]
  by_cases hx : x1 ∈ Set.range (tauM h) ∧ x2 ∈ Set.range (tauM h)
  · obtain ⟨⟨y1, rfl⟩, ⟨y2, rfl⟩⟩ := hx
    rw [← tauF_epsM h hk1 hn1 y1, ← tauF_epsM h hk1 hn1 y2,
      extendMat_apply_map, matM_apply, mat_twShortRoot_apply]
    simp only [← tauM_minusPos h, (tauM_injective h).eq_iff, planeVec_tauM, polarSingle_tauM]
  · rw [extendMat_apply_of_not_mem _ _ (by
      by_cases h1 : x1 ∈ Set.range (tauM h)
      · exact Or.inr (not_range_tauF h hk1 hn1 (fun h2 => hx ⟨h1, h2⟩))
      · exact Or.inl (not_range_tauF h hk1 hn1 h1))]
    simp only [Matrix.one_apply, (epsM n hn1).injective.eq_iff]
    have e1 : (if minusPos n (shiftC h i) (!s) = x2 then (1 : F) else 0) * planeVec n p x1 = 0 := by
      by_cases h2 : minusPos n (shiftC h i) (!s) = x2
      · have hx2 : x2 ∈ Set.range (tauM h) := ⟨minusPos k i (!s), by rw [tauM_minusPos, h2]⟩
        have hx1 : x1 ∉ Set.range (tauM h) := fun h1 => hx ⟨h1, hx2⟩
        rw [planeVec_of_not_plane h p (not_plane_of_not_range h hx1), mul_zero]
      · rw [if_neg h2, zero_mul]
    have e2 : (polar (quadMinus n F b c) (Pi.single x2 1) (planeVec n p) +
        planeNorm b c p * (if minusPos n (shiftC h i) (!s) = x2 then 1 else 0)) *
          (if x1 = minusPos n (shiftC h i) s then 1 else 0) = 0 := by
      by_cases h2 : x1 = minusPos n (shiftC h i) s
      · have hx1 : x1 ∈ Set.range (tauM h) := ⟨minusPos k i s, by rw [tauM_minusPos, h2]⟩
        have hx2 : x2 ∉ Set.range (tauM h) := fun h1 => hx ⟨hx1, h1⟩
        have h3 : minusPos n (shiftC h i) (!s) ≠ x2 := fun e =>
          hx2 ⟨minusPos k i (!s), by rw [tauM_minusPos, e]⟩
        rw [polar_single_planeVec_of_ne n (not_plane_of_not_range h hx2) p, if_neg h3]
        simp
      · rw [if_neg h2, mul_zero]
    have := e1
    have := e2
    simp only [e1, e2]
    ring

end DMu




section Gen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem ofStdB_single {m : ℕ} (i k : Fin m) (x : ℤ) :
    ofStdB m (Pi.single i x) k = if i.val ≤ k.val then x else 0 := by
  simp only [ofStdB, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

theorem ofStdB_pair' {m : ℕ} (i j k : Fin m) (x y : ℤ) :
    ofStdB m (Pi.single i x + Pi.single j y) k =
      (if i.val ≤ k.val then x else 0) + (if j.val ≤ k.val then y else 0) := by
  rw [← ofStdB_single i k x, ← ofStdB_single j k y]
  simp only [ofStdB, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

theorem minusDatum_iSup_eq_top_of_three_le (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : ℕ}
    (hk : 3 ≤ k) :
    ⨆ γ ∈ roots (isFiniteType_cartanB (k - 1)) ∅, minusRootGroup k hirr γ = ⊤ := by
  by_cases h4 : 4 ≤ k
  · exact minusDatum_iSup_eq_top k hirr h4
  · obtain rfl : k = 3 := by omega
    exact CFSG.RankThree.PartOne.CTP.SU4Even.minusDatum_iSup_eq_top_three_even hirr

theorem minusDatum_isCT_of_three_le (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hn : 3 ≤ n) :
    IsCTGroupDatum (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum n hirr).isFiniteType) (minusDatum n hirr).roots
      (minusDatum n hirr).rootGroup (minusWeyl n hirr) (minusTorus n hirr) := by
  by_cases h4 : 4 ≤ n
  · exact minusDatum_isCTGroupDatum n hirr h4
  · obtain rfl : n = 3 := by omega
    exact CFSG.RankThree.PartOne.CTP.SU4Even.minusDatum_isCTGroupDatum_three_even hirr

end Gen


section DBlockEquiv

variable {n k a : ℕ} (h : a + k = n) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hk3 : 3 ≤ k)

include h hk3

theorem dblock_E1 (hk1 : 1 ≤ k) (hn1 : 1 ≤ n) (x : spinGroup (quadMinus k F b c)) :
    ∃ t ∈ leviM (minusDatum n hirr) (blkNodes (n - 1) a), matM hn1 t = dMu h hk1 hn1 x := by
  classical
  have hct := minusDatum_isCT_of_three_le hirr (by omega : 3 ≤ n)
  let S : Subgroup (spinGroup (quadMinus k F b c)) :=
    { carrier := {s | ∃ t ∈ leviM (minusDatum n hirr) (blkNodes (n - 1) a),
        matM hn1 t = dMu h hk1 hn1 s}
      mul_mem' := by
        rintro s1 s2 ⟨t1, h1, e1⟩ ⟨t2, h2, e2⟩
        exact ⟨t1 * t2, mul_mem h1 h2, by rw [map_mul, map_mul, e1, e2]⟩
      one_mem' := ⟨1, one_mem _, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro s1 ⟨t1, h1, e1⟩
        refine ⟨t1⁻¹, inv_mem h1, ?_⟩
        have h3 : dMu h hk1 hn1 s1 * dMu h hk1 hn1 s1⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        calc matM hn1 t1⁻¹ = matM hn1 t1⁻¹ * (dMu h hk1 hn1 s1 * dMu h hk1 hn1 s1⁻¹) := by
              rw [h3, mul_one]
          _ = (matM hn1 t1⁻¹ * matM hn1 t1) * dMu h hk1 hn1 s1⁻¹ := by rw [← e1, mul_assoc]
          _ = dMu h hk1 hn1 s1⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul] }
  have htop : (⊤ : Subgroup (spinGroup (quadMinus k F b c))) ≤ S := by
    rw [← minusDatum_iSup_eq_top_of_three_le hirr hk3]
    refine iSup₂_le fun γ hγ s hs => ?_
    have hsupp_of : ∀ γ' : Fin (n - 1) → ℤ, (∀ q : Fin (n - 1), q.val < a → γ' q = 0) →
        ∀ q ∉ blkNodes (n - 1) a, γ' q = 0 := fun γ' hγ' q hq =>
      hγ' q (by by_contra hcon; exact hq (show a ≤ q.val by omega))
    rcases exists_toStdB_eq_of_mem_roots k hγ with ⟨i, j, hij, s0, t0, hγ'⟩ | ⟨i, s0, hγ'⟩
    · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff k hirr hij s0 t0 hγ').mp hs
      have hij' : shiftC h i ≠ shiftC h j := fun e => hij (shiftC_injective h e)
      set γ' : Fin (n - 1) → ℤ := ofStdB (n - 1)
        (Pi.single (shiftC h i) (boolSign s0) + Pi.single (shiftC h j) (boolSign t0)) with hγ'def
      have h' : toStdB (n - 1) γ' =
          Pi.single (shiftC h i) (boolSign s0) + Pi.single (shiftC h j) (boolSign t0) :=
        toStdB_ofStdB (n - 1) _
      refine ⟨(minusFrame n b c).longRoot hij' s0 t0 (.ofAdd y), ?_, ?_⟩
      · refine rootGroup_le_leviM hct (mem_roots_of_toStdB_eq_long n hij' s0 t0 h')
          (hsupp_of γ' (fun q hq => ?_)) (longRoot_mem_minusRootGroup n hirr hij' s0 t0 h' y)
        have e1 : ¬ (shiftC h i).val ≤ q.val := by simp only [shiftC]; omega
        have e2 : ¬ (shiftC h j).val ≤ q.val := by simp only [shiftC]; omega
        rw [hγ'def, ofStdB_pair', if_neg e1, if_neg e2]
        simp
      · exact shift_longRoot h hk1 hn1 hij s0 t0 y
    · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff k hirr i s0 hγ').mp hs
      set γ' : Fin (n - 1) → ℤ := ofStdB (n - 1) (Pi.single (shiftC h i) (boolSign s0)) with hγ'def
      have h' : toStdB (n - 1) γ' = Pi.single (shiftC h i) (boolSign s0) :=
        toStdB_ofStdB (n - 1) _
      refine ⟨twShortRoot n hirr (shiftC h i) s0 (.ofAdd p), ?_, ?_⟩
      · refine rootGroup_le_leviM hct (mem_roots_of_toStdB_eq_short n (shiftC h i) s0 h')
          (hsupp_of γ' (fun q hq => ?_)) (twShortRoot_mem_minusRootGroup n hirr (shiftC h i) s0 h' p)
        have e1 : ¬ (shiftC h i).val ≤ q.val := by simp only [shiftC]; omega
        rw [hγ'def, ofStdB_single, if_neg e1]
      · exact shift_shortRoot h hk1 hn1 hirr i s0 p
  exact htop (Subgroup.mem_top x)


theorem dblock_E2 (hk1 : 1 ≤ k) (hn1 : 1 ≤ n) :
    leviM (minusDatum n hirr) (blkNodes (n - 1) a) ≤
      liftImage (matM (b := b) (c := c) hn1) (dMu (b := b) (c := c) h hk1 hn1) := by
  refine iSup₂_le fun j hj => ?_
  have haj : a ≤ j.val := hj
  have hjlt : j.val < n - 1 := j.isLt
  by_cases hlong : j.val + 1 < n - 1
  · obtain ⟨j0, rfl⟩ : ∃ j0 : Fin (k - 1), shiftC h j0 = j :=
      ⟨⟨j.val - a, by omega⟩, Fin.ext (by simp only [shiftC]; omega)⟩
    have hk0 : j0.val + 1 < k - 1 := by simp only [shiftC] at hlong; omega
    unfold rankOne
    refine sup_le ?_ ?_
    · refine (le_of_eq (minusRootGroup_single_of_lt n hirr hlong)).trans ?_
      rintro _ ⟨m, rfl⟩
      have := shift_longRoot h hk1 hn1 (b := b) (c := c) (succ_ne_of_lt k hk0) true false
        (Multiplicative.toAdd m)
      simp only [ofAdd_toAdd] at this
      exact ⟨_, this.symm⟩
    · refine (le_of_eq (minusRootGroup_neg_single_of_lt n hirr hlong)).trans ?_
      rintro _ ⟨m, rfl⟩
      have := shift_longRoot h hk1 hn1 (b := b) (c := c) (succ_ne_of_lt k hk0).symm true false
        (Multiplicative.toAdd m)
      simp only [ofAdd_toAdd] at this
      exact ⟨_, this.symm⟩
  · obtain ⟨j0, rfl⟩ : ∃ j0 : Fin (k - 1), shiftC h j0 = j :=
      ⟨⟨k - 2, by omega⟩, Fin.ext (by simp only [shiftC]; omega)⟩
    refine (le_of_eq (rankOne_minusRootGroup_of_not_lt n hirr hlong)).trans ?_
    refine sup_le ?_ ?_
    · rintro _ ⟨m, rfl⟩
      have := shift_shortRoot h hk1 hn1 hirr j0 true (Multiplicative.toAdd m)
      simp only [twShortRoot_true, ofAdd_toAdd] at this
      exact ⟨_, this.symm⟩
    · rintro _ ⟨m, rfl⟩
      have := shift_shortRoot h hk1 hn1 hirr j0 false (Multiplicative.toAdd m)
      simp only [twShortRoot_false, ofAdd_toAdd] at this
      exact ⟨_, this.symm⟩

@[expose] noncomputable def blkEquivMinus :
    spinGroup (quadMinus k F b c) ≃*
      ↥(leviM (minusDatum n hirr) (blkNodes (n - 1) a)) :=
  matLiftEquiv (matM (b := b) (c := c) (by omega : 1 ≤ n))
    (dMu h (by omega : 1 ≤ k) (by omega : 1 ≤ n))
    (leviM (minusDatum n hirr) (blkNodes (n - 1) a)) (matM_injective hirr _)
    (dblock_E1 h hirr hk3 (by omega) (by omega)) (dMu_injective h _ _ hirr)
    (dblock_E2 h hirr hk3 (by omega) (by omega))

end DBlockEquiv

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
