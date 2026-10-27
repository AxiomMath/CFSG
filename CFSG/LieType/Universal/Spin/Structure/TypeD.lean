module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Steinberg.Extras
import CFSG.LieType.Universal.Spin.Structure.Levels
import CFSG.LieType.Universal.Spin.Structure.Spinor
import CFSG.LieType.Universal.Spin.Structure.Entries

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.Steinberg

variable {n : ℕ} {K : Type} [Field K]

private def idxP (m : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl m
  | false => .inr m

private def lvlP : Fin n ⊕ Fin n → ℤ
  | .inl m => (n : ℤ) - 1 - m
  | .inr m => -((n : ℤ) - 1 - m)

private theorem lvlP_idxP (m : Fin n) (r : Bool) :
    lvlP (idxP m r) = boolSign r * ((n : ℤ) - 1 - m) := by
  cases r <;> simp [lvlP, idxP]

private theorem idxP_surj (a : Fin n ⊕ Fin n) : ∃ m r, idxP m r = a := by
  rcases a with m | m
  · exact ⟨m, true, rfl⟩
  · exact ⟨m, false, rfl⟩

private theorem isCoord_plusFrame (hn : 3 ≤ n) :
    (plusFrame n K hn).IsCoord (idxP (n := n)) where
  idx_inj {m r m' r'} h := by
    cases r <;> cases r' <;> simp_all [idxP]
  vec_eq m r := by cases r <;> rfl
  polar_vec v m r := by
    cases r
    · exact polar_quadPlus_single_inr n K v m
    · exact polar_quadPlus_single_inl n K v m

private theorem idxP_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) : idxP i s ≠ idxP j t := by
  intro h
  cases s <;> cases t <;> simp_all [idxP]

section Roots

variable (hn : 3 ≤ n)

include hn in
private theorem lvl_sub₁ {γ : Fin n → ℤ} {i j : Fin n} {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    lvlP (idxP i s) - lvlP (idxP j (!t)) = ht γ := by
  rw [ht_of_toStdD_eq_add n (by omega) hstd, lvlP_idxP, lvlP_idxP, boolSign_not]
  ring

include hn in
private theorem lvl_sub₂ {γ : Fin n → ℤ} {i j : Fin n} {s t : Bool}
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    lvlP (idxP j t) - lvlP (idxP i (!s)) = ht γ := by
  rw [ht_of_toStdD_eq_add n (by omega) hstd, lvlP_idxP, lvlP_idxP, boolSign_not]
  ring

include hn in
private theorem idBelow_of_mem (ε : ℤ) {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅) {x : spinGroup (quadPlus n K)}
    (hx : x ∈ plusRootGroup n K hn γ) :
    IdBelow (fun a => ε * lvlP a) (ε * ht γ) (spinMat (quadPlus n K) x) := by
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  have hF := isCoord_plusFrame (K := K) hn
  rw [hX] at hx
  obtain ⟨c, rfl⟩ := hx
  intro a b hab
  change ε * lvlP a - ε * lvlP b < ε * ht γ at hab
  rw [← mul_sub] at hab
  have h1 : ¬(a = idxP i s ∧ b = idxP j (!t)) := by
    rintro ⟨rfl, rfl⟩
    rw [lvl_sub₁ hn hstd] at hab
    exact lt_irrefl _ hab
  have h2 : ¬(a = idxP j t ∧ b = idxP i (!s)) := by
    rintro ⟨rfl, rfl⟩
    rw [lvl_sub₂ hn hstd] at hab
    exact lt_irrefl _ hab
  rw [← ofAdd_toAdd c, hF.spinMat_longRoot hij s t, ite_eq_right h1, ite_eq_right h2, add_zero,
    sub_zero]

include hn in
private theorem exists_pos (ε : ℤ) {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅) :
    ∃ a b : Fin n ⊕ Fin n, a ≠ b ∧ ε * lvlP a - ε * lvlP b ≤ ε * ht γ ∧
      (∀ δ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅, δ ≠ γ →
        ∀ x ∈ plusRootGroup n K hn δ, spinMat (quadPlus n K) x a b = 0) ∧
      ∀ x ∈ plusRootGroup n K hn γ, ∀ y ∈ plusRootGroup n K hn γ,
        spinMat (quadPlus n K) x a b = spinMat (quadPlus n K) y a b → x = y := by
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  have hF := isCoord_plusFrame (K := K) hn
  have hab : idxP i s ≠ idxP j (!t) := idxP_ne hij s (!t)
  refine ⟨idxP i s, idxP j (!t), hab, by rw [← mul_sub, lvl_sub₁ hn hstd], ?_, ?_⟩
  · intro δ hδ hne x hx
    obtain ⟨i', j', hij', s', t', hstd', hX'⟩ := exists_plusRootGroup_eq (K := K) hn hδ
    rw [hX'] at hx
    obtain ⟨c, rfl⟩ := hx
    have h1 : ¬(idxP i s = idxP i' s' ∧ idxP j (!t) = idxP j' (!t')) := by
      rintro ⟨e1, e2⟩
      obtain ⟨rfl, rfl⟩ := hF.idx_inj e1
      obtain ⟨rfl, e3⟩ := hF.idx_inj e2
      obtain rfl := Bool.not_inj e3
      exact hne (toStdD_injective n (hstd'.trans hstd.symm))
    have h2 : ¬(idxP i s = idxP j' t' ∧ idxP j (!t) = idxP i' (!s')) := by
      rintro ⟨e1, e2⟩
      obtain ⟨rfl, rfl⟩ := hF.idx_inj e1
      obtain ⟨rfl, e3⟩ := hF.idx_inj e2
      obtain rfl := Bool.not_inj e3
      exact hne (toStdD_injective n (hstd'.trans (hstd.trans (add_comm _ _)).symm))
    rw [← ofAdd_toAdd c, hF.spinMat_longRoot hij' s' t', Matrix.one_apply_ne hab,
      ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
  · intro x hx y hy hxy
    rw [hX] at hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    have h1 : idxP i s = idxP i s ∧ idxP j (!t) = idxP j (!t) := ⟨rfl, rfl⟩
    have h2 : ¬(idxP i s = idxP j t ∧ idxP j (!t) = idxP i (!s)) :=
      fun h => idxP_ne hij s t h.1
    rw [← ofAdd_toAdd c, ← ofAdd_toAdd d, hF.spinMat_longRoot hij s t,
      hF.spinMat_longRoot hij s t, ite_eq_left h1, ite_eq_left h1, ite_eq_right h2,
      ite_eq_right h2] at hxy
    have hcd : Multiplicative.toAdd c = Multiplicative.toAdd d := by simpa using hxy
    rw [Multiplicative.toAdd.injective hcd]

include hn in
private theorem prodInjectiveD (ε : ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅)
    (hpos : ∀ γ ∈ L, 0 < ε * ht γ) (hsort : L.Pairwise fun γ δ => ε * ht γ ≤ ε * ht δ) :
    ProdInjectiveFor (plusRootGroup n K hn) L :=
  prodInjectiveFor_of_idBelow (fun a => ε * lvlP a) (spinMat (quadPlus n K))
    (plusRootGroup n K hn) (fun γ => ε * ht γ) L hL hpos
    (fun γ hγ _ hx => idBelow_of_mem hn ε (hroots γ hγ) hx)
    (fun γ hγ => by
      obtain ⟨a, b, h1, h2, h3, h4⟩ := exists_pos (K := K) hn ε (hroots γ hγ)
      exact ⟨a, b, h1, h2, fun δ hδ hne x hx => h3 δ (hroots δ hδ) hne x hx, h4⟩)
    hsort

include hn in
private theorem idBelow_of_mem_iSup (ε : ℤ) (P : Set (Fin n → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅ ∧ 0 < ε * ht γ)
    {x : spinGroup (quadPlus n K)} (hx : x ∈ ⨆ γ ∈ P, plusRootGroup n K hn γ) :
    IdBelow (fun a => ε * lvlP a) 1 (spinMat (quadPlus n K) x) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : spinGroup (quadPlus n K) =>
    IdBelow (fun a => ε * lvlP a) 1 (spinMat (quadPlus n K) x)) (fun γ y hy => ?_) ?_
    fun y z hy hz => ?_
  · exact (idBelow_of_mem hn ε (hP γ.1 γ.2).1 hy).mono (by have := (hP γ.1 γ.2).2; omega)
  · rw [map_one]
    exact idBelow_one _ 1
  · rw [map_mul]
    exact idBelow_mul _ one_pos hy hz

private noncomputable abbrev omegaP : CliffordAlgebra (quadPlus n K) :=
  (plusFrame n K hn).spinor fun _ => true

include hn in
private theorem posPart_le_stab :
    (⨆ γ ∈ {γ | γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅ ∧ 0 < ht γ},
      plusRootGroup n K hn γ) ≤ stabSubgroup (quadPlus n K) (omegaP (K := K) hn) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ.1
  rw [hX]
  rintro _ ⟨c, rfl⟩
  rw [mem_stabSubgroup, ← ofAdd_toAdd c]
  refine (plusFrame n K hn).coe_longRoot_mul_spinor _ hij ?_ _
  show s = true ∨ t = true
  by_contra h
  rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at h
  have hht := ht_of_toStdD_eq_add n (by omega) hstd
  rw [h.1, h.2, boolSign_false] at hht
  have h0 : 0 < ht γ := hγ.2
  have hi := i.isLt
  have hj := j.isLt
  omega

include hn in
private theorem eq_one_of_mem_posPart {x : spinGroup (quadPlus n K)}
    (hx : x ∈ ⨆ γ ∈ {γ | γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅ ∧ 0 < ht γ},
      plusRootGroup n K hn γ)
    (h : spinMat (quadPlus n K) x = 1) : x = 1 :=
  eq_one_of_mul_eq_self _
    (eq_one_or_eq_neg_one_of_spinAction_eq_one n K x (spinAction_eq_one_of_spinMat_eq_one h))
    ((plusFrame n K hn).spinor_ne_zero _) (posPart_le_stab hn hx)

end Roots

section Torus

variable (hn : 3 ≤ n)

private theorem spinAction_torusD_single (k : Fin n) (τ : Kˣ) (m : Fin n) (r : Bool) :
    spinAction (quadPlus n K) (torusD K hn k τ) (Pi.single (idxP m r) 1) =
      ((τ ^ longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m r : Kˣ) : K) •
        Pi.single (idxP m r) 1 := by
  rw [← (isCoord_plusFrame (K := K) hn).vec_eq]
  exact spinAction_torusD K hn k τ m r

private theorem isDiag_torusD (k : Fin n) (τ : Kˣ) :
    (spinMat (quadPlus n K) (torusD K hn k τ)).IsDiag := by
  refine isDiag_spinMat fun b => ?_
  obtain ⟨m, r, rfl⟩ := idxP_surj b
  exact ⟨_, spinAction_torusD_single hn k τ m r⟩

private theorem isDiag_of_mem_iSup {x : spinGroup (quadPlus n K)}
    (hx : x ∈ ⨆ k, (torusD K hn k).range) : (spinMat (quadPlus n K) x).IsDiag := by
  refine Subgroup.iSup_induction _ hx (C := fun x : spinGroup (quadPlus n K) =>
    (spinMat (quadPlus n K) x).IsDiag) (fun k y hy => ?_) ?_ fun y z hy hz => ?_
  · obtain ⟨τ, rfl⟩ := hy
    exact isDiag_torusD hn k τ
  · rw [map_one]
    exact Matrix.isDiag_one
  · rw [map_mul]
    exact isDiag_mul hy hz

private theorem sum_longCoroot (k i j : Fin n) (t : Bool) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), longCoroot i j true t m true =
      (if i.val ≤ k.val then 1 else 0) + (if j.val ≤ k.val then boolSign t else 0) := by
  simp only [longCoroot, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases t <;> simp

private theorem sum_corootD {k : Fin n} (hk : k.val + 2 < n) (j : Fin n) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      longCoroot (rootIdxD n j) (rootIdxD' n j) true (rootSignD n j) m true =
        if j = k then 1 else 0 := by
  rw [sum_longCoroot]
  by_cases hj : j.val + 1 < n
  · have e1 : (rootIdxD n j).val = j.val := by rw [rootIdxD_of_lt n hj]
    have e2 : (rootIdxD' n j).val = j.val + 1 := by rw [rootIdxD'_of_lt n hj]
    rw [e1, e2, rootSignD_of_lt n hj, boolSign_false]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rw [ite_eq_right hjk]
      split_ifs <;> omega
  · rw [val_rootIdxD_of_not_lt n hj, val_rootIdxD'_of_not_lt n hj,
      ite_eq_right (fun h => by omega : ¬(n - 2 ≤ k.val)),
      ite_eq_right (fun h => by omega : ¬(n - 1 ≤ k.val)),
      ite_eq_right (fun h => by rw [h] at hj; omega : ¬j = k)]
    simp

private theorem prod_diag_torusD (k j : Fin n) (τ : Kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      spinMat (quadPlus n K) (torusD K hn j τ) (idxP m true) (idxP m true) =
        ((τ ^ ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
          longCoroot (rootIdxD n j) (rootIdxD' n j) true (rootSignD n j) m true : Kˣ) : K) := by
  rw [← prod_zpow_eq_zpow_sum, Units.coe_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [spinMat_apply_of_eq_smul (spinAction_torusD_single hn j τ m true), ite_eq_left rfl]

private def spinSigns (k : Fin n) (m : Fin n) : Bool :=
  if m.val + 1 = n then rootSignD n k else true

include hn in
private theorem spinSigns_rootIdxD (k j : Fin n) : spinSigns k (rootIdxD n j) = true := by
  have : (rootIdxD n j).val + 1 ≠ n := by
    by_cases hj : j.val + 1 < n
    · rw [rootIdxD_of_lt n hj]
      omega
    · rw [val_rootIdxD_of_not_lt n hj]
      omega
  simp [spinSigns, this]

include hn in
private theorem coe_torusD_mul_spinor_self {k : Fin n} (hk : ¬k.val + 2 < n) (τ : Kˣ) :
    (torusD K hn k τ : CliffordAlgebra (quadPlus n K)) * (plusFrame n K hn).spinor (spinSigns k) =
      (τ : K) • (plusFrame n K hn).spinor (spinSigns k) := by
  refine (plusFrame n K hn).coe_longTorus_mul_spinor_of_eq _ _ (spinSigns_rootIdxD hn k k).symm ?_ τ
  have : (rootIdxD' n k).val + 1 = n := by
    by_cases h : k.val + 1 < n
    · rw [rootIdxD'_of_lt n h]
      simp only
      omega
    · rw [val_rootIdxD'_of_not_lt n h]
      omega
  simp [spinSigns, this]

include hn in
private theorem coe_torusD_mul_spinor_of_ne {k j : Fin n} (hk : ¬k.val + 2 < n) (hjk : j ≠ k)
    (τ : Kˣ) :
    (torusD K hn j τ : CliffordAlgebra (quadPlus n K)) * (plusFrame n K hn).spinor (spinSigns k) =
      (plusFrame n K hn).spinor (spinSigns k) := by
  refine (plusFrame n K hn).coe_longTorus_mul_spinor_of_ne _ _
    (Or.inl ⟨(spinSigns_rootIdxD hn k j).symm, ?_⟩) τ
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  by_cases hj : j.val + 1 < n
  · rw [rootIdxD'_of_lt n hj, rootSignD_of_lt n hj]
    simp only [spinSigns]
    split_ifs with h
    · rw [rootSignD_of_not_lt n (by omega)]
      decide
    · decide
  · have h1 : (rootIdxD' n j).val + 1 = n := by
      rw [val_rootIdxD'_of_not_lt n hj]
      omega
    simp only [spinSigns, h1, ite_true]
    rw [rootSignD_of_not_lt n hj, rootSignD_of_lt n (by omega)]
    decide

end Torus

variable (n K)

theorem plusDatum_prodInjective_pos (hn : 3 ≤ n) :
    ∀ L : List (Fin (plusDatum n K hn).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (plusDatum n K hn).roots ∧ 0 < ht γ ∧
        ∀ δ ∈ (plusDatum n K hn).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor (plusDatum n K hn).rootGroup L := by
  intro L hL hmem hsort
  refine prodInjectiveD hn 1 L hL (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ?_) ?_
  · have : 0 < ht (ι := Fin n) γ := ((hmem γ).1 hγ).2.1
    omega
  · refine hsort.imp fun {γ δ} h => ?_
    have h' : ht (ι := Fin n) γ ≤ ht (ι := Fin n) δ := h
    omega

theorem plusDatum_prodInjective_neg (hn : 3 ≤ n) :
    ∀ L : List (Fin (plusDatum n K hn).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (plusDatum n K hn).roots ∧ ht γ < 0 ∧
        ∀ δ ∈ (plusDatum n K hn).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht δ ≤ ht γ) → ProdInjectiveFor (plusDatum n K hn).rootGroup L := by
  intro L hL hmem hsort
  refine prodInjectiveD hn (-1) L hL (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ?_) ?_
  · have : ht (ι := Fin n) γ < 0 := ((hmem γ).1 hγ).2.1
    omega
  · refine hsort.imp fun {γ δ} h => ?_
    have h' : ht (ι := Fin n) δ ≤ ht (ι := Fin n) γ := h
    omega

theorem plusDatum_posPart_inf_negPart (hn : 3 ≤ n) :
    (⨆ γ ∈ {γ | γ ∈ (plusDatum n K hn).roots ∧ 0 < ht γ}, (plusDatum n K hn).rootGroup γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ (plusDatum n K hn).roots ∧ ht γ < 0}, (plusDatum n K hn).rootGroup γ) =
        ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  have h1 := idBelow_of_mem_iSup hn 1 _
    (fun γ hγ => ⟨hγ.1, by have : 0 < ht (ι := Fin n) γ := hγ.2; omega⟩) hxp
  have h2 := idBelow_of_mem_iSup hn (-1) _
    (fun γ hγ => ⟨hγ.1, by have : ht (ι := Fin n) γ < 0 := hγ.2; omega⟩) hxn
  exact eq_one_of_mem_posPart hn hxp (eq_one_of_idBelow_one_of_idBelow_neg_one _ h1 h2)

theorem plusDatum_torus_iSupIndep (hn : 3 ≤ n) :
    iSupIndep (fun k : Fin (plusDatum n K hn).rank => (torusD K hn k).range) := by
  show iSupIndep fun k : Fin n => (torusD K hn k).range
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  obtain ⟨τ, rfl⟩ := hxk
  suffices hτ : τ = 1 by rw [hτ, map_one]
  by_cases hk : k.val + 2 < n
  ·
    have key : (spinMat (quadPlus n K) (torusD K hn k τ)).IsDiag ∧
        ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
          spinMat (quadPlus n K) (torusD K hn k τ) (idxP m true) (idxP m true) = 1 := by
      rw [iSup_subtype'] at hx
      refine Subgroup.iSup_induction _ hx (C := fun y : spinGroup (quadPlus n K) =>
        (spinMat (quadPlus n K) y).IsDiag ∧
          ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
            spinMat (quadPlus n K) y (idxP m true) (idxP m true) = 1)
        (fun j y hy => ?_) ?_ fun y z hy hz => ?_
      · obtain ⟨σ, rfl⟩ := hy
        refine ⟨isDiag_torusD hn j.1 σ, ?_⟩
        rw [prod_diag_torusD, sum_corootD hk, ite_eq_right j.2, zpow_zero, Units.val_one]
      · rw [map_one]
        exact ⟨Matrix.isDiag_one, Finset.prod_eq_one fun m _ => Matrix.one_apply_eq _⟩
      · rw [map_mul]
        refine ⟨isDiag_mul hy.1 hz.1, ?_⟩
        rw [prod_diag_mul_of_isDiag _ (fun m => idxP m true) hy.1 hz.1, hy.2, hz.2, one_mul]
    have h := key.2
    rw [prod_diag_torusD, sum_corootD hk, ite_eq_left rfl, zpow_one] at h
    exact Units.val_eq_one.mp h
  ·
    have hfix : (torusD K hn k τ : CliffordAlgebra (quadPlus n K)) *
        (plusFrame n K hn).spinor (spinSigns k) = (plusFrame n K hn).spinor (spinSigns k) := by
      have hle : (⨆ (j : Fin n) (_ : j ≠ k), (torusD K hn j).range) ≤
          stabSubgroup (quadPlus n K) ((plusFrame n K hn).spinor (spinSigns k)) := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨σ, rfl⟩
        exact coe_torusD_mul_spinor_of_ne hn hk hj σ
      exact hle hx
    rw [coe_torusD_mul_spinor_self hn hk] at hfix
    have h0 : ((τ : K) - 1) • (plusFrame n K hn).spinor (spinSigns k) = 0 := by
      rw [sub_smul, hfix, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact Units.ext (sub_eq_zero.mp h)
    · exact absurd h ((plusFrame n K hn).spinor_ne_zero _)

theorem plusDatum_torus_inf_posPart (hn : 3 ≤ n) :
    (⨆ i : Fin (plusDatum n K hn).rank, (torusD K hn i).range) ⊓
      (⨆ γ ∈ {γ | γ ∈ (plusDatum n K hn).roots ∧ 0 < ht γ}, (plusDatum n K hn).rootGroup γ) =
        ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_posPart hn hxp (eq_one_of_isDiag_of_idBelow (fun a => 1 * lvlP a)
    (isDiag_of_mem_iSup hn hxt) ?_)
  exact idBelow_of_mem_iSup hn 1 _
    (fun γ hγ => ⟨hγ.1, by have : 0 < ht (ι := Fin n) γ := hγ.2; omega⟩) hxp

end CFSG.LieType.Universal.Spin
