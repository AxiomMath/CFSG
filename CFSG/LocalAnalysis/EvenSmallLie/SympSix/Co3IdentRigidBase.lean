
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs

@[expose] public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem eH_ne_one :
    eH ≠ 1 := fun h => by
  have h1 := congrArg (fun x : edgeGroup => orderOf x) h
  simp only [orderOf_one] at h1
  rw [← orderOf_injective edgeGroup.subtype Subtype.val_injective eH] at h1
  have := involutions.2.1
  simp only [coe_subtype] at h1
  rw [show ((eH : edgeGroup) : co3M) = me from rfl, this] at h1
  omega

theorem aH_ne_one :
    aH ≠ 1 := fun h => ma_ne_one (congrArg Subtype.val h)

theorem eH_ne_aH
    : eH ≠ aH := fun h => involutions.2.2 (congrArg Subtype.val h).symm

theorem eaH_ne_one :
    eH * aH ≠ 1 := by
  intro h
  have h2 : aH = eH⁻¹ := eq_inv_of_mul_eq_one_right h
  have he2 : eH⁻¹ = eH := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext; apply Subtype.ext
    simp only [coe_mul, eH, coe_me, coe_one]
    exact co3Z_mul_self
  exact eH_ne_aH (by rw [h2, he2])

theorem eaH_ne_eH
    : eH * aH ≠ eH := fun h => aH_ne_one (by simpa using h)

theorem eaH_ne_aH
    : eH * aH ≠ aH := fun h => eH_ne_one (by simpa using h)

open Classical in
noncomputable def zcH
    (x : edgeGroup) : ℕ :=
  if x = 1 then 0 else if x = eH then 1 else if x = aH then 2 else if x = eH * aH then 3 else 4

theorem rep_eH
    : Rep 276 (genArr 4) (perm eH) := by rw [perm_eH, ← gp_four]; exact rep_g4

theorem rep_aH :
    Rep 276 (genArr 0) (perm aH) := by rw [perm_aH]; exact rep_g0

theorem rep_oneH :
    Rep 276 (idA 276) (perm (1 : edgeGroup)) := rep_idA

theorem eqA_iff_eq
    {t u : Array ℕ} {x w : edgeGroup} (ht : Rep 276 t (perm x))
    (hu : Rep 276 u (perm w)) : eqA 276 t u = true ↔ x = w := by
  rw [eqA_iff ht hu]
  exact perm_injective.eq_iff

theorem zcA_eq
    {t : Array ℕ} {x : edgeGroup} (ht : Rep 276 t (perm x)) : zcA t = zcH x := by
  have h0 := eqA_iff_eq ht rep_oneH
  have h1 := eqA_iff_eq ht rep_eH
  have h2 := eqA_iff_eq ht rep_aH
  have h3 := eqA_iff_eq ht rep_eaH
  unfold zcA zcH
  simp only [h0, h1, h2, h3]

theorem eaH_comm
    : aH * eH = eH * aH := (mem_center_iff.1 aH_mem_center eH).symm

theorem zcH_one :
    zcH 1 = 0 := by simp [zcH]
theorem zcH_eH
    : zcH eH = 1 := by simp [zcH, eH_ne_one]
theorem zcH_aH
    : zcH aH = 2 := by simp [zcH, aH_ne_one, eH_ne_aH.symm]
theorem zcH_eaH
    : zcH (eH * aH) = 3 := by simp [zcH, eaH_ne_one, aH_ne_one, eH_ne_one]
theorem zcH_other
    {x : edgeGroup} (h0 : x ≠ 1) (h1 : x ≠ eH) (h2 : x ≠ aH)
    (h3 : x ≠ eH * aH) : zcH x = 4 := by
  simp [zcH, h0, h1, h2, h3]

theorem zcH_map
    (σ : MulAut edgeGroup) (he : σ eH = aH) (ha : σ aH = eH) (x : edgeGroup) :
    zcH (σ x) = swapZ (zcH x) := by
  have hea : σ (eH * aH) = eH * aH := by rw [map_mul, he, ha, eaH_comm]
  by_cases c0 : x = 1
  · subst c0; rw [map_one, zcH_one]; rfl
  by_cases c1 : x = eH
  · subst c1; rw [he, zcH_aH, zcH_eH]; rfl
  by_cases c2 : x = aH
  · subst c2; rw [ha, zcH_eH, zcH_aH]; rfl
  by_cases c3 : x = eH * aH
  · subst c3; rw [hea, zcH_eaH]; rfl
  have d0 : σ x ≠ 1 := fun h => c0 (σ.injective (h.trans (map_one σ).symm))
  have d1 : σ x ≠ eH := fun h => c2 (σ.injective (h.trans ha.symm))
  have d2 : σ x ≠ aH := fun h => c1 (σ.injective (h.trans he.symm))
  have d3 : σ x ≠ eH * aH := fun h => c3 (σ.injective (h.trans hea.symm))
  rw [zcH_other d0 d1 d2 d3, zcH_other c0 c1 c2 c3]
  rfl

theorem perm_pow
    (x : edgeGroup) (n : ℕ) : perm (x ^ n) = perm x ^ n := by
  rw [← permHom_apply, map_pow]
  rfl

theorem rep_powA
    {t : Array ℕ} {x : edgeGroup} (ht : Rep 276 t (perm x)) :
    ∀ n, Rep 276 (powA t n) (perm (x ^ n))
  | 0 => by rw [pow_zero]; exact rep_oneH
  | n + 1 => by
    rw [powA, pow_succ, show perm (x ^ n * x) = perm (x ^ n) * perm x from rfl]
    exact rep_compA (rep_powA ht n) ht

theorem profOK_of
    {t : Array ℕ} {x : edgeGroup} (ht : Rep 276 t (perm x)) :
    ∀ (es : List ℕ) (acc : Array ℕ) (m : ℕ), Rep 276 acc (perm (x ^ m)) →
      (∀ k < es.length, zcH (x ^ (m + k + 1)) = es[k]!) → profOK t acc es = true
  | [], _, _, _, _ => rfl
  | e :: es, acc, m, hacc, h => by
    have hacc' : Rep 276 (compA 276 acc t) (perm (x ^ (m + 1))) := by
      rw [pow_succ, show perm (x ^ m * x) = perm (x ^ m) * perm x from rfl]
      exact rep_compA hacc ht
    rw [profOK, Bool.and_eq_true, beq_iff_eq, zcA_eq hacc']
    refine ⟨by simpa using h 0 (by simp), profOK_of ht es _ (m + 1) hacc' fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    rw [show m + (k + 1) + 1 = m + 1 + k + 1 by omega] at this
    simpa using this

theorem expProf_eq
    {t : Array ℕ} {x : edgeGroup} (ht : Rep 276 t (perm x)) :
    expProf t = (List.range 24).map fun m => swapZ (zcH (x ^ (m + 1))) := by
  rw [expProf]
  exact List.map_congr_left fun m _ => by rw [zcA_eq (rep_powA ht (m + 1))]

theorem gArrs_size : gArrs.size = 3 := by simp [gArrs]

theorem perm_list_prod
    (l : List edgeGroup) : perm l.prod = (l.map perm).prod := by
  rw [← permHom_apply, map_list_prod]
  rfl

theorem rep_prodA_gH
    {w : List ℕ} (hw : ∀ i ∈ w, i < 3) :
    Rep 276 (prodA 276 gArrs w) (perm (w.map gH).prod) := by
  rw [perm_list_prod, List.map_map]
  exact rep_prodA (x := fun i => perm (gH i)) (fun i hi => rep_gArrs i hi) w
    (fun i hi => by rw [gArrs_size]; exact hw i hi)

theorem testsOK_of
    (σ : MulAut edgeGroup) (he : σ eH = aH) (ha : σ aH = eH)
    {Y : Array (Array ℕ)} (hY : ∀ m < Y.size, Rep 276 Y[m]! (perm (σ (gH m))))
    {ws : List (List ℕ)} (hws : ∀ w ∈ ws, ∀ i ∈ w, i < Y.size ∧ i < 3) :
    testsOK Y (withProf ws) = true := by
  rw [testsOK, List.all_eq_true]
  intro p hp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  have hw' := hws w hw
  set W : edgeGroup := (w.map gH).prod
  have hX := rep_prodA_gH fun i hi => (hw' i hi).2
  have hY' : Rep 276 (prodA 276 Y w) (perm (σ W)) := by
    have : σ W = (w.map fun i => σ (gH i)).prod := by
      rw [map_list_prod, List.map_map]
      rfl
    rw [this, perm_list_prod, List.map_map]
    exact rep_prodA (x := fun i => perm (σ (gH i))) hY w fun i hi => (hw' i hi).1
  rw [expProf_eq hX]
  refine profOK_of hY' _ (idA 276) 0 (by rw [pow_zero]; exact rep_oneH) fun k hk => ?_
  rw [List.length_map, List.length_range] at hk
  rw [zero_add, ← map_pow, zcH_map σ he ha]
  simp [hk, W]

theorem mem_wordsOfLen {k : ℕ} : ∀ {n : ℕ} {w : List ℕ}, w ∈ wordsOfLen k n → ∀ i ∈ w, i < k
  | 0, w, hw, i, hi => by simp [wordsOfLen] at hw; subst hw; simp at hi
  | n + 1, w, hw, i, hi => by
    simp only [wordsOfLen, List.mem_flatMap, List.mem_map, List.mem_range] at hw
    obtain ⟨u, hu, j, hj, rfl⟩ := hw
    rcases List.mem_append.1 hi with hi | hi
    · exact mem_wordsOfLen hu i hi
    · simp only [List.mem_singleton] at hi
      omega

theorem mem_testWords {k L : ℕ} {w : List ℕ} (hw : w ∈ testWords k L) : ∀ i ∈ w, i < k := by
  simp only [testWords, List.mem_filter, List.mem_flatMap] at hw
  obtain ⟨⟨n, -, hn⟩, -⟩ := hw
  exact mem_wordsOfLen hn

theorem conj_apply_central
    {v x : edgeGroup} (hx : x ∈ center edgeGroup) :
    v * x * v⁻¹ = x := by
  rw [mem_center_iff.1 hx v, mul_inv_cancel_right]

theorem planeTest_conj
    {σ : MulAut edgeGroup} (hp : PlaneTest σ) (v : edgeGroup) :
    PlaneTest (σ.trans (MulAut.conj v)) := by
  intro h' hh'
  have key : ∀ x : edgeGroup, (σ.trans (MulAut.conj v)) (h' * x * h'⁻¹) =
      σ ((σ.symm v * h') * x * (σ.symm v * h')⁻¹) := by
    intro x
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    group
  rw [key] at hh'
  obtain ⟨k, hk, hchain⟩ := hp _ hh'
  refine ⟨k, hk, fun x₀ x₁ x₂ hx₀ h1 h2 => ?_⟩
  rw [key] at h1 h2 ⊢
  exact hchain x₀ x₁ x₂ hx₀ h1 h2

theorem gLetters_of_ge {i : ℕ} (hi : 3 ≤ i) : gLetters i = [] := by
  rw [gLetters, List.getD_eq_default _ _ (by simpa [gPaths] using hi)]
  rfl

theorem gH_of_ge
    {i : ℕ} (hi : 3 ≤ i) : gH i = 1 := by
  apply Subtype.ext
  show mWord (gLetters i) = 1
  rw [gLetters_of_ge hi]
  rfl

theorem closure_gH :
    closure (Set.range fun m : Fin 3 => gH m) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨j, -, rfl⟩ := exists_eltH x
  refine treeEval_mem _ (fun i => ?_) _ _ _
  rcases Nat.lt_or_ge i 3 with hi | hi
  · exact subset_closure ⟨⟨i, hi⟩, rfl⟩
  · rw [gH_of_ge hi]
    exact one_mem _

theorem eq_of_gH
    {σ τ : MulAut edgeGroup} (h : ∀ m < 3, σ (gH m) = τ (gH m)) : σ = τ := by
  have hh : (σ : edgeGroup →* edgeGroup) = (τ : edgeGroup →* edgeGroup) :=
    MonoidHom.eq_of_eqOn_dense closure_gH (by
      rintro _ ⟨m, rfl⟩
      exact h m m.2)
  exact MulEquiv.ext fun x => DFunLike.congr_fun hh x

theorem psiGArrs_getElem {m : ℕ} (hm : m < 3) :
    psiGArrs[m]! = compA 276 (genArr 3) (compA 276 gArrs[m]! (genArr 3)) := by
  rw [psiGArrs, getElem!_pos _ m (by simp [gArrs_size, hm]), Array.getElem_map,
    ← getElem!_pos gArrs m (by rw [gArrs_size]; exact hm)]

theorem rep_psiG
    {m : ℕ} (hm : m < 3) : Rep 276 psiGArrs[m]! (perm (psi (gH m))) := by
  rw [psiGArrs_getElem hm, perm_psi, sP_inv, mul_assoc]
  exact rep_compA rep_g3 (rep_compA (rep_gArrs m (by rw [gArrs_size]; exact hm)) rep_g3)

theorem psiForm_spec
    {σ : MulAut edgeGroup} {Y : Array (Array ℕ)}
    (hY : ∀ m < 3, Rep 276 Y[m]! (perm (σ (gH m)))) (h : psiFormOK Y = true) :
    ∃ w : edgeGroup, σ = psi.trans (MulAut.conj w) := by
  unfold psiFormOK anyLt at h
  obtain ⟨i, hi, hall⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  refine ⟨eltH i, eq_of_gH fun m hm => ?_⟩
  have hm' := allLt_spec hall hm
  have e : eltH i * psi (gH m) = σ (gH m) * eltH i :=
    perm_injective (eq_of_eqA (rep_compA (rep_eltH hi) (rep_psiG hm))
      (rep_compA (hY m hm) (rep_eltH hi)) hm')
  simp only [MulEquiv.trans_apply, MulAut.conj_apply]
  rw [e, mul_inv_cancel_right]

theorem rep_sigmaTab
    (σ : MulAut edgeGroup) {Y : Array (Array ℕ)}
    (hY : ∀ m < Y.size, Rep 276 Y[m]! (perm (σ (gH m))))
    (hT : treeTabOK 276 Y hPar hLab (sigmaTab Y) 4608 = true) :
    ∀ j < 4608, Rep 276 (sigmaTab Y)[j]! (perm (σ (eltH j))) := by
  intro j hj
  have h := rep_treeTab hT hY j hj
  have e : perm (σ (eltH j)) = treeEval hPar hLab (fun m => perm (σ (gH m))) j := by
    rw [← permHom_apply, eltH, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply,
      map_treeEval]
    rfl
  rw [e]
  exact h

theorem chainBad_spec {T : Array (Array ℕ)} {h hi : Array ℕ} {j₀ k : ℕ}
    (hc : chainBad T h hi j₀ k = true) :
    ∃ i1 i1' i2 i2' i3 : ℕ, i1 < 4608 ∧ i1' < 4608 ∧ i2 < 4608 ∧ i2' < 4608 ∧ i3 < 4608 ∧
      eqA 276 (compA 276 hList[i1]! h) (compA 276 h hList[j₀]!) = true ∧
      eqA 276 hList[i1']! (compA 276 bcbArr (compA 276 T[i1]! bcbArr)) = true ∧
      eqA 276 (compA 276 hList[i2]! h) (compA 276 h hList[i1']!) = true ∧
      eqA 276 hList[i2']! (compA 276 bcbArr (compA 276 T[i2]! bcbArr)) = true ∧
      eqA 276 (compA 276 hList[i3]! h) (compA 276 h hList[i2']!) = true ∧
      eqA 276 (compA 276 (compA 276 bcbArr (compA 276 T[i3]! bcbArr)) hList[k]!)
        (compA 276 hList[k]! hList[j₀]!) = false := by
  unfold chainBad at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hc
  exact ⟨_, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem bcb_conj_perm
    (x : edgeGroup) {t : Array ℕ} (ht : Rep 276 t (perm x)) :
    Rep 276 (compA 276 bcbArr (compA 276 t bcbArr))
      ((bcbM * (x : co3M) * bcbM⁻¹ : co3M) : Equiv.Perm (Fin 276)) := by
  rw [bcbM_inv, coe_mul, coe_mul, mul_assoc]
  exact rep_compA rep_bcb (rep_compA ht rep_bcb)

theorem conj_eq_of
    {x z h : edgeGroup} {i : ℕ} {tx th : Array ℕ} (hi : i < 4608)
    (hx : Rep 276 tx (perm x)) (hh : Rep 276 th (perm h)) (hix : eltH i = z)
    (he : eqA 276 (compA 276 hList[i]! th) (compA 276 th tx) = true) :
    z = h * x * h⁻¹ := by
  have e : z * h = h * x := by
    rw [← hix]
    exact perm_injective (eq_of_eqA (rep_compA (rep_eltH hi) hh) (rep_compA hh hx) he)
  rw [← e, mul_inv_cancel_right]

theorem not_planeTest
    {σ : MulAut edgeGroup} {Y : Array (Array ℕ)}
    (hY : ∀ m < Y.size, Rep 276 Y[m]! (perm (σ (gH m)))) (hbad : planeBadOK Y = true) :
    ¬ PlaneTest σ := by
  intro hp
  unfold planeBadOK anyLt at hbad
  simp only [Bool.and_eq_true] at hbad
  obtain ⟨hT, hany⟩ := hbad
  have hTr := rep_sigmaTab σ hY hT
  obtain ⟨jh, hjh, hjh'⟩ := List.any_eq_true.1 hany
  rw [List.mem_range] at hjh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hjh'
  obtain ⟨⟨⟨hiy, hiy1⟩, hiy2⟩, hall⟩ := hjh'
  set iy := hIdx (compA 276 hList[jh]! (compA 276 yArr (invCand 276 hList[jh]!)))
  set T := sigmaTab Y
  set h := eltH jh
  have hy : eltH iy = h * yH * h⁻¹ := conj_eq_of hiy rep_yH (rep_eltH hjh) rfl hiy1
  have hσy : σ (h * yH * h⁻¹) = yH := by
    rw [← hy]
    exact perm_injective (eq_of_eqA (hTr iy hiy) rep_yH hiy2)
  obtain ⟨k₀, hk₀, hchain⟩ := hp h hσy
  obtain ⟨kk, hkk, rfl⟩ := exists_eltH k₀
  have hck := (commutesA_iff (rep_eltH hkk) rep_yH).2 hk₀
  have hk := allLt_spec hall hkk
  rw [hck, Bool.not_true, Bool.false_or] at hk
  obtain ⟨j₀, hj₀, hj₀'⟩ := List.any_eq_true.1 hk
  rw [List.mem_range] at hj₀
  rw [Bool.and_eq_true] at hj₀'
  obtain ⟨hcy, hcb⟩ := hj₀'
  obtain ⟨i1, i1', i2, i2', i3, hi1, hi1', hi2, hi2', hi3, e1, e1', e2, e2', e3, efin⟩ :=
    chainBad_spec hcb
  set x₀ := eltH j₀
  have hx₀ : x₀ * yH = yH * x₀ := (commutesA_iff (rep_eltH hj₀) rep_yH).1 hcy
  have c1 : eltH i1 = h * x₀ * h⁻¹ := conj_eq_of hi1 (rep_eltH hj₀) (rep_eltH hjh) rfl e1
  have d1 : ((eltH i1' : edgeGroup) : co3M) = bcbM * σ (h * x₀ * h⁻¹) * bcbM⁻¹ := by
    rw [← c1]
    exact Subtype.ext (eq_of_eqA (rep_eltH hi1') (bcb_conj_perm _ (hTr i1 hi1)) e1')
  have c2 : eltH i2 = h * eltH i1' * h⁻¹ := conj_eq_of hi2 (rep_eltH hi1') (rep_eltH hjh) rfl e2
  have d2 : ((eltH i2' : edgeGroup) : co3M) = bcbM * σ (h * eltH i1' * h⁻¹) * bcbM⁻¹ := by
    rw [← c2]
    exact Subtype.ext (eq_of_eqA (rep_eltH hi2') (bcb_conj_perm _ (hTr i2 hi2)) e2')
  have c3 : eltH i3 = h * eltH i2' * h⁻¹ := conj_eq_of hi3 (rep_eltH hi2') (rep_eltH hjh) rfl e3
  have hc := hchain x₀ (eltH i1') (eltH i2') hx₀ d1 d2
  rw [← c3] at hc
  have hrep : Rep 276 (compA 276 bcbArr (compA 276 T[i3]! bcbArr))
      (perm (eltH kk * x₀ * (eltH kk)⁻¹)) := by
    have := bcb_conj_perm _ (hTr i3 hi3)
    rw [hc] at this
    exact this
  have hfin : eqA 276 (compA 276 (compA 276 bcbArr (compA 276 T[i3]! bcbArr)) hList[kk]!)
      (compA 276 hList[kk]! hList[j₀]!) = true := by
    rw [eqA_iff (rep_compA hrep (rep_eltH hkk)) (rep_compA (rep_eltH hkk) (rep_eltH hj₀))]
    show perm (eltH kk * x₀ * (eltH kk)⁻¹ * eltH kk) = perm (eltH kk * x₀)
    rw [inv_mul_cancel_right]
  rw [hfin] at efin
  exact absurd efin (by decide)

theorem edgePerm_mul
    (a b : edgeGroup) :
    perm (a * b) = perm a * perm b := rfl

theorem mul_eq_of_mul_hom {K G : Type*} [Mul K] [Mul G] {p : K → G} (hinj : Function.Injective p)
    (hmul : ∀ a b, p (a * b) = p a * p b) {a b c d : K} (h : p a * p b = p c * p d) :
    a * b = c * d :=
  hinj (by rw [hmul, hmul]; exact h)

theorem rep_arr1 {n : ℕ} {a : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)} (h0 : Rep n a (f 0)) :
    ∀ m < (#[a] : Array (Array ℕ)).size, Rep n (#[a] : Array (Array ℕ))[m]! (f m) := by
  intro m hm
  have hm1 : m < 1 := by simpa using hm
  interval_cases m
  exact h0

theorem rep_arr2 {n : ℕ} {a b : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)} (h0 : Rep n a (f 0))
    (h1 : Rep n b (f 1)) :
    ∀ m < (#[a, b] : Array (Array ℕ)).size, Rep n (#[a, b] : Array (Array ℕ))[m]! (f m) := by
  intro m hm
  have hm2 : m < 2 := by simpa using hm
  interval_cases m
  · exact h0
  · exact h1

theorem rep_arr3 {n : ℕ} {a b c : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)} (h0 : Rep n a (f 0))
    (h1 : Rep n b (f 1)) (h2 : Rep n c (f 2)) :
    ∀ m < (#[a, b, c] : Array (Array ℕ)).size, Rep n (#[a, b, c] : Array (Array ℕ))[m]! (f m) := by
  intro m hm
  have hm3 : m < 3 := by simpa using hm
  interval_cases m
  · exact h0
  · exact h1
  · exact h2

end CFSG.EvenSmallLie.SympSix.Co3Ident
