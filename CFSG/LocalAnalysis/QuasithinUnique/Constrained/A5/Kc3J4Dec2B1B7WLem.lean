module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7W
public import CFSG.Sporadic.J4.QT2LocBasicRep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Fix

public section

namespace CFSG.QuasithinUnique.A5.B7

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4.QT2.B7 CFSG.Sporadic.J4.QT2A Matrix

theorem cntFix_root_b
    (hM : MatFacts) (hF : J4Basic) {m' : J} {t : List ℕ} (hA : Acts m' t) :
    cntFix RIn w₀ m' = (List.range 2048).countP fun c => actT t c == c := by
  have hRIn : ∀ x : J, RIn w₀ x ↔ x ∈ Eg uJ 11 := fun x => by
    have := RIn_rep_b hM hF.stab (u := 1) (r := w₀) (by simp) x
    simpa using this
  have hset : {x : J | RIn w₀ x ∧ x * m' = m' * x} =
      eta uJ 11 '' {c : ℕ | c < 2048 ∧ actT t c = c} := by
    ext x
    constructor
    · rintro ⟨hx, hcomm⟩
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 ((hRIn x).1 hx)
      have hc' : c < 2048 := by simpa using hc
      refine ⟨c, ⟨hc', ?_⟩, rfl⟩
      have h1 := hA.2 c hc
      have h2 : m' * eta uJ 11 c * m'⁻¹ = eta uJ 11 c := by
        rw [← hcomm]
        group
      rw [h2] at h1
      exact (eta_inj hM _ hc' _ (by simpa using actT_lt hA.1 c) h1).symm
    · rintro ⟨c, ⟨hc, hfix⟩, rfl⟩
      refine ⟨(hRIn _).2 (eta_mem_Eg 11 le_rfl c), ?_⟩
      have h1 := hA.2 c (by simpa using hc)
      rw [hfix] at h1
      calc eta uJ 11 c * m' = (m' * eta uJ 11 c * m'⁻¹) * m' := by rw [h1]
        _ = m' * eta uJ 11 c := by group
  unfold cntFix
  rw [hset, Set.InjOn.ncard_image (fun c hc d hd e => eta_inj hM c hc.1 d hd.1 e)]
  have hfin : {c : ℕ | c < 2048 ∧ actT t c = c} =
      ↑((Finset.range 2048).filter fun c => actT t c = c) := by
    ext c
    simp
  rw [hfin, Set.ncard_coe_finset]
  have := Nat.count_eq_card_filter_range (fun c => actT t c = c) 2048
  rw [← this, Nat.count]
  apply List.countP_congr
  intro c _
  simp

theorem cntRowsT_checks {K Ki M Mi : Array V2} {t : List ℕ} {n : ℕ}
    (h : cntRowsT K Ki M Mi t = some n) :
    eqRows (mulRows K Ki) idRows = true ∧ eqRows (mulRows M Mi) idRows = true := by
  unfold cntRowsT at h
  by_cases hc : (eqRows (mulRows K Ki) idRows && eqRows (mulRows M Mi) idRows) = true
  · simpa using hc
  · simp [hc] at h

theorem cntRowsT_sound
    (hM : MatFacts) (hF : J4Basic) {K Ki M Mi : Array V2} {k m : J}
    (hK : Mx k = rowsMatrix K) (hMm : Mx m = rowsMatrix M) {t : List ℕ} {n : ℕ}
    (h : cntRowsT K Ki M Mi t = some n) : cntFix RIn (k • w₀) m = n := by
  obtain ⟨hKi, hMi⟩ := cntRowsT_checks h
  have hKi' : Mx k⁻¹ = rowsMatrix Ki := Mx_inv_rows hK hKi
  have hMi' : Mx m⁻¹ = rowsMatrix Mi := Mx_inv_rows hMm hMi
  have hc : (eqRows (mulRows K Ki) idRows && eqRows (mulRows M Mi) idRows) = true := by
    simp [hKi, hMi]
  unfold cntRowsT at h
  simp only [hc, ite_true] at h
  split_ifs at h with hok
  · have hx : Mx (k⁻¹ * m * k) = rowsMatrix (mulRows (mulRows Ki M) K) := by
      rw [map_mul, map_mul, hKi', hMm, hK, rowsMatrix_mulRows, rowsMatrix_mulRows]
    have hxi : Mx (k⁻¹ * m * k)⁻¹ = rowsMatrix (mulRows (mulRows Ki Mi) K) := by
      have e : (k⁻¹ * m * k)⁻¹ = k⁻¹ * m⁻¹ * k := by group
      rw [e, map_mul, map_mul, hKi', hMi', hK, rowsMatrix_mulRows, rowsMatrix_mulRows]
    rw [cntFix_conj RIn RIn_conj k w₀ m, cntFix_root_b hM hF (acts_of_actTabOK hM hx hxi hok)]
    exact Option.some.inj h

theorem isGoodPt_baseW
    (hM : MatFacts) (hF : J4Basic) {t g0 : J} {T0 : Array V2} {c0 : ℕ}
    (hξ : Mx fiveElt = rowsMatrix fiveRows) (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv)
    (hT : Mx t = rowsMatrix T0) (hfac : B7Facts t g0 c0) (hB : baseP T0) :
    IsGoodPt (Eg (vEl t) 4) RIn w₀ := by
  intro m hm hm1
  have hV := Mx_vEl hξ hξi hT
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff hfac.elem).1 hm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm1 (eta_zero _ _)
  have hc16 : c < 16 := by simpa using hc
  have hMm : Mx (eta (vEl t) 4 c) = rowsMatrix (prodRows (vRows T0) c) := Mx_eta_of hV 4 le_rfl c
  rcases hB c (by omega) hc16 with h1 | ⟨tt, h1⟩
  · exfalso
    apply hm1
    apply Mx_injective
    rw [hMm, eqRows_iff.1 h1, rowsMatrix_idRows, map_one]
  · have := cntRowsT_sound hM hF (k := 1) (m := eta (vEl t) 4 c) (K := idRows) (Ki := idRows)
      (by rw [map_one, rowsMatrix_idRows]) hMm h1
    rwa [one_smul] at this

theorem candOKW_sound
    (hM : MatFacts) (hF : J4Basic) {t : J} {T0 : Array V2}
    (hξ : Mx fiveElt = rowsMatrix fiveRows) (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv)
    (hT : Mx t = rowsMatrix T0) {qv : V2} {w : B7Wit}
    (h : candOKW (vRows T0) qv w = true) :
    fiveElt • toRow qv.toVec = toRow qv.toVec ∨
      ∃ m ∈ Eg (vEl t) 4, m ≠ 1 ∧ cntFix RIn (toRow qv.toVec) m ≠ 128 := by
  unfold candOKW at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨⟨⟨hk, hk1⟩, hk2⟩, hMne⟩, hcnt⟩
  · left
    exact smul_fix_of_apply hξ qv (toVec_eq_of_differs_false h)
  · right
    rcases hcr : cntRowsT (wR w.kw) (invRows (wR w.kw)) (prodRows (vRows T0) w.k)
      (prodRows (vRows T0) w.k) w.t with _ | n
    · rw [hcr] at hcnt
      simp at hcnt
    · rw [hcr] at hcnt
      have hK : Mx (el5 w.kw) = rowsMatrix (wR w.kw) := Mx_el5 hM w.kw
      obtain ⟨hKi, -⟩ := cntRowsT_checks hcr
      have hKi' := Mx_inv_rows hK hKi
      have hq : el5 w.kw • w₀ = toRow qv.toVec := by
        have e1 := smul_toRow_rows hKi' rootV
        rw [toVec_eq_of_differs_false hk] at e1
        exact e1
      have hV := Mx_vEl hξ hξi hT
      have hMm : Mx (eta (vEl t) 4 w.k) = rowsMatrix (prodRows (vRows T0) w.k) :=
        Mx_eta_of hV 4 le_rfl w.k
      refine ⟨eta (vEl t) 4 w.k, eta_mem_Eg 4 le_rfl w.k, ?_, ?_⟩
      · intro h1
        rw [h1, map_one] at hMm
        exact rowsMatrix_ne_one_of_neId hMne hMm.symm
      · rw [← hq, cntRowsT_sound hM hF hK hMm hcr]
        simpa using hcnt

theorem survP_sound
    (hM : MatFacts) (hF : J4Basic) {t : J} {T0 : Array V2} {g0w : List Int}
    (hξ : Mx fiveElt = rowsMatrix fiveRows) (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv)
    (hT : Mx t = rowsMatrix T0) (hsq : ∀ j < 4, vEl t j * vEl t j = 1) {u : V2}
    (hS : survP T0 g0w u)
    (hfix : ∀ j < 4, vEl t j • toRow (frApply (frTable (invRows (wR g0w))) u).toVec =
      toRow (frApply (frTable (invRows (wR g0w))) u).toVec) :
    fiveElt • toRow (frApply (frTable (invRows (wR g0w))) u).toVec =
        toRow (frApply (frTable (invRows (wR g0w))) u).toVec ∨
      ∃ m ∈ Eg (vEl t) 4, m ≠ 1 ∧
        cntFix RIn (toRow (frApply (frTable (invRows (wR g0w))) u).toVec) m ≠ 128 := by
  have hfb := fixedBy_of_fix hξ hξi hT hsq hfix
  rcases hS with h | ⟨w, hw⟩
  · rw [hfb] at h
    exact absurd h (by decide)
  · exact candOKW_sound hM hF hξ hξi hT hw

theorem tree_mem_Dlt (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) {P : List V2}
    (hP : B7Tree (pathVec (repPaths.getD ℓ [])) P) :
    ∀ k < P.length, toRow (P[k]!).toVec ∈ Dlt ℓ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e : P[0]! = pathVec (repPaths.getD ℓ []) := by
        rw [getElem!_pos P 0 hk]
        exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hP.1)
      rw [e, ← rep_toVec hM hℓ]
      exact ⟨1, Hj.one_mem, (one_smul _ _).symm⟩
    · obtain ⟨j, hj, g, hg, e⟩ := hP.2 k hk0 hk
      obtain ⟨h, hh, hv⟩ := ih j hj (by omega)
      refine ⟨(xJ g)⁻¹ * h, Hj.mul_mem (Hj.inv_mem (xJ_mem hg)) hh, ?_⟩
      rw [mul_smul, ← hv, e, ← ofRow_inj, xJ_inv_smul hM]
      change (frApply locTabs[g]! P[j]!).toVec = (P[j]!).toVec ᵥ* _
      rw [locTabs_get hM hg, frApply_toVec_eq_vecMul]

theorem orbit_cover (hM : MatFacts) {ℓ n : ℕ} (hℓ : ℓ < 7) {P : List V2}
    (hP : B7Tree (pathVec (repPaths.getD ℓ [])) P) (hnd : P.Nodup) (hlen : P.length = n)
    (hwf : ∀ p ∈ P, p.wf = true) (hcard : (Dlt ℓ).ncard ≤ n) :
    ∀ v ∈ Dlt ℓ, ∃ p ∈ P, v = toRow p.toVec := by
  classical
  let f : V2 → Row := fun p => toRow p.toVec
  have hsub : (P.toFinset.image f : Set Row) ⊆ Dlt ℓ := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 (List.mem_toFinset.1 hp)
    have := tree_mem_Dlt hM hℓ hP k hk
    rwa [getElem!_pos P k hk] at this
  have hinj : Set.InjOn f P.toFinset := by
    intro a ha b hb e
    have ha' := hwf a (List.mem_toFinset.1 ha)
    have hb' := hwf b (List.mem_toFinset.1 hb)
    exact (V2.toVec_inj ha' hb').1 e
  have hc : (P.toFinset.image f).card = n := by
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnd, hlen]
  have hfin : (Dlt ℓ).Finite := Set.toFinite _
  have heq : (P.toFinset.image f : Set Row) = Dlt ℓ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hc]; exact hcard) hfin
  intro v hv
  rw [← heq] at hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
  exact ⟨p, List.mem_toFinset.1 hp, rfl⟩

theorem b7_fixed_of_goodW
    (hM : MatFacts) (hF : J4Basic) {t : J} {T0 : Array V2} {g0w : List Int}
    {c0 : ℕ} (hξ : Mx fiveElt = rowsMatrix fiveRows) (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv)
    (hT : Mx t = rowsMatrix T0) (hG0 : Mx (el5 g0w)⁻¹ = rowsMatrix (invRows (wR g0w)))
    (hfac : B7Facts t (el5 g0w) c0) (hS0 : survP T0 g0w rootV)
    (hS5 : survOrb T0 g0w 5 15180) (hS6 : survOrb T0 g0w 6 28336)
    (hok5 : vorbOK locTabs rep5Vec orb5 15180 = true) {n : J}
    (hfix : ∀ j < 4, vEl t j • (n • w₀) = n • w₀) :
    fiveElt • (n • w₀) = n • w₀ ∨
      ∃ m ∈ Eg (vEl t) 4, m ≠ 1 ∧ cntFix RIn (n • w₀) m ≠ 128 := by
  have hsq := hfac.elem.sq
  have h0 : (el5 g0w * eta uJ 11 c0 * (el5 g0w)⁻¹) • (n • w₀) = n • w₀ := by
    rw [← hfac.conj]
    exact hfix 0 (by norm_num)
  have hrel := fix2B_rel_b hF hfac.mask h0
  have hconv : ∀ u : V2, el5 g0w • toRow u.toVec =
      toRow (frApply (frTable (invRows (wR g0w))) u).toVec := fun u => smul_toRow_rows hG0 u
  have fin : ∀ {u : V2}, n • w₀ = el5 g0w • toRow u.toVec → survP T0 g0w u →
      (fiveElt • (n • w₀) = n • w₀ ∨
        ∃ m ∈ Eg (vEl t) 4, m ≠ 1 ∧ cntFix RIn (n • w₀) m ≠ 128) := by
    intro u hq hs
    rw [hq, hconv] at hfix ⊢
    exact survP_sound hM hF hξ hξi hT hsq hs hfix
  have orb : ∀ {ℓ m : ℕ}, ℓ < 7 → survOrb T0 g0w ℓ m → (Dlt ℓ).ncard ≤ m →
      (el5 g0w)⁻¹ • (n • w₀) ∈ Dlt ℓ →
      (fiveElt • (n • w₀) = n • w₀ ∨
        ∃ m ∈ Eg (vEl t) 4, m ≠ 1 ∧ cntFix RIn (n • w₀) m ≠ 128) := by
    intro ℓ m hℓ hS hc hmem
    obtain ⟨P, hP, hnd, hlen, hall⟩ := hS
    obtain ⟨p, hp, e⟩ := orbit_cover hM hℓ hP hnd hlen (fun p hp => (hall p hp).1) hc _ hmem
    exact fin (u := p) (by rw [← e, smul_inv_smul]) (hall p hp).2
  rcases hrel with h1 | h1 | h1
  · exact fin (u := rootV) h1 hS0
  · exact orb (by norm_num) hS5 (Dlt_card_le_of_vorb hM hok5 (rep_toVec hM (by norm_num)))
      ((Rel_smul_w₀_b hF).1 h1)
  · exact orb (by norm_num) hS6 (Dlt_card_le_of_vorb hM orb6_ok (rep_toVec hM (by norm_num)))
      ((Rel_smul_w₀_b hF).1 h1)

theorem noNonHBlockAt_b7W
    (hF : J4Basic) (h5 : ¬ 5 ^ 2 ∣ Nat.card J) {t : J} {T0 : Array V2}
    (hT : Mx t = rowsMatrix T0) {g0w : List Int} {c0 : ℕ}
    (hV : chkB7V T0 g0w c0 = true) (hS0 : survP T0 g0w rootV)
    (hS5 : survOrb T0 g0w 5 15180) (hS6 : survOrb T0 g0w 6 28336)
    (hB : baseP T0) (hok5 : vorbOK locTabs rep5Vec orb5 15180 = true) :
    NoNonHBlockAt Hj (Eg (vEl t) 4) := by
  have hM := hF.mat
  obtain ⟨hξi, hG0, hfac⟩ := b7Facts_of_chk hM hT hV
  have hξ : Mx fiveElt = rowsMatrix fiveRows := Mx_wordProd hM fiveWord
  have hvH : ∀ j, vEl t j ∈ Hj := by
    intro j
    induction j with
    | zero => exact stab_w₀_b hF hfac.fix
    | succ j ih => exact Hj.mul_mem (Hj.mul_mem fiveElt_mem_Hj ih) (Hj.inv_mem fiveElt_mem_Hj)
  have hVH : Eg (vEl t) 4 ≤ Hj := by
    unfold Eg
    rw [Subgroup.closure_le]
    rintro x ⟨j, -, rfl⟩
    exact hvH j
  have hcm : ∀ v ∈ Eg (vEl t) 4, fiveElt * v * fiveElt⁻¹ ∈ Eg (vEl t) 4 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      by_cases h3 : j = 3
      · subst h3
        rw [hfac.norm]
        exact eta_mem_Eg 4 le_rfl 15
      · have e : fiveElt * vEl t j * fiveElt⁻¹ = vEl t (j + 1) := rfl
        rw [e]
        exact u_mem_Eg (by omega)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : fiveElt * (x * y) * fiveElt⁻¹ =
          (fiveElt * x * fiveElt⁻¹) * (fiveElt * y * fiveElt⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : fiveElt * x⁻¹ * fiveElt⁻¹ = (fiveElt * x * fiveElt⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  have hxiN := normalizer_of_conj_maps (Eg (vEl t) 4) fiveElt hcm
  refine noNonHBlockAt_of_conj_fixed h5 Hj 1 hxiN (orderOf_fiveElt hM) ?_
  intro m hm
  have hn : m⁻¹ ∈ Subgroup.normalizer ((Eg (vEl t) 4 : Subgroup J) : Set J) := inv_mem hm
  have hgood : IsGoodPt (Eg (vEl t) 4) RIn (m⁻¹ • w₀) :=
    isGoodPt_smul RIn RIn_conj hn (isGoodPt_baseW hM hF hξ hξi hT hfac hB)
  have hq : ∀ j < 4, vEl t j • (m⁻¹ • w₀) = m⁻¹ • w₀ := by
    intro j hj
    have hv : vEl t j ∈ Eg (vEl t) 4 := u_mem_Eg hj
    have h1 : m * vEl t j * m⁻¹ ∈ Eg (vEl t) 4 := (Subgroup.mem_normalizer_iff.1 hm _).1 hv
    have h2 : (m * vEl t j * m⁻¹) • w₀ = w₀ := smul_root_of_mem_Hj hM (hVH h1)
    have e : m⁻¹ * (m * vEl t j * m⁻¹) = vEl t j * m⁻¹ := by group
    calc vEl t j • (m⁻¹ • w₀) = (vEl t j * m⁻¹) • w₀ := (mul_smul _ _ _).symm
      _ = (m⁻¹ * (m * vEl t j * m⁻¹)) • w₀ := by rw [e]
      _ = m⁻¹ • ((m * vEl t j * m⁻¹) • w₀) := mul_smul _ _ _
      _ = m⁻¹ • w₀ := by rw [h2]
  rcases b7_fixed_of_goodW hM hF hξ hξi hT hG0 hfac hS0 hS5 hS6 hok5 hq with
    hfx | ⟨m', hm', hm'1, hc⟩
  · have h1 : (m * fiveElt * m⁻¹) • w₀ = w₀ := by
      calc (m * fiveElt * m⁻¹) • w₀ = m • (fiveElt • (m⁻¹ • w₀)) := by
            rw [mul_smul, mul_smul]
        _ = m • (m⁻¹ • w₀) := by rw [hfx]
        _ = w₀ := smul_inv_smul m w₀
    exact ⟨m * fiveElt * m⁻¹, stab_w₀_b hF h1, by simp [cm_apply]⟩
  · exact absurd (hgood m' hm' hm'1) hc

theorem noNonHBlockAt_b7W_closure
    (hF : J4Basic) (h5 : ¬ 5 ^ 2 ∣ Nat.card J)
    {ws : List (List ℤ)} (hlen : ws.length = 4) {tw g0w : List ℤ} {c0 : ℕ}
    (hV : chkB7V (wR tw) g0w c0 = true) (hS0 : survP (wR tw) g0w rootV)
    (hS5 : survOrb (wR tw) g0w 5 15180) (hS6 : survOrb (wR tw) g0w 6 28336)
    (hB : baseP (wR tw))
    (h1 : chkCross (vRows (wR tw)) (ws.map wR).toArray = true)
    (h2 : chkCross (ws.map wR).toArray (vRows (wR tw)) = true) :
    NoNonHBlockAt Hj (Subgroup.closure {x : J | x ∈ ws.map el5}) := by
  have hM := hF.mat
  obtain ⟨hξi, -, -⟩ := b7Facts_of_chk hM (Mx_el5 hM tw) hV
  have hξ : Mx fiveElt = rowsMatrix fiveRows := Mx_wordProd hM fiveWord
  have hu := Mx_vEl hξ hξi (Mx_el5 hM tw)
  have hg : ∀ j < 4,
      Mx (el5 (ws.getD j [])) = rowsMatrix (((ws.map wR).toArray)[j]?.getD idRows) :=
    fun j hj => Mx_words_rows hM (by omega)
  have heq := Eg_eq_of_rows hu hg (cross_of_chk h1) (cross_of_chk h2)
  rw [closure_words_eq_Eg hlen, ← heq]
  exact noNonHBlockAt_b7W hF h5 (Mx_el5 hM tw) hV hS0 hS5 hS6 hB orb5_ok

end CFSG.QuasithinUnique.A5.B7
