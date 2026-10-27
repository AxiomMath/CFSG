module

public import Certificates.Certificate38702
public import CFSG.GF2Type.SmithTypeE.DMod.LineTree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

attribute [local irreducible] tvCols tvLin

theorem wtCheck_holds :
    wtArr.size = 75735 ∧ wtArr[0]! = 1 ∧ (∀ i < 75735, wt i < 4294967296) ∧
      (∀ i < 75734, wt i < wt (i + 1)) ∧ ∀ i < 75735, wtIdx (wt i) = i :=
  Certificates.certificate38702.1

theorem planesCheck_holds :
    (∀ i < 75735, (pbArr[i]!).size = 6 ∧ (ppArr[i]!).size = 6 ∧ (∀ m < 6, (pbArr[i]!)[m]! < 4096) ∧
      (∀ d < 64, d = 0 ∨ xorComb pbArr[i]! d ≠ 0) ∧
      ∀ d < 64, memR pbArr[i]! ppArr[i]! (xorComb pbArr[i]! d) = true) ∧ pbArr[0]! = fBasis :=
  ⟨Certificates.certificate38702.2.1, Certificates.certificate38702.2.2.1⟩

theorem basesCheck_holds :
    (∀ i < 75735, planeSpan pbArr[i]! = annSub (exL (decode32 (wt i)))) ∧
    ∀ i < 75735, ∀ g < 13, ∃ j < 75735,
      tlift (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).1) (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).2)
        (exL (decode32 (wt i))) = exL (decode32 (wt j)) :=
  ⟨Certificates.certificate38702.2.2.2.1, Certificates.certificate38702.2.2.2.2.1⟩

theorem gramRowCheck_holds :
    ∀ j < 75735, fModel (decode32 (wt 0)) (decode32 (wt j)) = 1 ↔
      Disjoint (planeSpan pbArr[0]!) (planeSpan pbArr[j]!) :=
  Certificates.certificate38702.2.2.2.2.2.1

theorem planeTreeCheck_holds :
    ∀ Q : ℕ → Prop, Q 0 → (∀ g < 13, ∀ p < 75735, ∀ i < 75735,
      tlift (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).1) (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).2)
        (exL (decode32 (wt p))) = exL (decode32 (wt i)) → Q p → Q i) → ∀ i < 75735, Q i :=
  Certificates.certificate38702.2.2.2.2.2.2

structure WtFacts : Prop where
  size : wtArr.size = 75735
  zero : wtArr[0]! = 1
  lt : ∀ i < 75735, wtArr[i]! < 4294967296
  mono : ∀ i < 75734, wtArr[i]! < wtArr[i + 1]!
  idx : ∀ i < 75735, wtIdx wtArr[i]! = i

theorem wtFacts : WtFacts := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := wtCheck_holds
  exact ⟨h1, h2, h3, h4, h5⟩

theorem wt_lt {i : ℕ} (hi : i < 75735) : wt i < 2 ^ 32 :=
  wtFacts.lt i hi

theorem wt_strictMono {i j : ℕ} (hij : i < j) (hj : j < 75735) :
    wt i < wt j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact lt_trans (ih h (by omega)) (wtFacts.mono j (by omega))
    · subst h
      exact wtFacts.mono i (by omega)

theorem wt_injective {i j : ℕ} (hi : i < 75735) (hj : j < 75735)
    (h : wt i = wt j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (ne_of_lt (wt_strictMono hij hj))
  · exact hij
  · exact absurd h.symm (ne_of_lt (wt_strictMono hij hi))

theorem wtIdx_wt {i : ℕ} (hi : i < 75735) : wtIdx (wt i) = i :=
  wtFacts.idx i hi

theorem wtIdx_spec {s : ℕ} (h : wtIdx s < 75735) : wtArr[wtIdx s]! = s := by
  unfold wtIdx at h ⊢
  set i := lowerBoundGo wtArr s 40 0 wtArr.size with hi
  by_cases hc : i < 75735 ∧ wtArr[i]! = s
  · have e : (if i < 75735 && wtArr[i]! == s then i else 75735) = i := by
      simp [hc.1, hc.2]
    rw [e]
    exact hc.2
  · have e : (if i < 75735 && wtArr[i]! == s then i else 75735) = 75735 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rw [if_neg hc]
    rw [e] at h
    exact absurd h (lt_irrefl _)

@[expose] noncomputable def wtV (i : ℕ) : V := decode32 (wt i)

theorem wtV_injective {i j : ℕ} (hi : i < 75735) (hj : j < 75735)
    (h : wtV i = wtV j) : i = j :=
  wt_injective hi hj (eq_of_decode32_eq (wt_lt hi) (wt_lt hj) h)

structure PlaneFacts (i : ℕ) : Prop where
  sizeB : (pbArr[i]!).size = 6
  sizeP : (ppArr[i]!).size = 6
  lt : ∀ m < 6, (pbArr[i]!)[m]! < 4096
  indep : ∀ d < 64, d = 0 ∨ xorComb pbArr[i]! d ≠ 0
  complete : ∀ d < 64, memR pbArr[i]! ppArr[i]! (xorComb pbArr[i]! d) = true

theorem planeFacts {i : ℕ} (hi : i < 75735) : PlaneFacts i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := planesCheck_holds.1 i hi
  exact ⟨h1, h2, h3, h4, h5⟩

theorem pbArr_zero : pbArr[0]! = fBasis :=
  planesCheck_holds.2

@[expose] noncomputable def planeSub (i : ℕ) : Submodule (ZMod 2) V12 := planeSpan pbArr[i]!

@[expose] def Opp (i j : ℕ) : Prop := Disjoint (planeSub i) (planeSub j)

structure Good (k : ℕ) : Prop where
  invol : ∀ v : V, tvLin k (tvLin k v) = v
  form : ∀ v w : V, fModel (tvLin k v) (tvLin k w) = fModel v w
  perm : ∀ i < 75735, ∃ j < 75735, tvLin k (wtV i) = wtV j ∧
    Submodule.map (siegelK k).toLinearMap (planeSub i) = planeSub j

theorem exL_tvLin_gensArr
    {g : ℕ} (hg : g < 13) (v : V) :
    exL (tvLin gensArr[g]! v) = tlift (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).1)
      (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).2) (exL v) := by
  unfold tvLin
  rw [exL_colsLin_tvCols, lineTreeCheck_holds.1 g hg, tlift_lineOf_gensV hg]

set_option maxRecDepth 20000 in
theorem good_of_exL {k g : ℕ}
    (hk : k < 365211) (hg : g < 13)
    (hT : ∀ v, exL (tvLin k v) = tlift (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).1)
      (dec12 (CFSG.KD.SmithD6.gensV.getD g (0, 0)).2) (exL v)) : Good k := by
  have hts := tsPair_linePair hk
  refine ⟨fun v => ?_, fun v w => ?_, fun i hi => ?_⟩
  · unfold tvLin
    exact colsLin_tvCols_invol hts v
  · unfold tvLin
    exact fModel_colsLin_tvCols hts v w
  · obtain ⟨j, hj, he⟩ := basesCheck_holds.2 i hi g hg
    have hw : tvLin k (wtV i) = wtV j := exL_injective (by
      rw [hT, wtV, wtV]
      exact he)
    refine ⟨j, hj, hw, ?_⟩
    unfold planeSub
    rw [basesCheck_holds.1 i hi, basesCheck_holds.1 j hj]
    rw [wtV, wtV] at hw
    rw [← hw]
    unfold tvLin siegelK
    exact (annSub_exL_colsLin_tvCols hts _).symm

theorem good_gen
    {g : ℕ} (hg : g < 13) : Good gensArr[g]! :=
  good_of_exL (gensArr_lt hg) hg (exL_tvLin_gensArr hg)

theorem good_step
    {g p v : ℕ} (hg : g < 365211) (hp : p < 365211) (hv : v < 365211) (hgv : tvImg g p = v)
    (Gg : Good g) (Gp : Good p) : Good v := by
  have hTv : ∀ x, tvLin v x = tvLin g (tvLin p (tvLin g x)) := fun x => by
    rw [← hgv]
    exact tvLin_tvImg hg hp x
  have hspec := tvImg_spec hg hp
  have hline : lineSet v = (lineSet p).map (siegelK g).toEquiv.toEmbedding := by
    rw [← hgv]
    exact hspec.2
  have hinv : (siegelK g)⁻¹ = siegelK g := siegelEquiv_inv (tsPair_linePair hg)
  have hS : siegelK g * siegelK p * siegelK g = siegelK v := by
    have h := conj_siegelK (g := siegelK g) (fun x => q12_siegelEquiv (tsPair_linePair hg) x) hp hv
      hline
    rwa [hinv] at h
  refine ⟨fun x => ?_, fun a b => ?_, fun i hi => ?_⟩
  · calc tvLin v (tvLin v x)
        = tvLin g (tvLin p (tvLin g (tvLin g (tvLin p (tvLin g x))))) := by
          rw [hTv (tvLin v x), hTv x]
      _ = x := by simp only [Gg.invol, Gp.invol]
  · simp only [hTv, Gg.form, Gp.form]
  · obtain ⟨j1, hj1, hw1, hS1⟩ := Gg.perm i hi
    obtain ⟨j2, hj2, hw2, hS2⟩ := Gp.perm j1 hj1
    obtain ⟨j3, hj3, hw3, hS3⟩ := Gg.perm j2 hj2
    refine ⟨j3, hj3, ?_, ?_⟩
    · rw [hTv, hw1, hw2, hw3]
    · have h : (siegelK v).toLinearMap = (siegelK g).toLinearMap ∘ₗ (siegelK p).toLinearMap ∘ₗ
          (siegelK g).toLinearMap := by
        refine LinearMap.ext fun x => ?_
        rw [← hS]
        rfl
      rw [h, Submodule.map_comp, Submodule.map_comp, hS1, hS2, hS3]

theorem good_all
    {k : ℕ} (hk : k < 365211) : Good k := by
  have hgen : ∀ g < 13, Good gensArr[g]! := fun g hg =>
    good_gen hg
  refine lineTree_induct_from (fun k => Good k) (gensArr_lt (g := 0) (by norm_num))
    (hgen 0 (by norm_num)) ?_ k hk
  intro g hg p hp v hv hgv hGp
  exact good_step (gensArr_lt hg) hp hv hgv (hgen g hg) hGp

theorem tvLin_tvLin
    {k : ℕ} (hk : k < 365211) (v : V) :
    tvLin k (tvLin k v) = v :=
  (good_all hk).invol v

@[expose] noncomputable def tvEquiv
    (k : ℕ) : V ≃ₗ[ZMod 2] V :=
  if hk : k < 365211 then LinearEquiv.ofInvolutive (tvLin k) (tvLin_tvLin hk)
  else LinearEquiv.refl (ZMod 2) V

section Equiv

theorem tvEquiv_apply {k : ℕ} (hk : k < 365211) (v : V) : tvEquiv k v = tvLin k v := by
  simp only [tvEquiv, hk, ↓reduceDIte]
  rfl

theorem tvEquiv_decode {k : ℕ} (hk : k < 365211) (c : ℕ) :
    tvEquiv k (decode32 c) = decode32 (applyCols (tvCols k) c) := by
  rw [tvEquiv_apply hk, tvLin_decode]

theorem tvEquiv_single {k : ℕ} (hk : k < 365211) (m : Fin 32) :
    tvEquiv k (Pi.single m 1) = decode32 (tvCols k)[m.val]! := by
  rw [tvEquiv_apply hk, tvLin_single]

theorem tvEquiv_mul_self {k : ℕ} (hk : k < 365211) : tvEquiv k * tvEquiv k = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, tvEquiv_apply hk, tvEquiv_apply hk, tvLin_tvLin hk]
  rfl

theorem fModel_tvEquiv {k : ℕ} (hk : k < 365211) (v w : V) :
    fModel (tvEquiv k v) (tvEquiv k w) = fModel v w := by
  rw [tvEquiv_apply hk, tvEquiv_apply hk]
  exact (good_all hk).form v w

theorem tvCols_lt (k : ℕ) {c : ℕ} (hc : c < 32) : (tvCols k)[c]! < 2 ^ 32 := by
  unfold tvCols
  simp only
  rw [getElem!_pos _ c (by simp [hc])]
  simp only [Array.getElem_ofFn]
  exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ (by norm_num))
    (Nat.pow_lt_pow_right (by norm_num) hc)

theorem applyCols_lt {cols : Array ℕ} (hsz : cols.size = 32) (h : ∀ c < 32, cols[c]! < 2 ^ 32)
    (y : ℕ) : applyCols cols y < 2 ^ 32 := by
  unfold applyCols
  rw [hsz]
  have key : ∀ n ≤ 32, (List.range n).foldl
      (fun acc m => if y.testBit m then acc ^^^ cols[m]! else acc) 0 < 2 ^ 32 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      split_ifs
      · exact Nat.xor_lt_two_pow (ih (by omega)) (h n (by omega))
      · exact ih (by omega)
  exact key 32 le_rfl

theorem tvEquiv_wtV {k i : ℕ} (hk : k < 365211) (hi : i < 75735) :
    planeImg k i < 75735 ∧ tvEquiv k (wtV i) = wtV (planeImg k i) := by
  obtain ⟨j, hj, hw, -⟩ := (good_all hk).perm i hi
  have hcodes : applyCols (tvCols k) (wt i) = wt j := by
    have h1 : decode32 (applyCols (tvCols k) (wt i)) = decode32 (wt j) := by
      rw [← tvLin_decode]
      exact hw
    exact eq_of_decode32_eq (applyCols_lt (size_tvCols k) (fun c hc => tvCols_lt k hc) _)
      (wt_lt hj) h1
  have hpi : planeImg k i = j := by
    show wtIdx (applyCols (tvCols k) (wtArr[i]!)) = j
    rw [show wtArr[i]! = wt i from rfl, hcodes, wtIdx_wt hj]
  refine ⟨hpi ▸ hj, ?_⟩
  rw [hpi, tvEquiv_apply hk]
  exact hw

theorem map_planeSub_siegelK {k i : ℕ} (hk : k < 365211) (hi : i < 75735) :
    Submodule.map (siegelK k).toLinearMap (planeSub i) = planeSub (planeImg k i) := by
  obtain ⟨j, hj, hw, hmap⟩ := (good_all hk).perm i hi
  have h := tvEquiv_wtV hk hi
  have hpj : planeImg k i = j :=
    wtV_injective h.1 hj (by rw [← h.2, tvEquiv_apply hk]; exact hw)
  rw [hpj]
  exact hmap

end Equiv

theorem planeTree_induct
    (Q : ℕ → Prop) (h0 : Q 0)
    (hstep : ∀ g < 13, ∀ p < 75735, ∀ v < 75735, planeImg gensArr[g]! p = v → Q p → Q v) :
    ∀ v < 75735, Q v := by
  refine planeTreeCheck_holds Q h0 fun g hg p hp v hv he hQ => hstep g hg p hp v hv ?_ hQ
  have hT := exL_tvLin_gensArr hg
  generalize gensArr[g]! = k at hT ⊢
  have hw : tvLin k (decode32 (wt p)) = decode32 (wt v) := exL_injective (by
    rw [hT]
    exact he)
  rw [tvLin_decode] at hw
  have e := eq_of_decode32_eq (applyCols_lt (size_tvCols _) (fun c hc => tvCols_lt _ hc) _)
    (wt_lt hv) hw
  unfold planeImg
  rw [← wt, e, wtIdx_wt hv]

theorem disjoint_map_iff (σ : V12 ≃ₗ[ZMod 2] V12) (A B : Submodule (ZMod 2) V12) :
    Disjoint (Submodule.map σ.toLinearMap A) (Submodule.map σ.toLinearMap B) ↔ Disjoint A B := by
  rw [Submodule.disjoint_def, Submodule.disjoint_def]
  constructor
  · intro h x hxA hxB
    have := h (σ x) ⟨x, hxA, rfl⟩ ⟨x, hxB, rfl⟩
    exact σ.map_eq_zero_iff.mp this
  · rintro h y ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hab : b = a := σ.injective hba
    subst hab
    have := h b ha hb
    simp [this]

section Pi

@[expose] noncomputable def pairGen (k : Fin 365211) :
    (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12) := (tvEquiv k.val, siegelK k.val)

@[expose] noncomputable def PiGrp : Subgroup ((V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12)) :=
  Subgroup.closure (Set.range pairGen)

theorem pairGen_mem (k : Fin 365211) : pairGen k ∈ PiGrp := Subgroup.subset_closure ⟨k, rfl⟩

theorem pi_mul_inv_apply_fst (x : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12)) (u : V) :
    x.1 ((x⁻¹).1 u) = u := by
  have := congrArg (fun z : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12) => z.1 u) (mul_inv_cancel x)
  simpa using this

theorem pi_inv_mul_apply_fst (x : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12)) (u : V) :
    (x⁻¹).1 (x.1 u) = u := by
  have := congrArg (fun z : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12) => z.1 u) (inv_mul_cancel x)
  simpa using this

theorem piGrp_form {x : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12)} (hx : x ∈ PiGrp) (v w : V) :
    fModel (x.1 v) (x.1 w) = fModel v w := by
  revert v w
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro v w
    exact fModel_tvEquiv k.2 v w
  | one => intro v w; rfl
  | mul x y _ _ hx hy =>
    intro v w
    show fModel (x.1 (y.1 v)) (x.1 (y.1 w)) = _
    rw [hx, hy]
  | inv x _ hx =>
    intro v w
    have h := hx ((x⁻¹).1 v) ((x⁻¹).1 w)
    rw [pi_mul_inv_apply_fst, pi_mul_inv_apply_fst] at h
    exact h.symm

theorem piGrp_perm {x : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12)} (hx : x ∈ PiGrp) :
    ∀ i < 75735, ∃ j < 75735, x.1 (wtV i) = wtV j ∧
      Submodule.map x.2.toLinearMap (planeSub i) = planeSub j := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro i hi
    obtain ⟨hlt, hw⟩ := tvEquiv_wtV k.2 hi
    exact ⟨planeImg k.val i, hlt, hw, map_planeSub_siegelK k.2 hi⟩
  | one =>
    intro i hi
    refine ⟨i, hi, rfl, ?_⟩
    have : (1 : V12 ≃ₗ[ZMod 2] V12).toLinearMap = LinearMap.id := rfl
    show Submodule.map (1 : V12 ≃ₗ[ZMod 2] V12).toLinearMap (planeSub i) = planeSub i
    rw [this, Submodule.map_id]
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨j, hj, hw, hm⟩ := hy i hi
    obtain ⟨l, hl, hw', hm'⟩ := hx j hj
    refine ⟨l, hl, ?_, ?_⟩
    · show x.1 (y.1 (wtV i)) = _
      rw [hw, hw']
    · have h : (x * y).2.toLinearMap = x.2.toLinearMap ∘ₗ y.2.toLinearMap := rfl
      rw [h, Submodule.map_comp, hm, hm']
  | inv x _ hx =>
    choose f hf hw hm using hx
    let F : Fin 75735 → Fin 75735 := fun i => ⟨f i.val i.2, hf i.val i.2⟩
    have hF : Function.Injective F := by
      intro a b hab
      have hab' : f a.val a.2 = f b.val b.2 := congrArg Fin.val hab
      have : x.1 (wtV a.val) = x.1 (wtV b.val) := by rw [hw a.val a.2, hw b.val b.2, hab']
      exact Fin.ext (wtV_injective a.2 b.2 (x.1.injective this))
    intro i hi
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
    have hfa : f a.val a.2 = i := congrArg Fin.val ha
    refine ⟨a.val, a.2, ?_, ?_⟩
    · have h1 := hw a.val a.2
      rw [hfa] at h1
      rw [← h1]
      exact pi_inv_mul_apply_fst x _
    · have h1 := hm a.val a.2
      rw [hfa] at h1
      rw [← h1, ← Submodule.map_comp]
      have : (x⁻¹).2.toLinearMap ∘ₗ x.2.toLinearMap = LinearMap.id := by
        refine LinearMap.ext fun u => ?_
        have := congrArg (fun z : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12) => z.2 u)
          (inv_mul_cancel x)
        simpa using this
      rw [this, Submodule.map_id]

theorem exists_pi_of_weight {i : ℕ} (hi : i < 75735) :
    ∃ x ∈ PiGrp, x.1 (wtV 0) = wtV i ∧ Submodule.map x.2.toLinearMap (planeSub 0) = planeSub i := by
  refine planeTree_induct (fun i => ∃ x ∈ PiGrp, x.1 (wtV 0) = wtV i ∧
    Submodule.map x.2.toLinearMap (planeSub 0) = planeSub i) ?_ ?_ i hi
  · refine ⟨1, Subgroup.one_mem _, rfl, ?_⟩
    have : (1 : V12 ≃ₗ[ZMod 2] V12).toLinearMap = LinearMap.id := rfl
    show Submodule.map (1 : V12 ≃ₗ[ZMod 2] V12).toLinearMap (planeSub 0) = planeSub 0
    rw [this, Submodule.map_id]
  · intro g hg p hp v hv hgv ⟨x, hx, hxw, hxm⟩
    have hk : gensArr[g]! < 365211 := gensArr_lt hg
    refine ⟨pairGen ⟨gensArr[g]!, hk⟩ * x, Subgroup.mul_mem _ (pairGen_mem _) hx, ?_, ?_⟩
    · show tvEquiv gensArr[g]! (x.1 (wtV 0)) = _
      rw [hxw, (tvEquiv_wtV hk hp).2, hgv]
    · have h : (pairGen ⟨gensArr[g]!, hk⟩ * x).2.toLinearMap =
          (siegelK gensArr[g]!).toLinearMap ∘ₗ x.2.toLinearMap := rfl
      rw [h, Submodule.map_comp, hxm, map_planeSub_siegelK hk hp, hgv]

open Classical in
theorem fModel_wtV_zero {j : ℕ} (hj : j < 75735) :
    fModel (wtV 0) (wtV j) = if Opp 0 j then 1 else 0 := by
  have h := gramRowCheck_holds j hj
  by_cases ho : Opp 0 j
  · rw [if_pos ho]
    exact h.2 ho
  · rw [if_neg ho]
    have hne : fModel (wtV 0) (wtV j) ≠ 1 := fun e => ho (h.1 e)
    generalize fModel (wtV 0) (wtV j) = c at hne ⊢
    revert c
    decide

open Classical in
theorem fModel_wtV {i j : ℕ} (hi : i < 75735) (hj : j < 75735) :
    fModel (wtV i) (wtV j) = if Opp i j then 1 else 0 := by
  obtain ⟨x, hx, hxw, hxp⟩ := exists_pi_of_weight hi
  obtain ⟨j', hj', hwj', hmj'⟩ := piGrp_perm (inv_mem hx) j hj
  have e1 : x.1 (wtV j') = wtV j := by
    rw [← hwj']
    exact pi_mul_inv_apply_fst x _
  have e2 : Submodule.map x.2.toLinearMap (planeSub j') = planeSub j := by
    rw [← hmj', ← Submodule.map_comp]
    have : x.2.toLinearMap ∘ₗ (x⁻¹).2.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun u => ?_
      have := congrArg (fun z : (V ≃ₗ[ZMod 2] V) × (V12 ≃ₗ[ZMod 2] V12) => z.2 u)
        (mul_inv_cancel x)
      simpa using this
    rw [this, Submodule.map_id]
  have hrow := fModel_wtV_zero hj'
  have hform := piGrp_form hx (wtV 0) (wtV j')
  rw [hxw, e1] at hform
  rw [hform, hrow]
  have hopp : Opp 0 j' ↔ Opp i j := by
    unfold Opp
    rw [← hxp, ← e2]
    exact (disjoint_map_iff x.2 _ _).symm
  simp only [hopp]

end Pi

end CFSG.GF2Type.SmithTypeE.DMod
