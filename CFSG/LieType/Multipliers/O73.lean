module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.LieType.Multipliers.O73Data
import CFSG.ClassicalInvolution.Orders.Orthogonal

public section

namespace CFSG.LieType.Multipliers.O73

open CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.CosetEnumeration CFSG.RankThree.PerfectCover Matrix

@[expose] def eRelSet : Set (FreeGroup (Fin 8)) := {x | ∃ w ∈ eWords, wordFG 8 w = x}

abbrev TripleCover : Type := PresentedGroup eRelSet

@[expose] noncomputable def eGen (c : ℕ) : TripleCover :=
  if h : c < 8 then PresentedGroup.of ⟨c, h⟩ else 1

private theorem map_evalWord' {G H : Type*} [Group G] [Group H] (φ : G →* H) (g : ℕ → G)
    (w : List ℕ) : φ (evalWord g w) = evalWord (fun c => φ (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

private theorem evalWord_app {G : Type*} [Group G] (g : ℕ → G) (u v : List ℕ) :
    evalWord g (u ++ v) = evalWord g u * evalWord g v := by
  simp [evalWord, List.map_append, List.prod_append]

private theorem evalWord_eGen (w : List ℕ) :
    evalWord eGen w = PresentedGroup.mk _ (wordFG 8 w) := by
  induction w with
  | nil => simp [evalWord, wordFG]
  | cons c w ih =>
    rw [evalWord_cons, ih]
    simp only [wordFG, List.map_cons, List.prod_cons, map_mul]
    congr 1
    by_cases h : c < 8
    · simp [eGen, h, PresentedGroup.of]
    · simp [eGen, h]

private theorem evalWord_eGen_of_mem {w : List ℕ} (hw : w ∈ eWords) : evalWord eGen w = 1 := by
  rw [evalWord_eGen]
  exact PresentedGroup.one_of_mem ⟨w, hw, rfl⟩

private noncomputable def eHom {H : Type*} [Group H] (img : ℕ → H) (himg : ∀ c, 8 ≤ c → img c = 1)
    (h : ∀ w ∈ eWords, evalWord img w = 1) : TripleCover →* H :=
  PresentedGroup.toGroup (f := fun c : Fin 8 => img c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := img)]
    · exact h w hw
    · intro c _
      by_cases hc : c < 8
      · simp [hc]
      · simp [hc, himg c (by omega)])

private theorem eHom_eGen {H : Type*} [Group H] {img : ℕ → H} {himg : ∀ c, 8 ≤ c → img c = 1}
    {h : ∀ w ∈ eWords, evalWord img w = 1} (c : ℕ) : eHom img himg h (eGen c) = img c := by
  by_cases hc : c < 8
  · rw [eGen, dite_eq_left hc, eHom, PresentedGroup.toGroup.of]
  · rw [eGen, dite_eq_right hc, map_one, himg c (by omega)]

private theorem eHom_evalWord {H : Type*} [Group H] {img : ℕ → H}
    {himg : ∀ c, 8 ≤ c → img c = 1} {h : ∀ w ∈ eWords, evalWord img w = 1} (w : List ℕ) :
    eHom img himg h (evalWord eGen w) = evalWord img w := by
  rw [map_evalWord']
  exact evalWord_congr fun c _ => eHom_eGen c

private theorem closure_eGen : Subgroup.closure (eGen '' Set.Iio 8) = ⊤ := by
  have : eGen '' Set.Iio 8 = Set.range (PresentedGroup.of (rels := eRelSet)) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, by simp [eGen, show c < 8 from hc]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, by simp [eGen]⟩
  rw [this]
  exact PresentedGroup.closure_range_of _

private theorem range_eHom {H : Type*} [Group H] {img : ℕ → H}
    {himg : ∀ c, 8 ≤ c → img c = 1} {h : ∀ w ∈ eWords, evalWord img w = 1} :
    (eHom img himg h).range = Subgroup.closure (img '' Set.Iio 8) := by
  rw [MonoidHom.range_eq_map, ← closure_eGen, MonoidHom.map_closure, Set.image_image]
  congr 1
  exact Set.image_congr fun c _ => eHom_eGen c

private theorem eGen_mul_self (c : ℕ) : eGen c * eGen c = 1 := by
  by_cases hc : c < 8
  · have hm : [c, c] ∈ eWords := by
      have : ∀ c : Fin 8, [c.val, c.val] ∈ eWords := by decide
      exact this ⟨c, hc⟩
    simpa [evalWord] using evalWord_eGen_of_mem hm
  · simp [eGen, hc]

private theorem evalWord_reverse {G : Type*} [Group G] {g : ℕ → G} (hg : ∀ c, g c * g c = 1)
    (w : List ℕ) : evalWord g w.reverse = (evalWord g w)⁻¹ := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.reverse_cons, evalWord_app, ih, evalWord_cons, evalWord_cons, evalWord_nil,
      mul_one, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left (hg c)]

private noncomputable def sp : TripleCover := evalWord eGen spW

private theorem eGen_comm_sp (c : ℕ) : eGen c * sp = sp * eGen c := by
  by_cases hc : c < 8
  · have hm : [c] ++ spW ++ [c] ++ spW.reverse ∈ eWords := by
      unfold eWords
      exact List.mem_append_right _ (List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩)
    have h := evalWord_eGen_of_mem hm
    rw [evalWord_app, evalWord_app, evalWord_app, evalWord_reverse eGen_mul_self] at h
    simp only [evalWord_cons, evalWord_nil, mul_one] at h
    have h' := mul_inv_eq_one.1 h
    rw [← sp] at h'
    calc eGen c * sp = eGen c * sp * eGen c * eGen c := by
          rw [mul_assoc (eGen c * sp), eGen_mul_self, mul_one]
      _ = sp * eGen c := by rw [h']
  · simp [eGen, hc]

private theorem sp_mem_center : sp ∈ Subgroup.center TripleCover := by
  rw [Subgroup.mem_center_iff]
  have hle : Subgroup.closure (eGen '' Set.Iio 8) ≤ Subgroup.centralizer {sp} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (eGen_comm_sp c)
  intro g
  have hg : g ∈ Subgroup.closure (eGen '' Set.Iio 8) := by
    rw [closure_eGen]
    exact Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

private theorem sp_pow_three : sp ^ 3 = 1 := by
  have hm : spW ++ spW ++ spW ∈ eWords := by
    unfold eWords
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have h := evalWord_eGen_of_mem hm
  rw [evalWord_app, evalWord_app] at h
  rw [pow_three, ← mul_assoc]
  exact h

private theorem liftArrs_rels
    : ∀ w ∈ eWords, evalWord (arrGen 1134 liftArrs) w = 1 :=
  evalWord_arrGen_eq_one relators_check.2.2.2.1 relators_check.2.2.2.2.1

private noncomputable def coverPerm
    : TripleCover →* Equiv.Perm (Fin 1134) :=
  eHom (arrGen 1134 liftArrs) (fun _ hc => arrGen_of_le (by rw [relators_check.2.2.1]; exact hc))
    liftArrs_rels

private theorem sp_ne_one : sp ≠ 1 := by
  intro h
  have h1 : coverPerm sp = 1 := by rw [h, map_one]
  rw [sp, coverPerm, eHom_evalWord] at h1
  have h2 := (eqA_iff (rep_evalW relators_check.2.2.2.1 spW) rep_idA).2 h1
  rw [relators_check.2.2.2.2.2] at h2
  exact Bool.false_ne_true h2

private theorem orderOf_sp : orderOf sp = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime sp_pow_three sp_ne_one

private theorem card_zpowers_sp
    : Nat.card (Subgroup.zpowers sp) = 3 := by
  rw [Nat.card_zpowers, orderOf_sp]

private theorem yRels_eq : yRels 3 2 2 = coxWords ++ [spW] := by decide +kernel

private theorem coxWords_sub : ∀ w ∈ coxWords, w ∈ eWords := fun w hw => by
  unfold eWords
  exact List.mem_append_left _ (List.mem_append_left _ hw)

private theorem f1_mem : y322WordF1 ∈ eWords := by
  unfold eWords
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))

private theorem evalWord_const {G : Type*} [Group G] (a : G) (w : List ℕ) :
    evalWord (fun _ => a) w = a ^ w.length := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, ih, List.length_cons, pow_succ']

private theorem commutator_cover : commutator TripleCover = ⊤ := by
  set a : ℕ → Abelianization TripleCover := fun c => Abelianization.of (eGen c) with ha
  have hsq : ∀ c, a c * a c = 1 := fun c => by
    simp only [ha, ← map_mul, eGen_mul_self, map_one]
  have hinv : ∀ c, (a c)⁻¹ = a c := fun c => inv_eq_of_mul_eq_one_left (hsq c)
  have hval : ∀ w ∈ eWords, evalWord a w = 1 := fun w hw => by
    rw [ha, ← map_evalWord' Abelianization.of eGen w, evalWord_eGen_of_mem hw, map_one]
  have hedge : ∀ e ∈ [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)],
      [e.1, e.2, e.1, e.2, e.1, e.2] ∈ eWords := by decide +kernel
  have hadj : ∀ e ∈ [(0, 1), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (6, 7)],
      a e.2 = a e.1 := fun e he => by
    have h := hval _ (hedge e he)
    simp only [evalWord_cons, evalWord_nil, mul_one] at h
    have h' : a e.1 * a e.2 = 1 := by
      calc a e.1 * a e.2 = (a e.1 * a e.1) * (a e.1 * a e.2) * (a e.2 * a e.2) := by
            rw [hsq, hsq, one_mul, mul_one]
        _ = a e.1 * (a e.2 * (a e.1 * (a e.2 * (a e.1 * a e.2)))) := by
            simp only [mul_comm, mul_left_comm]
        _ = 1 := h
    rw [← hinv (e.1), eq_inv_iff_mul_eq_one, mul_comm]
    exact h'
  have hall : ∀ c < 8, a c = a 0 := by
    have h01 := hadj (0, 1) (by simp)
    have h04 := hadj (0, 4) (by simp)
    have h06 := hadj (0, 6) (by simp)
    have h12 := hadj (1, 2) (by simp)
    have h23 := hadj (2, 3) (by simp)
    have h45 := hadj (4, 5) (by simp)
    have h67 := hadj (6, 7) (by simp)
    simp only at h01 h04 h06 h12 h23 h45 h67
    intro c hc
    interval_cases c <;> simp_all
  have hf1 := hval _ f1_mem
  rw [evalWord_congr (g' := fun _ => a 0) (fun c hc => hall c (by
    have : ∀ c ∈ y322WordF1, c < 8 := by decide
    exact this c hc)), evalWord_const] at hf1
  have hlen : y322WordF1.length = 63 := by decide
  have h0 : a 0 = 1 := by
    rw [hlen, show 63 = 2 * 31 + 1 by norm_num, pow_succ, pow_mul, pow_two, hsq, one_pow,
      one_mul] at hf1
    exact hf1
  rw [eq_top_iff, ← closure_eGen, Subgroup.closure_le, ← Abelianization.ker_of]
  rintro _ ⟨c, hc, rfl⟩
  exact (hall c hc).trans h0

private theorem map_eq_one_of_comm {A : Type*} [CommGroup A] (f : TripleCover →* A)
    (x : TripleCover) : f x = 1 :=
  Abelianization.commutator_subset_ker f (commutator_cover ▸ Subgroup.mem_top x)

private theorem card_y322'
    : Nat.card (YGroup 3 2 2) = 9170703360 := card_y322

private instance : Finite (YGroup 3 2 2) :=
  Nat.finite_of_card_ne_zero (by rw [card_y322']; norm_num)

private theorem card_range_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

private instance zpowers_sp_normal : (Subgroup.zpowers sp).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 sp_mem_center)

private theorem quotient_rels :
    ∀ w ∈ yRels 3 2 2,
      evalWord (fun c => (QuotientGroup.mk (eGen c) : TripleCover ⧸ Subgroup.zpowers sp)) w =
        1 := by
  intro w hw
  have hm := map_evalWord' (QuotientGroup.mk' (Subgroup.zpowers sp)) eGen w
  simp only [QuotientGroup.mk'_apply] at hm
  rw [← hm, QuotientGroup.eq_one_iff]
  rw [yRels_eq, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · rw [evalWord_eGen_of_mem (coxWords_sub w hw)]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers sp

private theorem card_cover
    : Finite TripleCover ∧ Nat.card TripleCover ≤ 3 * 4585351680 := by
  have := zpowers_sp_normal
  set σ := yModelHom (p := 3) (q := 2) (r := 2) _ quotient_rels
  have hσ : ∀ c < 8, σ (yGen 3 2 2 c) = QuotientGroup.mk (eGen c) := fun c hc =>
    yModelHom_yGen (by simpa [ngen] using hc)
  have hsurj : σ.range = ⊤ := by
    rw [range_yModelHom, eq_top_iff]
    have hmk : (⊤ : Subgroup (TripleCover ⧸ Subgroup.zpowers sp)) =
        (Subgroup.closure (eGen '' Set.Iio 8)).map (QuotientGroup.mk' _) := by
      rw [closure_eGen, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    rw [hmk, MonoidHom.map_closure, Set.image_image]
    exact Subgroup.closure_mono (Set.image_subset_iff.2 fun c hc => ⟨c, by simpa [ngen] using hc,
      rfl⟩)
  have hf1 : y322F1 ∈ σ.ker := by
    rw [MonoidHom.mem_ker, y322F1, map_evalWord',
      evalWord_congr
        (g' := fun c => (QuotientGroup.mk (eGen c) : TripleCover ⧸ Subgroup.zpowers sp))
        (fun c hc => hσ c (by
          have : ∀ c ∈ y322WordF1, c < 8 := by decide
          exact this c hc))]
    have hm := map_evalWord' (QuotientGroup.mk' (Subgroup.zpowers sp)) eGen y322WordF1
    simp only [QuotientGroup.mk'_apply] at hm
    rw [← hm, evalWord_eGen_of_mem f1_mem]
    rfl
  have hker : 2 ≤ Nat.card σ.ker := by
    have hne : σ.ker ≠ ⊥ := fun h => y322F1_ne_one (by rw [← Subgroup.mem_bot, ← h]; exact hf1)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hrange := card_range_mul_card_ker σ
  rw [hsurj, Subgroup.card_top, card_y322'] at hrange
  have hq : Nat.card (TripleCover ⧸ Subgroup.zpowers sp) ≤ 4585351680 := by
    by_contra hlt
    have := Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.lt_of_not_le hlt)) hker
    omega
  have hfinq : Finite (TripleCover ⧸ Subgroup.zpowers sp) :=
    Finite.of_surjective σ (MonoidHom.range_eq_top.1 hsurj)
  have hfinz : Finite (Subgroup.zpowers sp) :=
    Nat.finite_of_card_ne_zero (by rw [card_zpowers_sp]; norm_num)
  have hfin : Finite TripleCover := Finite.of_subgroup_quotient (Subgroup.zpowers sp)
  refine ⟨hfin, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers sp), card_zpowers_sp]
  omega

private theorem tMat_mul_self
    (i : Fin 8) : tMat (vecs i) * tMat (vecs i) = 1 :=
  (vecs_check.2.2.2.1 i).1

private theorem rMat_mul_self
    (i : Fin 8) : rMat (vecs i) * rMat (vecs i) = 1 :=
  (vecs_check.2.2.2.1 i).2

private noncomputable def tG (c : ℕ) : GL Idx (ZMod 3) :=
  if h : c < 8 then ⟨tMat (vecs c), tMat (vecs c), tMat_mul_self ⟨c, h⟩, tMat_mul_self ⟨c, h⟩⟩
  else 1

private noncomputable def rG (c : ℕ) : GL Idx (ZMod 3) :=
  if h : c < 8 then ⟨rMat (vecs c), rMat (vecs c), rMat_mul_self ⟨c, h⟩, rMat_mul_self ⟨c, h⟩⟩
  else 1

private def mOne : GL Idx (ZMod 3) := -1

private theorem rG_eq
    (c : ℕ) (hc : c < 8) : rG c = mOne * tG c := by
  ext i j
  simp only [rG, tG, hc, dite_true, mOne, Units.val_neg, tMat,
    neg_one_mul]
  exact (neg_neg _).symm

private theorem mOne_comm (A : GL Idx (ZMod 3)) : mOne * A = A * mOne := by
  simp [mOne]

private theorem mOne_mul_self : mOne * mOne = 1 := by
  simp [mOne]

private theorem code_lt (v : Idx → ZMod 3) : code v < 2187 := by
  have h : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt (v i)
  have := h (.inl 0); have := h (.inl 1); have := h (.inl 2)
  have := h (.inr (.inl 0)); have := h (.inr (.inl 1)); have := h (.inr (.inl 2))
  have := h (.inr (.inr ()))
  unfold code
  omega

private theorem dec_injective
    : Function.Injective fun x : Fin 2187 => dec x := by
  intro x y h
  have hx := code_dec_check x
  have hy := code_dec_check y
  simp only at h
  rw [h] at hx
  exact Fin.ext (hx.symm.trans hy)

private theorem dec_surjective
    : Function.Surjective fun x : Fin 2187 => dec x := by
  have hcard : Nat.card (Idx → ZMod 3) ≤ Nat.card (Fin 2187) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  exact (dec_injective.bijective_of_nat_card_le hcard).2

private theorem dec_code (v : Idx → ZMod 3) : dec (code v) = v := by
  obtain ⟨x, rfl⟩ := dec_surjective v
  simp only
  rw [code_dec_check x]

private noncomputable def cE : (Idx → ZMod 3) ≃ Fin 2187 where
  toFun v := ⟨code v, code_lt v⟩
  invFun x := dec x
  left_inv v := dec_code v
  right_inv x := Fin.ext (code_dec_check x)

private noncomputable def ψ
    : GL Idx (ZMod 3) →* Equiv.Perm (Fin 2187) :=
  (Equiv.permCongrHom cE).toMonoidHom.comp
    ((MulAction.toPermHom ((Idx → ZMod 3) ≃ₗ[ZMod 3] (Idx → ZMod 3)) (Idx → ZMod 3)).comp
      (ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 3)).toMonoidHom)

private theorem ψ_apply (A : GL Idx (ZMod 3)) (x : Fin 2187) :
    ((ψ A x : Fin 2187) : ℕ) = code ((A : Matrix Idx Idx (ZMod 3)) *ᵥ dec x) := rfl

private theorem ψ_injective : Function.Injective ψ := by
  intro A B h
  apply (ClassicalGroups.Orthogonal.toLinEquiv Idx (ZMod 3)).injective
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := dec_surjective v
  have := congrArg (fun g : Equiv.Perm (Fin 2187) => ((g x : Fin 2187) : ℕ)) h
  simp only [ψ_apply] at this
  rw [ClassicalGroups.Orthogonal.toLinEquiv_apply, ClassicalGroups.Orthogonal.toLinEquiv_apply,
    ← dec_code ((A : Matrix Idx Idx (ZMod 3)) *ᵥ dec x),
    ← dec_code ((B : Matrix Idx Idx (ZMod 3)) *ᵥ dec x), this]

private theorem getElem!_ofFn' {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem rep_tabOf
    {A : GL Idx (ZMod 3)} {M : Matrix Idx Idx (ZMod 3)}
    (hA : (A : Matrix Idx Idx (ZMod 3)) = M) : Rep 2187 (tabOf M) (ψ A) := fun x => by
  rw [tabOf, getElem!_ofFn_nat _ x.2, ψ_apply, hA]

private theorem ψ_tG (c : ℕ) : ψ (tG c) = arrGen 2187 tTabs c := by
  by_cases hc : c < 8
  · have h1 : Rep 2187 tTabs[c]! (ψ (tG c)) := by
      rw [tTabs, getElem!_ofFn' _ hc]
      exact rep_tabOf (by simp [tG, hc])
    have h2 := rep_letterOf vecs_check.2.2.2.2.1 c
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.1]; exact hc)] at h2
    exact Rep.unique h1 h2
  · rw [tG, dite_eq_right hc, map_one, arrGen_of_le (by rw [vecs_check.2.1]; omega)]

private theorem ψ_rG (c : ℕ) : ψ (rG c) = arrGen 2187 rTabs c := by
  by_cases hc : c < 8
  · have h1 : Rep 2187 rTabs[c]! (ψ (rG c)) := by
      rw [rTabs, getElem!_ofFn' _ hc]
      exact rep_tabOf (by simp [rG, hc])
    have h2 := rep_letterOf vecs_check.2.2.2.2.2.1 c
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.2.1]; exact hc)] at h2
    exact Rep.unique h1 h2
  · rw [rG, dite_eq_right hc, map_one, arrGen_of_le (by rw [vecs_check.2.2.1]; omega)]

private theorem evalWord_tG_eq_one
    {w : List ℕ} (hw : w ∈ yRels 3 2 2 ++ eWords) :
    evalWord tG w = 1 := by
  apply ψ_injective
  rw [map_evalWord', map_one]
  simp only [ψ_tG]
  exact evalWord_arrGen_eq_one vecs_check.2.2.2.2.1 relators_check.1 w hw

private theorem evalWord_rG_eq_one
    {w : List ℕ} (hw : w ∈ yRels 3 2 2) :
    evalWord rG w = 1 := by
  apply ψ_injective
  rw [map_evalWord', map_one]
  simp only [ψ_rG]
  exact evalWord_arrGen_eq_one vecs_check.2.2.2.2.2.1 relators_check.2.1 w hw

private noncomputable def τ : YGroup 3 2 2 →* GL Idx (ZMod 3) :=
  yModelHom tG fun _ hw => evalWord_tG_eq_one (List.mem_append_left _ hw)

private noncomputable def ρ : YGroup 3 2 2 →* GL Idx (ZMod 3) :=
  yModelHom rG fun _ hw => evalWord_rG_eq_one hw

private noncomputable def pGL : TripleCover →* GL Idx (ZMod 3) :=
  eHom tG (fun c hc => by simp [tG, show ¬c < 8 by omega])
    fun _ hw => evalWord_tG_eq_one (List.mem_append_right _ hw)

private noncomputable def βf (x : Fin 728) : Fin 2187 :=
  ⟨betaArr[x.val]!, beta_check.2.1 x⟩

private theorem βf_injective : Function.Injective βf := fun x y h =>
  beta_check.2.2.1 x y (congrArg Fin.val h)

private theorem ρ_beta
    (g : YGroup 3 2 2) (x : Fin 728) : ψ (ρ g) (βf x) = βf (y322Model g x) := by
  let S : Subgroup (YGroup 3 2 2) :=
    { carrier := {g | ∀ x, ψ (ρ g) (βf x) = βf (y322Model g x)}
      one_mem' := fun x => by simp
      mul_mem' := fun {g h} hg hh x => by
        simp only [Set.mem_ofPred_eq] at hg hh ⊢
        rw [map_mul, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hh x, hg]
      inv_mem' := fun {g} hg x => by
        simp only [Set.mem_ofPred_eq, map_inv] at hg ⊢
        have := hg ((y322Model g)⁻¹ x)
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
        rw [Equiv.Perm.inv_eq_iff_eq, this] }
  have hS : Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩ x
    have hc' : c < 8 := by simpa [ngen] using hc
    have hρ : ρ (yGen 3 2 2 c) = rG c := yModelHom_yGen hc
    rw [hρ, ψ_rG]
    apply Fin.ext
    have h1 := (rep_letterOf vecs_check.2.2.2.2.2.1 c) (βf x)
    rw [letterOf, ite_eq_left (by rw [vecs_check.2.2.1]; exact hc')] at h1
    rw [← h1, βf]
    simp only
    rw [beta_check.2.2.2 ⟨c, hc'⟩ x, (y322Model_rep hc') x]
    rfl
  exact (hS (by rw [closure_yGen]; trivial)) x

private theorem ρ_injective :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply y322Model_injective
  rw [map_one]
  ext x
  have := ρ_beta g x
  rw [hg, map_one, Equiv.Perm.one_apply] at this
  rw [βf_injective this.symm]
  rfl

private theorem ρ_eq_or
    (g : YGroup 3 2 2) : ρ g = τ g ∨ ρ g = mOne * τ g := by
  let S : Subgroup (YGroup 3 2 2) :=
    { carrier := {g | ρ g = τ g ∨ ρ g = mOne * τ g}
      one_mem' := Or.inl (by simp)
      mul_mem' := fun {g h} hg hh => by
        simp only [Set.mem_ofPred_eq, map_mul] at hg hh ⊢
        rcases hg with hg | hg <;> rcases hh with hh | hh <;> rw [hg, hh]
        · exact Or.inl rfl
        · right; rw [← mul_assoc, ← mOne_comm, mul_assoc]
        · right; rw [mul_assoc]
        · left; rw [mul_assoc, ← mul_assoc (τ g), ← mOne_comm, ← mul_assoc, ← mul_assoc,
            mOne_mul_self, one_mul]
      inv_mem' := fun {g} hg => by
        simp only [Set.mem_ofPred_eq, map_inv] at hg ⊢
        rcases hg with hg | hg <;> rw [hg]
        · exact Or.inl rfl
        · right
          rw [_root_.mul_inv_rev, mOne_comm, inv_eq_of_mul_eq_one_left mOne_mul_self] }
  have hS : Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c < 8 := by simpa [ngen] using hc
    right
    show ρ (yGen 3 2 2 c) = mOne * τ (yGen 3 2 2 c)
    rw [ρ, τ, yModelHom_yGen hc, yModelHom_yGen hc, rG_eq c hc']
  exact hS (by rw [closure_yGen]; trivial)

private theorem card_range_pGL :
    4585351680 ≤ Nat.card pGL.range := by
  have hker : Nat.card τ.ker ≤ 2 := by
    let f : τ.ker → ({1, mOne} : Set (GL Idx (ZMod 3))) := fun g =>
      ⟨ρ g, by
        rcases ρ_eq_or g with h | h <;> rw [h, MonoidHom.mem_ker.1 g.2]
        · exact Or.inl rfl
        · exact Or.inr (mul_one _)⟩
    have hf : Function.Injective f := fun g h hgh =>
      Subtype.ext (ρ_injective (congrArg Subtype.val hgh))
    calc Nat.card τ.ker ≤ Nat.card ({1, mOne} : Set (GL Idx (ZMod 3))) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hrange : pGL.range = τ.range := by
    rw [pGL, range_eHom, τ, range_yModelHom]
    rfl
  have h := card_range_mul_card_ker τ
  rw [card_y322'] at h
  rw [hrange]
  by_contra hlt
  have := Nat.mul_le_mul (Nat.le_sub_one_of_lt (Nat.lt_of_not_le hlt)) hker
  omega

private theorem pGL_sp : pGL sp = 1 := by
  rw [sp, pGL, eHom_evalWord]
  exact evalWord_tG_eq_one (List.mem_append_left _ (by rw [yRels_eq]; simp))

section Field

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
include hK

private theorem charP_three : CharP K 3 := by
  have h := ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_three le_rfl
    (by rw [hK, pow_one] : Nat.card K = 3 ^ 1)
  rw [← h]
  exact ringChar.charP K

private noncomputable def φK : ZMod 3 →+* K :=
  have := charP_three hK
  ZMod.castHom (dvd_refl 3) K

private theorem φK_bijective : Function.Bijective (φK hK) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (φK hK).injective.bijective_of_nat_card_le ?_
  rw [hK, Nat.card_eq_fintype_card, ZMod.card]

private theorem quad_comp (w : Idx → ZMod 3) :
    Assembly.LowTwoRank.StatedQuadOdd 3 K (φK hK ∘ w) = φK hK (q3 w) := by
  simp [Assembly.LowTwoRank.StatedQuadOdd, q3, Fin.sum_univ_three]

private theorem tG_isometry (c : ℕ) (v : Idx → K) :
    Assembly.LowTwoRank.StatedQuadOdd 3 K
        ((Matrix.GeneralLinearGroup.map (φK hK) (tG c) : Matrix Idx Idx K) *ᵥ v) =
      Assembly.LowTwoRank.StatedQuadOdd 3 K v := by
  obtain ⟨w, rfl⟩ : ∃ w : Idx → ZMod 3, φK hK ∘ w = v :=
    ⟨fun i => Function.surjInv (φK_bijective hK).2 (v i),
      funext fun i => Function.surjInv_eq (φK_bijective hK).2 (v i)⟩
  have hmul : (Matrix.GeneralLinearGroup.map (φK hK) (tG c) : Matrix Idx Idx K) *ᵥ
      (φK hK ∘ w) = φK hK ∘ ((tG c : Matrix Idx Idx (ZMod 3)) *ᵥ w) := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    rfl
  rw [hmul, quad_comp, quad_comp]
  congr 1
  by_cases hc : c < 8
  · obtain ⟨x, rfl⟩ := dec_surjective w
    have h := vecs_check.2.2.2.2.2.2 ⟨c, hc⟩ x
    simp only [tG, dite_eq_left hc]
    exact h
  · simp [tG, hc]

private noncomputable def pK : TripleCover →* GL Idx K :=
  (Matrix.GeneralLinearGroup.map (φK hK)).comp pGL

private theorem range_pK_le :
    (pK hK).range ≤ Assembly.LowTwoRank.StatedOmega (Assembly.LowTwoRank.StatedQuadOdd 3 K) := by
  set S := Subgroup.closure {A : GL Idx K | ∀ v,
    Assembly.LowTwoRank.StatedQuadOdd 3 K ((A : Matrix Idx Idx K) *ᵥ v) =
      Assembly.LowTwoRank.StatedQuadOdd 3 K v}
  have hle : (pK hK).range ≤ S := by
    rw [pK, MonoidHom.range_comp, pGL, range_eHom, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact Subgroup.subset_closure (tG_isometry hK c)
  have hperf : ⁅(pK hK).range, (pK hK).range⁆ = (pK hK).range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, commutator_cover]
  rw [← hperf]
  exact Subgroup.commutator_mono hle hle

private theorem eq_one_of_scalar
    {A : GL Idx K} (hA : A ∈ (pK hK).range)
    (hs : A ∈ Assembly.LowTwoRank.StatedScalars Idx K) : A = 1 := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨x, hx⟩ := hA
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar Idx u) = 1 := by
    rw [← hx]
    exact map_eq_one_of_comm (Matrix.GeneralLinearGroup.det.comp (pK hK)) x
  rw [Matrix.GeneralLinearGroup.det_scalar] at hdet
  have hcard : Fintype.card Idx = 7 := rfl
  have := Fintype.ofFinite K
  have hu2 : u ^ 2 = 1 := by
    ext
    have := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
    rw [hc] at this
    simpa using this
  have hu : u = 1 := by
    rw [hcard, show 7 = 2 * 3 + 1 by norm_num, pow_succ, pow_mul, hu2, one_pow, one_mul] at hdet
    exact hdet
  rw [hu, map_one]

end Field

private theorem ordBC_three : CFSG.Open.ordBC 3 3 = 4585351680 := by decide

theorem exists_perfectCentralExtension_card_ker_three
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .POmegaOdd 3 3 1) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (p : E →* X),
      IsPerfectCentralExtension X p ∧ Nat.card p.ker = 3 := by
  obtain ⟨-, hm⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩ := h
  rotate_left
  · exact absurd hce (by decide)
  · exact absurd hrt (by decide)
  · exact absurd hsz (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  obtain ⟨hfin, hcard⟩ := card_cover
  set Ω := Assembly.LowTwoRank.StatedOmega (Assembly.LowTwoRank.StatedQuadOdd 3 K)
  let q : TripleCover →* Assembly.LowTwoRank.StatedProj Ω :=
    (QuotientGroup.mk' _).comp ((pK hK3).codRestrict Ω fun x => range_pK_le hK3 ⟨x, rfl⟩)
  have hkerq : q.ker = pGL.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hs : pK hK3 x ∈ Assembly.LowTwoRank.StatedScalars Idx K := by
        have := (QuotientGroup.eq_one_iff _).1 hx
        exact this
      have h1 := eq_one_of_scalar hK3 ⟨x, rfl⟩ hs
      have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Idx) (φK hK3)) := by
        rw [injective_iff_map_eq_one]
        intro A hA
        ext i j
        have := congrArg (fun B : GL Idx K => (B : Matrix Idx Idx K) i j) hA
        simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
        apply (φK_bijective hK3).1
        simpa [Matrix.one_apply, apply_ite] using this
      exact hinj (h1.trans (map_one _).symm)
    · intro hx
      simp only [q, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_one_iff]
      have : (pK hK3).codRestrict Ω (fun x => range_pK_le hK3 ⟨x, rfl⟩) x = 1 := by
        ext : 1
        simp [pK, hx]
      rw [this]
      exact Subgroup.one_mem _
  have hcardX : Nat.card (Assembly.LowTwoRank.StatedProj Ω) = 4585351680 := by
    rw [← ordBC_three]
    exact ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC Nat.prime_three
      (by norm_num) hK le_rfl
  have hrq : q.range = ⊤ := by
    have h1 := card_range_mul_card_ker q
    have h2 := card_range_mul_card_ker pGL
    rw [hkerq] at h1
    have hpos : 0 < Nat.card pGL.ker := Nat.card_pos
    have hge : 4585351680 ≤ Nat.card q.range := by
      have := card_range_pGL
      nlinarith
    have : Finite (Assembly.LowTwoRank.StatedProj Ω) :=
      Nat.finite_of_card_ne_zero (by rw [hcardX]; norm_num)
    exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
      (hcardX ▸ hge))
  let p : TripleCover →* X := e.symm.toMonoidHom.comp q
  have hsurj : Function.Surjective p :=
    e.symm.surjective.comp (MonoidHom.range_eq_top.1 hrq)
  have hkerp : p.ker = pGL.ker := by
    rw [← hkerq]
    ext x
    simp [p]
  have hcardp : Nat.card p.ker ≤ 3 := by
    have h1 := card_range_mul_card_ker p
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_congr e.toEquiv,
      hcardX] at h1
    omega
  have hsp : Subgroup.zpowers sp ≤ p.ker := by
    rw [Subgroup.zpowers_le, hkerp, MonoidHom.mem_ker]
    exact pGL_sp
  have hfink : Finite p.ker := Subgroup.instFiniteSubtypeMem _
  have hzk : Subgroup.zpowers sp = p.ker :=
    Subgroup.eq_of_le_of_card_ge hsp (by rw [card_zpowers_sp]; exact hcardp)
  refine ⟨TripleCover, inferInstance, hfin, p, ⟨⟨hsurj, ?_⟩, commutator_cover⟩, ?_⟩
  · rw [← hzk]
    exact Subgroup.zpowers_le.2 sp_mem_center
  · rw [← hzk, card_zpowers_sp]

end CFSG.LieType.Multipliers.O73
