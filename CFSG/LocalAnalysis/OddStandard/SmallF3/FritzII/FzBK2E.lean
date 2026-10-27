module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2Spec

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def fzbRep (c : Bool) (i : ℕ) : Array ℕ :=
  ((repImgs c).map (extArr (wordTab ())))[i]!

theorem fzb_modl_tables (c : Bool) :
    (modl c ()).aq = fzbRep c 0 ∧ (modl c ()).as = fzbRep c 1 ∧ (modl c ()).ay = fzbRep c 2 :=
  ⟨rfl, rfl, rfl⟩

theorem fzb_wordsOK : wordsOK (wordTab ()) = true := by decide +kernel

theorem fzbEnc_decB : ∀ n : Fin 64, fzbEnc (fzbDecB n) = n := by decide +kernel

theorem fzbDecB_enc : ∀ x : FzUT, fzbDecB (fzbEnc x) = x := by decide +kernel

theorem fzbEnc_decB' {n : ℕ} (hn : n < 64) : fzbEnc (fzbDecB n) = n := fzbEnc_decB ⟨n, hn⟩

@[expose] def fzbTab (σ : MulAut FzUT) : Array ℕ :=
  Array.ofFn (n := 64) fun i => fzbEnc (σ (fzbDecB i))

theorem fzbTab_get (σ : MulAut FzUT) {i : ℕ} (hi : i < 64) :
    (fzbTab σ)[i]! = fzbEnc (σ (fzbDecB i)) := by
  rw [getElem!_pos (fzbTab σ) i (by simpa [fzbTab] using hi)]
  simp [fzbTab]

theorem fzbTab_enc (σ : MulAut FzUT) (x : FzUT) : (fzbTab σ)[fzbEnc x]! = fzbEnc (σ x) := by
  rw [fzbTab_get σ (fzbEnc_lt x), fzbDecB_enc]

theorem fzb_uMul_enc (x y : FzUT) : uMul (fzbEnc x) (fzbEnc y) = fzbEnc (x * y) :=
  (fzbEnc_mul x y).symm

theorem fzbTab_isAut (σ : MulAut FzUT) : isAutArr (fzbTab σ) = true := by
  have hsz : (fzbTab σ).size = 64 := by simp [fzbTab]
  have hmul : ∀ g < 64, ∀ x < 64,
      (fzbTab σ)[uMul g x]! = uMul (fzbTab σ)[g]! (fzbTab σ)[x]! := by
    intro g hg x hx
    obtain ⟨g', rfl⟩ := fzbEnc_surj hg
    obtain ⟨x', rfl⟩ := fzbEnc_surj hx
    rw [fzb_uMul_enc, fzbTab_enc, fzbTab_enc, fzbTab_enc, map_mul, fzb_uMul_enc]
  simp only [isAutArr, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, fzb_allBelow_iff,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨hsz, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [fzbTab_get σ hx]
    exact fzbEnc_lt _
  · rw [fzbTab_get σ (by norm_num)]
    have : fzbDecB 0 = 1 := by decide +kernel
    rw [this, map_one, fzbEnc_one]
  · intro x hx y hy e
    rw [fzbTab_get σ hx, fzbTab_get σ (by omega)] at e
    have := congrArg fzbEnc (σ.injective (fzbEnc_inj e))
    rw [fzbEnc_decB' hx, fzbEnc_decB' (by omega)] at this
    omega
  · intro i hi x hx
    have hg : gensU[i]! < 64 := by interval_cases i <;> decide
    exact hmul _ hg x hx

@[expose] def fzbAutFun (a : Array ℕ) (x : FzUT) : FzUT := fzbDecB a[fzbEnc x]!

theorem fzbAutFun_enc {a : Array ℕ} (ha : isAutArr a = true) (x : FzUT) :
    fzbEnc (fzbAutFun a x) = a[fzbEnc x]! :=
  fzbEnc_decB' (fzb_isAutArr_lt ha (fzbEnc_lt _))

theorem fzbAutFun_mul {a : Array ℕ} (ha : isAutArr a = true) (x y : FzUT) :
    fzbAutFun a (x * y) = fzbAutFun a x * fzbAutFun a y := by
  apply fzbEnc_inj
  rw [fzbEnc_mul (fzbAutFun a x), fzbAutFun_enc ha, fzbAutFun_enc ha, fzbAutFun_enc ha,
    fzbEnc_mul, fzb_isAutArr_hom fzb_wordsOK ha (fzbEnc_lt x) (fzbEnc_lt y)]

theorem fzbAutFun_inj {a : Array ℕ} (ha : isAutArr a = true) :
    Function.Injective (fzbAutFun a) := by
  intro x y e
  have e' := congrArg fzbEnc e
  rw [fzbAutFun_enc ha, fzbAutFun_enc ha] at e'
  exact fzbEnc_inj (fzb_isAutArr_inj ha (fzbEnc_lt x) (fzbEnc_lt y) e')

@[expose] noncomputable def fzbAut (a : Array ℕ) (ha : isAutArr a = true) : MulAut FzUT :=
  MulEquiv.ofBijective (⟨fzbAutFun a, fzbAutFun_mul ha⟩ : FzUT →ₙ* FzUT)
    ⟨fzbAutFun_inj ha, Finite.injective_iff_surjective.mp (fzbAutFun_inj ha)⟩

theorem fzbAut_enc {a : Array ℕ} (ha : isAutArr a = true) (x : FzUT) :
    fzbEnc (fzbAut a ha x) = a[fzbEnc x]! :=
  fzbAutFun_enc ha x

theorem fzb_all_codes {p : ℕ → Bool} (h : allBelow p 64 = true) (x : FzUT) :
    p (fzbEnc x) = true :=
  (fzb_allBelow_iff p 64).mp h _ (fzbEnc_lt x)

theorem fzb_inZ_decB : ∀ z : Fin 4, FzInZ (fzbDecB z) := by
  unfold FzInZ
  decide +kernel

theorem fzb_commA {a b : Array ℕ} (ha : isAutArr a = true) (hb : isAutArr b = true)
    (h : commA a b = true) (x : FzUT) : fzbAut a ha (fzbAut b hb x) = fzbAut b hb (fzbAut a ha x) := by
  apply fzbEnc_inj
  have := fzb_all_codes h x
  simp only [beq_iff_eq] at this
  rw [fzbAut_enc, fzbAut_enc, fzbAut_enc, fzbAut_enc, this]

theorem fzb_adm {r aq as ay : Array ℕ}
    (hr : isAutArr r = true) (hq : isAutArr aq = true) (hs : isAutArr as = true)
    (hy : isAutArr ay = true) (hrho : isRho r = true) (hQ : condQ r aq = true)
    (hS : condS r aq as = true) (hinv : isInvR r ay = true) (hyq : commA ay aq = true)
    (hys : commA ay as = true) :
    FzbAdm (fzbAut r hr) (fzbAut aq hq) (fzbAut as hs) (fzbAut ay hy) := by
  set R := fzbAut r hr
  set Q := fzbAut aq hq
  set S := fzbAut as hs
  set Y := fzbAut ay hy
  have eR : ∀ x, fzbEnc (R x) = r[fzbEnc x]! := fzbAut_enc hr
  have eQ : ∀ x, fzbEnc (Q x) = aq[fzbEnc x]! := fzbAut_enc hq
  have eS : ∀ x, fzbEnc (S x) = as[fzbEnc x]! := fzbAut_enc hs
  have eY : ∀ x, fzbEnc (Y x) = ay[fzbEnc x]! := fzbAut_enc hy
  simp only [isRho, Bool.and_eq_true] at hrho
  simp only [condQ, Bool.and_eq_true] at hQ
  simp only [condS, Bool.and_eq_true, Bool.or_eq_true] at hS
  simp only [isInvR, Bool.and_eq_true] at hinv
  obtain ⟨hr1, hr2⟩ := hrho
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hQ
  obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := hS
  obtain ⟨hy1, hy2⟩ := hinv
  refine ⟨?_, ?_, fzb_commA hq hr hq1, ?_, ?_, fzb_commA hs hr hs1, ?_, ?_, ?_, ?_, ?_, ?_,
    fzb_commA hy hq hyq, fzb_commA hy hs hys⟩
  · intro x
    apply fzbEnc_inj
    have := fzb_all_codes hr2 x
    simp only [beq_iff_eq] at this
    rw [eR, eR, eR, this]
  · intro x hx e
    have := fzb_all_codes hr1 x
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at this
    rcases this with h0 | h0
    · exact hx (fzbEnc_inj (by rw [h0, fzbEnc_one]))
    · exact h0 (by rw [← eR, e])
  · intro x
    apply fzbEnc_inj
    have := fzb_all_codes hq2 x
    simp only [beq_iff_eq] at this
    rw [eQ, eQ, eQ, eQ, this]
  · rw [fzb_countBelow_eq] at hq3
    simp only [beq_iff_eq] at hq3
    rw [← hq3]
    apply Finset.card_bij (fun x _ => fzbEnc x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_filter, Finset.mem_range, beq_iff_eq]
      exact ⟨fzbEnc_lt x, by rw [← eQ, ← eQ, hx]⟩
    · intro x _ y _ e
      exact fzbEnc_inj e
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, beq_iff_eq] at hn
      refine ⟨fzbDecB n, ?_, fzbEnc_decB' hn.1⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply fzbEnc_inj
      rw [eQ, eQ, fzbEnc_decB' hn.1, hn.2]
  · have key : ∀ k : ℕ, ∀ x, fzbEnc ((Q ^ k) x) = Nat.iterate (fun n => aq[n]!) k (fzbEnc x) := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, eQ, Function.iterate_succ_apply]
    rcases hs2 with ((h | h) | h) | h
    · refine ⟨0, fun x => fzbEnc_inj ?_⟩
      have := fzb_all_codes h x
      simp only [beq_iff_eq] at this
      rw [eS, eS, this, key]
      rfl
    · refine ⟨1, fun x => fzbEnc_inj ?_⟩
      have := fzb_all_codes h x
      simp only [beq_iff_eq] at this
      rw [eS, eS, this, key]
      rfl
    · refine ⟨2, fun x => fzbEnc_inj ?_⟩
      have := fzb_all_codes h x
      simp only [beq_iff_eq] at this
      rw [eS, eS, this, key]
      rfl
    · refine ⟨3, fun x => fzbEnc_inj ?_⟩
      have := fzb_all_codes h x
      simp only [beq_iff_eq] at this
      rw [eS, eS, this, key]
      rfl
  · rcases hs3 with h | h
    · exact Or.inl (fzb_commA hs hq h)
    · right
      intro x
      apply fzbEnc_inj
      have := fzb_all_codes h x
      simp only [beq_iff_eq] at this
      rw [eS, eQ, this, eQ, eQ, eQ, eS]
  · intro x e
    have := fzb_all_codes hs4 x
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at this
    rcases this with h | h
    · exact absurd (by rw [← eQ, ← eQ, e]) h
    · apply fzbEnc_inj
      rw [fzbEnc_mul, eS, h, fzbEnc_one]
  · intro x
    have := fzb_all_codes hs5 x
    rw [fzb_anyBelow_iff] at this
    obtain ⟨z, hz, e⟩ := this
    simp only [beq_iff_eq] at e
    have hSx : S x = fzbDecB z * x := by
      apply fzbEnc_inj
      rw [eS, e, fzbEnc_mul, fzbEnc_decB' (by omega)]
    rw [hSx, mul_inv_cancel_right]
    exact fzb_inZ_decB ⟨z, hz⟩
  · intro x
    apply fzbEnc_inj
    have := fzb_all_codes hy1 x
    simp only [beq_iff_eq] at this
    rw [eY, eY, this]
  · intro x
    apply fzbEnc_inj
    have := fzb_all_codes hy2 x
    simp only [beq_iff_eq] at this
    rw [eY, eR, this, eR, eR, eY]

theorem fzb_conjP_tab {g b : MulAut FzUT} {a : Array ℕ} (ha : isAutArr a = true)
    (h : ∀ x, g (fzbAut a ha x) = b (g x)) : conjP (fzbTab g) a (fzbTab b) = true := by
  rw [conjP, fzb_allBelow_iff]
  intro i hi
  obtain ⟨y, rfl⟩ := fzbEnc_surj hi
  rw [beq_iff_eq, ← fzbAut_enc ha, fzbTab_enc, fzbTab_enc, fzbTab_enc, h]

theorem fzbDecB_gens : fzbDecB 16 = fzE1 ∧ fzbDecB 32 = fzEW ∧ fzbDecB 4 = fzF1 ∧
    fzbDecB 8 = fzFW := by decide +kernel

theorem fzb_repImgs_lt : ∀ c : Bool, ∀ i < 3, ∀ j < 4, ((repImgs c)[i]!)[j]! < 64 := by
  decide +kernel

theorem fzb_repImgs_eta (c : Bool) (i : ℕ) (hi : i < 3) :
    (repImgs c)[i]! = #[((repImgs c)[i]!)[0]!, ((repImgs c)[i]!)[1]!, ((repImgs c)[i]!)[2]!,
      ((repImgs c)[i]!)[3]!] := by
  cases c <;> interval_cases i <;> rfl

theorem fzbRep_eq (c : Bool) {i : ℕ} (hi : i < 3) (B : MulAut FzUT) (hB : fzGens B = fzbRepD c i) :
    fzbRep c i = fzbTab B := by
  have hext := fzb_extArr_eq fzb_wordsOK (fzbTab_isAut B)
  have e1 : (fzbTab B)[16]! = ((repImgs c)[i]!)[0]! := by
    rw [fzbTab_get B (by norm_num), fzbDecB_gens.1]
    have := congrArg FzAutD.g1 hB
    change B fzE1 = _ at this
    rw [this, fzbRepD, fzbEnc_decB' (fzb_repImgs_lt c i hi 0 (by norm_num))]
  have e2 : (fzbTab B)[32]! = ((repImgs c)[i]!)[1]! := by
    rw [fzbTab_get B (by norm_num), fzbDecB_gens.2.1]
    have := congrArg FzAutD.g2 hB
    change B fzEW = _ at this
    rw [this, fzbRepD, fzbEnc_decB' (fzb_repImgs_lt c i hi 1 (by norm_num))]
  have e3 : (fzbTab B)[4]! = ((repImgs c)[i]!)[2]! := by
    rw [fzbTab_get B (by norm_num), fzbDecB_gens.2.2.1]
    have := congrArg FzAutD.g3 hB
    change B fzF1 = _ at this
    rw [this, fzbRepD, fzbEnc_decB' (fzb_repImgs_lt c i hi 2 (by norm_num))]
  have e4 : (fzbTab B)[8]! = ((repImgs c)[i]!)[3]! := by
    rw [fzbTab_get B (by norm_num), fzbDecB_gens.2.2.2]
    have := congrArg FzAutD.g4 hB
    change B fzFW = _ at this
    rw [this, fzbRepD, fzbEnc_decB' (fzb_repImgs_lt c i hi 3 (by norm_num))]
  rw [e1, e2, e3, e4, ← fzb_repImgs_eta c i hi] at hext
  have hsz : (repImgs c).size = 3 := by cases c <;> rfl
  have hi' : i < (repImgs c).size := by rw [hsz]; exact hi
  have hi'' : i < ((repImgs c).map (extArr (wordTab ()))).size := by rw [Array.size_map]; exact hi'
  rw [← hext, fzbRep, getElem!_pos _ i hi'', Array.getElem_map, ← getElem!_pos (repImgs c) i hi']

theorem fzb_classSpec_extract (h : FzbClassSpec) {r aq as ay : Array ℕ}
    (hr : isAutArr r = true) (hq : isAutArr aq = true) (hs : isAutArr as = true)
    (hy : isAutArr ay = true) (hrho : isRho r = true) (hQ : condQ r aq = true)
    (hS : condS r aq as = true) (hinv : isInvR r ay = true) (hyq : commA ay aq = true)
    (hys : commA ay as = true) :
    wordsOK (wordTab ()) = true ∧ ∃ (c : Bool) (g : Array ℕ), isAutArr g = true ∧
      conjP g aq (fzbRep c 0) = true ∧ conjP g as (fzbRep c 1) = true ∧
      conjP g ay (fzbRep c 2) = true ∧
      repOK (fzbRep c 0) (fzbRep c 1) (fzbRep c 2) = true := by
  have A := fzb_adm hr hq hs hy hrho hQ hS hinv hyq hys
  obtain ⟨c, G, -, hgq, hgs, hgy, hs2, hsq⟩ := h _ _ _ _ A
  have bq := fzbRep_eq c (by norm_num) _ hgq
  have bs := fzbRep_eq c (by norm_num) _ hgs
  have bY := fzbRep_eq c (by norm_num) _ hgy
  have cj : ∀ σ : MulAut FzUT, ∀ x, G (σ x) = (G * σ * G⁻¹) (G x) := fun σ x => by
    change G (σ x) = G (σ (G⁻¹ (G x)))
    rw [MulAut.inv_apply_self]
  have back : ∀ σ : MulAut FzUT, ∀ x, (G * σ * G⁻¹) x = G (σ (G⁻¹ x)) := fun _ _ => rfl
  refine ⟨fzb_wordsOK, c, fzbTab G, fzbTab_isAut G, ?_, ?_, ?_, ?_⟩
  · rw [bq]
    exact fzb_conjP_tab hq (cj (fzbAut aq hq))
  · rw [bs]
    exact fzb_conjP_tab hs (cj (fzbAut as hs))
  · rw [bY]
    exact fzb_conjP_tab hy (cj (fzbAut ay hy))
  rw [bq, bs, bY]
  have ex : ∃ y, fzbAut aq hq (fzbAut aq hq y) ≠ y := by
    by_contra hall
    push Not at hall
    have hf := A.q_fix
    rw [Finset.filter_true_of_mem (fun x _ => hall x)] at hf
    exact absurd hf (by decide)
  obtain ⟨y0, hy0⟩ := ex
  have q4 := A.q4
  have ysq := A.y_sq
  have yq := A.y_q
  have ys := A.y_s
  simp only [repOK, Bool.and_eq_true, fzb_allBelow_iff, fzb_anyBelow_iff, beq_iff_eq,
    bne_iff_ne, commA]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨fzbTab_isAut _, fzbTab_isAut _⟩, fzbTab_isAut _⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, q4, MulAut.apply_inv_self]
  · refine ⟨fzbEnc (G y0), fzbEnc_lt _, ?_⟩
    simp only [fzbTab_enc, back, MulAut.inv_apply_self]
    intro e
    exact hy0 (G.injective (fzbEnc_inj e))
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, hs2, MulAut.apply_inv_self]
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, hsq]
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, ysq, MulAut.apply_inv_self]
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, yq]
  · intro n hn
    obtain ⟨y, rfl⟩ := fzbEnc_surj hn
    simp only [fzbTab_enc, back, MulAut.inv_apply_self, ys]

end CFSG.OddStandard.SmallF3.FritzII
