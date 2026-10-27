module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLatWit

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

@[expose] def litEls (wg : List ℕ) : List Γ := C.sg ++ [wordElt C.a C.b wg]

@[expose] def litGrp (wg : List ℕ) : Subgroup Γ := Subgroup.closure {x | x ∈ C.litEls wg}

theorem litEls_tabs (wg : List ℕ) (hw : ∀ l ∈ wg, l < 2) :
    genTabs n (C.litEls wg) = C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg] := by
  have hel : ∀ l < (#[C.a, C.b] : Array Γ).size, (#[C.ta, C.tb] : Array (Array ℕ)).getD l #[] =
      (tab n ((#[C.a, C.b] : Array Γ).getD l 1)).toArray := C.hel0'
  have h := (wordTabA_eq (n := n) #[C.a, C.b] #[C.ta, C.tb] hel wg (by simpa using hw)).symm
  unfold litEls
  rw [genTabs_append, C.hsg]
  unfold wordElt
  rw [← h]
  rfl

theorem S_le_litGrp (wg : List ℕ) : C.S ≤ C.litGrp wg := by
  rw [← C.hSeq]
  apply Subgroup.closure_mono
  intro x hx
  exact List.mem_append_left _ hx

variable {wg : List ℕ} {Ω : OmegaData Lab}

theorem litGrp_card (hw : ∀ l ∈ wg, l < 2)
    (hΩ : OmegaSpec C.A.act (C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg]).toArray C.Δ Ω) :
    Nat.card (C.litGrp wg) = Ω.lbl.size * 2 ^ C.k := by
  rw [← C.litEls_tabs wg hw] at hΩ
  have := hΩ.card_eq C.hlaw C.hΔ (C.litEls wg).toArray (genTabs_size _).symm (genTabs_hel' _)
    (H := C.litGrp wg) (by rw [toList_toArray_set]; rfl) (C.S_le_litGrp wg)
  rw [this]
  congr 1
  exact C.S_card

theorem Λ_sub (hw : ∀ l ∈ wg, l < 2)
    (hΩ : OmegaSpec C.A.act (C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg]).toArray C.Δ Ω)
    {j : ℕ} (hj : j < C.J) (hZ : C.litGrp wg = C.Y j) : ∀ x ∈ C.Λ j, x ∈ Ω.lbl.toList := by
  rw [← C.litEls_tabs wg hw] at hΩ
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < C.D.Om[j]!.lbl.size := by simpa [Λ] using hi
  rw [C.Λ_getElem i hi]
  set els := (C.sg ++ C.gens j).toArray with hels
  have hreach := (C.hOm hj).reach C.hlaw C.hΔ els (genTabs_hel' _) i i le_rfl hi'
  have hmem : evalElt els (C.D.Om[j]!.pathWord i i) ∈ C.Y j := by
    refine evalElt_mem els (fun l hl => ?_) _ (fun l hl => ?_)
    · have := evalElt_getD_mem_closure els hl
      rw [hels, toList_toArray_set] at this
      exact this
    · have := (C.hOm hj).pathWord_lt i i hi' l hl
      rw [genTabs_size] at this
      exact this
  rw [← hZ] at hmem
  obtain ⟨x', hx', hlab⟩ := (hΩ.mem_iff C.hlaw C.hΔ (C.litEls wg).toArray (genTabs_size _).symm
    (genTabs_hel' _) (H := C.litGrp wg) (by rw [toList_toArray_set]; rfl) (C.S_le_litGrp wg)
    _).1 hmem
  rw [← hreach, hlab, getElem!_pos _ x' hx']
  exact Array.getElem_mem_toList _

end CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type} [DecidableEq Lab]

theorem quotElt_mem_closure (E : List Γ) (x : QuotGen) (hw : ∀ l ∈ x.w, l < E.length) :
    quotElt E x ∈ Subgroup.closure {y | y ∈ E} := by
  have hels : ∀ l < E.toArray.size, E.toArray.getD l 1 ∈ Subgroup.closure {y | y ∈ E} := by
    intro l hl
    have := evalElt_getD_mem_closure E.toArray hl
    rw [LatCtx.toList_toArray_set] at this
    exact this
  exact Subgroup.pow_mem _ (evalElt_mem E.toArray hels x.w (by simpa using hw)) _

theorem wit3_sound_of {lact : Array ℕ → Lab → Lab} (E : List Γ) {lbls : List Lab}
    (hcore : ∀ z : Γ, (∀ x ∈ lbls, lact (tab n z).toArray x = x) →
      z ∈ pCoreOf 2 (Subgroup.closure {y | y ∈ E}))
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {b q₁ q₂ : QuotGen} (h : Wit3Ok n lact (genTabs n E) lbls b q₁ q₂) :
    ∃ b' ∈ Subgroup.closure {y | y ∈ E}, orderOf b' = 3 ∧
      ∃ x ∈ ⁅pCoreOf 2 (Subgroup.closure {y | y ∈ E}), Subgroup.zpowers b'⁆,
      ∃ y ∈ ⁅pCoreOf 2 (Subgroup.closure {y | y ∈ E}), Subgroup.zpowers b'⁆,
        x * y ≠ y * x ∨ x * x ≠ 1 := by
  obtain ⟨hlet, hbm, hb1, hb3, hq, hne⟩ := h
  have hlen : ∀ x : QuotGen, x ∈ [b, q₁, q₂] → ∀ l ∈ x.w, l < E.length := by
    intro x hx l hl
    have := (hlet x hx).1 l hl
    simpa [genTabs_length] using this
  have hwb := hlen b (by simp)
  have hw1 := hlen q₁ (by simp)
  have hw2 := hlen q₂ (by simp)
  have hm1 : 0 < q₁.m := (hlet q₁ (by simp)).2
  have hm2 : 0 < q₂.m := (hlet q₂ (by simp)).2
  have hTb := quotGt_eq (n := n) E b hwb
  have hb1' : quotElt E b ≠ 1 := by
    intro h1
    apply hb1
    rw [hTb, h1, tab_one_toArray]
  have hb3' : quotElt E b ^ 3 = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hTb]
    exact hb3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (quotElt E b) = 3 := orderOf_eq_prime hb3' hb1'
  obtain ⟨-, hinv1⟩ := quotGi_eq (n := n) hB hbase E q₁ hw1 hm1 (hq q₁ (by simp)).1
  obtain ⟨-, hinv2⟩ := quotGi_eq (n := n) hB hbase E q₂ hw2 hm2 (hq q₂ (by simp)).1
  obtain ⟨-, hinvb⟩ := quotGi_eq (n := n) hB hbase E b hwb (by omega) (by rw [hbm]; exact hb3)
  have hcomm : ∀ (q : QuotGen), (∀ l ∈ q.w, l < E.length) → quotGi n (genTabs n E) q =
      (tab n (quotElt E q)⁻¹).toArray →
      (tab n (⁅quotElt E q, quotElt E b⁆)).toArray = commOf n (genTabs n E) q b := by
    intro q hwq hinvq
    rw [commutatorElement_def, tabArr_comm]
    unfold commOf
    rw [hinvq, hinvb, quotGt_eq (n := n) E q hwq, hTb]
  have hmem : ∀ q : QuotGen, (∀ l ∈ q.w, l < E.length) →
      (∀ x ∈ lbls, lact (quotGt n (genTabs n E) q) x = x) →
      ⁅quotElt E q, quotElt E b⁆ ∈
        ⁅pCoreOf 2 (Subgroup.closure {y | y ∈ E}), Subgroup.zpowers (quotElt E b)⁆ := by
    intro q hwq hfix
    refine Subgroup.commutator_mem_commutator ?_ (Subgroup.mem_zpowers _)
    apply hcore
    rw [← quotGt_eq (n := n) E q hwq]
    exact hfix
  refine ⟨quotElt E b, quotElt_mem_closure E b hwb, hord, ⁅quotElt E q₁, quotElt E b⁆,
    hmem q₁ hw1 (hq q₁ (by simp)).2, ⁅quotElt E q₂, quotElt E b⁆,
    hmem q₂ hw2 (hq q₂ (by simp)).2, ?_⟩
  have h1 := hcomm q₁ hw1 hinv1
  have h2 := hcomm q₂ hw2 hinv2
  rcases hne with hne | hne
  · left
    intro hxy
    apply hne
    rw [← h1, ← h2, ← tabArr_mul, ← tabArr_mul, hxy]
  · right
    intro hxx
    apply hne
    rw [← h1, ← tabArr_mul, hxx, tab_one_toArray]

theorem witP_sound_of {lact : Array ℕ → Lab → Lab} (E : List Γ) {lbls : List Lab}
    (hcore : ∀ z : Γ, (∀ x ∈ lbls, lact (tab n z).toArray x = x) →
      z ∈ pCoreOf 2 (Subgroup.closure {y | y ∈ E}))
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {p : ℕ} (hp : p.Prime) {b q : QuotGen} (h : WitPOk n lact (genTabs n E) lbls p b q) :
    ∃ b' ∈ Subgroup.closure {y | y ∈ E}, orderOf b' = p ∧
      ∃ q' ∈ pCoreOf 2 (Subgroup.closure {y | y ∈ E}), q' * b' ≠ b' * q' := by
  obtain ⟨hlet, hb1, hbp, hq, hne⟩ := h
  have hwb : ∀ l ∈ b.w, l < E.length := by
    intro l hl
    have := hlet b (by simp) l hl
    simpa [genTabs_length] using this
  have hwq : ∀ l ∈ q.w, l < E.length := by
    intro l hl
    have := hlet q (by simp) l hl
    simpa [genTabs_length] using this
  have hTb := quotGt_eq (n := n) E b hwb
  have hTq := quotGt_eq (n := n) E q hwq
  have hb1' : quotElt E b ≠ 1 := by
    intro h1
    apply hb1
    rw [hTb, h1, tab_one_toArray]
  have hbp' : quotElt E b ^ p = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hTb]
    exact hbp
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (quotElt E b) = p := orderOf_eq_prime hbp' hb1'
  refine ⟨quotElt E b, quotElt_mem_closure E b hwb, hord, quotElt E q, ?_, ?_⟩
  · apply hcore
    rw [← hTq]
    exact hq
  · intro heq
    apply hne
    rw [hTq, hTb, ← tabArr_mul, ← tabArr_mul, heq]

end CFSG.QuasithinUnique.Vol2Native.L239

namespace CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem goodLocal_of_lit {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1)
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {wg : List ℕ} (hw : ∀ l ∈ wg, l < 2) {Ω : OmegaData Lab}
    (hΩ : OmegaSpec C.A.act (C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg]).toArray C.Δ Ω)
    (hZ : C.litGrp wg = C.Y j) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hcard : Ω.lbl.size = 3 * p) {b q₁ q₂ b' q' : QuotGen}
    (h3 : Wit3Ok n C.A.act (C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg]) Ω.lbl.toList b q₁ q₂)
    (hP : WitPOk n C.A.act (C.D.sTabs ++ [wordTabA #[C.ta, C.tb] n wg]) Ω.lbl.toList p b' q') :
    GoodLocal (C.Y j) := by
  have hsub := C.Λ_sub hw hΩ hj hZ
  have hcard' : Nat.card (C.litGrp wg) = 2 ^ C.k * 3 * p := by
    rw [C.litGrp_card hw hΩ, hcard]
    ring
  have hcore : ∀ z : Γ, (∀ x ∈ Ω.lbl.toList, C.A.act (tab n z).toArray x = x) →
      z ∈ pCoreOf 2 (Subgroup.closure {y | y ∈ C.litEls wg}) := by
    intro z hz
    have : Subgroup.closure {y | y ∈ C.litEls wg} = C.Y j := hZ
    rw [this]
    exact C.mem_pCoreOf_of_fix hj hodd fun x hx => hz x (hsub x hx)
  rw [← C.litEls_tabs wg hw] at h3 hP
  rw [← hZ]
  exact goodLocal_of_witnesses (C.litGrp wg) hp h5 hcard'
    (wit3_sound_of (C.litEls wg) hcore hB hbase h3)
    (witP_sound_of (C.litEls wg) hcore hB hbase hp hP)

end CFSG.QuasithinUnique.Ch1.SporLat.LatCtx
