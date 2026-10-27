module

public import Certificates.Data.Kernel.SmithL6KR
public import CFSG.Certificates.Kernel.SmithL6KOSound
public import CFSG.Certificates.Kernel.SmithL6KWSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols)

theorem form_comm (a b : Nat) : form a b = form b a := by
  unfold form
  rw [Nat.and_comm]

theorem eq_of_form {a b : Nat} (ha : a < 64) (hb : b < 64) (h : ∀ x, form a x = form b x) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have e := h (2 ^ i)
    rwa [form_comm a, form_comm b, form_two_pow hi, form_two_pow hi] at e
  · have h64 : 64 ≤ 2 ^ i := by
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem conjP_comp {p q r : Nat × Nat} (hp : TvP p) (hq : TvP q) (hr : TvP r) :
    conjP p (conjP q r) = conjP (conjP p q) (conjP p r) := by
  have h1 := conjP_tvP hp (conjP_tvP hq hr)
  have h2 := conjP_tvP (conjP_tvP hp hq) (conjP_tvP hp hr)
  refine Prod.ext ?_ (eq_of_form h1.2.1 h2.2.1 fun x => ?_)
  · change tvA p (tvA q r.1) = tvA (conjP p q) (tvA p r.1)
    rw [tvA_conjP hp, tvA_tvA hp]
  · simp only [form_conjP_snd, tvA_conjP hp, tvA_tvA hp]

theorem tvImg_comp {j a x : Nat} (hj : j < 1953) (ha : a < 1953) (hx : x < 1953) :
    tvImg j (tvImg a x) = tvImg (tvImg j a) (tvImg j x) := by
  rw [tvImg_eq j (tvImg a x), tvImg_eq (tvImg j a) (tvImg j x), tvPair_tvImg ha hx,
    tvPair_tvImg hj ha, tvPair_tvImg hj hx,
    conjP_comp (tvP_tvPair hj) (tvP_tvPair ha) (tvP_tvPair hx)]

theorem tvPair_inj {a b : Nat} (ha : a < 1953) (hb : b < 1953) (h : tvPair a = tvPair b) :
    a = b := by
  rw [← tvIdxTab_code ha, ← tvIdxTab_code hb, h]

@[expose] def LiftF (f : Nat → Nat) : Prop :=
  (∀ x < 1953, f x < 1953) ∧ (∀ x < 1953, f (f x) = x) ∧
    ∀ p < 1953, ∀ x < 1953, f (tvImg p x) = tvImg (f p) (f x)

theorem liftF_id : LiftF id :=
  ⟨fun _ hx => hx, fun _ _ => rfl, fun _ _ _ _ => by rw [id_eq, id_eq, id_eq]⟩

theorem liftF_tvImg {q : Nat} (hq : q < 1953) : LiftF (tvImg q) :=
  ⟨fun _ hx => tvImg_lt hq hx, fun _ hx => tvImg_tvImg hq hx,
    fun _ hp _ hx => tvImg_comp hq hp hx⟩

theorem liftF_comp {f g : Nat → Nat} (hf : LiftF f) (hg : LiftF g)
    (hc : ∀ x < 1953, f (g x) = g (f x)) : LiftF (fun x => f (g x)) := by
  obtain ⟨f1, f2, f3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := hg
  refine ⟨fun x hx => f1 _ (g1 x hx), fun x hx => ?_, fun p hp x hx => ?_⟩
  · simp only
    rw [← hc _ (g1 x hx), g2 x hx, f2 x hx]
  · simp only
    rw [g3 p hp x hx, f3 _ (g1 p hp) _ (g1 x hx)]

@[expose] def swP (p : Nat × Nat) : Nat × Nat := (trSw p.2, trSw p.1)

theorem sw_table : ((List.range 64).all fun a => (List.range 64).all fun b =>
    decide (trSw a < 64) && trSw (trSw a) == a && trSw (a ^^^ b) == (trSw a ^^^ trSw b) &&
      form (trSw a) (trSw b) == form a b) = true := by
  decide +kernel

theorem sw_facts : ∀ a < 64, ∀ b < 64, trSw a < 64 ∧ trSw (trSw a) = a ∧
    trSw (a ^^^ b) = trSw a ^^^ trSw b ∧ form (trSw a) (trSw b) = form a b := by
  intro a ha b hb
  have h := List.all_eq_true.1 (List.all_eq_true.1 sw_table a (List.mem_range.2 ha)) b
    (List.mem_range.2 hb)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem swP_tvP {p : Nat × Nat} (hp : TvP p) : TvP (swP p) := by
  obtain ⟨v, φ⟩ := p
  obtain ⟨hv, hφ, hv0, hφ0, hφv⟩ := hp
  simp only at hv hφ hv0 hφ0 hφv
  have ne : ∀ x < 64, x ≠ 0 → trSw x ≠ 0 := fun x hx h0 e => by
    have h2 := (sw_facts x hx 0 (by decide)).2.1
    rw [e] at h2
    exact h0 (h2.symm.trans (by decide))
  refine ⟨(sw_facts φ hφ 0 (by decide)).1, (sw_facts v hv 0 (by decide)).1, ne φ hφ hφ0,
    ne v hv hv0, ?_⟩
  change form (trSw v) (trSw φ) = false
  rw [(sw_facts v hv φ hφ).2.2.2, form_comm, hφv]

theorem swP_swP {p : Nat × Nat} (hp : TvP p) : swP (swP p) = p := by
  obtain ⟨v, φ⟩ := p
  unfold swP
  simp only
  rw [(sw_facts v hp.1 0 (by decide)).2.1, (sw_facts φ hp.2.1 0 (by decide)).2.1]

theorem swP_conjP {p q : Nat × Nat} (hp : TvP p) (hq : TvP q) :
    swP (conjP p q) = conjP (swP p) (swP q) := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  obtain ⟨hw, hψ, -, -, -⟩ := hp
  obtain ⟨hv, hφ, -, -, -⟩ := hq
  simp only at hw hψ hv hφ
  have f1 : form (trSw w) (trSw φ) = form φ w := by rw [(sw_facts w hw φ hφ).2.2.2, form_comm]
  have f2 : form (trSw v) (trSw ψ) = form ψ v := by rw [(sw_facts v hv ψ hψ).2.2.2, form_comm]
  unfold swP conjP
  simp only [f1, f2]
  cases form φ w <;> cases form ψ v <;>
    simp [(sw_facts φ hφ ψ hψ).2.2.1, (sw_facts v hv w hw).2.2.1]

theorem trTauT_get {k : Nat} (hk : k < 1953) :
    trTauT[k]! = tvIdxTab[codeOf (swP (tvPair k))]! := by
  unfold trTauT codeOf swP
  exact ofFn_get! (fun k : Fin 1953 =>
    tvIdxTab[64 * trSw (tvPair k.val).2 + trSw (tvPair k.val).1]!) hk

theorem trTauT_spec {k : Nat} (hk : k < 1953) :
    trTauT[k]! < 1953 ∧ tvPair trTauT[k]! = swP (tvPair k) := by
  obtain ⟨k', hk', he⟩ := tvPair_surj (swP_tvP (tvP_tvPair hk))
  rw [trTauT_get hk, ← he, tvIdxTab_code hk']
  exact ⟨hk', rfl⟩

theorem liftF_tau : LiftF fun k => trTauT[k]! := by
  refine ⟨fun x hx => (trTauT_spec hx).1, fun x hx => ?_, fun p hp x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := trTauT_spec hx
    obtain ⟨h3, h4⟩ := trTauT_spec h1
    refine tvPair_inj h3 hx ?_
    rw [h4, h2, swP_swP (tvP_tvPair hx)]
  · obtain ⟨hp1, hp2⟩ := trTauT_spec hp
    obtain ⟨hx1, hx2⟩ := trTauT_spec hx
    have hi := tvImg_lt hp hx
    obtain ⟨hi1, hi2⟩ := trTauT_spec hi
    refine tvPair_inj hi1 (tvImg_lt hp1 hx1) ?_
    simp only
    rw [hi2, tvPair_tvImg hp hx, tvPair_tvImg hp1 hx1, hp2, hx2,
      swP_conjP (tvP_tvPair hp) (tvP_tvPair hx)]

theorem tauP_eq {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
    (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!) {k : Nat} (hk : k < 1953) :
    tauP C I k = trTauT[k]! := by
  have hp := tvP_tvPair hk
  unfold tauP
  rw [hC k hk, codeOf_div hp, codeOf_mod hp, trTauT_get hk, ← hI _ (codeOf_lt (swP_tvP hp))]
  rfl

theorem lift_facts {s : Array Nat} {f : Nat → Nat} (hs : ∀ x < 1953, s[x]! = f x) (hf : LiftF f) :
    (∀ x < 1953, s[x]! < 1953 ∧ s[s[x]!]! = x) ∧
    (∀ p < 1953, ∀ x < 1953, s[(tvTab[p]!)[x]!]! = (tvTab[s[p]!]!)[s[x]!]!) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨fun x hx => ?_, fun p hp x hx => ?_⟩
  · rw [hs x hx, hs _ (h1 x hx)]
    exact ⟨h1 x hx, h2 x hx⟩
  · rw [tvTab_get hp hx, hs _ (tvImg_lt hp hx), hs p hp, hs x hx,
      tvTab_get (h1 p hp) (h1 x hx), h3 p hp x hx]

theorem mem_planePts0 {P : List Nat} (hP : planePts 0 = P.toArray) {x : Nat} (hx : x ∈ P) :
    x < 1953 ∧ inPlane 0 x = true := by
  have hx' : x ∈ planePts 0 := by
    rw [hP]
    exact List.mem_toArray.2 hx
  unfold planePts at hx'
  rw [List.mem_toArray, List.mem_filter, List.mem_range] at hx'
  exact hx'

theorem lift_W0 {s : Array Nat} {f : Nat → Nat} {P : List Nat} (hP : planePts 0 = P.toArray)
    (hs : ∀ x < 1953, s[x]! = f x) (h : fixW0K P f = true) :
    ∀ p ∈ planePtsArr[0]!, (flagArr[0]!)[s[p]!]! = true := by
  intro p hp
  rw [planePtsArr_get (by decide), hP, List.mem_toArray] at hp
  have hq := (List.all_eq_true.1 h) p hp
  rw [List.contains_iff_mem] at hq
  obtain ⟨hq1, hq2⟩ := mem_planePts0 hP hq
  rw [hs p (mem_planePts0 hP hp).1, flagArr_get (by decide) hq1]
  exact hq2

theorem trColsT_eq {s : Array Nat} {f : Nat → Nat} {P : List Nat} (hP : planePts 0 = P.toArray)
    (hs : ∀ j < 9, s[ugens[j]!]! = f ugens[j]!) : trColsT s = (colsF P f).toArray := by
  apply Array.ext
  · simp [trColsT, colsF]
  · intro j h1 _
    have hj : j < 9 := by simpa [trColsT] using h1
    simp only [trColsT, colsF, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      List.getElem_range]
    rw [pos0_eq hP, hs j hj]

theorem colsF_congr {P : List Nat} {f g : Nat → Nat} (h : ∀ j < 9, f ugens[j]! = g ugens[j]!) :
    colsF P f = colsF P g := by
  unfold colsF
  exact List.map_congr_left fun j hj => by rw [h j (List.mem_range.1 hj)]

theorem collMul_toArray (A B : List Nat) (hB : B.length = 9) :
    collMul A.toArray B.toArray = (B.map (apK A)).toArray := by
  apply Array.ext
  · simp [collMul, hB]
  · intro m h1 _
    have hm : m < 9 := by simpa [collMul] using h1
    simp only [collMul, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
    change applyCols A.toArray B.toArray[m]! = apK A B[m]
    rw [getElem!_pos B.toArray m (by simp [hB, hm]), List.getElem_toArray, applyCols_toArray]

theorem trConjC_toArray (g M : List Nat) (hg : g.length = 9) (hM : M.length = 9) :
    trConjC g.toArray M.toArray = (conjK g M).toArray := by
  unfold trConjC conjK
  rw [collMul_toArray g M hM, collMul_toArray _ g hg]

theorem toArray_beq (a b : List Nat) : (a.toArray == b.toArray) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · have h' : a.toArray ≠ b.toArray := fun e => h (List.toArray_inj e)
    simp [h, h']

end CFSG.SmithL6.K
