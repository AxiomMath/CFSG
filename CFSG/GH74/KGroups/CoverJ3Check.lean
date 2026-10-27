module

public import CFSG.GH74.Filter.Sporadic.Spec

public section

namespace CFSG.GH74.KGroups.J3

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

section Check

variable {M V : Type} (O : Ops M V)

@[expose] def letterMat (A B : M) (z : ℤ) : M :=
  if z = 1 ∨ z = -1 then A else if z = 2 then B else if z = -2 then O.mul B B else O.one

@[expose] def wordMat (A B : M) (w : List ℤ) : M := (w.map (letterMat O A B)).foldr O.mul O.one

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def prodBase2 : List M → ℕ → M
  | [], _ => O.one
  | X :: xs, n => if n % 2 = 1 then O.mul X (prodBase2 xs (n / 2)) else prodBase2 xs (n / 2)

@[expose] def xOf (A B : M) (ws : List (List ℤ)) (i : ℕ) : M :=
  O.mul (O.mul (wordMat O A B (ws.getD (2 ^ i - 1) [])) A)
    (wordMat O A B (invWord (ws.getD (2 ^ i - 1) [])))

@[expose] def xsOf (A B : M) (ws : List (List ℤ)) : List M :=
  [xOf O A B ws 0, xOf O A B ws 1, xOf O A B ws 2, xOf O A B ws 3]

@[expose] def conjCheckAux (A B : M) (ws : List (List ℤ)) (tests : List ℕ) : Bool :=
  O.eq (O.mul A A) O.one && O.eq (O.mul B (O.mul B B)) O.one && decide (ws.length = 15) &&
    (List.range 15).all (fun k =>
      O.eq (O.mul (wordMat O A B (ws.getD k [])) (wordMat O A B (invWord (ws.getD k [])))) O.one &&
      O.eq (O.mul (wordMat O A B (invWord (ws.getD k []))) (wordMat O A B (ws.getD k []))) O.one &&
      O.eq (O.mul (wordMat O A B (ws.getD k [])) (xOf O A B ws 0))
        (O.mul (prodBase2 O (xsOf O A B ws) (k + 1)) (wordMat O A B (ws.getD k [])))) &&
    (xsOf O A B ws).all (fun X => O.eq (O.mul X X) O.one) && O.commsOK (xsOf O A B ws) &&
    O.kerModOK O.one (xsOf O A B ws) tests

@[expose] def conjCheck (seedA seedB : String) (ws : List (List ℤ)) (tests : List ℕ) : Bool :=
  conjCheckAux O (O.decode seedA) (O.decode seedB) ws tests

end Check

theorem map_prod_ofFn_pow {R G : Type*} [Monoid R] [Monoid G] (f : R →* G) {n : ℕ}
    (u : Fin n → R) (m : Fin n → G) (h : ∀ i, f (u i) = m i) (a : Fin n → Fin 2) :
    f (List.ofFn fun i => u i ^ (a i : ℕ)).prod = (List.ofFn fun i => m i ^ (a i : ℕ)).prod := by
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [Function.comp_apply, map_pow, h i]

section Spec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem letterMat_spec (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) {A B : M}
    (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S) (z : ℤ) :
    Sp.WF (letterMat O A B z) ∧ Sp.toMat (letterMat O A B z) ∈ S := by
  unfold letterMat
  split_ifs
  · exact hA
  · exact hB
  · exact ⟨Sp.mul_wf hB.1 hB.1, by rw [Sp.toMat_mul hB.1 hB.1]; exact S.mul_mem hB.2 hB.2⟩
  · exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact S.one_mem⟩

theorem wordMat_spec (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) {A B : M}
    (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S) :
    ∀ w : List ℤ, Sp.WF (wordMat O A B w) ∧ Sp.toMat (wordMat O A B w) ∈ S
  | [] => ⟨Sp.one_wf, by
      change Sp.toMat O.one ∈ S
      rw [Sp.toMat_one]
      exact S.one_mem⟩
  | z :: w => by
    obtain ⟨h1, h2⟩ := letterMat_spec Sp S hA hB z
    obtain ⟨h3, h4⟩ := wordMat_spec S hA hB w
    have e : wordMat O A B (z :: w) = O.mul (letterMat O A B z) (wordMat O A B w) := rfl
    rw [e]
    exact ⟨Sp.mul_wf h1 h3, by rw [Sp.toMat_mul h1 h3]; exact S.mul_mem h2 h4⟩

theorem prodBase2_spec : ∀ (xs : List M), (∀ X ∈ xs, Sp.WF X) → ∀ (a : Fin xs.length → Fin 2),
    Sp.WF (prodBase2 O xs (enc2 _ a)) ∧ Sp.toMat (prodBase2 O xs (enc2 _ a)) =
      (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod
  | [], _, a => ⟨Sp.one_wf, by simp [prodBase2, Sp.toMat_one]⟩
  | X :: xs, hxs, a => by
    have hX := hxs X List.mem_cons_self
    obtain ⟨hw, hf⟩ := prodBase2_spec xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY))
      (Fin.tail a)
    have h0 := (a 0).isLt
    have hd : (enc2 (xs.length + 1) a) % 2 = (a 0 : ℕ) := by rw [enc2]; omega
    have hq : (enc2 (xs.length + 1) a) / 2 = enc2 xs.length (Fin.tail a) := by rw [enc2]; omega
    have e : prodBase2 O (X :: xs) (enc2 (xs.length + 1) a) =
        if (enc2 (xs.length + 1) a) % 2 = 1 then
          O.mul X (prodBase2 O xs (enc2 (xs.length + 1) a / 2))
        else prodBase2 O xs (enc2 (xs.length + 1) a / 2) := rfl
    change Sp.WF (prodBase2 O (X :: xs) (enc2 (xs.length + 1) a)) ∧
      Sp.toMat (prodBase2 O (X :: xs) (enc2 (xs.length + 1) a)) = _
    rw [e, hd, hq, List.ofFn_succ, List.prod_cons]
    have ha0 : (a 0 : ℕ) = 0 ∨ (a 0 : ℕ) = 1 := by omega
    rcases ha0 with h | h
    · simp only [h, zero_ne_one, ↓reduceIte, pow_zero, one_mul]
      exact ⟨hw, hf⟩
    · simp only [h, ↓reduceIte, pow_one]
      exact ⟨Sp.mul_wf hX hw, by rw [Sp.toMat_mul hX hw, hf]; rfl⟩

theorem xOf_spec (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) {A B : M}
    (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S) (ws : List (List ℤ)) (i : ℕ) :
    Sp.WF (xOf O A B ws i) ∧ Sp.toMat (xOf O A B ws i) ∈ S := by
  obtain ⟨w1, m1⟩ := wordMat_spec Sp S hA hB (ws.getD (2 ^ i - 1) [])
  obtain ⟨w2, m2⟩ := wordMat_spec Sp S hA hB (invWord (ws.getD (2 ^ i - 1) []))
  have w3 := Sp.mul_wf w1 hA.1
  refine ⟨Sp.mul_wf w3 w2, ?_⟩
  unfold xOf
  rw [Sp.toMat_mul w3 w2, Sp.toMat_mul w1 hA.1]
  exact S.mul_mem (S.mul_mem m1 hA.2) m2

theorem exists_of_conjCheckAux (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) {A B : M}
    (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S)
    (ws : List (List ℤ)) (tests : List ℕ) (h : conjCheckAux O A B ws tests = true) :
    ∃ e : Fin 4 → Sˣ, (∀ i, e i * e i = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
      (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ a : Fin 4 → Fin 2, a ≠ 0 →
        ∃ g : Sˣ, g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod := by
  classical
  unfold conjCheckAux at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hAA, -⟩, -⟩, hconjs⟩, -⟩, hcomm⟩, hker⟩ := h
  have hlen4 : (xsOf O A B ws).length = 4 := rfl
  have hxsWF : ∀ X ∈ xsOf O A B ws, Sp.WF X := by
    intro X hX
    simp only [xsOf, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> exact (xOf_spec Sp S hA hB ws _).1
  have hAA' : Sp.toMat A * Sp.toMat A = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf hA.1 hA.1) Sp.one_wf hAA
    rwa [Sp.toMat_mul hA.1 hA.1, Sp.toMat_one] at this
  let Au : Sˣ := ⟨⟨Sp.toMat A, hA.2⟩, ⟨Sp.toMat A, hA.2⟩, Subtype.ext hAA', Subtype.ext hAA'⟩
  have hAu : Au * Au = 1 := Units.ext (Subtype.ext hAA')
  have hk : ∀ k : Fin 15, ∃ u : Sˣ,
      ((u : S) : Matrix (Fin d) (Fin d) (ZMod p)) =
        Sp.toMat (wordMat O A B (ws.getD k [])) ∧
      (((u⁻¹ : Sˣ) : S) : Matrix (Fin d) (Fin d) (ZMod p)) =
        Sp.toMat (wordMat O A B (invWord (ws.getD k []))) := by
    intro k
    obtain ⟨⟨h1, h2⟩, -⟩ := hconjs k k.isLt
    obtain ⟨wg, mg⟩ := wordMat_spec Sp S hA hB (ws.getD k [])
    obtain ⟨wh, mh⟩ := wordMat_spec Sp S hA hB (invWord (ws.getD k []))
    have e1 : Sp.toMat (wordMat O A B (ws.getD k [])) *
        Sp.toMat (wordMat O A B (invWord (ws.getD k []))) = 1 := by
      have := Sp.toMat_eq (Sp.mul_wf wg wh) Sp.one_wf h1
      rwa [Sp.toMat_mul wg wh, Sp.toMat_one] at this
    have e2 : Sp.toMat (wordMat O A B (invWord (ws.getD k []))) *
        Sp.toMat (wordMat O A B (ws.getD k [])) = 1 := by
      have := Sp.toMat_eq (Sp.mul_wf wh wg) Sp.one_wf h2
      rwa [Sp.toMat_mul wh wg, Sp.toMat_one] at this
    exact ⟨⟨⟨_, mg⟩, ⟨_, mh⟩, Subtype.ext e1, Subtype.ext e2⟩, rfl, rfl⟩
  choose gU hgU using hk
  let f : Sˣ →* Matrix (Fin d) (Fin d) (ZMod p) := S.subtype.comp (Units.coeHom S)
  have hfinj : ∀ a b : Sˣ, f a = f b → a = b := fun a b hab => Units.ext (Subtype.ext hab)
  have hfg : ∀ k : Fin 15, f (gU k) = Sp.toMat (wordMat O A B (ws.getD k [])) :=
    fun k => (hgU k).1
  have hfgi : ∀ k : Fin 15, f (gU k)⁻¹ = Sp.toMat (wordMat O A B (invWord (ws.getD k []))) :=
    fun k => (hgU k).2
  have hfA : f Au = Sp.toMat A := rfl
  let idx : Fin 4 → Fin 15 := ![0, 1, 3, 7]
  let e : Fin 4 → Sˣ := fun i => gU (idx i) * Au * (gU (idx i))⁻¹
  have hfe : ∀ i : Fin 4, f (e i) = Sp.toMat (xOf O A B ws i) := by
    intro i
    have hi : 2 ^ (i : ℕ) - 1 = (idx i : ℕ) := by fin_cases i <;> rfl
    obtain ⟨wg, -⟩ := wordMat_spec Sp S hA hB (ws.getD (2 ^ (i : ℕ) - 1) [])
    obtain ⟨wh, -⟩ := wordMat_spec Sp S hA hB (invWord (ws.getD (2 ^ (i : ℕ) - 1) []))
    unfold xOf
    rw [Sp.toMat_mul (Sp.mul_wf wg hA.1) wh, Sp.toMat_mul wg hA.1, hi]
    show f (gU (idx i) * Au * (gU (idx i))⁻¹) = _
    rw [map_mul, map_mul, hfg, hfgi, hfA]
  have hlt : ∀ i : Fin 4, (i : ℕ) < (xsOf O A B ws).length := fun i => by
    rw [hlen4]; exact i.isLt
  have hx : ∀ i : Fin 4, Sp.toMat ((xsOf O A B ws)[(i : ℕ)]'(hlt i)) = f (e i) := by
    intro i
    rw [hfe i]
    fin_cases i <;> rfl
  have hsq' : ∀ i, e i * e i = 1 := by
    intro i
    show gU (idx i) * Au * (gU (idx i))⁻¹ * (gU (idx i) * Au * (gU (idx i))⁻¹) = 1
    calc _ = gU (idx i) * (Au * Au) * (gU (idx i))⁻¹ := by group
      _ = 1 := by rw [hAu]; group
  have hpair := Sp.pairwise_of_commsOK hxsWF hcomm
  have hcomm' : ∀ i j, e i * e j = e j * e i := by
    intro i j
    apply hfinj
    rw [map_mul, map_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := List.pairwise_iff_getElem.1 hpair i j (hlt i) (hlt j) hij
      rw [hx i, hx j] at this
      exact this
    · rfl
    · have := List.pairwise_iff_getElem.1 hpair j i (hlt j) (hlt i) hij
      rw [hx i, hx j] at this
      exact this.symm
  have hlist : ∀ a : Fin 4 → Fin 2, f (List.ofFn fun i => e i ^ (a i : ℕ)).prod =
      (List.ofFn fun i : Fin (xsOf O A B ws).length =>
        Sp.toMat (xsOf O A B ws)[i] ^ (a i : ℕ)).prod := fun a =>
    map_prod_ofFn_pow f (fun i : Fin (xsOf O A B ws).length => e i)
      (fun i : Fin (xsOf O A B ws).length => Sp.toMat (xsOf O A B ws)[i])
      (fun i => (hx i).symm) a
  refine ⟨e, hsq', hcomm', ?_, ?_⟩
  · intro a ha h1
    have key := (Sp.ne_of_kerModOK Sp.one_wf hxsWF hker a ha).1
    apply key
    rw [← hlist a, h1, map_one]
  · intro a ha
    have hn0 : enc2 _ (a : Fin (xsOf O A B ws).length → Fin 2) ≠ 0 :=
      fun h0 => ha (eq_zero_of_enc2_eq_zero _ _ h0)
    have hnlt := enc2_lt _ (a : Fin (xsOf O A B ws).length → Fin 2)
    have hn16 : enc2 _ (a : Fin (xsOf O A B ws).length → Fin 2) < 16 := by
      simpa [hlen4] using hnlt
    let k : Fin 15 := ⟨enc2 _ (a : Fin (xsOf O A B ws).length → Fin 2) - 1, by omega⟩
    obtain ⟨-, h3⟩ := hconjs k k.isLt
    have hk1 : (k : ℕ) + 1 = enc2 _ (a : Fin (xsOf O A B ws).length → Fin 2) := by
      show enc2 _ (a : Fin (xsOf O A B ws).length → Fin 2) - 1 + 1 = _
      omega
    rw [hk1] at h3
    obtain ⟨wg, -⟩ := wordMat_spec Sp S hA hB (ws.getD k [])
    obtain ⟨wx, -⟩ := xOf_spec Sp S hA hB ws 0
    obtain ⟨wP, hP⟩ := prodBase2_spec Sp (xsOf O A B ws) hxsWF a
    have h4 := Sp.toMat_eq (Sp.mul_wf wg wx) (Sp.mul_wf wP wg) h3
    rw [Sp.toMat_mul wg wx, Sp.toMat_mul wP wg, hP] at h4
    refine ⟨gU k, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply hfinj
    rw [map_mul f (gU k) (e 0), map_mul f _ (gU k), hlist a, hfg k, hfe 0]
    exact h4

theorem exists_of_conjCheck (seedA seedB : String) (ws : List (List ℤ)) (tests : List ℕ)
    (h : conjCheck O seedA seedB ws tests = true) :
    ∃ e : Fin 4 → (NativeSporadic.seedMonoid p d 1 seedA seedB)ˣ,
      (∀ i, e i * e i = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
      (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ a : Fin 4 → Fin 2, a ≠ 0 →
        ∃ g : (NativeSporadic.seedMonoid p d 1 seedA seedB)ˣ,
          g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod :=
  exists_of_conjCheckAux Sp (NativeSporadic.seedMonoid p d 1 seedA seedB)
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
    ws tests h

end Spec

end CFSG.GH74.KGroups.J3
