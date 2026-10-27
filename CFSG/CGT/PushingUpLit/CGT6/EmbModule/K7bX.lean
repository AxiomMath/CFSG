module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeRep
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeCrit
public import CFSG.LieType.Ree.ExceptionalAutomorphismData
public import Certificates.Certificate271038

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
  Certificates.G2ThreeMax CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

section Abstract

variable {E : Type} [Group E]

@[expose] def ev3 (s : Fin 3 → E) (x : Fin 3 → ZMod 2) : E :=
  s 0 ^ (x 0).val * s 1 ^ (x 1).val * s 2 ^ (x 2).val

theorem pow_val_add (a : E) (ha : a * a = 1) (p q : ZMod 2) :
    a ^ (p + q).val = a ^ p.val * a ^ q.val := by
  have h2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  rw [ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]

theorem ev3_add (s : Fin 3 → E) (hsq : ∀ i, s i * s i = 1) (hcomm : ∀ i j, s i * s j = s j * s i)
    (x y : Fin 3 → ZMod 2) : ev3 s (x + y) = ev3 s x * ev3 s y := by
  simp only [ev3, Pi.add_apply]
  rw [pow_val_add _ (hsq 0), pow_val_add _ (hsq 1), pow_val_add _ (hsq 2)]
  have c : ∀ (i j : Fin 3) (m n : ℕ), Commute (s i ^ m) (s j ^ n) := fun i j m n =>
    Commute.pow_pow (show Commute (s i) (s j) from hcomm i j) m n
  calc s 0 ^ (x 0).val * s 0 ^ (y 0).val * (s 1 ^ (x 1).val * s 1 ^ (y 1).val) *
        (s 2 ^ (x 2).val * s 2 ^ (y 2).val)
      = s 0 ^ (x 0).val * s 1 ^ (x 1).val * (s 0 ^ (y 0).val * s 1 ^ (y 1).val) *
        (s 2 ^ (x 2).val * s 2 ^ (y 2).val) := by
        rw [Commute.mul_mul_mul_comm (c 0 1 _ _)]
    _ = _ := by
        rw [Commute.mul_mul_mul_comm ((c 0 2 _ _).mul_left (c 1 2 _ _))]

theorem ev3_zero (s : Fin 3 → E) : ev3 s 0 = 1 := by simp [ev3]

theorem card_closure_three (s : Fin 3 → E) (hsq : ∀ i, s i * s i = 1)
    (hcomm : ∀ i j, s i * s j = s j * s i) (hne : ∀ x : Fin 3 → ZMod 2, x ≠ 0 → ev3 s x ≠ 1) :
    Nat.card (Subgroup.closure (Set.range s)) = 8 := by
  let f : Multiplicative (Fin 3 → ZMod 2) →* E :=
    { toFun := fun x => ev3 s x.toAdd
      map_one' := ev3_zero s
      map_mul' := fun x y => ev3_add s hsq hcomm x.toAdd y.toAdd }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    exact hne x.toAdd (fun h => hx1 (by simpa using h)) hx
  have hmem : ∀ i, s i ∈ Subgroup.closure (Set.range s) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have hrange : f.range = Subgroup.closure (Set.range s) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hmem 0) _)
        (Subgroup.pow_mem _ (hmem 1) _)) (Subgroup.pow_mem _ (hmem 2) _)
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
      have h1 : (1 : ZMod 2).val = 1 := rfl
      fin_cases i <;> simp [f, ev3, h1]
  rw [← hrange]
  have : Nat.card f.range = Nat.card (Multiplicative (Fin 3 → ZMod 2)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [this]
  simp [Nat.card_eq_fintype_card]

end Abstract

section G3


@[expose] noncomputable def mt (x : G3) : Mat3 :=
  ((ρG x : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)

theorem mt_mul (x y : G3) : mt x * mt y = mt (x * y) := by
  unfold mt
  rw [map_mul, Units.val_mul]

theorem mt_one : mt (1 : G3) = M idArr := by
  rw [M_idArr]
  unfold mt
  rw [map_one, Units.val_one]

theorem mt_inj {x y : G3} (h : mt x = mt y) : x = y := ρG_injective (Units.ext h)

theorem mt_word : ∀ (w : List ℕ), (∀ k ∈ w, k < 8) → mt (wordElem gensG w) = M (wordArr w)
  | [], _ => by
    have h : wordElem gensG [] = 1 := by simp [wordElem]
    have h0 : wordArr [] = idArr := by simp only [wordArr, List.foldr_nil]
    rw [h, mt_one, h0]
  | k :: w, hw => by
    have hk : k < 8 := hw k (by simp)
    have h : wordElem gensG (k :: w) = gensG k * wordElem gensG w := by simp [wordElem]
    have hrec := mt_word w (fun x hx => hw x (by simp [hx]))
    have hg : mt (gensG k) = M (genArr k) := hρ_gens k hk
    have hc : wordArr (k :: w) = mmul (genArr k) (wordArr w) := by
      simp only [wordArr, List.foldr_cons]
    rw [h, ← mt_mul, hg, hrec, hc, M_mmul]

theorem mt_mul' {x y : G3} {a b : Array ℕ} (hx : mt x = M a) (hy : mt y = M b) :
    mt (x * y) = M (mmul a b) := by
  rw [← mt_mul, hx, hy, M_mmul]

theorem eq_of_beq3 {x y : G3} {a b : Array ℕ} (hx : mt x = M a) (hy : mt y = M b)
    (h : (a == b) = true) : x = y :=
  mt_inj (by rw [hx, hy, beq_iff_eq.1 h])

theorem ne_one_of_nz {x : G3} {a : Array ℕ} {p : ℕ} (hx : mt x = M a) (hp : p / 14 ≠ p % 14)
    (hpl : p < 196) (h : nzFlat a p = true) : x ≠ 1 := by
  intro hx1
  have h1 : M a = 1 := by rw [← hx, hx1, mt_one, M_idArr]
  have hr : p / 14 < 14 := by omega
  have hc : p % 14 < 14 := by omega
  have h2 := congrFun (congrFun h1 ⟨p / 14, hr⟩) ⟨p % 14, hc⟩
  rw [Matrix.one_apply_ne (fun e => hp (congrArg Fin.val e))] at h2
  simp only [M, Matrix.of_apply] at h2
  have h3 : 14 * (p / 14) + p % 14 = p := Nat.div_add_mod p 14
  rw [h3] at h2
  have h4 : 3 ∣ a[p]! := (ZMod.natCast_eq_zero_iff _ _).1 h2
  simp only [nzFlat, bne_iff_ne, ne_eq] at h
  exact h (Nat.mod_eq_zero_of_dvd h4)

theorem pow_exponent' (i : Fin Tag.G2.rank) (c : ZMod 3) : c ^ ReeTag.G2.exponent i = c := by
  rcases fin_rank_cases i with rfl | rfl <;> revert c <;> decide

section Phi

variable
  [CharP (ZMod 3) ReeTag.G2.prime]

@[expose] noncomputable def phiG : MulAut G3 := ReeTag.G2.finiteReeAut (ZMod 3) 0

theorem phiG_eq : phiG = ReeTag.G2.finiteExceptionalAut (ZMod 3) := by
  have h : ReeTag.G2.finiteReeAut (ZMod 3) 0 = ReeTag.G2.finiteExceptionalAut (ZMod 3) := by
    simp [ReeTag.finiteReeAut]
  exact h

theorem phi_xElement (i : Fin Tag.G2.rank) (c : ZMod 3) :
    phiG (xElement i c) = xElement (ReeTag.G2.perm i) (c ^ ReeTag.G2.exponent i) := by
  rw [phiG_eq]
  exact ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := ZMod 3) i c

theorem phi_yElement (i : Fin Tag.G2.rank) (c : ZMod 3) :
    phiG (yElement i c) = yElement (ReeTag.G2.perm i) (c ^ ReeTag.G2.exponent i) := by
  rw [phiG_eq]
  exact ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := ZMod 3) i c

theorem phi_gens : ∀ k < 8,
    phiG (gensG k) = gensG Certificates.G2ThreeMax.outerInput.sigma[k]! := by
  intro k hk
  interval_cases k
  · exact (phi_xElement i0 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_xElement i0 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_xElement i1 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_xElement i1 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_yElement i0 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_yElement i0 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_yElement i1 _).trans (by rw [pow_exponent']; rfl)
  · exact (phi_yElement i1 _).trans (by rw [pow_exponent']; rfl)

theorem phi_word : ∀ (w : List ℕ), (∀ k ∈ w, k < 8) →
    phiG (wordElem gensG w) = wordElem gensG (swapK7b w)
  | [], _ => by
    simp only [wordElem, swapK7b, List.map_nil, List.prod_nil]
    exact map_one _
  | k :: w, hw => by
    have hk : k < 8 := hw k (by simp)
    have hrec := phi_word w (fun x hx => hw x (by simp [hx]))
    simp only [wordElem, swapK7b, List.map_cons, List.prod_cons] at hrec ⊢
    rw [map_mul, hrec, phi_gens k hk]

end Phi

@[expose] noncomputable def kU (i : Fin 3) : G3 := wordElem gensG (k7bU i)

@[expose] noncomputable def kS (i : Fin 3) : G3 := wordElem gensG (k7bS i)

@[expose] noncomputable def kG0 : G3 := wordElem gensG k7bG0

@[expose] noncomputable def kG0i : G3 := wordElem gensG (invK7b k7bG0)

@[expose] noncomputable def kCe (i : Fin 3) : G3 := kG0 * (kU i * kG0i)

@[expose] noncomputable def kHg (n : ℕ) : G3 :=
  if n < 3 then kU ⟨n % 3, Nat.mod_lt _ (by decide)⟩ else kCe ⟨n % 3, Nat.mod_lt _ (by decide)⟩

theorem lt8_U : ∀ i : Fin 3, ∀ k ∈ k7bU i, k < 8 := by decide

theorem lt8_S : ∀ i : Fin 3, ∀ k ∈ k7bS i, k < 8 := by decide

theorem lt8_G0 : ∀ k ∈ k7bG0, k < 8 := by decide

theorem lt8_swap {w : List ℕ} (hw : ∀ k ∈ w, k < 8) : ∀ k ∈ swapK7b w, k < 8 := by
  intro k hk
  simp only [swapK7b, List.mem_map] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have := hw j hj
  interval_cases j <;> decide

theorem lt8_inv {w : List ℕ} (hw : ∀ k ∈ w, k < 8) : ∀ k ∈ invK7b w, k < 8 := by
  intro k hk
  simp only [invK7b, List.mem_map, List.mem_reverse] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have := hw j hj
  simp only [invK]
  split_ifs <;> omega

theorem mt_kU (i : Fin 3) : mt (kU i) = M (wordArr (k7bU i)) := mt_word _ (lt8_U i)

theorem mt_kS (i : Fin 3) : mt (kS i) = M (wordArr (k7bS i)) := mt_word _ (lt8_S i)

theorem mt_kG0 : mt kG0 = M (wordArr k7bG0) := mt_word _ lt8_G0

theorem mt_kG0i : mt kG0i = M (wordArr (invK7b k7bG0)) := mt_word _ (lt8_inv lt8_G0)

theorem mt_kCe (i : Fin 3) : mt (kCe i) = M (kCArr i) :=
  mt_mul' mt_kG0 (mt_mul' (mt_kU i) mt_kG0i)

theorem mt_kHg (n : ℕ) : mt (kHg n) = M (kHgArr n) := by
  unfold kHg kHgArr
  split_ifs
  · exact mt_kU _
  · exact mt_kCe _

theorem mt_slp : ∀ idxs : List ℕ, mt ((idxs.map kHg).prod) = M (kSlpArr idxs)
  | [] => by
    have h : kSlpArr [] = idArr := by simp only [kSlpArr, List.foldr_nil]
    rw [h, List.map_nil, List.prod_nil, mt_one]
  | n :: idxs => by
    have h : kSlpArr (n :: idxs) = mmul (kHgArr n) (kSlpArr idxs) := by
      simp only [kSlpArr, List.foldr_cons]
    rw [h, List.map_cons, List.prod_cons]
    exact mt_mul' (mt_kHg n) (mt_slp idxs)

section Final

variable
  [CharP (ZMod 3) ReeTag.G2.prime]

theorem g23_pinned :
    ∃ (u : Fin 3 → G3) (s : Fin 3 → G3) (g₀ : G3),
      (∀ i, (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3) (u i) = u i ∧ u i * u i = 1 ∧
        u i ≠ 1) ∧
      (∀ i, (ReeTag.G2.finiteReeAut (ZMod 3) 0 : MulAut G3) (s i) = s i ∧ s i * s i = 1) ∧
      (∀ i j, s i * s j = s j * s i) ∧
      Nat.card (Subgroup.closure (Set.range s)) = 8 ∧
      (∀ i, g₀ * s i * g₀⁻¹ ∈ Subgroup.closure (Set.range s)) ∧
      Subgroup.closure (Set.range u ∪ Set.range fun i => g₀ * u i * g₀⁻¹) = ⊤ := by
  have h := Certificates.certificate271038
  simp only [k7bCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hGG, hu0, hu1, hu2, hs0, hs1, hs2, hfu0, hfu1, hfu2, hfs0, hfs1, hfs2, hnu0, hnu1,
    hnu2, hc01, hc02, hc12, hn1, hn2, hn3, hn12, hn13, hn23, hn123, hg0, hg1, hg2, hr0, hr1, hr2,
    hr3⟩ := h
  have hone : mt (1 : G3) = M idArr := mt_one
  have symm' : ∀ {a b : Array ℕ}, (a == b) = true → (b == a) = true := by
    intro a b h
    rw [beq_iff_eq] at h ⊢
    exact h.symm
  have sqU : ∀ i : Fin 3, kU i * kU i = 1 := by
    have h0 : kU 0 * kU 0 = 1 := eq_of_beq3 (mt_mul' (mt_kU 0) (mt_kU 0)) hone hu0
    have h1 : kU 1 * kU 1 = 1 := eq_of_beq3 (mt_mul' (mt_kU 1) (mt_kU 1)) hone hu1
    have h2 : kU 2 * kU 2 = 1 := eq_of_beq3 (mt_mul' (mt_kU 2) (mt_kU 2)) hone hu2
    intro i
    fin_cases i
    exacts [h0, h1, h2]
  have sqS : ∀ i : Fin 3, kS i * kS i = 1 := by
    have h0 : kS 0 * kS 0 = 1 := eq_of_beq3 (mt_mul' (mt_kS 0) (mt_kS 0)) hone hs0
    have h1 : kS 1 * kS 1 = 1 := eq_of_beq3 (mt_mul' (mt_kS 1) (mt_kS 1)) hone hs1
    have h2 : kS 2 * kS 2 = 1 := eq_of_beq3 (mt_mul' (mt_kS 2) (mt_kS 2)) hone hs2
    intro i
    fin_cases i
    exacts [h0, h1, h2]
  have hcomm : ∀ i j : Fin 3, kS i * kS j = kS j * kS i := by
    have c01 : kS 0 * kS 1 = kS 1 * kS 0 :=
      eq_of_beq3 (mt_mul' (mt_kS 0) (mt_kS 1)) (mt_mul' (mt_kS 1) (mt_kS 0)) hc01
    have c02 : kS 0 * kS 2 = kS 2 * kS 0 :=
      eq_of_beq3 (mt_mul' (mt_kS 0) (mt_kS 2)) (mt_mul' (mt_kS 2) (mt_kS 0)) hc02
    have c12 : kS 1 * kS 2 = kS 2 * kS 1 :=
      eq_of_beq3 (mt_mul' (mt_kS 1) (mt_kS 2)) (mt_mul' (mt_kS 2) (mt_kS 1)) hc12
    intro i j
    fin_cases i <;> fin_cases j
    exacts [rfl, c01, c02, c01.symm, rfl, c12, c02.symm, c12.symm, rfl]
  have phikey : ∀ (w : List ℕ), (∀ k ∈ w, k < 8) → (wordArr w == wordArr (swapK7b w)) = true →
      phiG (wordElem gensG w) = wordElem gensG w := by
    intro w hw h
    rw [phi_word w hw]
    exact (eq_of_beq3 (mt_word w hw) (mt_word _ (lt8_swap hw)) h).symm
  have fixU : ∀ i : Fin 3, phiG (kU i) = kU i := by
    intro i
    fin_cases i
    exacts [phikey _ (lt8_U 0) hfu0, phikey _ (lt8_U 1) hfu1, phikey _ (lt8_U 2) hfu2]
  have fixS : ∀ i : Fin 3, phiG (kS i) = kS i := by
    intro i
    fin_cases i
    exacts [phikey _ (lt8_S 0) hfs0, phikey _ (lt8_S 1) hfs1, phikey _ (lt8_S 2) hfs2]
  have neU : ∀ i : Fin 3, kU i ≠ 1 := by
    intro i
    fin_cases i
    · exact ne_one_of_nz (mt_kU 0) (by decide) (by decide) hnu0
    · exact ne_one_of_nz (mt_kU 1) (by decide) (by decide) hnu1
    · exact ne_one_of_nz (mt_kU 2) (by decide) (by decide) hnu2
  have n1 : kS 0 ≠ 1 := ne_one_of_nz (mt_kS 0) (by decide) (by decide) hn1
  have n2 : kS 1 ≠ 1 := ne_one_of_nz (mt_kS 1) (by decide) (by decide) hn2
  have n3 : kS 2 ≠ 1 := ne_one_of_nz (mt_kS 2) (by decide) (by decide) hn3
  have n12 : kS 0 * kS 1 ≠ 1 :=
    ne_one_of_nz (mt_mul' (mt_kS 0) (mt_kS 1)) (by decide) (by decide) hn12
  have n13 : kS 0 * kS 2 ≠ 1 :=
    ne_one_of_nz (mt_mul' (mt_kS 0) (mt_kS 2)) (by decide) (by decide) hn13
  have n23 : kS 1 * kS 2 ≠ 1 :=
    ne_one_of_nz (mt_mul' (mt_kS 1) (mt_kS 2)) (by decide) (by decide) hn23
  have n123 : kS 0 * (kS 1 * kS 2) ≠ 1 :=
    ne_one_of_nz (mt_mul' (mt_kS 0) (mt_mul' (mt_kS 1) (mt_kS 2))) (by decide) (by decide) hn123
  have hne : ∀ x : Fin 3 → ZMod 2, x ≠ 0 → ev3 kS x ≠ 1 := by
    intro x hx
    have hcases : x = ![1, 0, 0] ∨ x = ![0, 1, 0] ∨ x = ![0, 0, 1] ∨ x = ![1, 1, 0] ∨
        x = ![1, 0, 1] ∨ x = ![0, 1, 1] ∨ x = ![1, 1, 1] := by
      revert x
      decide
    have h1 : (1 : ZMod 2).val = 1 := rfl
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [ev3, h1] using n1
    · simpa [ev3, h1] using n2
    · simpa [ev3, h1] using n3
    · simpa [ev3, h1] using n12
    · simpa [ev3, h1] using n13
    · simpa [ev3, h1] using n23
    · simpa [ev3, h1, mul_assoc] using n123
  have hcard : Nat.card (Subgroup.closure (Set.range kS)) = 8 := card_closure_three kS sqS hcomm hne
  have hGi : kG0 * kG0i = 1 := eq_of_beq3 (mt_mul' mt_kG0 mt_kG0i) hone hGG
  have hGinv : kG0i = kG0⁻¹ := eq_inv_of_mul_eq_one_right hGi
  have mem8 : ∀ (x : G3) (X : Array ℕ), mt x = M X → (kE8Arr.any fun e => e == X) = true →
      x ∈ Subgroup.closure (Set.range kS) := by
    intro x X hx hany
    rw [List.any_eq_true] at hany
    obtain ⟨e, he, hb⟩ := hany
    have hmem : ∀ i, kS i ∈ Subgroup.closure (Set.range kS) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    simp only [kE8Arr, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [eq_of_beq3 hx hone (symm' hb)]
      exact Subgroup.one_mem _
    · rw [eq_of_beq3 hx (mt_kS 0) (symm' hb)]
      exact hmem 0
    · rw [eq_of_beq3 hx (mt_kS 1) (symm' hb)]
      exact hmem 1
    · rw [eq_of_beq3 hx (mt_kS 2) (symm' hb)]
      exact hmem 2
    · rw [eq_of_beq3 hx (mt_mul' (mt_kS 0) (mt_kS 1)) (symm' hb)]
      exact Subgroup.mul_mem _ (hmem 0) (hmem 1)
    · rw [eq_of_beq3 hx (mt_mul' (mt_kS 0) (mt_kS 2)) (symm' hb)]
      exact Subgroup.mul_mem _ (hmem 0) (hmem 2)
    · rw [eq_of_beq3 hx (mt_mul' (mt_kS 1) (mt_kS 2)) (symm' hb)]
      exact Subgroup.mul_mem _ (hmem 1) (hmem 2)
    · rw [eq_of_beq3 hx (mt_mul' (mt_kS 0) (mt_mul' (mt_kS 1) (mt_kS 2))) (symm' hb)]
      exact Subgroup.mul_mem _ (hmem 0) (Subgroup.mul_mem _ (hmem 1) (hmem 2))
  have hnorm : ∀ i : Fin 3, kG0 * kS i * kG0⁻¹ ∈ Subgroup.closure (Set.range kS) := by
    have key : ∀ i : Fin 3, (kE8Arr.any fun e =>
        e == mmul (wordArr k7bG0) (mmul (wordArr (k7bS i)) (wordArr (invK7b k7bG0)))) = true →
        kG0 * kS i * kG0⁻¹ ∈ Subgroup.closure (Set.range kS) := by
      intro i hany
      have h : kG0 * kS i * kG0⁻¹ = kG0 * (kS i * kG0i) := by rw [hGinv, mul_assoc]
      rw [h]
      exact mem8 _ _ (mt_mul' mt_kG0 (mt_mul' (mt_kS i) mt_kG0i)) hany
    intro i
    fin_cases i
    exacts [key 0 hg0, key 1 hg1, key 2 hg2]
  have hconj : ∀ i : Fin 3, kCe i = kG0 * kU i * kG0⁻¹ := by
    intro i
    rw [kCe, hGinv, mul_assoc]
  have hHg : ∀ n < 6, kHg n ∈ Subgroup.closure (Set.range kU ∪
      Set.range fun i => kG0 * kU i * kG0⁻¹) := by
    intro n _
    unfold kHg
    split_ifs
    · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [hconj]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  have hslp : ∀ j : Fin 4, ∀ n ∈ k7bSlp j, n < 6 := by decide
  have hroot : ∀ j : Fin 4, (kSlpArr (k7bSlp j) == genArr (k7bRootLetter j)) = true →
      gensG (k7bRootLetter j) ∈ Subgroup.closure (Set.range kU ∪
        Set.range fun i => kG0 * kU i * kG0⁻¹) := by
    intro j hj
    have hk : k7bRootLetter j < 8 := by fin_cases j <;> decide
    have heq : ((k7bSlp j).map kHg).prod = gensG (k7bRootLetter j) :=
      eq_of_beq3 (mt_slp _) (hρ_gens _ hk) hj
    rw [← heq]
    refine Subgroup.list_prod_mem _ (fun x hx => ?_)
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    exact hHg n (hslp j n hn)
  have hgen : Subgroup.closure (Set.range kU ∪ Set.range fun i => kG0 * kU i * kG0⁻¹) = ⊤ := by
    have h0 := hroot 0 hr0
    have h1 := hroot 1 hr1
    have h2 := hroot 2 hr2
    have h3 := hroot 3 hr3
    simp only [k7bRootLetter] at h0 h1 h2 h3
    have hinv : ∀ k < 8, k % 2 = 0 → gensG (k + 1) = (gensG k)⁻¹ := by
      intro k hk h2k
      have := hinv_gens k hk
      simpa [invK, h2k] using this
    rw [eq_top_iff, ← closure_gensG, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk8 : k < 8 := hk
    interval_cases k
    · exact h0
    · have := hinv 0 (by norm_num) (by norm_num)
      rw [this]
      exact Subgroup.inv_mem _ h0
    · exact h1
    · have := hinv 2 (by norm_num) (by norm_num)
      rw [this]
      exact Subgroup.inv_mem _ h1
    · exact h2
    · have := hinv 4 (by norm_num) (by norm_num)
      rw [this]
      exact Subgroup.inv_mem _ h2
    · exact h3
    · have := hinv 6 (by norm_num) (by norm_num)
      rw [this]
      exact Subgroup.inv_mem _ h3
  exact ⟨kU, kS, kG0, fun i => ⟨fixU i, sqU i, neU i⟩, fun i => ⟨fixS i, sqS i⟩, hcomm, hcard,
    hnorm, hgen⟩

end Final

end G3

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
