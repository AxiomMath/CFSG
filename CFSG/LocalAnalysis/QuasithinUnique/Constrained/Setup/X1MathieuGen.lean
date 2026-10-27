module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Count

theorem card_distinct_nonid_pairs {S : Type} [Group S] [Finite S] (B : Subgroup S) :
    ∃ P : Finset (S × S), P.card = (Nat.card B - 1) * (Nat.card B - 2) ∧
      ∀ q ∈ P, q.1 ∈ B ∧ q.2 ∈ B ∧ q.1 ≠ 1 ∧ q.2 ≠ 1 ∧ q.1 ≠ q.2 := by
  classical
  set Bf : Finset S := (Set.toFinite (B : Set S)).toFinset with hBf
  have hBcard : Bf.card = Nat.card B := by
    rw [hBf, ← Set.ncard_eq_toFinset_card (B : Set S)]
    exact (Nat.card_coe_set_eq (B : Set S)).symm
  have h1 : (1 : S) ∈ Bf := by simp [hBf]
  set N1 : Finset S := Bf.erase 1 with hN1
  have hN1card : N1.card = Nat.card B - 1 := by
    rw [hN1, Finset.card_erase_of_mem h1, hBcard]
  refine ⟨(N1 ×ˢ N1).filter (fun q => q.1 ≠ q.2), ?_, ?_⟩
  · have hdiag : ((N1 ×ˢ N1).filter (fun q => ¬ (q.1 ≠ q.2))).card = N1.card := by
      have : (N1 ×ˢ N1).filter (fun q => ¬ (q.1 ≠ q.2)) = N1.image (fun x => (x, x)) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_product, not_not, Finset.mem_image]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨q.1, h1, Prod.ext rfl h3⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨hx, hx⟩, rfl⟩
      rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    have hsum := Finset.card_filter_add_card_filter_not (s := N1 ×ˢ N1) (fun q => q.1 ≠ q.2)
    rw [Finset.card_product, hdiag, hN1card] at hsum
    have hn : 1 ≤ Nat.card B := by rw [← hBcard]; exact Finset.card_pos.2 ⟨1, h1⟩
    have : (Nat.card B - 1) * (Nat.card B - 2) + (Nat.card B - 1) =
        (Nat.card B - 1) * (Nat.card B - 1) := by
      rcases Nat.lt_or_ge (Nat.card B) 2 with h | h
      · have : Nat.card B = 1 := by omega
        simp [this]
      · obtain ⟨k, hk⟩ : ∃ k, Nat.card B = k + 2 := ⟨Nat.card B - 2, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 from rfl]
        ring
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, hN1, Finset.mem_erase, hBf,
      Set.Finite.mem_toFinset, SetLike.mem_coe] at hq
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hq
    exact ⟨h2, h4, h1, h3, h5⟩

end Count

section Gen

variable {S : Type} [Group S] [Finite S] [DecidableEq S]

structure SylowData (S : Type) [Group S] (a m : ℕ) (Rl : List S) : Prop where
  length : Rl.length = 2 ^ a
  nodup : Rl.Nodup
  pow : ∀ x ∈ Rl, x ^ (2 ^ a) = 1
  card : Nat.card S = 2 ^ a * m
  odd : Odd m
  subgroup : ∃ R : Subgroup S, ∀ x, x ∈ R ↔ x ∈ Rl

theorem SylowData.of_mul_mem {S : Type} [Group S] [Finite S] {a m : ℕ} {Rl : List S}
    (hlen : Rl.length = 2 ^ a) (hnd : Rl.Nodup) (h1 : (1 : S) ∈ Rl)
    (hmul : ∀ x ∈ Rl, ∀ y ∈ Rl, x * y ∈ Rl) (hpow : ∀ x ∈ Rl, x ^ (2 ^ a) = 1)
    (hcard : Nat.card S = 2 ^ a * m) (hodd : Odd m) : SylowData S a m Rl :=
  ⟨hlen, hnd, hpow, hcard, hodd, exists_subgroup_of_list Rl h1 hmul⟩

theorem SylowData.of_gens {S : Type} [Group S] [Finite S] {a m : ℕ} {Rl : List S}
    (rg : List S) (hlen : Rl.length = 2 ^ a) (hnd : Rl.Nodup) (h1 : (1 : S) ∈ Rl)
    (hgen : ∀ x ∈ Rl, ∀ g ∈ rg, x * g ∈ Rl)
    (hRl : ∀ x ∈ Rl, x ∈ Subgroup.closure {g | g ∈ rg}) (hpow : ∀ x ∈ Rl, x ^ (2 ^ a) = 1)
    (hcard : Nat.card S = 2 ^ a * m) (hodd : Odd m) : SylowData S a m Rl :=
  ⟨hlen, hnd, hpow, hcard, hodd, exists_subgroup_of_gens rg Rl h1 hgen hRl⟩

@[expose] def invG (Rl : List S) : List S := Rl.filter fun x => decide (x ≠ 1 ∧ x * x = 1)

@[expose] def pairG (Rinv : List S) : List (S × S) :=
  Rinv.flatMap fun x => Rinv.filterMap fun y => if x ≠ y ∧ x * y = y * x then some (x, y) else none

omit [Finite S] in
theorem mem_invG {Rl : List S} {x : S} : x ∈ invG Rl ↔ x ∈ Rl ∧ x ≠ 1 ∧ x * x = 1 := by
  simp [invG]

omit [Finite S] in
theorem mem_pairG {Rinv : List S} {x y : S} :
    (x, y) ∈ pairG Rinv ↔ x ∈ Rinv ∧ y ∈ Rinv ∧ x ≠ y ∧ x * y = y * x := by
  simp only [pairG, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x', hx', y', hy', h⟩
    split_ifs at h with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hx', hy', hc.1, hc.2⟩
  · rintro ⟨hx, hy, hne, hc⟩
    exact ⟨x, hx, y, hy, by simp [hne, hc]⟩

variable {a m : ℕ} {Rl : List S}

omit [DecidableEq S] in
theorem SylowData.conj_into (h : SylowData S a m Rl) (B : Subgroup S) (hB : ∀ x ∈ B, x * x = 1) :
    ∃ g : S, ∀ x ∈ B, g * x * g⁻¹ ∈ Rl :=
  by
  obtain ⟨R, hR⟩ := h.subgroup
  exact exists_conj_mem_of_subgroup R Rl hR h.pow h.nodup h.length h.card h.odd B hB

theorem SylowData.rank_le (h : SylowData S a m Rl) (r : ℕ)
    (hrank : forallIndep (invG Rl) (fun _ => false) (r + 1) [] = true) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  intro B hcomm hsq
  by_contra hgt
  push Not at hgt
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  set B' : Subgroup S := B.map (MulAut.conj g).toMonoidHom with hB'
  have hmem : ∀ x ∈ B', x ∈ Rl := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y hy
  have hcomm' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = _ := by group
  have hsq' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show g * a * g⁻¹ * (g * a * g⁻¹) = 1
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨l, hl, hlen, hlB⟩ :=
    exists_indepList_of_lt_card B' hcomm' hsq' r (by rw [hcard]; exact hgt)
  have hl' : ∀ y ∈ l, y ∈ invG Rl := by
    intro y hy
    exact mem_invG.2 ⟨hmem y (hlB y hy), hl.ne_one y hy, hsq' y (hlB y hy)⟩
  have := forallIndep_sound (invG Rl) (fun _ => false) (r + 1) [] hrank l hlen hl'
    (by simpa using hl)
  simp at this

theorem SylowData.gen1 (h : SylowData S a m Rl) {k p : ℕ} (reps : List S)
    (hcover : ∀ x ∈ invG Rl, ∃ t0 ∈ reps, ∃ r ∈ Rl, r * x * r⁻¹ = t0)
    (hwit : ∀ t0 ∈ reps, ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t0}), orderOf x = p)
    (B : Subgroup S) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S)), orderOf x = p := by
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb'sq : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hsq b hbB]; group
  have hinv : g * b * g⁻¹ ∈ invG Rl :=
    mem_invG.2 ⟨hg b hbB, fun h => hb1' (conj_eq_one_iff.1 h), hb'sq⟩
  obtain ⟨t0, ht0, r, hr, hrt⟩ := hcover _ hinv
  obtain ⟨cs0, hcs0, x, hx, hxp⟩ := hwit t0 ht0
  have hx' := closure_conjSet_transfer (T := ({b} : Set S)) (r * g)
    (fun t' ht' => ⟨b, rfl, by
      have : t' = t0 := by simpa using ht'
      rw [this, ← hrt]; group⟩) cs0 hx
  refine ⟨cs0.map (· * (r * g)), by simpa using hcs0, x, ?_, hxp⟩
  exact Subgroup.closure_mono (conjSet_mono (by simpa using hbB)) hx'

omit [Finite S] in
theorem pair_mem_pairG {Rl : List S} {B : Subgroup S} {g : S} (hg : ∀ x ∈ B, g * x * g⁻¹ ∈ Rl)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) {x y : S} (hx : x ∈ B)
    (hy : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    (g * x * g⁻¹, g * y * g⁻¹) ∈ pairG (invG Rl) := by
  have hsqc : ∀ z : S, z * z = 1 → (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := fun z hz => by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz]; group
  refine mem_pairG.2 ⟨mem_invG.2 ⟨hg x hx, fun h => hx1 (conj_eq_one_iff.1 h), hsqc x (hsq x hx)⟩,
    mem_invG.2 ⟨hg y hy, fun h => hy1 (conj_eq_one_iff.1 h), hsqc y (hsq y hy)⟩,
    fun h => hxy (by simpa using h), ?_⟩
  calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hcomm x hx y hy]
    _ = _ := by group

theorem SylowData.gen2_of_count (h : SylowData S a m Rl) {k p : ℕ} (reps bad : List (S × S))
    (hcover : ∀ q ∈ pairG (invG Rl), q ∈ bad ∨ ∃ t ∈ reps, ∃ r ∈ Rl,
      r * q.1 * r⁻¹ = t.1 ∧ r * q.2 * r⁻¹ = t.2)
    (hwit : ∀ t ∈ reps, ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t.1, t.2}), orderOf x = p)
    (B : Subgroup S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hbig : bad.length < (Nat.card B - 1) * (Nat.card B - 2)) :
    ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S)), orderOf x = p := by
  classical
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  obtain ⟨P, hPcard, hP⟩ := card_distinct_nonid_pairs B
  have hex : ∃ q ∈ P, ∃ t ∈ reps, ∃ r ∈ Rl, r * (g * q.1 * g⁻¹) * r⁻¹ = t.1 ∧
      r * (g * q.2 * g⁻¹) * r⁻¹ = t.2 := by
    by_contra hno
    push Not at hno
    have hsub : P.image (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) ⊆ bad.toFinset := by
      intro q' hq'
      obtain ⟨q, hqP, rfl⟩ := Finset.mem_image.1 hq'
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP q hqP
      have hpair := pair_mem_pairG hg hcomm hsq h1 h2 h3 h4 h5
      rcases hcover _ hpair with hb | ⟨t, ht, r, hr, e1, e2⟩
      · simpa using hb
      · exact absurd e2 (hno q hqP t ht r hr e1)
    have hinj : Function.Injective (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) := by
      intro q q' hqq
      simp only [Prod.mk.injEq, mul_left_inj, mul_right_inj] at hqq
      exact Prod.ext hqq.1 hqq.2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at h1
    have h2 := List.toFinset_card_le bad
    omega
  obtain ⟨q, hqP, t, ht, r, hr, e1, e2⟩ := hex
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP q hqP
  obtain ⟨cs0, hcs0, z, hz, hzp⟩ := hwit t ht
  have hz' := closure_conjSet_transfer (T := ({q.1, q.2} : Set S)) (r * g)
    (fun t' ht' => by
      have : t' = t.1 ∨ t' = t.2 := by simpa using ht'
      rcases this with rfl | rfl
      · exact ⟨q.1, by simp, by rw [← e1]; group⟩
      · exact ⟨q.2, by simp, by rw [← e2]; group⟩) cs0 hz
  refine ⟨cs0.map (· * (r * g)), by simpa using hcs0, z, ?_, hzp⟩
  refine Subgroup.closure_mono (conjSet_mono ?_) hz'
  intro u hu
  rcases hu with rfl | rfl
  · exact h1
  · exact h2

theorem SylowData.gen2 (h : SylowData S a m Rl) {k p : ℕ} (reps : List (S × S))
    (hcover : ∀ q ∈ pairG (invG Rl), ∃ t ∈ reps, ∃ r ∈ Rl,
      r * q.1 * r⁻¹ = t.1 ∧ r * q.2 * r⁻¹ = t.2)
    (hwit : ∀ t ∈ reps, ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t.1, t.2}), orderOf x = p)
    (B : Subgroup S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (h3 : 2 < Nat.card B) :
    ∃ cs : List S, cs.length = k ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S)), orderOf x = p :=
  h.gen2_of_count reps [] (fun q hq => Or.inr (hcover q hq)) hwit B hcomm hsq
    (by simpa using Nat.mul_pos (by omega : 0 < Nat.card B - 1) (by omega : 0 < Nat.card B - 2))

theorem SylowData.card_le_of_count (h : SylowData S a m Rl) (r : ℕ)
    (hcount : (pairG (invG Rl)).length < (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2)) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  classical
  intro B hcomm hsq
  by_contra hgt
  push Not at hgt
  have hpg : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    have := hsq x x.2
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hpg
  have hrn : r + 1 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  obtain ⟨P, hPcard, hP⟩ := card_distinct_nonid_pairs B
  have hsub : P.image (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) ⊆
      (pairG (invG Rl)).toFinset := by
    intro q' hq'
    obtain ⟨q, hqP, rfl⟩ := Finset.mem_image.1 hq'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP q hqP
    simpa using pair_mem_pairG hg hcomm hsq h1 h2 h3 h4 h5
  have hinj : Function.Injective (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) := by
    intro q q' hqq
    simp only [Prod.mk.injEq, mul_left_inj, mul_right_inj] at hqq
    exact Prod.ext hqq.1 hqq.2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at h1
  have h2 := List.toFinset_card_le (pairG (invG Rl))
  have h3 : 2 ^ (r + 1) ≤ Nat.card B := by
    rw [hn]; exact Nat.pow_le_pow_right (by norm_num) hrn
  have h4 : (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2) ≤ (Nat.card B - 1) * (Nat.card B - 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end Gen

section Tables

variable {S : Type} [Group S] [DecidableEq S]

@[expose] def g1ok (Rl : List S) (conj : List (List ℤ) → List S)
    (G1 : List (ℕ × List (List ℤ) × List ℕ)) (p : ℕ) : Bool :=
  G1.all fun e => e.2.1.length == 2 && witOK [Rl.getD e.1 1] (conj e.2.1) e.2.2 p

@[expose] def g1cover (Rl : List S) (G1 : List (ℕ × List (List ℤ) × List ℕ)) : Bool :=
  (invG Rl).all fun x => G1.any fun e => Rl.any fun r => r * x * r⁻¹ == Rl.getD e.1 1

@[expose] def g2ok (Rl : List S) (conj : List (List ℤ) → List S)
    (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) (p : ℕ) : Bool :=
  G2.all fun e => e.2.2.1.length == 1 &&
    witOK [Rl.getD e.1 1, Rl.getD e.2.1 1] (conj e.2.2.1) e.2.2.2 p

@[expose] def g2cover (Rl : List S) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) : Bool :=
  (pairG (invG Rl)).all fun q => G2.any fun e =>
    Rl.any fun r => r * q.1 * r⁻¹ == Rl.getD e.1 1 && r * q.2 * r⁻¹ == Rl.getD e.2.1 1

theorem gen1_hyps (Rl : List S) (conj : List (List ℤ) → List S)
    (G1 : List (ℕ × List (List ℤ) × List ℕ)) {p : ℕ} [Fact p.Prime]
    (hok : g1ok Rl conj G1 p = true) (hconj : ∀ ws, (conj ws).length = ws.length)
    (hcov : g1cover Rl G1 = true) :
    (∀ x ∈ invG Rl, ∃ t0 ∈ G1.map (fun e => Rl.getD e.1 1), ∃ r ∈ Rl, r * x * r⁻¹ = t0) ∧
    (∀ t0 ∈ G1.map (fun e => Rl.getD e.1 1), ∃ cs : List S, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t0}), orderOf x = p) := by
  constructor
  · intro x hx
    obtain ⟨e, he, hanyr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcov x hx)
    obtain ⟨r, hr, hrx⟩ := List.any_eq_true.1 hanyr
    exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, r, hr, beq_iff_eq.1 hrx⟩
  · intro t0 ht0
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht0
    have hew := List.all_eq_true.1 hok e he
    simp only [Bool.and_eq_true] at hew
    obtain ⟨hlen, hw⟩ := hew
    obtain ⟨cs0, hcs0, x, hx, hxp⟩ := exists_gen_of_witOK [Rl.getD e.1 1] (conj e.2.1) e.2.2
      (p := p) hw
    have hlen' : e.2.1.length = 2 := by simpa using hlen
    exact ⟨cs0, by rw [hcs0, hconj, hlen'], x, by simpa using hx, hxp⟩

theorem g2ok_wit (Rl : List S) (conj : List (List ℤ) → List S)
    (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) {p : ℕ} [Fact p.Prime]
    (hok : g2ok Rl conj G2 p = true) (hconj : ∀ ws, (conj ws).length = ws.length) :
    ∀ t ∈ G2.map (fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)), ∃ cs : List S, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t.1, t.2}), orderOf x = p := by
  intro t ht0
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht0
  have hew := List.all_eq_true.1 hok e he
  simp only [Bool.and_eq_true] at hew
  obtain ⟨hlen, hw⟩ := hew
  obtain ⟨cs0, hcs0, x, hx, hxp⟩ := exists_gen_of_witOK [Rl.getD e.1 1, Rl.getD e.2.1 1]
    (conj e.2.2.1) e.2.2.2 (p := p) hw
  have hlen' : e.2.2.1.length = 1 := by simpa using hlen
  have hset : {t | t ∈ [Rl.getD e.1 1, Rl.getD e.2.1 1]} =
      ({Rl.getD e.1 1, Rl.getD e.2.1 1} : Set S) := by
    ext t
    simp
  exact ⟨cs0, by rw [hcs0, hconj, hlen'], x, by rw [← hset]; exact hx, hxp⟩

theorem gen2_hyps (Rl : List S) (conj : List (List ℤ) → List S)
    (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) {p : ℕ} [Fact p.Prime]
    (hok : g2ok Rl conj G2 p = true) (hconj : ∀ ws, (conj ws).length = ws.length)
    (hcov : g2cover Rl G2 = true) :
    (∀ q ∈ pairG (invG Rl), ∃ t0 ∈ G2.map (fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)),
      ∃ r ∈ Rl, r * q.1 * r⁻¹ = t0.1 ∧ r * q.2 * r⁻¹ = t0.2) ∧
    (∀ t0 ∈ G2.map (fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)), ∃ cs : List S, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t0.1, t0.2}), orderOf x = p) := by
  refine ⟨fun q hq => ?_, g2ok_wit Rl conj G2 hok hconj⟩
  obtain ⟨e, he, hanyr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcov q hq)
  obtain ⟨r, hr, hrx⟩ := List.any_eq_true.1 hanyr
  simp only [Bool.and_eq_true] at hrx
  exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, r, hr, beq_iff_eq.1 hrx.1, beq_iff_eq.1 hrx.2⟩

end Tables

end CFSG.QuasithinUnique.Setup.X1
