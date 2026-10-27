module

public import CFSG.ClassicalInvolution.SmallCases.SmallWeylFour

public section

namespace CFSG.ClassicalInvolution.SmallWeyl

private def starFam : List (List (ℕ × ℕ)) := [
  [(1, 2), (2, 1), (3, 3)],
  [(1, 2), (1, 6), (2, 1), (2, 5), (3, 3), (3, 7)],
  [(1, 2), (1, 10), (2, 1), (2, 9), (3, 3), (3, 11)],
  [(1, 2), (1, 14), (2, 1), (2, 13), (3, 3), (3, 15)],
  [(1, 2), (2, 1), (3, 3), (5, 2), (6, 1), (7, 3)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11)],
  [(1, 2), (2, 1), (3, 3), (9, 2), (10, 1), (11, 3)],
  [(1, 2), (2, 1), (3, 3), (9, 6), (10, 5), (11, 7)],
  [(1, 2), (2, 1), (3, 3), (13, 2), (14, 1), (15, 3)],
  [(1, 2), (2, 1), (3, 3), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (1, 14), (2, 1), (2, 13), (3, 3), (3, 15), (13, 2), (13, 14), (14, 1), (14, 13),
    (15, 3), (15, 15)],
  [(1, 2), (2, 1), (3, 3), (4, 8), (9, 6), (10, 5), (11, 7), (13, 14), (14, 13), (15, 15)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11), (8, 4), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (2, 1), (3, 3), (4, 8), (5, 10), (6, 9), (7, 11), (8, 4), (9, 6), (10, 5), (11, 7),
    (12, 12), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (2, 1), (3, 3), (5, 2), (6, 1), (7, 3), (9, 2), (10, 1), (11, 3), (13, 2), (14, 1),
    (15, 3)],
  [
    (1, 2), (1, 6), (2, 1), (2, 5), (3, 3), (3, 7), (9, 2), (9, 6), (10, 1), (10, 5), (11, 3),
    (11, 7)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11), (9, 6), (10, 5), (11, 7), (12, 12)],
  [
    (1, 2), (1, 10), (2, 1), (2, 9), (3, 3), (3, 11), (5, 2), (5, 10), (6, 1), (6, 9), (7, 3),
    (7, 11)],
  [
    (1, 2), (1, 6), (1, 10), (1, 14), (2, 1), (2, 5), (2, 9), (2, 13), (3, 3), (3, 7), (3, 11),
    (3, 15)]
]


private theorem familyOK_starFam : familyOK 4 30 starFam = true := by decide +kernel

private theorem seed_mem_starFam : [(1, 2), (2, 1), (3, 3)] ∈ starFam := by decide

@[expose] def HasTriC (R : Finset (ℕ × ℕ)) : Prop :=
  ∃ a ∈ R, ∃ b ∈ R, ∃ c ∈ R, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    adjC a b = false ∧ adjC a c = false ∧ adjC b c = false

@[expose] def HasStarC (R : Finset (ℕ × ℕ)) : Prop :=
  ∃ c ∈ R, ∃ a ∈ R, ∃ b ∈ R, ∃ d ∈ R, adjC c a = true ∧ adjC c b = true ∧ adjC c d = true ∧
    a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ adjC a b = false ∧ adjC a d = false ∧ adjC b d = false

private def triL (S : List (ℕ × ℕ)) : Bool :=
  S.any fun a => S.any fun b => S.any fun c =>
    a != b && a != c && b != c && !adjC a b && !adjC a c && !adjC b c

private def starL (S : List (ℕ × ℕ)) : Bool :=
  S.any fun c => S.any fun a => S.any fun b => S.any fun d =>
    adjC c a && adjC c b && adjC c d && a != b && a != d && b != d && !adjC a b && !adjC a d &&
      !adjC b d

private def triTab (𝓛 : List (List (ℕ × ℕ))) : Bool :=
  𝓛.all fun S => decide S.Nodup && (S.length != 12 || starL S) && (S.length != 10 || !triL S)

private theorem triTab_starFam : triTab starFam = true := by decide +kernel

private theorem triL_eq_true {S : List (ℕ × ℕ)} :
    triL S = true ↔ ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      adjC a b = false ∧ adjC a c = false ∧ adjC b c = false := by
  simp only [triL, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨a, ha, b, hb, c, hc, by tauto⟩
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨a, ha, b, hb, c, hc, by tauto⟩

private theorem starL_eq_true {S : List (ℕ × ℕ)} :
    starL S = true ↔ ∃ c ∈ S, ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S, adjC c a = true ∧ adjC c b = true ∧
      adjC c d = true ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ adjC a b = false ∧ adjC a d = false ∧
      adjC b d = false := by
  simp only [starL, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨c, hc, a, ha, b, hb, d, hd, h⟩
    exact ⟨c, hc, a, ha, b, hb, d, hd, by tauto⟩
  · rintro ⟨c, hc, a, ha, b, hb, d, hd, h⟩
    exact ⟨c, hc, a, ha, b, hb, d, hd, by tauto⟩

theorem IsAutC.hasTriC_image {g : ℕ × ℕ → ℕ × ℕ} (hg : IsAutC g) {R : Finset (ℕ × ℕ)}
    (hR : CodedSet 4 R) : HasTriC (R.image g) ↔ HasTriC R := by
  have hinj := hg.injOn hR.valid
  constructor
  · rintro ⟨a', ha', b', hb', c', hc', hab, hac, hbc, h1, h2, h3⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    refine ⟨a, ha, b, hb, c, hc, fun h => hab (congrArg g h), fun h => hac (congrArg g h),
      fun h => hbc (congrArg g h), ?_, ?_, ?_⟩
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)] at h1
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid c hc)] at h2
    · rwa [hg.adjC_eq (hR.valid b hb) (hR.valid c hc)] at h3
  · rintro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h1, h2, h3⟩
    refine ⟨g a, Finset.mem_image_of_mem _ ha, g b, Finset.mem_image_of_mem _ hb, g c,
      Finset.mem_image_of_mem _ hc, fun h => hab (hinj ha hb h), fun h => hac (hinj ha hc h),
      fun h => hbc (hinj hb hc h), ?_, ?_, ?_⟩
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)]
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid c hc)]
    · rwa [hg.adjC_eq (hR.valid b hb) (hR.valid c hc)]

theorem IsAutC.hasStarC_image {g : ℕ × ℕ → ℕ × ℕ} (hg : IsAutC g) {R : Finset (ℕ × ℕ)}
    (hR : CodedSet 4 R) : HasStarC (R.image g) ↔ HasStarC R := by
  have hinj := hg.injOn hR.valid
  constructor
  · rintro ⟨c', hc', a', ha', b', hb', d', hd', h1, h2, h3, hab, had, hbd, h4, h5, h6⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    refine ⟨c, hc, a, ha, b, hb, d, hd, ?_, ?_, ?_, fun h => hab (congrArg g h),
      fun h => had (congrArg g h), fun h => hbd (congrArg g h), ?_, ?_, ?_⟩
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid a ha)] at h1
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid b hb)] at h2
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid d hd)] at h3
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)] at h4
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid d hd)] at h5
    · rwa [hg.adjC_eq (hR.valid b hb) (hR.valid d hd)] at h6
  · rintro ⟨c, hc, a, ha, b, hb, d, hd, h1, h2, h3, hab, had, hbd, h4, h5, h6⟩
    refine ⟨g c, Finset.mem_image_of_mem _ hc, g a, Finset.mem_image_of_mem _ ha, g b,
      Finset.mem_image_of_mem _ hb, g d, Finset.mem_image_of_mem _ hd, ?_, ?_, ?_,
      fun h => hab (hinj ha hb h), fun h => had (hinj ha hd h), fun h => hbd (hinj hb hd h),
      ?_, ?_, ?_⟩
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid a ha)]
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid b hb)]
    · rwa [hg.adjC_eq (hR.valid c hc) (hR.valid d hd)]
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)]
    · rwa [hg.adjC_eq (hR.valid a ha) (hR.valid d hd)]
    · rwa [hg.adjC_eq (hR.valid b hb) (hR.valid d hd)]

theorem Red.normalizeWith {gens : List (ℕ × ℕ → ℕ × ℕ)} (hgens : ∀ g ∈ gens, IsAutC g)
    (P : Finset (ℕ × ℕ) → Prop)
    (hP : ∀ g ∈ gens, ∀ R : Finset (ℕ × ℕ), CodedSet 4 R → P (R.image g) → P R)
    {a₀ b₀ a b : ℕ × ℕ} (h : Red gens a₀ b₀ a b) :
    ∀ R : Finset (ℕ × ℕ), CodedSet 4 R → a ∈ R → b ∈ R →
      ∃ R' : Finset (ℕ × ℕ), CodedSet 4 R' ∧ a₀ ∈ R' ∧ b₀ ∈ R' ∧ (P R' → P R) := by
  induction h with
  | base => exact fun R hR ha hb => ⟨R, hR, ha, hb, fun h => h⟩
  | @step g hg a b _ ih =>
    intro R hR ha hb
    obtain ⟨R', hR', h1, h2, h3⟩ := ih (R.image g) ((hgens g hg).codedSet_image hR)
      (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
    exact ⟨R', hR', h1, h2, fun h => hP g hg R hR (h3 h)⟩

@[expose] def TriStarOK (R : Finset (ℕ × ℕ)) : Prop :=
  (R.card = 12 → HasStarC R) ∧ (R.card = 10 → ¬ HasTriC R)

private theorem triStarOK_of_image {g : ℕ × ℕ → ℕ × ℕ} (hg : IsAutC g) {R : Finset (ℕ × ℕ)}
    (hR : CodedSet 4 R) (h : TriStarOK (R.image g)) : TriStarOK R := by
  have hc : (R.image g).card = R.card := Finset.card_image_of_injOn (hg.injOn hR.valid)
  refine ⟨fun h12 => ?_, fun h10 ht => ?_⟩
  · exact (hg.hasStarC_image hR).mp (h.1 (hc ▸ h12))
  · exact h.2 (hc ▸ h10) ((hg.hasTriC_image hR).mpr ht)

theorem triStar_four {R : Finset (ℕ × ℕ)} (hne : R.Nonempty) (hR : CodedSet 4 R) :
    TriStarOK R := by
  by_cases hadj : ∃ a ∈ R, ∃ b ∈ R, adjC a b = true
  · obtain ⟨a, ha, b, hb, hab⟩ := hadj
    obtain ⟨R', hR', h1, h2, h3⟩ :=
      (red_of_adj (hR.valid a ha) (hR.valid b hb) hab).normalizeWith
        (fun g hg => isAutC_of_mem_allGens hg) TriStarOK
        (fun g hg R hR h => triStarOK_of_image (isAutC_of_mem_allGens hg) hR h) R hR ha hb
    refine h3 ?_
    have h12 : adjC (1, 2) (2, 1) = true := by decide
    obtain ⟨S, hS, hSR⟩ := exists_mem_family (d := 4) (fuel := 30) (by norm_num) familyOK_starFam
      R' hR'.valid hR'.closed hR'.sym hR'.conn
      ⟨[(1, 2), (2, 1), (3, 3)], seed_mem_starFam, by simp, fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact hR'.closed _ h1 _ h2 h12⟩
    have htab := List.all_eq_true.mp triTab_starFam S hS
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_true'] at htab
    obtain ⟨⟨hnd, h12S⟩, h10S⟩ := htab
    have hRS : S.toFinset = R' := Finset.ext fun x => by simpa using hSR x
    have hcard : R'.card = S.length := by rw [← hRS, List.toFinset_card_of_nodup hnd]
    refine ⟨fun hc => ?_, fun hc ht => ?_⟩
    · rw [hcard] at hc
      obtain ⟨c, hcS, a, haS, b, hbS, d, hdS, hca, hcb, hcd, hab, had, hbd, e1, e2, e3⟩ :=
        starL_eq_true.mp (h12S.resolve_left (by omega))
      exact ⟨c, (hSR c).mp hcS, a, (hSR a).mp haS, b, (hSR b).mp hbS, d, (hSR d).mp hdS, hca, hcb,
        hcd, hab, had, hbd, e1, e2, e3⟩
    · rw [hcard] at hc
      obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc, e1, e2, e3⟩ := ht
      have h := h10S.resolve_left (by omega)
      have : triL S = true := triL_eq_true.mpr ⟨a, (hSR a).mpr ha, b, (hSR b).mpr hb, c,
        (hSR c).mpr hc', hab, hac, hbc, e1, e2, e3⟩
      rw [this] at h
      exact absurd h (by decide)
  · push Not at hadj
    have hsingle : ∀ a ∈ R, ∀ b ∈ R, a = b := by
      intro a ha b hb
      have h := hR.conn a ha b hb
      induction h with
      | refl => rfl
      | @tail u v _ hstep _ => exact absurd (hadj u hstep.1 v hstep.2.1) (by simp [hstep.2.2])
    obtain ⟨p₀, hp₀⟩ := hne
    have hc1 : R.card = 1 := Finset.card_eq_one.mpr ⟨p₀, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hp₀, fun x hx => hsingle x hx p₀ hp₀⟩⟩
    exact ⟨fun h => by omega, fun h => by omega⟩

section Bridge

variable {A : Type*} [AddCommGroup A]

private theorem codedSet_image_code {d : ℕ} (hE : EncOK d) (e : A ≃+ (Fin d → ZMod 2))
    {R : Finset (Datum A)} (hs : IsSymm R) (hc : IsClosed R) (hconn : IsConn R) :
    CodedSet d (R.image (Datum.code e)) where
  valid := by
    intro a ha
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
    exact Datum.validC_code hE e p
  closed := by
    intro a ha b hb hab
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    rw [Datum.addC_code hE e ((Datum.adjC_code hE e p q).mp hab)]
    exact Finset.mem_image_of_mem _ (hc p hp q hq)
  sym := by
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    rw [Datum.pairC_code hE e, Datum.pairC_code hE e, hs p hp q hq]
  conn := by
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    refine (hconn p hp q hq).lift (Datum.code e) fun a b hab => ?_
    exact ⟨Finset.mem_image_of_mem _ hab.1, Finset.mem_image_of_mem _ hab.2.1,
      (Datum.adjC_code hE e a b).mpr hab.2.2⟩

private theorem adjC_code_eq_false {d : ℕ} (hE : EncOK d) (e : A ≃+ (Fin d → ZMod 2))
    (p q : Datum A) : adjC (p.code e) (q.code e) = false ↔ ¬ p.Adj q := by
  rw [← Datum.adjC_code hE e p q]
  exact Bool.eq_false_iff.trans (by simp)

theorem rootSet_triStar_four (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 16)
    (R : Finset (Datum A)) (hne : R.Nonempty) (hs : IsSymm R) (hc : IsClosed R)
    (hconn : IsConn R) :
    (R.card = 12 → ∃ c ∈ R, ∃ a ∈ R, ∃ b ∈ R, ∃ d ∈ R, c.Adj a ∧ c.Adj b ∧ c.Adj d ∧
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ ¬ a.Adj b ∧ ¬ a.Adj d ∧ ¬ b.Adj d) ∧
    (R.card = 10 → ¬ ∃ a ∈ R, ∃ b ∈ R, ∃ d ∈ R, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      ¬ a.Adj b ∧ ¬ a.Adj d ∧ ¬ b.Adj d) := by
  obtain ⟨e⟩ := nonempty_addEquiv_of_card h2 (hcard.trans (by norm_num : 16 = 2 ^ 4))
  have hE : EncOK 4 := encOK_four
  have hinj := Datum.code_injective hE e
  have hcard' : (R.image (Datum.code e)).card = R.card := Finset.card_image_of_injective _ hinj
  obtain ⟨h12, h10⟩ := triStar_four (hne.image _) (codedSet_image_code hE e hs hc hconn)
  refine ⟨fun hR => ?_, fun hR ⟨a, ha, b, hb, d, hd, hab, had, hbd, n1, n2, n3⟩ => ?_⟩
  · obtain ⟨c', hc', a', ha', b', hb', d', hd', e1, e2, e3, hab, had, hbd, n1, n2, n3⟩ :=
      h12 (hcard'.trans hR)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    exact ⟨c, hc, a, ha, b, hb, d, hd, (Datum.adjC_code hE e c a).mp e1,
      (Datum.adjC_code hE e c b).mp e2, (Datum.adjC_code hE e c d).mp e3,
      fun h => hab (congrArg _ h), fun h => had (congrArg _ h), fun h => hbd (congrArg _ h),
      (adjC_code_eq_false hE e a b).mp n1, (adjC_code_eq_false hE e a d).mp n2,
      (adjC_code_eq_false hE e b d).mp n3⟩
  · exact h10 (hcard'.trans hR) ⟨Datum.code e a, Finset.mem_image_of_mem _ ha, Datum.code e b,
      Finset.mem_image_of_mem _ hb, Datum.code e d, Finset.mem_image_of_mem _ hd,
      fun h => hab (hinj h), fun h => had (hinj h), fun h => hbd (hinj h),
      (adjC_code_eq_false hE e a b).mpr n1, (adjC_code_eq_false hE e a d).mpr n2,
      (adjC_code_eq_false hE e b d).mpr n3⟩

end Bridge

section Rack

variable {A : Type*} [AddCommGroup A]

theorem Datum.adj_conj_left {p q : Datum A} (h : p.Adj q) : p.Adj (p.conj q) := by
  obtain ⟨h1, h2⟩ := h
  have hp := p.form_vec
  refine ⟨?_, ?_⟩
  · show p.form (q.vec + (if p.pair q = 1 then p.vec else 0)) = 1
    simp only [h1, ↓reduceIte, map_add, hp, add_zero]
    exact h1
  · show (q.form + (if q.pair p = 1 then p.form else 0)) p.vec = 1
    simp only [h2, ↓reduceIte, AddMonoidHom.add_apply, hp, add_zero]
    exact h2

theorem Datum.conj_eq_of_not_pair {p q : Datum A} (h1 : ¬ p.pair q = 1) (h2 : ¬ q.pair p = 1) :
    p.conj q = q :=
  Datum.ext (by simp [Datum.conj, h1]) (by simp [Datum.conj, h2])

theorem exists_component {R : Finset (Datum A)} (hs : IsSymm R) (hc : IsClosed R) {x : Datum A}
    (hx : x ∈ R) :
    ∃ C : Finset (Datum A), C ⊆ R ∧ x ∈ C ∧ IsSymm C ∧ IsClosed C ∧ IsConn C ∧
      ∀ y ∈ R, x.Adj y → y ∈ C := by
  classical
  set C : Finset (Datum A) :=
    R.filter fun y => Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y with hC
  have hmem : ∀ y, y ∈ C ↔
      y ∈ R ∧ Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y :=
    fun y => Finset.mem_filter
  have hxC : x ∈ C := (hmem x).mpr ⟨hx, Relation.ReflTransGen.refl⟩
  refine ⟨C, Finset.filter_subset _ _, hxC, ?_, ?_, ?_, ?_⟩
  · exact fun p hp q hq => hs p ((hmem p).mp hp).1 q ((hmem q).mp hq).1
  · intro p hp q hq
    obtain ⟨hpR, hxp⟩ := (hmem p).mp hp
    obtain ⟨hqR, hxq⟩ := (hmem q).mp hq
    have hr : p.conj q ∈ R := hc p hpR q hqR
    refine (hmem _).mpr ⟨hr, ?_⟩
    have hsym := hs p hpR q hqR
    by_cases hpq : p.pair q = 1
    · have hqp : q.pair p = 1 := hsym.symm.trans hpq
      exact hxp.tail ⟨hpR, hr, Datum.adj_conj_left ⟨hpq, hqp⟩⟩
    · have hqp : ¬ q.pair p = 1 := fun h => hpq (hsym.trans h)
      rw [Datum.conj_eq_of_not_pair hpq hqp]
      exact hxq
  · have key : ∀ y, Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) x y →
        Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ a.Adj b) x y := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hxb hbc ih =>
        have hbC : b ∈ C := (hmem b).mpr ⟨hbc.1, hxb⟩
        have hcC : c ∈ C := (hmem c).mpr ⟨hbc.2.1, hxb.tail hbc⟩
        exact ih.tail ⟨hbC, hcC, hbc.2.2⟩
    intro p hp q hq
    have : Std.Symm (fun a b : Datum A => a ∈ C ∧ b ∈ C ∧ a.Adj b) :=
      ⟨fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
    exact (Std.Symm.symm _ _ (key p ((hmem p).mp hp).2)).trans (key q ((hmem q).mp hq).2)
  · intro y hy hxy
    exact (hmem y).mpr ⟨hy, Relation.ReflTransGen.single ⟨hx, hy, hxy⟩⟩

theorem rootSet_eq_of_chain_three (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 8)
    {R R₀ : Finset (Datum A)} (hR : R.card = 6) (hsub : R₀ ⊆ R) (hs : IsSymm R₀)
    (hc : IsClosed R₀) {x₀ x₁ x₂ : Datum A} (h₀ : x₀ ∈ R₀) (h₁ : x₁ ∈ R₀) (h₂ : x₂ ∈ R₀)
    (a₀ : x₁.Adj x₀) (a₂ : x₁.Adj x₂) (n : ¬ x₀.Adj x₂) (hne : x₀ ≠ x₂) : R₀ = R := by
  obtain ⟨C, hCR, hxC, hCs, hCc, hCconn, hnb⟩ := exists_component hs hc h₁
  have h0C := hnb x₀ h₀ a₀
  have h2C := hnb x₂ h₂ a₂
  rcases rootSet_classification_three h2 hcard C ⟨x₁, hxC⟩ hCs hCc hCconn with
    h | ⟨-, hadj⟩ | ⟨h6, -⟩
  · exact absurd (Finset.card_le_one.mp h.le x₀ h0C x₂ h2C) hne
  · exact absurd (hadj x₀ h0C x₂ h2C hne) n
  · have hCeq : C = R := Finset.eq_of_subset_of_card_le (hCR.trans hsub) (by omega)
    exact Finset.Subset.antisymm hsub (hCeq ▸ hCR)

theorem rootSet_eq_of_star_four (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 16)
    {R R₀ : Finset (Datum A)} (hR : R.card = 12) (hsub : R₀ ⊆ R) (hs : IsSymm R₀)
    (hc : IsClosed R₀) {x₀ x₁ x₂ x₃ : Datum A} (h₀ : x₀ ∈ R₀) (h₁ : x₁ ∈ R₀) (h₂ : x₂ ∈ R₀)
    (h₃ : x₃ ∈ R₀) (a₀ : x₁.Adj x₀) (a₂ : x₁.Adj x₂) (a₃ : x₁.Adj x₃) (n₀₂ : ¬ x₀.Adj x₂)
    (n₀₃ : ¬ x₀.Adj x₃) (n₂₃ : ¬ x₂.Adj x₃) (d₀₂ : x₀ ≠ x₂) (d₀₃ : x₀ ≠ x₃) (d₂₃ : x₂ ≠ x₃) :
    R₀ = R := by
  obtain ⟨C, hCR, hxC, hCs, hCc, hCconn, hnb⟩ := exists_component hs hc h₁
  have h0C := hnb x₀ h₀ a₀
  have h2C := hnb x₂ h₂ a₂
  have h3C := hnb x₃ h₃ a₃
  have hCle : C.card ≤ 12 := hR ▸ Finset.card_le_card (hCR.trans hsub)
  rcases rootSet_classification_four h2 hcard C ⟨x₁, hxC⟩ hCs hCc hCconn with
    h | ⟨-, hadj⟩ | ⟨-, huniq⟩ | ⟨h10, -⟩ | ⟨h12, -⟩ | ⟨h15, -⟩
  · exact absurd (Finset.card_le_one.mp h.le x₀ h0C x₂ h2C) d₀₂
  · exact absurd (hadj x₀ h0C x₂ h2C d₀₂) n₀₂
  · obtain ⟨q, -, hq⟩ := huniq x₀ h0C
    exact absurd ((hq x₂ ⟨h2C, d₀₂.symm, n₀₂⟩).trans (hq x₃ ⟨h3C, d₀₃.symm, n₀₃⟩).symm) d₂₃
  · exact absurd ⟨x₀, h0C, x₂, h2C, x₃, h3C, d₀₂, d₀₃, d₂₃, n₀₂, n₀₃, n₂₃⟩
      ((rootSet_triStar_four h2 hcard C ⟨x₁, hxC⟩ hCs hCc hCconn).2 h10)
  · have hCeq : C = R := Finset.eq_of_subset_of_card_le (hCR.trans hsub) (by omega)
    exact Finset.Subset.antisymm hsub (hCeq ▸ hCR)
  · omega

end Rack

end CFSG.ClassicalInvolution.SmallWeyl
