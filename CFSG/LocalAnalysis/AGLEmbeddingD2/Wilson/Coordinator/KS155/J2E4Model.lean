module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public import Certificates.Certificate12643
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.Tools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem ks155_parts : eltsOK () = true ∧
    enumsOK (c5a ()) (c5c ()) (c7 ()) (cE ()) (cD ()) (cS5 ()) = true ∧
    bruteOK (c5a ()) (c5c ()) (c7 ()) (cE ()) = true ∧ linesOK (cS5 ()) = true ∧
    dOK (cE ()) (cD ()) = true := by
  have h := Certificates.certificate12643
  unfold ks155OK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem all_spec {gs : Array (Array ℕ)} {p : Array ℕ → Bool} (h : gs.all p = true) :
    ∀ k < gs.size, p gs[k]! = true := by
  intro k hk
  rw [Array.all_eq_true] at h
  rw [getElem!_pos gs k hk]
  exact h k hk

theorem elts_parts :
    okA x7A = true ∧ okA x5aA = true ∧ okA x5cA = true ∧ okA y2A = true ∧ okA e1A = true ∧
      okA e2A = true ∧ gC5a.all okA = true ∧ gC5c.all okA = true ∧ gCE.all okA = true ∧
      gD.all okA = true ∧ lineA.all okA = true ∧ transA.all okA = true ∧ dUA.all okA = true ∧
      dVA.all okA = true ∧
      eqA 315 (powArr 315 x7A 7) (idA 315) = true ∧ eqA 315 x7A (idA 315) = false ∧
      eqA 315 (powArr 315 x5aA 5) (idA 315) = true ∧ eqA 315 x5aA (idA 315) = false ∧
      eqA 315 (powArr 315 x5cA 5) (idA 315) = true ∧ eqA 315 x5cA (idA 315) = false ∧
      eqA 315 (powArr 315 e1A 2) (idA 315) = true ∧ eqA 315 (powArr 315 e2A 2) (idA 315) = true ∧
      eqA 315 e1A (idA 315) = false ∧ eqA 315 e2A (idA 315) = false ∧ eqA 315 e1A e2A = false ∧
      commA e1A e2A = true ∧ commA e1A x5aA = true ∧ commA e2A x5aA = true := by
  have h := ks155_parts.1
  unfold eltsOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩,
    h27⟩, h28⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28⟩

theorem enums_parts :
    enumOK 315 gC5a keyPts (c5a ()) = true ∧ (c5a ()).pts.size = 300 ∧
      enumOK 315 gC5c keyPts (c5c ()) = true ∧ (c5c ()).pts.size = 50 ∧
      enumOK 315 gC7 keyPts (c7 ()) = true ∧ (c7 ()).pts.size = 7 ∧
      enumOK 315 gCE keyPts (cE ()) = true ∧ (cE ()).pts.size = 240 ∧
      enumOK 315 gD keyPts (cD ()) = true ∧ (cD ()).pts.size = 60 ∧
      enumOK 315 gS5 keyPts (cS5 ()) = true ∧ (cS5 ()).pts.size = 25 ∧
      gC5a.all (fun t => commA t x5aA) = true ∧ gC5c.all (fun t => commA t x5cA) = true ∧
      gCE.all (fun t => commA t e1A && commA t e2A) = true := by
  have h := ks155_parts.2.1
  unfold enumsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem lines_parts :
    (∀ k < (cS5 ()).pts.size, eqA 315 (cS5 ()).pts[k]! (idA 315) = true ∨
      ∃ j < 6, ∃ e < 5, eqA 315 (cS5 ()).pts[k]! (powArr 315 lineA[j]! e) = true) ∧
      lineA.size = 6 ∧ transA.size = 6 ∧ recL.length = 6 ∧
      ∀ j < 6, eqA 315 (powArr 315 lineA[j]! 5) (idA 315) = true ∧ recL.getD j 0 < 2 ∧
        eqA 315 (conjA 315 transA[j]! caseA[recL.getD j 0]!) lineA[j]! = true := by
  have h := ks155_parts.2.2.2.1
  unfold linesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩ := h
  refine ⟨fun k hk => ?_, h2, h3, h4, fun j hj => ?_⟩
  · have := allLt_spec h1 hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at this
    rcases this with h | ⟨j, hj, e, he, hje⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, e, he, hje⟩
  · have := allLt_spec h6 hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem d_parts :
    gD.all (inCert (cE ())) = true ∧ dUA.size = gD.size ∧ dVA.size = gD.size ∧
      (∀ i < gD.size, inCert (cD ()) dUA[i]! = true ∧ inCert (cD ()) dVA[i]! = true ∧
        eqA 315 gD[i]! (commutatorA 315 dUA[i]! dVA[i]!) = true) ∧
      inCert (cD ()) e1A = false ∧ inCert (cD ()) e2A = false ∧
      inCert (cD ()) (compA 315 e1A e2A) = false := by
  have h := ks155_parts.2.2.2.2
  unfold dOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5, h6, h7⟩
  have := allLt_spec h4 hi
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

section Elements

@[expose] noncomputable def x7J : GJ := eltOf x7A elts_parts.1

@[expose] noncomputable def x5aJ : GJ := eltOf x5aA elts_parts.2.1

@[expose] noncomputable def x5cJ : GJ := eltOf x5cA elts_parts.2.2.1

@[expose] noncomputable def e1J : GJ := eltOf e1A elts_parts.2.2.2.2.1

@[expose] noncomputable def e2J : GJ := eltOf e2A elts_parts.2.2.2.2.2.1

theorem rep_x7 : Rep 315 x7A x7J.1 := rep_eltOf _

theorem rep_x5a : Rep 315 x5aA x5aJ.1 := rep_eltOf _

theorem rep_x5c : Rep 315 x5cA x5cJ.1 := rep_eltOf _

theorem rep_e1 : Rep 315 e1A e1J.1 := rep_eltOf _

theorem rep_e2 : Rep 315 e2A e2J.1 := rep_eltOf _

@[expose] noncomputable def lineJ (j : ℕ) : GJ :=
  if h : j < lineA.size then eltOf lineA[j]! (all_spec elts_parts.2.2.2.2.2.2.2.2.2.2.1 j h) else 1

@[expose] noncomputable def transJ (j : ℕ) : GJ :=
  if h : j < transA.size then eltOf transA[j]! (all_spec elts_parts.2.2.2.2.2.2.2.2.2.2.2.1 j h)
  else 1

@[expose] noncomputable def caseJ (c : ℕ) : GJ := if c = 0 then x5aJ else x5cJ

theorem rep_lineJ {j : ℕ} (hj : j < 6) : Rep 315 lineA[j]! (lineJ j).1 := by
  have h : j < lineA.size := by rw [lines_parts.2.1]; exact hj
  simp only [lineJ, h, ↓reduceDIte]
  exact rep_eltOf _

theorem rep_transJ {j : ℕ} (hj : j < 6) : Rep 315 transA[j]! (transJ j).1 := by
  have h : j < transA.size := by rw [lines_parts.2.2.1]; exact hj
  simp only [transJ, h, ↓reduceDIte]
  exact rep_eltOf _

theorem valid_transA {j : ℕ} (hj : j < 6) : validA 315 transA[j]! = true :=
  (okA_spec (all_spec elts_parts.2.2.2.2.2.2.2.2.2.2.2.1 j
    (by rw [lines_parts.2.2.1]; exact hj))).1

theorem rep_caseJ {c : ℕ} (hc : c < 2) : Rep 315 caseA[c]! (caseJ c).1 := by
  interval_cases c
  · exact rep_x5a
  · exact rep_x5c

theorem x7_pow : x7J ^ 7 = 1 :=
  eq_of_rep (rep_pow rep_x7 7) rep_one elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x7_ne_one : x7J ≠ 1 := fun h => by
  have := (eqA_iff rep_x7 rep_one).2 (congrArg Subtype.val h)
  rw [elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem x5a_pow : x5aJ ^ 5 = 1 :=
  eq_of_rep (rep_pow rep_x5a 5) rep_one elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x5c_pow : x5cJ ^ 5 = 1 :=
  eq_of_rep (rep_pow rep_x5c 5) rep_one elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e1_sq : e1J * e1J = 1 := by
  rw [← pow_two]
  exact eq_of_rep (rep_pow rep_e1 2) rep_one
    elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e2_sq : e2J * e2J = 1 := by
  rw [← pow_two]
  exact eq_of_rep (rep_pow rep_e2 2) rep_one
    elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ne_of_eqA_false {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (he : eqA 315 t u = false) : g ≠ h := fun hgh => by
  have := (eqA_iff ht hu).2 (congrArg Subtype.val hgh)
  rw [he] at this
  exact Bool.false_ne_true this

theorem e1_ne_one : e1J ≠ 1 :=
  ne_of_eqA_false rep_e1 rep_one elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e2_ne_one : e2J ≠ 1 :=
  ne_of_eqA_false rep_e2 rep_one elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e1_ne_e2 : e1J ≠ e2J :=
  ne_of_eqA_false rep_e1 rep_e2 elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e1_comm_e2 : e1J * e2J = e2J * e1J :=
  (commute_of_commA rep_e1 rep_e2 elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).eq

theorem e1_comm_x5a : Commute e1J x5aJ :=
  commute_of_commA rep_e1 rep_x5a elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e2_comm_x5a : Commute e2J x5aJ :=
  commute_of_commA rep_e2 rep_x5a elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Elements

section Cent

theorem okA_all_spec {gs : Array (Array ℕ)} (h : gs.all okA = true) :
    ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true :=
  fun k hk => okA_spec (all_spec h k hk)

theorem subOf_le_centralizer {gs : Array (Array ℕ)} (hok : gs.all okA = true) {x : GJ}
    {t : Array ℕ} (hx : Rep 315 t x.1) (hc : gs.all (fun u => commA u t) = true) :
    subOf gs ≤ centralizer ({x} : Set GJ) := by
  intro g hg
  have hle : Subgroup.closure (permsA 315 gs) ≤
      Subgroup.centralizer ({x.1} : Set (Equiv.Perm (Fin 315))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hv := (okA_all_spec hok k hk).1
    exact (eqA_iff (rep_compA (rep_of_validA hv) hx) (rep_compA hx (rep_of_validA hv))).1
      (all_spec hc k hk)
  have := mem_centralizer_singleton_iff.1 (hle (mem_subOf.1 hg))
  exact mem_centralizer_singleton_iff.2 (Subtype.ext this)

theorem brute_spec (g : GJ) :
    ∃ t, Rep 315 t g.1 ∧ brutePr (c5a ()) (c5c ()) (c7 ()) (cE ()) t = true :=
  exists_rep_of_check ks155_parts.2.2.1 g

theorem brute_cases {t : Array ℕ} (h : brutePr (c5a ()) (c5c ()) (c7 ()) (cE ()) t = true) :
    (commA t x5aA = true → inCert (c5a ()) t = true) ∧
      (commA t x5cA = true → inCert (c5c ()) t = true) ∧
      (commA t x7A = true → inCert (c7 ()) t = true) ∧
      (commA t e1A = true → commA t e2A = true → inCert (cE ()) t = true) := by
  unfold brutePr at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc hc' => ?_⟩
  · rcases h1 with h1 | h1
    · rw [hc] at h1; exact absurd h1 (by decide)
    · exact h1
  · rcases h2 with h2 | h2
    · rw [hc] at h2; exact absurd h2 (by decide)
    · exact h2
  · rcases h3 with h3 | h3
    · rw [hc] at h3; exact absurd h3 (by decide)
    · exact h3
  · rcases h4 with h4 | h4
    · simp only [Bool.and_eq_false_iff] at h4
      rcases h4 with h4 | h4
      · rw [hc] at h4; exact absurd h4 (by decide)
      · rw [hc'] at h4; exact absurd h4 (by decide)
    · exact h4

theorem centralizer_x5a : centralizer ({x5aJ} : Set GJ) = subOf gC5a := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t, ht, hpr⟩ := brute_spec g
    exact mem_of_inCert enums_parts.1 ht ((brute_cases hpr).1
      (commA_of_commute ht rep_x5a (mem_centralizer_singleton_iff.1 hg)))
  · exact subOf_le_centralizer elts_parts.2.2.2.2.2.2.1 rep_x5a
      enums_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_centralizer_x5a : Nat.card (centralizer ({x5aJ} : Set GJ)) = 300 := by
  rw [centralizer_x5a, card_subOf (by decide) enums_parts.1
    (okA_all_spec elts_parts.2.2.2.2.2.2.1), enums_parts.2.1]

theorem centralizer_x5c : centralizer ({x5cJ} : Set GJ) = subOf gC5c := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t, ht, hpr⟩ := brute_spec g
    exact mem_of_inCert enums_parts.2.2.1 ht ((brute_cases hpr).2.1
      (commA_of_commute ht rep_x5c (mem_centralizer_singleton_iff.1 hg)))
  · exact subOf_le_centralizer elts_parts.2.2.2.2.2.2.2.1 rep_x5c
      enums_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_centralizer_x5c : Nat.card (centralizer ({x5cJ} : Set GJ)) = 50 := by
  rw [centralizer_x5c, card_subOf (by decide) enums_parts.2.2.1
    (okA_all_spec elts_parts.2.2.2.2.2.2.2.1), enums_parts.2.2.2.1]

theorem gC7_all_okA : gC7.all okA = true := by
  rw [gC7, Array.all_eq_true]
  intro i hi
  have : i = 0 := by simpa using hi
  subst this
  exact elts_parts.1

theorem card_centralizer_x7_le : Nat.card (centralizer ({x7J} : Set GJ)) ≤ 7 := by
  have hle : centralizer ({x7J} : Set GJ) ≤ subOf gC7 := by
    intro g hg
    obtain ⟨t, ht, hpr⟩ := brute_spec g
    exact mem_of_inCert enums_parts.2.2.2.2.1 ht ((brute_cases hpr).2.2.1
      (commA_of_commute ht rep_x7 (mem_centralizer_singleton_iff.1 hg)))
  calc Nat.card (centralizer ({x7J} : Set GJ)) ≤ Nat.card (subOf gC7) := Subgroup.card_le_of_le hle
    _ = 7 := by
      rw [card_subOf (by decide) enums_parts.2.2.2.2.1 (okA_all_spec gC7_all_okA),
        enums_parts.2.2.2.2.2.1]

theorem centralizer_E0 : centralizer ({e1J, e2J} : Set GJ) = subOf gCE := by
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_iff] at hg
    obtain ⟨t, ht, hpr⟩ := brute_spec g
    exact mem_of_inCert enums_parts.2.2.2.2.2.2.1 ht ((brute_cases hpr).2.2.2
      (commA_of_commute ht rep_e1 (hg e1J (by simp)).symm)
      (commA_of_commute ht rep_e2 (hg e2J (by simp)).symm))
  · intro g hg
    have hc := enums_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h1 : gCE.all (fun u => commA u e1A) = true := by
      rw [Array.all_eq_true] at hc ⊢
      intro i hi
      have := hc i hi
      simp only [Bool.and_eq_true] at this
      exact this.1
    have h2 : gCE.all (fun u => commA u e2A) = true := by
      rw [Array.all_eq_true] at hc ⊢
      intro i hi
      have := hc i hi
      simp only [Bool.and_eq_true] at this
      exact this.2
    have g1 := mem_centralizer_singleton_iff.1
      (subOf_le_centralizer elts_parts.2.2.2.2.2.2.2.2.1 rep_e1 h1 hg)
    have g2 := mem_centralizer_singleton_iff.1
      (subOf_le_centralizer elts_parts.2.2.2.2.2.2.2.2.1 rep_e2 h2 hg)
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · exact g1.symm
    · rw [Set.mem_singleton_iff.1 hh]; exact g2.symm

theorem card_centralizer_E0 : Nat.card (centralizer ({e1J, e2J} : Set GJ)) = 240 := by
  rw [centralizer_E0, card_subOf (by decide) enums_parts.2.2.2.2.2.2.1
    (okA_all_spec elts_parts.2.2.2.2.2.2.2.2.1), enums_parts.2.2.2.2.2.2.2.1]

end Cent

theorem centralizer_zpow_eq_of_ne_one {G : Type*} [Group G] {x : G} (hp : (orderOf x).Prime)
    {n : ℤ} (hn : x ^ n ≠ 1) : centralizer ({x ^ n} : Set G) = centralizer ({x} : Set G) := by
  have hg : n.gcd (orderOf x) = 1 := by
    rcases Nat.coprime_or_dvd_of_prime hp n.natAbs with h | h
    · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.Coprime.gcd_eq_one h.symm
    · exfalso
      apply hn
      obtain ⟨m, hm⟩ := h
      have : (orderOf x : ℤ) ∣ n := by
        rw [← Int.natAbs_dvd_natAbs]
        exact ⟨m, by simpa using hm⟩
      exact orderOf_dvd_iff_zpow_eq_one.1 this
  apply le_antisymm
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (mem_zpowers_zpow_iff.2 hg)
    have h1 : Commute c ((x ^ n) ^ m) := (show Commute c (x ^ n) from hc).zpow_right m
    rw [hm] at h1
    exact h1.eq
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    exact ((show Commute c x from hc).zpow_right n).eq

section Lines

@[expose] noncomputable def S5 : Subgroup GJ := subOf gS5

theorem gS5_all_okA : gS5.all okA = true := by
  rw [gS5, Array.all_eq_true]
  intro i hi
  have hi2 : i < 2 := by simpa using hi
  interval_cases i
  · exact elts_parts.2.1
  · exact elts_parts.2.2.2.1

theorem card_S5 : Nat.card S5 = 5 ^ 2 := by
  rw [S5, card_subOf (by decide) enums_parts.2.2.2.2.2.2.2.2.2.2.1 (okA_all_spec gS5_all_okA),
    enums_parts.2.2.2.2.2.2.2.2.2.2.2.1]
  norm_num

theorem exists_line {s : GJ} (hs : s ∈ S5) (hs1 : s ≠ 1) : ∃ j < 6, ∃ e < 5, s = lineJ j ^ e := by
  obtain ⟨i, hi, hrep⟩ := exists_rep_subOf (by decide) enums_parts.2.2.2.2.2.2.2.2.2.2.1 hs
  rcases lines_parts.1 i hi with h | ⟨j, hj, e, he, hje⟩
  · exact absurd (eq_of_rep hrep rep_one h) hs1
  · exact ⟨j, hj, e, he, eq_of_rep hrep (rep_pow (rep_lineJ hj) e) hje⟩

theorem line_conj {j : ℕ} (hj : j < 6) :
    transJ j * caseJ (recL.getD j 0) * (transJ j)⁻¹ = lineJ j := by
  have h := lines_parts.2.2.2.2 j hj
  exact eq_of_rep (rep_conj (rep_transJ hj) (valid_transA hj) (rep_caseJ h.2.1)) (rep_lineJ hj)
    h.2.2

theorem exists_conj_case {g : GJ} (hg : orderOf g = 5) :
    ∃ k : GJ, ∃ c < 2, ∃ e : ℕ, 0 < e ∧ e < 5 ∧ g = k * caseJ c ^ e * k⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, hh⟩ := NormalizerAction.exists_conj_mem_of_orderOf_prime 5 2 S5 card_S5
    (by rw [card_GJ]; norm_num) hg
  have hne : h⁻¹ * g * h ≠ 1 := by
    intro h1
    have hg1 : g = 1 := by
      have : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
      rw [this, h1]
      group
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  obtain ⟨j, hj, e, he, hje⟩ := exists_line hh hne
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · rw [pow_zero] at hje
      exact absurd hje hne
    · exact h0
  refine ⟨h * transJ j, recL.getD j 0, (lines_parts.2.2.2.2 j hj).2.1, e, he0, he, ?_⟩
  calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    _ = h * lineJ j ^ e * h⁻¹ := by rw [hje]
    _ = h * (transJ j * caseJ (recL.getD j 0) * (transJ j)⁻¹) ^ e * h⁻¹ := by
        rw [line_conj hj]
    _ = h * transJ j * caseJ (recL.getD j 0) ^ e * (h * transJ j)⁻¹ := by
        rw [conj_pow]
        group

theorem orderOf_caseJ {c : ℕ} (hc : c < 2) : orderOf (caseJ c) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  interval_cases c
  · exact orderOf_eq_prime x5a_pow (ne_of_eqA_false rep_x5a rep_one
      elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact orderOf_eq_prime x5c_pow (ne_of_eqA_false rep_x5c rep_one
      elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem centralizer_caseJ_pow {c : ℕ} (hc : c < 2) {e : ℕ} (he0 : 0 < e) (he : e < 5) :
    centralizer ({caseJ c ^ e} : Set GJ) = centralizer ({caseJ c} : Set GJ) := by
  have ho := orderOf_caseJ hc
  have hne : caseJ c ^ (e : ℤ) ≠ 1 := by
    rw [zpow_natCast]
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    exact absurd (Nat.le_of_dvd he0 this) (by omega)
  have := centralizer_zpow_eq_of_ne_one (by rw [ho]; norm_num) hne
  rwa [zpow_natCast] at this

theorem card_centralizer_le_of_orderOf_seven {g : GJ} (hg : orderOf g = 7) :
    Nat.card (centralizer ({g} : Set GJ)) ≤ 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho7 : orderOf x7J = 7 := orderOf_eq_prime x7_pow x7_ne_one
  have hQ : Nat.card (zpowers x7J) = 7 ^ 1 := by rw [Nat.card_zpowers, ho7, pow_one]
  obtain ⟨h, hh⟩ := NormalizerAction.exists_conj_mem_of_orderOf_prime 7 1 (zpowers x7J) hQ
    (by rw [card_GJ]; norm_num) hg
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hh
  set y := h⁻¹ * g * h with hydef
  have hy : h * y * h⁻¹ = g := by rw [hydef]; group
  have hne : x7J ^ n ≠ 1 := by
    rw [hn]
    intro h1
    have hg1 : g = 1 := by rw [← hy, h1]; group
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hC := centralizer_zpow_eq_of_ne_one (by rw [ho7]; norm_num) hne
  rw [hn] at hC
  have e1 := Nat.card_congr (KS219.centralizerConjEquiv h y).toEquiv
  rw [hy] at e1
  rw [e1, hC]
  exact card_centralizer_x7_le

end Lines

section D

@[expose] noncomputable def E0 : Subgroup GJ := kleinSub e1_sq e2_sq e1_comm_e2

theorem card_E0 : Nat.card E0 = 4 := by
  classical
  have h1 := e1_ne_one
  have h2 := e2_ne_one
  have h3 := e1_ne_e2
  have h4 : e1J * e2J ≠ 1 := fun h => h3 (by
    have : e2J = e1J⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right e1_sq])
  have h5 : e1J * e2J ≠ e1J := fun h => h2 (by simpa using h)
  have h6 : e1J * e2J ≠ e2J := fun h => h1 (by simpa using h)
  have e : ((E0 : Subgroup GJ) : Set GJ) = ↑({1, e1J, e2J, e1J * e2J} : Finset GJ) := by
    ext x
    rw [E0, SetLike.mem_coe, mem_kleinSub]
    simp
  change Nat.card ((E0 : Subgroup GJ) : Set GJ) = 4
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  all_goals simp [h3, h1.symm, h2.symm, h4.symm, h5.symm, h6.symm]

theorem centralizer_E0_eq : centralizer (E0 : Set GJ) = centralizer ({e1J, e2J} : Set GJ) := by
  ext g
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    apply h
    rcases hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff.1 hx]
      exact Or.inr (Or.inr (Or.inl rfl))
  · intro h x hx
    have c1 := h e1J (by simp)
    have c2 := h e2J (by simp)
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact c1
    · exact c2
    · rw [mul_assoc, c2, ← mul_assoc, c1, mul_assoc]

theorem E0_le_centralizer_x5a : E0 ≤ centralizer ({x5aJ} : Set GJ) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact e1_comm_x5a.eq
  · exact e2_comm_x5a.eq
  · exact (e1_comm_x5a.mul_left e2_comm_x5a).eq

@[expose] noncomputable def DJ : Subgroup GJ := subOf gD

theorem card_DJ : Nat.card DJ = 60 := by
  rw [DJ, card_subOf (by decide) enums_parts.2.2.2.2.2.2.2.2.1
    (okA_all_spec elts_parts.2.2.2.2.2.2.2.2.2.1), enums_parts.2.2.2.2.2.2.2.2.2.1]

theorem DJ_le : DJ ≤ centralizer (E0 : Set GJ) := by
  rw [centralizer_E0_eq, centralizer_E0, DJ, subOf_eq_closure_gElt gD
    (okA_all_spec elts_parts.2.2.2.2.2.2.2.2.2.1), closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_of_inCert enums_parts.2.2.2.2.2.2.1 (rep_elA _) (all_spec d_parts.1 k hk)

theorem DJ_perfect : Group.IsPerfect DJ := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact DJ.mul_mem (DJ.mul_mem (DJ.mul_mem ha hb) (DJ.inv_mem ha)) (DJ.inv_mem hb)
  · have hcl := subOf_eq_closure_gElt gD (okA_all_spec elts_parts.2.2.2.2.2.2.2.2.2.1)
    calc DJ = _ := hcl
      _ ≤ ⁅DJ, DJ⁆ := by
        rw [closure_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨hu, hv, he⟩ := d_parts.2.2.2.1 k hk
        have hku : k < dUA.size := by rw [d_parts.2.1]; exact hk
        have hkv : k < dVA.size := by rw [d_parts.2.2.1]; exact hk
        have oku := all_spec elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.1 k hku
        have okv := all_spec elts_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hkv
        have huD : eltOf dUA[k]! oku ∈ DJ :=
          mem_of_inCert enums_parts.2.2.2.2.2.2.2.2.1 (rep_eltOf oku) hu
        have hvD : eltOf dVA[k]! okv ∈ DJ :=
          mem_of_inCert enums_parts.2.2.2.2.2.2.2.2.1 (rep_eltOf okv) hv
        have hrep : Rep 315 (commutatorA 315 dUA[k]! dVA[k]!)
            (⁅eltOf dUA[k]! oku, eltOf dVA[k]! okv⁆ : GJ).1 := by
          have := rep_commutatorA (n := 315) (okA_spec oku).1 (okA_spec okv).1
          have hu1 : ((eltOf dUA[k]! oku : GJ) : Equiv.Perm (Fin 315)) = permOfArr 315 dUA[k]! :=
            rfl
          have hv1 : ((eltOf dVA[k]! okv : GJ) : Equiv.Perm (Fin 315)) = permOfArr 315 dVA[k]! :=
            rfl
          rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv, Subgroup.coe_inv, hu1, hv1]
          rwa [commutatorElement_def] at this
        have heq : gElt gD (okA_all_spec elts_parts.2.2.2.2.2.2.2.2.2.1) k hk =
            ⁅eltOf dUA[k]! oku, eltOf dVA[k]! okv⁆ :=
          eq_of_rep (rep_elA _) hrep he
        rw [SetLike.mem_coe, heq]
        exact Subgroup.commutator_mem_commutator huD hvD

theorem disjoint_E0_DJ : Disjoint E0 DJ := by
  rw [Subgroup.disjoint_def]
  intro x hx hxD
  rcases hx with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (inCert_of_mem enums_parts.2.2.2.2.2.2.2.2.1 rep_e1 hxD)
      (by rw [d_parts.2.2.2.2.1]; decide)
  · exact absurd (inCert_of_mem enums_parts.2.2.2.2.2.2.2.2.1 rep_e2 hxD)
      (by rw [d_parts.2.2.2.2.2.1]; decide)
  · exact absurd (inCert_of_mem enums_parts.2.2.2.2.2.2.2.2.1 (rep_mul rep_e1 rep_e2) hxD)
      (by rw [d_parts.2.2.2.2.2.2]; decide)

end D

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
