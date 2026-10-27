module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem isSubnormal_bot_or_eq {Y : Type} [Group Y] {A K : Subgroup Y} (h : IsSubnormal A K) :
    IsSimpleGroup ↥K → A = ⊥ ∨ A = K := by
  induction h with
  | refl H => intro _; exact Or.inr rfl
  | @step H M K' hHM hn hMK ih =>
    intro hK'
    rcases ih hK' with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hHM))
    · subst hM
      haveI := hK'
      rcases Subgroup.Normal.eq_bot_or_eq_top (H.subgroupOf M) with h1 | h1
      · left
        ext x
        constructor
        · intro hx
          have hx' : (⟨x, hHM hx⟩ : ↥M) ∈ H.subgroupOf M := Subgroup.mem_subgroupOf.2 hx
          rw [h1, Subgroup.mem_bot] at hx'
          exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
        · intro hx
          rw [Subgroup.mem_bot] at hx
          rw [hx]
          exact H.one_mem
      · right
        exact le_antisymm hHM (Subgroup.subgroupOf_eq_top.1 h1)

theorem nontrivial_of_isQuasisimple {G : Type} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    Nontrivial G := by
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := h.2
  exact Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center G))

theorem nontrivial_of_quotient {G : Type} [Group G] (N : Subgroup G) [Nontrivial (G ⧸ N)] :
    Nontrivial G :=
  Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := N))

theorem not_nontrivial_bot {Y : Type} [Group Y] : ¬ Nontrivial ↥(⊥ : Subgroup Y) := by
  intro _
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(⊥ : Subgroup Y)
  exact hxy (Subtype.ext ((Subgroup.mem_bot.1 x.2).trans (Subgroup.mem_bot.1 y.2).symm))

theorem card_psl2_ne_360 {F : Type} [Field F] [Finite F] (hF : 10 ≤ Nat.card F) :
    Nat.card (StatedProj (StatedSL 2 F)) ≠ 360 := by
  intro h
  have key := CFSG.HardMathSupport.Solomon.Coordinator.l514c_card_psl2 (F := F)
  rw [h] at key
  have hg : Nat.gcd 2 (Nat.card F - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h100 : 100 ≤ Nat.card F ^ 2 := by nlinarith
  have hq2 : 99 ≤ Nat.card F ^ 2 - 1 := by omega
  have hbig : 10 * 99 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul hF hq2
  linarith

theorem not_comp_of_solvable {Y : Type} [Group Y] [Finite Y] {X A : Subgroup Y}
    (hX : Group.IsSolvable ↥X) (hA : CFSG.Open.GLAPComponent 3 X A) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hAX : A ≤ X := hA.1
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hAX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAX).surjective
  have hQ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hA
  haveI := nontrivial_of_isQuasisimple hQ
  have hlt : commutator (PQuot 3 A) < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot 3 A)
  exact absurd hQ.1 (ne_of_lt hlt)

theorem card_of_isA6 (i : TauCeti.CFSGIndex) (hi : CFSG.LocalAnalysis.GLTheoremA.S8.isA6 i) :
    Nat.card i.Group = 360 := by
  cases i with
  | cyclic p hp => rcases hi with h | h <;> exact (show False from h).elim
  | alternating n hn =>
    rcases hi with h | h
    · have h6 : n = 6 := h
      subst h6
      show Nat.card (alternatingGroup (Fin 6)) = 360
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    · exact (show False from h).elim
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    rcases hi with h | h
    · exact (show False from h).elim
    · cases d with
      | A r q =>
        rcases r with _ | _ | r
        · exact (show False from h).elim
        · have hq9c : q.card = 9 := h
          have hq9 : q.p ^ q.exponent = 9 := (TauCeti.PrimePower.card_def q).symm.trans hq9c
          haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
          have hexp : q.exponent ≠ 0 := q.exponent_pos.ne'
          have hF : Nat.card (GaloisField q.p q.exponent) = 9 := by
            rw [GaloisField.card q.p q.exponent hexp]
            exact hq9
          have h360 := CFSG.HardMathSupport.Solomon.Coordinator.l514c_card_psl2
            (F := GaloisField q.p q.exponent)
          rw [hF] at h360
          refine (Nat.card_congr ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
              (GaloisField q.p q.exponent))).toEquiv).trans ?_
          norm_num at h360
          omega
        · exact (show False from h).elim
      | _ => exact (show False from h).elim
  | sporadic s => rcases hi with h | h <;> exact (show False from h).elim

theorem catalogIs_three18 {S : Type} [Group S] [Finite S]
    (h : catalogIs S CFSG.LocalAnalysis.GLTheoremA.H1431c.isL2three18) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ^ 18 ∧
      Nonempty (S ≃* StatedProj (StatedSL 2 F)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact (show False from hi).elim
  | sporadic s => exact (show False from hi).elim
  | alternating k hk => exact (show False from hi).elim
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact (show False from hi).elim
      · have hqc : q.card = 3 ^ 18 := hi
        have hq : q.p ^ q.exponent = 3 ^ 18 := (TauCeti.PrimePower.card_def q).symm.trans hqc
        haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
        have hexp : q.exponent ≠ 0 := q.exponent_pos.ne'
        refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, ?_,
          ⟨e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
              (GaloisField q.p q.exponent)))⟩⟩
        rw [GaloisField.card q.p q.exponent hexp]
        exact hq
      · exact (show False from hi).elim
    | _ => exact (show False from hi).elim

theorem isPGroup_center_of_glaPPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : CFSG.Open.GLAPPrimeCore 3 Y = ⊥) : IsPGroup 3 ↥(Subgroup.center Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card ↥(Subgroup.center Y)).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_
  intro d hd hdvd
  by_contra hd3
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hwc : (w : Y) ∈ Subgroup.center Y := w.2
  have hN : Subgroup.zpowers (w : Y) ≤ Subgroup.center Y := Subgroup.zpowers_le.2 hwc
  haveI hNn : (Subgroup.zpowers (w : Y)).Normal := Subgroup.normal_of_le_center hN
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers (w : Y))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
    exact (Nat.coprime_primes Nat.prime_three hd).2 (Ne.symm hd3)
  have hmem : Subgroup.zpowers (w : Y) ∈ {K : Subgroup Y | K.Normal ∧ Nat.Coprime 3 (Nat.card K)} :=
    ⟨hNn, hcop⟩
  have hle : Subgroup.zpowers (w : Y) ≤ CFSG.Open.GLAPPrimeCore 3 Y := le_sSup hmem
  rw [hO] at hle
  have hw1 : (w : Y) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have hd1 : d = 1 := by
    rw [← hw, ← Subgroup.orderOf_coe, hw1, orderOf_one]
  exact hd.one_lt.ne' hd1

theorem not_comp_A6_of_simple {Y : Type} [Group Y] [Finite Y] {X A : Subgroup Y} {F₀ : Type}
    [Field F₀] [Finite F₀] {k : ℕ} (hk : 3 ≤ k) (hF₀ : Nat.card F₀ = 3 ^ k)
    (e : ↥X ≃* StatedProj (StatedSL 2 F₀)) (hA : CFSG.Open.GLAPComponent 3 X A) :
    ¬ catalogIs (PSimple 3 A) CFSG.LocalAnalysis.GLTheoremA.S8.isA6 := by
  intro hcat
  have hp : Nat.Prime 3 := Nat.prime_three
  have h27 : 27 ≤ Nat.card F₀ := by
    rw [hF₀]
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hW : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F₀).isSimpleGroup_congr.1
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  haveI hX : IsSimpleGroup ↥X := e.isSimpleGroup
  have hcardW : Nat.card ↥X = Nat.card (StatedProj (StatedSL 2 F₀)) := Nat.card_congr e.toEquiv
  have h3X : 3 ∣ Nat.card ↥X := by
    have key := CFSG.HardMathSupport.Solomon.Coordinator.l514c_card_psl2 (F := F₀)
    have h3q : 3 ∣ Nat.card F₀ := by
      rw [hF₀]
      exact dvd_pow_self 3 (by omega)
    have h3prod : 3 ∣ Nat.card (StatedProj (StatedSL 2 F₀)) * Nat.gcd 2 (Nat.card F₀ - 1) := by
      rw [key]
      exact Dvd.dvd.mul_right h3q _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3prod with h | h
    · rw [hcardW]
      exact h
    · exfalso
      have h32 : 3 ∣ 2 := dvd_trans h (Nat.gcd_dvd_left _ _)
      norm_num at h32
  have hO3 : CFSG.Open.GLAPPrimeCore 3 ↥X = ⊥ := by
    unfold CFSG.Open.GLAPPrimeCore CFSG.pPrimeCore
    refine eq_bot_iff.2 (sSup_le ?_)
    rintro K ⟨hK, hcop⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top K with h | h
    · exact le_of_eq h
    · exfalso
      rw [h, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ↥X) ≃* ↥X).toEquiv] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3X
  have hQ0 := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hA
  rcases isSubnormal_bot_or_eq hA.2.1 hX with hbot | htop
  · exfalso
    rw [hbot] at hQ0
    haveI := nontrivial_of_isQuasisimple hQ0
    exact not_nontrivial_bot (nontrivial_of_quotient (CFSG.Open.GLAPPrimeCore 3 ↥(⊥ : Subgroup Y)))
  · rw [htop] at hQ0 hcat
    have eQ : PQuot 3 X ≃* ↥X :=
      (QuotientGroup.quotientMulEquivOfEq hO3).trans QuotientGroup.quotientBot
    haveI hSQ : IsSimpleGroup (PQuot 3 X) := eQ.isSimpleGroup
    have hcz : Subgroup.center (PQuot 3 X) = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (PQuot 3 X)) with h | h
      · exact h
      · exfalso
        haveI := hQ0.2
        obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 X ⧸ Subgroup.center (PQuot 3 X))
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        apply hab
        rw [QuotientGroup.eq, h]
        exact Subgroup.mem_top _
    have hnum : Nat.card (PSimple 3 X) = Nat.card ↥X := by
      have h1 : Nat.card (PQuot 3 X ⧸ Subgroup.center (PQuot 3 X)) =
          (Subgroup.center (PQuot 3 X)).index := rfl
      show Nat.card (PQuot 3 X ⧸ Subgroup.center (PQuot 3 X)) = Nat.card ↥X
      rw [h1, hcz, Subgroup.index_bot, Nat.card_congr eQ.toEquiv]
    obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    have h360 : Nat.card i.Group = 360 := card_of_isA6 i hi
    have hPS : Nat.card (PSimple 3 X) = Nat.card i.Group := Nat.card_congr f.toEquiv
    have hW360 : Nat.card (StatedProj (StatedSL 2 F₀)) = 360 := by
      rw [← hcardW, ← hnum, hPS, h360]
    exact card_psl2_ne_360 (by omega) hW360

end CFSG.LocalAnalysis.GLTheoremA.SFM5

end
