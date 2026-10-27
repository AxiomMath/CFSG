module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLinRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniBound
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure P3Hyp (q : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) : Prop where
  prime : q.Prime
  two : q ≠ 2
  three : q ≠ 3
  kGroup : CFSG.Open.IsKGroup Ω
  normal : S.Normal
  perfect : ⁅S, S⁆ = S
  core : GLAPPrimeCore 3 ↥S = ⊥
  chev : IsChevSimple q (PSimple 3 S)
  elem : IsElemAbelian 3 B
  sup : S ⊔ B = ⊤
  twoLocal : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B
  card : Nat.card B = 3 ^ 4
  cent : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3

@[expose] def P3Closed (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ Q, d = .A 1 Q) ∨ (∃ Q, d = .A 2 Q) ∨ (∃ Q, d = .twistedA 2 Q) ∨
    d.characteristic = 2 ∨ d.characteristic = 3

@[expose] def P3At (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), P3Hyp q S B →
    d.1.characteristic = q → Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    S267ConcA 3 S B ∨ S267ConcBCDE 3 q S B

theorem P3Hyp.exists_cube {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) :
    ∃ E : Subgroup (MulAut (PSimple 3 S)), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_le_card_inf_centMod_mul_pow Nat.prime_three H.normal H.perfect H.elem
  rw [H.card, H.cent] at h
  set m := CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 S))) with hm
  have h3 : 3 ≤ m := by
    by_contra hlt
    have h9 : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := h.trans (Nat.mul_le_mul_left 3 h9)
    norm_num at this
  obtain ⟨E₀, -, hE₀, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (MulAut (PSimple 3 S)))
  obtain ⟨E, -, hE, hEc⟩ := exists_le_isElemAbelian_card hE₀ (n := 3)
    (by rw [hcard]; exact pow_dvd_pow 3 h3)
  exact ⟨E, hE, hEc⟩

private theorem isElemAbelian_map_three {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {E : Subgroup X} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    apply Subtype.ext
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem exists_cube_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ E : Subgroup (MulAut X), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) :
    ∃ E : Subgroup (MulAut Y), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  obtain ⟨E, hE, hEc⟩ := h
  refine ⟨E.map (MulAut.congr e).toMonoidHom, isElemAbelian_map_three _ hE, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hEc]

private theorem three_ne_zero_galois {ℓ n : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) :
    ((3 : ℕ) : GaloisField ℓ n) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (GaloisField ℓ n) ℓ]
  intro h
  exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 h)

theorem no_cube_A1 (Q : TauCeti.PrimePower) (hQ3 : Q.p ≠ 3)
    (hv : (TauCeti.LieTypeIndex.A 1 Q).Valid) :
    ¬ ∃ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  intro h
  obtain ⟨E, hE, hEc⟩ :=
    exists_cube_of_mulEquiv (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv) h
  haveI : NeZero ((3 : ℕ) : GaloisField Q.p Q.exponent) := ⟨three_ne_zero_galois hQ3⟩
  exact CFSG.RankThree.PartOne.K133.noRankThree_psl2 (K := GaloisField Q.p Q.exponent)
    Nat.prime_three (by norm_num)
    ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE, hEc⟩

theorem no_cube_A2 (Q : TauCeti.PrimePower) (hQ3 : Q.p ≠ 3) (hQ : ¬ 3 ∣ Q.card - 1)
    (hv : (TauCeti.LieTypeIndex.A 2 Q).Valid) :
    ¬ ∃ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  intro h
  obtain ⟨E, hE, hEc⟩ := exists_cube_of_mulEquiv
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField Q.p Q.exponent))) h
  obtain ⟨-, hdvd, -⟩ := CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin.cube_facts Nat.prime_three
    (by norm_num) (three_ne_zero_galois hQ3) hE hEc
  apply hQ
  rwa [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', ← TauCeti.PrimePower.card_def] at hdvd

theorem no_cube_twistedA2 (Q : TauCeti.PrimePower) (hQ2 : Q.p ≠ 2) (hQ3 : Q.p ≠ 3)
    (hQ : ¬ 3 ∣ Q.card + 1) (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid) :
    ¬ ∃ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩).Group),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  intro h
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.exists_mulEquiv_PU
    (Q := Q) (S := (TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩).Group)
    ⟨.lie ⟨.twistedA 2 Q, hv⟩, rfl, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨E, hE, hEc⟩ := exists_cube_of_mulEquiv e h
  have h1 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker
    (CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.fieldFactor hK hQ2) E
  rw [CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.ker_fieldFactor, hEc] at h1
  have h2 := CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.card_map_fieldFactor_le hK hQ2
    Nat.prime_three hE
  have h3 : 3 ^ 2 ≤ Nat.card ↥(E ⊓ CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.innDiag hK) := by
    by_contra hlt
    have : Nat.card ↥(E ⊓ CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.innDiag hK) ≤ 8 := by omega
    have := Nat.mul_le_mul h2 this
    omega
  apply hQ
  rw [TauCeti.PrimePower.card_def]
  exact CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni.dvd_add_one_of_le_card_inf_innDiag hK hQ2
    Nat.prime_three (by norm_num) (Ne.symm hQ3) hE h3

theorem pRank_mulAut_alt5_le :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (alternatingGroup (Fin 5)))) ≤ 1 := by
  have hZ : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer Nat.prime_three
    hZ).trans ?_
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ 1 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 1 fun hd => ?_
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hd
    exact absurd hd (by decide)
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Outer (alternatingGroup (Fin 5)))) ≤ 0 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0 fun hd => ?_
    have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four 5 le_rfl
    have := hd.trans h4
    norm_num at this
  omega

theorem no_cube_alt5 :
    ¬ ∃ E : Subgroup (MulAut (alternatingGroup (Fin 5))), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  rintro ⟨E, hE, hEc⟩
  have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE hEc
  have := pRank_mulAut_alt5_le
  omega

theorem concB_of_A2 {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.A 2 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group) (h3 : 3 ∣ Q.card - 1) :
    S267ConcBCDE 3 q S B :=
  Or.inl ⟨H.card, rfl, Q, hQq, Or.inl ⟨⟨.lie ⟨.A 2 Q, hv⟩, rfl, ⟨e⟩⟩, h3⟩⟩

theorem concB_of_twistedA2 {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩).Group)
    (h3 : 3 ∣ Q.card + 1) :
    S267ConcBCDE 3 q S B :=
  Or.inl ⟨H.card, rfl, Q, hQq, Or.inr ⟨⟨.lie ⟨.twistedA 2 Q, hv⟩, rfl, ⟨e⟩⟩, h3⟩⟩

private theorem ambiguousChev_lie {r : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : ambiguousChev r (TauCeti.CFSGIndex.lie d)) : r = 2 ∨ r = 3 := by
  obtain ⟨lt, hv⟩ := d
  simp only [ambiguousChev] at h
  split at h
  · rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  · rcases h with ⟨-, h⟩ <;> simp [h]
  · rcases h with ⟨-, h⟩ <;> simp [h]
  · exact absurd h (by simp)

theorem s267FactP3_of_open (h : ∀ d : TauCeti.ValidLieTypeIndex, ¬ P3Closed d.1 → P3At d) :
    S267FactP3 := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hS hperf hcore hchev hB hSB hm2 _ hBC hp3 hB81
  subst hp3
  have H : P3Hyp q S B :=
    ⟨hq, hq2, hqp, hK, hS, hperf, hcore, hchev, hB, hSB, hm2, hB81, hBC⟩
  have hcube := H.exists_cube
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with _ | _ | d | _
    · exact absurd hi id
    · exact absurd hi id
    swap
    · exact absurd hi id
    change d.1.characteristic = q at hi
    by_cases hcl : P3Closed d.1
    · obtain ⟨d, hv⟩ := d
      rcases hcl with ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | hc | hc
      · subst hQ
        have hi' : Q.p = q := by simpa using hi
        exact absurd (exists_cube_of_mulEquiv e hcube) (no_cube_A1 Q (by rw [hi']; exact hqp) hv)
      · subst hQ
        have hi' : Q.p = q := by simpa using hi
        by_cases h3 : 3 ∣ Q.card - 1
        · exact Or.inr (concB_of_A2 H hi' hv e h3)
        · exact absurd (exists_cube_of_mulEquiv e hcube)
            (no_cube_A2 Q (by rw [hi']; exact hqp) h3 hv)
      · subst hQ
        have hi' : Q.p = q := by simpa using hi
        by_cases h3 : 3 ∣ Q.card + 1
        · exact Or.inr (concB_of_twistedA2 H hi' hv e h3)
        · exact absurd (exists_cube_of_mulEquiv e hcube)
            (no_cube_twistedA2 Q (by rw [hi']; exact hq2) (by rw [hi']; exact hqp) h3 hv)
      · exact absurd (hi.symm.trans hc) hq2
      · exact absurd (hi.symm.trans hc) hqp
    · exact h d hcl q Ω S B H hi ⟨e⟩
  · rcases i with _ | ⟨n, hn⟩ | d | _
    · exact absurd hi id
    · have hn5 : n = 5 := by
        simp only [ambiguousChev] at hi
        omega
      subst hn5
      exact absurd (exists_cube_of_mulEquiv e hcube) no_cube_alt5
    · rcases ambiguousChev_lie hi with h2 | h3
      · exact absurd h2 hq2
      · exact absurd h3 hqp
    · exact absurd hi id

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
