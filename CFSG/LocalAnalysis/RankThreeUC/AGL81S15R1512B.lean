module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterScalars
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

section CentreOfLift

variable {X : Type} [Group X] [Finite X]

theorem center_comap_eq_of_central_ext {K S : Type*} [Group K] [Group S]
    (hK : commutator K = ⊤) (f : K →* S) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center K) : (Subgroup.center S).comap f = Subgroup.center K := by
  haveI : Group.IsPerfect K := ⟨hK⟩
  exact CFSG.Wreathed.DegreeThreeModelFullCenter.center_comap_eq_of_perfect_image (MonoidHom.id K) f hf hker
    (Subgroup.center K) le_rfl (fun g hg => Subgroup.mem_center_iff.2 fun x => (hg x).symm.eq)

theorem quotCenter_mulEquiv_of_central_ext {K S : Type*} [Group K] [Group S]
    (hK : commutator K = ⊤) (f : K →* S) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center K) :
    Nonempty ((K ⧸ Subgroup.center K) ≃* (S ⧸ Subgroup.center S)) := by
  have hc := center_comap_eq_of_central_ext hK f hf hker
  have hs : Function.Surjective ((QuotientGroup.mk' (Subgroup.center S)).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hk : ((QuotientGroup.mk' (Subgroup.center S)).comp f).ker = Subgroup.center K := by
    rw [← hc, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)⟩

theorem barO2_centralExt {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) :
    ∃ f : ↥(barO2 L) →* ↥Ls, Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥(barO2 L) := by
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφ : ∀ A : Subgroup X, (barO2 A).map φ = A.map (toStar T) := by
    intro A
    unfold barO2
    rw [Subgroup.map_map]
    congr 1
  have hφmk : ∀ x : X, φ (QuotientGroup.mk' (CFSG.pCore 2 X) x) = toStar T x := fun x => rfl
  let f : ↥(barO2 L) →* ↥Ls := (φ.comp (barO2 L).subtype).codRestrict Ls (by
    intro k
    have h : φ k ∈ (barO2 L).map φ := ⟨k, k.2, rfl⟩
    rw [hφ, hL.2] at h
    exact h)
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    rw [← hL.2, ← hφ] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  have hcentral := (liftOf_central_ext hX hLs hL).1
  have hkerf : f.ker ≤ Subgroup.center ↥(barO2 L) := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := k.2
    have h1 : φ k = 1 := by
      have h0 : f k = 1 := MonoidHom.mem_ker.1 hk
      exact congrArg Subtype.val h0
    have h2 : l ∈ gnC T := by
      have h3 : toStar T l = 1 := by
        rw [← hφmk l]
        have : QuotientGroup.mk' (CFSG.pCore 2 X) l = (k : X ⧸ CFSG.pCore 2 X) := hlk
        rw [this]
        exact h1
      exact (QuotientGroup.eq_one_iff l).1 h3
    have h4 : (k : X ⧸ CFSG.pCore 2 X) ∈
        ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
      ⟨l, ⟨hl, h2⟩, hlk⟩
    obtain ⟨z, hz, hzk⟩ := hcentral h4
    have : z = k := Subtype.ext hzk
    rwa [← this]
  exact ⟨f, hf, hkerf⟩

theorem centre_of_lift {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) :
    Nonempty ((↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (↥Ls ⧸ Subgroup.center ↥Ls)) ∧
      Nat.card (Subgroup.center ↥Ls) ∣ Nat.card (Subgroup.center ↥(barO2 L)) ∧
      Odd (Nat.card (Subgroup.center ↥Ls)) := by
  obtain ⟨f, hf, hker⟩ := barO2_centralExt hX hLs hL
  have hK : commutator ↥(barO2 L) = ⊤ := hL.1.component.2.2.1
  have hc := center_comap_eq_of_central_ext hK f hf hker
  have hdvd : Nat.card (Subgroup.center ↥Ls) ∣ Nat.card (Subgroup.center ↥(barO2 L)) := by
    have h1 : (Subgroup.center ↥(barO2 L)).map f = Subgroup.center ↥Ls := by
      rw [← hc, Subgroup.map_comap_eq_self_of_surjective hf]
    rw [← h1]
    exact Subgroup.card_map_dvd _ _
  exact ⟨quotCenter_mulEquiv_of_central_ext hK f hf hker, hdvd,
    (centre_barO2_odd hL.1).of_dvd_nat hdvd⟩

end CentreOfLift

section Datum

variable {X : Type} [Group X] [Finite X]

@[expose] def AltRanks (T L : Subgroup X) (n : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = n / r

@[expose] def RankDatum (T L : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)) : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L)))) ∨
  (∃ n : ℕ, (n = 6 ∨ n = 8) ∧ Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) ∧
      AltRanks T L n) ∨
  (∃ n : ℕ, (n = 7 ∨ (8 < n ∧ Even n)) ∧ Nonempty (↥Ls ≃* alternatingGroup (Fin n)) ∧
      AltRanks T L n) ∨
  ((∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 7 ∧ d.1 = .A 1 q ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = if r = 3 ∨ r = 7 then 1 else 0) ∨
  ((∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 3 ∧ d.1 = .twistedA 2 q ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = if r = 3 then 2 else if r = 7 then 1 else 0)

theorem isRankTwoPlus_of_classical {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsClassicalOrG2Index d.1) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hr : ¬ RankOneChevTwo S) : IsRankTwoPlus d.1 := by
  obtain ⟨d1, hv⟩ := d
  have hr' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hr'.1
  cases d1 with
  | A l Q =>
    have hQ : Q.p = 2 := hd
    have hl : 1 ≤ l := (hrange : 1 ≤ l ∧ (l = 1 → 4 ≤ Q.card)).1
    refine ⟨hQ, ?_⟩
    by_contra hlt
    have hl1 : l = 1 := by omega
    subst hl1
    exact hr (Or.inl ⟨⟨_, hv⟩, Or.inl ⟨Q, hQ, rfl⟩, ⟨e⟩⟩)
  | twistedA l Q =>
    have hQ : Q.p = 2 := hd
    have hl : 2 ≤ l := (hrange : 2 ≤ l ∧ (l = 2 → 3 ≤ Q.card)).1
    refine ⟨hQ, ?_⟩
    by_contra hlt
    have hl1 : l = 2 := by omega
    subst hl1
    exact hr (Or.inl ⟨⟨_, hv⟩, Or.inr ⟨Q, hQ, rfl⟩, ⟨e⟩⟩)
  | B l Q => exact ⟨hd, (hrange : 2 ≤ l ∧ ¬ (l = 2 ∧ Q.card = 2)).1⟩
  | D l Q => exact ⟨hd, (hrange : 4 ≤ l)⟩
  | twistedD l Q => exact ⟨hd, (hrange : 4 ≤ l)⟩
  | G2 Q => exact hd
  | C _ _ => exact hd.elim
  | E6 _ => exact hd.elim
  | E7 _ => exact hd.elim
  | E8 _ => exact hd.elim
  | F4 _ => exact hd.elim
  | twistedE6 _ => exact hd.elim
  | trialityD4 _ => exact hd.elim
  | suzuki _ => exact hd.elim
  | reeG2 _ => exact hd.elim
  | reeF4 _ => exact hd.elim
  | tits => exact hd.elim

theorem quotCenter_equiv_alt {S : Type} [Group S] {n : ℕ} (hn : 4 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) :
    Subgroup.center S = ⊥ ∧ Nonempty ((S ⧸ Subgroup.center S) ≃* alternatingGroup (Fin n)) := by
  have h1 : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using hn)
  have hc : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨s, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
    rw [h1, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by simpa using hz')
  exact ⟨hc, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientBot.trans e)⟩⟩

theorem pRank_lift_eq_chev (hT : LieOddRankTable) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  exact (pRank_barO2_eq hL.1 hr hr2).trans
    ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L)).trans
      (hT.chev _ hK d hd ⟨eQ.trans e'⟩ r hr hr2))

theorem rankDatum (hT : LieOddRankTable) {T T₁ T₂ : Subgroup X} {L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hshape : GNShape T T₁ T₂)
    (hLs : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls) : RankDatum T L Ls := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs.1 hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = CFSG.Open.pRank r (⊤ : Subgroup ↥(barO2 L)) := fun r hr hr2 =>
    (pRank_barO2_eq hL.1 hr hr2).trans (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))
  obtain ⟨-, hcase⟩ := hshape Ls hLs
  rcases hcase with ⟨hcl, hnr⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
    · exact Or.inl ⟨d, isRankTwoPlus_of_classical hd e hnr, ⟨e⟩, fun r hr hr2 =>
        (hrank r hr hr2).trans (hT.chev _ hK d hd ⟨eQ.trans e⟩ r hr hr2)⟩
    · rcases hn with rfl | rfl | rfl
      · exact absurd (Or.inr ⟨e⟩) hnr
      · exact Or.inr (Or.inl ⟨6, Or.inl rfl, ⟨e⟩, fun r hr hr2 =>
          (hrank r hr hr2).trans (hT.alt _ hK 6 (by norm_num) ⟨eQ.trans e⟩ r hr hr2)⟩)
      · exact Or.inr (Or.inl ⟨8, Or.inr rfl, ⟨e⟩, fun r hr hr2 =>
          (hrank r hr hr2).trans (hT.alt _ hK 8 (by norm_num) ⟨eQ.trans e⟩ r hr hr2)⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨d, q, hq, hd, ⟨e⟩⟩, fun r hr hr2 =>
        (hrank r hr hr2).trans ((hT.small _ hK r hr hr2).1 ⟨q, d, hq, hd, ⟨eQ.trans e⟩⟩)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨d, q, hq, hd, ⟨e⟩⟩, fun r hr hr2 =>
        (hrank r hr hr2).trans ((hT.small _ hK r hr hr2).2 ⟨q, d, hq, hd, ⟨eQ.trans e⟩⟩)⟩)))
  · obtain ⟨-, ⟨e'⟩⟩ := quotCenter_equiv_alt (n := n) (by rcases hn with rfl | ⟨h, -⟩ <;> omega) e
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e⟩, fun r hr hr2 =>
      (hrank r hr hr2).trans (hT.alt _ hK n (by rcases hn with rfl | ⟨h, -⟩ <;> omega)
        ⟨eQ.trans e'⟩ r hr hr2)⟩))

@[expose] def RankDatum1512 (T L : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)) : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 ∧ In1512 d.1 ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L)))) ∨
  (∃ n : ℕ, (n = 6 ∨ n = 8) ∧ Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) ∧
      AltRanks T L n) ∨
  (∃ n : ℕ, (n = 7 ∨ n = 10) ∧ Nonempty (↥Ls ≃* alternatingGroup (Fin n)) ∧ AltRanks T L n) ∨
  ((∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 7 ∧ d.1 = .A 1 q ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = if r = 3 ∨ r = 7 then 1 else 0) ∨
  ((∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 3 ∧ d.1 = .twistedA 2 q ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = if r = 3 then 2 else if r = 7 then 1 else 0)

theorem rankDatum1512_of_rankDatum_gen {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hd : RankDatum T L Ls) (h3 : CFSG.Open.pRank 3 L ≤ 3)
    (hres : ∀ d : TauCeti.ValidLieTypeIndex, Res1512 d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L)))) → False) :
    RankDatum1512 T L Ls := by
  rcases hd with ⟨d, hdr, e, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨n, hn, e, hr⟩ | h4 | h5
  · rcases in1512_or_res1512 hdr ((hr 3 Nat.prime_three (by norm_num)) ▸ h3) with hin | hres'
    · exact Or.inl ⟨d, hdr, hin, e, hr⟩
    · exact (hres d hres' e hr).elim
  · exact Or.inr (Or.inl ⟨n, hn, e, hr⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨n, ?_, e, hr⟩))
    have h := hr 3 Nat.prime_three (by norm_num)
    rcases hn with rfl | ⟨h8, ⟨k, hk⟩⟩
    · exact Or.inl rfl
    · right
      omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

theorem rankDatum1512_of_rankDatum {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hd : RankDatum T L Ls)
    (h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3) : RankDatum1512 T L Ls :=
  rankDatum1512_of_rankDatum_gen hd (h3 3 Nat.prime_three (by norm_num)) fun d hres e hr => by
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A l Q =>
      obtain ⟨q, hq, hq2, -, hq4⟩ := exists_prime_four_le_of_res1512_A hres
        (Nat.card (Subgroup.center ↥(barO2 L)))
      have h3q := h3 q hq hq2
      rw [← hr q hq hq2] at hq4
      omega
    | twistedA l Q =>
      obtain ⟨q, hq, hq2, -, hq4⟩ := exists_prime_four_le_of_res1512_twistedA hres
        (Nat.card (Subgroup.center ↥(barO2 L)))
      have h3q := h3 q hq hq2
      rw [← hr q hq hq2] at hq4
      omega
    | _ => exact hres.elim

end Datum

end CFSG.LocalAnalysis.RankThreeUC.S15
