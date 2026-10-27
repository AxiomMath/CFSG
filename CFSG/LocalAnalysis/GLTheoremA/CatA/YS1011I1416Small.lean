module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagL2
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem small_sq_dvd_aut {G : Type} [Group G] [Finite G] {X K A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hK : GLAPComponent p X K) (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hA : IsElemAbelian p A)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A) :
    p ^ 2 ∣ Nat.card (MulAut (PSimple p K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let H : Subgroup N := A.subgroupOf N
  let ψ : H →* MulAut (PSimple p K) := (chevAut p K).comp H.subtype
  have hcardH : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hmap : ψ.ker.map (N.subtype.comp H.subtype) = A ⊓ centModSubgroup p K := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : chevAut p K x.1 = 1 := hx
      have hcent : CentMod p K (x.1 : G) := (chevAut_eq_one_iff hp hK x.1.2).1 hx'
      exact ⟨Subgroup.mem_subgroupOf.1 x.2, centMod_iff.1 hcent⟩
    · rintro ⟨hgA, hgC⟩
      have hgN : g ∈ N := (mem_centModSubgroup.1 hgC).1
      refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, ?_, rfl⟩
      show chevAut p K ⟨g, hgN⟩ = 1
      exact (chevAut_eq_one_iff hp hK hgN).2 (centMod_iff.2 hgC)
  have hf : Function.Injective (N.subtype.comp H.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(A ⊓ centModSubgroup p K) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hsplitA : Nat.card A = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← hcardH, hsplit]
  have hdvdR : Nat.card ψ.range ∣ p ^ m := by
    rw [← hm, hsplitA]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdR
  have hcpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hRge : p ^ 2 ≤ Nat.card ψ.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [← hsplitA, hkerCard]
    exact hcard
  have hj2 : 2 ≤ j := by
    rw [hj] at hRge
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRge
  have hp2r : p ^ 2 ∣ Nat.card ψ.range := by
    rw [hj]
    exact pow_dvd_pow p hj2
  exact hp2r.trans (Subgroup.card_subgroup_dvd_card ψ.range)

theorem small_not_sq_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 120) : False := by
  have hle : p ≤ 11 := by
    have : p ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem small_not_sq_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 336) : False := by
  have hle : p ≤ 18 := by
    have : p ^ 2 ≤ 336 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem small_eq3_1512 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 1512) : p = 3 := by
  have hle : p ≤ 38 := by
    have : p ^ 2 ≤ 1512 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | rfl | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem small_eq3_12096 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 12096) : p = 3 := by
  have hle : p ≤ 110 := by
    have : p ^ 2 ≤ 12096 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | rfl | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem small_psl_iso {S : Type} [Group S] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : StatedClassicalModel S .PSL 2 p f) : Nonempty (S ≃* CFSG.AGLEmbedding.PSL2GF p f) :=
  CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated (F := GaloisField p f) p f (by omega)
    (GaloisField.card p f (by omega)) h

theorem small_card_aut_psl {S : Type} [Group S] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (e : S ≃* CFSG.AGLEmbedding.PSL2GF p f) :
    Nat.card (MulAut S) = p ^ f * ((p ^ f) ^ 2 - 1) * f :=
  (Nat.card_congr (MulAut.congr e).toEquiv).trans (CFSG.AGLEmbedding.card_mulAut_psl2GF p f hf)

theorem small_card_psl24 {S : Type} [Group S] (h : CFSG.Blueprint.LieModel S .PSL 2 2 2) :
    Nat.card (MulAut S) = 120 := by
  obtain ⟨e⟩ := small_psl_iso (p := 2) (f := 2) (by norm_num)
    (h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  exact (small_card_aut_psl (by norm_num) e).trans (by norm_num)

theorem small_card_psl32 {S : Type} [Group S] (h : CFSG.Blueprint.LieModel S .PSL 3 2 1) :
    Nat.card (MulAut S) = 336 := by
  have h7 := CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two
    (h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  obtain ⟨e⟩ := small_psl_iso (p := 7) (f := 1) le_rfl h7
  exact (small_card_aut_psl le_rfl e).trans (by norm_num)

theorem small_card_psl28 {S : Type} [Group S] (h : CFSG.Blueprint.LieModel S .PSL 2 2 3) :
    Nat.card (MulAut S) = 1512 := by
  obtain ⟨e⟩ := small_psl_iso (p := 2) (f := 3) (by norm_num)
    (h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  exact (small_card_aut_psl (by norm_num) e).trans (by norm_num)

theorem small_amb_lie {r : ℕ} (hr2 : r ≠ 2) {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : ambiguousChev r (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    (∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.card = 8 ∧ r = 3) ∨
      (∃ q : TauCeti.PrimePower, d = .twistedA 3 q ∧ q.card = 2 ∧ r = 3) := by
  revert h
  cases d
  case A r' q =>
    match r', q with
    | 1, q => exact fun h => Or.elim h (fun h7 => absurd h7.2 hr2) fun h8 => Or.inl ⟨q, rfl, h8.1, h8.2⟩
    | 0, q => exact fun h => False.elim h
    | r' + 2, q => exact fun h => False.elim h
  case twistedA r' q =>
    match r', q with
    | 3, q => exact fun h => Or.inr ⟨q, rfl, h.1, h.2⟩
    | 2, q => exact fun h => absurd h.2 hr2
    | 0, q => exact fun h => False.elim h
    | 1, q => exact fun h => False.elim h
    | r' + 4, q => exact fun h => False.elim h
  all_goals exact fun h => False.elim h

def small_pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

theorem small_pp3_card : small_pp3.card = 3 := by
  rw [TauCeti.PrimePower.card_def]
  rfl

theorem small_valid_tw23 : (TauCeti.LieTypeIndex.twistedA 2 small_pp3).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [small_pp3]

theorem small_u42_of_model {S : Type} [Group S] (h : CFSG.Blueprint.LieModel S .PSU 4 2 1) :
    catalogIs S S9.isU4two := by
  obtain ⟨-, F, _, _, hF, ⟨eU⟩⟩ := h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  exact CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj (by rw [hF]; norm_num) eU

theorem small_alt6 {G : Type} [Group G] [Finite G] {p : ℕ} {Y K A : Subgroup G} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : GLAPComponent p Y K) (hinn : InnDiagOn p A K) (hA : IsElemAbelian p A)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A)
    (e : PSimple p K ≃* alternatingGroup (Fin 6)) :
    p = 3 ∧ catalogIs (PSimple p K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i) := by
  have h56 : (5 : ℕ) ≤ 6 := by norm_num
  have hc : catalogIs (PSimple p K) S10.isA6 := ⟨TauCeti.CFSGIndex.alternating 6 h56, rfl, ⟨e⟩⟩
  have h3 : p = 3 := rank_holds G p Y K A hp hp2 hK (Or.inr hc) hinn.1 hA hcard
  subst h3
  exact ⟨rfl, TauCeti.CFSGIndex.alternating 6 h56, Or.inl rfl, ⟨e⟩⟩

theorem small_u42 {G : Type} [Group G] [Finite G] {p : ℕ} {Y K A : Subgroup G} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : GLAPComponent p Y K) (hinn : InnDiagOn p A K) (hA : IsElemAbelian p A)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A)
    (hcat : catalogIs (PSimple p K) S9.isU4two) :
    p = 3 ∧ catalogIs (PSimple p K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i) := by
  have h3 : p = 3 := rank_holds G p Y K A hp hp2 hK (Or.inl hcat) hinn.1 hA hcard
  subst h3
  obtain ⟨i, hi, e⟩ := hcat
  exact ⟨rfl, i, Or.inr (Or.inr (Or.inr hi)), e⟩

section L2Certs


theorem small_l2_8 {G : Type} [Group G] [Finite G] {p : ℕ} {Y K A : Subgroup G} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : GLAPComponent p Y K) (hinn : InnDiagOn p A K) (hA : IsElemAbelian p A)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A) (hAut : p ^ 2 ∣ 1512)
    (hL2 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd (PSimple p K)) : False := by
  have h3 : p = 3 := small_eq3_1512 hp hp2 hAut
  subst h3
  obtain ⟨hs, hnc⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs
  exact i112d_l2_false hK hA hinn hcard (chev_center_eq_bot_of_simple_nonabelian hnc) hL2

end L2Certs

section U33Certs


theorem small_u33 {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hAut : p ^ 2 ∣ Nat.card (MulAut S)) (hPSU : StatedClassicalModel S .PSU 3 3 1) :
    p = 3 ∧ catalogIs S (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i) := by
  have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
  obtain ⟨eS⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  have hN := CFSG.GH74.KGroups.U33.card_mulAut eS
  have h3 : p = 3 := small_eq3_12096 hp hp2 (by rw [hN] at hAut; exact hAut)
  subst h3
  have hT : StatedClassicalModel
      (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 small_pp3, small_valid_tw23⟩) .PSU 3 3 1 :=
    CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two small_pp3
      small_valid_tw23 small_pp3_card (MulEquiv.refl _)
  obtain ⟨eT⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hT⟩)
  exact ⟨rfl, .lie ⟨.twistedA 2 small_pp3, small_valid_tw23⟩,
    Or.inr (Or.inr (Or.inl small_pp3_card)), ⟨eS.trans eT.symm⟩⟩

end U33Certs

section OddCerts


theorem small_odd_lie {S : Type} [Group S] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = r)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : CFSG.Blueprint.OddLieType S := by
  obtain ⟨t, n, p, f, hp, hM⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char d
  have hpr : p = r := hp.trans hd
  subst hpr
  have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.LieModel.of_mulEquiv e.symm hM)
  exact ⟨t, n, p, f, hr, hr2, CFSG.Blueprint.LieModel.admissible hB, hB⟩

end OddCerts

section MainCerts


theorem i1416TwoSmall_holds (G : Type) [Group G] [Finite G] : I1416TwoSmall G := by
  intro p Y K A r hp hp2 hr hr2 _hY hK h2 hrC hA hinn hcard
  haveI : Fact p.Prime := ⟨hp⟩
  have hAut := small_sq_dvd_aut hp hK hinn.1 hA hcard
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h2 with ⟨t, n, f, hX⟩ | ⟨e6⟩ | hPSU
  · rcases hrC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX
            (small_odd_lie (d := d) hr hr2 hi e) with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [small_card_psl24 hX] at hAut
          exact (small_not_sq_120 hp hp2 hAut).elim
        · rw [small_card_psl32 hX] at hAut
          exact (small_not_sq_336 hp hp2 hAut).elim
        · obtain ⟨h3, hc⟩ := small_u42 hp hp2 hK hinn hA hcard (small_u42_of_model hX)
          subst h3
          exact ⟨rfl, hc⟩
    ·
      cases i with
      | cyclic _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | alternating n' hn' =>
        rcases hi with ⟨rfl, h5 | h5⟩ | ⟨rfl, h6 | h6⟩ | ⟨rfl, h8⟩
        · exact absurd h5 hr2
        · rw [small_card_psl24 (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e)] at hAut
          exact (small_not_sq_120 hp hp2 hAut).elim
        · exact absurd h6 hr2
        · obtain ⟨h3, hc⟩ := small_alt6 hp hp2 hK hinn hA hcard e
          subst h3
          exact ⟨rfl, hc⟩
        · exact absurd h8 hr2
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases small_amb_lie hr2 hv hi with ⟨q, rfl, hq8, rfl⟩ | ⟨q, rfl, hq2, rfl⟩
        ·
          have hM := CFSG.Models.lieModel_A 1 q hv e
          obtain ⟨hq2', hq3⟩ := primePower_eq_of_card_eq (r := 2) (s := 3) Nat.prime_two (by norm_num)
            (hq8.trans (by norm_num))
          have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
          rw [hq2', hq3] at hBP
          rw [small_card_psl28 hBP] at hAut
          obtain ⟨eL⟩ := small_psl_iso (p := 2) (f := 3) (by norm_num)
            (hBP.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
          exact (small_l2_8 hp hp2 hK hinn hA hcard hAut ⟨3, by decide, by norm_num, ⟨eL⟩⟩).elim
        ·
          have hcat : catalogIs (PSimple p K) S9.isU4two := ⟨.lie ⟨.twistedA 3 q, hv⟩, hq2, ⟨e⟩⟩
          obtain ⟨h3, hc⟩ := small_u42 hp hp2 hK hinn hA hcard hcat
          subst h3
          exact ⟨rfl, hc⟩
  ·
    obtain ⟨h3, hc⟩ := small_alt6 hp hp2 hK hinn hA hcard e6.some
    subst h3
    exact ⟨rfl, hc⟩
  ·
    obtain ⟨h3, hc⟩ := small_u33 hp hp2 hAut hPSU
    subst h3
    exact ⟨rfl, hc⟩

end MainCerts

section FinalCerts


theorem i1416TwoAt_holds' (G : Type) [Group G] [Finite G] (hSpor : I1416TwoSpor G) : I1416TwoAt G :=
  i1416TwoAt_holds hSpor (i1416TwoSmall_holds G)

end FinalCerts

end CFSG.LocalAnalysis.GLTheoremA
