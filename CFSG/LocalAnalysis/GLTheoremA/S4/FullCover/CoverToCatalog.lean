module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Open.StatedSUFieldChange
import CFSG.Open.StatedCenterThree
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Catalogue

open TauCeti Matrix

private theorem i1912_no_C_index (p : ℕ) (i : CFSGIndex)
    (hi : onLie (fun d => match d with
      | .C 2 q => p = 3 ∧ q.card = 8
      | .C 3 q => p = 3 ∧ q.card = 2
      | _ => False) i) : False := by
  cases i with
  | cyclic _ _ => exact hi
  | alternating _ _ => exact hi
  | sporadic _ => exact hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | C r q =>
      have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
      have hr3 : 3 ≤ r := hr.1
      have hp2 : q.p ≠ 2 := hr.2
      rcases r with _ | _ | _ | r
      · omega
      · omega
      · omega
      · rcases r with _ | r
        · obtain ⟨-, hc⟩ := hi
          have hq : q.p ∣ 2 := by
            rw [← hc, PrimePower.card_def]
            exact dvd_pow_self q.p q.exponent_pos.ne'
          exact hp2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hq)
        · exact hi
    | _ => exact hi

private noncomputable def i1912_quotCenter_SL {Q F : Type} [Group Q] [Field F] (n : ℕ)
    (e : Q ≃* StatedSL n F) : Q ⧸ Subgroup.center Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
  let eSL : Q ≃* Matrix.SpecialLinearGroup (Fin n) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).symm
  QuotientGroup.congr _ _ eSL (Subgroup.map_center_eq eSL)

private noncomputable def i1912_quotCenter_SU {Q F : Type} [Group Q] [Field F] [Finite F] {d f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ f) ≠ (3, 2))
    (e : Q ≃* StatedSU d (2 ^ f) F) :
    Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSU d (2 ^ f) F) :=
  (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f) hF hd hdq).2)

private theorem i1912_fullLinear_false_iff (d q : ℕ) (Q : Type) [Group Q] :
    FullLinearCover false d q Q ↔
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (Q ≃* StatedSL d F) :=
  Iff.rfl

private theorem i1912_fullLinear_true_iff (d q : ℕ) (Q : Type) [Group Q] :
    FullLinearCover true d q Q ↔
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
        Nonempty (Q ≃* StatedSU d q F) :=
  Iff.rfl

private def i1912_galois_transport {G : Type} [Group G] (r : ℕ) {c c' fe fe' : ℕ}
    [Fact c.Prime] [Fact c'.Prime] (hc : c = c') (hf : fe = fe')
    (e : G ≃* StatedProj (StatedSU r (c ^ fe) (GaloisField c (2 * fe)))) :
    G ≃* StatedProj (StatedSU r (c' ^ fe') (GaloisField c' (2 * fe'))) := by
  subst hc hf
  exact e

private noncomputable def i1912_twistedA_equiv (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) [Fact q.p.Prime] :
    ValidLieTypeIndex.Group ⟨LieTypeIndex.twistedA r q, hv⟩ ≃*
      StatedProj (StatedSU (r + 1) (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) :=
  i1912_galois_transport (r + 1)
    (show ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA r q, hv⟩ = q.p by
      simp only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_twistedA])
    (show ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA r q, hv⟩ = q.exponent by
      simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_twistedA])
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)

private theorem i1912_catalog_SL (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (K : Type) [Group K] (F : Type) [Field F] [Finite F] (hcard : Nat.card F = 2 ^ n)
    (e : K ≃* StatedSL 3 F) :
    catalogIs (K ⧸ Subgroup.center K) (k2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqc : q.card = 2 ^ n := by rw [PrimePower.card_def]
  have hv : (LieTypeIndex.A 2 q).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ⟨by norm_num, ?_⟩, ?_⟩
    · intro h
      omega
    · intro hdup
      have hd := (LieTypeIndex.isDuplicateRepresentative_iff _).1 hdup
      rcases hd with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h3, _⟩
      · omega
      · rw [hqc] at h2
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      · omega
  refine ⟨.lie ⟨LieTypeIndex.A 2 q, hv⟩, Or.inl ⟨rfl, rfl, ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  · have hq0 : 0 < n := by omega
    exact ⟨((i1912_quotCenter_SL 3 e).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 n hq0 hcard) (Fin 3))).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm⟩

private theorem i1912_catalog_SU3 (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (K : Type) [Group K] (F : Type) [Field F] [Finite F] (hcard : Nat.card F = (2 ^ n) ^ 2)
    (e : K ≃* StatedSU 3 (2 ^ n) F) :
    catalogIs (K ⧸ Subgroup.center K) (k2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hv : (LieTypeIndex.twistedA 2 q).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ⟨le_rfl, fun _ => ?_⟩,
      fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [PrimePower.card_def]
    show 3 ≤ 2 ^ n
    omega
  have hdq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hF' : Nat.card F = 2 ^ (2 * n) := by
    rw [hcard, ← pow_mul, mul_comm]
  have hqe : q.exponent = n := rfl
  have hqp : q.p = 2 := rfl
  have hn0 : 0 < 2 * n := by omega
  refine ⟨.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩, ⟨rfl, hqp, hodd, by omega⟩, ?_⟩
  exact ⟨((i1912_quotCenter_SU hcard (le_refl 3) hdq e).trans
    (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 (2 * n) hn0 hF') 3 (2 ^ n))).trans
    (i1912_twistedA_equiv 2 q hv).symm⟩

private theorem i1912_catalog_SU6 (K : Type) [Group K] (F : Type) [Field F] [Finite F]
    (hcard : Nat.card F = 2 ^ 2) (e : K ≃* StatedSU 6 2 F) :
    catalogIs (K ⧸ Subgroup.center K) (k2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hv : (LieTypeIndex.twistedA 5 q).Valid :=
    (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ⟨by norm_num,
      fun h => absurd h (by norm_num)⟩, fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
  have hF1 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hcard] <;> norm_num
  have hdq : ((6 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hF' : Nat.card F = 2 ^ (2 * 1) := by rw [hcard] <;> norm_num
  have hcq : q.card = 2 := by rw [PrimePower.card_def] <;> norm_num
  refine ⟨.lie ⟨LieTypeIndex.twistedA 5 q, hv⟩, ⟨rfl, hcq⟩, ?_⟩
  exact ⟨((i1912_quotCenter_SU hF1 (by norm_num) hdq e).trans
    (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 (2 * 1) (by norm_num) hF') 6 (2 ^ 1))).trans
    (i1912_twistedA_equiv 5 q hv).symm⟩

private theorem i1912_catalog_linear (K : Type) [Group K] (p : ℕ) (h : K2LinearCover p K) :
    catalogIs (K ⧸ Subgroup.center K) (k2 p) := by
  obtain ⟨rfl, h⟩ := h
  rcases h with ⟨n, hn1, heven, hF⟩ | ⟨n, hn1, hodd, hF⟩ | hF
  · obtain ⟨F, hFf, hFfin, hcard, ⟨e⟩⟩ := (i1912_fullLinear_false_iff 3 (2 ^ n) K).1 hF
    obtain ⟨k, hk⟩ := heven
    exact i1912_catalog_SL n (by omega) ⟨k, hk⟩ K F hcard e
  · obtain ⟨F, hFf, hFfin, hcard, ⟨e⟩⟩ := (i1912_fullLinear_true_iff 3 (2 ^ n) K).1 hF
    exact i1912_catalog_SU3 n (by omega) hodd K F hcard e
  · obtain ⟨F, hFf, hFfin, hcard, ⟨e⟩⟩ := (i1912_fullLinear_true_iff 6 2 K).1 hF
    exact i1912_catalog_SU6 K F hcard e

theorem k2Cover_imp_catalogIs (p : ℕ) {Q : Type} [Group Q] (h : K2Cover p Q) :
    catalogIs (Q ⧸ Subgroup.center Q) (k2 p) := by
  obtain ⟨-, hc⟩ := h
  rcases hc with ⟨hz, i, hi, ⟨e⟩⟩ | ⟨hz, i, hi, ⟨e⟩⟩ | hL | ⟨i, hi, hmax, -⟩
  · exact ⟨i, hi, ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e⟩⟩
  · exact (i1912_no_C_index p i hi).elim
  · exact i1912_catalog_linear Q p hL
  · obtain ⟨-, -, -, -, π, hπs, hπk, -⟩ := hmax
    have hk : k2 p i := by
      cases i with
      | cyclic _ _ => exact False.elim hi
      | alternating _ _ => exact False.elim hi
      | lie _ => exact False.elim hi
      | sporadic s =>
        obtain ⟨rfl, hs⟩ := hi
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k2, k2Spor]
    exact ⟨i, hk, ⟨(QuotientGroup.quotientMulEquivOfEq hπk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)⟩⟩

end Catalogue

private theorem k3_exists_primePower_card_eq (F : Type) [Field F] [Finite F] :
    ∃ (q : TauCeti.PrimePower) (_ : Fact q.p.Prime), q.card = Nat.card F ∧
      Nonempty (F ≃+* GaloisField q.p q.exponent) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  refine ⟨⟨ringChar F, m, hp, m.pos⟩, ⟨hp⟩, ?_, ⟨?_⟩⟩
  · rw [TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card, hm]
  · have : Fintype (GaloisField (ringChar F) m) := Fintype.ofFinite _
    refine FiniteField.ringEquivOfCardEq (K := F) (K' := GaloisField (ringChar F) m) ?_
    rw [hm, ← Nat.card_eq_fintype_card, GaloisField.card _ _ m.ne_zero]

private theorem k3_exists_primePower_sq_card_eq (F : Type) [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (hq : 2 ≤ q) :
    ∃ (Q : TauCeti.PrimePower) (_ : Fact Q.p.Prime), Q.card = q ∧
      Nonempty (F ≃+* GaloisField Q.p (2 * Q.exponent)) := by
  obtain ⟨⟨p, e, hp, he⟩, hpf, hQ₀, ⟨φ⟩⟩ := k3_exists_primePower_card_eq F
  rw [TauCeti.PrimePower.card_def, hFq] at hQ₀
  have hqd : q ∣ p ^ e := ⟨q, by rw [hQ₀, pow_two]⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hq
  have hek : e = 2 * k := by
    refine Nat.pow_right_injective hp.two_le ?_
    show p ^ e = p ^ (2 * k)
    rw [hQ₀, ← pow_mul, mul_comm]
  subst hek
  exact ⟨⟨p, k, hp, Nat.pos_of_ne_zero hk⟩, ⟨hp⟩, TauCeti.PrimePower.card_def _, ⟨φ⟩⟩

private theorem k3_center_statedSU_three_eq {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (h3 : 3 ∣ q + 1) :
    Subgroup.center (StatedSU 3 q F) = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F) := by
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hF
  have hq : q ≠ 0 := by omega
  symm
  refine Subgroup.eq_of_le_of_card_ge (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ?_
  rw [CFSG.Open.StatedCenterThree.card_center_statedSU_three hF h3]
  have h3F : 3 ∣ Nat.card F - 1 := by
    rw [hF, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left h3 _
  have hr : Nat.card (rootsOfUnity 3 F) = 3 :=
    CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3F
  let f : rootsOfUnity 3 F → ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) := fun ζ =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Fˣ),
      CFSG.Open.StatedCenterThree.scalar_mem hq h3 ((mem_rootsOfUnity 3 (ζ : Fˣ)).mp ζ.2)⟩,
      Subgroup.mem_subgroupOf.2 ⟨(ζ : Fˣ), rfl⟩⟩
  refine hr.symm.le.trans (Nat.card_le_card_of_injective f fun ζ₁ ζ₂ h => ?_)
  have h' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₁ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 =
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₂ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun z : ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) =>
      ((((z : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h'
  exact Subtype.ext (Units.ext h')

private theorem catalogIs_k3_of_statedSL_three {Q F : Type} [Group Q] [Field F] [Finite F]
    (h6 : Nat.card F % 6 = 1) (e : Q ≃* StatedSL 3 F) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 3) := by
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := k3_exists_primePower_card_eq F
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqc]
    omega
  refine ⟨.lie ⟨.A 2 q, hv⟩, ?_, ⟨?_⟩⟩
  · show 3 = 3 ∧ q.card % 6 = 1
    rw [hqc]
    exact ⟨rfl, h6⟩
  · let e₁ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    exact ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

private theorem catalogIs_k3_of_statedSU_three {Q F : Type} [Group Q] [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (h6 : q % 6 = 5) (e : Q ≃* StatedSU 3 q F) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 3) := by
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by omega
  obtain ⟨R, _, hRc, ⟨φ⟩⟩ := k3_exists_primePower_sq_card_eq F hFq hq2
  have hv : (TauCeti.LieTypeIndex.twistedA 2 R).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨⟨le_rfl, fun _ => ?_⟩, fun h => h⟩
    show 3 ≤ R.card
    rw [hRc]
    exact hq3
  have hR' : R.p ^ R.exponent = q := (TauCeti.PrimePower.card_def R).symm.trans hRc
  subst hR'
  have hFq' : Nat.card (GaloisField R.p (2 * R.exponent)) = (R.p ^ R.exponent) ^ 2 := by
    rw [GaloisField.card _ _ (by have := R.exponent_pos; omega), ← pow_mul, mul_comm]
  have e₃ : Q ≃* StatedSU 3 (R.p ^ R.exponent) (GaloisField R.p (2 * R.exponent)) :=
    e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 3 _)
  refine ⟨.lie ⟨.twistedA 2 R, hv⟩, ?_, ⟨?_⟩⟩
  · show 3 = 3 ∧ R.card % 6 = 5
    rw [TauCeti.PrimePower.card_def]
    exact ⟨rfl, h6⟩
  · exact ((QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)).trans
      (QuotientGroup.quotientMulEquivOfEq (k3_center_statedSU_three_eq hFq' h3))).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 R hv).symm

private theorem catalogIs_k3_of_k3LinearCover {p : ℕ} {Q : Type} [Group Q] (h : K3LinearCover p Q) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
  obtain ⟨rfl, r, f, -, -, ⟨h6, hfl⟩ | ⟨h6, hfl⟩⟩ := h
  · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = r ^ f ∧ Nonempty (Q ≃* StatedSL 3 F) := by
      simpa [FullLinearCover] using hfl
    exact catalogIs_k3_of_statedSL_three (by rw [hc]; exact h6) e
  · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (r ^ f) ^ 2 ∧ Nonempty (Q ≃* StatedSU 3 (r ^ f) F) := by
      simpa [FullLinearCover] using hfl
    exact catalogIs_k3_of_statedSU_three hc h6 e

theorem k3Cover_imp_catalogIs {p : ℕ} {Q : Type} [Group Q] (h : K3Cover p Q) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
  obtain ⟨-, h | h | h⟩ := h
  · obtain ⟨hZ, i, hi, ⟨e⟩⟩ := h
    exact ⟨i, hi, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans e)⟩⟩
  · exact catalogIs_k3_of_k3LinearCover h
  · obtain ⟨i, hi, ⟨-, -, -, -, π, hπ, hker, -⟩, -⟩ := h
    refine ⟨i, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩⟩
    cases i <;> first | exact ⟨hi.1, Or.inl hi.2⟩ | exact ⟨hi.1, Or.inr hi.2⟩ | exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA
