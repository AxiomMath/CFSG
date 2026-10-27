module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

section Transport

noncomputable abbrev i1912CQ (K : Type) [Group K] : MulAut K →* MulAut (K ⧸ Subgroup.center K) :=
  CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K

private theorem i1912_cqHom_conj {K : Type} [Group K] (g : K) :
    i1912CQ K (MulAut.conj g) = MulAut.conj (g : K ⧸ Subgroup.center K) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
  change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (MulAut.conj g)
    (QuotientGroup.mk' (Subgroup.center K) y) = _
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem i1912_innerAut_quotient_le_map {K : Type} [Group K] :
    innerAut (K ⧸ Subgroup.center K) ≤ (innerAut K).map (i1912CQ K) := by
  intro φ hφ
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hφ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) s
  refine ⟨MulAut.conj g, MonoidHom.mem_range.2 ⟨g, rfl⟩, ?_⟩
  rw [i1912_cqHom_conj]
  rfl

private theorem i1912_map_innerAut_le {K : Type} [Group K] :
    (innerAut K).map (i1912CQ K) ≤ innerAut (K ⧸ Subgroup.center K) := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hφ
  exact MonoidHom.mem_range.2 ⟨(g : K ⧸ Subgroup.center K), (i1912_cqHom_conj g).symm⟩

private theorem i1912_isElemAbelian_map {M M' : Type*} [Group M] [Group M'] {p : ℕ}
    (ψ : M →* M') (hψ : Function.Injective ψ) {E : Subgroup M} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map ψ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    change ψ x * ψ y = ψ y * ψ x
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ this
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

private theorem i1912_twoPrimary_of_map {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (p : ℕ) (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A)
    (h : IsTwoPrimaryWeaklyLocallyBalanced p 1 (A.map (i1912CQ K))) :
    IsTwoPrimaryWeaklyLocallyBalanced p 1 A := by
  have hΨi : Function.Injective (i1912CQ K) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  intro D hD H hH hAH
  have hD' : IsEkIn p 1 (A.map (i1912CQ K)) (D.map (i1912CQ K)) := by
    refine ⟨Subgroup.map_mono hD.1, i1912_isElemAbelian_map _ hΨi hD.2.1, ?_⟩
    rw [Subgroup.card_map_of_injective hΨi, hD.2.2]
  have hH' : innerAut (K ⧸ Subgroup.center K) ≤ H.map (i1912CQ K) :=
    i1912_innerAut_quotient_le_map.trans (Subgroup.map_mono hH)
  have hAH' : A.map (i1912CQ K) ≤
      Subgroup.normalizer ((H.map (i1912CQ K) : Subgroup (MulAut (K ⧸ Subgroup.center K))) :
        Set (MulAut (K ⧸ Subgroup.center K))) :=
    (Subgroup.map_mono hAH).trans (Subgroup.le_normalizer_map _)
  have key := h (D.map (i1912CQ K)) hD' (H.map (i1912CQ K)) hH' hAH'
  have hle : ⁅(localDeltaIn p H D).map (i1912CQ K), A.map (i1912CQ K)⁆ ≤
      ⁅localDeltaIn p (H.map (i1912CQ K)) (D.map (i1912CQ K)), A.map (i1912CQ K)⁆ :=
    Subgroup.commutator_mono
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le p _ hΨi H D) le_rfl
  have hmap : (⁅localDeltaIn p H D, A⁆ : Subgroup (MulAut K)).map (i1912CQ K) =
      ⁅(localDeltaIn p H D).map (i1912CQ K), A.map (i1912CQ K)⁆ :=
    Subgroup.map_commutator _ _ _
  have hcard : Nat.card (⁅localDeltaIn p H D, A⁆ : Subgroup (MulAut K)) =
      Nat.card ((⁅localDeltaIn p H D, A⁆ : Subgroup (MulAut K)).map (i1912CQ K)) :=
    (Subgroup.card_map_of_injective hΨi).symm
  rw [hcard, hmap]
  exact key.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end Transport

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

theorem i1912_catalog_of_K2Cover (p : ℕ) (K : Type) [Group K] (hK : K2Cover p K) :
    catalogIs (K ⧸ Subgroup.center K) (k2 p) := by
  obtain ⟨-, hc⟩ := hK
  rcases hc with ⟨hz, i, hi, ⟨e⟩⟩ | ⟨hz, i, hi, ⟨e⟩⟩ | hL | ⟨i, hi, hmax, -⟩
  · exact ⟨i, hi, ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e⟩⟩
  · exact (i1912_no_C_index p i hi).elim
  · exact i1912_catalog_linear K p hL
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

theorem i1912At_of (h1 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD1912Chev p)
    (h2 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD1912Two p) : I1912At := by
  intro p hp hp2 K _ hfin hK _ hcov A hA
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  have hS : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hnon : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
    by_contra hc
    simp only [ne_eq, not_exists, not_not] at hc
    haveI : Nontrivial (K ⧸ Subgroup.center K) := hS.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative (G := K ⧸ Subgroup.center K)
      ⟨⟨fun a b => hc a b⟩⟩
  have hA' : IsElemAbelian p (A.map (i1912CQ K)) :=
    i1912_isElemAbelian_map _ (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K) hA
  rcases hcov with hK1 | hK2
  · rcases h1 p hp hp2 (K ⧸ Subgroup.center K) hS hnon hK1.2 (A.map (i1912CQ K)) hA' with
      h | ⟨h3, h4, h5⟩
    · exact Or.inl (i1912_twoPrimary_of_map p A hA h)
    · exact Or.inr ⟨h3, h4, fun hAK => h5 ((Subgroup.map_mono hAK).trans i1912_map_innerAut_le)⟩
  · exact Or.inl (i1912_twoPrimary_of_map p A hA
      (h2 p hp hp2 (K ⧸ Subgroup.center K) hS hnon (i1912_catalog_of_K2Cover p K hK2)
        (A.map (i1912CQ K)) hA'))

end CFSG.LocalAnalysis.GLTheoremA
