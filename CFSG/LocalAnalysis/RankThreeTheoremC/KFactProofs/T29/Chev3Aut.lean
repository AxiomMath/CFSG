module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporStruct
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.UnitaryFlag TauCeti

section Aut

theorem aut_three_inner_projectiveSL_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (ψ : MulAut (projectiveSL 3 K)) (hψ : ψ ^ 3 = 1) :
    ∃ a : projectiveSL 3 K, ψ = MulAut.conj a := by
  have hodd : Odd (orderOf ψ) := by
    have h1 : orderOf ψ ∣ 3 := orderOf_dvd_of_pow_eq_one hψ
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      decide
  have hE := mem_semilinearAutGroup_of_odd (n := 3) (K := K) le_rfl hodd
  have hAut : Subsingleton (K ≃+* K) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K
      (n := 1) (by rw [hK]; norm_num)).1
    have : Nat.card (RingAut K) = 1 := h
    exact (Nat.card_eq_one_iff_unique.mp this).1
  have hED : semilinearAutGroup 3 K ≤ linearAutGroup 3 K := by
    rw [semilinearAutGroup, Subgroup.closure_le]
    rintro _ (h | ⟨σ, rfl⟩)
    · exact h
    · have : σ = 1 := Subsingleton.elim _ _
      subst this
      rw [map_one]
      exact one_mem _
  have hIdx : (inner (projectiveSL 3 K)).relIndex (linearAutGroup 3 K) = 1 := by
    have h := relIndex_inner_linearAutGroup_dvd (k := K) (n := 3) (by norm_num)
    have h2 : Nat.gcd 3 (Nat.card K - 1) = 1 := by
      rw [hK]
      norm_num
    rw [h2] at h
    exact Nat.dvd_one.mp h
  have hDI : linearAutGroup 3 K ≤ inner (projectiveSL 3 K) := Subgroup.relIndex_eq_one.mp hIdx
  obtain ⟨a, ha⟩ := hDI (hED hE)
  exact ⟨a, ha.symm⟩

theorem aut_three_inner_primeFormP {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hf3 : ¬ 3 ∣ f)
    (hℓ : ¬ 3 ∣ ℓ ^ f + 1)
    (ψ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (hψ : ψ ^ 3 = 1) :
    ψ ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  have hfin := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, hDnorm, -, hDI⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set Dl := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDl
  set F := primeFormFieldFactor h hC hn hq with hF
  have hcardAut : Nat.card (K ≃+* K) = 2 * f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic h.prime K h.card).1
  have hFψ3 : (F ψ) ^ 3 = 1 := by rw [← map_pow, hψ, map_one]
  have hFψ : F ψ = 1 := by
    have h1 : orderOf (F ψ) ∣ 3 := orderOf_dvd_of_pow_eq_one hFψ3
    have h2 : orderOf (F ψ) ∣ 2 * f := hcardAut ▸ orderOf_dvd_natCard (F ψ)
    have hcop : Nat.Coprime 3 (2 * f) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h3 | h3
      · omega
      · exact hf3 h3
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hψD : ψ ∈ Dl := by
    rw [← hFker, MonoidHom.mem_ker]
    exact hFψ
  have hIN : (inner T).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hcop : Nat.Coprime 3 (Nat.card (Dl ⧸ (inner T).subgroupOf Dl)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => hℓ (hd.trans hDI)
  set y : Dl ⧸ (inner T).subgroupOf Dl := QuotientGroup.mk ⟨ψ, hψD⟩ with hy
  have hyp : y ^ 3 = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : (⟨ψ, hψD⟩ : Dl) ^ 3 = 1 := Subtype.ext hψ
    rw [this]
    rfl
  have hyd : orderOf y ∣ Nat.card (Dl ⧸ (inner T).subgroupOf Dl) := orderOf_dvd_natCard y
  have hyo : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hyp
  have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hyo hyd
  have hy1 : y = 1 := orderOf_eq_one_iff.1 this
  rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
  exact hy1

theorem primePower_card_three {q : PrimePower} (hq : q.card = 3) : q.p = 3 ∧ q.exponent = 1 := by
  have h1 : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp h1
  refine ⟨hp, ?_⟩
  have h2 : 3 ^ q.exponent = 3 ^ 1 := by
    have h3 := hq
    rw [PrimePower.card_def, hp] at h3
    rw [h3]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2

theorem aut_three_inner_of_A_two {G : Type} [Group G] {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.card = 3)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) (ψ : MulAut G) (hψ : ψ ^ 3 = 1) :
    ∃ a : G, ψ = MulAut.conj a := by
  obtain ⟨hp, he⟩ := primePower_card_three hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e' : G ≃* LinearFlag.projectiveSL (2 + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (2 + 1) _))
  have hK : Nat.card (GaloisField q.p q.exponent) = 3 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hp, he]
    norm_num
  obtain ⟨a, ha⟩ := aut_three_inner_projectiveSL_three hK (MulAut.congr e' ψ)
    (by rw [← map_pow, hψ, map_one])
  refine ⟨e'.symm a, ?_⟩
  apply (MulAut.congr e').injective
  rw [ha]
  ext s
  simp [MulAut.congr_apply]

theorem aut_three_inner_of_twistedA_two {G : Type} [Group G] {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) (ψ : MulAut G) (hψ : ψ ^ 3 = 1) :
    ∃ a : G, ψ = MulAut.conj a := by
  obtain ⟨hp, he⟩ := primePower_card_three hq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨⟨hℓ, hf, hn, hq'⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq'' : ¬(2 + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq' (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 2 + 1) (K := K))
  let e' : G ≃* primeFormP h ((1 : GL (Fin (2 + 1)) K) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hinner := aut_three_inner_primeFormP h (n := 2 + 1) (by omega) hq''
    (by rw [he]; decide) (by rw [hp, he]; decide) (MulAut.congr e' ψ)
    (by rw [← map_pow, hψ, map_one])
  obtain ⟨a, ha⟩ := hinner
  refine ⟨e'.symm a, ?_⟩
  apply (MulAut.congr e').injective
  rw [← ha]
  ext s
  simp [MulAut.congr_apply]

end Aut

section Orders

theorem not_dvd_card_PSL_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    ¬ 3 ^ 4 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h1 := h.trans (Subgroup.index_dvd_card
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem not_dvd_card_statedProj_SU_three {K : Type} [Field K] [Finite K] {Q : ℕ}
    (hQ : Q = 3 ^ 1) (hK : Nat.card K = Q ^ 2) [CharP K 3] :
    ¬ 3 ^ 4 ∣ Nat.card (CFSG.Open.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 Q K)) := by
  subst hQ
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := h.trans (Subgroup.index_dvd_card _)
  rw [CFSG.SectionRank.OddCover.card_statedSU_three (p := 3) (f := 1) hK] at h1
  norm_num at h1

end Orders

section Exclusion

variable {X : Type} [Group X] [Finite X]

theorem false_of_A_two_setup {L : Subgroup X} {x : X} (h : T29Setup X L x)
    (hZ : center ↥L = ⊥) {q : PrimePower} (hv : (LieTypeIndex.A 2 q).Valid)
    (hq : q.card = 3) (e : (↥L ⧸ center ↥L) ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) :
    False := by
  have hC := h.centralizer_eq_bot hZ
  have hall : ∀ g : X, g ^ 3 = 1 → g ∈ L := by
    intro g hg
    obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_of_inner e
      (fun ψ hψ => aut_three_inner_of_A_two hv hq (MulEquiv.refl _) ψ hψ) hg
    rw [hC, Subgroup.mem_bot] at hc
    rw [hc, mul_one]
    exact hl
  obtain ⟨hp, he⟩ := primePower_card_three hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = 3 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hp, he]
    norm_num
  have hcard : Nat.card ↥L = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (2 + 1))
      (GaloisField q.p q.exponent)) :=
    Nat.card_congr ((mulEquivQuotientCenter hZ).trans
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))).toEquiv
  have h4 : ¬ 3 ^ 4 ∣ Nat.card ↥L := by
    rw [hcard]
    exact not_dvd_card_PSL_three hK
  have h3 := three_le_pRank_centralizer_of_sylow h4 hall h.rank h.ord
  rw [h.cent] at h3
  omega

theorem false_of_twistedA_two_setup {L : Subgroup X} {x : X} (h : T29Setup X L x)
    (hZ : center ↥L = ⊥) {q : PrimePower} (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (hq : q.card = 3)
    (e : (↥L ⧸ center ↥L) ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) :
    False := by
  have hC := h.centralizer_eq_bot hZ
  have hall : ∀ g : X, g ^ 3 = 1 → g ∈ L := by
    intro g hg
    obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_of_inner e
      (fun ψ hψ => aut_three_inner_of_twistedA_two hv hq (MulEquiv.refl _) ψ hψ) hg
    rw [hC, Subgroup.mem_bot] at hc
    rw [hc, mul_one]
    exact hl
  obtain ⟨hp, he⟩ := primePower_card_three hq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
    (MulEquiv.refl (ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq'⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP K 3 := by
    have := (UnitaryFieldData.mk hℓ hf (by rw [hK, ← pow_mul, mul_comm] : Nat.card K = q.p ^
      (2 * q.exponent))).charP
    rwa [hp] at this
  have hcard : Nat.card ↥L = Nat.card (CFSG.Open.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (q.p ^ q.exponent) K)) :=
    Nat.card_congr ((mulEquivQuotientCenter hZ).trans (e.trans eT)).toEquiv
  have h4 : ¬ 3 ^ 4 ∣ Nat.card ↥L := by
    rw [hcard]
    exact not_dvd_card_statedProj_SU_three (by rw [hp, he]) hK
  have h3 := three_le_pRank_centralizer_of_sylow h4 hall h.rank h.ord
  rw [h.cent] at h3
  omega

end Exclusion

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
