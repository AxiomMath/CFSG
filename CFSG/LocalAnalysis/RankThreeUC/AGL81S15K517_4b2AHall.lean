module

public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.ClassicalGroups.Unitary.ComponentCartanUnitary
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.GroupTheory.CartanLiftCentral
public import CFSG.GroupTheory.IsMulCommutativeComapPcore
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bGenericHall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorel2A
public import CFSG.ClassicalGroups.Unitary.ComponentBorelUnitary

public section

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise commutatorElement

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem isMulCommutative_hypBorel_quotient {p f : ℕ} {K : Type} [Field K] [Finite K]
    {r ε : ℕ} (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (hp : p = 2) (hε : ε ≤ 1) (hr : 1 ≤ r) :
    IsMulCommutative (↥(hypBorel h r ε) ⧸ CFSG.pCore 2 ↥(hypBorel h r ε)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U' : Subgroup ↥(hypBorel h r ε) :=
    (hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)
  have hU2 : IsPGroup 2 (hypUnitriangular h r ε) := by
    rw [← hp]
    exact isPGroup_hypUnitriangular_of_sylow h hr hε
  have hU'2 : IsPGroup 2 U' :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe (hypUnitriangular_le_hypBorel h)).symm
  have hU'norm : U'.Normal := normal_hypUnitriangular hε
  have hquotcard : Nat.card (↥(hypBorel h r ε) ⧸ U') =
      Nat.card (hypDiagHom h r ε hε).range := by
    rw [show Nat.card (↥(hypBorel h r ε) ⧸ U') = U'.index from
        (Subgroup.index_eq_card _).symm,
      ← Subgroup.index_ker (hypDiagHom h r ε hε), ker_hypDiagHom hε]
  have hoddquot : Odd (Nat.card (↥(hypBorel h r ε) ⧸ U')) := by
    rw [hquotcard]
    have hbig : Odd (Nat.card (Fin r → Kˣ)) := by
      haveI : CharP K 2 := hp ▸ h.charP
      have hKodd : Odd (Nat.card K - 1) :=
        CFSG.ClassicalGroups.SpecialLinear.odd_card_sub_one_of_char_two
      have hunits : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
      have hfun : Nat.card (Fin r → Kˣ) = Nat.card Kˣ ^ r := by
        rw [Nat.card_fun, Nat.card_fin]
      rw [hfun, hunits]
      exact hKodd.pow
    have htop : Odd (Nat.card (⊤ : Subgroup (Fin r → Kˣ))) := by simpa using hbig
    exact Odd.of_dvd_nat htop (Subgroup.card_dvd_of_le (le_top :
      (hypDiagHom h r ε hε).range ≤ ⊤))
  have hidx : ¬ 2 ∣ U'.index := by
    rw [Subgroup.index_eq_card]
    exact hoddquot.not_two_dvd_nat
  let P : Sylow 2 ↥(hypBorel h r ε) := hU'2.toSylow hidx
  have hP : (P : Subgroup ↥(hypBorel h r ε)) = U' := IsPGroup.toSylow_coe hU'2 hidx
  have hpc : CFSG.pCore 2 ↥(hypBorel h r ε) = U' := by
    refine le_antisymm ?_ (le_sSup ⟨hU'norm, hU'2⟩)
    haveI : (CFSG.pCore 2 ↥(hypBorel h r ε)).Normal := CFSG.pCore_normal
    have := CFSG.pCore_isPGroup (p := 2) (G := ↥(hypBorel h r ε))
    exact (this.le_sylow_of_normal P).trans (le_of_eq hP)
  have hcomm : ⁅(⊤ : Subgroup ↥(hypBorel h r ε)),
      (⊤ : Subgroup ↥(hypBorel h r ε))⁆ ≤ U' := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h1 : hypDiagHom h r ε hε ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm (hypDiagHom h r ε hε x)
        (hypDiagHom h r ε hε y))
    have h1' : ⁅x, y⁆ ∈ (hypDiagHom h r ε hε).ker := MonoidHom.mem_ker.mpr h1
    rwa [ker_hypDiagHom hε] at h1'
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
    rw [hpc]
    exact hcomm)

theorem exists_hc_comap_of_isPi_ker {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    (pi : L →* Q) (hpi : Function.Surjective pi)
    (hpi_pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} pi.ker)
    {q : ℕ} (hq : q.Prime) (hqker : ¬ q ∣ Nat.card pi.ker)
    {HcQ : Subgroup Q}
    (hHcQpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} HcQ)
    (hHcQrk : 3 ≤ CFSG.Open.pRank q HcQ) :
    ∃ Hc : Subgroup L, IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨HcQ.comap pi, ?_, ?_⟩
  · intro p hp
    have hcard := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card pi hpi HcQ
    have hdvd : (p : ℕ) ∣ Nat.card pi.ker * Nat.card HcQ := by
      rwa [hcard] at hp
    rcases p.2.dvd_mul.mp hdvd with h1 | h1
    · exact hpi_pi p h1
    · exact hHcQpi p h1
  · have hmap : (HcQ.comap pi).map pi = HcQ :=
      Subgroup.map_comap_eq_self_of_surjective hpi HcQ
    have hrank := CFSG.pRank_map_eq_of_not_dvd_card_ker pi hpi hq hqker (HcQ.comap pi)
    rw [hmap] at hrank
    rw [← hrank]
    exact hHcQrk

end CFSG.LocalAnalysis.RankThreeUC.S15

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem transport_K
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup K} (hUmax : IsSylowTwoOf U ⊤) :
    (∃ Hc : Subgroup K, Hc ≤ Subgroup.normalizer (U : Set K) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc) ∧
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set K)) ∧
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set K)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set K))) := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he : 0 < Q.exponent := Q.exponent_pos
  let ef := Q.exponent
  let F := GaloisField 2 (2 * ef)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := inferInstance
  have hFcard : Nat.card F = (2 ^ ef) ^ 2 := by
    rw [GaloisField.card (p := 2) (n := 2 * ef) (by omega), Nat.mul_comm 2 ef, pow_mul]
  have hFcard' : Fintype.card F = (2 ^ ef) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hFcard
  have hring : ringChar F = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (by
      simpa using (CharP.cast_eq_zero F 2))
  have hQcardpow : Q.card = 2 ^ ef := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hm1 : 3 ≤ m + 1 := by omega
  have hne : (m + 1, 2 ^ ef) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    omega
  obtain ⟨q', hv', hq'p, hq'card, ⟨eAd⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (m := m + 1) (q := 2 ^ ef) (K := F) hFcard' hm1 hne
  have hq'p2 : q'.p = 2 := by rw [hq'p, hring]
  have hpow : q'.p ^ q'.exponent = Q.p ^ Q.exponent := by
    rw [← TauCeti.PrimePower.card_def q', ← TauCeti.PrimePower.card_def Q,
      hq'card, hQcardpow]
  have hexp : q'.exponent = Q.exponent := by
    have h2 : 2 ^ q'.exponent = 2 ^ Q.exponent := by
      simpa [hq'p2, hQ] using hpow
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h2
  have hqeq : q' = Q := by
    cases q' with
    | mk p1 e1 hp1 he1 =>
      cases Q with
      | mk p2 e2 hp2 he2 =>
        simp only at hq'p2 hexp hQ
        subst hq'p2
        subst hexp
        subst hQ
        rfl
  cases hqeq
  have eAd' : (StatedSU (m + 1) (2 ^ ef) F) ⧸
      Subgroup.center (StatedSU (m + 1) (2 ^ ef) F) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩).Group := by
    simpa [Nat.add_sub_cancel] using eAd
  let hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 ef F :=
    CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFcard
  let r := (m + 1) / 2
  let ε := (m + 1) % 2
  have hε : ε ≤ 1 := by
    have := Nat.mod_lt (m + 1) (by norm_num : 0 < 2); omega
  have hr : 3 ≤ r := by
    have h6 : 6 ≤ m + 1 := by omega
    have hdiv : 6 / 2 ≤ (m + 1) / 2 := Nat.div_le_div_right h6
    simpa [r] using hdiv
  have hr1 : 1 ≤ r := by omega
  have hn : 2 * r + ε = m + 1 := by
    have := Nat.div_add_mod (m + 1) 2; omega
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport hUF
  let eP := CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj hUF hR
    (r := r) (ε := ε) (by omega)
  let eP' : hypPSU hUF r ε ≃* StatedProj (StatedSU (m + 1) (2 ^ ef) F) := by
    rw [← hn]
    exact eP
  have hcenterS := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := ef) (n := m + 1) hFcard hm1 hne).2
  let eQ : (StatedSU (m + 1) (2 ^ ef) F) ⧸
      Subgroup.center (StatedSU (m + 1) (2 ^ ef) F) ≃*
      StatedProj (StatedSU (m + 1) (2 ^ ef) F) :=
    QuotientGroup.quotientMulEquivOfEq hcenterS
  let eKP : K ⧸ Subgroup.center K ≃* hypPSU hUF r ε :=
    (e.trans eAd'.symm).trans (eQ.trans eP'.symm)
  let qK : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let ρ : K →* StatedProj (StatedSU (m + 1) (2 ^ ef) F) :=
    eP'.toMonoidHom.comp (eKP.toMonoidHom.comp qK)
  have hρ : Function.Surjective ρ :=
    eP'.surjective.comp (eKP.surjective.comp (QuotientGroup.mk'_surjective _))
  have hρker : ρ.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : eKP (qK x) = 1 := eP'.injective (by simpa [ρ] using hx)
    have h2 : qK x = 1 := eKP.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff x).mp h2
  haveI : Group.IsPerfect K := ⟨hK.1⟩
  have hcop : Even (m + 1) → Nat.Coprime 2 (Nat.card ρ.ker) := by
    intro _
    exact Nat.coprime_two_left.2 (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hρker))
  obtain ⟨φ, hφ, hφρ⟩ :=
    CFSG.LieType.SeitzGeneration.exists_su_cover_hom (ℓ := 2) (f := ef) (n := m + 1)
      hFcard (by omega) (by omega) ρ hρ hρker hcop
  have hker_le_scalars : φ.ker ≤
      (StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (2 ^ ef) F) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ρ (φ x) = 1 := by rw [hx, map_one]
    have h2 : (QuotientGroup.mk' ((StatedScalars (Fin (m + 1)) F).subgroupOf
        (StatedSU (m + 1) (2 ^ ef) F))) x = 1 := by
      rw [← hφρ x]; exact h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hscalar_hd : ∀ c : Fˣ,
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c ∈
        StatedSU (m + 1) (2 ^ ef) F → c ^ (2 ^ ef + 1) = 1 :=
    fun c hc => ((CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hFcard
      (by omega) c).mp hc).2
  have hscalar_odd : Odd (Nat.card
      ((StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (2 ^ ef) F))) := by
    have hpd : ¬ 2 ∣ 2 ^ ef + 1 := by
      have hdvd2 : 2 ∣ 2 ^ ef := dvd_pow_self 2 (by omega)
      intro h
      exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_right hdvd2).mp h)
    have h := CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (M := StatedSU (m + 1) (2 ^ ef) F) (d := 2 ^ ef + 1) (p := 2)
      Nat.prime_two hpd hscalar_hd
    exact Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
  have hker_odd : Odd (Nat.card φ.ker) :=
    hscalar_odd.of_dvd_nat (Subgroup.card_dvd_of_le hker_le_scalars)
  have hker_pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} φ.ker := by
    intro p hp
    change (p : ℕ) ≠ 2
    intro hp2
    have hp' : 2 ∣ Nat.card φ.ker := by
      have hp'' := hp
      rw [hp2] at hp''
      exact hp''
    exact hker_odd.not_two_dvd_nat hp'
  have hdvdQ : q ∣ 2 ^ ef - 1 := by
    rw [← hQcardpow]; exact hdvd
  have hq_not_dvd_pow_add : ¬ q ∣ 2 ^ ef + 1 := by
    intro h
    have heq : 2 ^ ef + 1 = (2 ^ ef - 1) + 2 := by omega
    rw [heq] at h
    have h2 : q ∣ 2 := (Nat.dvd_add_right hdvdQ).mp h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
  have hq_not_dvd_scalars : ¬ q ∣ Nat.card
      ((StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (2 ^ ef) F)) :=
    CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (M := StatedSU (m + 1) (2 ^ ef) F) (d := 2 ^ ef + 1) (p := q)
      hq hq_not_dvd_pow_add hscalar_hd
  have hker_q : ¬ q ∣ Nat.card φ.ker := fun h =>
    hq_not_dvd_scalars (h.trans (Subgroup.card_dvd_of_le hker_le_scalars))
  let eSS : hypSU hUF r ε ≃* StatedSU (m + 1) (2 ^ ef) F := by
    rw [← hn]
    exact hypTransport hUF hR
  let U_S0 : Subgroup (StatedSU (m + 1) (2 ^ ef) F) :=
    (hypUnitriangular hUF r ε).map eSS.toMonoidHom
  let B_S0 : Subgroup (StatedSU (m + 1) (2 ^ ef) F) :=
    (hypBorel hUF r ε).map eSS.toMonoidHom
  have hB_S0norm : Subgroup.normalizer (U_S0 : Set (StatedSU (m + 1) (2 ^ ef) F)) =
      B_S0 := by
    rw [show U_S0 = (hypUnitriangular hUF r ε).map eSS.toMonoidHom from rfl,
      ← Subgroup.map_equiv_normalizer_eq (hypUnitriangular hUF r ε) eSS,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular
        hUF hr1 hε]
  have hU_S0_sylow : IsSylowTwoOf U_S0 ⊤ := by
    obtain ⟨-, ⟨P0, hP0⟩, -, -, -, -, -⟩ := unitary_order_and_Sylow hUF hr1 hε
    have hUsyl : IsSylowTwoOf (hypUnitriangular hUF r ε) ⊤ := by
      refine ⟨le_top, ?_, ?_⟩
      · rw [← hP0]; exact P0.isPGroup'
      · have h := P0.not_dvd_index
        rw [show (P0 : Subgroup (hypSU hUF r ε)) = hypUnitriangular hUF r ε from hP0] at h
        rw [show ((hypUnitriangular hUF r ε).subgroupOf ⊤).index =
          (hypUnitriangular hUF r ε).index from Subgroup.relIndex_top_right _]
        exact h
    have h := hUsyl.map_mulEquiv eSS
    simpa [U_S0, Subgroup.map_top_of_surjective eSS.toMonoidHom eSS.surjective] using h
  have hB_S0_comm : IsMulCommutative
      (↥B_S0 ⧸ CFSG.pCore 2 ↥B_S0) := by
    let eB : ↥(hypBorel hUF r ε) ≃* ↥B_S0 :=
      Subgroup.equivMapOfInjective _ eSS.toMonoidHom eSS.injective
    exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      eB.toMonoidHom eB.surjective
      (isMulCommutative_hypBorel_quotient hUF rfl hε hr1)
  have hB_S0_solv : Group.IsSolvable ↥B_S0 := by
    let eB : ↥(hypBorel hUF r ε) ≃* ↥B_S0 :=
      Subgroup.equivMapOfInjective _ eSS.toMonoidHom eSS.injective
    haveI : Group.IsSolvable ↥(hypBorel hUF r ε) :=
      isSolvable_hypBorel hUF hr1 hε
    exact Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective
  have hVsyl : IsSylowTwoOf (U_S0.map φ) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map φ hφ hU_S0_sylow
  obtain ⟨k, -, hk⟩ := hVsyl.exists_conj hUmax
  obtain ⟨s, hs⟩ := hφ k
  let U_S : Subgroup (StatedSU (m + 1) (2 ^ ef) F) :=
    U_S0.map (MulAut.conj s).toMonoidHom
  have hφU_S : U_S.map φ = U := by
    rw [hk]
    have hconj : (MulAut.conj k).toMonoidHom.comp φ =
        φ.comp (MulAut.conj s).toMonoidHom := by
      ext x
      change k * φ x * k⁻¹ = φ (s * x * s⁻¹)
      rw [map_mul, map_mul, map_inv, hs]
    calc U_S.map φ
        = U_S0.map (φ.comp (MulAut.conj s).toMonoidHom) := by
            rw [show U_S = U_S0.map (MulAut.conj s).toMonoidHom from rfl,
              Subgroup.map_map]
      _ = U_S0.map ((MulAut.conj k).toMonoidHom.comp φ) := by rw [← hconj]
      _ = (U_S0.map φ).map (MulAut.conj k).toMonoidHom :=
            (Subgroup.map_map _ _ _).symm
  have hU_S_sylow : IsSylowTwoOf U_S ⊤ := by
    have h := hU_S0_sylow.map_mulEquiv (MulAut.conj s)
    simpa [U_S, Subgroup.map_top_of_surjective (MulAut.conj s).toMonoidHom (MulAut.conj s).surjective] using h
  let B_S : Subgroup (StatedSU (m + 1) (2 ^ ef) F) :=
    Subgroup.normalizer (U_S : Set (StatedSU (m + 1) (2 ^ ef) F))
  have hB_S_norm : B_S = B_S0.map (MulAut.conj s).toMonoidHom := by
    rw [show B_S = Subgroup.normalizer (U_S0.map (MulAut.conj s).toMonoidHom :
        Set (StatedSU (m + 1) (2 ^ ef) F)) from rfl,
      ← Subgroup.map_equiv_normalizer_eq U_S0 (MulAut.conj s), hB_S0norm]
  have hB_S_comm : IsMulCommutative (↥B_S ⧸ CFSG.pCore 2 ↥B_S) := by
    let eC : ↥B_S0 ≃* ↥B_S :=
      (Subgroup.equivMapOfInjective B_S0 (MulAut.conj s).toMonoidHom
        (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hB_S_norm).symm
    exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      eC.toMonoidHom eC.surjective hB_S0_comm
  have hB_S_solv : Group.IsSolvable ↥B_S := by
    let eC : ↥B_S0 ≃* ↥B_S :=
      (Subgroup.equivMapOfInjective B_S0 (MulAut.conj s).toMonoidHom
        (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hB_S_norm).symm
    exact Group.isSolvable_of_surjective (f := eC.toMonoidHom) eC.surjective
  have hcopker : Nat.Coprime 2 (Nat.card φ.ker) :=
    Nat.coprime_two_left.2 hker_odd
  haveI : Fact (IsPGroup 2 U_S) := ⟨hU_S_sylow.2.1⟩
  have hNq := CFSG.normalizer_map_quotient_eq_map_normalizer (G :=
      StatedSU (m + 1) (2 ^ ef) F) 2 U_S (MonoidHom.ker φ) inferInstance hcopker
  let eΦ : (StatedSU (m + 1) (2 ^ ef) F) ⧸ MonoidHom.ker φ ≃* K :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hcomp : eΦ.toMonoidHom.comp (QuotientGroup.mk' (MonoidHom.ker φ)) = φ := by
    ext x; rfl
  have hUmap : (U_S.map (QuotientGroup.mk' (MonoidHom.ker φ))).map eΦ.toMonoidHom = U := by
    rw [Subgroup.map_map, hcomp, hφU_S]
  have hNK : Subgroup.normalizer (U : Set K) = B_S.map φ := by
    calc Subgroup.normalizer (U : Set K)
        = Subgroup.normalizer ((U_S.map (QuotientGroup.mk' (MonoidHom.ker φ))).map
            eΦ.toMonoidHom : Set K) := by rw [hUmap]
      _ = (Subgroup.normalizer (U_S.map (QuotientGroup.mk' (MonoidHom.ker φ)))).map
            eΦ.toMonoidHom := (Subgroup.map_equiv_normalizer_eq _ eΦ).symm
      _ = ((Subgroup.normalizer (U_S : Set _)).map
            (QuotientGroup.mk' (MonoidHom.ker φ))).map eΦ.toMonoidHom := by rw [hNq]
      _ = B_S.map φ := by rw [Subgroup.map_map, hcomp]
  have hsolvN : Group.IsSolvable ↥(Subgroup.normalizer (U : Set K)) := by
    rw [hNK]
    let eB : ↥B_S →* ↥(B_S.map φ) :=
      (φ.comp B_S.subtype).codRestrict _ (fun x => Subgroup.mem_map_of_mem φ x.2)
    have heB : Function.Surjective eB := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Group.isSolvable_of_surjective (f := eB) heB
  have hcommN : IsMulCommutative
      (↥(Subgroup.normalizer (U : Set K)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set K))) := by
    rw [hNK]
    let eB : ↥B_S →* ↥(B_S.map φ) :=
      (φ.comp B_S.subtype).codRestrict _ (fun x => Subgroup.mem_map_of_mem φ x.2)
    have heB : Function.Surjective eB := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      eB heB hB_S_comm
  have hUsyl_std : IsSylowTwoOf (hypProjUnitriangular hUF r ε) ⊤ := by
    obtain ⟨-, -, -, -, ⟨P0, hP0⟩, -, -⟩ := unitary_order_and_Sylow hUF hr1 hε
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hP0]; exact P0.isPGroup'
    · have h := P0.not_dvd_index
      rw [show (P0 : Subgroup (hypPSU hUF r ε)) = hypProjUnitriangular hUF r ε from hP0] at h
      rw [show ((hypProjUnitriangular hUF r ε).subgroupOf ⊤).index =
        (hypProjUnitriangular hUF r ε).index from Subgroup.relIndex_top_right _]
      exact h
  have hUbar_sylow : IsSylowTwoOf (U.map (eKP.toMonoidHom.comp qK)) ⊤ := by
    have h1 : IsSylowTwoOf (U.map qK) ⊤ :=
      CFSG.Quasithin.A312.isSylowTwoOf_top_map qK (QuotientGroup.mk'_surjective _) hUmax
    have h2 := h1.map_mulEquiv eKP
    simpa [Subgroup.map_map, Subgroup.map_top_of_surjective eKP.toMonoidHom eKP.surjective] using h2
  obtain ⟨H0, hH0N, hH0pi, hH0rk⟩ :=
    exists_piSubgroup_three_le_pRank_in_borel_projective_unitary_split hUF hr hε hq hq2 hdvdQ
  obtain ⟨g, -, hg⟩ := hUsyl_std.exists_conj hUbar_sylow
  let HcP : Subgroup (hypPSU hUF r ε) := H0.map (MulAut.conj g).toMonoidHom
  have hHcPN : HcP ≤ Subgroup.normalizer
      ((U.map (eKP.toMonoidHom.comp qK)) : Set (hypPSU hUF r ε)) := by
    calc HcP ≤ (Subgroup.normalizer (hypProjUnitriangular hUF r ε :
          Set (hypPSU hUF r ε))).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hH0N
      _ = Subgroup.normalizer ((hypProjUnitriangular hUF r ε).map
            (MulAut.conj g).toMonoidHom : Set (hypPSU hUF r ε)) :=
          Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g)
      _ = Subgroup.normalizer ((U.map (eKP.toMonoidHom.comp qK)) :
            Set (hypPSU hUF r ε)) := by rw [← hg]
  have hHcPpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} HcP :=
    CFSG.LocalCores.isPiSubgroup_map hH0pi _
  have hHcPrk : 3 ≤ CFSG.Open.pRank q HcP := by
    rw [show CFSG.Open.pRank q HcP = CFSG.Open.pRank q H0 from
      CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) hq H0]
    exact hH0rk
  let N := Subgroup.normalizer (U : Set K)
  let Nbar : Subgroup (hypPSU hUF r ε) := (N.map qK).map eKP.toMonoidHom
  have hNbar_eq : (Subgroup.normalizer ((U.map (eKP.toMonoidHom.comp qK)) :
      Set (hypPSU hUF r ε))) = Nbar := by
    have hcopZ : Nat.Coprime 2 (Nat.card (Subgroup.center K)) :=
      Nat.coprime_two_left.2 hodd
    haveI : Fact (IsPGroup 2 U) := ⟨hUmax.2.1⟩
    have hNq' := CFSG.normalizer_map_quotient_eq_map_normalizer (G := K) 2 U
      (Subgroup.center K) inferInstance hcopZ
    calc Subgroup.normalizer ((U.map (eKP.toMonoidHom.comp qK)) : Set (hypPSU hUF r ε))
        = Subgroup.normalizer ((U.map qK).map eKP.toMonoidHom :
            Set (hypPSU hUF r ε)) := by rw [Subgroup.map_map]
      _ = (Subgroup.normalizer (U.map qK : Set (K ⧸ Subgroup.center K))).map
            eKP.toMonoidHom := (Subgroup.map_equiv_normalizer_eq _ eKP).symm
      _ = ((Subgroup.normalizer (U : Set K)).map qK).map eKP.toMonoidHom := by rw [hNq']
      _ = Nbar := rfl
  have hHcPNbar : HcP ≤ Nbar := by rw [← hNbar_eq]; exact hHcPN
  have hHcBar_pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} (HcP.subgroupOf Nbar) := by
    intro p hp
    refine hHcPpi p ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHcPNbar).toEquiv] at hp
  have hHcBar_rk : 3 ≤ CFSG.Open.pRank q (HcP.subgroupOf Nbar) := by
    have hmap : (HcP.subgroupOf Nbar).map Nbar.subtype = HcP := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHcPNbar]
    have hEq := CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt
      Nbar.subtype Nbar.subtype_injective (HcP.subgroupOf Nbar)
    rw [hmap] at hEq
    rw [← hEq]
    exact hHcPrk
  let κ : ↥N →* ↥Nbar :=
    { toFun := fun x => ⟨eKP (qK x.1), Subgroup.mem_map_of_mem eKP.toMonoidHom
        (Subgroup.mem_map_of_mem qK x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hκ_surj : Function.Surjective κ := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨x, hx⟩, Subtype.ext hzy⟩
  have hcenter_le_N : Subgroup.center K ≤ N := Subgroup.center_le_normalizer (U : Set K)
  have hκker_eq : κ.ker = (Subgroup.center K).subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hxe : eKP (qK (x : K)) = 1 := by
        have := congrArg Subtype.val h
        simpa [κ] using this
      have hxe' : eKP (qK (x : K)) = eKP 1 := by simpa using hxe
      exact (QuotientGroup.eq_one_iff (x : K)).mp (eKP.injective hxe')
    · intro h
      have h1 : qK (x : K) = 1 := (QuotientGroup.eq_one_iff (x : K)).mpr h
      show κ x = 1
      ext
      simp [κ, h1]
  have hκker_card : Nat.card κ.ker = Nat.card (Subgroup.center K) := by
    rw [hκker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenter_le_N).toEquiv
  haveI : Group.IsPerfect (StatedSU (m + 1) (2 ^ ef) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := ef) (n := m + 1) hFcard hm1 hne).1.1
  have hker_le_centerS : φ.ker ≤ Subgroup.center (StatedSU (m + 1) (2 ^ ef) F) := by
    rw [hcenterS]; exact hker_le_scalars
  have hcenterK_dvd : Nat.card (Subgroup.center K) ∣ Nat.card
      ((StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (2 ^ ef) F)) := by
    rw [← hcenterS, ← CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      φ hφ hker_le_centerS]
    exact Subgroup.card_map_dvd _ φ
  have hscalar_pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2}
      ((StatedScalars (Fin (m + 1)) F).subgroupOf (StatedSU (m + 1) (2 ^ ef) F)) := by
    intro p hp
    change (p : ℕ) ≠ 2
    intro hp2
    have hp' : 2 ∣ Nat.card ((StatedScalars (Fin (m + 1)) F).subgroupOf
        (StatedSU (m + 1) (2 ^ ef) F)) := by
      have hp'' := hp
      rw [hp2] at hp''
      exact hp''
    exact hscalar_odd.not_two_dvd_nat hp'
  have hκ_pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} κ.ker := by
    intro p hp
    apply hscalar_pi p
    rw [hκker_card] at hp
    exact hp.trans hcenterK_dvd
  have hκ_q : ¬ q ∣ Nat.card κ.ker := by
    intro h
    apply hq_not_dvd_scalars
    rw [hκker_card] at h
    exact h.trans hcenterK_dvd
  obtain ⟨HcN, hHcNpi, hHcNrk⟩ :=
    exists_hc_comap_of_isPi_ker κ hκ_surj hκ_pi hq hκ_q hHcBar_pi hHcBar_rk
  refine ⟨⟨HcN.map N.subtype, ?_, ?_, ?_⟩, hsolvN, hcommN⟩
  · exact (Subgroup.map_subtype_le HcN).trans (le_refl N)
  · exact CFSG.LocalCores.isPiSubgroup_map hHcNpi N.subtype
  · have hmap : HcN.map N.subtype = HcN.map N.subtype := rfl
    have hEq := CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt
      N.subtype N.subtype_injective HcN
    rw [hEq]
    exact hHcNrk

end CFSG.LocalAnalysis.RankThreeUC.S15

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem transport_L
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : IsSylowTwoOf U ⊤) :
    (∃ Hc : Subgroup L, Hc ≤ Subgroup.normalizer (U : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc) ∧
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) ∧
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup L := CFSG.Open.pCoreOf 2 (Subgroup.center L)
  have hO_center : O ≤ Subgroup.center L := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _
  haveI hO_normal : O.Normal := Subgroup.normal_of_le_center hO_center
  have hO_2 : IsPGroup 2 O := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _
  have hO_le_U : O ≤ U := by
    have hidxU : ¬ 2 ∣ U.index := by
      have h := hUmax.2.2
      rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at h
      exact h
    let P : Sylow 2 L := hUmax.2.1.toSylow hidxU
    have hP : (P : Subgroup L) = U := IsPGroup.toSylow_coe _ _
    have := hO_2.le_sylow_of_normal P
    rwa [hP] at this
  let K := L ⧸ O
  have hK : CFSG.Open.IsQuasisimple K :=
    CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hL
  have hoddK : Odd (Nat.card (Subgroup.center K)) :=
    CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hL
  let eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group :=
    (CFSG.GroupTheory.quotientPCoreOfCenterEquiv hL).trans e
  let U_K : Subgroup K := U.map (QuotientGroup.mk' O)
  have hU_K : IsSylowTwoOf U_K ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) hUmax
  obtain ⟨⟨HcK, hHcKN, hHcKpi, hHcKrk⟩, hsolvK, hcommK⟩ :=
    transport_K hK hoddK hm hQ eK hQcard hq hq2 hdvd hU_K
  have hcomap : Subgroup.comap (QuotientGroup.mk' O) U_K = U := by
    rw [show U_K = U.map (QuotientGroup.mk' O) from rfl,
      QuotientGroup.comap_map_mk', sup_eq_right.mpr hO_le_U]
  obtain ⟨E, hEHc, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (H := HcK) (k := 3) hHcKrk
  have hEpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} E := fun p hp =>
    hHcKpi p (hp.trans (Subgroup.card_dvd_of_le hEHc))
  have hErk : 3 ≤ CFSG.Open.pRank q E := by
    exact CFSG.SectionRank.le_pRank hq.one_lt le_rfl hEelem hEcard
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    CFSG.Open.IsElemAbelian.comm hEelem ha hb
  have hker_center : (QuotientGroup.mk' O).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']; exact hO_center
  obtain ⟨Hc, hHcN, hHcpi, hHcrk⟩ :=
    CFSG.exists_cartan_in_borel_of_central_comap (e := QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) hker_center (by
        rw [QuotientGroup.ker_mk']; exact hO_2) hq hq2
      (hEHc.trans hHcKN) hEab hEpi hErk
  have hHcN' : Hc ≤ Subgroup.normalizer (U : Set L) := by
    rw [← hcomap]
    exact hHcN
  have hNK : Subgroup.normalizer (U : Set L) =
      Subgroup.comap (QuotientGroup.mk' O) (Subgroup.normalizer (U_K : Set K)) := by
    rw [show U_K = U.map (QuotientGroup.mk' O) from rfl]
    have h := (Subgroup.comap_normalizer_eq_of_surjective
      (U.map (QuotientGroup.mk' O)) (QuotientGroup.mk'_surjective O)).symm
    rwa [QuotientGroup.comap_map_mk', sup_eq_right.mpr hO_le_U] at h
  have hsolvL : Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) := by
    rw [hNK]
    exact CFSG.GroupTheory.isSolvable_comap_of_isPGroup_ker (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) hsolvK (by
        rw [QuotientGroup.ker_mk']; exact hO_2)
  have hcommL : IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
    rw [hNK]
    exact CFSG.isMulCommutative_comap_quotient_pCore (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) (by rw [QuotientGroup.ker_mk']; exact hO_2) hcommK
  exact ⟨⟨Hc, hHcN', hHcpi, hHcrk⟩, hsolvL, hcommL⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem exists_hc_twistedA
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ Hc : Subgroup L, Hc ≤ Subgroup.normalizer (U : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc :=
  (transport_L hL hm hQ e hQcard hq hq2 hdvd hUmax).1

theorem isSolvable_normalizer_sylow_of_component_twistedA
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) :=
  (transport_L hL hm hQ e hQcard hq hq2 hdvd hUmax).2.1

theorem isMulCommutative_normalizer_quotient_pCore_of_component_twistedA
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) :=
  (transport_L hL hm hQ e hQcard hq hq2 hdvd hUmax).2.2

theorem noXBlock_borelPre_subtype_2A
    {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) :
    ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hsub hblock
  let H : Subgroup X := borelPre T Ls
  let Y' : Subgroup X := Y.map H.subtype
  have hY' : Y' ≤ H := Subgroup.map_subtype_le (H := H) Y
  have hsub' : IsSubnormal Y' H := by
    have h := CFSG.Open.IsSubnormal.map (f := H.subtype) hsub
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hblock' : InClassXBlock Y' := by
    have hx : CFSG.RankThree.PartOne.InClassX ↥Y :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hblock
    let eY : ↥Y ≃* ↥Y' :=
      Subgroup.equivMapOfInjective Y H.subtype H.subtype_injective
    have hx' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv eY hx
    exact CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hx'
  exact noXBlock_borelPre_done_2A hX hLs hinv m hm Q hQ hv e Y' hY' hsub' hblock'

theorem k517_4b_2A_of_top_of_hall
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls) (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 5 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  have hQcard : 4 ≤ Q.card := by
    have hpow : Q.card = 2 ^ Q.exponent := by
      rw [TauCeti.PrimePower.card_def, hQ]
    have h2le : 2 ≤ Q.card := by
      rw [hpow]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) Q.exponent_pos
    have hdiv : 2 ∣ Q.card := by
      rw [hpow]
      exact dvd_pow_self 2 Q.exponent_pos.ne'
    have hne2 : Q.card ≠ 2 := by
      intro h2
      have h2' : Q.card - 1 = 1 := by omega
      exact hq.not_dvd_one (h2' ▸ hqQ)
    rcases Nat.lt_or_ge Q.card 4 with hlt | hge
    · rcases Nat.lt_or_ge Q.card 2 with h1 | h1
      · omega
      · interval_cases Q.card
        · exact absurd rfl hne2
        · exact absurd hdiv (by norm_num)
    · exact hge
  have hHc : ∃ Hc : Subgroup ↥Ls, Hc ≤ Subgroup.normalizer (U : Set ↥Ls) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧ 3 ≤ CFSG.Open.pRank q Hc :=
    exists_hc_twistedA (L := ↥Ls) (m := m) (Q := Q) (hv := hv)
      hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax
  have hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False :=
    noXBlock_borelPre_subtype_2A hX hLs.1 hTinv m (by omega) Q hQ hv e
  have hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
    isSolvable_gnImg_borelPre_of_borel hX hTinv hU
      (isSolvable_normalizer_sylow_of_component_twistedA (L := ↥Ls) (m := m) (Q := Q)
        (hv := hv) hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax)
  obtain ⟨hB, hHallB, hcommBY⟩ :=
    k517_4b_normalizer_data_of_mulCommutative hX hGood hLs hTinv hU
      (isMulCommutative_normalizer_quotient_pCore_of_component_twistedA (L := ↥Ls) (m := m)
        (Q := Q) (hv := hv) hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax)
  have hBLs : (Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls).subgroupOf (gnImg T (borelPre T Ls)) ≤
      Ls.subgroupOf (gnImg T (borelPre T Ls)) := by
    intro y hy
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
  exact k517_4b_of_setting_of_hall hX hGood hLs hq hq2 hHc hU hNB hsolvY hB hHallB hcommBY hBLs

end CFSG.LocalAnalysis.RankThreeUC.S15
