module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M1
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace T7X

theorem not_mem_inf_of_orderOf_four (hΩ : HypOmegaGen Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {u : G} (hu4 : orderOf u = 4) (huK : u ∈ K)
    (huK' : u ∈ K') : False := by
  have := Sec6Gen.eq_of_le_of_le hΩ hK hK' (T7A.isPGroup_zpowers_of_orderOf_four hu4)
    (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr huK')
  exact hne this.symm

end T7X

theorem exists_twinSylow (hΩ : HypOmegaGen Ω)
    {K K' J : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) :
    ∃ (S : Sylow 2 G) (R R' T : Subgroup G), IsSylow2In R K ∧ IsSylow2In R' K' ∧
      IsSylow2In T J ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) ∧ T ≤ (S : Subgroup G) ∧
      Commutes R R' ∧ Commutes R T ∧ Commutes R' T := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  have hJK : J ∈ omegaNbr Ω K := hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := hJ.2 K' hK'
  obtain ⟨-, hJneK, T, hT, hTJ, hTN⟩ := hJK
  have hJneK' : J ≠ K' := hJK'.2.1
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hz hTN
  have hTN' : T ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hJΩ hJneK'.symm hzK' hTJ hT2 (by omega) hTc
  obtain ⟨R, hRsyl, hRfix⟩ := exists_sylow_normalized hT2 hTN
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hTnR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix t ht)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hRsyl.2.1 hTnR
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hPN : T ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hTN' (hRsyl.1.trans hKN)
  obtain ⟨R', hR'syl, hR'fix⟩ := exists_sylow_normalized hTR2 hPN
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  have hPnR' : T ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix t ht)
  have hQ2 : IsPGroup 2 ↥((T ⊔ R) ⊔ R') := hTR2.to_sup_of_normal_right' hR'syl.2.1 hPnR'
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hTS : T ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRR' : R ≠ R' := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm hRsyl.2.1 hRsyl.1 (h ▸ hR'syl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  have hRT : R ≠ T := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK hJΩ hJneK.symm hRsyl.2.1 hRsyl.1 (h ▸ hTsyl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  have hR'T : R' ≠ T := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK'Ω hJΩ hJneK'.symm hR'syl.2.1 hR'syl.1 (h ▸ hTsyl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hR'set
    omega
  exact ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS,
    Q3.Q3CP.l67Gen G Ω hΩ S R hRset R' hR'set hRS hR'S hRR',
    Q3.Q3CP.l67Gen G Ω hΩ S R hRset T hT hRS hTS hRT,
    Q3.Q3CP.l67Gen G Ω hΩ S R' hR'set T hT hR'S hTS hR'T⟩

theorem exists_mem_eta_of_sylow (hΩ : HypOmegaGen Ω) {S : Sylow 2 G}
    {η : Set (Subgroup G)} (hη : η ∈ etaSet Ω (S : Subgroup G)) {M T : Subgroup G} {w : G}
    (hM : M ∈ Ω) (hw : IsUniqueInvolution M w) (hT : IsSylow2In T M)
    (hTS : T ≤ (S : Subgroup G)) : w ∈ ⨆ U ∈ η, U := by
  have hTset : T ∈ RSet Ω := mem_RSet_of_isSylow2In hM hT
  have hquat := Sec6Gen.isQuatSub_of_mem_RSet hΩ hTset
  obtain ⟨U₀, hU₀T, hcyc, hcard⟩ := hquat.exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hM hT hU₀T hcyc hcard
  obtain ⟨V, hVη, hVM⟩ := Hat2A7M.Asc77.exists_mem_of_mem_etaSet hΩ hη hM ⟨hU₀, hU₀T.trans hTS⟩
    (hU₀T.trans hT.1)
  have hVU : V ∈ USet Ω := (hη.1 hVη).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have hwV : w ∈ V :=
    mem_of_isUniqueInvolution_of_isPGroup hw hVM (Sec6Gen.isPGroup_of_mem_USet hΩ hVU) (by omega)
  have hVW : V ≤ ⨆ U ∈ η, U := le_iSup₂_of_le V hVη le_rfl
  exact hVW hwV

theorem exists_twinFrameData (hΩ : HypOmegaGen Ω)
    {K K' J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) :
    ∃ (u : G) (W : Subgroup G), TwinFrameData Ω K K' z u J t ∧ W ∈ WSet Ω ∧ z ∈ W ∧ t ∈ W := by
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow   hΩ hK hz hK' hne hJ
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  obtain ⟨u₁, hu₁R, hu₁4⟩ := Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ hRset
  obtain ⟨u₂, hu₂R', hu₂4⟩ := Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ hR'set
  have hu₁K : u₁ ∈ K := hRsyl.1 hu₁R
  have hu₂K' : u₂ ∈ K' := hR'syl.1 hu₂R'
  have hsq₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hzK' hu₂K' hu₂4
  have hc : u₁ * u₂ = u₂ * u₁ := hRR' u₁ hu₁R u₂ hu₂R'
  have hu₁K' : u₁ ∉ K' := fun h => T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hu₁4 hu₁K h
  have hu₂K : u₂ ∉ K := fun h => T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hu₂4 h hu₂K'
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← hc]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [hsq₁, hsq₂, hz.sq]
  have hu1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁K'
    have : u₁ = u₂⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hu₂K'
  have huz : u₁ * u₂ ≠ z := by
    intro h
    apply hu₁K'
    have : u₁ = z * u₂⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hu₂K')
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup ht hTsyl.1 hT2 (by omega)
  have htu : t * (u₁ * u₂) = (u₁ * u₂) * t := by
    have h1 : u₁ * t = t * u₁ := hRT u₁ hu₁R t htT
    have h2 : u₂ * t = t * u₂ := hR'T u₂ hu₂R' t htT
    calc t * (u₁ * u₂) = (t * u₁) * u₂ := by group
      _ = (u₁ * t) * u₂ := by rw [h1]
      _ = u₁ * (t * u₂) := by group
      _ = u₁ * (u₂ * t) := by rw [h2]
      _ = (u₁ * u₂) * t := by group
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  have hzW := exists_mem_eta_of_sylow  hΩ hη hK hz hRsyl hRS
  have htW := exists_mem_eta_of_sylow  hΩ hη hJ.1 ht hTsyl hTS
  refine ⟨u₁ * u₂, ⨆ U ∈ η, U, ?_, hWmem, hzW, htW⟩
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁K) (Subgroup.mem_sup_right hu₂K')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ
      ht := ht
      htu := htu }

theorem kPerp_eq_of_mem_twinSet (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) {K L : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) (hL : L ∈ twinSet Ω K) :
    KPerp Ω K = KPerp Ω L := by
  have hzL := isUniqueInvolution_of_mem_twinSet hz hL
  ext M
  by_cases hM : M ∈ Ω
  · obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM
    rw [mem_kPerp_iff_normalizes_a7 hΩ hcl hK hM hz hu,
      mem_kPerp_iff_normalizes_a7 hΩ hcl hL.1 hM hzL hu]
  · have h1 : M ∉ KPerp Ω K := by
      rintro (h | h)
      · exact hM (h ▸ hK)
      · exact hM h.1
    have h2 : M ∉ KPerp Ω L := by
      rintro (h | h)
      · exact hM (h ▸ hL.1)
      · exact hM h.1
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem exists_mem_omegaOfSet_twinSet (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z)
    (hne : KPerp Ω K ≠ twinSet Ω K) : ∃ J ∈ omegaOfSet Ω (twinSet Ω K), J ∉ twinSet Ω K := by
  have hsub : twinSet Ω K ⊆ KPerp Ω K := fun L hL =>
    Hat2A7M.Asc77.mem_kPerp_of_twin hΩ hL.1 hK (isUniqueInvolution_of_mem_twinSet hz hL) hz
  by_contra hcon
  push Not at hcon
  have hJ : ∀ J ∈ KPerp Ω K, J ∈ twinSet Ω K := by
    intro J hJ
    by_contra hJnot
    have hJΩ : J ∈ Ω := by
      rcases Set.mem_insert_iff.mp hJ with h | h
      · exact h ▸ hK
      · exact h.1
    have hmem : J ∈ omegaOfSet Ω (twinSet Ω K) := by
      refine ⟨hJΩ, fun L hL => ?_⟩
      have hKL := kPerp_eq_of_mem_twinSet hΩ hcl hK hz hL
      have hJL : J ∈ KPerp Ω L := hKL ▸ hJ
      rcases Set.mem_insert_iff.mp hJL with h | h
      · exact absurd (h ▸ hL) hJnot
      · exact h
    exact hJnot (hcon J hmem)
  exact hne (Set.Subset.antisymm (fun J hJ' => hJ J hJ') hsub)

namespace T7X

theorem isSylow2In_sup_of_twin (hΩ : HypOmegaGen Ω) {K K' R R' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hc : Commutes R R') : IsSylow2In (R ⊔ R') (K ⊔ K') := by
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  have hprod := T7A.card_sup_mul_card_inf hKN
  rw [sup_comm] at hprod
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK' hR'
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have h8' : 8 ≤ Nat.card R' := Sec6Gen.eight_le_of_mem_RSet hΩ hR'set
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hR'.1 hR'.2.1 (by omega)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hN0 : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
  have hinfK : (Nat.card ↥(K ⊓ K')).factorization 2 = 1 := by
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := z) ⟨hz.mem, hz'.mem⟩
      rwa [hz2] at this
    have h1 : 1 ≤ (Nat.card ↥(K ⊓ K')).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hN0).mp hdvd
    have h2 : padicValNat 2 (Nat.card ↥(K ⊓ K')) ≤ 1 :=
      (hΩ.omega4 K hK K' hK' hne.symm).1
    rw [Nat.factorization_def _ Nat.prime_two] at h1 ⊢
    omega
  have hinfR : Nat.card ↥(R ⊓ R') = 2 := by
    refine le_antisymm ?_ ?_
    · exact Sec6Gen.card_le_two_of_le_inf hΩ hK hK' hne.symm (hR.2.1.to_le inf_le_left)
        (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
    · have h1 : Subgroup.zpowers z ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hzR, hzR'⟩
      have := Subgroup.card_le_of_le h1
      rwa [Nat.card_zpowers, hz2] at this
  have hRN : R' ≤ Subgroup.normalizer (R : Set G) := T7A.le_normalizer_of_commutes hc
  have hprodR := T7A.card_sup_mul_card_inf hRN
  rw [hinfR] at hprodR
  have ha := natCard_eq_pow_of_isSylow2In hR
  have hb := natCard_eq_pow_of_isSylow2In hR'
  have hQ0 : Nat.card ↥(K ⊔ K') ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hK'0 : Nat.card ↥K' ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K ⊔ K')).factorization 2 + 1 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥K').factorization 2 := by
    have := congrArg (fun n => n.factorization 2) hprod
    simp only [Nat.factorization_mul hQ0 hN0, Nat.factorization_mul hK0 hK'0, Finsupp.add_apply,
      hinfK] at this
    exact this
  have hRR : Nat.card ↥(R ⊔ R') = 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 := by
    have h1 : Nat.card ↥(R' ⊔ R) = Nat.card ↥(R ⊔ R') := by rw [sup_comm]
    rw [h1, ha, hb] at hprodR
    have h2 : 2 ^ ((Nat.card ↥(K ⊔ K')).factorization 2 + 1) =
        2 ^ (Nat.card ↥K).factorization 2 * 2 ^ (Nat.card ↥K').factorization 2 := by
      rw [hfac, pow_add]
    rw [pow_succ] at h2
    have := hprodR.trans h2.symm
    have h3 : 0 < 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h3 (by linarith)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1
    (T7A.le_normalizer_of_commutes hc.symm)
  refine ⟨sup_le_sup hR.1 hR'.1, hP2, fun V hVQ hV2 hle => ?_⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hdvd : Nat.card ↥V ∣ Nat.card ↥(K ⊔ K') := Subgroup.card_dvd_of_le hVQ
  rw [hn] at hdvd
  have hnle : n ≤ (Nat.card ↥(K ⊔ K')).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQ0).mp hdvd
  have hcard : Nat.card ↥V ≤ Nat.card ↥(R ⊔ R') := by
    rw [hn, hRR]
    exact Nat.pow_le_pow_right (by norm_num) hnle
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end T7X

namespace T7X

theorem exists_conj_sylow_pair (hΩ : HypOmegaGen Ω)
    {K K' R R' R₀ R₀' : Subgroup G} {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K)
    (hR' : IsSylow2In R' K') (hc : Commutes R R') (hR₀ : IsSylow2In R₀ K)
    (hR₀' : IsSylow2In R₀' K') (hc₀ : Commutes R₀ R₀') :
    ∃ g ∈ K ⊔ K', conjSub g R₀ = R ∧ conjSub g R₀' = R' := by
  have hQ := isSylow2In_sup_of_twin  hΩ hK hK' hne hz hz' hR hR' hc
  have hQ₀ := isSylow2In_sup_of_twin  hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hQ
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hQ.2.1
  refine ⟨g, hgQ, ?_, ?_⟩
  · have h1 : IsSylow2In (conjSub g R₀) K := by
      have := hR₀.conj g
      rwa [hgK] at this
    have h1le : conjSub g R₀ ≤ R ⊔ R' := by
      rw [← hg, T7A.conjSub_sup_eq]
      exact le_sup_left
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K) := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K = R := hR.eq_of_le hT2 inf_le_right (le_inf le_sup_left hR.1)
    have h2 : conjSub g R₀ ≤ R := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR).ge
  · have h1 : IsSylow2In (conjSub g R₀') K' := by
      have := hR₀'.conj g
      rwa [hgK'] at this
    have h1le : conjSub g R₀' ≤ R ⊔ R' := by
      rw [← hg, T7A.conjSub_sup_eq]
      exact le_sup_right
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K') := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K' = R' := hR'.eq_of_le hT2 inf_le_right (le_inf le_sup_right hR'.1)
    have h2 : conjSub g R₀' ≤ R' := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR').ge

end T7X

theorem exists_twinFrameData_of_sylows (hΩ : HypOmegaGen Ω)
    {K K' J R₁ R₂ : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K')
    (hc : Commutes R₁ R₂) :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧
      IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) ∧ W ∈ WSet Ω ∧ z ∈ W ∧ g * t * g⁻¹ ∈ W ∧
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        TwinFrameData Ω K K' z (x * y) (conjSub g J) (g * t * g⁻¹) := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    exists_twinSylow   hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ := T7X.exists_conj_sylow_pair  hΩ hK hK'Ω hne hz hzK' hR₁ hR₂ hc
    hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hK hne hzK' hz
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJΩ' : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have ht' : IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) := ht.conj g
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hJΩ', fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hT8 : 8 ≤ Nat.card ↥(conjSub g T₀) :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJΩ' hTsyl)
  have htT : g * t * g⁻¹ ∈ conjSub g T₀ :=
    mem_of_isUniqueInvolution_of_isPGroup ht' hTsyl.1 hTsyl.2.1 (by omega)
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Sylow 2 G, conjSub g (S₀ : Subgroup G) ≤ (S₁ : Subgroup G) :=
    (isPGroup_conjSub g S₀.isPGroup').exists_le_sylow
  have hS₀ : ∀ {A : Subgroup G}, A ≤ (S₀ : Subgroup G) → conjSub g A ≤ (S₁ : Subgroup G) :=
    fun hA => (conjSub_mono hA).trans hS₁
  have hR₁S : R₁ ≤ (S₁ : Subgroup G) := by rw [← hgR]; exact hS₀ hR₀S
  have hTS : conjSub g T₀ ≤ (S₁ : Subgroup G) := hS₀ hT₀S
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S₁
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S₁, hη, hηinv⟩, rfl⟩
  have hzW := exists_mem_eta_of_sylow  hΩ hη hK hz hR₁ hR₁S
  have htW := exists_mem_eta_of_sylow  hΩ hη hJΩ' ht' hTsyl hTS
  refine ⟨g, hgQ, ⨆ U ∈ η, U, hJ', ht', hWmem, hzW, htW, ?_⟩
  intro x hx y hy hx4 hy4
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hsqx : x * x = z := T7A.sq_eq_of_orderOf_four hz hxK hx4
  have hsqy : y * y = z := T7A.sq_eq_of_orderOf_four hzK' hyK' hy4
  have hcxy : x * y = y * x := hc x hx y hy
  have hxK' : x ∉ K' := fun h => T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hx4 hxK h
  have hyK : y ∉ K := fun h => T7X.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hy4 h hyK'
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, hz.sq]
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxK'
    have : x = y⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hyK'
  have huz : x * y ≠ z := by
    intro h
    apply hxK'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hyK')
  have htu : (g * t * g⁻¹) * (x * y) = (x * y) * (g * t * g⁻¹) := by
    have h1 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := hcRT x hx _ htT
    have h2 : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := hcR'T y hy _ htT
    calc (g * t * g⁻¹) * (x * y) = ((g * t * g⁻¹) * x) * y := by group
      _ = (x * (g * t * g⁻¹)) * y := by rw [h1]
      _ = x * ((g * t * g⁻¹) * y) := by group
      _ = x * (y * (g * t * g⁻¹)) := by rw [h2]
      _ = (x * y) * (g * t * g⁻¹) := by group
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hxK) (Subgroup.mem_sup_right hyK')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ'
      ht := ht'
      htu := htu }

namespace T7X

theorem exists_commuting_sylow_twin (hΩ : HypOmegaGen Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'
  obtain ⟨R', hR', hfix⟩ := exists_sylow_normalized hR.2.1 (hR.1.trans hKN)
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have h2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  exact ⟨R, R', hR, hR',
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' hne.symm hz hz' hR.1 hR'.1 h2⟩

end T7X

namespace T7X

theorem exists_sylow_pair_of_mem (hΩ : HypOmegaGen Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧ u ∈ R ⊔ R' := by
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ := exists_commuting_sylow_twin hΩ hK hK' hne hz hz'
  have hQ₀ := isSylow2In_sup_of_twin  hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨P, hP, huP⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self_eq_one hu2 hu1)
    (Subgroup.zpowers_le.mpr hu)
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  refine ⟨conjSub g R₀, conjSub g R₀', ?_, ?_, hc₀.conjSub g, ?_⟩
  · have := hR₀.conj g
    rwa [hgK] at this
  · have := hR₀'.conj g
    rwa [hgK'] at this
  · rw [← T7A.conjSub_sup_eq, hg]
    exact huP (Subgroup.mem_zpowers u)

end T7X

theorem exists_twinFrameData_at (hΩ : HypOmegaGen Ω)
    {K K' J' : Subgroup G} {z u t' : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K)) (ht' : IsUniqueInvolution J' t') :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, TwinFrameData Ω K K' z u (conjSub g J') (g * t' * g⁻¹) ∧
      W ∈ WSet Ω ∧ z ∈ W ∧ g * t' * g⁻¹ ∈ W := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    T7X.exists_sylow_pair_of_mem  hΩ hK hK'Ω hne hz hzK' hu hu2 hu1
  obtain ⟨g, hgQ, W, hJ'', ht'', hW, hzW, htW, hfr⟩ :=
    exists_twinFrameData_of_sylows   hΩ hK hz hK' hne hJ' ht' hR₁ hR₂ hc
  obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  have hcxy : x * y = y * x := hc x hx y hy
  have hsq : (x * x) * (y * y) = 1 := by
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hcxy]
      _ = (x * y) * (x * y) := by group
      _ = 1 := hu2
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have hxxA : x * x ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem hx hx, ?_⟩
    have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hy hy)
  have hx2 : x * x = z := by
    rcases hz.unique (x * x) (K.mul_mem hxK hxK) (hA _ hxxA) with h1 | h1
    · exfalso
      have hy2 : y * y = 1 := by rwa [h1, one_mul] at hsq
      rcases hz.unique x hxK h1 with h2 | h2 <;> rcases hzK'.unique y hyK' hy2 with h3 | h3
      · exact hu1 (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, mul_one])
      · exact hu1 (by rw [h2, h3]; exact hz.sq)
    · exact h1
  have hy2 : y * y = z := by
    have h1 : y * y = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [hx2] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz.sq
  exact ⟨g, hgQ, W, hfr x hx y hy (T7A.orderOf_eq_four_of_sq hz hx2)
    (T7A.orderOf_eq_four_of_sq hz hy2), hW, hzW, htW⟩

variable {K K' J : Subgroup G} {z u t : G}

theorem twinFrame_comm_zt (hΩ : HypOmegaGen Ω)
    (h : TwinFrameData Ω K K' z u J t) : z * t = t * z := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 K (mem_twinSet_self h.mem h.hz)
  have hRsyl : IsSylow2In R J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ h.hJ.1 hR hRJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN htR)).symm

theorem twinFrame_t_not_mem_closure (hΩ : HypOmegaGen Ω)
    (h : TwinFrameData Ω K K' z u J t) : t ∉ Subgroup.closure ({z, u} : Set G) := by
  intro htcl
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hΩ h.mem h.hz h.hK' h.hne h.hJ
  have hQ := T7X.isSylow2In_sup_of_twin hΩ h.mem h.hK'.1 h.hne h.hz hzK' hRsyl hR'syl hRR'
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have htQ : t ∈ K ⊔ K' := by
    have : Subgroup.closure ({z, u} : Set G) ≤ K ⊔ K' := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_left h.hz.mem
      · exact h.hu
    exact this htcl
  have hS2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) :=
    (Sylow.isPGroup' S).to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' :=
    hQ.eq_of_le hS2 inf_le_right (le_inf (sup_le hRS hR'S) hQ.1)
  have htRR' : t ∈ R ⊔ R' := by
    rw [← heq]
    exact ⟨hTS htT, htQ⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hRR' htRR'
  have hxc : ∀ r ∈ R, r * x = x * r := by
    intro r hr
    have h1 : r * t = t * r := hRT r hr t htT
    have h2 : r * y = y * r := hRR' r hr y hy
    have : (r * x) * y = (x * r) * y := by
      calc (r * x) * y = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
        _ = x * (r * y) := by rw [h2]
        _ = (x * r) * y := by group
    exact mul_right_cancel this
  have hyc : ∀ r ∈ R', r * y = y * r := by
    intro r hr
    have h1 : r * t = t * r := hR'T r hr t htT
    have h2 : x * r = r * x := hRR' x hx r hr
    have : x * (r * y) = x * (y * r) := by
      calc x * (r * y) = (x * r) * y := by group
        _ = (r * x) * y := by rw [h2]
        _ = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
    exact mul_left_cancel this
  have hxz := T7A.eq_one_or_eq_of_central h.hz
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hRsyl)) hRsyl.1 hx hxc
  have hyz := T7A.eq_one_or_eq_of_central hzK'
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.hK'.1 hR'syl)) hR'syl.1 hy hyc
  have htz := h.t_ne_z
  have ht1 := h.ht.ne_one
  rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
  · exact ht1 (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, mul_one])
  · exact ht1 (by rw [← hxy, h1, h2]; exact h.hz.sq)

theorem twinFrame_comm_gen (hΩ : HypOmegaGen Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    ∀ a ∈ ({z, u, t} : Set G), ∀ b ∈ ({z, u, t} : Set G), a * b = b * a := by
  have hzu := h.comm_zu
  have hzt := twinFrame_comm_zt hΩ h
  have hut : u * t = t * u := h.htu.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hzu
  · exact hzt
  · exact hzu.symm
  · rfl
  · exact hut
  · exact hzt.symm
  · exact hut.symm
  · rfl

theorem twinFrame_isElemAbelian (hΩ : HypOmegaGen Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hcomm := T7A.commutes_closure (twinFrame_comm_gen hΩ h)
  have hsq : ∀ a ∈ ({z, u, t} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact h.hz.sq
    · exact h.hu2
    · exact h.ht.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (twinFrame_comm_gen hΩ h) x hx

theorem twinFrame_natCard_eight (hΩ : HypOmegaGen Ω)
    (h : TwinFrameData Ω K K' z u J t) :
    Nat.card ↥(Subgroup.closure ({z, u, t} : Set G)) = 8 := by
  have hzt := twinFrame_comm_zt hΩ h
  have hD := T7A.isElemAbelian2_closure_pair h.hu2 h.hz.sq h.hu1 h.hz.ne_one h.huz h.comm_zu.symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  have hcl : Subgroup.closure ({z, u, t} : Set G) =
      Subgroup.closure ({u, z} : Set G) ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({u, z} : Set G)) (Subgroup.zpowers t) := by
    have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h.htu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, z} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers ht2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply twinFrame_t_not_mem_closure hΩ h
      rw [Set.pair_comm]
      rw [← h1]
      exact he.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, ht2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end Frame

end CFSG.ClassicalInvolution.Hat2A7S
