module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT7ATwin
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.A7Q.Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isSylow2In_sup_of_twin (hΩ : HypOmegaGen Ω) {K K' R R' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hc : Commutes R R') : IsSylow2In (R ⊔ R') (K ⊔ K') := by
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  have hprod := T7A.card_sup_mul_card_inf hKN
  rw [sup_comm] at hprod
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have h8' : 8 ≤ Nat.card R' :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK' hR')
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
    have h2 : padicValNat 2 (Nat.card ↥(K ⊓ K')) ≤ 1 := (hΩ.omega4 K hK K' hK' hne.symm).1
    rw [Nat.factorization_def _ Nat.prime_two] at h1 ⊢
    omega
  have hinfR : Nat.card ↥(R ⊓ R') = 2 := by
    refine le_antisymm ?_ ?_
    · exact Sec6Gen.card_le_two_of_le_inf hΩ hK hK' hne.symm (hR.2.1.to_le inf_le_left)
        (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
    · have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr ⟨hzR, hzR'⟩ :
        Subgroup.zpowers z ≤ R ⊓ R')
      rwa [Nat.card_zpowers, hz2] at this
  have hprodR := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hc)
  rw [hinfR] at hprodR
  have ha := natCard_eq_pow_of_isSylow2In hR
  have hb := natCard_eq_pow_of_isSylow2In hR'
  have hQ0 : Nat.card ↥(K ⊔ K') ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K ⊔ K')).factorization 2 + 1 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥K').factorization 2 := by
    have := congrArg (fun n => n.factorization 2) hprod
    simp only [Nat.factorization_mul hQ0 hN0, Nat.factorization_mul Nat.card_pos.ne'
      Nat.card_pos.ne', Finsupp.add_apply, hinfK] at this
    exact this
  have hRR : Nat.card ↥(R ⊔ R') = 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 := by
    have h1 : Nat.card ↥(R' ⊔ R) = Nat.card ↥(R ⊔ R') := by rw [sup_comm]
    rw [h1, ha, hb] at hprodR
    have h2 : 2 ^ ((Nat.card ↥(K ⊔ K')).factorization 2 + 1) =
        2 ^ (Nat.card ↥K).factorization 2 * 2 ^ (Nat.card ↥K').factorization 2 := by
      rw [hfac, pow_add]
    rw [pow_succ] at h2
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (by linarith [hprodR.trans h2.symm])
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

theorem conjSub_eq_of_mem_sup (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    {g : G} (hg : g ∈ K ⊔ K') : conjSub g K = K ∧ conjSub g K' = K' :=
  ⟨mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer
      (Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz)) hg),
    mem_normalizer_iff_conjSub_eq.mp ((sup_le (Sec6Gen.le_normalizer_of_twin hΩ hK hK'
      hne.symm hz hz') Subgroup.le_normalizer) hg)⟩

theorem eq_of_le_sup {K R R' V : Subgroup G} (hR : IsSylow2In R K) (hP2 : IsPGroup 2 ↥(R ⊔ R'))
    (hV : IsSylow2In V K) (hVle : V ≤ R ⊔ R') : V = R := by
  have hTR : (R ⊔ R') ⊓ K = R := hR.eq_of_le (hP2.to_le inf_le_left) inf_le_right
    (le_inf le_sup_left hR.1)
  exact Subgroup.eq_of_le_of_card_ge (hTR ▸ le_inf hVle hV.1) (hV.natCard_eq hR).ge

theorem exists_conj_sylow_pair (hΩ : HypOmegaGen Ω) {K K' R R' R₀ R₀' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hc : Commutes R R') (hR₀ : IsSylow2In R₀ K) (hR₀' : IsSylow2In R₀' K')
    (hc₀ : Commutes R₀ R₀') : ∃ g ∈ K ⊔ K', conjSub g R₀ = R ∧ conjSub g R₀' = R' := by
  have hQ := isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR hR' hc
  have hQ₀ := isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hQ
  obtain ⟨hgK, hgK'⟩ := conjSub_eq_of_mem_sup hΩ hK hK' hne hz hz' hgQ
  have hle : conjSub g (R₀ ⊔ R₀') = R ⊔ R' := hg
  rw [T7A.conjSub_sup_eq] at hle
  refine ⟨g, hgQ, eq_of_le_sup hR hQ.2.1 (hgK ▸ hR₀.conj g) (hle ▸ le_sup_left), ?_⟩
  have hQ' : IsPGroup 2 ↥(R' ⊔ R) := by rw [sup_comm]; exact hQ.2.1
  exact eq_of_le_sup hR' hQ' (hgK' ▸ hR₀'.conj g) (by rw [sup_comm, ← hle]; exact le_sup_right)

theorem exists_commuting_sylow_twin (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨R', hR', hfix⟩ := exists_sylow_normalized hR.2.1
    (hR.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'))
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  exact ⟨R, R', hR, hR', Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' hne.symm hz hz' hR.1
    hR'.1 (hR.2.1.to_sup_of_normal_right' hR'.2.1 hRn)⟩

theorem exists_sylow_pair_of_mem (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧ u ∈ R ⊔ R' := by
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ := exists_commuting_sylow_twin hΩ hK hK' hne hz hz'
  have hQ₀ := isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨P, hP, huP⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self_eq_one hu2 hu1)
    (Subgroup.zpowers_le.mpr hu)
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  obtain ⟨hgK, hgK'⟩ := conjSub_eq_of_mem_sup hΩ hK hK' hne hz hz' hgQ
  refine ⟨conjSub g R₀, conjSub g R₀', hgK ▸ hR₀.conj g, hgK' ▸ hR₀'.conj g, hc₀.conjSub g, ?_⟩
  rw [← T7A.conjSub_sup_eq, hg]
  exact huP (Subgroup.mem_zpowers u)

end CFSG.ClassicalInvolution.A7Q.Gen
