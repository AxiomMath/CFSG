module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneThreeStarImg
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Quasithin.EmptyFaithful.S152L27C
import CFSG.RankThree.GF2n.Tim81.Components
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)

variable {G : Type} [Group G] [Finite G]

theorem CaseOneCtx.fitting_threeStar_eq_bot {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) : CFSG.fittingSubgroup (threeStar M) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.Fitting_eq_pcore (threeStar M) 3
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)]
  exact h2

theorem CaseOneCtx.exists_isComponent_threeStar {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) :
    ∃ K : Subgroup (threeStar M), CFSG.IsComponent K := by
  classical
  by_contra hnone
  push Not at hnone
  have hfit := c.fitting_threeStar_eq_bot h2
  have hlayer : CFSG.layer (threeStar M) = ⊥ :=
    CFSG.LocalCores.layer_eq_bot_of_forall hnone
  have hF : CFSG.generalizedFitting (threeStar M) = ⊥ := by
    rw [CFSG.generalizedFitting.eq_sup, hfit, hlayer, sup_bot_eq]
  have htop : (⊤ : Subgroup (threeStar M)) ≤ ⊥ := by
    have h := CFSG.centralizer_generalizedFitting_le (threeStar M)
    rw [hF] at h
    intro x hx
    apply h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := Subgroup.mem_bot.mp hy
    rw [hy1, one_mul, mul_one]
  have htopbot : (⊤ : Subgroup (threeStar M)) = ⊥ := le_antisymm htop bot_le
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  have hE3 : IsPGroup 3 E := c.choice.elem.isPGroup
  have hEM : E ≤ M := c.choice.E_le_Q.trans hQM
  have hEbar_bot : threeStarImg M E = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ (⊤ : Subgroup (threeStar M)) := Subgroup.mem_top x
    rw [htopbot] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hcard := card_threeStarImg_of_isPGroup hE3 hEM
  rw [hEbar_bot] at hcard
  have hEcard : Nat.card ↥E = 9 := c.choice.card
  rw [hEcard] at hcard
  norm_num at hcard

theorem CaseOneCtx.component_facts {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) {K : Subgroup (threeStar M)}
    (hK : CFSG.IsComponent K) :
    IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ 3 ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfit := c.fitting_threeStar_eq_bot h2
  obtain ⟨hsimple, hnonab⟩ :=
    CFSG.RankThree.GF2n.Tim81.component_isSimple hfit hK
  refine ⟨hsimple, hnonab, ?_⟩
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hKle : K ≤ CFSG.pPrimeCore 3 (threeStar M) :=
    CFSG.Quasithin.le_pPrimeCore_of_isSubnormal_of_coprime152 3 hK.2 hcop
  rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three] at hKle
  have hbot : K = ⊥ := le_bot_iff.mp hKle
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  haveI : Subsingleton K := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial K).exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem CaseOneCtx.centerImg_le_of_normalizes
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) {K : Subgroup (threeStar M)}
    (hK : CFSG.IsComponent K)
    (hQK : threeStarImg M Q ≤ Subgroup.normalizer (K : Set (threeStar M))) :
    threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) ≤ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  obtain ⟨-, -, h3K⟩ := c.component_facts h2 hK
  have hQ3 : IsPGroup 3 ↥Q := c.choice.sylow.isPGroup
  have hQsub3 : IsPGroup 3 ↥(Q.subgroupOf M) := hQ3.comap_subtype
  have hQb3 : IsPGroup 3 ↥(threeStarImg M Q) :=
    IsPGroup.map hQsub3 (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  obtain ⟨z, hzK, hzord, hzcent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hQb3 hQK h3K
  have hzQ : threeStarImg M Q ≤ Subgroup.centralizer ({z} : Set (threeStar M)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp hzcent y hy).symm
  let A : Subgroup (threeStar M) :=
    threeStarImg M ((Subgroup.center ↥Q).map Q.subtype)
  have hzA : z ∈ A := c.mem_centerImg_of_centralizes h142 hzord hzQ
  have hAcardG : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = 3 :=
    (h142 H E Q J c.choice c.typeA).1.2.2.2
  have hA3 : IsPGroup 3 ↥((Subgroup.center ↥Q).map Q.subtype) :=
    IsPGroup.map (hQ3.to_subgroup (Subgroup.center ↥Q)) Q.subtype
  have hAM : (Subgroup.center ↥Q).map Q.subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans hQM
  have hAcard : Nat.card ↥A = 3 := by
    rw [show Nat.card ↥A = Nat.card ↥(threeStarImg M
      ((Subgroup.center ↥Q).map Q.subtype)) from rfl,
      card_threeStarImg_of_isPGroup hA3 hAM, hAcardG]
  have hcardZp : Nat.card ↥(Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  have hAeq : A = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzA) ?_).symm
    rw [hAcard, hcardZp]
  change A ≤ K
  rw [hAeq]
  exact Subgroup.zpowers_le.mpr hzK

private theorem component_element_prime {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hfit : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hpK : p ∣ Nat.card K) :
    ∃ e ∈ K, orderOf e = p ∧ ∃ c ∈ K, e * c ≠ c * e := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨e, heord⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  have heordX : orderOf (e : X) = p := by
    rw [Subgroup.orderOf_coe]
    exact heord
  have hene : (e : X) ≠ 1 := by
    intro h
    have : orderOf (e : X) = 1 := by rw [h, orderOf_one]
    rw [heordX] at this
    omega
  have hnc : ∃ c ∈ K, (e : X) * c ≠ c * (e : X) := by
    by_contra h
    push Not at h
    have heZ : (⟨(e : X), e.2⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (h (g : X) g.2).symm
    rw [CFSG.RankThree.GF2n.Tim81.center_component_eq_bot hfit hK, Subgroup.mem_bot] at heZ
    exact hene (congrArg Subtype.val heZ)
  exact ⟨(e : X), e.2, heordX, hnc⟩

private theorem orbit_ncard_le_pRank_of_isComponent {X : Type} [Group X] [Finite X]
    {A : Subgroup X} [MulAction A (Subgroup X)] {K : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hsmul : ∀ (a : A) (C : Subgroup X),
      a • C = C.map (MulAut.conj (a : X)).toMonoidHom)
    (hfit : CFSG.fittingSubgroup X = ⊥) (hK : CFSG.IsComponent K)
    (hpK : p ∣ Nat.card K) :
    (MulAction.orbit A K).ncard ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  classical
  by_contra hle
  have hlt : CFSG.Open.pRank p (⊤ : Subgroup X) < (MulAction.orbit A K).ncard := by
    omega
  have hfin : (MulAction.orbit A K).Finite := Set.toFinite _
  have hcard : CFSG.Open.pRank p (⊤ : Subgroup X) + 1 ≤ hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    omega
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcard
  have hscomp : ∀ C ∈ s, CFSG.IsComponent C ∧
      ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e := by
    intro C hC
    have hCorbit : C ∈ MulAction.orbit A K := hfin.mem_toFinset.mp (hs_sub hC)
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hCorbit
    have hCcomp : CFSG.IsComponent (a • K) := by
      rw [hsmul]
      exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (a : X)) hK
    have hpC : p ∣ Nat.card ↥(a • K) := by
      rw [hsmul, Subgroup.card_map_of_injective (MulAut.conj (a : X)).injective]
      exact hpK
    exact ⟨hCcomp, component_element_prime hfit hCcomp hpC⟩
  have hle' := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_le_pRank_of_components
    (p := p) (Fact.out : p.Prime) s hscomp
  rw [hs_card] at hle'
  have htop : CFSG.pRank p (⊤ : Subgroup X) = CFSG.pRank p X :=
    CFSG.pRank_congr_of_mulEquiv Subgroup.topEquiv p
  rw [htop] at hle'
  have hprank : CFSG.pRank p X = CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top p X
  rw [hprank] at hle'
  omega

private theorem isComponent_of_mem_orbit {X : Type} [Group X] {A : Subgroup X}
    [MulAction A (Subgroup X)] {K : Subgroup X}
    (hsmul : ∀ (a : A) (C : Subgroup X),
      a • C = C.map (MulAut.conj (a : X)).toMonoidHom)
    (hK : CFSG.IsComponent K) {C : Subgroup X} (hC : C ∈ MulAction.orbit A K) :
    CFSG.IsComponent C := by
  obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hC
  rw [hsmul]
  exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (a : X)) hK

private theorem stabilizer_normal_index_three_of_orbit {A : Type} [Group A] [Finite A]
    {α : Type} [MulAction A α] {a : α}
    (hcard : Nat.card A = 3 ^ 5)
    (hgt : 1 < (MulAction.orbit A a).ncard)
    (hle : (MulAction.orbit A a).ncard ≤ 3) :
    (MulAction.stabilizer A a).Normal ∧ (MulAction.stabilizer A a).index = 3 := by
  classical
  have hidx : (MulAction.stabilizer A a).index = (MulAction.orbit A a).ncard :=
    MulAction.index_stabilizer A a
  have hdvd : (MulAction.orbit A a).ncard ∣ 3 ^ 5 := by
    rw [← hidx, ← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk
    omega
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hge : 3 ≤ (MulAction.orbit A a).ncard := by
    rw [hk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have heq : (MulAction.orbit A a).ncard = 3 := by omega
  constructor
  · apply Subgroup.normal_of_index_eq_minFac_card (G := A)
    rw [hidx, heq, hcard]
    exact (Nat.prime_three.pow_minFac (by norm_num : 5 ≠ 0)).symm
  · rw [hidx, heq]

private theorem stabilizer_le_stabilizer_of_mem_orbit {X : Type} [Group X] {A : Subgroup X}
    [MulAction A (Subgroup X)] {K C : Subgroup X}
    (hN : (MulAction.stabilizer A K).Normal) (hC : C ∈ MulAction.orbit A K) :
    MulAction.stabilizer A K ≤ MulAction.stabilizer A C := by
  obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hC
  intro n hn
  rw [MulAction.mem_stabilizer_iff]
  calc n • (q • K) = (n * q) • K := (mul_smul n q K).symm
    _ = (q * (q⁻¹ * n * q)) • K := by group
    _ = q • ((q⁻¹ * n * q) • K) := mul_smul q (q⁻¹ * n * q) K
    _ = q • K := by
        rw [MulAction.mem_stabilizer_iff.mp (hN.conj_mem' n hn q)]

private theorem map_le_normalizer_of_le_stabilizer {X : Type} [Group X] {A C : Subgroup X}
    [MulAction A (Subgroup X)]
    (hsmul : ∀ (a : A) (D : Subgroup X),
      a • D = D.map (MulAut.conj (a : X)).toMonoidHom)
    {N : Subgroup A} (hN : N ≤ MulAction.stabilizer A C) :
    N.map A.subtype ≤ Subgroup.normalizer (C : Set X) := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [hsmul] using MulAction.mem_stabilizer_iff.mp (hN hn)

private theorem exists_stabilizer_data {X : Type} [Group X] [Finite X]
    {A : Subgroup X} [MulAction A (Subgroup X)] {K : Subgroup X}
    (hsmul : ∀ (a : A) (C : Subgroup X),
      a • C = C.map (MulAut.conj (a : X)).toMonoidHom)
    (hcardA : Nat.card A = 3 ^ 5)
    (hgt : 1 < (MulAction.orbit A K).ncard)
    (hle : (MulAction.orbit A K).ncard ≤ 3) :
    ∃ N : Subgroup A, N.Normal ∧ N.index = 3 ∧ Nat.card ↥N = 3 ^ 4 ∧
      (MulAction.orbit A K).ncard = 3 ∧
      ∀ C ∈ MulAction.orbit A K,
        N.map A.subtype ≤ Subgroup.normalizer (C : Set X) := by
  obtain ⟨hNnormal, hNindex⟩ := stabilizer_normal_index_three_of_orbit hcardA hgt hle
  let N : Subgroup A := MulAction.stabilizer A K
  have hNcard : Nat.card ↥N = 3 ^ 4 := by
    have h := Subgroup.card_mul_index N
    rw [hNindex, hcardA] at h
    have h' : Nat.card ↥N * 3 = 243 := by simpa using h
    omega
  have horb : (MulAction.orbit A K).ncard = 3 := by
    rw [← MulAction.index_stabilizer A K, hNindex]
  have hNle : ∀ C ∈ MulAction.orbit A K,
      N.map A.subtype ≤ Subgroup.normalizer (C : Set X) := by
    intro C hC
    exact map_le_normalizer_of_le_stabilizer hsmul
      (stabilizer_le_stabilizer_of_mem_orbit hNnormal hC)
  exact ⟨N, hNnormal, hNindex, hNcard, horb, hNle⟩

private theorem exists_smul_ne_of_not_le_normalizer {X : Type} [Group X] {A K : Subgroup X}
    [MulAction A (Subgroup X)]
    (hsmul : ∀ (a : A) (C : Subgroup X),
      a • C = C.map (MulAut.conj (a : X)).toMonoidHom)
    (hnot : ¬ A ≤ Subgroup.normalizer (K : Set X)) :
    ∃ a : A, a • K ≠ K := by
  obtain ⟨q, hqA, hqnot⟩ : ∃ q ∈ A, q ∉ Subgroup.normalizer (K : Set X) := by
    by_contra h
    push Not at h
    exact hnot h
  refine ⟨⟨q, hqA⟩, ?_⟩
  intro hfix
  apply hqnot
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [hsmul] using hfix

private theorem one_lt_ncard_orbit_of_smul_ne {A : Type} [Group A] {α : Type} [Finite α]
    [MulAction A α] {a : α} (h : ∃ g : A, g • a ≠ a) :
    1 < (MulAction.orbit A a).ncard := by
  obtain ⟨g, hg⟩ := h
  refine (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨a, ?_, g • a, ?_, ?_⟩
  · exact MulAction.mem_orbit_self a
  · exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
  · exact hg.symm

private theorem exists_three_distinct_of_orbit_ncard_three {X : Type} [Group X] [Finite X]
    {A : Subgroup X} [MulAction A (Subgroup X)] {K : Subgroup X}
    (hcard : (MulAction.orbit A K).ncard = 3) :
    ∃ K1 K2 K3 : Subgroup X, K1 ∈ MulAction.orbit A K ∧
      K2 ∈ MulAction.orbit A K ∧ K3 ∈ MulAction.orbit A K ∧
      K1 ≠ K2 ∧ K1 ≠ K3 ∧ K2 ≠ K3 := by
  classical
  have hfin : (MulAction.orbit A K).Finite := Set.toFinite _
  have hcard' : hfin.toFinset.card = 3 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq (s := hfin.toFinset) (n := 3)
    (by rw [hcard'])
  obtain ⟨K1, K2, K3, h12, h13, h23, hs_eq⟩ := Finset.card_eq_three.mp hs_card
  have hmem : ∀ C ∈ ({K1, K2, K3} : Finset (Subgroup X)),
      C ∈ MulAction.orbit A K := by
    intro C hC
    have hCs : C ∈ s := by rwa [hs_eq]
    exact hfin.mem_toFinset.mp (hs_sub hCs)
  exact ⟨K1, K2, K3, hmem K1 (by simp), hmem K2 (by simp), hmem K3 (by simp),
    h12, h13, h23⟩

private theorem exists_elemAbelian_sup_two_zpowers {X : Type} [Group X] [Finite X]
    {K1 K2 : Subgroup X} (hfit : CFSG.fittingSubgroup X = ⊥)
    (hK1 : CFSG.IsComponent K1) (hK2 : CFSG.IsComponent K2) (h12 : K1 ≠ K2)
    {z1 z2 : X} (hz1K1 : z1 ∈ K1) (hz2K2 : z2 ∈ K2)
    (hz1ord : orderOf z1 = 3) (hz2ord : orderOf z2 = 3) :
    ∃ B : Subgroup X, IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧ z1 ∈ B ∧ z2 ∈ B ∧
      B = Subgroup.zpowers z1 ⊔ Subgroup.zpowers z2 ∧ B ≤ K1 ⊔ K2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a :=
    (CFSG.RankThree.GF2n.Tim81.components_commute_inf hfit hK1 hK2 h12).1
  let B1 : Subgroup X := Subgroup.zpowers z1
  have hB1leK1 : B1 ≤ K1 := Subgroup.zpowers_le.mpr hz1K1
  have hB1ea : IsElemAbelian 3 B1 := by
    rw [show B1 = Subgroup.zpowers z1 from rfl]
    exact CFSG.Open.isElemAbelian_zpowers (by simpa [hz1ord] using pow_orderOf_eq_one z1)
  have hB1card : Nat.card ↥B1 = 3 := by
    rw [show B1 = Subgroup.zpowers z1 from rfl, Nat.card_zpowers, hz1ord]
  have hz2notB1 : z2 ∉ B1 := by
    intro hz
    have hzK1 : z2 ∈ K1 := hB1leK1 hz
    have hzbot : z2 ∈ (⊥ : Subgroup X) := by
      rw [← (CFSG.RankThree.GF2n.Tim81.components_commute_inf hfit hK1 hK2 h12).2]
      exact ⟨hzK1, hz2K2⟩
    have hz1 : z2 = 1 := Subgroup.mem_bot.mp hzbot
    have : orderOf z2 = 1 := by rw [hz1, orderOf_one]
    omega
  have hcomm2 : ∀ e ∈ B1, Commute e z2 := fun e he => hcomm12 e (hB1leK1 he) z2 hz2K2
  obtain ⟨hB2ea, hB2card⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers hB1ea hz2ord hcomm2 hz2notB1
  let B2 : Subgroup X := B1 ⊔ Subgroup.zpowers z2
  have hB2leK12 : B2 ≤ K1 ⊔ K2 :=
    sup_le (hB1leK1.trans le_sup_left)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hz2K2))
  have hB2card' : Nat.card ↥B2 = 9 := by
    rw [show B2 = B1 ⊔ Subgroup.zpowers z2 from rfl, hB2card, hB1card]
  refine ⟨B2, hB2ea, hB2card', ?_, ?_, rfl, hB2leK12⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z1)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z2)

private theorem exists_elemAbelian_sup_three_zpowers {X : Type} [Group X] [Finite X]
    {K1 K2 K3 : Subgroup X} (hfit : CFSG.fittingSubgroup X = ⊥)
    (hK1 : CFSG.IsComponent K1) (hK2 : CFSG.IsComponent K2) (hK3 : CFSG.IsComponent K3)
    (h12 : K1 ≠ K2) (h13 : K1 ≠ K3) (h23 : K2 ≠ K3)
    {z1 z2 z3 : X} (hz1K1 : z1 ∈ K1) (hz2K2 : z2 ∈ K2) (hz3K3 : z3 ∈ K3)
    (hz1ord : orderOf z1 = 3) (hz2ord : orderOf z2 = 3) (hz3ord : orderOf z3 = 3) :
    ∃ B : Subgroup X, IsElemAbelian 3 B ∧ Nat.card ↥B = 27 ∧ z1 ∈ B ∧ z2 ∈ B ∧ z3 ∈ B ∧
      B = (Subgroup.zpowers z1 ⊔ Subgroup.zpowers z2) ⊔ Subgroup.zpowers z3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B2, hB2ea, hB2card, hz1B2, hz2B2, hB2gen, hB2leK12⟩ :=
    exists_elemAbelian_sup_two_zpowers hfit hK1 hK2 h12 hz1K1 hz2K2 hz1ord hz2ord
  have hcomm13 : ∀ a ∈ K1, ∀ b ∈ K3, a * b = b * a :=
    (CFSG.RankThree.GF2n.Tim81.components_commute_inf hfit hK1 hK3 h13).1
  have hcomm23 : ∀ a ∈ K2, ∀ b ∈ K3, a * b = b * a :=
    (CFSG.RankThree.GF2n.Tim81.components_commute_inf hfit hK2 hK3 h23).1
  have hK12cent : K1 ⊔ K2 ≤ Subgroup.centralizer (K3 : Set X) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm13 a ha b hb).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm23 a ha b hb).symm
  have hz3notB2 : z3 ∉ B2 := by
    intro hz
    have hzK12 : z3 ∈ K1 ⊔ K2 := hB2leK12 hz
    have hzcent : z3 ∈ Subgroup.centralizer (K3 : Set X) := hK12cent hzK12
    have hzZ : (⟨z3, hz3K3⟩ : K3) ∈ Subgroup.center K3 := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hc := Subgroup.mem_centralizer_iff.mp hzcent (g : X) g.2
      exact Subtype.ext hc
    rw [CFSG.RankThree.GF2n.Tim81.center_component_eq_bot hfit hK3,
      Subgroup.mem_bot] at hzZ
    have hz1 : z3 = 1 := congrArg Subtype.val hzZ
    have : orderOf z3 = 1 := by rw [hz1, orderOf_one]
    omega
  have hcomm3 : ∀ e ∈ B2, Commute e z3 := by
    intro e he
    have he' : e ∈ K1 ⊔ K2 := hB2leK12 he
    exact (Subgroup.mem_centralizer_iff.mp (hK12cent he') z3 hz3K3).symm
  obtain ⟨hB3ea, hB3card0⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers hB2ea hz3ord hcomm3 hz3notB2
  let B3 : Subgroup X := B2 ⊔ Subgroup.zpowers z3
  have hB3card : Nat.card ↥B3 = 27 := by
    rw [show B3 = B2 ⊔ Subgroup.zpowers z3 from rfl, hB3card0, hB2card]
  refine ⟨B3, hB3ea, hB3card, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_sup_left hz1B2
  · exact Subgroup.mem_sup_left hz2B2
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z3)
  · rw [show B3 = B2 ⊔ Subgroup.zpowers z3 from rfl, hB2gen]

private theorem le_centralizer_of_sup_three_zpowers {X : Type} [Group X]
    {B : Subgroup X} {z1 z2 z3 y : X}
    (hB : B = (Subgroup.zpowers z1 ⊔ Subgroup.zpowers z2) ⊔ Subgroup.zpowers z3)
    (h1 : z1 * y = y * z1) (h2 : z2 * y = y * z2) (h3 : z3 * y = y * z3) :
    B ≤ Subgroup.centralizer ({y} : Set X) := by
  rw [hB]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact h1.symm)
  · exact Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact h2.symm)
  · exact Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact h3.symm)

private theorem le_of_exponent_three_of_rank_le_three {X : Type} [Group X] [Finite X]
    {B Nim : Subgroup X} (hB : IsElemAbelian 3 B) (hBcard : Nat.card ↥B = 27)
    (hNim : IsPGroup 3 Nim) (hexp : ∀ y ∈ Nim, y ^ 3 = 1)
    (hcent : ∀ z ∈ B, ∀ y ∈ Nim, z * y = y * z)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) : Nim ≤ B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  by_contra hyB
  have hyne : y ≠ 1 := by
    intro h
    apply hyB
    rw [h]
    exact B.one_mem
  have hyord : orderOf y = 3 := orderOf_eq_prime (hexp y hy) hyne
  have hcomm : ∀ e ∈ B, Commute e y := fun e he => hcent e he y hy
  obtain ⟨hEea, hEcard⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers hB hyord hcomm hyB
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    have hcard : Nat.card ↥(B ⊔ Subgroup.zpowers y) = 3 ^ 4 := by
      rw [hEcard, hBcard]
      norm_num
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hEea hcard
  omega

private theorem threeStar_Q_data
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h2 : CFSG.pCore 3 (threeStar M) = ⊥) :
    CFSG.fittingSubgroup (threeStar M) = ⊥ ∧
      IsPGroup 3 ↥(threeStarImg M Q) ∧
      Nat.card ↥(threeStarImg M Q) = 3 ^ 5 ∧
      (∀ y ∈ threeStarImg M Q, y ^ 3 = 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  have hQ3 : IsPGroup 3 ↥Q := c.choice.sylow.isPGroup
  have hQb3 : IsPGroup 3 ↥(threeStarImg M Q) := IsPGroup.map hQ3.comap_subtype _
  have hQbcard : Nat.card ↥(threeStarImg M Q) = 3 ^ 5 := by
    rw [card_threeStarImg_of_isPGroup hQ3 hQM]
    exact (h142 H E Q J c.choice c.typeA).1.1
  have hexpQ : ∀ x ∈ Q, x ^ 3 = 1 := (h142 H E Q J c.choice c.typeA).1.2.1
  have hexpQb : ∀ y ∈ threeStarImg M Q, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hq3 : (q : G) ^ 3 = 1 := hexpQ _ hqQ
    rw [← map_pow]
    have : q ^ 3 = 1 := Subtype.ext (by simpa using hq3)
    rw [this, map_one]
  exact ⟨c.fitting_threeStar_eq_bot h2, hQb3, hQbcard, hexpQb⟩

private theorem exists_span_of_three_orbit_components {X : Type} [Group X] [Finite X]
    {A : Subgroup X} [MulAction A (Subgroup X)] {K Nim : Subgroup X}
    (hsmul : ∀ (a : A) (C : Subgroup X),
      a • C = C.map (MulAut.conj (a : X)).toMonoidHom)
    (hfit : CFSG.fittingSubgroup X = ⊥) (hK : CFSG.IsComponent K)
    (hdiv : ∀ C : Subgroup X, CFSG.IsComponent C → 3 ∣ Nat.card C)
    (horb : (MulAction.orbit A K).ncard = 3)
    (hNim3 : IsPGroup 3 Nim)
    (hNleNorm : ∀ C ∈ MulAction.orbit A K, Nim ≤ Subgroup.normalizer (C : Set X)) :
    ∃ B : Subgroup X, IsElemAbelian 3 B ∧ Nat.card ↥B = 27 ∧
      ∀ z ∈ B, ∀ y ∈ Nim, z * y = y * z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K1, K2, K3, hK1o, hK2o, hK3o, h12, h13, h23⟩ :=
    exists_three_distinct_of_orbit_ncard_three horb
  have hcomp1 : CFSG.IsComponent K1 := isComponent_of_mem_orbit hsmul hK hK1o
  have hcomp2 : CFSG.IsComponent K2 := isComponent_of_mem_orbit hsmul hK hK2o
  have hcomp3 : CFSG.IsComponent K3 := isComponent_of_mem_orbit hsmul hK hK3o
  have h3K1 : 3 ∣ Nat.card K1 := hdiv K1 hcomp1
  have h3K2 : 3 ∣ Nat.card K2 := hdiv K2 hcomp2
  have h3K3 : 3 ∣ Nat.card K3 := hdiv K3 hcomp3
  obtain ⟨z1, hz1K1, hz1ord, hz1cent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hNim3
      (hNleNorm K1 hK1o) h3K1
  obtain ⟨z2, hz2K2, hz2ord, hz2cent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hNim3
      (hNleNorm K2 hK2o) h3K2
  obtain ⟨z3, hz3K3, hz3ord, hz3cent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hNim3
      (hNleNorm K3 hK3o) h3K3
  obtain ⟨B, hBea, hBcard, -, -, -, hBgen⟩ :=
    exists_elemAbelian_sup_three_zpowers hfit hcomp1 hcomp2 hcomp3 h12 h13 h23
      hz1K1 hz2K2 hz3K3 hz1ord hz2ord hz3ord
  refine ⟨B, hBea, hBcard, ?_⟩
  intro z hz y hy
  have hzy : z ∈ Subgroup.centralizer ({y} : Set X) := by
    refine le_centralizer_of_sup_three_zpowers hBgen ?_ ?_ ?_ hz
    · exact (Subgroup.mem_centralizer_iff.mp hz1cent y hy).symm
    · exact (Subgroup.mem_centralizer_iff.mp hz2cent y hy).symm
    · exact (Subgroup.mem_centralizer_iff.mp hz3cent y hy).symm
  exact (Subgroup.mem_centralizer_iff.mp hzy y (Set.mem_singleton y)).symm

theorem CaseOneCtx.threeStarImg_le_normalizer_component
    {M H E Q J R T : Subgroup G} (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h2 : CFSG.pCore 3 (threeStar M) = ⊥)
    {K : Subgroup (threeStar M)} (hK : CFSG.IsComponent K) :
    threeStarImg M Q ≤ Subgroup.normalizer (K : Set (threeStar M)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := threeStar M
  let Qb : Subgroup X := threeStarImg M Q
  obtain ⟨hfit, hQb3, hQbcard, hexpQb⟩ := threeStar_Q_data c h142 h2
  by_contra hnot
  letI : MulAction (MulAut X) (Subgroup X) := Subgroup.pointwiseMulAction
  let act : MulAction ↥Qb (Subgroup X) :=
    MulAction.compHom (Subgroup X) ((MulAut.conj : X →* MulAut X).comp Qb.subtype)
  letI := act
  have hsmul : ∀ (q : ↥Qb) (C : Subgroup X),
      q • C = C.map (MulAut.conj (q : X)).toMonoidHom := fun q C => rfl
  have h3K : 3 ∣ Nat.card K := (c.component_facts h2 hK).2.2
  have horb_le : (MulAction.orbit ↥Qb K).ncard ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    orbit_ncard_le_pRank_of_isComponent hsmul hfit hK h3K
  have horb_le3 : (MulAction.orbit ↥Qb K).ncard ≤ 3 := horb_le.trans c.pRank_threeStar_le
  have hnotfix := exists_smul_ne_of_not_le_normalizer hsmul hnot
  have horb_gt : 1 < (MulAction.orbit ↥Qb K).ncard :=
    one_lt_ncard_orbit_of_smul_ne hnotfix
  obtain ⟨N, hNnormal, hNindex, hNcard, horb_eq3, hNleNorm⟩ :=
    exists_stabilizer_data hsmul hQbcard horb_gt horb_le3
  let Nim : Subgroup X := N.map Qb.subtype
  have hNim3 : IsPGroup 3 ↥Nim := IsPGroup.map (hQb3.to_subgroup N) Qb.subtype
  have hNimcard : Nat.card ↥Nim = Nat.card ↥N :=
    Subgroup.card_map_of_injective Qb.subtype_injective
  have hNim_le_Qb : Nim ≤ Qb := Subgroup.map_subtype_le N
  have hdiv : ∀ C : Subgroup X, CFSG.IsComponent C → 3 ∣ Nat.card C :=
    fun C hC => (c.component_facts h2 hC).2.2
  obtain ⟨B, hBea, hBcard, hcent⟩ :=
    exists_span_of_three_orbit_components hsmul hfit hK hdiv horb_eq3 hNim3 hNleNorm
  have hNim_le_B : Nim ≤ B :=
    le_of_exponent_three_of_rank_le_three hBea hBcard hNim3
      (fun y hy => hexpQb y (hNim_le_Qb hy)) hcent c.pRank_threeStar_le
  have hcardle : Nat.card ↥Nim ≤ Nat.card ↥B := Subgroup.card_le_of_le hNim_le_B
  rw [hNimcard, hNcard, hBcard] at hcardle
  norm_num at hcardle

private theorem generalizedFitting_eq_of_unique_component {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hfit : CFSG.fittingSubgroup X = ⊥) (hK : CFSG.IsComponent K)
    (huniq : ∀ K' : Subgroup X, CFSG.IsComponent K' → K' = K) :
    CFSG.generalizedFitting X = K := by
  have hlayer : CFSG.layer X = K := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hK)
  rw [CFSG.generalizedFitting.eq_sup, hfit, hlayer, bot_sup_eq]

private theorem centralizer_eq_bot_of_unique_component {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hfit : CFSG.fittingSubgroup X = ⊥) (hK : CFSG.IsComponent K)
    (huniq : ∀ K' : Subgroup X, CFSG.IsComponent K' → K' = K) :
    Subgroup.centralizer (K : Set X) = ⊥ := by
  have hF : CFSG.generalizedFitting X = K :=
    generalizedFitting_eq_of_unique_component hfit hK huniq
  have hCKle : Subgroup.centralizer (K : Set X) ≤ K := by
    have h := CFSG.centralizer_generalizedFitting_le X
    rwa [hF] at h
  have hcentbot : (Subgroup.center ↥K).map K.subtype = ⊥ := by
    rw [CFSG.RankThree.GF2n.Tim81.center_component_eq_bot hfit hK, Subgroup.map_bot]
  have hinter : K ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (g : X) g.2)
    have hxmap : x ∈ (Subgroup.center ↥K).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype hxZ
    rw [hcentbot] at hxmap
    exact Subgroup.mem_bot.mp hxmap
  exact le_bot_iff.mp (le_inf hCKle le_rfl |>.trans_eq hinter)

theorem CaseOneCtx.exists_unique_component
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) :
    ∃ K : Subgroup (threeStar M), CFSG.IsComponent K ∧ K.Normal ∧
      (∀ K' : Subgroup (threeStar M), CFSG.IsComponent K' → K' = K) ∧
      Subgroup.centralizer (K : Set (threeStar M)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := threeStar M
  obtain ⟨K, hK⟩ := c.exists_isComponent_threeStar h2
  have hfit : CFSG.fittingSubgroup X = ⊥ := c.fitting_threeStar_eq_bot h2
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  have hQ3 : IsPGroup 3 ↥Q := c.choice.sylow.isPGroup
  have hA3 : IsPGroup 3 ↥((Subgroup.center ↥Q).map Q.subtype) :=
    IsPGroup.map (hQ3.to_subgroup (Subgroup.center ↥Q)) Q.subtype
  have hAM : (Subgroup.center ↥Q).map Q.subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans hQM
  have hAcard : Nat.card ↥(threeStarImg M ((Subgroup.center ↥Q).map Q.subtype)) = 3 := by
    rw [card_threeStarImg_of_isPGroup hA3 hAM]
    exact (h142 H E Q J c.choice c.typeA).1.2.2.2
  have hAne : threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hAcard
    simp at hAcard
  have huniq : ∀ K' : Subgroup X, CFSG.IsComponent K' → K' = K := by
    intro K' hK'
    by_contra hne
    have hQK : threeStarImg M Q ≤ Subgroup.normalizer (K : Set X) :=
      c.threeStarImg_le_normalizer_component h142 h2 hK
    have hQK' : threeStarImg M Q ≤ Subgroup.normalizer (K' : Set X) :=
      c.threeStarImg_le_normalizer_component h142 h2 hK'
    have hAleK : threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) ≤ K :=
      c.centerImg_le_of_normalizes h142 h2 hK hQK
    have hAleK' : threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) ≤ K' :=
      c.centerImg_le_of_normalizes h142 h2 hK' hQK'
    have hinf : K ⊓ K' = ⊥ :=
      (CFSG.RankThree.GF2n.Tim81.components_commute_inf hfit hK hK' (Ne.symm hne)).2
    have hle : threeStarImg M ((Subgroup.center ↥Q).map Q.subtype) ≤ ⊥ := by
      rw [← hinf]
      exact le_inf hAleK hAleK'
    exact hAne (le_bot_iff.mp hle)
  have hKnormal : K.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    exact huniq (K.map (MulAut.conj g).toMonoidHom)
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK)
  have hcentK : Subgroup.centralizer (K : Set X) = ⊥ :=
    centralizer_eq_bot_of_unique_component hfit hK huniq
  exact ⟨K, hK, hKnormal, huniq, hcentK⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
