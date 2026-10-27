module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.GH74.Uniqueness.Section15HeringCyclic
import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JOneSolvPrimes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOne

open CFSG.AGLEmbedding CFSG.Open

theorem exists_normal_pComplement_of_normalizer_le_centralizer {Y : Type*} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) {y : Y} (hyp : orderOf y = p)
    (hNC : Subgroup.normalizer (Subgroup.zpowers y : Set Y) ≤
      Subgroup.centralizer (Subgroup.zpowers y : Set Y))
    (hcyc : ∀ S : Subgroup Y, IsPGroup p S → IsCyclic S) :
    ∃ N : Subgroup Y, N.Normal ∧ ¬ p ∣ Nat.card N ∧ ∃ n : ℕ, N.index = p ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyp, pow_one])
  obtain ⟨Q, hQ⟩ := hZp.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup Y) := hcyc _ Q.isPGroup'
  obtain ⟨r, hr⟩ := hQcyc.exists_generator
  have hQr : (Q : Subgroup Y) = Subgroup.zpowers (r : Y) := by
    refine le_antisymm (fun z hz => ?_) (Subgroup.zpowers_le.2 r.2)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
  have hyQ : y ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers y)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf).1 Q.isPGroup' r
  have hm' : orderOf (r : Y) = p ^ m := by rw [Subgroup.orderOf_coe]; exact hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm'
    rw [hQr, hm', Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hyQ
    rw [hyQ, orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hpb : p ^ b ∣ orderOf (r : Y) := by rw [hm', pow_succ]; exact dvd_mul_right _ _
  have hcard : Nat.card (Subgroup.zpowers ((r : Y) ^ p ^ b)) = p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero b hp.ne_zero) hpb, hm', pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos b)]
  have hymem : y ∈ Subgroup.zpowers ((r : Y) ^ p ^ b) := by
    rw [hQr] at hyQ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hyQ
    have h1 : (r : Y) ^ (i * (p : ℤ)) = 1 := by
      rw [zpow_mul, hi, zpow_natCast]
      have := pow_orderOf_eq_one y
      rwa [hyp] at this
    have h2 : ((p ^ (b + 1) : ℕ) : ℤ) ∣ i * (p : ℤ) := by
      rw [← hm']
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have h3 : ((p ^ b : ℕ) : ℤ) ∣ i := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have : ((p ^ b : ℕ) : ℤ) * (p : ℤ) ∣ i * (p : ℤ) := by
        rw [← Nat.cast_mul, ← pow_succ]
        exact h2
      exact (mul_dvd_mul_iff_right hpz).1 this
    obtain ⟨j, hj⟩ := h3
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← hi, hj, zpow_mul, zpow_natCast]
  have hzeq : Subgroup.zpowers y = Subgroup.zpowers ((r : Y) ^ p ^ b) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hymem)
      (by rw [hcard, Nat.card_zpowers, hyp])
  rw [hzeq] at hNC
  obtain ⟨N, hNn, hNcop, hNidx⟩ :=
    CFSG.GH74.Uniqueness.Hering.exists_normal_pComplement_of_cyclic Q hQr hm' hNC
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 Q.isPGroup'
  exact ⟨N, hNn, hNcop, n, by rw [hNidx, hn]⟩

theorem eq_one_of_mem_zpowers_of_isPGroup_two {Γ : Type*} [Group Γ] {N : Subgroup Γ}
    (hN : IsPGroup 2 N) {z c : Γ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzp : orderOf z = p)
    (hcz : c ∈ Subgroup.zpowers z) (hcN : c ∈ N) : c = 1 := by
  obtain ⟨m, hm⟩ := hN ⟨c, hcN⟩
  have hc2 : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcp : c ^ p = 1 := by
    have := orderOf_dvd_of_mem_zpowers hcz
    rw [hzp] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h := (pow_gcd_eq_one (a := c) (m := p) (n := 2 ^ m)).mpr ⟨hcp, hc2⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

theorem not_dvd_card_of_perfect {A : Type*} [Group A] [Finite A] [Group.IsPerfect A] {p : ℕ}
    [Fact p.Prime] (M : Subgroup A) [M.Normal] (hM : ¬ p ∣ Nat.card M)
    (hpow : ∀ g : A, ∃ n : ℕ, g ^ p ^ n ∈ M) : ¬ p ∣ Nat.card A := by
  have hp : IsPGroup p (A ⧸ M) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hn⟩
  haveI : Group.IsNilpotent (A ⧸ M) := hp.isNilpotent
  haveI : Subsingleton (A ⧸ M) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isNilpotent (A ⧸ M) ‹_›
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have : (QuotientGroup.mk g : A ⧸ M) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff g).1 this
  intro hdvd
  apply hM
  rwa [hMtop, Subgroup.card_top]

theorem two_dvd_card_of_symThree {Q : Type} [Group Q] (h : IsSymThreeOrSUThreeTwo Q) :
    2 ∣ Nat.card Q := by
  rcases h with ⟨f⟩ | ⟨K, _, _, hK, ⟨f⟩⟩
  · rw [Nat.card_congr f.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K hK
    have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1)
      (by rw [hK]; norm_num)
    rw [pow_one] at h2
    rw [Nat.card_congr f.toEquiv, h2]
    norm_num

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_of_symThree (hSU : KFactSUThreeTwoNoNormalThreePrime) {I : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I))
    (M : Subgroup ↥I) [M.Normal] (hM : ¬ p ∣ Nat.card M)
    (hpow : ∀ g : ↥I, ∃ n : ℕ, g ^ p ^ n ∈ M) : ¬ p ∣ Nat.card I := by
  intro hpI
  have hp3 : p = 3 := (prime_eq_of_dvd_card_of_symThree hb hp hpI).resolve_left hp2
  subst hp3
  set π : ↥I →* ↥I ⧸ CFSG.pCore 2 ↥I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  haveI : (M.map π).Normal := Subgroup.Normal.map ‹_› π (QuotientGroup.mk'_surjective _)
  have h3 : ¬ 3 ∣ Nat.card (M.map π) := fun h => hM (h.trans (Subgroup.card_map_dvd M π))
  have hbot : M.map π = ⊥ := SevenFourL34.normal_eq_bot_of_not_three_dvd hSU hb (M.map π) h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥I ⧸ CFSG.pCore 2 ↥I) 2
    (two_dvd_card_of_symThree hb)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨n, hn⟩ := hpow g
  have h1 : π g ^ 3 ^ n = 1 := by
    have : π (g ^ 3 ^ n) ∈ M.map π := Subgroup.mem_map_of_mem π hn
    rw [hbot, Subgroup.mem_bot, map_pow] at this
    exact this
  have h2 : orderOf (π g) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (π g) = 2 := ht
  rw [h4] at h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

theorem exists_mem_cZero_dvd_card {H L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpJ : p ∣ Nat.card (jZero H L)) : ∃ I ∈ cZero (H ⊓ L), p ∣ Nat.card I := by
  by_contra hne
  push Not at hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hJ : jZero H L ≤ (CFSG.pPrimeCore p ↥(H ⊓ L)).map (H ⊓ L).subtype := by
    refine iSup₂_le fun I hI => ?_
    have hle : I ≤ H ⊓ L := hI.le
    have hsn : (I.subgroupOf (H ⊓ L)).IsSubnormal :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hle).1 hI.subnormal
    have hcop : Nat.Coprime p (Nat.card (I.subgroupOf (H ⊓ L))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hp.coprime_iff_not_dvd.2 (hne I hI)
    have hcore := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hsn hcop
    intro x hx
    exact ⟨⟨x, hle hx⟩, hcore (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hdvd := hpJ.trans (Subgroup.card_dvd_of_le hJ)
  rw [Subgroup.card_map_of_injective (H ⊓ L).subtype_injective] at hdvd
  exact hp.coprime_iff_not_dvd.1 CFSG.pPrimeCore_coprime_card hdvd

theorem exists_normal_pPrime_of_comm {J : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (hz : z ∈ J) (hzp : orderOf z = p)
    (hcyc : ∀ S : Subgroup G, S ≤ J → IsPGroup p S → IsCyclic S)
    (hc : ∀ x ∈ J, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 J) :
    ∃ N : Subgroup ↥J, N.Normal ∧ ¬ p ∣ Nat.card N ∧ ∃ n : ℕ, ∀ g : ↥J, g ^ p ^ n ∈ N := by
  have hzord : orderOf (⟨z, hz⟩ : ↥J) = p := by rw [Subgroup.orderOf_mk]; exact hzp
  have hcycJ : ∀ S : Subgroup ↥J, IsPGroup p S → IsCyclic S := by
    intro S hS
    have h1 : IsCyclic ↥(S.map J.subtype) := hcyc _ (Subgroup.map_subtype_le _) (hS.map _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective S J.subtype J.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hNC : Subgroup.normalizer (Subgroup.zpowers (⟨z, hz⟩ : ↥J) : Set ↥J) ≤
      Subgroup.centralizer (Subgroup.zpowers (⟨z, hz⟩ : ↥J) : Set ↥J) := by
    intro g hg
    have hg1 := (Subgroup.mem_normalizer_iff.mp hg ⟨z, hz⟩).mp (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg1
    have hk' : z ^ k = (g : G) * z * (g : G)⁻¹ := by simpa using congrArg Subtype.val hk
    have hcg : z * (g : G) * z⁻¹ * (g : G)⁻¹ ∈ pCoreOf 2 J := hc g g.2
    have hinv : (z * (g : G) * z⁻¹ * (g : G)⁻¹)⁻¹ = z ^ (k - 1) := by
      rw [zpow_sub_one, hk']
      group
    have hcz : (z * (g : G) * z⁻¹ * (g : G)⁻¹)⁻¹ ∈ Subgroup.zpowers z := by
      rw [hinv]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _
    have hc1 : (z * (g : G) * z⁻¹ * (g : G)⁻¹)⁻¹ = 1 :=
      eq_one_of_mem_zpowers_of_isPGroup_two
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J) hp hp2 hzp hcz
        ((pCoreOf 2 J).inv_mem hcg)
    have hcomm : z * (g : G) = (g : G) * z := by
      rw [inv_eq_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
      exact hc1
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute (⟨z, hz⟩ : ↥J) g from Subtype.ext hcomm) m).eq
  obtain ⟨N, hNn, hNp, n, hn⟩ :=
    exists_normal_pComplement_of_normalizer_le_centralizer hp hzord hNC hcycJ
  exact ⟨N, hNn, hNp, n, fun g => by rw [← hn]; exact Subgroup.pow_index_mem N g⟩

theorem false_of_comm_jZero_of_cyclic
    (hSU : KFactSUThreeTwoNoNormalThreePrime)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H L : Subgroup G} {z : G}
    (hz : z ∈ jZero H L) (hzp : orderOf z = p)
    (hcyc : ∀ S : Subgroup G, S ≤ jZero H L → IsPGroup p S → IsCyclic S)
    (hpJ : p ∣ Nat.card (jZero H L))
    (hc : ∀ x ∈ jZero H L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hNn, hNp, n, hn⟩ := exists_normal_pPrime_of_comm hp hp2 hz hzp hcyc hc
  obtain ⟨I, hI, hpI⟩ := exists_mem_cZero_dvd_card hp hpJ
  have hIJ : I ≤ jZero H L := IsCZeroMember.le_jZero hI
  haveI : (N.comap (Subgroup.inclusion hIJ)).Normal := hNn.comap _
  have hM : ¬ p ∣ Nat.card (N.comap (Subgroup.inclusion hIJ)) := fun h =>
    hNp (h.trans (Subgroup.card_comap_dvd_of_injective N _ (Subgroup.inclusion_injective hIJ)))
  have hpow : ∀ g : ↥I, ∃ n : ℕ, g ^ p ^ n ∈ N.comap (Subgroup.inclusion hIJ) := fun g =>
    ⟨n, by rw [Subgroup.mem_comap, map_pow]; exact hn _⟩
  rcases hI.shape with hperf | ⟨_, hb⟩
  · haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 hperf.perfect
    exact not_dvd_card_of_perfect _ hM hpow hpI
  · exact not_dvd_card_of_symThree hSU hp hp2 hb _ hM hpow hpI

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOne
