module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightExclCover
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.Quasithin.Background.KnownMultOdd

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace GSz8Mult

theorem exists_sq_ne_one_pow_four {K : Type*} [Group K] {x : K} (hx : x ^ 2 ≠ 1) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : ∃ n : ℕ, (x ^ 2 ^ n) ^ 2 ≠ 1 ∧ (x ^ 2 ^ n) ^ 4 = 1 := by
  classical
  have hex : ∃ n, (x ^ 2) ^ 2 ^ n = 1 :=
    ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hx ?_)
    have h := Nat.find_spec hex
    rwa [h0, pow_zero, pow_one] at h
  have hmin := Nat.find_min hex (show n < Nat.find hex by omega)
  have hspec := Nat.find_spec hex
  rw [hn] at hspec
  have h2 : (x ^ 2 ^ n) ^ 2 = (x ^ 2) ^ 2 ^ n := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨n, h2 ▸ hmin, ?_⟩
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, ← pow_mul, ← pow_succ]
  exact hspec

open CFSG.ProperTwoGeneratedCore.Lemma37 in
theorem sq_eq_one_of_mem_center
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* CFSG.Theory.Comparator.SzModel 1) :
    ∀ x ∈ Subgroup.center K, x ^ 2 = 1 := by
  classical
  intro x hx
  by_contra hx2
  set Z := Subgroup.center K with hZdef
  obtain ⟨k, hk⟩ := hZ2 ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨n, hc₀2, hc₀4⟩ := exists_sq_ne_one_pow_four hx2 hk'
  set c₀ := x ^ 2 ^ n with hc₀def
  have hc₀ : c₀ ∈ Z := Z.pow_mem hx _
  obtain ⟨N, ⟨hNZ, hcN⟩, hNmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {N : Subgroup K | N ≤ Z ∧ c₀ ^ 2 ∉ N})
    ⟨⊥, bot_le, by simpa using hc₀2⟩
  have : N.Normal := Subgroup.normal_of_le_center hNZ
  have hcenter := center_quotient_eq_map hperf hNZ
  have : (Z.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  let e₁ : (K ⧸ N) ⧸ Subgroup.center (K ⧸ N) ≃* CFSG.Theory.Comparator.SzModel 1 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      ((QuotientGroup.quotientQuotientEquivQuotient N Z hNZ).trans e)
  have hZ2' : IsPGroup 2 (Subgroup.center (K ⧸ N)) := hcenter ▸ hZ2.map _
  have hc : (c₀ : K ⧸ N) ∈ Subgroup.center (K ⧸ N) := hcenter ▸ ⟨c₀, hc₀, rfl⟩
  have hcc : (c₀ : K ⧸ N) * c₀ ≠ 1 := by
    rw [← QuotientGroup.mk_mul, ← pow_two, Ne, QuotientGroup.eq_one_iff]
    exact hcN
  have hcccc : (c₀ : K ⧸ N) * c₀ * (c₀ * c₀) = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show c₀ * c₀ * (c₀ * c₀) = c₀ ^ 4 by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
      hc₀4, QuotientGroup.mk_one]
  refine false_of_szModel_of_mem_center (commutator_quotient_eq_top hperf N) hZ2' hc hcc hcccc
    (fun s hs hss => ?_) e₁
  by_cases hs1 : s = 1
  · exact Or.inl hs1
  right
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  set M := (Subgroup.zpowers s).comap (QuotientGroup.mk' N) with hMdef
  have hNM : N ≤ M := fun n hn => by
    change QuotientGroup.mk' N n ∈ Subgroup.zpowers s
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact (Subgroup.zpowers s).one_mem
  have hMZ : M ≤ Z := by
    intro k hk
    have hks : (k : K ⧸ N) ∈ Subgroup.center (K ⧸ N) :=
      Subgroup.zpowers_le.mpr hs hk
    rw [hcenter] at hks
    obtain ⟨z, hz, hzk⟩ := hks
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hzk
    rw [show k = z * (z⁻¹ * k) by group]
    exact Z.mul_mem hz (hNZ hzk)
  have hcM : c₀ ^ 2 ∈ M := by
    by_contra hcM
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective s
    have haM : a ∈ M := Subgroup.mem_zpowers _
    have haN := hNmax ⟨hMZ, hcM⟩ hNM haM
    exact hs1 ((QuotientGroup.eq_one_iff a).mpr haN)
  rcases eq_one_or_eq_of_mem_zpowers_two hs2 hcM with h | h
  · exact absurd ((QuotientGroup.eq_one_iff _).mp h) hcN
  · rw [← h, QuotientGroup.mk'_apply, pow_two, QuotientGroup.mk_mul]

theorem isPGroup_center {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Open.Sz 1) : IsPGroup 2 (Subgroup.center K) := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow (Subgroup.center K) le_rfl
    (e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv 1))
    fun _ _ hr2 _ Q => CFSG.SectionRank.suzuki_sylow_isCyclic 1 one_pos hr2 Q

theorem isElemAbelian_center
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Open.Sz 1) : IsElemAbelian 2 (Subgroup.center K) := by
  have hmodel : CFSG.Theory.Comparator.SzModel 1 = Sz 1 := by
    simp only [Sz, SzGenerators, CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators]
  exact ⟨inferInstance, sq_eq_one_of_mem_center hK.1 (isPGroup_center hK e)
    (e.trans (MulEquiv.subgroupCongr hmodel).symm)⟩

end GSz8Mult

end CFSG.Goldschmidt
