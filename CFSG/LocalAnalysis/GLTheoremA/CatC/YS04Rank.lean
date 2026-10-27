module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04G

open CFSG.Open CFSG.RankThree.PerfectCover

theorem le_glaTwoLocalRank_of_commute {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {t : G} (ht : orderOf t = 2) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ k) (hEt : ∀ x ∈ E, x * t = t * x) : k ≤ GLATwoLocalRank p G := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hP : Subgroup.zpowers t ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  have hP2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hEP : E ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (hEt x hx).symm n).eq
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (Subgroup.zpowers t : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEP hE hc
  exact h1.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _
    ⟨_, hP, hP2, rfl⟩)

theorem rank_le_of_hom {H K : Type} [Group H] [Finite H] [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (φ : H →* K) {E : Subgroup H} (hE : IsElemAbelian p E) {k c : ℕ}
    (hk : Nat.card E = p ^ k) {t : H} (ht2 : t ^ 2 = 1) (htφ : φ t ≠ 1)
    (hEt : ∀ x ∈ E, x * t = t * x) (hc : Nat.card ↥(E ⊓ φ.ker) ≤ p ^ c) :
    k - c ≤ GLATwoLocalRank p K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set ψ : ↥E →* K := φ.comp E.subtype with hψ
  have hker : Nat.card ψ.ker ≤ p ^ c := by
    have h1 : ψ.ker.map E.subtype = E ⊓ φ.ker := by
      ext x
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply,
        Subgroup.coe_subtype, Subgroup.mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxE, hxφ⟩
        exact ⟨⟨x, hxE⟩, hxφ, rfl⟩
    have h2 := Subgroup.card_map_of_injective (K := ψ.ker) E.subtype_injective
    rw [h1] at h2
    rw [← h2]
    exact hc
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hk] at hcard
  have hrange : ψ.range = E.map φ := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  haveI : IsMulCommutative ↥E := hE.1
  have hE' : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : K) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm' x y]
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hz
      have hx : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
      rw [← map_pow, hx, map_one]
  have hpg : IsPGroup p ψ.range := fun z => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE'.2 z z.2)⟩
  obtain ⟨k', hk'⟩ := IsPGroup.iff_card.mp hpg
  have hdvd : Nat.card ψ.ker ∣ p ^ k := ⟨Nat.card ψ.range, by rw [← hcard]⟩
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hjc : j ≤ c := by
    have : p ^ j ≤ p ^ c := hjk ▸ hker
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hkk : k' + j = k := by
    have : p ^ (k' + j) = p ^ k := by rw [pow_add, ← hk', ← hjk]; rw [mul_comm] at hcard; exact hcard
    exact Nat.pow_right_injective hp.two_le this
  have ht' : orderOf (φ t) = 2 := by
    refine orderOf_eq_prime ?_ htφ
    rw [← map_pow, ht2, map_one]
  have h2 := le_glaTwoLocalRank_of_commute hp ht' (E := ψ.range) hE' hk' (fun x hx => by
    rw [hrange] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul, ← map_mul, hEt y hy])
  omega

theorem card_inf_le_of_cyclic {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {N : Subgroup H} (hN : IsCyclic N) {E : Subgroup H} (hE : IsElemAbelian p E) :
    Nat.card ↥(E ⊓ N) ≤ p := by
  haveI : IsCyclic ↥(E ⊓ N) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_right : E ⊓ N ≤ N))
      (Subgroup.inclusion_injective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(E ⊓ N))
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 g (g.2.1))
  have h1 : orderOf g = Nat.card ↥(E ⊓ N) := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← h1]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)

theorem rank_of_cover {H K : Type} [Group H] [Finite H] [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (N : Subgroup H) [N.Normal] (hNc : N ≤ Subgroup.center H) (hNcyc : IsCyclic N)
    (hH : Group.IsPerfect H) (hK : Group.IsPerfect K) (ρ : K →* H ⧸ N)
    (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K)
    (hKp : IsPGroup p (Subgroup.center K)) [Finite (hopfMultiplier (H ⧸ N))]
    (hM : (Nat.card (hopfMultiplier (H ⧸ N))).factorization p ≤ (Nat.card N).factorization p)
    {E : Subgroup H} (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) {t : H}
    (ht2 : t ^ 2 = 1) (htN : t ∉ N) (hEt : ∀ x ∈ E, x * t = t * x) :
    k - 1 ≤ GLATwoLocalRank p K ∧
      (Nat.card (Subgroup.center K) = p ^ (Nat.card N).factorization p →
        k ≤ GLATwoLocalRank p K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set α : H →* H ⧸ N := QuotientGroup.mk' N with hα
  have hαk : α.ker = N := QuotientGroup.ker_mk' N
  obtain ⟨φ, hφs, hφ⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_hom_of_cover
    hH hK α (QuotientGroup.mk'_surjective N) (by rw [hαk]; exact hNc) ρ hρ
    (by rw [hρk]) hp (by rw [hρk]; exact hKp) (by rw [hαk]; exact hM)
  have hkerφ : φ.ker ≤ N := by
    intro x hx
    have h1 : ρ (φ x) = α x := DFunLike.congr_fun hφ x
    rw [MonoidHom.mem_ker.1 hx, map_one] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1.symm
  have htφ : φ t ≠ 1 := fun h => htN (hkerφ (MonoidHom.mem_ker.2 h))
  refine ⟨?_, fun hZ => ?_⟩
  · refine rank_le_of_hom hp φ hE hk ht2 htφ hEt (c := 1) ?_
    calc Nat.card ↥(E ⊓ φ.ker) ≤ Nat.card ↥(E ⊓ N) :=
          Subgroup.card_le_of_le (inf_le_inf_left E hkerφ)
      _ ≤ p := card_inf_le_of_cyclic hp hNcyc hE
      _ = p ^ 1 := (pow_one p).symm
  · have hXpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
    have h1 : Nat.card φ.ker * Nat.card K = Nat.card H := by
      have := Subgroup.card_ker_mul_card_range φ
      rwa [MonoidHom.range_eq_top.2 hφs, Subgroup.card_top] at this
    have h2 : Nat.card ρ.ker * Nat.card (H ⧸ N) = Nat.card K := by
      have := Subgroup.card_ker_mul_card_range ρ
      rwa [MonoidHom.range_eq_top.2 hρ, Subgroup.card_top] at this
    have h3 : Nat.card (H ⧸ N) * Nat.card N = Nat.card H :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
    rw [hρk, hZ] at h2
    have h4 : Nat.card φ.ker * p ^ (Nat.card N).factorization p = Nat.card N := by
      have : (Nat.card φ.ker * p ^ (Nat.card N).factorization p) * Nat.card (H ⧸ N) =
          Nat.card N * Nat.card (H ⧸ N) := by
        rw [mul_assoc, h2, h1, ← h3, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hXpos this
    have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have hkpos : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    have h5 : (Nat.card φ.ker).factorization p = 0 := by
      have := congrArg (fun m => m.factorization p) h4
      simp only [Nat.factorization_mul hkpos (pow_ne_zero _ hp.ne_zero),
        Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        hp.factorization_self, mul_one] at this
      omega
    have hndvd : ¬ p ∣ Nat.card φ.ker := by
      rw [hp.dvd_iff_one_le_factorization hkpos]
      omega
    have hEp : IsPGroup p ↥(E ⊓ φ.ker) := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
      exact hE.2 x x.2.1)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
    have hdvd : Nat.card ↥(E ⊓ φ.ker) ∣ Nat.card φ.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    have hn0 : n = 0 := by
      by_contra hne
      exact hndvd ((dvd_pow_self p hne).trans (hn ▸ hdvd))
    have hc0 : Nat.card ↥(E ⊓ φ.ker) ≤ p ^ 0 := by rw [hn, hn0]
    have := rank_le_of_hom hp φ hE hk ht2 htφ hEt (c := 0) hc0
    simpa using this

end CFSG.LocalAnalysis.GLTheoremA.YS04G
