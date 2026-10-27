module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.TorusRank
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)

variable {K : Type} [Field K]

theorem pRank_statedProj_le [Finite K] {p f n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = r ^ f ∧ H = StatedSL n K ∧ p ∣ r ^ f - 1) ∨
      (Nat.card K = (r ^ f) ^ 2 ∧ H = StatedSU n (r ^ f) K ∧ p ∣ r ^ f + 1)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) ≤ n - 1 := by
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    rcases hH with ⟨hK, -, hd⟩ | ⟨hK, -, hd⟩
    · rw [hK]
      exact hd
    · have hq : 1 ≤ r ^ f := by
        by_contra h0
        have h1 : r ^ f = 0 := by omega
        rw [h1] at hK
        simp at hK
        exact absurd hK (Nat.card_pos (α := K)).ne'
      rw [hK, sq_sub_one_eq hq]
      exact Dvd.dvd.mul_right hd _
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  refine card_le_of_scalar_kernel hp hp2 hpK hn H
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf H)) ?_ E ?_ hE
  · intro A
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  · rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact le_top

theorem rank_of_cover_succ [Finite K] {L : Type} [Group L] [Finite L]
    (hLperf : Group.IsPerfect L) {p f n r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (hn : 4 ≤ n) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (β : L →* StatedProj H) (hβ : Function.Surjective β) (hβc : β.ker ≤ Subgroup.center L)
    (hβp : IsPGroup r β.ker) (z : L) (hz : z ∈ β.ker) (hz1 : z ≠ 1) (hzr : z ^ r = 1)
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization r ≤
      (Nat.card ((StatedScalars (Fin n) K).subgroupOf H)).factorization r) :
    n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have : Fact r.Prime := ⟨hr⟩
  have hHK : (Nat.card K = p ^ f ∧ H = StatedSL n K) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K) := by
    rcases hH with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hHperf := isPerfect_linUni hp hn hHK
  set D := (StatedScalars (Fin n) K).subgroupOf H with hD
  have hDc : D ≤ Subgroup.center H := scalars_le_center H
  let α : H →* StatedProj H := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  obtain ⟨φ, hφs, hβφ⟩ := exists_hom_of_cover hHperf hLperf α hα (hαk ▸ hDc) β hβ hβc hr hβp
    (by rw [hαk]; exact hM)
  have hkerφ : φ.ker ≤ D := by
    intro h hh
    have h1 : α h = 1 := by
      rw [← hβφ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hh, map_one]
    rw [← hαk]
    exact h1
  obtain ⟨y, hy⟩ := hφs z
  have hyD : y ∈ D := by
    have h1 : α y = 1 := by
      rw [← hβφ, MonoidHom.comp_apply, hy]
      exact hz
    rw [← hαk]
    exact h1
  have hyr : y ^ r ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hzr]
  have hyC : y ∉ φ.ker := by
    rw [MonoidHom.mem_ker, hy]
    exact hz1
  have hrank := scalar_quotient_torus_rank_succ (K := K) hp (by omega) hr2 hH φ.ker hkerφ y hyD
    hyr hyC
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)] at hrank
  exact hrank

@[expose] def centerPPrime (L : Type) [Group L] (p : ℕ) : Subgroup L where
  carrier := {g | g ∈ Subgroup.center L ∧ Nat.Coprime p (orderOf g)}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have hc : Commute a b := Subgroup.mem_center_iff.1 hb a
    refine Nat.Coprime.coprime_dvd_right (hc.orderOf_mul_dvd_lcm) ?_
    exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_right ha' hb')
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Subgroup.inv_mem _ ha, by rwa [orderOf_inv]⟩

theorem centerPPrime_le_center (L : Type) [Group L] (p : ℕ) :
    centerPPrime L p ≤ Subgroup.center L := fun _ h => h.1

instance centerPPrime_normal (L : Type) [Group L] (p : ℕ) : (centerPPrime L p).Normal :=
  Subgroup.normal_of_le_center (centerPPrime_le_center L p)

theorem not_dvd_card_centerPPrime (L : Type) [Group L] [Finite L] {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (centerPPrime L p) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centerPPrime L p)) p hd
  have h1 : orderOf (g : L) = p := by rw [Subgroup.orderOf_coe]; exact hg
  have h2 := g.2.2
  rw [h1] at h2
  exact hp.one_lt.ne' (Nat.coprime_self p |>.1 h2)

theorem rank_ge_cover [Finite K] {L : Type} [Group L] [Finite L]
    (hLperf : Group.IsPerfect L) {p f n r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (hn : 4 ≤ n) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (e : L ⧸ Subgroup.center L ≃* StatedProj H) (hrZ : r ∣ Nat.card (Subgroup.center L))
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization r ≤
      (Nat.card ((StatedScalars (Fin n) K).subgroupOf H)).factorization r) :
    n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have : Fact r.Prime := ⟨hr⟩
  set Q := centerPPrime L r with hQ
  set β₀ := CFSG.GH74.Generic.centralQuotientMap e with hβ₀
  have hβ₀k : β₀.ker = Subgroup.center L := CFSG.GH74.Generic.centralQuotientMap_ker e
  have hβ₀s : Function.Surjective β₀ := CFSG.GH74.Generic.centralQuotientMap_surjective e
  have hQker : Q ≤ β₀.ker := by
    rw [hβ₀k]
    exact centerPPrime_le_center L r
  let β : L ⧸ Q →* StatedProj H := QuotientGroup.lift Q β₀ hQker
  have hβmk : ∀ g : L, β (QuotientGroup.mk g) = β₀ g := fun g => rfl
  have hβs : Function.Surjective β := by
    intro x
    obtain ⟨g, rfl⟩ := hβ₀s x
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hperf₁ : Group.IsPerfect (L ⧸ Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  have hβc : β.ker ≤ Subgroup.center (L ⧸ Q) := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ Subgroup.center L := by
      rw [← hβ₀k]
      exact (hβmk g).symm.trans (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hg g']
  have hβp : IsPGroup r β.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ Subgroup.center L := by
      rw [← hβ₀k]
      exact (hβmk g).symm.trans (MonoidHom.mem_ker.mp hx)
    set a := (orderOf g).factorization r with ha
    have hdvd : r ^ a ∣ orderOf g := Nat.ordProj_dvd _ r
    have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hordg : orderOf (g ^ (r ^ a)) = orderOf g / r ^ a :=
      orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd
    have hcop : Nat.Coprime r (orderOf g / r ^ a) := by
      have := Nat.coprime_ordCompl hr hord0
      exact this
    have hmem : g ^ (r ^ a) ∈ Q := ⟨Subgroup.pow_mem _ hg _, by rw [hordg]; exact hcop⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk g : L ⧸ Q) ^ (r ^ a) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) r hrZ
  have hzo : orderOf (z : L) = r := by rw [Subgroup.orderOf_coe]; exact hz
  have hzr : (z : L) ^ r = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hzQ : (z : L) ∉ Q := by
    intro h
    have h2 := h.2
    rw [hzo] at h2
    exact hr.one_lt.ne' (Nat.coprime_self r |>.1 h2)
  have hrank := rank_of_cover_succ hperf₁ hp hr hr2 hn hH β hβs hβc hβp
    (QuotientGroup.mk (z : L)) (by
      rw [MonoidHom.mem_ker, hβmk]
      rw [← MonoidHom.mem_ker, hβ₀k]
      exact z.2)
    (by
      intro h
      exact hzQ (QuotientGroup.eq_one_iff _ |>.1 h))
    (by rw [← QuotientGroup.mk_pow, hzr, QuotientGroup.mk_one]) hM
  rw [CFSG.SectionRank.pRank_quotient_eq Q (not_dvd_card_centerPPrime L hr)] at hrank
  exact hrank

end CFSG.HardMathSupport.Timmesfeld.LinearRank
