module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (factorization_card_table)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem isPerfect_statedSL_three (F : Type) [Field F] : Group.IsPerfect (StatedSL 3 F) := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
    (by norm_num)
  exact Group.IsPerfect.ofSurjective
    (f := (specialLinearGroupEquivStatedSL 3 F).toMonoidHom)
    (specialLinearGroupEquivStatedSL 3 F).surjective

theorem isPerfect_statedSU_three {p f : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [Finite F]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) :
    Group.IsPerfect (StatedSU 3 (p ^ f) F) := by
  have hcard : Nat.card Fˣ = (p ^ f) ^ 2 - 1 := by
    rw [CFSG.SectionRank.OddCover.card_units_eq, hF]
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (K := F) (d := Nat.card Fˣ) dvd_rfl
  have h3 : 3 = 3 → ∃ s : F, s ≠ 0 ∧
      CFSG.LieType.BorelTits.unitaryInvolution F p f s * s ≠ 1 := by
    intro _
    refine ⟨(ζ : F), ζ.ne_zero, ?_⟩
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    intro h
    have hu : ζ ^ (p ^ f + 1) = 1 := by
      ext
      simpa using h
    have hdvd : orderOf ζ ∣ p ^ f + 1 := orderOf_dvd_of_pow_eq_one hu
    rw [hζ, hcard] at hdvd
    have hle : (p ^ f) ^ 2 - 1 ≤ p ^ f + 1 := Nat.le_of_dvd (by omega) hdvd
    have h1 : (p ^ f) ^ 2 ≤ p ^ f + 1 + 1 := (Nat.sub_le_iff_le_add).1 hle
    have h2 : 3 * p ^ f ≤ p ^ f * p ^ f := Nat.mul_le_mul_right (p ^ f) hq
    nlinarith
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF) (n := 3)
    (by norm_num) h3
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3]
  exact hperf

variable {K : Type} [Field K]

theorem rank_of_cover_succ_perfect [Finite K] {L : Type} [Group L] [Finite L]
    (hLperf : Group.IsPerfect L) {p f n r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (hn : 2 ≤ n) {H : Subgroup (GL (Fin n) K)} (hHP : Group.IsPerfect H)
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (β : L →* StatedProj H) (hβ : Function.Surjective β) (hβc : β.ker ≤ Subgroup.center L)
    (hβp : IsPGroup r β.ker) (z : L) (hz : z ∈ β.ker) (hz1 : z ≠ 1) (hzr : z ^ r = 1)
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization r ≤
      (Nat.card ((StatedScalars (Fin n) K).subgroupOf H)).factorization r) :
    n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have : Fact r.Prime := ⟨hr⟩
  have hHperf := hHP
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
  have hrank := scalar_quotient_torus_rank_succ (K := K) hp hn hr2 hH φ.ker hkerφ y hyD
    hyr hyC
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)] at hrank
  exact hrank

theorem rank_ge_cover_perfect [Finite K] {L : Type} [Group L] [Finite L]
    (hLperf : Group.IsPerfect L) {p f n r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (hn : 2 ≤ n) {H : Subgroup (GL (Fin n) K)} (hHP : Group.IsPerfect H)
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
  have hrank := rank_of_cover_succ_perfect hperf₁ hp hr hr2 hn hHP hH β hβs hβc hβp
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

theorem pRank_ge_two_PSL (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) {F : Type} [Field F] [Finite F] {r f : ℕ}
    (hadm : StatedLieAdmissible .PSL 3 r f) (hF : Nat.card F = r ^ f)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL 3 F)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ r ^ f - 1) (hne : p ≠ r)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := hF ▸ Nat.card_pos
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSL 3 F)) .PSL 3 r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have ha : p ∣ (genericOrders .PSL 3 r f).1 :=
    dvd_generic_of_dvd_center hGA hK e hmm (Or.inl rfl) hp hp2 hne hpZ
  have hga : (genericOrders .PSL 3 r f).1 = Nat.gcd 3 (r ^ f - 1) := rfl
  obtain ⟨hfin, hcard⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf
    hGA hmm
  haveI := hfin
  have hdv : (genericOrders .PSL 3 r f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by norm_num)
      hq0 (Or.inl ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL 3 F)))).factorization p ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).factorization p := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2
      hdv p
  have : Fact p.Prime := ⟨hp⟩
  have := rank_ge_cover_perfect (K := F) ⟨hK.1⟩ hr hp hp2 (by norm_num)
    (isPerfect_statedSL_three F) (Or.inl ⟨hF, rfl, hpq⟩) e hpZ hM
  simpa using this

theorem pRank_ge_two_PSU (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) {F : Type} [Field F] [Finite F] {r f : ℕ}
    (hadm : StatedLieAdmissible .PSU 3 r f) (hF : Nat.card F = (r ^ f) ^ 2)
    (hq3 : 3 ≤ r ^ f)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU 3 (r ^ f) F)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ r ^ f + 1) (hne : p ≠ r)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := by omega
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F r := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU 3 (r ^ f) F)) .PSU 3 r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have ha : p ∣ (genericOrders .PSU 3 r f).1 :=
    dvd_generic_of_dvd_center hGA hK e hmm (Or.inr (Or.inl rfl)) hp hp2 hne hpZ
  have hga : (genericOrders .PSU 3 r f).1 = Nat.gcd 3 (r ^ f + 1) := rfl
  obtain ⟨hfin, hcard⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf
    hGA hmm
  haveI := hfin
  have hdv : (genericOrders .PSU 3 r f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (r ^ f) F)) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by norm_num)
      hq0 (Or.inr ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU 3 (r ^ f) F)))).factorization p ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (r ^ f) F))).factorization p := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2
      hdv p
  have : Fact p.Prime := ⟨hp⟩
  have := rank_ge_cover_perfect (K := F) ⟨hK.1⟩ hr hp hp2 (by norm_num)
    (isPerfect_statedSU_three (p := r) (f := f) hF hq3) (Or.inr ⟨hF, rfl, hpq⟩) e hpZ hM
  simpa using this

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
