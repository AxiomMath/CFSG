module

public import CFSG.Open.GLADefs
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
import CFSG.LocalAnalysis.AGLEmbedding.OneLieBender

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem glaPComponent_of_isComponentOf_of_pPrimeCoreOf_eq_bot {G : Type*} [Group G]
    [Finite G] {p : ℕ} {C J : Subgroup G} (hC : CFSG.Open.GLAPPrimeCoreOf p C = ⊥)
    (hJ : CFSG.Open.IsComponentOf J C) : CFSG.Open.GLAPComponent p C J := by
  have hcore : GLAPPrimeCore p ↥C = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hC
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  refine ⟨hJ.1, hJ.2.1, ⟨le_top, barX_isSubnormal_top p hJ.2.1, ?_⟩, ?_⟩
  · let e : ↥J ≃* ↥(barX p C J) :=
      (Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans (Subgroup.equivMapOfInjective _ _ hinj)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hJ.2.2
  · intro J' hlt _ heq
    have h1 : J'.subgroupOf C = J.subgroupOf C := Subgroup.map_injective hinj heq
    have h2 : J' = J := by
      have := congrArg (Subgroup.map C.subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le (hlt.le.trans hJ.1),
        Subgroup.map_subgroupOf_eq_of_le hJ.1] at this
    exact hlt.ne h2

theorem centralizer_pCore_le_pCore_of_noComp {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C : Subgroup G} (hO : CFSG.Open.GLAPPrimeCoreOf p C = ⊥)
    (hnc : ∀ J : Subgroup G, ¬ CFSG.Open.GLAPComponent p C J) :
    Subgroup.centralizer (CFSG.pCore p ↥C : Set ↥C) ≤ CFSG.pCore p ↥C := by
  refine CFSG.AGLEmbedding.centralizer_pCore_le_pCore_of_forall (X := ↥C) ?_ ?_
  · intro L hL
    have hcomp : CFSG.Open.IsComponentOf (L.map C.subtype) C := by
      refine ⟨?_, ?_, ?_⟩
      · rintro x ⟨y, -, rfl⟩
        exact y.2
      · have h := hL.2.1.map C.subtype
        rwa [Subgroup.map_top, Subgroup.range_subtype] at h
      · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective L C.subtype C.subtype_injective) hL.2.2
    exact hnc (L.map C.subtype)
      (glaPComponent_of_isComponentOf_of_pPrimeCoreOf_eq_bot hO hcomp)
  · intro q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := q) (G := ↥C))
    have hcop : Nat.Coprime p (Nat.card (CFSG.pCore q ↥C)) := by
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_primes hp hq |>.2 (Ne.symm hqp))
    have hle : CFSG.pCore q ↥C ≤ CFSG.Open.GLAPPrimeCore p ↥C :=
      le_sSup (show CFSG.pCore q ↥C ∈
        {K : Subgroup ↥C | K.Normal ∧ Nat.Coprime p (Nat.card K)}
        from ⟨inferInstance, hcop⟩)
    have hmap : (CFSG.pCore q ↥C).map C.subtype ≤ CFSG.Open.GLAPPrimeCoreOf p C :=
      Subgroup.map_mono hle
    rw [hO] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1
      (le_bot_iff.1 hmap)

private theorem exists_index_of_fixed_subgroup {G : Type*} [Group G] [Finite G]
    {p r m : ℕ} (hp : p.Prime) (hr : r.Prime) {R : Subgroup G}
    (hR : Nat.card R = p ^ m) {w : G} (hw : orderOf w = r)
    (hwR : w ∈ Subgroup.normalizer (R : Set G))
    (S : Subgroup (Subgroup.normalizer (R : Set G)))
    (hS : S = Subgroup.zpowers (⟨w, hwR⟩ : Subgroup.normalizer (R : Set G)))
    (F : Subgroup R) (hF : F = FixedPoints.subgroup S R)
    (hwC : w ∉ Subgroup.centralizer (R : Set G)) :
    ∃ i, Nat.card F = p ^ i ∧ F ≠ ⊤ ∧ p ^ m ≡ p ^ i [MOD r] := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have htr : IsPGroup r (Subgroup.zpowers w) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hw, pow_one]
  have hSr : IsPGroup r S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htr
    refine IsPGroup.of_card (n := k) ?_
    rw [hS, Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers, hk]
  have hmod := hSr.card_modEq_card_fixedPoints R
  have hFcard : Nat.card (MulAction.fixedPoints S R) = Nat.card F := by
    rw [hF]
    rfl
  rw [hFcard, hR] at hmod
  obtain ⟨i, -, hFi⟩ := (Nat.dvd_prime_pow hp).mp (hR ▸ Subgroup.card_subgroup_dvd_card F)
  have hFtop : F ≠ ⊤ := by
    intro htop
    apply hwC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have ht'mem : (⟨w, hwR⟩ : Subgroup.normalizer (R : Set G)) ∈ S := by
      rw [hS]
      exact Subgroup.mem_zpowers _
    have hmem : (⟨y, hy⟩ : R) ∈ FixedPoints.subgroup S R := by
      rw [← hF]
      exact htop ▸ Subgroup.mem_top _
    have h := congrArg Subtype.val
      ((FixedPoints.mem_subgroup S R _).mp hmem ⟨_, ht'mem⟩)
    have h3 : (((⟨_, ht'mem⟩ : S) • (⟨y, hy⟩ : R) : R) : G) = w * y * w⁻¹ := rfl
    rw [h3] at h
    calc y * w = (w * y * w⁻¹) * w := by rw [h]
      _ = w * y := by group
  have hlt : Nat.card F < Nat.card R :=
    lt_of_le_of_ne (Subgroup.card_le_card_group F) fun h =>
      hFtop ((Subgroup.card_eq_iff_eq_top F).1 h)
  rw [hR, hFi] at hlt
  have him : i < m := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  rw [hFi] at hmod
  exact ⟨i, hFi, hFtop, hmod⟩

private theorem mem_fixedSubgroup_of_commute {G : Type*} [Group G] {R : Subgroup G}
    {w z : G} (hwR : w ∈ Subgroup.normalizer (R : Set G)) (hzR : z ∈ R)
    (hwz : w * z = z * w) :
    (⟨z, hzR⟩ : R) ∈
      FixedPoints.subgroup
        (Subgroup.zpowers (⟨w, hwR⟩ : Subgroup.normalizer (R : Set G))) R := by
  set t' : Subgroup.normalizer (R : Set G) := ⟨w, hwR⟩
  have ht'z : t' • (⟨z, hzR⟩ : R) = ⟨z, hzR⟩ := by
    refine Subtype.ext ?_
    change w * z * w⁻¹ = z
    rw [hwz, mul_assoc, mul_inv_cancel, mul_one]
  have hstab : Subgroup.zpowers t' ≤
      MulAction.stabilizer (Subgroup.normalizer (R : Set G)) (⟨z, hzR⟩ : R) :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 ht'z)
  rw [FixedPoints.mem_subgroup]
  intro m
  rw [Subgroup.smul_def]
  exact MulAction.mem_stabilizer_iff.1 (hstab m.2)

private theorem exists_dvd_pow_sub_one_of_modEq {p r m i : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : r ≠ p) (hi0 : 0 < i) (him : i < m) (hmod : p ^ m ≡ p ^ i [MOD r]) :
    ∃ k, 1 ≤ k ∧ k < m ∧ r ∣ p ^ k - 1 := by
  have hdvd : r ∣ p ^ m - p ^ i :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.pos him.le)).1 hmod.symm
  have hsub : p ^ m - p ^ i = p ^ i * (p ^ (m - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' him.le]
  rw [hsub] at hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h)) hrp
  · exact ⟨m - i, by omega, by omega, h⟩

theorem exists_dvd_pow_sub_one_of_not_mem_centralizer {G : Type*} [Group G] [Finite G]
    {p r m : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) {R : Subgroup G}
    (hR : Nat.card R = p ^ m) {w z : G} (hw : orderOf w = r)
    (hwR : w ∈ Subgroup.normalizer (R : Set G)) (hzR : z ∈ R) (hz : z ≠ 1)
    (hwz : w * z = z * w) (hwC : w ∉ Subgroup.centralizer (R : Set G)) :
    ∃ k, 1 ≤ k ∧ k < m ∧ r ∣ p ^ k - 1 := by
  let t' : Subgroup.normalizer (R : Set G) := ⟨w, hwR⟩
  let S : Subgroup (Subgroup.normalizer (R : Set G)) := Subgroup.zpowers t'
  let F : Subgroup R := FixedPoints.subgroup S R
  have hS : S = Subgroup.zpowers (⟨w, hwR⟩ : Subgroup.normalizer (R : Set G)) := rfl
  have hF : F = FixedPoints.subgroup S R := rfl
  obtain ⟨i, hFi, hFtop, hmod⟩ :=
    exists_index_of_fixed_subgroup hp hr hR hw hwR S hS F hF hwC
  have hzF : (⟨z, hzR⟩ : R) ∈ F := mem_fixedSubgroup_of_commute hwR hzR hwz
  have him : i < m := by
    have hlt : Nat.card F < Nat.card R :=
      lt_of_le_of_ne (Subgroup.card_le_card_group F) fun h =>
        hFtop ((Subgroup.card_eq_iff_eq_top F).1 h)
    rw [hR, hFi] at hlt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  have hi0 : 0 < i := by
    by_contra h
    have h0 : i = 0 := by omega
    have hFbot : F = ⊥ := (Subgroup.card_eq_one).1 (by rw [hFi, h0, pow_zero])
    rw [hFbot, Subgroup.mem_bot] at hzF
    exact hz (congrArg Subtype.val hzF)
  exact exists_dvd_pow_sub_one_of_modEq hp hr hrp hi0 him hmod

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
