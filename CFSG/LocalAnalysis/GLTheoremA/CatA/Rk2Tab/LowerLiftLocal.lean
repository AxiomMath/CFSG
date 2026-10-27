module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Shared
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic
public import CFSG.ClassicalInvolution.Sp62Rec.FourLift
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem le_twoLocalPrimeRank_of_normalizer {G : Type} [Group G] [Finite G] {r k : ℕ}
    (hr : r.Prime) {X E : Subgroup G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set G)) : k ≤ CFSG.Open.twoLocalPrimeRank r G := by
  have h1 : k ≤ CFSG.Open.pRank r (Subgroup.normalizer (X : Set G)) :=
    CFSG.SectionRank.le_pRank hr.one_lt hXE hE hEcard
  exact h1.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr _
    ⟨X, hX, hX2, rfl⟩)

theorem le_twoLocalPrimeRank_of_quotient {G : Type} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : ¬ r ∣ Nat.card N) {X E : Subgroup (G ⧸ N)} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set (G ⧸ N))) :
    k ≤ CFSG.Open.twoLocalPrimeRank r G := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  set H : Subgroup G := X.comap π with hH
  have hcardH : Nat.card H = Nat.card X * Nat.card N := by
    rw [hH]
    exact CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk N X
  obtain ⟨B, hBle, hBelem, hBcard⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift hr
      (by rw [hπ, QuotientGroup.ker_mk']; exact hrN)
      (π := π) (P := E.comap π) (E := E)
      (Subgroup.map_comap_eq_self_of_surjective (f := π) hπsurj E) hE
  have hBcard' : Nat.card B = r ^ k := hBcard.2.trans hEcard
  have hBnle : B ≤ Subgroup.normalizer (H : Set G) := by
    intro b hb
    have hb' : π b ∈ E := Subgroup.mem_comap.1 (hBle hb)
    rw [hH, ← Subgroup.comap_normalizer_eq_of_surjective X hπsurj, Subgroup.mem_comap]
    exact hXE hb'
  have hcoprime : Nat.Coprime r (Nat.card H) := by
    rw [hcardH]
    refine Nat.Coprime.mul_right ?_ ?_
    · obtain ⟨n, hn⟩ := hX2.exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right n
    · exact (hr.coprime_iff_not_dvd).2 hrN
  obtain ⟨S, -, hSnorm⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_pgroup_actor_sylow_containing r 2 hr
      Nat.prime_two B H ⊥ (isPGroup_of_isElemAbelian hBelem) hBnle hcoprime bot_le
      (IsPGroup.of_bot (p := 2)) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hP2 : IsPGroup 2 ((S : Subgroup H).map H.subtype) := S.isPGroup'.map H.subtype
  have h2H : 2 ∣ Nat.card H := by
    rw [hcardH]
    refine dvd_mul_of_dvd_left ?_ _
    have h1 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).mpr hX
    exact (hX2.card_eq_or_dvd).resolve_left h1.ne'
  have hPne : (S : Subgroup H).map H.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective (S : Subgroup H) (f := H.subtype)
      H.subtype_injective]
    exact S.ne_bot_of_dvd_card h2H
  exact le_twoLocalPrimeRank_of_normalizer hr hPne hP2 hBelem hBcard' hSnorm

theorem le_twoLocalPrimeRank_of_surjective {G R : Type} [Group G] [Finite G] [Group R]
    {φ : G →* R} (hφ : Function.Surjective φ)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrker : ¬ r ∣ Nat.card φ.ker)
    {X E : Subgroup R} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X) (hE : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) :
    k ≤ CFSG.Open.twoLocalPrimeRank r G := by
  classical
  let e : G ⧸ φ.ker ≃* R := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  refine le_twoLocalPrimeRank_of_quotient (N := φ.ker) hr hr2 hrker
    (X := X.map e.symm.toMonoidHom) (E := E.map e.symm.toMonoidHom) ?_ ?_ ?_ ?_ ?_
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective X (f := e.symm.toMonoidHom)
      e.symm.injective]
    exact hX
  · exact hX2.map e.symm.toMonoidHom
  · exact CFSG.SectionRank.isElemAbelian_map hE e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
  · calc E.map e.symm.toMonoidHom
        ≤ (Subgroup.normalizer (X : Set R)).map e.symm.toMonoidHom := Subgroup.map_mono hXE
      _ = Subgroup.normalizer (X.map e.symm.toMonoidHom) :=
        Subgroup.map_equiv_normalizer_eq X e.symm

theorem le_twoLocalPrimeRank_of_center_quotient {G R : Type} [Group G] [Finite G] [Group R]
    (θ : G ⧸ Subgroup.center G ≃* R) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center G)) {X E : Subgroup R} (hX : X ≠ ⊥)
    (hX2 : IsPGroup 2 X) (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) :
    k ≤ CFSG.Open.twoLocalPrimeRank r G := by
  classical
  let φ : G →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hφ : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hker : φ.ker = Subgroup.center G := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  exact le_twoLocalPrimeRank_of_surjective hφ hr hr2 (by rw [hker]; exact hrZ)
    hX hX2 hE hEcard hXE

theorem twoLocalPrimeRank_le_of_quotient {G : Type} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN2 : Odd (Nat.card N)) {r : ℕ} (hr : r.Prime) (hrN : ¬ r ∣ Nat.card N) :
    CFSG.Open.twoLocalPrimeRank r G ≤ CFSG.Open.twoLocalPrimeRank r (G ⧸ N) := by
  classical
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπker : π.ker = N := QuotientGroup.ker_mk' N
  have hπ2N : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hN2) (even_iff_two_dvd.mpr h)
  apply csSup_le'
  rintro k ⟨M, hM, rfl⟩
  obtain ⟨P, hPne, hP2, rfl⟩ := hM
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained r hr
      (Subgroup.normalizer (P : Set G))
  have hEker : E ⊓ π.ker = ⊥ := by
    rw [hπker]
    refine (Subgroup.eq_bot_iff_card (E ⊓ N)).mpr
      (Nat.eq_one_of_dvd_coprimes (a := Nat.card E) (b := Nat.card N) ?_ ?_ ?_)
    · rw [hEcard]
      exact Nat.Coprime.pow_left _ ((hr.coprime_iff_not_dvd).2 hrN)
    · exact Subgroup.card_dvd_of_le inf_le_left
    · exact Subgroup.card_dvd_of_le inf_le_right
  have hinj : Set.InjOn π E := by
    intro x hx y hy hxy
    have hmem : x * y⁻¹ ∈ E ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨E.mul_mem hx (E.inv_mem hy), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hEker, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hEcard' : Nat.card (E.map π) =
      r ^ CFSG.Open.pRank r (Subgroup.normalizer (P : Set G)) := by
    rw [CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral.card_map_eq_of_injOn
      hinj, hEcard]
  have hPbar : P.map π ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, hπker]
    intro hPN
    have h2dvdP : 2 ∣ Nat.card P := by
      obtain ⟨n, hn⟩ := hP2.exists_card_eq
      have hnpos : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := by omega
        rw [hn0', pow_zero] at hn
        exact hPne ((Subgroup.eq_bot_iff_card P).mpr hn)
      rw [hn]
      exact dvd_pow_self 2 hnpos.ne'
    exact hπ2N (dvd_trans h2dvdP (Subgroup.card_dvd_of_le hPN))
  have hP2bar : IsPGroup 2 (P.map π) := hP2.map π
  have hE' : IsElemAbelian r (E.map π) := CFSG.SectionRank.isElemAbelian_map hE π
  have hnorm : E.map π ≤ Subgroup.normalizer (P.map π : Set (G ⧸ N)) :=
    (Subgroup.map_mono hEM).trans (Subgroup.le_normalizer_map (H := P) π)
  exact le_twoLocalPrimeRank_of_normalizer hr hPbar hP2bar hE' hEcard' hnorm

end CFSG.LocalAnalysis.GLTheoremA
