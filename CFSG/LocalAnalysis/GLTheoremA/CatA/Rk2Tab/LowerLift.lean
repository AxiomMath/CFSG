module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Lift
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment
public import CFSG.ClassicalInvolution.Sp62Rec.FourLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem le_evenRank_of_normalizer {G : Type} [Group G] [Finite G] {r k : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {X E : Subgroup G} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set G)) : k ≤ evenRank G :=
  (CFSG.SectionRank.le_pRank hr.one_lt hXE hE hEcard).trans
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 _
      ⟨X, hX, hX2, rfl⟩)

private theorem exists_isElemAbelian_le_comap {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {r : ℕ} (hr : r.Prime) (hrN : ¬ r ∣ Nat.card N)
    {E : Subgroup (G ⧸ N)} (hE : IsElemAbelian r E) :
    ∃ B : Subgroup G, B ≤ E.comap (QuotientGroup.mk' N) ∧ IsElemAbelian r B ∧
      Nat.card B = Nat.card E := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  let ψ : ↥(E.comap π) →* G ⧸ N := π.comp (E.comap π).subtype
  have hψ : ∀ x : ↥(E.comap π), ψ x ∈ E := fun x => x.2
  let α : ↥(E.comap π) →* ↥E := ψ.codRestrict E hψ
  have hα : Function.Surjective α := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : G ⧸ N)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [Subgroup.mem_comap]
    rw [show π g = (e : G ⧸ N) from hg]
    exact e.2
  have hcardker : Nat.card α.ker = Nat.card N := by
    have h1 : Nat.card α.ker * Nat.card E = Nat.card ↥(E.comap π) := by
      have h := Subgroup.card_ker_mul_card_range α
      rw [MonoidHom.range_eq_top.2 hα, Subgroup.card_top] at h
      exact h
    have h2 : Nat.card ↥(E.comap π) = Nat.card E * Nat.card N :=
      CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk N E
    have hEpos : 0 < Nat.card E :=
      Nat.card_pos_iff.2 ⟨⟨1, E.one_mem⟩, inferInstance⟩
    rw [h2, mul_comm (Nat.card α.ker) (Nat.card E)] at h1
    exact Nat.eq_of_mul_eq_mul_left hEpos h1
  have hker : ¬ r ∣ Nat.card α.ker := by
    rw [hcardker]
    exact hrN
  have htop : IsElemAbelian r (⊤ : Subgroup ↥E) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact isElemAbelian_commute hE (a : ↥E).2 (b : ↥E).2
    · apply Subtype.ext
      simpa using hE.2 (x : ↥E).1 (x : ↥E).2
  obtain ⟨B, hBelem, hBcard⟩ := rk2_lift_elemAbelian hr α hα hker htop
  refine ⟨B.map (E.comap π).subtype, Subgroup.map_subtype_le B,
    CFSG.SectionRank.isElemAbelian_map hBelem (E.comap π).subtype, ?_⟩
  rw [Subgroup.card_map_of_injective (E.comap π).subtype_injective, hBcard,
    Subgroup.card_top]

theorem le_evenRank_of_quotient {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : ¬ r ∣ Nat.card N) {X E : Subgroup (G ⧸ N)} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set (G ⧸ N))) : k ≤ evenRank G := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  set H : Subgroup G := X.comap π with hH
  have hcardH : Nat.card H = Nat.card X * Nat.card N := by
    rw [hH]
    exact CFSG.ClassicalInvolution.Sp62Rec.natCard_comap_mk N X
  obtain ⟨B, hBle, hBelem, hBcard⟩ := exists_isElemAbelian_le_comap hr hrN hE
  have hBcard' : Nat.card B = r ^ k := by
    rw [hBcard, hEcard]
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
  exact le_evenRank_of_normalizer hr hr2 hPne hP2 hBelem hBcard' hSnorm

theorem le_evenRank_of_surjective {G R : Type} [Group G] [Finite G] [Group R]
    {φ : G →* R} (hφ : Function.Surjective φ)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrker : ¬ r ∣ Nat.card φ.ker)
    {X E : Subgroup R} (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X) (hE : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) : k ≤ evenRank G := by
  classical
  let e : G ⧸ φ.ker ≃* R := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  refine le_evenRank_of_quotient (N := φ.ker) hr hr2 hrker
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

theorem le_evenRank_of_center_quotient {G R : Type} [Group G] [Finite G] [Group R]
    (θ : G ⧸ Subgroup.center G ≃* R) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center G)) {X E : Subgroup R} (hX : X ≠ ⊥)
    (hX2 : IsPGroup 2 X) (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) : k ≤ evenRank G := by
  classical
  let φ : G →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hφ : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hker : φ.ker = Subgroup.center G := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  exact le_evenRank_of_surjective hφ hr hr2 (by rw [hker]; exact hrZ)
    hX hX2 hE hEcard hXE

end CFSG.LocalAnalysis.GLTheoremA
