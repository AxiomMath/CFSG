module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace Transport

section Equivariance

variable {G' G : Type} [Group G'] [Group G]

theorem pPrimeCoreOf_map (p : ℕ) {f : G' →* G} (hf : Function.Injective f) (X : Subgroup G') :
    pPrimeCoreOf p (X.map f) = (pPrimeCoreOf p X).map f := by
  let φ : ↥X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf
  have h1 := pPrimeCore_map_iso p φ
  have hcomp : (X.map f).subtype.comp φ.toMonoidHom = f.comp X.subtype := by
    ext x; rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem pPrimePCore_map_iso (p : ℕ) {Y Y' : Type*} [Group Y] [Group Y'] (φ : Y ≃* Y') :
    (pPrimePCore p Y).map φ.toMonoidHom = pPrimePCore p Y' := by
  have hN : (pPrimeCore p Y).map φ.toMonoidHom = pPrimeCore p Y' := pPrimeCore_map_iso p φ
  let ψ : Y ⧸ pPrimeCore p Y ≃* Y' ⧸ pPrimeCore p Y' := QuotientGroup.congr _ _ φ hN
  have hψ : ∀ y, ψ (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
  have hcore : (pCore p (Y ⧸ pPrimeCore p Y)).map ψ.toMonoidHom =
      pCore p (Y' ⧸ pPrimeCore p Y') := pCore_map_iso p ψ
  ext y'
  rw [Subgroup.mem_map_equiv]
  have h1 : ψ.symm (QuotientGroup.mk y') = QuotientGroup.mk (φ.symm y') := by
    apply ψ.injective
    rw [ψ.apply_symm_apply, hψ, φ.apply_symm_apply]
  have h2 : φ.symm y' ∈ pPrimePCore p Y ↔
      QuotientGroup.mk (φ.symm y') ∈ pCore p (Y ⧸ pPrimeCore p Y) := Iff.rfl
  have h3 : y' ∈ pPrimePCore p Y' ↔
      (QuotientGroup.mk y' : Y' ⧸ pPrimeCore p Y') ∈ pCore p (Y' ⧸ pPrimeCore p Y') := Iff.rfl
  rw [h2, h3, ← hcore, Subgroup.mem_map_equiv, h1]

theorem O22Of_map {f : G' →* G} (hf : Function.Injective f) (X : Subgroup G') :
    O22Of (X.map f) = (O22Of X).map f := by
  let φ : ↥X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf
  have h1 := pPrimePCore_map_iso 2 φ
  have hcomp : (X.map f).subtype.comp φ.toMonoidHom = f.comp X.subtype := by
    ext x; rfl
  unfold O22Of
  rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map]

end Equivariance

section Maps

variable {G' G : Type} [Group G'] [Group G]

theorem centralizer_map_of_le_range {f : G' →* G} (hf : Function.Injective f) {A : Subgroup G'}
    (h : centralizer ((A.map f : Subgroup G) : Set G) ≤ f.range) :
    centralizer ((A.map f : Subgroup G) : Set G) = (centralizer (A : Set G')).map f := by
  apply le_antisymm
  · intro c hc
    obtain ⟨c', rfl⟩ := MonoidHom.mem_range.mp (h hc)
    refine Subgroup.mem_map.mpr ⟨c', ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp hc (f a) (Subgroup.mem_map_of_mem f ha)
    exact hf (by simpa using h1)
  · rintro _ ⟨c', hc', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc' a ha
    simp only [← map_mul, h1]

theorem map_inf_centralizer_map {f : G' →* G} (hf : Function.Injective f) (Q Xg : Subgroup G') :
    Q.map f ⊓ centralizer ((Xg.map f : Subgroup G) : Set G) =
      (Q ⊓ centralizer (Xg : Set G')).map f := by
  ext c
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hc⟩
    have hc' : f q ∈ centralizer ((Xg.map f : Subgroup G) : Set G) := hc
    refine Subgroup.mem_map.mpr ⟨q, Subgroup.mem_inf.mpr ⟨hq, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hc' ⊢
    intro a ha
    exact hf (by simpa using hc' (f a) (Subgroup.mem_map_of_mem f ha))
  · rintro ⟨q, ⟨hq, hqc⟩, rfl⟩
    have hqc' : q ∈ centralizer (Xg : Set G') := hqc
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem f hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hqc' ⊢
    rintro _ ⟨a, ha, rfl⟩
    simp only [← map_mul, hqc' a ha]

theorem mem_normalizer_map (f : G' →* G) {Q : Subgroup G'} {x : G'}
    (hx : x ∈ normalizer (Q : Set G')) : f x ∈ normalizer ((Q.map f : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, (hx q).mp hq, by simp⟩
  · rintro ⟨q, hq, hqy⟩
    refine ⟨x⁻¹ * q * x, ?_, ?_⟩
    · have e : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
      exact (hx (x⁻¹ * q * x)).mpr (by rw [e]; exact hq)
    · simp only [map_mul, map_inv, hqy]
      group

theorem isSylowOf_map_inj [Finite G] {f : G' →* G} (hf : Function.Injective f)
    {P K : Subgroup G'} (h : CFSG.ABGLocalTools.IsSylowOf 2 P K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P.map f) (K.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_injective f hf
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map f, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective P K hf]

theorem isL34Two_map_inj {f : G' →* G} (hf : Function.Injective f) {Q : Subgroup G'}
    (h : IsL34Two ↥Q) : IsL34Two ↥(Q.map f) := by
  obtain ⟨e⟩ := h
  exact ⟨(Subgroup.equivMapOfInjective Q f hf).symm.trans e⟩

theorem quotIso_map {f : G' →* G} (hf : Function.Injective f) {X N : Subgroup G'} {Y : Type}
    [Group Y] (h : QuotIso X N Y) : QuotIso (X.map f) (N.map f) Y := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  let φ : ↥X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf
  have hmap : (N.subgroupOf X).map φ.toMonoidHom = (N.map f).subgroupOf (X.map f) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hy : f ((φ.symm y : ↥X) : G') = (y : G) := by
      have := Subgroup.coe_equivMapOfInjective_apply X f hf (φ.symm y)
      rw [← this]
      simp [φ]
    rw [← hy]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have hnormal : ((N.map f).subgroupOf (X.map f)).Normal := by
    rw [← hmap]
    exact hn.map φ.toMonoidHom φ.surjective
  have := hn
  have := hnormal
  exact ⟨hnormal, ⟨(QuotientGroup.congr (N.subgroupOf X) ((N.map f).subgroupOf (X.map f)) φ
    hmap).symm.trans e⟩⟩

end Maps

section Master

variable {G' G : Type} [Group G'] [Group G] [Finite G]

theorem lemma29b_map {f : G' →* G} (hf : Function.Injective f) {U : Subgroup G'}
    (hc : centralizer ((U.map f : Subgroup G) : Set G) ≤ f.range) (h : Lemma29b U) :
    Lemma29b (U.map f) := by
  obtain ⟨Q, Xg, v, hQsyl, hv, ⟨x, hXg, hXg3, hxN, hx3⟩, hdec, hQXg, hQL34, hQC, hUsyl, hquot⟩ := h
  have hcen : centralizer ((U.map f : Subgroup G) : Set G) = (centralizer (U : Set G')).map f :=
    centralizer_map_of_le_range hf hc
  have hUQ : U ≤ Q := hQC ▸ inf_le_left
  have hcQ : centralizer ((Q.map f : Subgroup G) : Set G) = (centralizer (Q : Set G')).map f :=
    centralizer_map_of_le_range hf
      ((Subgroup.centralizer_le (SetLike.coe_mono (Subgroup.map_mono hUQ))).trans hc)
  refine ⟨Q.map f, Xg.map f, f v, ?_, ?_, ⟨f x, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcen, O22Of_map hf]
    exact isSylowOf_map_inj hf hQsyl
  · rw [← map_mul, hv, map_one]
  · rw [hXg, MonoidHom.map_zpowers]
  · exact hXg3.map f
  · refine Subgroup.mem_inf.mpr ⟨mem_normalizer_map f (Subgroup.mem_inf.mp hxN).1, ?_⟩
    have hxc : x ∈ centralizer (U : Set G') := (Subgroup.mem_inf.mp hxN).2
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    rintro _ ⟨u, hu, rfl⟩
    simp only [← map_mul, hxc u hu]
  · rw [hcen, pPrimeCoreOf_map 2 hf, ← map_pow]
    exact Subgroup.mem_map_of_mem f hx3
  · intro c hc'
    rw [hcen] at hc'
    obtain ⟨c', hc'', rfl⟩ := Subgroup.mem_map.mp hc'
    obtain ⟨o, ho, q, hq, a, ha, b, hb, hcoo⟩ := hdec c' hc''
    refine ⟨f o, ?_, f q, Subgroup.mem_map_of_mem f hq, f a, Subgroup.mem_map_of_mem f ha, f b,
      ?_, ?_⟩
    · rw [hcen, pPrimeCoreOf_map 2 hf]
      exact Subgroup.mem_map_of_mem f ho
    · rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem f hb
    · rw [hcoo]
      simp only [map_mul]
  · rw [← Subgroup.map_commutator, hQXg]
  · exact isL34Two_map_inj hf hQL34
  · rw [map_inf_centralizer_map hf, hQC]
  · rw [hcQ]
    exact isSylowOf_map_inj hf hUsyl
  · rw [hcen, O22Of_map hf]
    exact hquot.imp (quotIso_map hf) (quotIso_map hf)

end Master

end Transport

section Transport

variable {G : Type} [Group G] [Finite G]

theorem lemma29b_of_subgroupOf (C U : Subgroup G) (hUC : U ≤ C)
    (hcent : centralizer (U : Set G) ≤ C) (h : Lemma29b (U.subgroupOf C)) : Lemma29b U := by
  have h1 := Transport.lemma29b_map (f := C.subtype) C.subtype_injective (U := U.subgroupOf C)
    (by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUC, Subgroup.range_subtype]
      exact hcent) h
  rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUC] at h1

theorem lemma29b_conj (U : Subgroup G) (g : G) (h : Lemma29b U) :
    Lemma29b (U.map (MulAut.conj g).toMonoidHom) :=
  Transport.lemma29b_map (MulAut.conj g).injective (by
    intro c _
    exact ⟨g⁻¹ * c * g, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩) h

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
