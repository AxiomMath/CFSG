module

public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


namespace E8Lift

theorem units_map_entrywiseHom_weylElt_one {τ : Tag} {L : Type} [Field L] (σ : L →+* L)
    (i : Fin τ.rank) :
    Units.map (entrywiseHom σ) (weylElt τ L i 1) = weylElt τ L i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul,
    units_map_entrywiseHom_xUnit, units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [map_one, map_neg]

theorem units_map_entrywiseHom_canonicalRep {τ : Tag} {L : Type} [Field L] (σ : L →+* L)
    (w : WeylGroup τ) :
    Units.map (entrywiseHom σ) (canonicalRep (coxeterSystem τ) L w) =
      canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun i _ => units_map_entrywiseHom_weylElt_one σ i)

theorem torusGroup_mul_comm {τ : Tag} {L : Type} [Field L] {x y : ModGL τ L}
    (hx : x ∈ torusGroup τ L) (hy : y ∈ torusGroup τ L) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hy

theorem mapsRootLines_pow {τ : Tag} {L : Type} [Field L] {g : ModGL τ L} {w : WeylGroup τ}
    (h : MapsRootLines g w) (n : ℕ) : MapsRootLines (g ^ n) (w ^ n) := by
  induction n with
  | zero => simpa using mapsRootLines_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem mem_torusGroup_of_mapsRootLines_one {τ : Tag} {L : Type} [Field L] {g : ModGL τ L}
    (hg : g ∈ monomialSubgroup τ L) (h1 : MapsRootLines g 1) : g ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines g w := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw : w = 1 := hmaps.unique h1
  rw [hgk, hw, canonicalRep_one, mul_one]
  exact hk

theorem torusGroup_le_supportedTorus_univ {τ : Tag} {L : Type} [Field L] :
    torusGroup τ L ≤ supportedTorus τ L Set.univ := by
  rw [supportedTorus_eq_subsystemTorus]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact Subgroup.subset_closure ⟨i, Set.mem_univ _, t, rfl⟩

end E8Lift

theorem exists_fixed_lift {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (w z : WeylGroup Tag.E8) (hwz : w * z = z * w) :
    ∃ v : ModGL Tag.E8 L, v ∈ adjointGroup Tag.E8 L ∧
      canonicalRep (coxeterSystem Tag.E8) L w * Units.map (entrywiseHom Fr) v *
        (canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ = v ∧
      (∀ x ∈ torusGroup Tag.E8 L, v * x * v⁻¹ ∈ torusGroup Tag.E8 L) ∧
      (z ^ 5 = 1 → v ^ 5 ∈ torusGroup Tag.E8 L) ∧
      (z ≠ 1 → v ∉ torusGroup Tag.E8 L) ∧
      ∀ a : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit Tag.E8 a * v = v * rootDiagUnit Tag.E8 a ↔ z ∈ rootCharStabilizer a := by
  classical
  set nw := canonicalRep (coxeterSystem Tag.E8) L w with hnw
  set nz := canonicalRep (coxeterSystem Tag.E8) L z with hnz
  set H := torusGroup Tag.E8 L with hH
  have hΦz : Units.map (entrywiseHom Fr) nz = nz := E8Lift.units_map_entrywiseHom_canonicalRep Fr z
  obtain ⟨κ, hκH, hκ⟩ : ∃ κ ∈ H, nw * nz * nw⁻¹ = κ * nz := by
    obtain ⟨κ₁, hκ₁, h₁⟩ := canonicalRep_mul_mem (R := L) (τ := Tag.E8) w z
    obtain ⟨κ₂, hκ₂, h₂⟩ := canonicalRep_mul_mem (R := L) (τ := Tag.E8) z w
    rw [hwz] at h₁
    refine ⟨κ₁ * κ₂⁻¹, mul_mem hκ₁ (inv_mem hκ₂), ?_⟩
    have h3 : nw * nz = (κ₁ * κ₂⁻¹) * (nz * nw) := by
      rw [h₁, h₂]
      group
    rw [h3]
    group
  have hnzN : nz ∈ Subgroup.normalizer (H : Set (ModGL Tag.E8 L)) := canonicalRep_mem_normalizer z
  have hnzN' : nz⁻¹ ∈ Subgroup.normalizer (H : Set (ModGL Tag.E8 L)) := inv_mem hnzN
  have hs : nz⁻¹ * κ⁻¹ * nz ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 hnzN' κ⁻¹).1 (inv_mem hκH)
    simpa using this
  obtain ⟨t, ht, htL⟩ := CFSG.HardMathSupport.Foote.Coordinator.exists_lang_supportedTorus_of_monomial
    (τ := Tag.E8) (Ω := L) hq hFr nw (canonicalRep_mem_monomialSubgroup L w) (J := Set.univ)
    (fun β hβ => ⟨IsRoot.smul hβ.1 _, fun i hi => absurd (Set.mem_univ i) hi⟩)
    (nz⁻¹ * κ⁻¹ * nz) (E8Lift.torusGroup_le_supportedTorus_univ hs)
  have htH : t ∈ H := supportedTorus_le_torusGroup _ ht
  have hfix : nw * Units.map (entrywiseHom Fr) (nz * t) * nw⁻¹ = nz * t := by
    have hXe : nw * Units.map (entrywiseHom Fr) t * nw⁻¹ = t * (nz⁻¹ * κ⁻¹ * nz) := by
      rw [← htL]
      group
    have hu : nz * t * nz⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hnzN t).1 htH
    have hcomm : κ * (nz * t * nz⁻¹) = (nz * t * nz⁻¹) * κ := E8Lift.torusGroup_mul_comm hκH hu
    calc nw * Units.map (entrywiseHom Fr) (nz * t) * nw⁻¹
        = (nw * nz * nw⁻¹) * (nw * Units.map (entrywiseHom Fr) t * nw⁻¹) := by
          rw [map_mul, hΦz]
          group
      _ = (κ * nz) * (t * (nz⁻¹ * κ⁻¹ * nz)) := by rw [hκ, hXe]
      _ = (κ * (nz * t * nz⁻¹)) * κ⁻¹ * nz := by group
      _ = (nz * t * nz⁻¹) * κ * κ⁻¹ * nz := by rw [hcomm]
      _ = nz * t := by group
  have hvN : nz * t ∈ Subgroup.normalizer (H : Set (ModGL Tag.E8 L)) :=
    mul_mem hnzN (Subgroup.le_normalizer htH)
  have hmon : nz * t ∈ monomialSubgroup Tag.E8 L :=
    mul_mem (canonicalRep_mem_monomialSubgroup L z) (torusGroup_le_monomialSubgroup htH)
  have hmaps : MapsRootLines (nz * t) z := by
    simpa using (mapsRootLines_canonicalRep z).mul (mapsRootLines_of_mem_torusGroup htH)
  refine ⟨nz * t, ?_, hfix, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (canonicalRep_mem_adjointGroup _ L z)
      (monomialSubgroup_le_adjointGroup' (torusGroup_le_monomialSubgroup htH))
  · intro x hx
    exact (Subgroup.mem_normalizer_iff.1 hvN x).1 hx
  · intro hz5
    have h5 : MapsRootLines ((nz * t) ^ 5) 1 := by
      have := E8Lift.mapsRootLines_pow hmaps 5
      rwa [hz5] at this
    exact E8Lift.mem_torusGroup_of_mapsRootLines_one (pow_mem hmon 5) h5
  · intro hz1 hvH
    have hnzH : nz ∈ H := by
      simpa using mul_mem hvH (inv_mem htH)
    exact hz1 ((mapsRootLines_canonicalRep z).unique (mapsRootLines_of_mem_torusGroup hnzH))
  · intro a
    have hc := rootDiagUnit_mul_comm_of_mem_torusGroup a htH
    rw [← conj_canonicalRep_eq_iff (K := L) a z, mul_inv_eq_iff_eq_mul]
    constructor
    · intro h
      refine mul_right_cancel (b := t) ?_
      calc rootDiagUnit Tag.E8 a * nz * t = rootDiagUnit Tag.E8 a * (nz * t) := by group
        _ = nz * t * rootDiagUnit Tag.E8 a := h
        _ = nz * (t * rootDiagUnit Tag.E8 a) := by group
        _ = nz * (rootDiagUnit Tag.E8 a * t) := by rw [hc]
        _ = nz * rootDiagUnit Tag.E8 a * t := by group
    · intro h
      calc rootDiagUnit Tag.E8 a * (nz * t) = (rootDiagUnit Tag.E8 a * nz) * t := by group
        _ = (nz * rootDiagUnit Tag.E8 a) * t := by rw [h]
        _ = nz * (rootDiagUnit Tag.E8 a * t) := by group
        _ = nz * (t * rootDiagUnit Tag.E8 a) := by rw [hc]
        _ = nz * t * rootDiagUnit Tag.E8 a := by group

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
