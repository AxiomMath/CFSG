module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Order

theorem bgll_three_dvd_card_psl (K : Type) [Field K] [Finite K] :
    3 ∣ Nat.card (projectiveSL 3 K) := by
  have h : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) *
      Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
  have hc : Nat.card (projectiveSL 3 K) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :=
    (Nat.card_congr (psiO K).toEquiv).symm
  rw [← hc] at h
  generalize Nat.card (projectiveSL 3 K) = N at h ⊢
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  generalize Nat.card K = q at h hq
  obtain ⟨s, hs⟩ : ∃ s, q = s + 2 := ⟨q - 2, by omega⟩
  subst hs
  have h2 : (s + 2) ^ 2 - 1 = (s + 1) * (s + 3) := by
    have : 1 ≤ (s + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this]; ring
  have h3 : (s + 2) ^ 3 - 1 = (s + 1) * ((s + 2) ^ 2 + (s + 2) + 1) := by
    have : 1 ≤ (s + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [this]; ring
  rw [h2, h3] at h
  have hmod : (s + 2) % 3 = 0 ∨ (s + 2) % 3 = 1 ∨ (s + 2) % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2'
  · have hg : Nat.gcd 3 (s + 2 - 1) = 1 := by
      have : ¬ 3 ∣ s + 2 - 1 := by omega
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 this)) |>.symm
    rw [hg, mul_one] at h
    have : 3 ∣ (s + 2) ^ 3 := dvd_pow (Nat.dvd_of_mod_eq_zero h0) (by norm_num)
    rw [h]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
  · have hg : Nat.gcd 3 (s + 2 - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg] at h
    have h9 : 3 ∣ (s + 1) := by omega
    obtain ⟨m, hm⟩ := h9
    have h4 : 3 ∣ ((s + 2) ^ 2 + (s + 2) + 1) := by
      have : (s + 2) % 3 = 1 := h1
      have h5 : (s + 2) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, this]
      omega
    obtain ⟨m', hm'⟩ := h4
    rw [hm, hm'] at h
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = (s + 2) ^ 3 * (m * (s + 3)) * (m * m') := ⟨_, rfl⟩
    have h' : N * 3 = 27 * Z := by rw [h, hZ]; ring
    exact ⟨3 * Z, by omega⟩
  · have hg : Nat.gcd 3 (s + 2 - 1) = 1 := by
      have : ¬ 3 ∣ s + 2 - 1 := by omega
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 this)) |>.symm
    rw [hg, mul_one] at h
    have h9 : 3 ∣ (s + 3) := by omega
    rw [h]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.dvd.mul_left h9 (s + 1)) _) _

end Order

section Normal

variable {F : Type} [Field F] [Finite F]

theorem bgll_range_normal {k : Subfield F} {σ : F ≃+* F} (hk : ∀ x, x ∈ k ↔ σ x = x) :
    ((linearSubfieldInclusion 3 k).range.subgroupOf (fixSubgroup (fieldAut 3 F σ))).Normal := by
  refine ⟨fun a ha y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨S, hS, hSa⟩ := mem_range_linearSubfieldInclusion.1 ha
  obtain ⟨G, hG⟩ := proj_surjective 3 F (y : projectiveSL 3 F)
  have hy : fieldAut 3 F σ (y : projectiveSL 3 F) = y := y.2
  rw [← hG, fieldAut_proj] at hy
  have hw : G⁻¹ * SpecialLinearGroup.map σ.toRingHom G ∈ scalars 3 F :=
    proj_eq_proj_iff.1 hy.symm
  have hwc := scalars_le_center 3 F hw
  set w := G⁻¹ * SpecialLinearGroup.map σ.toRingHom G with hwdef
  have hmapG : SpecialLinearGroup.map σ.toRingHom G = G * w := by rw [hwdef]; group
  have hmapS : SpecialLinearGroup.map σ.toRingHom S = S := by
    apply Subtype.ext
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (hk _).1 (hS i j)
  have hSw : S * w = w * S := Subgroup.mem_center_iff.1 hwc S
  obtain ⟨T, hTdef⟩ : ∃ T, T = G * S * G⁻¹ := ⟨_, rfl⟩
  have hT : SpecialLinearGroup.map σ.toRingHom T = T := by
    rw [hTdef, map_mul, map_mul, map_inv, hmapG, hmapS]
    calc G * w * S * (G * w)⁻¹ = G * (w * S * w⁻¹) * G⁻¹ := by group
      _ = G * S * G⁻¹ := by rw [← hSw]; group
  refine mem_range_linearSubfieldInclusion.2 ⟨T, fun i j => ?_, ?_⟩
  · rw [hk]
    have := congrArg (fun X : SpecialLinearGroup (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F) i j) hT
    simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using
      (show σ ((T : Matrix (Fin 3) (Fin 3) F) i j) = (T : Matrix (Fin 3) (Fin 3) F) i j from this)
  · change proj 3 F T = (y : projectiveSL 3 F) * (a : projectiveSL 3 F) *
      (y : projectiveSL 3 F)⁻¹
    rw [hTdef, map_mul, map_mul, map_inv, hG, hSa]

end Normal

section Join

variable {F : Type} [Field F] [Finite F]

theorem bgll_model_join (hcore : BGL.SL3SubfieldJoin) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {k : Subfield F} (hk : ∀ x, x ∈ k ↔ σ x = x) (h : GL (Fin 3) F)
    (hh : ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
      c * (h : Matrix (Fin 3) (Fin 3) F) i j) :
    (linearSubfieldInclusion 3 k).range ⊔
      (linearSubfieldInclusion 3 k).range.map (conjAut 3 F h).toMonoidHom = ⊤ := by
  have h1 : (BGL.fixSL3 σ).map (proj 3 F) = (linearSubfieldInclusion 3 k).range := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact mem_range_linearSubfieldInclusion.2 ⟨g, fun i j => (hk _).2 (hg i j), rfl⟩
    · intro hx
      obtain ⟨g, hg, rfl⟩ := mem_range_linearSubfieldInclusion.1 hx
      exact ⟨g, fun i j => (hk _).1 (hg i j), rfl⟩
  have hcomp : (proj 3 F).comp (BGL.conjGL3 h) = (conjAut 3 F h).toMonoidHom.comp (proj 3 F) := by
    ext g
    change proj 3 F (BGL.conjGL3 h g) = conjAut 3 F h (proj 3 F g)
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation]
    rfl
  have h2 : ((BGL.fixSL3 σ).map (BGL.conjGL3 h)).map (proj 3 F) =
      ((BGL.fixSL3 σ).map (proj 3 F)).map (conjAut 3 F h).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hc := hcore F σ hσ h hh
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  have hg : g ∈ BGL.fixSL3 σ ⊔ (BGL.fixSL3 σ).map (BGL.conjGL3 h) := hc trivial
  have : proj 3 F g ∈ ((BGL.fixSL3 σ ⊔ (BGL.fixSL3 σ).map (BGL.conjGL3 h)).map (proj 3 F)) :=
    ⟨g, hg, rfl⟩
  rw [Subgroup.map_sup, h2, h1] at this
  exact this

end Join

section NSP

@[expose] def BglNSP {M : Type} [Group M] (β : MulAut M) (A : Subgroup M) : Prop :=
  A ≤ fixSubgroup β ∧ (A.subgroupOf (fixSubgroup β)).Normal ∧ IsSimpleGroup A ∧
    (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A

theorem bglNSP_le_layer {M : Type} [Group M] [Finite M] {β : MulAut M} {A : Subgroup M} (h : BglNSP β A) :
    A ≤ GLAPLayer 3 (fixSubgroup β) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact le_glaPLayer_of_normal_simple Nat.prime_three h1 h2 h4 h5

theorem bglNSP_map {Q M : Type} [Group Q] [Group M] (e : Q ≃* M) {β : MulAut Q} {β' : MulAut M}
    (hβ : MulAut.congr e β = β') {A : Subgroup M} (h : BglNSP β' A) :
    BglNSP β (A.map e.symm.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hmem : ∀ x : Q, x ∈ A.map e.symm.toMonoidHom ↔ e x ∈ A := fun x => by
    rw [Subgroup.mem_map_equiv]; rfl
  have hfix : ∀ q : Q, q ∈ fixSubgroup β ↔ e q ∈ fixSubgroup β' := by
    intro q
    have h' : β' (e q) = e (β q) := by
      rw [← hβ]
      simp [MulAut.congr_apply]
    rw [mem_fixSubgroup, mem_fixSubgroup, h']
    exact (e.injective.eq_iff).symm
  let e' : ↥A ≃* ↥(A.map e.symm.toMonoidHom) :=
    Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
  refine ⟨fun x hx => (hfix x).2 (h1 ((hmem x).1 hx)), ⟨fun a ha y => ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at ha ⊢
    have ha' : (⟨e a, (hfix a).1 a.2⟩ : ↥(fixSubgroup β')) ∈ A.subgroupOf (fixSubgroup β') :=
      Subgroup.mem_subgroupOf.2 ((hmem a).1 ha)
    have := h2.conj_mem _ ha' ⟨e y, (hfix y).1 y.2⟩
    rw [Subgroup.mem_subgroupOf] at this
    rw [hmem]
    simpa using this
  · exact e'.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := h4
    exact ⟨e' a, e' b, fun hc => hab (e'.injective (by rw [map_mul, map_mul, hc]))⟩
  · rw [← Nat.card_congr e'.toEquiv]
    exact h5

theorem bgll_range_nsp {F : Type} [Field F] [Finite F] {k : Subfield F} {σ : F ≃+* F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) :
    BglNSP (fieldAut 3 F σ) (linearSubfieldInclusion 3 k).range := by
  have hsn := simple_nonabelian_range_linearSubfieldInclusion (n := 3) (K := F) le_rfl k
  refine ⟨?_, bgll_range_normal hk, hsn.1, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) x
  · by_contra hcon
    apply hsn.2
    intro x y
    by_contra hxy
    exact hcon ⟨x, y, hxy⟩
  · have hinj := linearSubfieldInclusion_injective (by norm_num : 0 < 3) k
    have e : (linearSubfieldInclusion 3 k).range ≃* projectiveSL 3 k :=
      (MonoidHom.ofInjective hinj).symm
    rw [Nat.card_congr e.toEquiv]
    exact bgll_three_dvd_card_psl k

end NSP

end CFSG.HardMathSupport.Solomon.Coordinator
