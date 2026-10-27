module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4Grp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PDescent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Universal.Spin (quadOdd)
open CFSG.RankThree.PartOne.KCOrthogonalDescent (inr_mem_similarityPairs coordinateQuadOdd_field)
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)

section Transfer

variable {A A' : Type*} [Group A] [Group A']

theorem isSylowIn_map {Φ : A →* A'} (hΦ : Function.Injective Φ) {P C : Subgroup A}
    (hP : IsSylowIn 2 P C) : IsSylowIn 2 (P.map Φ) (C.map Φ) := by
  obtain ⟨hPC, hP2, hidx⟩ := hP
  refine ⟨map_mono hPC, hP2.map Φ, ?_⟩
  rwa [relIndex_map_map_of_injective P C hΦ]

theorem isU4Complement_comap {Φ : A →* A'} (hΦ : Function.Injective Φ) {I : Subgroup A}
    {I' : Subgroup A'} (hI : I'.comap Φ = I) {P : Subgroup A} {V' : Subgroup A'}
    (h : IsU4Complement I' (P.map Φ) V') : IsU4Complement I P (V'.comap Φ) := by
  obtain ⟨hVP, hPV, hn, htwo, ⟨b', hb'P, hb'⟩, hinv, hlast⟩ := h
  have hmemI : ∀ a : A, a ∈ I ↔ Φ a ∈ I' := fun a => by rw [← hI, mem_comap]
  have hVP' : V'.comap Φ ≤ P := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ := mem_map.mp (hVP hv)
    rwa [← hΦ hpv]
  refine ⟨hVP', fun v hv => ?_, fun s hs v hv => ?_, fun v hv w hw hvI hwI => ?_, ?_,
    fun v hv hvv => ?_, fun ⟨s, hs, hsV⟩ => ?_⟩
  · exact hPV ⟨mem_map_of_mem Φ hv.1, (hmemI v).mp hv.2⟩
  · rw [mem_comap, map_mul, map_mul, map_inv]
    exact hn _ (mem_map_of_mem Φ hs) _ hv
  · rw [hmemI, map_mul, map_inv]
    exact htwo _ hv _ hw (fun h' => hvI ((hmemI v).mpr h')) fun h' => hwI ((hmemI w).mpr h')
  · obtain ⟨b, hbP, rfl⟩ := mem_map.mp hb'P
    refine ⟨b, hbP, fun s hs => ?_⟩
    obtain ⟨k, hk⟩ := hb' (Φ s) (mem_map_of_mem Φ hs)
    exact ⟨k, by rw [mem_comap, map_mul, map_inv, map_zpow]; exact hk⟩
  · exact (hmemI v).mpr (hinv _ hv (by rw [← map_mul, hvv, map_one]))
  · obtain ⟨x', hx'P, hx'I, hx'x'⟩ := hlast ⟨Φ s, mem_map_of_mem Φ hs, hsV⟩
    obtain ⟨x, hxP, rfl⟩ := mem_map.mp hx'P
    exact ⟨x, hxP, fun h' => hx'I ((hmemI x).mp h'), hΦ (by rw [map_mul, hx'x', map_one])⟩

end Transfer

section Model

variable (K : Type) [Field K] (n : ℕ)

theorem two_cosets_linear (h2 : ringChar K ≠ 2) (hn : 3 ≤ n) [Finite K]
    {a b : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))}
    (ha : a ∈ (linearConjugationHom (coordinateQuadOdd n K)).range)
    (hb : b ∈ (linearConjugationHom (coordinateQuadOdd n K)).range)
    (haI : a ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K)))
    (hbI : b ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    a⁻¹ * b ∈ inner (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  obtain ⟨A, hA⟩ := exists_isometry_of_linear K n h2 hn g
  obtain ⟨B, hB⟩ := exists_isometry_of_linear K n h2 hn h
  change _ = linearConjugationHom _ g at hA
  change _ = linearConjugationHom _ h at hB
  rw [← hA] at haI ⊢
  rw [← hB] at hbI ⊢
  have hAH : A ∉ innerOdd K n := fun hmem =>
    haI (isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem)
  have hBH : B ∉ innerOdd K n := fun hmem =>
    hbI (isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem)
  have hmem : A⁻¹ * B ∈ innerOdd K n := by
    have hi := index_innerOdd_le_two K n h2
    have hi0 : (innerOdd K n).index ≠ 0 := index_ne_zero_of_finite
    rcases (show (innerOdd K n).index = 1 ∨ (innerOdd K n).index = 2 by omega) with h1 | h1
    · exact absurd ((index_eq_one.mp h1) ▸ mem_top A) hAH
    · exact (mul_mem_iff_of_index_two h1).mpr
        (iff_of_false (fun hinv => hAH (by simpa using inv_mem hinv)) hBH)
  rw [← map_inv, ← map_mul]
  exact isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem

theorem exists_involution_coset_linear (h2 : ringChar K ≠ 2) (hn : 3 ≤ n) [Finite K]
    {d : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))}
    (hd : d ∈ (linearConjugationHom (coordinateQuadOdd n K)).range)
    (hdI : d ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    ∃ x : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)), x * x = 1 ∧
      d⁻¹ * x ∈ inner (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  classical
  have : NeZero (2 : K) := ⟨Ring.two_ne_zero h2⟩
  obtain ⟨g, rfl⟩ := hd
  obtain ⟨A, hA⟩ := exists_isometry_of_linear K n h2 hn g
  change _ = linearConjugationHom _ g at hA
  rw [← hA] at hdI ⊢
  have hAH : A ∉ innerOdd K n := fun hmem =>
    hdI (isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem)
  let ι : matrixIsometries (coordinateQuadOdd n K) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K) :=
    matrixIsometriesReindexEquiv (oddIndexEquiv n) (quadOdd n K)
  let H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)) :=
    (innerOdd K n).map ι.toMonoidHom
  by_cases hall : ∀ (v : Fin n ⊕ Fin n ⊕ Unit → K) [Invertible (quadOdd n K v)],
      TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd n K) v ∈ H
  · exfalso
    have htop := TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem (quadOdd n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_quadOdd n K) H hall
    apply hAH
    have hιA : ι A ∈ H := by rw [htop]; exact mem_top _
    obtain ⟨A', hA', hA'A⟩ := mem_map.mp hιA
    rwa [← ι.injective hA'A]
  · push Not at hall
    obtain ⟨v, hv, hrv⟩ := hall
    set R := ι.symm (TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd n K) v) with hR
    have hRH : R ∉ innerOdd K n := fun hmem => hrv (by
      have h1 : ι.toMonoidHom R ∈ H := mem_map_of_mem ι.toMonoidHom hmem
      rwa [hR, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1)
    have hRR : R * R = 1 := by
      rw [hR, ← map_mul, TauCeti.QuadraticMap.reflectionOrthogonal_mul_self, map_one]
    refine ⟨isometryConjugationHom (coordinateQuadOdd n K) R, by rw [← map_mul, hRR, map_one],
      ?_⟩
    have hmem : A⁻¹ * R ∈ innerOdd K n := by
      have hi := index_innerOdd_le_two K n h2
      have hi0 : (innerOdd K n).index ≠ 0 := index_ne_zero_of_finite
      rcases (show (innerOdd K n).index = 1 ∨ (innerOdd K n).index = 2 by omega) with h1 | h1
      · exact absurd ((index_eq_one.mp h1) ▸ mem_top A) hAH
      · exact (mul_mem_iff_of_index_two h1).mpr
          (iff_of_false (fun hinv => hAH (by simpa using inv_mem hinv)) hRH)
    rw [← map_inv, ← map_mul]
    exact isometryConjugationHom_mem_inner_of_mem_innerOdd K n hmem

theorem outData_coordinateQuadOdd [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h2 : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hgates : OrthogonalGates (coordinateQuadOdd n K) f) :
    ∃ φ : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)),
      OutData (inner (matrixProjectiveDerived (coordinateQuadOdd n K)))
        (linearConjugationHom (coordinateQuadOdd n K)).range φ := by
  classical
  set Q := coordinateQuadOdd n K with hQ
  set κ := matrixProjectiveConjugationHom Q with hκ
  obtain ⟨hker, ⟨ψ, hψg, hψker, hψcyc⟩, ⟨hID, -⟩, -⟩ := hgates
  have htop : matrixProjectiveImage Q = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn h2
  have hsurj : Function.Surjective κ := MonoidHom.range_eq_top.mp htop
  let ι' : MulAut (matrixProjectiveDerived Q) →* matrixProjectiveImage Q :=
    (MonoidHom.id _).codRestrict _ fun a => by rw [htop]; exact mem_top a
  let π : MulAut (matrixProjectiveDerived Q) →* (K ≃+* K) := ψ.comp ι'
  have hπκ : ∀ g : similarityPairs Q, π (κ g) = g.val.right := fun g => hψg g
  have hπker : ∀ a, π a = 1 ↔ a ∈ (linearConjugationHom Q).range := by
    intro a
    have h1 : ι' a ∈ ψ.ker ↔ ((ι' a : matrixProjectiveImage Q) : MulAut _) ∈
        (linearConjugationHom Q).range := by
      rw [hψker, mem_subgroupOf]
    exact MonoidHom.mem_ker.symm.trans h1
  obtain ⟨⟨γ, hγ⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥ψ.range)
  let gγ : similarityPairs Q := ⟨SemidirectProduct.inr γ,
    inr_mem_similarityPairs Q γ (coordinateQuadOdd_field n γ)⟩
  have hgγ : ∀ k : ℤ, (gγ ^ k).val = SemidirectProduct.inr (γ ^ k) := fun k => by
    rw [SubgroupClass.coe_zpow]
    exact (map_zpow SemidirectProduct.inr γ k).symm
  have hπφ : ∀ k : ℤ, π (κ gγ ^ k) = γ ^ k := fun k => by
    rw [← map_zpow, hπκ, hgγ, SemidirectProduct.right_inr]
  have hrange : ∀ a, ∃ k : ℤ, π a = γ ^ k := fun a => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hgen ⟨π a, ⟨ι' a, rfl⟩⟩)
    exact ⟨k, (congrArg Subtype.val hk).symm.trans (by simp)⟩
  refine ⟨κ gγ, ⟨fun a b => commutator_mem_inner_coordinateQuadOdd K n h2 hn a b, hID,
    fun d hd e he hdI heI => two_cosets_linear K n h2 hn hd he hdI heI, fun a => ?_,
    fun k hk => ?_, fun d hd hdI => exists_involution_coset_linear K n h2 hn hd hdI,
    fun x hx hxD => ?_⟩⟩
  ·
    obtain ⟨k, hk⟩ := hrange a
    refine ⟨k, (hπker _).mp ?_⟩
    rw [map_mul, map_inv, hπφ, hk, inv_mul_cancel]
  ·
    have h1 : γ ^ k = 1 := by rw [← hπφ]; exact (hπker _).mpr hk
    rw [← map_zpow]
    have h3 : gγ ^ k = 1 := Subtype.ext (by rw [hgγ, h1, map_one, OneMemClass.coe_one])
    rw [h3, map_one]
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, rfl⟩ := hsurj x
    have hσ1 : g.val.right ≠ 1 := fun h' => hxD ((hπker _).mp (by rw [hπκ, h']))
    have hσ2 : g.val.right ^ 2 = 1 := by
      rw [← hπκ, ← map_pow, pow_two, hx, map_one]
    have hσ : orderOf g.val.right = 2 := orderOf_eq_prime hσ2 hσ1
    obtain ⟨Θ, hΘ⟩ := exists_conj_eq_inr_of_orderOf_eq_two hℓ hf hK h2 hn hker g hσ hx
    obtain ⟨k, hk⟩ := hrange (κ g)
    rw [hπκ] at hk
    have hφk : κ gγ ^ k = Θ * κ g * Θ⁻¹ := by
      rw [hΘ, ← map_zpow]
      congr 1
      exact Subtype.ext (by rw [hgγ, ← hk])
    refine ⟨k, ?_, ?_⟩
    · rw [hφk]
      calc Θ * κ g * Θ⁻¹ * (Θ * κ g * Θ⁻¹) = Θ * (κ g * κ g) * Θ⁻¹ := by group
        _ = 1 := by rw [hx, mul_one, mul_inv_cancel]
    · rw [hφk]
      have h1 := commutator_mem_inner_coordinateQuadOdd K n h2 hn Θ (κ g)⁻¹
      have h2' : (Θ * κ g * Θ⁻¹)⁻¹ * κ g = Θ * (κ g)⁻¹ * Θ⁻¹ * (κ g)⁻¹⁻¹ := by group
      rw [h2']
      exact h1

end Model

theorem harris82Lemma411U4_holds : Harris82Lemma411U4 := by
  intro X _ _ p f hp hp2 h5 hX C P hIC hP
  obtain ⟨hq, -, hL⟩ := hX
  have : Group.IsPerfect X := hq.1
  rcases hL with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hcm' := hcm
    obtain ⟨⟨-, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcm'
    have h2 : ringChar K ≠ 2 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]
      exact hp2
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates
      (X ⧸ center X) .POmegaOdd (Or.inl rfl) 3 p f hcm K hK e
    obtain ⟨φ, hOut⟩ := outData_coordinateQuadOdd K 3 hp hf hK h2 le_rfl hgates
    set e' := coordinateOddWitnessEquiv K e with he'
    let Φ : MulAut X →* MulAut (matrixProjectiveDerived (coordinateQuadOdd 3 K)) :=
      (MulAut.congr e').toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
    have hΦ : Function.Injective Φ :=
      (MulAut.congr e').injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
    have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (e' (QuotientGroup.mk' (center X) x)) :=
      fun x => by
        change MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
        rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
    have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
      exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
    have hI : (inner (matrixProjectiveDerived (coordinateQuadOdd 3 K))).comap Φ =
        (MulAut.conj : X →* MulAut X).range := by
      ext α
      rw [mem_comap]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hconjΦ y
        exact ⟨x, hΦ (hx.symm.trans hy)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, (hΦconj x).symm⟩
    have hIC' : inner (matrixProjectiveDerived (coordinateQuadOdd 3 K)) ≤ C.map Φ := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hconjΦ y
      exact ⟨MulAut.conj x, hIC ⟨x, rfl⟩, hx.symm⟩
    obtain ⟨V', hV'⟩ := exists_isU4Complement hOut hIC' (isSylowIn_map hΦ hP)
    exact ⟨_, isU4Complement_comap hΦ hI hV'⟩
  all_goals omega

end CFSG.ComponentClassification.HarrisLit.T1
