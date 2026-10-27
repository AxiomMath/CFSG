module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamUniBlock
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamCQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem unitary_block_is_L2 {s N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 s K)
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x)
    (a : {a : primaryFactors (x : Module.End K (Fin N → K)) // IsGoodBlock h x a})
    (T : Subgroup (primeFormP h (idGram K N)))
    (haT : T = ((specialBlock (idForm h N) x (a.1 : K[X])).comap (toLinSU h N)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K N)) N)))
    {r : ℕ} (hr : Odd r) (hL : catalogIs (↥T ⧸ Subgroup.center ↥T) (S10.isL2n r)) :
    dualPoly h.bar (a.1 : K[X]) = a.1 ∧
      primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X]) = 2 ∧
      s * (a.1 : K[X]).natDegree = r := by
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ s := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : s ≠ 0) h.prime.one_lt
    omega
  obtain ⟨g, hg, hker⟩ := exists_surjective_specialBlock hq H a T haT
  haveI : Finite (LinearMap.GeneralLinearGroup K (Fin N → K)) := finite_gl_of_unitaryFieldData h
  haveI : Finite ↥(specialBlock (idForm h N) x (a.1 : K[X])) := inferInstance
  have hd : 1 ≤ (a.1 : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.1.2)
  have hsd : 1 ≤ s * (a.1 : K[X]).natDegree := Nat.mul_pos h.one_le hd
  haveI : Finite ↥T := inferInstance
  have hkerT : ∀ {G : Type} [Group G] (e : G ≃* ↥(specialBlock (idForm h N) x (a.1 : K[X]))),
      (g.comp e.toMonoidHom).ker ≤ Subgroup.center G := by
    intro G _ e z hz
    have h1 : e z ∈ g.ker := hz
    have h2 := hker h1
    have h3 := Subgroup.comap_center_le_center (f := e.toMonoidHom) e.injective
    exact h3 (by simpa using h2)
  rcases good_block_cases hq H a.1 a.2 with
      ⟨hself, hm2, F, hF, hFt, -, hcardF, h4, ⟨e⟩⟩ |
      ⟨hself, hm3, E, hE, hEt, m, -, hcardE, hm, hne, ⟨e⟩⟩ |
      ⟨hself, E, hE, hEt, m, -, hcardE, hm2, h4, ⟨e⟩⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F
        (by rw [Nat.card_eq_fintype_card]; exact h4)).commutator_eq_top
    have hkerF := hkerT e.symm
    have hcF : Nat.card F = 2 ^ (s * (a.1 : K[X]).natDegree) := by
      rw [Nat.card_eq_fintype_card, hcardF]
    exact ⟨hself, hm2, eq_of_SL_two_centerQuot_isL2n (E := F) hsd hcF hperf
      (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) hkerF hr hL⟩
  · exfalso
    letI : Field E := hE
    letI : Fintype E := hEt
    obtain ⟨r', rfl⟩ : ∃ r', m = r' + 1 := ⟨m - 1, by omega⟩
    have hperf := (suFactorFacts_holds E (r' + 1) (2 ^ (s * (a.1 : K[X]).natDegree)) hcardE hm
      hne).perfect
    have hkerE := hkerT e.symm
    exact false_of_SU_centerQuot_isL2n (E := E) (r := r') (t := s * (a.1 : K[X]).natDegree)
      (by omega) hsd hne (by rw [Nat.card_eq_fintype_card, hcardE]) hperf
      (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) hkerE hr hL
  · exfalso
    letI : Field E := hE
    letI : Fintype E := hEt
    have hperf := (slFactorFacts_holds E m hm2 (fun _ => h4)).perfect
    have hkerE := hkerT e.symm
    exact false_of_SL_centerQuot_isL2n_even (E := E) (e := 2 * (s * (a.1 : K[X]).natDegree))
      hm2 (by omega) (even_two_mul _) (by rw [Nat.card_eq_fintype_card, hcardE]) hperf
      (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) hkerE hr hL

private theorem uni_three_blocks {s N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 s K)
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x) {c : K}
    (hroot : aeval (x : Module.End K (Fin N → K)) (X ^ 3 - C c : K[X]) = 0) {r : ℕ}
    (a₁ a₂ a₃ : primaryFactors (x : Module.End K (Fin N → K)))
    (h12 : (a₁ : K[X]) ≠ a₂) (h13 : (a₁ : K[X]) ≠ a₃) (h23 : (a₂ : K[X]) ≠ a₃)
    (hm₁ : primaryMultiplicity (x : Module.End K (Fin N → K)) (a₁ : K[X]) = 2)
    (hm₂ : primaryMultiplicity (x : Module.End K (Fin N → K)) (a₂ : K[X]) = 2)
    (hm₃ : primaryMultiplicity (x : Module.End K (Fin N → K)) (a₃ : K[X]) = 2)
    (hs₁ : s * (a₁ : K[X]).natDegree = r) (hs₂ : s * (a₂ : K[X]).natDegree = r)
    (hs₃ : s * (a₃ : K[X]).natDegree = r) :
    N = 6 ∧ s = r ∧ ∀ b : primaryFactors (x : Module.End K (Fin N → K)),
      (b : K[X]) = a₁ ∨ (b : K[X]) = a₂ ∨ (b : K[X]) = a₃ := by
  classical
  have hs : 1 ≤ s := h.one_le
  have hsq := H.squarefree
  have hmin : minpoly K (x : Module.End K (Fin N → K)) ∣ (X ^ 3 - C c : K[X]) :=
    minpoly.dvd K _ hroot
  have hmonic : (X ^ 3 - C c : K[X]).Monic := monic_X_pow_sub_C c (by norm_num)
  have hdegmin : (minpoly K (x : Module.End K (Fin N → K))).natDegree ≤ 3 := by
    have := natDegree_le_of_dvd hmin hmonic.ne_zero
    rwa [natDegree_X_pow_sub_C] at this
  have hsum : ∑ a ∈ (primaryFactors (x : Module.End K (Fin N → K))), (a : K[X]).natDegree =
      (minpoly K (x : Module.End K (Fin N → K))).natDegree := by
    rw [← prod_primaryFactors hsq, natDegree_prod_of_monic]
    intro a ha
    exact monic_of_mem_primaryFactors ha
  have hd₂ : (a₂ : K[X]).natDegree = (a₁ : K[X]).natDegree :=
    Nat.eq_of_mul_eq_mul_left hs (hs₂.trans hs₁.symm)
  have hd₃ : (a₃ : K[X]).natDegree = (a₁ : K[X]).natDegree :=
    Nat.eq_of_mul_eq_mul_left hs (hs₃.trans hs₁.symm)
  have hdpos : ∀ a ∈ (primaryFactors (x : Module.End K (Fin N → K))), 1 ≤ a.natDegree := fun a ha =>
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
  let S3 : Finset K[X] := {(a₁ : K[X]), (a₂ : K[X]), (a₃ : K[X])}
  have hS3P : S3 ⊆ (primaryFactors (x : Module.End K (Fin N → K))) := by
    intro a ha
    simp only [S3, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact a₁.2
    · exact a₂.2
    · exact a₃.2
  have hcard3 : S3.card = 3 := Finset.card_eq_three.2 ⟨_, _, _, h12, h13, h23, rfl⟩
  have hdS3 : ∀ a ∈ S3, a.natDegree = (a₁ : K[X]).natDegree := by
    intro a ha
    simp only [S3, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact hd₂
    · exact hd₃
  have hsumS3 : ∑ a ∈ S3, a.natDegree = 3 * (a₁ : K[X]).natDegree := by
    rw [Finset.sum_eq_card_nsmul hdS3, hcard3, smul_eq_mul]
  have hle : ∑ a ∈ S3, a.natDegree ≤ ∑ a ∈ (primaryFactors (x : Module.End K (Fin N → K))), a.natDegree :=
    Finset.sum_le_sum_of_subset hS3P
  have hd1 : (a₁ : K[X]).natDegree = 1 := by
    have h1 := hdpos _ a₁.2
    omega
  have hPS : (primaryFactors (x : Module.End K (Fin N → K))) = S3 := by
    by_contra hne
    obtain ⟨b, hbP, hbS⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.2 ⟨hS3P, fun e => hne e.symm⟩)
    have hlt := Finset.sum_lt_sum_of_subset hS3P hbP hbS (hdpos b hbP) (fun _ _ _ => Nat.zero_le _)
    omega
  have hmS3 : ∀ a ∈ S3, a.natDegree * primaryMultiplicity (x : Module.End K (Fin N → K)) a = 2 := by
    intro a ha
    simp only [S3, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · rw [hm₁, hd1]
    · rw [hm₂, hd₂, hd1]
    · rw [hm₃, hd₃, hd1]
  have hdim := finrank_eq_sum_degree_mul_multiplicity (x := (x : Module.End K (Fin N → K))) hsq
  rw [Finset.sum_coe_sort (primaryFactors (x : Module.End K (Fin N → K))) (fun a => a.natDegree *
    primaryMultiplicity (x : Module.End K (Fin N → K)) a), hPS, Finset.sum_eq_card_nsmul hmS3,
    hcard3, smul_eq_mul, Module.finrank_fin_fun] at hdim
  refine ⟨by omega, by rw [← hs₁, hd1, mul_one], fun b => ?_⟩
  have hb : (b : K[X]) ∈ S3 := hPS ▸ b.2
  simpa [S3] using hb

private theorem uni_three_components {ℓ s N : ℕ} (hℓ : ℓ = 2) {K : Type} [Field K]
    (h : UnitaryFieldData ℓ s K) (A : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {T₁ T₂ T₃ : Subgroup (primeFormP h (idGram K N))}
    (h1 : CFSG.Open.IsComponentOf T₁ (fixSubgroup (primeFormConjHom h (idGram K N) A)))
    (h2 : CFSG.Open.IsComponentOf T₂ (fixSubgroup (primeFormConjHom h (idGram K N) A)))
    (h3 : CFSG.Open.IsComponentOf T₃ (fixSubgroup (primeFormConjHom h (idGram K N) A)))
    (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃) (h23 : T₂ ≠ T₃) {r : ℕ} (hr : Odd r)
    (hL1 : catalogIs (↥T₁ ⧸ Subgroup.center ↥T₁) (S10.isL2n r))
    (hL2 : catalogIs (↥T₂ ⧸ Subgroup.center ↥T₂) (S10.isL2n r))
    (hL3 : catalogIs (↥T₃ ⧸ Subgroup.center ↥T₃) (S10.isL2n r)) :
    N = 6 ∧ s = r ∧ ∀ M : Subgroup (primeFormP h (idGram K N)),
      CFSG.Open.IsComponentOf M (fixSubgroup (primeFormConjHom h (idGram K N) A)) →
        M = T₁ ∨ M = T₂ ∨ M = T₃ := by
  subst hℓ
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ s := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : s ≠ 0) h.prime.one_lt
    omega
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA
  obtain ⟨a₁, ha₁⟩ := exists_good_primaryFactor_of_component hq A rfl H T₁ h1
  obtain ⟨a₂, ha₂⟩ := exists_good_primaryFactor_of_component hq A rfl H T₂ h2
  obtain ⟨a₃, ha₃⟩ := exists_good_primaryFactor_of_component hq A rfl H T₃ h3
  obtain ⟨-, hm₁, hs₁⟩ := unitary_block_is_L2 h H a₁ T₁ ha₁ hr hL1
  obtain ⟨-, hm₂, hs₂⟩ := unitary_block_is_L2 h H a₂ T₂ ha₂ hr hL2
  obtain ⟨-, hm₃, hs₃⟩ := unitary_block_is_L2 h H a₃ T₃ ha₃ hr hL3
  have hroot : aeval ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
      (X ^ 3 - C (c : K) : K[X]) = 0 := by
    have h1 : ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) =
        Matrix.toLin' ((A : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := rfl
    rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow,
      ← Units.val_pow_eq_pow_val, hA]
    ext v i
    by_cases hi : i = v <;> simp [hi]
  have hne12 : (a₁.1 : K[X]) ≠ a₂.1 := fun e => h12 (by rw [ha₁, ha₂, e])
  have hne13 : (a₁.1 : K[X]) ≠ a₃.1 := fun e => h13 (by rw [ha₁, ha₃, e])
  have hne23 : (a₂.1 : K[X]) ≠ a₃.1 := fun e => h23 (by rw [ha₂, ha₃, e])
  obtain ⟨hN, hsr, hall⟩ := uni_three_blocks h H hroot a₁.1 a₂.1 a₃.1 hne12 hne13 hne23 hm₁ hm₂
    hm₃ hs₁ hs₂ hs₃
  refine ⟨hN, hsr, fun M hM => ?_⟩
  obtain ⟨b, hb⟩ := exists_good_primaryFactor_of_component hq A rfl H M hM
  rcases hall b.1 with e | e | e
  · left
    rw [hb, ha₁, e]
  · right
    left
    rw [hb, ha₂, e]
  · right
    right
    rw [hb, ha₃, e]

private theorem censusBodyTwistedA_at (d : TauCeti.ValidLieTypeIndex) {n : ℕ}
    {q : TauCeti.PrimePower} (hd : d.1 = TauCeti.LieTypeIndex.twistedA n q) (hq2 : q.p = 2) :
    CensusBody d := by
  intro η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  classical
  have hU : KD264Lie.isUnitaryIdx d.1 := by
    rw [hd]
    trivial
  obtain ⟨r', q', K, hKf, h', hr', hd', hne, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx hU
  obtain ⟨hn', hq'⟩ := TauCeti.LieTypeIndex.twistedA.inj (hd.symm.trans hd')
  subst hq'
  let θ : (TauCeti.CFSGIndex.lie d).Group ≃* primeFormP h' (idGram K (r' + 1)) := eP.symm
  let β' : MulAut (primeFormP h' (idGram K (r' + 1))) := θ.symm.trans (η.trans θ)
  have hβ'mem : β' ∈ innAutDerived (primeFormP h' (idGram K (r' + 1))) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  have hq'' : ¬(r' + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    CFSG.ComponentClassification.OuterAutomorphisms.exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived
      h' isPrimeFormGram_idGram (by omega) hq'' hβ'mem hβ'3
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ η
  have hK : ∀ {J : Subgroup (TauCeti.CFSGIndex.lie d).Group},
      CFSG.Open.IsComponentOf J (fixSubgroup η) → CFSG.Open.IsComponentOf (J.map θ.toMonoidHom)
        (fixSubgroup (primeFormConjHom h' (idGram K (r' + 1)) A)) := by
    intro J hJ
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
    rw [← hβeq]
    exact hfix ▸ h1
  have hLT : ∀ {J : Subgroup (TauCeti.CFSGIndex.lie d).Group},
      catalogIs (↥J ⧸ Subgroup.center ↥J) (S10.isL2n r) →
        catalogIs (↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom))
          (S10.isL2n r) := by
    intro J hJ
    have eJ : ↥J ≃* ↥(J.map θ.toMonoidHom) := J.equivMapOfInjective θ.toMonoidHom θ.injective
    have eZ : (↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom)) :=
      QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
    exact (catalogIs_congr eZ).1 hJ
  obtain ⟨hN, hsr, hall⟩ := uni_three_components hq2 h' A hA (hK hJ₁) (hK hJ₂) (hK hJ₃)
    (fun h => h12 (Subgroup.map_injective θ.injective h))
    (fun h => h13 (Subgroup.map_injective θ.injective h))
    (fun h => h23 (Subgroup.map_injective θ.injective h)) hr (hLT hL1) (hLT hL2) (hLT hL3)
  have hr5 : n = 5 := by omega
  left
  refine ⟨?_, fun M hM => ?_⟩
  · refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨MulEquiv.refl _⟩⟩
    show S10.isU6n r (TauCeti.CFSGIndex.lie d)
    simp only [S10.isU6n, onLie, hd, hr5]
    exact ⟨hq2, hsr⟩
  · rcases hall _ (hK hM) with e | e | e
    · rw [Subgroup.map_injective θ.injective e]
      exact hL1
    · rw [Subgroup.map_injective θ.injective e]
      exact hL2
    · rw [Subgroup.map_injective θ.injective e]
      exact hL3

theorem censusBodyTwistedA : CensusBodyTwistedA := fun n q hv hq2 =>
  censusBodyTwistedA_at ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩ rfl hq2

end CFSG.LocalAnalysis.GLTheoremA.T1428
