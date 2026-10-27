module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrNice
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.RankThree.PartOne.OutStructure CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Index

variable {A : Type*} [Group A]

theorem exists_closure_sup_inf [Finite A] {E P : Subgroup A} {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) (hm : E.relIndex P ≤ 3) :
    P ≤ E ∨ ∃ c ∈ P, P ≤ Subgroup.closure {c} ⊔ (P ⊓ E) := by
  by_cases hPE : P ≤ E
  · exact Or.inl hPE
  right
  obtain ⟨c, hcP, hcE⟩ := Set.not_subset.1 hPE
  refine ⟨c, hcP, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : E.relIndex P ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card E P
  have hpos : 0 < E.relIndex P := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmp : E.relIndex P = p := by
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hio
      exact hPE (Subgroup.relIndex_eq_one.1 hio)
    have hp3 : p ≤ 3 := by
      have : p ∣ E.relIndex P := hio ▸ dvd_pow_self p hi0
      exact (Nat.le_of_dvd hpos this).trans hm
    have hi1 : i = 1 := by
      by_contra hne
      have hi2 : 2 ≤ i := by omega
      have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi2
      have := hio ▸ hm
      have h4 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
      omega
    rw [hio, hi1, pow_one]
  set Hc : Subgroup A := Subgroup.closure {c} ⊔ (P ⊓ E) with hHc
  have hHcP : Hc ≤ P := sup_le ((Subgroup.closure_le P).2 (by simpa using hcP)) inf_le_left
  have hPEHc : P ⊓ E ≤ Hc := le_sup_right
  have htower : (P ⊓ E).relIndex Hc * Hc.relIndex P = (P ⊓ E).relIndex P :=
    Subgroup.relIndex_mul_relIndex _ _ _ hPEHc hHcP
  rw [inf_relIndex_left, hmp] at htower
  have ha : (P ⊓ E).relIndex Hc ≠ 1 := by
    intro h1
    have := Subgroup.relIndex_eq_one.1 h1
    exact hcE (this (Subgroup.mem_sup_left (Subgroup.subset_closure rfl) : c ∈ Hc)).2
  have hdv : (P ⊓ E).relIndex Hc ∣ p := Dvd.intro _ htower
  rcases (Nat.dvd_prime hp).1 hdv with h1 | h1
  · exact absurd h1 ha
  · rw [h1] at htower
    have hb : Hc.relIndex P = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hp.pos (htower.trans (mul_one p).symm)
      exact this
    exact Subgroup.relIndex_eq_one.1 hb

theorem mem_of_pow_mem_of_index_le_three_of_coprime [Finite A] (E : Subgroup A)
    (h : E.index ≤ 3) {e : ℕ} (he : Nat.Coprime e 6) {α : A} (hα : α ^ e ∈ E) : α ∈ E := by
  classical
  have h0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Fintype (A ⧸ E) := Fintype.ofFinite _
  set N : ℕ := (E.index).factorial with hN
  have hNdvd : N ∣ 6 := by
    have : (E.index).factorial ∣ (3 : ℕ).factorial := Nat.factorial_dvd_factorial h
    simpa [Nat.factorial] using this
  have hαN : α ^ N ∈ E := by
    have hker : α ^ N ∈ (MulAction.toPermHom A (A ⧸ E)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have hc := pow_card_eq_one (x := (MulAction.toPermHom A (A ⧸ E)) α)
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hc
      exact hc
    exact (Subgroup.normalCore_le E) (by rwa [Subgroup.normalCore_eq_ker])
  have hcop : Nat.Coprime e N := Nat.Coprime.coprime_dvd_right hNdvd he
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have : α = (α ^ e) ^ u * (α ^ N) ^ v := by
    rw [← zpow_natCast α e, ← zpow_natCast α N, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← zpow_add]
    nth_rewrite 1 [← zpow_one α]
    congr 1
    linarith
  rw [this]
  exact mul_mem (E.zpow_mem hα u) (E.zpow_mem hαN v)

end Index

section Generic

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem orthD_conj_mem (g : similarityPairs Q) {δ : MulAut (matrixProjectiveDerived Q)}
    (hδ : δ ∈ orthD Q) :
    matrixProjectiveConjugationHom Q g * δ * (matrixProjectiveConjugationHom Q g)⁻¹ ∈
      orthD Q := by
  obtain ⟨⟨ℓ, hℓ⟩, rfl⟩ := (mem_orthD_iff Q δ).1 hδ
  refine (mem_orthD_iff Q _).2 ⟨⟨g * ℓ * g⁻¹, (linearPairsNormal Q).conj_mem ℓ hℓ g⟩, ?_⟩
  simp [map_mul, map_inv]

theorem image_le_normalizer_orthD : matrixProjectiveImage Q ≤
    Subgroup.normalizer (orthD Q : Set (MulAut (matrixProjectiveDerived Q))) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro δ
  refine ⟨fun hδ => orthD_conj_mem Q g hδ, fun hδ => ?_⟩
  have := orthD_conj_mem Q g⁻¹ hδ
  simpa [map_inv, mul_assoc] using this

variable [Finite K]

theorem exists_gen_image : ∃ g ∈ matrixProjectiveImage Q, ∀ x ∈ matrixProjectiveImage Q,
    ∃ k : ℤ, g ^ k * x ∈ orthD Q := by
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  refine ⟨matrixProjectiveConjugationHom Q g₀, ⟨g₀, rfl⟩, ?_⟩
  rintro _ ⟨h, rfl⟩
  obtain ⟨k, hk⟩ := hg₀ h
  exact ⟨k, (mem_orthD_iff Q _).2 ⟨⟨g₀ ^ k * h, hk⟩, by rw [map_mul, map_zpow]⟩⟩

variable [CharP K 2]

theorem gen_of_le_image (hQ : ∃ v, Q v ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hPE : P ≤ matrixProjectiveImage Q) (hP : IsPGroup p P) :
    ∃ a ∈ P, P ≤ Subgroup.closure {a} ⊔ inn (matrixProjectiveDerived Q) := by
  obtain ⟨a, haP, ha⟩ := exists_gen_mod hPE (image_le_normalizer_orthD Q) (exists_gen_image Q)
  refine ⟨a, haP, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := ha x hx
  have hmem : (a ^ k)⁻¹ * x ∈ P := mul_mem (inv_mem (P.zpow_mem haP k)) hx
  obtain ⟨j, hj⟩ := hP ⟨_, hmem⟩
  have hj' : ((a ^ k)⁻¹ * x) ^ p ^ j = 1 := congrArg Subtype.val hj
  have hinn : (a ^ k)⁻¹ * x ∈ inn (matrixProjectiveDerived Q) :=
    orthD_D2 Q hQ hnd hT hp hp2 hk (k := j) (by rw [hj']; exact one_mem _)
  have hx' : x = a ^ k * ((a ^ k)⁻¹ * x) := (mul_inv_cancel_left (a ^ k) x).symm
  have hmul := Subgroup.mul_mem_sup (Subgroup.zpow_mem (Subgroup.closure {a})
    (Subgroup.subset_closure (Set.mem_singleton a)) k) hinn
  rw [← hx'] at hmul
  exact hmul

theorem outPTwoGen_of_image_index_le_three (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hidx : (matrixProjectiveImage Q).index ≤ 3) :
    OutPTwoGen (matrixProjectiveDerived Q) p := by
  have hQ : ∃ v, Q v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  intro P hP
  have hm : (matrixProjectiveImage Q).relIndex P ≤ 3 := by
    refine le_trans (Subgroup.relIndex_le_of_le_right le_top ?_) ?_
    · rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    · rw [Subgroup.relIndex_top_right]
      exact hidx
  rcases exists_closure_sup_inf hp hP hm with hPE | ⟨c, hcP, hc⟩
  · obtain ⟨a, haP, ha⟩ := gen_of_le_image Q hQ hnd hT hp hp2 hPE hP
    refine ⟨a, haP, a, haP, ha.trans (sup_le_sup_right ?_ _)⟩
    exact Subgroup.closure_mono (by simp)
  · obtain ⟨a, haP, ha⟩ := gen_of_le_image Q hQ hnd hT hp hp2 (inf_le_right :
      P ⊓ matrixProjectiveImage Q ≤ matrixProjectiveImage Q) (hP.to_le inf_le_left)
    refine ⟨a, haP.1, c, hcP, hc.trans (sup_le ?_ ?_)⟩
    · have hcc : ({c} : Set (MulAut (matrixProjectiveDerived Q))) ⊆ {a, c} := by simp
      exact (Subgroup.closure_mono hcc).trans le_sup_left
    · have haa : ({a} : Set (MulAut (matrixProjectiveDerived Q))) ⊆ {a, c} := by simp
      exact ha.trans (sup_le ((Subgroup.closure_mono haa).trans le_sup_left) le_sup_right)

omit [Finite K] [CharP K 2] in
theorem linear_of_card_two (hK : Nat.card K = 2) (g : similarityPairs Q) :
    g ∈ linearSimilarityPairs Q := by
  rw [mem_linearSimilarityPairs_iff]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (le_refl 1) (show Nat.card K = 2 ^ 1 by simpa using hK)
  have := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact Subsingleton.elim _ _

theorem outPInner_of_image_two (hQ : ∃ v, Q v ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : Nat.card K = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hE : ∀ x : MulAut (matrixProjectiveDerived Q), (∃ k : ℕ, x ^ r ^ k = 1) →
      x ∈ matrixProjectiveImage Q) : OutPInner (matrixProjectiveDerived Q) r := by
  intro P hP x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ r ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨g, rfl⟩ := hE x ⟨k, hk'⟩
  have hD : matrixProjectiveConjugationHom Q g ∈ orthD Q :=
    (mem_orthD_iff Q _).2 ⟨⟨g, linear_of_card_two Q hK g⟩, rfl⟩
  exact orthD_D2 Q hQ hnd hT hr hr2 hD (k := k) (by rw [hk']; exact one_mem _)

end Generic

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

theorem plus_four_index {Y : Type} [Group Y] {f : ℕ} (h : StatedClassicalModel Y .POmegaPlus 4 2 f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  rw [← hEA, hst]
  exact (horbit.2.2.2.2.2 rfl).2

theorem outPTwoGen_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPTwoGen Y p := by
  have hn : 4 ≤ n := h.1.2.2
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
    exact OutPTwoGen.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
      (outPTwoGen_of_image_index_le_three _ hnd hT hp hp2 (plus_four_index h K hK e))
  · exact OutPTwoGen.of_outPNice (outPNice_POmegaPlus_ge_five hp hp2 hn5 h)

theorem outPTwoGen_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPTwoGen Y p :=
  OutPTwoGen.of_outPNice (outPNice_POmegaMinus hp hp2 h.1.2.2 h)

theorem outPInner_pomegaPlus_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    OutPInner Y r := by
  have hn : 4 ≤ n := h.1.2.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  refine OutPInner.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (outPInner_of_image_two _ hQ hnd hT hK2 hr (by omega) ?_)
  rintro x ⟨k, hk⟩
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · refine mem_of_pow_mem_of_index_le_three _ (plus_four_index h K hK e) hr (by omega)
      (k := k) (α := x) ?_
    rw [hk]
    exact one_mem _
  · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5]
    exact Subgroup.mem_top x

theorem outPInner_pomegaMinus_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    OutPInner Y r := by
  have hn : 4 ≤ n := h.1.2.2
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  refine OutPInner.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e).symm
    (outPInner_of_image_two _ hQ hnd hT hK2 hr (by omega) ?_)
  rintro x -
  rw [htop]
  exact Subgroup.mem_top x

end Model

end CFSG.AGLEmbedding.ParabAutIrr
