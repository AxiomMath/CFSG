module

public import CFSG.LieType.ChevTwo.OutDataGen
import CFSG.RankThree.PartOne.KLC.D4OutCentral

public section

namespace CFSG.LieType.ChevTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.Quasithin.H13.OutTwoNilp (twoNilpotent_of_comm)
open scoped commutatorElement

section ThreePoint

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem commutator_mem_of_fixes_orbit (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hE : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ N)
    {α : A} (hfix : ∀ a : A, α • (a • F) = a • F) (γ : A) : ⁅γ, α⁆ ∈ N := by
  have hstab : ∀ a γ : A, γ • (a • F) = a • F → ⁅γ, α⁆ ∈ N := by
    intro a γ hγ
    have h1 : (a⁻¹ * γ * a) • F = F := by
      calc (a⁻¹ * γ * a) • F = a⁻¹ • (γ • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hγ]
        _ = F := inv_smul_smul a F
    have h2 : (a⁻¹ * α * a) • F = F := by
      calc (a⁻¹ * α * a) • F = a⁻¹ • (α • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hfix a]
        _ = F := inv_smul_smul a F
    have h3 := hE _ _ h1 h2
    have e : ⁅a⁻¹ * γ * a, a⁻¹ * α * a⁆ = a⁻¹ * ⁅γ, α⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e] at h3
    have h4 := Subgroup.Normal.conj_mem ‹N.Normal› _ h3 a
    have e2 : a * (a⁻¹ * ⁅γ, α⁆ * a) * a⁻¹ = ⁅γ, α⁆ := by group
    rwa [e2] at h4
  set S := CFSG.RankThree.PartOne.KLC.commModSubgroup N α with hS
  have hSstab : ∀ a γ : A, γ • (a • F) = a • F → γ ∈ S := fun a γ h => hstab a γ h
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  have hz : ∀ γ₁ : A, γ₁ • F = y → ∃ s ∈ S, s • F = z := by
    intro γ₁ hγ₁
    have hκ₁ : (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • F := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • (κ • F) := by simp [mul_smul]
        _ = γ₁ • F := by rw [hκF]
    refine ⟨γ₁ * κ * γ₁⁻¹, hSstab γ₁ _ hκ₁, ?_⟩
    have hu : γ₁ • y = F ∨ γ₁ • y = y ∨ γ₁ • y = z := by
      have := hO (γ₁ * γ₁)
      rwa [mul_smul, hγ₁] at this
    have hv : γ₁ • z = F ∨ γ₁ • z = y ∨ γ₁ • z = z := by
      have := hO (γ₁ * (κ * γ₁))
      rwa [mul_smul, mul_smul, hγ₁, hκy] at this
    have hu_y : γ₁ • y ≠ y := fun h =>
      hFy (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have hv_y : γ₁ • z ≠ y := fun h =>
      hFz (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have huv : γ₁ • y ≠ γ₁ • z := fun h => hyz (smul_left_cancel γ₁ h)
    have hκu : (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • z := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • (κ • y) := by simp [mul_smul]
        _ = γ₁ • z := by rw [hκy]
    have hκv : (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • y := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • (κ • z) := by simp [mul_smul]
        _ = γ₁ • y := by rw [hκz]
    rcases hu with hu | hu | hu
    · have hvz : γ₁ • z = z := by
        rcases hv with hv | hv | hv
        · exact absurd (hu.trans hv.symm) huv
        · exact absurd hv hv_y
        · exact hv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) := by rw [hu]
        _ = γ₁ • z := hκu
        _ = z := hvz
    · exact absurd hu hu_y
    · have hvF : γ₁ • z = F := by
        rcases hv with hv | hv | hv
        · exact hv
        · exact absurd hv hv_y
        · exact absurd (hu.trans hv.symm) huv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) := by rw [hvF]
        _ = γ₁ • y := hκv
        _ = z := hu
  have hκS : κ ∈ S := hSstab 1 κ (by simpa using hκF)
  rcases hO γ with h | h | h
  · exact hSstab 1 γ (by simpa using h)
  · obtain ⟨s, hs, hsF⟩ := hz γ h
    have hksF : (κ * s) • F = y := by rw [mul_smul, hsF, hκz]
    have h1 : ((κ * s)⁻¹ * γ) • F = F := by
      calc ((κ * s)⁻¹ * γ) • F = (κ * s)⁻¹ • (γ • F) := mul_smul _ _ _
        _ = (κ * s)⁻¹ • ((κ * s) • F) := by rw [h, hksF]
        _ = F := inv_smul_smul _ _
    have h2 : (κ * s)⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem (S.mul_mem hκS hs) h2
    have e3 : κ * s * ((κ * s)⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3
  · obtain ⟨s, hs, hsF⟩ := hz (κ * γ) (by rw [mul_smul, h, hκz])
    have h1 : (s⁻¹ * γ) • F = F := by
      calc (s⁻¹ * γ) • F = s⁻¹ • (γ • F) := mul_smul _ _ _
        _ = s⁻¹ • (s • F) := by rw [h, hsF]
        _ = F := inv_smul_smul _ _
    have h2 : s⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem hs h2
    have e3 : s * (s⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3

theorem twoNilpotent_quotient_of_three_point [Finite A] (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z) {κ : A} (hκF : κ • F = F)
    (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z) (hN : ∀ n ∈ N, n • F = F)
    (hE : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ N) : TwoNilpotent (A ⧸ N) := by
  classical
  have hmk : ∀ a b : A, ⁅a, b⁆ ∈ N → (a : A ⧸ N) * b = b * a := by
    intro a b h
    have h1 : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  by_cases hall : ∀ a : A, a • F = F
  · refine twoNilpotent_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact hmk a b (hE a b (hall a) (hall b))
  push Not at hall
  obtain ⟨a₀, ha₀⟩ := hall
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  obtain ⟨a₁, ha₁⟩ : ∃ a : A, a • F = y := by
    rcases hO a₀ with h | h | h
    · exact absurd h ha₀
    · exact ⟨a₀, h⟩
    · exact ⟨κ * a₀, by rw [mul_smul, h, hκz]⟩
  have horb : MulAction.orbit A F = {F, y, z} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      rcases hO b with h | h | h <;> simp [h]
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact ⟨a₁, ha₁⟩
      · exact ⟨κ * a₁, by show (κ * a₁) • F = _; rw [mul_smul, ha₁, hκy]⟩
  set O := MulAction.orbit A F with hOdef
  haveI : Finite O := Finite.of_surjective (fun a : A => (⟨a • F, MulAction.mem_orbit F a⟩ : O))
    (by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩)
  letI : Fintype O := Fintype.ofFinite O
  have hcardO : Nat.card O = 3 := by
    rw [Nat.card_coe_set_eq, horb, Set.ncard_eq_three.mpr ⟨F, y, z, hFy, hFz, hyz, rfl⟩]
  haveI : Nontrivial O := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hcardAlt : Nat.card (alternatingGroup O) = 3 := by
    rw [nat_card_alternatingGroup, hcardO]
    decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : A →* Equiv.Perm O := MulAction.toPermHom A O with hψ
  have hT : ∀ α : A, ψ α = 1 → ∀ γ : A, ⁅γ, α⁆ ∈ N := by
    intro α hα
    refine commutator_mem_of_fixes_orbit N hO hκF hκy hκz hyz hE fun a => ?_
    exact congrArg (fun σ : Equiv.Perm O => ((σ ⟨a • F, MulAction.mem_orbit F a⟩ : O) : X)) hα
  set M : Subgroup A := (Equiv.Perm.sign.comp ψ).ker with hM
  have hMmem : ∀ α : A, α ∈ M → ψ α ∈ alternatingGroup O := by
    intro α hα
    rw [hM, MonoidHom.mem_ker, MonoidHom.comp_apply] at hα
    exact Equiv.Perm.mem_alternatingGroup.2 hα
  have hMcomm : ∀ α ∈ M, ∀ β ∈ M, ⁅α, β⁆ ∈ N := by
    intro α hα β hβ
    by_cases h1 : ψ α = 1
    · rw [← commutatorElement_inv]
      exact N.inv_mem (hT α h1 β)
    · have hσ : (⟨ψ α, hMmem α hα⟩ : alternatingGroup O) ≠ 1 := fun h =>
        h1 (congrArg Subtype.val h)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
        (mem_zpowers_of_prime_card hcardAlt hσ (g' := ⟨ψ β, hMmem β hβ⟩))
      have hk' : ψ α ^ k = ψ β := by
        have := congrArg Subtype.val hk
        simpa using this
      have ht : ψ (β * (α ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
      have e : ⁅α, β⁆ = ⁅α, β * (α ^ k)⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hT _ ht α
  set Mbar : Subgroup (A ⧸ N) := M.map (QuotientGroup.mk' N) with hMbar
  haveI : Mbar.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  refine TwoNilpotent.of_normal_comm Mbar ?_ fun x => ?_
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    exact hmk α β (hMcomm α hα β hβ)
  · induction x using QuotientGroup.induction_on with
    | H a =>
      refine ⟨1, Subgroup.mem_map.2 ⟨a ^ 2, ?_, by simp⟩⟩
      rw [hM, MonoidHom.mem_ker, map_pow, Int.units_sq]

end ThreePoint

section Orthogonal

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

theorem twoNilpotent_outer_of_POmegaPlus_ge_five {X : Type} [Group X] {n m : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n 2 m) : TwoNilpotent (Outer X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n 2 m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [show coordinateQuadPlus n K = reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)
      from rfl, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hP : TwoNilpotent (Outer (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
    twoNilpotent_outer_of_commutator_mem_inner fun γ α => by
      have := CFSG.RankThree.PartOne.KLC.matrixProjectiveImage_commutator_mem_inner _ hQ hab'
        (a := γ) (b := α) (by rw [htop]; trivial) (by rw [htop]; trivial)
      rwa [commutatorElement_def] at this
  exact TwoNilpotent.of_mulEquiv (equivalence (coordinatePlusWitnessEquiv K e).symm) hP

theorem twoNilpotent_outer_of_POmegaMinus {X : Type} [Group X] {n m : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n 2 m) : TwoNilpotent (Outer X) := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n 2 m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [show coordinateQuadMinus n K hn1 b c =
      reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c) from rfl,
      card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  have hP : TwoNilpotent (Outer (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))) :=
    twoNilpotent_outer_of_commutator_mem_inner fun γ α => by
      have := CFSG.RankThree.PartOne.KLC.matrixProjectiveImage_commutator_mem_inner _ hQ hab'
        (a := γ) (b := α) (by rw [htop]; trivial) (by rw [htop]; trivial)
      rwa [commutatorElement_def] at this
  exact TwoNilpotent.of_mulEquiv (equivalence (coordinateMinusWitnessEquiv K hn1 b c e).symm) hP

theorem twoNilpotent_outer_of_POmegaPlus_four {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 2 m) : TwoNilpotent (Outer X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus (.inr (.inl rfl))
    4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    finite_mulAut_of_finite _
  refine TwoNilpotent.of_mulEquiv (equivalence (coordinatePlusWitnessEquiv K e).symm)
    (twoNilpotent_quotient_of_three_point (inner _)
      (F := projectivePointFamily (coordinateQuadPlus 4 K))
      (y := plusCX 4 K) (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz ?_ ?_)
  · intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  · rintro _ ⟨g, rfl⟩
    exact CFSG.RankThree.PartOne.KLC.inner_smul_pointFamily_coordinate K g
  · intro a b ha hb
    refine CFSG.RankThree.PartOne.KLC.matrixProjectiveImage_commutator_mem_inner _ hQ hA ?_ ?_
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb

end Orthogonal

end CFSG.LieType.ChevTwo
