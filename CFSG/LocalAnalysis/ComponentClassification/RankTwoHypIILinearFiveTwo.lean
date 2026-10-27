module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYComponent
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource

public section

namespace CFSG.ComponentClassification.RankTwoHypIILinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.Assembly.LowTwoRank FourGroupEvenCanonical
  CFSG.ComponentClassification.PresentationLocal
open CFSG.ComponentClassification.OutcomeLocal (oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

variable {K : Type} [Field K]

theorem ringEquiv_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (φ : K ≃+* K) : φ = 1 := by
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    classical
    have := Fintype.ofFinite K
    intro x
    have hu : ({0, 1} : Finset K) = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK])
    have hx : x ∈ ({0, 1} : Finset K) := hu ▸ Finset.mem_univ x
    simpa using hx
  refine RingEquiv.ext fun x => ?_
  rcases h01 x with rfl | rfl
  · simp
  · simp

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map (e : G →* H) = commutator H := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    map_top_of_surjective _ e.surjective]

@[expose] noncomputable def commutatorEquivOfMulEquiv {W G : Type*} [Group W] [Group G]
    {N : Subgroup W} (e : N ≃* G) : (⁅N, N⁆ : Subgroup W) ≃* commutator G :=
  ((MulEquiv.subgroupCongr (map_subtype_commutator N).symm).trans
    ((commutator N).equivMapOfInjective N.subtype N.subtype_injective).symm).trans
    ((e.subgroupMap (commutator N)).trans (MulEquiv.subgroupCongr (map_commutator_mulEquiv e)))

theorem commutator_subgroupOf_self {W : Type*} [Group W] (N : Subgroup W) :
    (⁅N, N⁆ : Subgroup W).subgroupOf N = commutator N := by
  rw [← map_subtype_commutator N, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective]

theorem eq_one_of_mem_centralizer_commutator {W G : Type*} [Group W] [Group G] {N : Subgroup W}
    (e : N ≃* G) (hG : centralizer (commutator G : Set G) = ⊥) {c : W} (hcN : c ∈ N)
    (hc : c ∈ centralizer ((⁅N, N⁆ : Subgroup W) : Set W)) : c = 1 := by
  have h1 : e ⟨c, hcN⟩ ∈ centralizer (commutator G : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [← map_commutator_mulEquiv e] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : (x : W) ∈ ⁅N, N⁆ := by
      rw [← commutator_subgroupOf_self] at hx
      exact hx
    have := mem_centralizer_iff.mp hc _ hx'
    change e x * e ⟨c, hcN⟩ = e ⟨c, hcN⟩ * e x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this
  rw [hG, mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem rigidInvolution_dualAut_five_two [Finite K] (hK : Nat.card K = 2) :
    RigidInvolution (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range
      (dualAut 5 K) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK'
  have : Finite (MulAut (projectiveSL 5 K)) := finite_mulAut_projectiveSL
  obtain ⟨hinj, hNinn, -, hM, hNC, hNnormal, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers le_rfl hK' (n := 5) (by norm_num) 1
      (Or.inl rfl)
  have hβ : conjAut 5 K 1 * dualAut 5 K = dualAut 5 K := by rw [map_one, one_mul]
  rw [hβ] at hM hNC hNnormal
  set O := matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hO
  set N := O.map (conjAut 5 K) with hN
  have eN : N ≃* O := (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
    (MonoidHom.ofInjective hinj).symm
  obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
    (dotForm_restrict_isAlt (k := K) (n := 5)) (dotForm_restrict_nondegenerate (r := 2) rfl)
    (finrank_dotForm_ker (r := 2) rfl)
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp 2 K) hK' (by norm_num) ⟨MulEquiv.refl _⟩
  let e : N ≃* sympFour := ((eN.trans (oneRestrictEquiv (r := 2) rfl)).trans e₂).trans
    (eProj.symm.trans (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hK))
  set L : Subgroup (MulAut (projectiveSL 5 K)) := ⁅N, N⁆ with hL
  have eL : L ≃* commutator sympFour := commutatorEquivOfMulEquiv e
  have hLsimple : IsSimpleGroup L := by
    have := isSimpleGroup_commutator_sympFour
    exact eL.isSimpleGroup
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hab
    apply not_isMulCommutative_commutator_sympFour
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eL.symm.injective
    rw [map_mul, map_mul, hab]
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_isSimpleGroup hLsimple hnc
  have heven : Even (Nat.card L) := by
    rw [Nat.card_congr (eL.trans commutatorEquivAlternating).toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_fin] at h
    have h' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      have : Nat.factorial 6 = 720 := by decide
      omega
    rw [h']
    decide
  have hLN : L ≤ N := by
    rw [hL, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine ⟨L, hLN.trans hNinn, hLN.trans hNC, ?_, hLp,
    twoNilpotentCentral_of_isSimpleGroup hLsimple hLp heven, ?_⟩
  ·
    intro c hc
    have hcN : c ∈ normalizer (N : Set (MulAut (projectiveSL 5 K))) :=
      (normal_subgroupOf_iff_le_normalizer hNC).mp hNnormal hc
    have hmap : N.map (MulAut.conj c).toMonoidHom = N := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.mp hcN x).mp hx
      · intro x hx
        refine ⟨c⁻¹ * x * c, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (mem_normalizer_iff.mp (inv_mem hcN) x).mp hx
        simpa [mul_assoc] using this
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : (MulAut.conj c).toMonoidHom y ∈ L.map (MulAut.conj c).toMonoidHom :=
        mem_map_of_mem _ hy
      rwa [hL, Subgroup.map_commutator, hmap] at this
    · intro hy
      have hy' : (MulAut.conj c⁻¹).toMonoidHom (c * y * c⁻¹) ∈
          L.map (MulAut.conj c⁻¹).toMonoidHom := mem_map_of_mem _ hy
      have hmap' : N.map (MulAut.conj c⁻¹).toMonoidHom = N := by
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          exact (mem_normalizer_iff.mp (inv_mem hcN) x).mp hx
        · intro x hx
          refine ⟨c * x * c⁻¹, (mem_normalizer_iff.mp hcN x).mp hx, ?_⟩
          simp [mul_assoc]
      rw [hL, Subgroup.map_commutator, hmap'] at hy'
      simpa [MulAut.conj_apply, mul_assoc] using hy'
  ·
    intro s hs hsL _
    have hs' : s ∈ (centralizer {dualAut 5 K} : Set (MulAut (projectiveSL 5 K))) := hs
    rw [hM] at hs'
    obtain ⟨g, hg, φ, ε, hε, rfl⟩ := hs'
    rw [ringEquiv_eq_one_of_card_two hK φ, map_one, mul_one] at hsL ⊢
    have hδL : dualAut 5 K ^ ε ∈ centralizer (L : Set (MulAut (projectiveSL 5 K))) := by
      refine pow_mem ?_ ε
      rw [mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hNC (hLN hy))
    have hgL : conjAut 5 K g ∈ centralizer (L : Set (MulAut (projectiveSL 5 K))) := by
      have := mul_mem hsL (inv_mem hδL)
      rwa [mul_inv_cancel_right] at this
    have hg1 := eq_one_of_mem_centralizer_commutator e centralizer_commutator_sympFour
      (mem_map_of_mem _ hg) hgL
    rw [hg1, one_mul]
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · left
      rw [pow_zero]
    · right
      rw [pow_one]

end CFSG.ComponentClassification.RankTwoHypIILinear
