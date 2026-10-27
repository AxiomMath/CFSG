module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentInteraction
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

section OmegaAt

variable {G : Type*} [Group G]

@[expose] def omegaAt (J : Subgroup G) (z a : G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = J.map (MulAut.conj g⁻¹).toMonoidHom ∧ g⁻¹ * z * g = a}

theorem mem_omegaAt_iff {J : Subgroup G} {z a : G} {A : Subgroup G} :
    A ∈ omegaAt J z a ↔ ∃ g : G, A = J.map (MulAut.conj g⁻¹).toMonoidHom ∧ g⁻¹ * z * g = a :=
  Iff.rfl

theorem omegaAt_subset_conjugateSet (J : Subgroup G) (z a : G) :
    omegaAt J z a ⊆ conjugateSet J :=
  fun _ ⟨g, hA, _⟩ => ⟨g, hA⟩

theorem mem_conjugateSet_iff_exists_mem_omegaAt {J : Subgroup G} {z : G} {A : Subgroup G} :
    A ∈ conjugateSet J ↔ ∃ a : G, A ∈ omegaAt J z a :=
  ⟨fun ⟨g, hA⟩ => ⟨g⁻¹ * z * g, g, hA, rfl⟩,
    fun ⟨_, h⟩ => omegaAt_subset_conjugateSet J z _ h⟩

theorem iUnion_omegaAt (J : Subgroup G) (z : G) : (⋃ a : G, omegaAt J z a) = conjugateSet J := by
  ext A
  rw [Set.mem_iUnion]
  exact mem_conjugateSet_iff_exists_mem_omegaAt.symm

private theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj 1).toMonoidHom = J :=
  map_conj_eq_iff_mem_normalizer.mpr (Subgroup.one_mem _)

private theorem map_map_conj_eq (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show b * (a * x * a⁻¹) * b⁻¹ = b * a * x * (b * a)⁻¹
  group

theorem omegaAt_nonempty_iff {J : Subgroup G} {z a : G} :
    (omegaAt J z a).Nonempty ↔ IsConj z a := by
  constructor
  · rintro ⟨A, g, -, hg⟩
    exact isConj_iff.mpr ⟨g⁻¹, by rw [← hg, inv_inv]⟩
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact ⟨_, c⁻¹, rfl, by rw [← hc, inv_inv]⟩

theorem self_mem_omegaAt (J : Subgroup G) (z : G) : J ∈ omegaAt J z z :=
  ⟨1, by rw [inv_one, map_conj_one], by rw [inv_one, one_mul, mul_one]⟩

theorem omegaAt_eq_orbit {J : Subgroup G} {z a : G} {A₀ : Subgroup G} (hA₀ : A₀ ∈ omegaAt J z a) :
    omegaAt J z a =
      {A | ∃ c ∈ Subgroup.centralizer ({a} : Set G), A = A₀.map (MulAut.conj c).toMonoidHom} := by
  obtain ⟨g₀, rfl, hg₀⟩ := hA₀
  ext A
  constructor
  · rintro ⟨g, rfl, hg⟩
    refine ⟨g⁻¹ * g₀, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have e1 : g⁻¹ * g₀ * h = g⁻¹ * z * g₀ := by rw [← hg₀]; group
      have e2 : h * (g⁻¹ * g₀) = g⁻¹ * z * g₀ := by rw [← hg]; group
      exact e2.trans e1.symm
    · rw [map_map_conj_eq, mul_inv_cancel_right]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨g₀ * c⁻¹, ?_, ?_⟩
    · rw [map_map_conj_eq, mul_inv_rev, inv_inv]
    · have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a rfl
      calc (g₀ * c⁻¹)⁻¹ * z * (g₀ * c⁻¹) = c * (g₀⁻¹ * z * g₀) * c⁻¹ := by group
        _ = c * a * c⁻¹ := by rw [hg₀]
        _ = a := by rw [← hca]; group

theorem omegaAt_self_eq (J : Subgroup G) (z : G) :
    omegaAt J z z =
      {A | ∃ c ∈ Subgroup.centralizer ({z} : Set G), A = J.map (MulAut.conj c⁻¹).toMonoidHom} := by
  rw [omegaAt_eq_orbit (self_mem_omegaAt J z)]
  ext A
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_mem hc, by rw [inv_inv]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_mem hc, rfl⟩

theorem omegaAt_self_eq_map_conj (J : Subgroup G) (z : G) :
    omegaAt J z z =
      {A | ∃ c ∈ Subgroup.centralizer ({z} : Set G), A = J.map (MulAut.conj c).toMonoidHom} :=
  omegaAt_eq_orbit (self_mem_omegaAt J z)

theorem map_conj_mem_omegaAt_self {J : Subgroup G} {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    J.map (MulAut.conj c).toMonoidHom ∈ omegaAt J z z := by
  rw [omegaAt_self_eq_map_conj]
  exact ⟨c, hc, rfl⟩

theorem mem_of_mem_omegaAt {J : Subgroup G} {z a : G} (hzJ : z ∈ J) {A : Subgroup G}
    (hA : A ∈ omegaAt J z a) : a ∈ A := by
  obtain ⟨g, rfl, rfl⟩ := hA
  refine mem_map_conj_iff.mpr ?_
  have h : (g⁻¹)⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [h]
  exact hzJ

theorem le_centralizer_of_mem_omegaAt {J : Subgroup G} {z a : G}
    (hJ : J ≤ Subgroup.centralizer ({z} : Set G)) {A : Subgroup G} (hA : A ∈ omegaAt J z a) :
    A ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨g, rfl, rfl⟩ := hA
  have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hJ
  rwa [map_conj_centralizer_singleton, inv_inv] at this

theorem omegaAt_eq_of_mem {J : Subgroup G} {z a : G} {A : Subgroup G} (hA : A ∈ omegaAt J z a)
    (b : G) : omegaAt A a b = omegaAt J z b := by
  obtain ⟨g, rfl, rfl⟩ := hA
  ext B
  constructor
  · rintro ⟨h, rfl, hh⟩
    refine ⟨g * h, ?_, ?_⟩
    · rw [map_map_conj_eq, mul_inv_rev]
    · rw [← hh]
      group
  · rintro ⟨k, rfl, hk⟩
    refine ⟨g⁻¹ * k, ?_, ?_⟩
    · have : (g⁻¹ * k)⁻¹ * g⁻¹ = k⁻¹ := by group
      rw [map_map_conj_eq, this]
    · rw [← hk]
      group

theorem natCard_of_mem_omegaAt {J : Subgroup G} {z a : G} {A : Subgroup G}
    (hA : A ∈ omegaAt J z a) : Nat.card A = Nat.card J := by
  obtain ⟨g, rfl, -⟩ := hA
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

end OmegaAt

section Involutions

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}

theorem eq_of_mem_map_conj_inv_of_unique_involution (hU : ∀ t ∈ J, orderOf t = 2 → t = z)
    {g t : G} (ht : t ∈ J.map (MulAut.conj g⁻¹).toMonoidHom) (h2 : orderOf t = 2) :
    t = g⁻¹ * z * g := by
  simpa using eq_conj_of_mem_map_conj_of_unique_involution hU ht h2

theorem mem_omegaAt_iff_of_unique_involution (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A : Subgroup G} {a : G} :
    A ∈ omegaAt J z a ↔ A ∈ conjugateSet J ∧ a ∈ A ∧ orderOf a = 2 := by
  constructor
  · intro hA
    refine ⟨omegaAt_subset_conjugateSet J z a hA, mem_of_mem_omegaAt hzJ hA, ?_⟩
    obtain ⟨g, rfl, rfl⟩ := hA
    simpa [hz] using orderOf_conj_eq g⁻¹ z
  · rintro ⟨⟨g, rfl⟩, ha, ha2⟩
    exact ⟨g, rfl, (eq_of_mem_map_conj_inv_of_unique_involution hU ha ha2).symm⟩

theorem eq_of_mem_omegaAt (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A : Subgroup G} {a t : G}
    (hA : A ∈ omegaAt J z a) (ht : t ∈ A) (h2 : orderOf t = 2) : t = a := by
  obtain ⟨g, rfl, rfl⟩ := hA
  exact eq_of_mem_map_conj_inv_of_unique_involution hU ht h2

theorem mem_of_isPGroup_of_mem_omegaAt (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A : Subgroup G}
    {a : G} (hA : A ∈ omegaAt J z a) {P : Subgroup G} (hPA : P ≤ A) (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) : a ∈ P := by
  obtain ⟨g, rfl, rfl⟩ := hA
  exact mem_of_isPGroup_of_unique_involution_subgroup
    (fun _ ht h2 => eq_of_mem_map_conj_inv_of_unique_involution hU ht h2) hPA hP hP1

theorem eq_of_mem_omegaAt_of_mem_omegaAt (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A : Subgroup G} {a b : G} (ha : A ∈ omegaAt J z a)
    (hb : A ∈ omegaAt J z b) : a = b := by
  obtain ⟨-, hbA, hb2⟩ := (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mp hb
  exact (eq_of_mem_omegaAt hU ha hbA hb2).symm

theorem pairwiseDisjoint_omegaAt (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) :
    (Set.univ : Set G).PairwiseDisjoint (omegaAt J z) := by
  intro a _ b _ hab
  exact Set.disjoint_left.mpr fun A ha hb =>
    hab (eq_of_mem_omegaAt_of_mem_omegaAt hzJ hz hU ha hb)

end Involutions

section Subnormal

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}

theorem isSubnormal_of_mem_omegaAt (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    {A : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) :
    IsSubnormal A (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨g, rfl, rfl⟩ := hA
  simpa using isSubnormal_map_conj_centralizer hJ g⁻¹

end Subnormal

section TightlyEmbedded

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}

theorem existsUnique_involution_of_mem_conjugateSet (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A : Subgroup G} (hA : A ∈ conjugateSet J) :
    ∃! a : G, orderOf a = 2 ∧ a ∈ A := by
  obtain ⟨a, ha⟩ := (mem_conjugateSet_iff_exists_mem_omegaAt (z := z)).mp hA
  obtain ⟨-, haA, ha2⟩ := (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mp ha
  exact ⟨a, ⟨ha2, haA⟩, fun t ht => eq_of_mem_omegaAt hU ha ht.2 ht.1⟩

theorem exists_involution_mem_iff_exists_mem_omegaAt (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A B : Subgroup G} (hA : A ∈ conjugateSet J)
    (hB : B ∈ conjugateSet J) :
    (∃ a : G, orderOf a = 2 ∧ a ∈ A ∧ a ∈ B) ↔ ∃ a : G, A ∈ omegaAt J z a ∧ B ∈ omegaAt J z a := by
  constructor
  · rintro ⟨a, ha2, haA, haB⟩
    exact ⟨a, (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mpr ⟨hA, haA, ha2⟩,
      (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mpr ⟨hB, haB, ha2⟩⟩
  · rintro ⟨a, haA, haB⟩
    obtain ⟨-, haA', ha2⟩ := (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mp haA
    obtain ⟨-, haB', -⟩ := (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mp haB
    exact ⟨a, ha2, haA', haB'⟩

theorem forall_involution_mem_iff (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {A B : Subgroup G} (hA : A ∈ conjugateSet J)
    (hB : B ∈ conjugateSet J) :
    (∀ a : G, orderOf a = 2 → (a ∈ A ↔ a ∈ B)) ↔ ∃ a : G, orderOf a = 2 ∧ a ∈ A ∧ a ∈ B := by
  constructor
  · intro h
    obtain ⟨a, ⟨ha2, haA⟩, -⟩ := existsUnique_involution_of_mem_conjugateSet hzJ hz hU hA
    exact ⟨a, ha2, haA, (h a ha2).mp haA⟩
  · rintro ⟨c, hc2, hcA, hcB⟩ a ha2
    obtain ⟨c', -, huA⟩ := existsUnique_involution_of_mem_conjugateSet hzJ hz hU hA
    obtain ⟨c'', -, huB⟩ := existsUnique_involution_of_mem_conjugateSet hzJ hz hU hB
    constructor
    · intro haA
      have hac : a = c := (huA a ⟨ha2, haA⟩).trans (huA c ⟨hc2, hcA⟩).symm
      rw [hac]
      exact hcB
    · intro haB
      have hac : a = c := (huB a ⟨ha2, haB⟩).trans (huB c ⟨hc2, hcB⟩).symm
      rw [hac]
      exact hcA

variable [Finite G]

theorem tightlyEmbedded_iff_omegaAt_self_eq (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) :
    classicalInvolutionTightlyEmbedded J ↔ omegaAt J z z = {J} := by
  rw [tightlyEmbedded_iff_centralizer_le_normalizer_of_unique_involution hzJ hz hU]
  constructor
  · intro hC
    ext A
    constructor
    · intro hA
      rw [omegaAt_self_eq] at hA
      obtain ⟨c, hc, rfl⟩ := hA
      exact map_conj_eq_iff_mem_normalizer.mpr (hC (inv_mem hc))
    · intro hA
      rw [Set.mem_singleton_iff] at hA
      subst hA
      exact self_mem_omegaAt _ _
  · intro h c hc
    have hmem : J.map (MulAut.conj c).toMonoidHom ∈ omegaAt J z z :=
      map_conj_mem_omegaAt_self hc
    rw [h] at hmem
    exact map_conj_eq_iff_mem_normalizer.mp hmem

theorem tightlyEmbedded_iff_subsingleton_omegaAt (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) :
    classicalInvolutionTightlyEmbedded J ↔ ∀ a : G, (omegaAt J z a).Subsingleton := by
  constructor
  · intro hTE a A hA B hB
    obtain ⟨g, rfl, rfl⟩ := hA
    obtain ⟨h, rfl, hh⟩ := hB
    have := (conj_eq_iff_map_conj_eq_of_tightlyEmbedded hzJ hz hU hTE g⁻¹ h⁻¹).mp (by
      simpa only [inv_inv] using hh.symm)
    exact this
  · intro h
    rw [tightlyEmbedded_iff_omegaAt_self_eq hzJ hz hU]
    exact ((h z).eq_singleton_of_mem (self_mem_omegaAt J z))

end TightlyEmbedded

section Hypotheses

variable {G : Type*} [Group G] [Finite G] {J : Subgroup G} {z : G}

theorem eq_of_orderOf_eq_two_of_isSubnormal_quaternion_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ t ∈ J, orderOf t = 2 → t = z :=
  (unique_involution_of_quaternion_sylow hzJ hz (isSubnormal_le hJ) S hS).1

omit [Finite G] in
theorem unique_involution_map_conj (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) (g : G) :
    g⁻¹ * z * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom ∧ orderOf (g⁻¹ * z * g) = 2 ∧
      (∀ t ∈ J.map (MulAut.conj g⁻¹).toMonoidHom, orderOf t = 2 → t = g⁻¹ * z * g) ∧
      ∀ P : Subgroup G, P ≤ J.map (MulAut.conj g⁻¹).toMonoidHom → IsPGroup 2 P → P ≠ ⊥ →
        g⁻¹ * z * g ∈ P := by
  have hA : J.map (MulAut.conj g⁻¹).toMonoidHom ∈ omegaAt J z (g⁻¹ * z * g) := ⟨g, rfl, rfl⟩
  obtain ⟨-, h1, h2⟩ := (mem_omegaAt_iff_of_unique_involution hzJ hz hU).mp hA
  exact ⟨h1, h2, fun t ht h2 => eq_of_mem_map_conj_inv_of_unique_involution hU ht h2,
    fun _ hPA hP hP1 => mem_of_isPGroup_of_mem_omegaAt hU hA hPA hP hP1⟩

theorem unique_involution_map_conj_of_quaternion_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) (g : G) :
    g⁻¹ * z * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom ∧ orderOf (g⁻¹ * z * g) = 2 ∧
      (∀ t ∈ J.map (MulAut.conj g⁻¹).toMonoidHom, orderOf t = 2 → t = g⁻¹ * z * g) ∧
      ∀ P : Subgroup G, P ≤ J.map (MulAut.conj g⁻¹).toMonoidHom → IsPGroup 2 P → P ≠ ⊥ →
        g⁻¹ * z * g ∈ P :=
  unique_involution_map_conj hzJ hz
    (eq_of_orderOf_eq_two_of_isSubnormal_quaternion_sylow hzJ hz hJ S hS) g

theorem mem_omegaAt_iff_of_quaternion_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    {A : Subgroup G} {a : G} :
    A ∈ omegaAt J z a ↔ A ∈ conjugateSet J ∧ a ∈ A ∧ orderOf a = 2 :=
  mem_omegaAt_iff_of_unique_involution hzJ hz
    (eq_of_orderOf_eq_two_of_isSubnormal_quaternion_sylow hzJ hz hJ S hS)

theorem tightlyEmbedded_iff_omegaAt_self_eq_of_quaternion_sylow (hzJ : z ∈ J)
    (hz : orderOf z = 2) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    classicalInvolutionTightlyEmbedded J ↔ omegaAt J z z = {J} :=
  tightlyEmbedded_iff_omegaAt_self_eq hzJ hz
    (eq_of_orderOf_eq_two_of_isSubnormal_quaternion_sylow hzJ hz hJ S hS)

theorem exists_involution_mem_iff_exists_mem_omegaAt_of_quaternion_sylow (hzJ : z ∈ J)
    (hz : orderOf z = 2) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    {A B : Subgroup G} (hA : A ∈ conjugateSet J) (hB : B ∈ conjugateSet J) :
    (∃ a : G, orderOf a = 2 ∧ a ∈ A ∧ a ∈ B) ↔ ∃ a : G, A ∈ omegaAt J z a ∧ B ∈ omegaAt J z a :=
  exists_involution_mem_iff_exists_mem_omegaAt hzJ hz
    (eq_of_orderOf_eq_two_of_isSubnormal_quaternion_sylow hzJ hz hJ S hS) hA hB

end Hypotheses

section Twins

open CFSG.ComponentClassification

variable {G : Type*} [Group G]

private theorem isSubnormal_subgroupOf_top {J X : Subgroup G} (h : IsSubnormal J X) :
    IsSubnormal (J.subgroupOf X) ⊤ := by
  have key : ∀ {H K : Subgroup G}, IsSubnormal H K →
      IsSubnormal (H.subgroupOf X) (K.subgroupOf X) := by
    intro H K h
    induction h with
    | refl => exact IsSubnormal.refl _
    | @step H M K hHM hN _ ih =>
      have hle : H.subgroupOf X ≤ M.subgroupOf X := fun x hx => hHM hx
      refine IsSubnormal.step hle ?_ ih
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro x y hx hy
      exact (Subgroup.normal_subgroupOf_iff hHM).mp hN x y hx hy
  simpa using key h

private theorem isQuasisimple_map_conj {J : Subgroup G} (hJ : IsQuasisimple J) (g : G) :
    IsQuasisimple (J.map (MulAut.conj g).toMonoidHom) :=
  Components.quasisimple_of_equiv
    (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm hJ

private theorem subgroupOf_ne_of_ne {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hne : A ≠ B) : A.subgroupOf X ≠ B.subgroupOf X := fun h => hne (by
  have := congrArg (Subgroup.map X.subtype) h
  simpa only [Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.map_subgroupOf_eq_of_le hBX] using
    this)

theorem commute_of_isSubnormal_of_isQuasisimple [Finite G] {X A B : Subgroup G}
    (hA : IsSubnormal A X) (hB : IsSubnormal B X) (hAq : IsQuasisimple A)
    (hBq : IsQuasisimple B) (hne : A ≠ B) : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  have hAX := isSubnormal_le hA
  have hBX := isSubnormal_le hB
  have hcomp : ∀ {C : Subgroup G}, C ≤ X → IsSubnormal C X → IsQuasisimple C →
      IsComponentOf (C.subgroupOf X) ⊤ := fun hCX hC hq =>
    ⟨le_top, isSubnormal_subgroupOf_top hC,
      Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hCX) hq⟩
  have hcomm := LocalComponents.commute_of_ne (A.subgroupOf X) (B.subgroupOf X)
    (hcomp hAX hA hAq) (hcomp hBX hB hBq) (subgroupOf_ne_of_ne hAX hBX hne)
  intro x hx y hy
  have hx' : (⟨x, hAX hx⟩ : X) ∈ A.subgroupOf X := hx
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx') (⟨y, hBX hy⟩ : X) hy
  exact (congrArg Subtype.val this).symm

theorem inf_le_center_of_commute {A B : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    A ⊓ B ≤ (Subgroup.center A).map A.subtype ⊓ (Subgroup.center B).map B.subtype := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  refine ⟨⟨⟨x, hxA⟩, Subgroup.mem_center_iff.mpr fun a => ?_, rfl⟩,
    ⟨⟨x, hxB⟩, Subgroup.mem_center_iff.mpr fun b => ?_, rfl⟩⟩
  · exact Subtype.ext (hcomm a a.2 x hxB)
  · exact Subtype.ext (hcomm x hxA b b.2).symm

variable {J : Subgroup G} {z : G}

private theorem isQuasisimple_of_mem_omegaAt (hq : IsQuasisimple J) {A : Subgroup G} {a : G}
    (hA : A ∈ omegaAt J z a) : IsQuasisimple A := by
  obtain ⟨g, rfl, -⟩ := hA
  exact isQuasisimple_map_conj hq g⁻¹

theorem commute_of_mem_omegaAt_of_isQuasisimple [Finite G]
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (hq : IsQuasisimple J)
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    ∀ x ∈ A, ∀ y ∈ B, x * y = y * x :=
  commute_of_isSubnormal_of_isQuasisimple (isSubnormal_of_mem_omegaAt hJ hA)
    (isSubnormal_of_mem_omegaAt hJ hB) (isQuasisimple_of_mem_omegaAt hq hA)
    (isQuasisimple_of_mem_omegaAt hq hB) hne

theorem twins_of_isQuasisimple [Finite G] (hzJ : z ∈ J)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (hq : IsQuasisimple J)
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    (∀ x ∈ A, ∀ y ∈ B, x * y = y * x) ∧ Subgroup.zpowers a ≤ A ⊓ B ∧
      A ⊓ B ≤ (Subgroup.center A).map A.subtype ⊓ (Subgroup.center B).map B.subtype := by
  have hcomm := commute_of_mem_omegaAt_of_isQuasisimple hJ hq hA hB hne
  exact ⟨hcomm, Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
    ⟨mem_of_mem_omegaAt hzJ hA, mem_of_mem_omegaAt hzJ hB⟩), inf_le_center_of_commute hcomm⟩

theorem twins_self_of_isQuasisimple [Finite G] (hzJ : z ∈ J)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (hq : IsQuasisimple J)
    {A : Subgroup G} (hA : A ∈ omegaAt J z z) (hne : A ≠ J) :
    (∀ x ∈ A, ∀ y ∈ J, x * y = y * x) ∧ Subgroup.zpowers z ≤ A ⊓ J ∧
      A ⊓ J ≤ (Subgroup.center J).map J.subtype := by
  obtain ⟨hcomm, hz, hcenter⟩ := twins_of_isQuasisimple hzJ hJ hq hA (self_mem_omegaAt J z) hne
  exact ⟨hcomm, hz, hcenter.trans inf_le_right⟩

theorem twins_inf [Finite G] (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) {A B : Subgroup G} {a : G}
    (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    a ∈ A ⊓ B ∧ 2 ∣ Nat.card (A ⊓ B : Subgroup G) ∧ A ⊓ B < A ∧ A ⊓ B < B ∧
      IsSubnormal (A ⊓ B) A ∧ IsSubnormal (A ⊓ B) B := by
  have hmem : a ∈ A ⊓ B :=
    Subgroup.mem_inf.mpr ⟨mem_of_mem_omegaAt hzJ hA, mem_of_mem_omegaAt hzJ hB⟩
  have ha2 : orderOf a = 2 := by
    obtain ⟨g, -, rfl⟩ := hA
    simpa [hz] using orderOf_conj_eq g⁻¹ z
  have hcard : Nat.card A = Nat.card B :=
    (natCard_of_mem_omegaAt hA).trans (natCard_of_mem_omegaAt hB).symm
  have hAC := le_centralizer_of_mem_omegaAt (isSubnormal_le hJ) hA
  have hBC := le_centralizer_of_mem_omegaAt (isSubnormal_le hJ) hB
  refine ⟨hmem, ?_, ?_, ?_, ?_, ?_⟩
  · have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [ha2] at this
  · refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hAB : A ≤ B := by
      rw [← h]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hAB hcard.ge
  · refine lt_of_le_of_ne inf_le_right fun h => hne ?_
    have hBA : B ≤ A := by
      rw [← h]
      exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hBA hcard.le).symm
  · have := isSubnormal_inf (isSubnormal_of_mem_omegaAt hJ hB) A
    rwa [inf_comm B A, inf_of_le_right hAC] at this
  · have := isSubnormal_inf (isSubnormal_of_mem_omegaAt hJ hA) B
    rwa [inf_of_le_right hBC] at this

end Twins

section TwoComponentTwins

open CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G]

theorem isTwoComponent_subgroupOf_map_iff {G' : Type*} [Group G'] [Finite G'] (φ : G ≃* G')
    (X A : Subgroup G) :
    TwoComponents.IsTwoComponent ((A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom)) ↔
      TwoComponents.IsTwoComponent (A.subgroupOf X) := by
  rw [← TwoComponentTransport.equiv_iff (φ.subgroupMap X) (A.subgroupOf X)]
  have hmap : (A.subgroupOf X).map (φ.subgroupMap X).toMonoidHom =
      (A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hxX⟩, hxA, hxy⟩
      exact ⟨x, hxA, congrArg Subtype.val hxy⟩
    · rintro ⟨a, haA, rfl⟩
      obtain ⟨x, hxX, hx⟩ := hy
      obtain rfl := φ.injective hx
      exact ⟨⟨x, hxX⟩, haA, rfl⟩
  rw [hmap]
  exact Iff.rfl

variable {J : Subgroup G} {z : G}

theorem isTwoComponent_of_mem_omegaAt
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) :
    TwoComponents.IsTwoComponent (A.subgroupOf (Subgroup.centralizer ({a} : Set G))) := by
  obtain ⟨g, rfl, rfl⟩ := hA
  have h := (isTwoComponent_subgroupOf_map_iff (MulAut.conj g⁻¹)
    (Subgroup.centralizer ({z} : Set G)) J).mpr hJ
  rwa [map_conj_centralizer_singleton, inv_inv] at h

omit [Finite G] in
private theorem map_oddCore_subgroupOf {X A : Subgroup G} (hAX : A ≤ X) :
    ((componentClassificationOddCore (A.subgroupOf X)).map (A.subgroupOf X).subtype).map
        X.subtype = (classicalInvolutionOddCore A).map A.subtype := by
  rw [show classicalInvolutionOddCore A = componentClassificationOddCore A from rfl,
    ← OddCore.equiv_invariant (Subgroup.subgroupOfEquivOfLe hAX), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem twoComponents_interaction {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hA : TwoComponents.IsTwoComponent (A.subgroupOf X))
    (hB : TwoComponents.IsTwoComponent (B.subgroupOf X)) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore X).map X.subtype := by
  obtain ⟨h1, h2, h3⟩ := TwoComponentInteraction.mutual_normalization_core_commutation _ _ hA hB
    (subgroupOf_ne_of_ne hAX hBX hne)
  have hmap : ⁅A, B⁆ = (⁅A.subgroupOf X, B.subgroupOf X⁆).map X.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAX,
      Subgroup.map_subgroupOf_eq_of_le hBX]
  have hcore : ((componentClassificationOddCore (A.subgroupOf X)).map
      (A.subgroupOf X).subtype).map X.subtype ≤ (classicalInvolutionOddCore X).map X.subtype := by
    refine Subgroup.map_mono ?_
    rw [OddCore.subnormal_intersection _ hA.1, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (Subgroup.map_mono (f := X.subtype) h1).trans
      (Subgroup.le_normalizer_map (H := A.subgroupOf X) X.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hBX, Subgroup.map_subgroupOf_eq_of_le hAX] at this
  · have := (Subgroup.map_mono (f := X.subtype) h2).trans
      (Subgroup.le_normalizer_map (H := B.subgroupOf X) X.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.map_subgroupOf_eq_of_le hBX] at this
  · rw [hmap, ← map_oddCore_subgroupOf hAX, ← map_oddCore_subgroupOf hBX]
    exact (Subgroup.map_mono h3).trans (Subgroup.map_inf_le _ _ _)
  · rw [hmap]
    exact (Subgroup.map_mono (h3.trans inf_le_left)).trans hcore

theorem twins_of_isTwoComponent (hJle : J ≤ Subgroup.centralizer ({z} : Set G))
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype :=
  twoComponents_interaction (le_centralizer_of_mem_omegaAt hJle hA)
    (le_centralizer_of_mem_omegaAt hJle hB) (isTwoComponent_of_mem_omegaAt hJ hA)
    (isTwoComponent_of_mem_omegaAt hJ hB) hne

theorem twins_self_of_isTwoComponent (hJle : J ≤ Subgroup.centralizer ({z} : Set G))
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A : Subgroup G} (hA : A ∈ omegaAt J z z) (hne : A ≠ J) :
    A ≤ Subgroup.normalizer (J : Set G) ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore J).map J.subtype ⊓
        (classicalInvolutionOddCore A).map A.subtype ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype :=
  twins_of_isTwoComponent hJle hJ (self_mem_omegaAt J z) hA hne.symm

theorem isTwoComponent_subgroupOf_of_perfect {J X : Subgroup G} (hJX : IsSubnormal J X)
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J)) :
    TwoComponents.IsTwoComponent (J.subgroupOf X) := by
  refine (TwoComponentTransport.subgroupOf_iff J X (isSubnormal_le hJX)).mpr ⟨?_, ?_, hq⟩
  · exact Components.mathlib_subnormal_of_chain (isSubnormal_subgroupOf_top hJX)
      Subgroup.IsSubnormal.top
  · have : Group.IsPerfect J := ⟨hperf⟩
    have : (TwoResidual.subgroup J).Characteristic := TwoResidual.characteristic J
    have hodd : Odd (Nat.card (J ⧸ TwoResidual.subgroup J)) := by
      rw [← Subgroup.index_eq_card]
      exact TwoResidual.odd_index J
    have : Group.IsSolvable (J ⧸ TwoResidual.subgroup J) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    by_contra hne
    have : Nontrivial (J ⧸ TwoResidual.subgroup J) :=
      not_subsingleton_iff_nontrivial.mp fun h => hne (QuotientGroup.subsingleton_iff.mp h)
    exact Group.IsPerfect.not_isSolvable (J ⧸ TwoResidual.subgroup J) inferInstance

theorem twins_of_perfect (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J))
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype :=
  twins_of_isTwoComponent (isSubnormal_le hJ) (isTwoComponent_subgroupOf_of_perfect hJ hperf hq)
    hA hB hne

theorem twins_self_of_perfect (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J))
    {A : Subgroup G} (hA : A ∈ omegaAt J z z) (hne : A ≠ J) :
    A ≤ Subgroup.normalizer (J : Set G) ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore J).map J.subtype ⊓
        (classicalInvolutionOddCore A).map A.subtype ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype :=
  twins_self_of_isTwoComponent (isSubnormal_le hJ)
    (isTwoComponent_subgroupOf_of_perfect hJ hperf hq) hA hne

end TwoComponentTwins

section Frames

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}

@[expose] def IsFrame (z : G) (J : Subgroup G) (s : Finset G) : Prop :=
  ∃ A : G → Subgroup G, (∀ a ∈ s, orderOf a = 2 ∧ A a ∈ omegaAt J z a) ∧
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ x ∈ A a, ∀ y ∈ A b, x * y = y * x

theorem isFrame_empty (z : G) (J : Subgroup G) : IsFrame z J ∅ :=
  ⟨fun _ => ⊥, fun a ha => (Finset.notMem_empty a ha).elim,
    fun a ha => (Finset.notMem_empty a ha).elim⟩

theorem IsFrame.mono {s t : Finset G} (h : IsFrame z J t) (hst : s ⊆ t) : IsFrame z J s := by
  obtain ⟨A, hA, hcomm⟩ := h
  exact ⟨A, fun a ha => hA a (hst ha), fun a ha b hb => hcomm a (hst ha) b (hst hb)⟩

theorem isFrame_singleton_iff {a : G} :
    IsFrame z J {a} ↔ orderOf a = 2 ∧ (omegaAt J z a).Nonempty := by
  constructor
  · rintro ⟨A, hA, -⟩
    obtain ⟨h2, hAa⟩ := hA a (Finset.mem_singleton_self a)
    exact ⟨h2, A a, hAa⟩
  · rintro ⟨h2, A₀, hA₀⟩
    refine ⟨fun _ => A₀, ?_, ?_⟩
    · intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact ⟨h2, hA₀⟩
    · intro b hb c hc hbc
      obtain rfl := Finset.mem_singleton.mp hb
      obtain rfl := Finset.mem_singleton.mp hc
      exact absurd rfl hbc

theorem isFrame_singleton_iff_isConj (hz : orderOf z = 2) {a : G} :
    IsFrame z J {a} ↔ IsConj z a := by
  rw [isFrame_singleton_iff, omegaAt_nonempty_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, orderOf_conj_eq, hz]

theorem IsFrame.orderOf_eq_two {s : Finset G} (h : IsFrame z J s) {a : G} (ha : a ∈ s) :
    orderOf a = 2 := by
  obtain ⟨A, hA, -⟩ := h
  exact (hA a ha).1

theorem IsFrame.commute {s : Finset G} (hzJ : z ∈ J) (h : IsFrame z J s) {a b : G} (ha : a ∈ s)
    (hb : b ∈ s) : a * b = b * a := by
  obtain ⟨A, hA, hcomm⟩ := h
  by_cases hab : a = b
  · rw [hab]
  · exact hcomm a ha b hb hab a (mem_of_mem_omegaAt hzJ (hA a ha).2) b
      (mem_of_mem_omegaAt hzJ (hA b hb).2)

theorem IsFrame.exists_tuple {s : Finset G} (h : IsFrame z J s) {n : ℕ} (hcard : s.card = n) :
    ∃ g : Fin n → G, (∀ i j, i ≠ j → ∀ x ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom,
        ∀ y ∈ J.map (MulAut.conj (g j)⁻¹).toMonoidHom, x * y = y * x) ∧
      Function.Injective fun i => (g i)⁻¹ * z * g i := by
  obtain ⟨A, hA, hcomm⟩ := h
  let e : s ≃ Fin n := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)
  have hmem : ∀ i : Fin n, ∃ g : G, A (e.symm i) = J.map (MulAut.conj g⁻¹).toMonoidHom ∧
      g⁻¹ * z * g = (e.symm i : G) := fun i => (hA _ (e.symm i).2).2
  choose g hg1 hg2 using hmem
  refine ⟨g, fun i j hij x hx y hy => ?_, fun i j hij => ?_⟩
  · rw [← hg1 i] at hx
    rw [← hg1 j] at hy
    refine hcomm (e.symm i) (e.symm i).2 (e.symm j) (e.symm j).2 ?_ x hx y hy
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  · apply e.symm.injective
    apply Subtype.ext
    rw [← hg2 i, ← hg2 j]
    exact hij

theorem exists_isFrame_of_tuple (hz : orderOf z = 2) {n : ℕ} {g : Fin n → G}
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom,
      ∀ y ∈ J.map (MulAut.conj (g j)⁻¹).toMonoidHom, x * y = y * x)
    (hinj : Function.Injective fun i => (g i)⁻¹ * z * g i) :
    ∃ s : Finset G, s.card = n ∧ IsFrame z J s := by
  classical
  let a : Fin n → G := fun i => (g i)⁻¹ * z * g i
  let A : G → Subgroup G := fun b =>
    if h : ∃ i, a i = b then J.map (MulAut.conj (g h.choose)⁻¹).toMonoidHom else ⊥
  have hAa : ∀ i, A (a i) = J.map (MulAut.conj (g i)⁻¹).toMonoidHom := by
    intro i
    have h : ∃ j, a j = a i := ⟨i, rfl⟩
    simp only [A, dite_eq_left h]
    rw [hinj h.choose_spec]
  refine ⟨Finset.univ.image a, ?_, A, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨by simpa [a, hz] using orderOf_conj_eq (g i)⁻¹ z, ?_⟩
    rw [hAa i]
    exact ⟨g i, rfl, rfl⟩
  · intro b hb c hc hbc x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hc
    rw [hAa i] at hx
    rw [hAa j] at hy
    exact hcomm i j (fun hij => hbc (by rw [hij])) x hx y hy

theorem exists_isFrame_card_eq_iff (hz : orderOf z = 2) (n : ℕ) :
    (∃ s : Finset G, s.card = n ∧ IsFrame z J s) ↔
      ∃ g : Fin n → G, (∀ i j, i ≠ j → ∀ x ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom,
          ∀ y ∈ J.map (MulAut.conj (g j)⁻¹).toMonoidHom, x * y = y * x) ∧
        Function.Injective fun i => (g i)⁻¹ * z * g i :=
  ⟨fun ⟨_, hcard, h⟩ => h.exists_tuple hcard,
    fun ⟨_, hcomm, hinj⟩ => exists_isFrame_of_tuple hz hcomm hinj⟩

theorem distinctCentralTriple_of_isFrame {s : Finset G} (hcard : s.card = 3)
    (h : IsFrame z J s) : DistinctCentralTriple z J :=
  h.exists_tuple hcard

theorem distinctCentralTriple_iff_exists_isFrame (hz : orderOf z = 2) :
    DistinctCentralTriple z J ↔ ∃ s : Finset G, s.card = 3 ∧ IsFrame z J s :=
  (exists_isFrame_card_eq_iff hz 3).symm

theorem IsFrame.exists_commutingAdj (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {s : Finset G} (h : IsFrame z J s) :
    ∃ A : G → Subgroup G, (∀ a ∈ s, A a ∈ omegaAt J z a) ∧
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → commutingAdj J (A a) (A b) := by
  obtain ⟨A, hA, hcomm⟩ := h
  refine ⟨A, fun a ha => (hA a ha).2, fun a ha b hb hab => ⟨?_, ?_, ?_, hcomm a ha b hb hab⟩⟩
  · exact omegaAt_subset_conjugateSet J z a (hA a ha).2
  · exact omegaAt_subset_conjugateSet J z b (hA b hb).2
  · intro hAB
    have hb' : A a ∈ omegaAt J z b := hAB ▸ (hA b hb).2
    exact hab (eq_of_mem_omegaAt_of_mem_omegaAt hzJ hz hU (hA a ha).2 hb')

end Frames

end CFSG.ClassicalInvolution
