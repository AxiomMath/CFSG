module

public import CFSG.ClassicalInvolution.SmallCases.Alternating.OddCore
public import CFSG.ClassicalInvolution.SmallCases.Alternating.PairSwaps
import CFSG.ClassicalInvolution.SubnormalClosure.Reduction

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open Equiv

theorem alternating_no_classical (n : ℕ) (z : alternatingGroup (Fin n)) (hz : orderOf z = 2)
    (K : Subgroup (alternatingGroup (Fin n))) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) : False := by
  have hq := isQuasisimple_oddCoreQuotient_of_witness hw hns
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzP : (z : Perm (Fin n)) * z = 1 := by simpa using congrArg Subtype.val hzz
  have hKC : K ≤ Subgroup.centralizer {z} := isSubnormal_le hK
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin n, (z : Perm (Fin n)) a ≠ a := by
    by_contra h
    push Not at h
    have : z = 1 := Subtype.ext (Perm.ext h)
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  let U : Subgroup (alternatingGroup (Fin n)) :=
    (pairSwaps (z : Perm (Fin n)) hzP).subgroupOf (alternatingGroup (Fin n))
  have hUC : U ≤ Subgroup.centralizer {z} := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subtype.ext (Perm.ext fun a => (pairSwaps_apply_z (hz := hzP) hu a).symm)
  have hconj : ∀ c ∈ Subgroup.centralizer ({z} : Set (alternatingGroup (Fin n))), ∀ u ∈ U,
      c * u * c⁻¹ ∈ U := by
    intro c hc u hu
    have hcz : (c : Perm (Fin n)) * z = z * c := by
      have := Subgroup.mem_centralizer_iff.mp hc z (Set.mem_singleton z)
      simpa using (congrArg Subtype.val this).symm
    exact conj_mem_pairSwaps (hz := hzP) hu hcz
  have hCU : Subgroup.centralizer {z} ≤
      Subgroup.normalizer (U : Set (alternatingGroup (Fin n))) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hconj c hc h hh
    · intro hh
      have := hconj c⁻¹ (Subgroup.inv_mem _ hc) _ hh
      simpa [mul_assoc] using this
  have hUp : IsPGroup 2 U := by
    intro u
    refine ⟨1, ?_⟩
    have hu' : ((u : alternatingGroup (Fin n)) : Perm (Fin n)) ∈
        pairSwaps (z : Perm (Fin n)) hzP := u.2
    have := pairSwaps_mul_self (hz := hzP) hu'
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using this
  have hkz : ∀ k ∈ K, ∀ a, (k : Perm (Fin n)) ((z : Perm (Fin n)) a) =
      (z : Perm (Fin n)) ((k : Perm (Fin n)) a) := by
    intro k hk a
    have := Subgroup.mem_centralizer_iff.mp (hKC hk) z (Set.mem_singleton z)
    simpa using congrArg (fun p : alternatingGroup (Fin n) => (p : Perm (Fin n)) a) this.symm
  have key : ∀ g : alternatingGroup (Fin n), g ∈ K → Odd (orderOf g) →
      ∀ a : Fin n, (z : Perm (Fin n)) a ≠ a → (g : Perm (Fin n)) a = a := by
    intro g hgK hg a ha
    by_contra hga
    have hgz : (g : Perm (Fin n)) * z = z * g := Perm.ext (hkz g hgK)
    have hg' : Odd (orderOf (g : Perm (Fin n))) := by rwa [Subgroup.orderOf_coe]
    obtain ⟨u, hu, hsign, hne⟩ :=
      exists_mem_pairSwaps_not_commute (hz := hzP) (g : Perm (Fin n)) hgz hg' ha hga
    have huG : u ∈ alternatingGroup (Fin n) := hsign
    have hcomm := commute_of_odd_orderOf_of_isSubnormal hK hUC hCU hUp hq hgK hg ⟨u, huG⟩ hu
    exact hne (congrArg Subtype.val hcomm)
  let Fix : Subgroup (alternatingGroup (Fin n)) :=
    (fixingSubgroup (Perm (Fin n)) {a : Fin n | (z : Perm (Fin n)) a ≠ a}).comap
      (alternatingGroup (Fin n)).subtype
  have hFix : ∀ g : alternatingGroup (Fin n),
      g ∈ Fix ↔ ∀ a : Fin n, (z : Perm (Fin n)) a ≠ a → (g : Perm (Fin n)) a = a := by
    intro g
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    exact Iff.rfl
  have hAn : (Fix.subgroupOf K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf, hFix] at hx ⊢
    intro a ha
    have hza : (z : Perm (Fin n)) ((k : Perm (Fin n))⁻¹ a) ≠ (k : Perm (Fin n))⁻¹ a := by
      intro h
      apply ha
      have h2 := congrArg (k : Perm (Fin n)) h
      rw [hkz _ k.2] at h2
      simpa using h2
    change (k : Perm (Fin n)) ((x : Perm (Fin n)) ((k : Perm (Fin n))⁻¹ a)) = a
    rw [hx _ hza]
    simp
  have hA : ∀ x : K, Odd (orderOf x) → x ∈ Fix.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, hFix]
    exact key x x.2 (by rwa [Subgroup.orderOf_coe])
  have htop := eq_top_of_forall_odd_orderOf_mem hq.1 (Fix.subgroupOf K) hA
  have hzA : (⟨z, hzK⟩ : K) ∈ Fix.subgroupOf K := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf, hFix] at hzA
  exact ha₀ (hzA a₀ ha₀)

theorem no_classical_of_mulEquiv_alternating {F : Type*} [Group F] {n : ℕ}
    (e : F ≃* alternatingGroup (Fin n)) (z : F) (hz : orderOf z = 2) (K : Subgroup F)
    (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer {z}))
    (hw : classicalInvolutionWitness K) (hns : ¬ Group.IsSolvable K) : False := by
  have hC : (Subgroup.centralizer ({z} : Set F)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set (alternatingGroup (Fin n))) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := Subgroup.mem_centralizer_iff.mp hy z (Set.mem_singleton z)
      simpa using congrArg e this
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := hx (e h) (Set.mem_singleton _)
      apply e.injective
      simpa using this
  refine alternating_no_classical n (e z) (by rwa [MulEquiv.orderOf_eq]) (K.map e.toMonoidHom)
    ⟨z, hzK, rfl⟩ ?_ ?_ ?_
  · rw [← hC]
    exact isSubnormal_map_mulEquiv e hK
  · exact classicalInvolutionWitness_of_mulEquiv (e.subgroupMap K) hw
  · intro hs
    have : Group.IsSolvable (K.map (e : F →* alternatingGroup (Fin n))) := hs
    exact hns (Group.isSolvable_of_surjective (f := (e.subgroupMap K).symm.toMonoidHom)
      (e.subgroupMap K).symm.surjective)

end CFSG.ClassicalInvolution
