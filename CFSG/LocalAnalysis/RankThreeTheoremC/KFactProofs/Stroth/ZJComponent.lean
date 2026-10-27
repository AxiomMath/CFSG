module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG Subgroup
open scoped commutatorElement

section Quasisimple

variable {K H₁ H₂ : Type*} [Group K] [Group H₁] [Group H₂]

theorem zj_mem_center_of_commutator_mem_center [Group.IsPerfect K] {g : K}
    (h : ∀ y, ⁅g, y⁆ ∈ Subgroup.center K) : g ∈ Subgroup.center K := by
  have h2 : g ∈ Subgroup.upperCentralSeries K 2 := by
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact h y
  rwa [Group.IsPerfect.upperCentralSeries_eq_center K (by norm_num)] at h2

theorem zj_quasisimple_of_central_kernel (hK : Group.IsPerfect K) {f₁ : K →* H₁} {f₂ : K →* H₂}
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂) (hq : CFSG.IsQuasisimple H₁)
    (hker : ∀ r ∈ f₁.ker, ∀ y : K, ⁅r, y⁆ ∈ f₂.ker) (hnt : f₂.ker ≠ ⊤) :
    CFSG.IsQuasisimple H₂ ∧
      Nonempty ((H₁ ⧸ Subgroup.center H₁) ≃* (H₂ ⧸ Subgroup.center H₂)) := by
  haveI : Group.IsPerfect K := hK
  haveI hperf : Group.IsPerfect H₂ := Group.IsPerfect.ofSurjective (f := f₂) hf₂
  have hnt2 : Nontrivial H₂ := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    apply hnt
    rw [eq_top_iff]
    intro k _
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hnonab : ∃ a b : H₂, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    haveI : IsMulCommutative H₂ := isMulCommutative_iff.2 hall
    haveI := Group.IsPerfect.subsingleton_of_isMulCommutative (G := H₂)
    exact (not_subsingleton H₂) ‹_›
  have hcen : ∀ r ∈ f₁.ker, f₂ r ∈ Subgroup.center H₂ := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hf₂ z
    have h1 := hker r hr y
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  let h : K →* H₁ ⧸ Subgroup.center H₁ := (QuotientGroup.mk' (Subgroup.center H₁)).comp f₁
  let g : K →* H₂ ⧸ Subgroup.center H₂ := (QuotientGroup.mk' (Subgroup.center H₂)).comp f₂
  have hh : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hf₁
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf₂
  have hle : h.ker ≤ g.ker := by
    intro k hk
    have hk1 : f₁ k ∈ Subgroup.center H₁ :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hk)
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk (f₂ k) = 1
    rw [QuotientGroup.eq_one_iff]
    refine zj_mem_center_of_commutator_mem_center fun y' => ?_
    obtain ⟨y, rfl⟩ := hf₂ y'
    have hky : ⁅k, y⁆ ∈ f₁.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hk1 (f₁ y)).symm
    have := hcen _ hky
    rwa [map_commutatorElement] at this
  let g' : (H₁ ⧸ Subgroup.center H₁) →* (H₂ ⧸ Subgroup.center H₂) :=
    MonoidHom.liftOfSurjective h hh ⟨g, hle⟩
  have hg' : ∀ k, g' (h k) = g k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply h (Function.surjInv hh)
      (Function.rightInverse_surjInv hh) ⟨g, hle⟩ k
  have hT1 : IsSimpleGroup (H₁ ⧸ Subgroup.center H₁) := hq.2.1
  have hsurj : Function.Surjective g' := by
    intro t
    obtain ⟨k, rfl⟩ := hg t
    exact ⟨h k, hg' k⟩
  have hnt3 : Nontrivial (H₂ ⧸ Subgroup.center H₂) := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨⟨QuotientGroup.mk a, 1, fun h1 => hab ?_⟩⟩
    have ha : a ∈ Subgroup.center H₂ := (QuotientGroup.eq_one_iff a).mp h1
    exact (Subgroup.mem_center_iff.mp ha b).symm
  have hinj : Function.Injective g' := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hT1.eq_bot_or_eq_top_of_normal g'.ker with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨t, ht⟩ := exists_ne (1 : H₂ ⧸ Subgroup.center H₂)
      obtain ⟨s, rfl⟩ := hsurj t
      apply ht
      exact MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top s)
  let e : (H₁ ⧸ Subgroup.center H₁) ≃* (H₂ ⧸ Subgroup.center H₂) :=
    MulEquiv.ofBijective g' ⟨hinj, hsurj⟩
  refine ⟨⟨hperf, ?_, ?_⟩, ⟨e⟩⟩
  · haveI := hT1
    exact e.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e a, e b, fun h2 => hab (e.injective (by simpa using h2))⟩

end Quasisimple

section Image

variable {X : Type} [Group X] [Finite X]

theorem zj_pPrimeCore_eq_subgroupOf {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal] :
    CFSG.pPrimeCore p ↥K = (CFSG.pPrimeCore p X).subgroupOf K := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ p} (Subgroup.Normal.isSubnormal ‹K.Normal›)
  rw [← CFSG.pPrimeCore_eq_piCore ↥K p, ← CFSG.pPrimeCore_eq_piCore X p] at h
  apply Subgroup.map_injective K.subtype_injective
  rw [h, Subgroup.subgroupOf_map_subtype]
  exact inf_comm _ _

theorem zj_mem_ker_subgroupMap {N K : Subgroup X} [N.Normal] (k : K) :
    k ∈ ((QuotientGroup.mk' N).subgroupMap K).ker ↔ (k : X) ∈ N := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff (k : X)

theorem zj_component_image {p : ℕ} [Fact p.Prime] {K C : Subgroup X} [K.Normal] [C.Normal]
    (hK : CFSG.IsPComponent p K) (hKC : ¬ K ≤ C)
    (hcent : ∀ r ∈ K ⊓ CFSG.pPrimeCore p X, ∀ y ∈ K, ⁅r, y⁆ ∈ C) :
    CFSG.IsQuasisimple ↥(K.map (QuotientGroup.mk' C)) ∧
      Nonempty (((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pPrimeCore p ↥K)) ≃*
        (↥(K.map (QuotientGroup.mk' C)) ⧸ Subgroup.center ↥(K.map (QuotientGroup.mk' C)))) := by
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (zj_pComponent_perfect hK)
  obtain ⟨K₀, hK₀, -, hmap, -⟩ := hK
  subst hmap
  set f₁ : ↥K →* ↥(K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p X)).subgroupMap K with hf₁
  have hf₁s : Function.Surjective f₁ := MonoidHom.subgroupMap_surjective _ _
  have hf₁nt : f₁.ker ≠ ⊤ := by
    intro htop
    haveI := zj_quasisimple_nontrivial hK₀.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))))
    obtain ⟨k, rfl⟩ := hf₁s x
    apply hx
    exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top k)
  have hRK : CFSG.pPrimeCore p ↥K = f₁.ker := by
    ext x
    rw [zj_pPrimeCore_eq_subgroupOf, Subgroup.mem_subgroupOf, hf₁, zj_mem_ker_subgroupMap]
  have h1 := zj_quasisimple_of_central_kernel (f₁ := f₁)
    (f₂ := QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)) hperfK hf₁s (QuotientGroup.mk'_surjective _)
    hK₀.1 (fun r hr y => by
      rw [QuotientGroup.ker_mk', hRK]
      refine Subgroup.commutator_le_left f₁.ker ⊤ ?_
      exact Subgroup.commutator_mem_commutator hr (Subgroup.mem_top y))
    (by rw [QuotientGroup.ker_mk', hRK]; exact hf₁nt)
  set f₂ : ↥K →* ↥(K.map (QuotientGroup.mk' C)) := (QuotientGroup.mk' C).subgroupMap K with hf₂
  have hf₂s : Function.Surjective f₂ := MonoidHom.subgroupMap_surjective _ _
  have h2 := zj_quasisimple_of_central_kernel (f₁ := f₁) (f₂ := f₂) hperfK hf₁s hf₂s hK₀.1
    (fun r hr y => by
      have hrO : (r : X) ∈ CFSG.pPrimeCore p X := (zj_mem_ker_subgroupMap r).mp hr
      rw [hf₂, zj_mem_ker_subgroupMap]
      exact hcent r ⟨r.2, hrO⟩ y y.2)
    (by
      intro htop
      apply hKC
      intro k hk
      have hmem : (⟨k, hk⟩ : ↥K) ∈ f₂.ker := htop ▸ Subgroup.mem_top _
      exact (zj_mem_ker_subgroupMap (N := C) (K := K) ⟨k, hk⟩).mp hmem)
  obtain ⟨-, ⟨e₁⟩⟩ := h1
  obtain ⟨hq2, ⟨e₂⟩⟩ := h2
  exact ⟨hq2, ⟨e₁.symm.trans e₂⟩⟩

end Image

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
