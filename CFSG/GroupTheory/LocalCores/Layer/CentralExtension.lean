module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalCores

open Subgroup

variable {P Q : Type*} [Group P] [Group Q]

theorem comap_center_eq_of_perfect (hP : Group.IsPerfect P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) :
    (center Q).comap f = center P := by
  apply le_antisymm
  · have h1 : ⁅(⊤ : Subgroup P), (center Q).comap f⁆ ≤ center P := by
      refine (commutator_le.mpr fun g _ b hb => ?_).trans hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.mp hb (f g)
    have h2 : ⁅⁅(⊤ : Subgroup P), (center Q).comap f⁆, ⊤⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono h1 le_rfl).trans (commutator_center_left _).le)
    exact commutator_top_left_eq_bot_iff_le_center.mp
      (perfect_double_commutator (Group.IsPerfect.top_iff.mpr hP) h2)
  · intro z hz
    rw [mem_comap, mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := hf q
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz g]

theorem isQuasisimple_iff_of_surjective (hP : Group.IsPerfect P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) :
    IsQuasisimple P ↔ IsQuasisimple Q := by
  have hQ : Group.IsPerfect Q := by have := hP; exact Group.IsPerfect.ofSurjective hf
  have hc : center P = ((QuotientGroup.mk' (center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_center_eq_of_perfect hP f hf hker]
  let e : P ⧸ center P ≃* Q ⧸ center Q := (QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))
  constructor
  · rintro ⟨-, hs, a, b, hab⟩
    refine ⟨hQ, e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  · rintro ⟨-, hs, a, b, hab⟩
    refine ⟨hP, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]

theorem isQuasisimple_of_surjective (hP : IsQuasisimple P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) : IsQuasisimple Q :=
  (isQuasisimple_iff_of_surjective hP.1 f hf hker).mp hP

theorem quasisimple_central_quotient (hQ : IsQuasisimple Q) (A : Subgroup Q) [A.Normal]
    (hA : A ≤ center Q) :
    IsQuasisimple (Q ⧸ A) ∧ (center (Q ⧸ A)).comap (QuotientGroup.mk' A) = center Q ∧
      center (Q ⧸ A) = (center Q).map (QuotientGroup.mk' A) := by
  have hker : (QuotientGroup.mk' A).ker ≤ center Q := by rwa [QuotientGroup.ker_mk']
  have hcomap := comap_center_eq_of_perfect hQ.1 _ (QuotientGroup.mk'_surjective A) hker
  refine ⟨isQuasisimple_of_surjective hQ _ (QuotientGroup.mk'_surjective A) hker, hcomap, ?_⟩
  rw [← hcomap, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)]

theorem central_extension_derived_of_surjective {H : Type*} [Group H] (f : H →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center H) (hQ : Group.IsPerfect Q) :
    commutator H ⊔ f.ker = ⊤ ∧ Group.IsPerfect (commutator H) ∧
      Function.Surjective (f.comp (commutator H).subtype) := by
  have hmap : (commutator H).map f = ⊤ := by
    rw [commutator_def, map_commutator, map_top_of_surjective f hf, ← commutator_def,
      hQ.commutator_eq_top]
  have hsup : commutator H ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hmap, comap_top]
  refine ⟨hsup, ?_, fun q => ?_⟩
  ·
    have hK : ∀ N : Subgroup H, ⁅f.ker, N⁆ = ⊥ := fun N =>
      le_bot_iff.mp ((commutator_mono hker le_rfl).trans (commutator_center_left N).le)
    rw [isPerfect_iff]
    calc ⁅commutator H, commutator H⁆
        = ⁅commutator H, commutator H ⊔ f.ker⁆ := by
          rw [commutator_sup_left, commutator_comm (commutator H) f.ker, hK, sup_bot_eq]
      _ = ⁅commutator H ⊔ f.ker, commutator H ⊔ f.ker⁆ := by
          rw [commutator_sup_right (commutator H) f.ker, hK, sup_bot_eq]
      _ = commutator H := by rw [hsup, ← commutator_def]
  · obtain ⟨h, hh, hq⟩ := mem_map.mp (hmap ▸ mem_top q : q ∈ (commutator H).map f)
    exact ⟨⟨h, hh⟩, hq⟩

theorem central_extension_derived {H : Type*} [Group H] (A : Subgroup H) [A.Normal]
    (hA : A ≤ center H) (hHA : Group.IsPerfect (H ⧸ A)) :
    commutator H ⊔ A = ⊤ ∧ Group.IsPerfect (commutator H) ∧
      Function.Surjective ((QuotientGroup.mk' A).comp (commutator H).subtype) := by
  have h := central_extension_derived_of_surjective (QuotientGroup.mk' A)
    (QuotientGroup.mk'_surjective A) (by rwa [QuotientGroup.ker_mk']) hHA
  rwa [QuotientGroup.ker_mk'] at h

theorem quasisimple_central_extension_derived_of_surjective {H : Type*} [Group H] (f : H →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center H) (hQ : IsQuasisimple Q) :
    IsQuasisimple (commutator H) := by
  obtain ⟨-, hP, hsurj⟩ := central_extension_derived_of_surjective f hf hker hQ.1
  refine (isQuasisimple_iff_of_surjective hP _ hsurj fun x hx => ?_).mpr hQ
  have hxc : (x : H) ∈ center H := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hxc y)

theorem quasisimple_central_extension_derived {H : Type*} [Group H] (A : Subgroup H) [A.Normal]
    (hA : A ≤ center H) (hHA : IsQuasisimple (H ⧸ A)) : IsQuasisimple (commutator H) :=
  quasisimple_central_extension_derived_of_surjective (QuotientGroup.mk' A)
    (QuotientGroup.mk'_surjective A) (by rwa [QuotientGroup.ker_mk']) hHA

theorem isQuasisimple_of_isSimpleGroup [IsSimpleGroup Q] (hQ : ∃ a b : Q, a * b ≠ b * a) :
    IsQuasisimple Q ∧ center Q = ⊥ := by
  obtain ⟨a, b, hab⟩ := hQ
  have hZ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab
  have hP : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · refine absurd ?_ hab
      rw [← commutatorElement_eq_one_iff_mul_comm, ← mem_bot, ← h, commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    · exact h
  let e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hP, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩, hZ⟩
  rw [map_mul, map_mul, h]

theorem isQuasisimple_map {K : Subgroup P} (hK : IsQuasisimple K) (f : P →* Q)
    (hKf : ¬ K ≤ f.ker) : IsQuasisimple (K.map f) := by
  refine isQuasisimple_of_surjective hK (f.subgroupMap K) (f.subgroupMap_surjective K) ?_
  rcases quasisimple_normal_subgroups hK (f.subgroupMap K).normal_ker with h | h
  · refine absurd (fun x hx => ?_) hKf
    have hx' : (⟨x, hx⟩ : K) ∈ (f.subgroupMap K).ker := by rw [h]; exact mem_top _
    rw [MonoidHom.mem_ker] at hx' ⊢
    exact congrArg Subtype.val hx'
  · exact h

end CFSG.LocalCores
