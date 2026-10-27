module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup
open scoped commutatorElement

theorem isSubnormal_subgroupOf_centralizer_of_le {H : Type} [Group H] {L I : Subgroup H} {s : H}
    (hsL : s ∈ L)
    (hsub : (I.subgroupOf (Subgroup.centralizer ({s} : Set H))).IsSubnormal) :
    ((I.subgroupOf L).subgroupOf
      (Subgroup.centralizer ({(⟨s, hsL⟩ : ↥L)} : Set ↥L))).IsSubnormal := by
  have hmem : ∀ x : ↥(Subgroup.centralizer ({(⟨s, hsL⟩ : ↥L)} : Set ↥L)),
      ((x : ↥L) : H) ∈ Subgroup.centralizer ({s} : Set H) := fun x => by
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg Subtype.val hx)
  let g : ↥(Subgroup.centralizer ({(⟨s, hsL⟩ : ↥L)} : Set ↥L)) →*
      ↥(Subgroup.centralizer ({s} : Set H)) :=
    (L.subtype.comp (Subgroup.centralizer ({(⟨s, hsL⟩ : ↥L)} : Set ↥L)).subtype).codRestrict
      (Subgroup.centralizer ({s} : Set H)) hmem
  have h := hsub.comap g
  convert h using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rfl

theorem eq_top_of_isSubnormal_of_not_le_center {G : Type} [Group G] (hG : IsQuasisimple G)
    {A : Subgroup G} (hA : A.IsSubnormal) (hAZ : ¬ A ≤ center G) : A = ⊤ := by
  have hsimple : IsSimpleGroup (G ⧸ center G) := hG.2.1
  have hmap : (A.map (QuotientGroup.mk' (center G))).IsSubnormal :=
    hA.map (QuotientGroup.mk'_surjective _)
  have hnorm : (A.map (QuotientGroup.mk' (center G))).Normal :=
    hmap.normal_of_isSimpleGroup hsimple
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exfalso
    apply hAZ
    intro a ha
    have h1 : QuotientGroup.mk' (center G) a ∈ A.map (QuotientGroup.mk' (center G)) :=
      Subgroup.mem_map_of_mem _ ha
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  ·
    have hdec : ∀ g : G, ∃ a ∈ A, ∃ c ∈ center G, g = a * c := fun g => by
      have h1 : QuotientGroup.mk' (center G) g ∈ A.map (QuotientGroup.mk' (center G)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨a, ha, hag⟩ := h1
      refine ⟨a, ha, a⁻¹ * g, ?_, by group⟩
      exact QuotientGroup.eq.mp hag
    have hcomm : ∀ g h : G, ⁅g, h⁆ ∈ A := fun g h => by
      obtain ⟨a, ha, c, hc, rfl⟩ := hdec g
      obtain ⟨a', ha', c', hc', rfl⟩ := hdec h
      have h1 : ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ := by
        have hc1 := Subgroup.mem_center_iff.mp hc
        have hc2 := Subgroup.mem_center_iff.mp hc'
        simp only [commutatorElement_def, mul_inv_rev]
        have e1 : c * (a' * c') = (a' * c') * c := (hc1 _).symm
        calc a * c * (a' * c') * (c⁻¹ * a⁻¹) * (c'⁻¹ * a'⁻¹)
            = a * (c * (a' * c')) * (c⁻¹ * a⁻¹) * (c'⁻¹ * a'⁻¹) := by group
          _ = a * ((a' * c') * c) * (c⁻¹ * a⁻¹) * (c'⁻¹ * a'⁻¹) := by rw [e1]
          _ = a * a' * c' * a⁻¹ * (c'⁻¹ * a'⁻¹) := by group
          _ = a * a' * (c' * a⁻¹) * (c'⁻¹ * a'⁻¹) := by group
          _ = a * a' * (a⁻¹ * c') * (c'⁻¹ * a'⁻¹) := by rw [(hc2 a⁻¹).symm]
          _ = a * a' * a⁻¹ * a'⁻¹ := by group
      rw [h1, commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')
    have hperf : commutator G = ⊤ := hG.1.commutator_eq_top
    rw [eq_top_iff, ← hperf]
    exact (commutator_def G).symm ▸ Subgroup.commutator_le.mpr fun g _ h _ => hcomm g h

theorem eq_of_mem_center {H : Type} [Group H] {L I : Subgroup H} {s : H} (hsL : s ∈ L)
    (hL : IsQuasisimple ↥L) (hsc : (⟨s, hsL⟩ : ↥L) ∈ center ↥L) (hIL : I ≤ L)
    (hsub : (I.subgroupOf (Subgroup.centralizer ({s} : Set H))).IsSubnormal)
    (hnab : ¬ I.subgroupOf L ≤ center ↥L) : I = L := by
  have hLC : L ≤ Subgroup.centralizer ({s} : Set H) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp hsc ⟨x, hx⟩
    simpa using congrArg Subtype.val this
  have hsubL : (I.subgroupOf L).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion hLC)
    convert h using 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  have htop := eq_top_of_isSubnormal_of_not_le_center hL hsubL hnab
  exact le_antisymm hIL (Subgroup.subgroupOf_eq_top.mp htop)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
