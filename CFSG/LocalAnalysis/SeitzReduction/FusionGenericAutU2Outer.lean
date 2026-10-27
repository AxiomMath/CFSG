module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2FusionTwoCentral

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G]

theorem commutator_mem_of_isCyclic_range_outer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G))
    (hcyc : IsCyclic ((QuotientGroup.mk' (inner L)).comp
      (L.normalizerMonoidHom.comp (inclusion (hSt.trans hCN)))).range) :
    ∀ y ∈ S, ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ L := by
  have hLt : L ≤ centralizer ({t} : Set G) := SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  have hSN : S ≤ normalizer (L : Set G) := hSt.trans hCN
  set N : Subgroup S := L.subgroupOf S with hNdef
  have hNn : N.Normal := ⟨fun a ha b => by
    rw [hNdef, mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 (hSN b.2) _).1 ha⟩
  set φ : S →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp (L.normalizerMonoidHom.comp (inclusion hSN)) with hφ
  have hφ1 : ∀ a : S, φ a = 1 → ∃ l : L, ∀ y ∈ L, (a : G) * y * (a : G)⁻¹ = l * y * (l : G)⁻¹ := by
    intro a ha
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    obtain ⟨l, hl⟩ := ha
    refine ⟨l, fun y hy => ?_⟩
    have h3 := congrArg (fun β : MulAut L => ((β ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [h3]
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hNφ : N ≤ φ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨⟨a, mem_subgroupOf.1 ha⟩, ?_⟩
    ext y
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe, coe_inclusion]
  set f : S ⧸ N →* Outer L := QuotientGroup.lift N φ hNφ with hf
  have hrange : f.range = φ.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨a, by rw [hf, QuotientGroup.lift_mk]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : S ⧸ N), by rw [hf, QuotientGroup.lift_mk]⟩
  have : IsCyclic f.range := by rw [hrange]; exact hcyc
  have hker : f.rangeRestrict.ker ≤ center (S ⧸ N) := by
    intro q hq
    rw [MonoidHom.ker_rangeRestrict] at hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hf, QuotientGroup.lift_mk] at hq
    obtain ⟨l, hl⟩ := hφ1 a hq
    have hat : (a : G) ∈ centralizer ({t} : Set G) := hSt a.2
    rw [mem_center_iff]
    intro q'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNdef, mem_subgroupOf]
    have hbt : (b : G) * t = t * b := mem_centralizer_singleton_iff.1 (hSt b.2)
    set c : G := (l : G)⁻¹ * (b : G)⁻¹ * l * b with hcdef
    have hcL : c ∈ L := by
      have h1 : (b : G)⁻¹ * l * b ∈ L := (mem_normalizer_iff''.1 (hSN b.2) _).1 l.2
      have e : c = (l : G)⁻¹ * ((b : G)⁻¹ * l * b) := by rw [hcdef]; group
      rw [e]
      exact mul_mem (inv_mem l.2) h1
    have hct : c * t = t * c := mem_centralizer_singleton_iff.1 (hLt hcL)
    rcases F4Pilot.eq_or_eq_mul_of_conj_eq htC ht hK hat l.2 hl with h | h
    · have e : (((b * a)⁻¹ * (a * b) : S) : G) = c := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h, hcdef]
        group
      rw [e]
      exact hcL
    · have e : (((b * a)⁻¹ * (a * b) : S) : G) = t⁻¹ * (c * t) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h]
        calc ((b : G) * (l * t))⁻¹ * (l * t * b) = ((b : G) * (l * t))⁻¹ * (l * (t * b)) := by
              group
          _ = ((b : G) * (l * t))⁻¹ * (l * (b * t)) := by rw [← hbt]
          _ = t⁻¹ * (c * t) := by rw [hcdef]; group
      rw [e, hct, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hcL
  have hcomm := f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker
  intro y hy z hz
  have h := hcomm.is_comm.comm ((⟨y, hy⟩ : S) : S ⧸ N) ((⟨z, hz⟩ : S) : S ⧸ N)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h' := mem_subgroupOf.1 h
  have e : (((⟨y, hy⟩ : S) * ⟨z, hz⟩)⁻¹ * (⟨z, hz⟩ * ⟨y, hy⟩) : S) = (z⁻¹ * y⁻¹ * z * y : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
  rw [e] at h'
  have e2 : y * z * y⁻¹ * z⁻¹ = (y * z) * (z⁻¹ * y⁻¹ * z * y)⁻¹ * (y * z)⁻¹ := by group
  rw [e2]
  exact (mem_normalizer_iff.1 (hSN (mul_mem hy hz)) _).1 (inv_mem h')

theorem commutator_mem_of_isPGroup_of_isCyclic_outer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcyc : ∀ B : Subgroup (MulAut L), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner L))))
    {S : Subgroup G} (hS : IsPGroup 2 S) (hSt : S ≤ centralizer ({t} : Set G)) :
    ∀ y ∈ S, ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ L := by
  set ψ : S →* MulAut L := L.normalizerMonoidHom.comp (inclusion (hSt.trans hCN)) with hψ
  have hB : IsPGroup 2 ψ.range := hS.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  refine commutator_mem_of_isCyclic_range_outer htC ht hCN hK hSt ?_
  rw [MonoidHom.range_comp]
  exact hcyc _ hB

theorem commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer_two [Finite G] {L : Subgroup G}
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcyc : ∀ B : Subgroup (MulAut L), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner L)))) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L :=
  fun S hSt => commutator_mem_of_isPGroup_of_isCyclic_outer htC ht hCN hK hcyc S.isPGroup' hSt

end CFSG.SeitzReduction
