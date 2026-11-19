
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] {J P : Subgroup G}

theorem exists_conj_sylow_image
    [Finite G] (hP : IsSylowTwoIn P J) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) :
    ∃ g ∈ S, ∀ y : Equiv.Perm (Fin 42),
      (y ∈ S ∧ ∃ p ∈ P, ∃ hp : p ∈ J, q (jq J ⟨p, hp⟩) = y) ↔ g⁻¹ * y * g ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hP
  set φ : ↥J →* ↥S := (q.comp (jq J)).codRestrict S (fun j => hqS _) with hφ
  have hφs : Function.Surjective φ := by
    intro s
    obtain ⟨e, he⟩ := hqsurj s s.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, Subtype.ext he⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0 (T.mapSurjective hφs)
  refine ⟨g, g.2, fun y => ⟨?_, fun hy => ?_⟩⟩
  · rintro ⟨hyS, p, hpP, hpJ, rfl⟩
    have h1 : (⟨q (jq J ⟨p, hpJ⟩), hyS⟩ : S) ∈ ((g • sylowT0 : Sylow 2 S) : Subgroup S) := by
      rw [hg, Sylow.coe_mapSurjective]
      refine ⟨⟨p, hpJ⟩, ?_, rfl⟩
      rw [hT]
      exact mem_subgroupOf.mpr hpP
    exact (mem_smul_sylowT0_iff g _).1 h1
  · have hyS : y ∈ S := by
      have h1 := S.mul_mem (S.mul_mem g.2 (T0_le_S hy)) (S.inv_mem g.2)
      rwa [show (g : Equiv.Perm (Fin 42)) * ((g : Equiv.Perm (Fin 42))⁻¹ * y * g) *
        (g : Equiv.Perm (Fin 42))⁻¹ = y by group] at h1
    have h1 := (mem_smul_sylowT0_iff g ⟨y, hyS⟩).2 hy
    rw [hg, Sylow.coe_mapSurjective] at h1
    obtain ⟨j, hjT, hj⟩ := h1
    rw [hT] at hjT
    exact ⟨hyS, j, mem_subgroupOf.mp hjT, j.2, congrArg Subtype.val hj⟩

def pullP (J P : Subgroup G) (hPJ : P ≤ J) (H : Subgroup (Jhat J)) : Subgroup G :=
  (H.comap ((jq J).comp (Subgroup.inclusion hPJ))).map P.subtype

variable {hPJ : P ≤ J}

theorem mem_pullP {H : Subgroup (Jhat J)} {g : G} :
    g ∈ pullP J P hPJ H ↔ ∃ hg : g ∈ P, jq J ⟨g, hPJ hg⟩ ∈ H := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem pullP_le (H : Subgroup (Jhat J)) : pullP J P hPJ H ≤ P := fun _ hg =>
  (mem_pullP.1 hg).1

theorem pullP_mono {H H' : Subgroup (Jhat J)} (h : H ≤ H') :
    pullP J P hPJ H ≤ pullP J P hPJ H' := fun _ hg => by
  obtain ⟨hgP, hgH⟩ := mem_pullP.1 hg
  exact mem_pullP.2 ⟨hgP, h hgH⟩

variable {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem exists_mem_pullP (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {H : Subgroup (Jhat J)} (hH : H ≤ T0.comap q) {e : Jhat J} (he : e ∈ H) :
    ∃ p ∈ pullP J P hPJ H, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e := by
  obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 (hH he)
  exact ⟨p, mem_pullP.2 ⟨hpP, he⟩, hpJ, rfl⟩

theorem card_pullP [Finite G] (hP2 : IsPGroup 2 P)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) {H : Subgroup (Jhat J)}
    (hH : H ≤ T0.comap q) : Nat.card (pullP J P hPJ H) = Nat.card H := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨jq J ⟨g, hPJ (mem_pullP.1 g.2).1⟩, (mem_pullP.1 g.2).2⟩) ⟨fun a b hab => ?_, ?_⟩)
  · have h1 := congrArg Subtype.val hab
    exact Subtype.ext (eq_of_jq_eq hPJ hP2 (mem_pullP.1 a.2).1 (mem_pullP.1 b.2).1 h1)
  · rintro ⟨e, he⟩
    obtain ⟨p, hp, -, rfl⟩ := exists_mem_pullP (hPJ := hPJ) hT hH he
    exact ⟨⟨p, hp⟩, rfl⟩

theorem isElemTwo_pullP [Finite G] (hP2 : IsPGroup 2 P) {H : Subgroup (Jhat J)} (hH : IsElemTwo H) :
    IsElemTwo (pullP J P hPJ H) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨haP, haH⟩ := mem_pullP.1 ha
    obtain ⟨hbP, hbH⟩ := mem_pullP.1 hb
    apply eq_of_jq_eq hPJ hP2 (P.mul_mem haP hbP) (P.mul_mem hbP haP)
    show jq J (⟨a, hPJ haP⟩ * ⟨b, hPJ hbP⟩) = jq J (⟨b, hPJ hbP⟩ * ⟨a, hPJ haP⟩)
    rw [map_mul, map_mul]
    exact hH.1 _ haH _ hbH
  · obtain ⟨haP, haH⟩ := mem_pullP.1 ha
    apply eq_one_of_jq_eq_one hPJ hP2 (P.mul_mem haP haP)
    show jq J (⟨a, hPJ haP⟩ * ⟨a, hPJ haP⟩) = 1
    rw [map_mul]
    exact hH.2 _ haH

theorem le_of_pullP_le (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {H H' : Subgroup (Jhat J)} (hH : H ≤ T0.comap q)
    (hle : pullP J P hPJ H ≤ pullP J P hPJ H') : H ≤ H' := by
  intro e he
  obtain ⟨p, hp, hpJ, rfl⟩ := exists_mem_pullP (hPJ := hPJ) hT hH he
  exact (mem_pullP.1 (hle hp)).2

end CFSG.ComponentClassification.GrSLit.L34Facts
