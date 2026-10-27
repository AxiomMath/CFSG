module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5a2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem s888l5a3_oddCoreIn_le (X : Subgroup G) : oddCoreIn X ≤ X := by
  unfold oddCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem s888l5a3_sup_le_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    K₁ ⊔ K₂ ≤ L :=
  sup_le (fun _ hx => (c.pocket₁.2.1 hx).1) (fun _ hx => (c.pocket₂.2.1 hx).1)

theorem centralizerMod_inf_centralizer_le_C6 (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (h52a : Asc82Lemma52a) (hF3 : Asc82FactOm6CentD) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) ⊓
        centralizer ({t} : Set G) ≤ Sec5C6 L K₁ K₂ := by
  classical
  intro x hx
  obtain ⟨hxC, hxt⟩ := hx
  have hQO := h516a G t L S z r B A K₁ K₂ h c
  have hxQO : x ∈ Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) := by
    rw [hQO]
    exact hxC
  have hO_le_N : oddCoreIn (centralizer ({t} : Set G)) ≤
      normalizer (Qsub K₁ K₂ h : Set G) := by
    intro o ho
    have hmem : o ∈ Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) :=
      Subgroup.mem_sup_right ho
    rw [hQO] at hmem
    exact hmem.2.2.1
  haveI : ((Qsub K₁ K₂ h).subgroupOf
      (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)))).Normal := by
    have h1 := Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (H := oddCoreIn (centralizer ({t} : Set G))) (N := Qsub K₁ K₂ h) hO_le_N
    rw [sup_comm] at h1
    exact h1
  have hxL : (⟨x, hxQO⟩ :
      ↥(Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)))) ∈
      (Qsub K₁ K₂ h).subgroupOf
          (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G))) ⊔
        (oddCoreIn (centralizer ({t} : Set G))).subgroupOf
          (Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G))) := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left) (le_sup_right), Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨q, hq, o, ho, hqo⟩ := Subgroup.mem_sup_of_normal_left.mp hxL
  have hqG : (q : G) ∈ Qsub K₁ K₂ h := Subgroup.mem_subgroupOf.mp hq
  have hoG : (o : G) ∈ oddCoreIn (centralizer ({t} : Set G)) :=
    Subgroup.mem_subgroupOf.mp ho
  have hqoG : (q : G) * (o : G) = x := congrArg Subtype.val hqo
  have hoCt : (o : G) ∈ centralizer ({t} : Set G) := s888l5a3_oddCoreIn_le _ hoG
  have hqCt : (q : G) ∈ centralizer ({t} : Set G) := by
    have hq_eq : (q : G) = x * (o : G)⁻¹ := by rw [← hqoG]; group
    rw [hq_eq]
    exact mul_mem hxt (inv_mem hoCt)
  have hqC6 : (q : G) ∈ Sec5C6 L K₁ K₂ :=
    qsub_inf_centralizer_le_C6 h514 h52a c ⟨hqG, hqCt⟩
  have hoC6 : (o : G) ∈ Sec5C6 L K₁ K₂ := by
    have hoCentL : (o : G) ∈ centralizer (L : Set G) :=
      oddCoreIn_centralizer_le h514 h516a h52a hF3 c hoG
    have hoNormL : (o : G) ∈ normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer (L : Set G) hoCentL
    have hoCentK : (o : G) ∈ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (by intro y hy; exact s888l5a3_sup_le_L c hy) hoCentL
    rw [Sec5C6]
    exact Subgroup.mem_sup_right ⟨hoNormL, hoCentK⟩
  rw [← hqoG]
  exact mul_mem hqC6 hoC6

end CFSG.OddStandard.SmallF3.Omega
