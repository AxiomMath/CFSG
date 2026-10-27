module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fi24Inputs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Glue

open Subgroup

variable {G : Type} [Group G] {C R : Subgroup G}

theorem le_pCore_of_normal {p : ℕ} {Q : Type*} [Group Q] {S : Subgroup Q} (hS : S.Normal)
    (hp : IsPGroup p S) : S ≤ CFSG.pCore p Q :=
  le_sSup ⟨hS, hp⟩

theorem pCore_two_eq (h : O2In C = R) : CFSG.pCore 2 ↥C = R.subgroupOf C := by
  rw [← h]
  exact (comap_map_eq_self_of_injective C.subtype_injective _).symm

theorem le_O23In (hRC : R ≤ C) (h : O2In C = R) : R ≤ O23In C := by
  intro r hr
  have hr' : (⟨r, hRC hr⟩ : ↥C) ∈ CFSG.pCore 2 ↥C := by
    rw [pCore_two_eq h]
    exact hr
  refine ⟨⟨r, hRC hr⟩, mem_comap.2 ?_, rfl⟩
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hr']
  exact one_mem _

theorem O23In_le : O23In C ≤ C := map_subtype_le _

theorem O23In_normal : ((O23In C).subgroupOf C).Normal := by
  have h : (O23In C).subgroupOf C = (CFSG.pCore 3 (↥C ⧸ CFSG.pCore 2 ↥C)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) :=
    comap_map_eq_self_of_injective C.subtype_injective _
  rw [h]
  infer_instance

theorem O23In_conj_mem {w n : G} (hw : w ∈ O23In C) (hn : n ∈ C) : n * w * n⁻¹ ∈ O23In C :=
  (normal_subgroupOf_iff O23In_le).1 O23In_normal w n hw hn

theorem exists_pow_mem_of_mem_O23In (h : O2In C = R) {w : G} (hw : w ∈ O23In C) :
    ∃ k : ℕ, w ^ 3 ^ k ∈ R := by
  obtain ⟨y, hy, rfl⟩ := hw
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) (G := ↥C ⧸ CFSG.pCore 2 ↥C) ⟨_, mem_comap.1 hy⟩
  refine ⟨k, ?_⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥C) (y ^ 3 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  have := (QuotientGroup.eq_one_iff _).1 hk'
  rw [pCore_two_eq h, mem_subgroupOf] at this
  simpa using this

theorem le_O23In_of_pow_mem (h : O2In C = R) {V : Subgroup G} (hVC : V ≤ C)
    (hVn : ∀ v n, v ∈ V → n ∈ C → n * v * n⁻¹ ∈ V) (hV : ∀ v ∈ V, ∃ k : ℕ, v ^ 3 ^ k ∈ R) :
    V ≤ O23In C := by
  intro v hv
  refine ⟨⟨v, hVC hv⟩, mem_comap.2 ?_, rfl⟩
  have hnorm : (V.subgroupOf C).Normal := (normal_subgroupOf_iff hVC).2 hVn
  have hnorm' : ((V.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 3 ((V.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hV y hy
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥C) y) ^ 3 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pCore_two_eq h,
      mem_subgroupOf]
    simpa using hk
  exact le_pCore_of_normal hnorm' hp (mem_map_of_mem _ (mem_subgroupOf.2 hv))

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Glue
