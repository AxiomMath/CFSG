module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisReduce
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open Subgroup

section SylowAction

variable {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] (p : ℕ)

@[expose] def sylowConj : Y →* Equiv.Perm (Sylow p ↥N) :=
  (MulAction.toPermHom (MulAut ↥N) (Sylow p ↥N)).comp (MulAut.conjNormal (H := N))

theorem sylowConj_apply (y : Y) (T : Sylow p ↥N) :
    sylowConj N p y T = MulAut.conjNormal (H := N) y • T :=
  rfl

theorem mem_ker_sylowConj {y : Y} : y ∈ (sylowConj N p).ker ↔
    ∀ T : Sylow p ↥N, ∀ t ∈ (T : Subgroup ↥N),
      MulAut.conjNormal (H := N) y t ∈ (T : Subgroup ↥N) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h T t ht
    have hT : MulAut.conjNormal (H := N) y • T = T := by
      rw [← sylowConj_apply, h]
      rfl
    rw [← hT, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul t _ _ ht
  · intro h
    refine Equiv.ext fun T => ?_
    rw [sylowConj_apply]
    have hle : ((MulAut.conjNormal (H := N) y • T : Sylow p ↥N) : Subgroup ↥N) ≤ T := by
      intro x hx
      rw [Sylow.pointwise_smul_def, mem_smul_pointwise_iff_exists] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact h T t ht
    exact Sylow.ext ((MulAut.conjNormal (H := N) y • T).is_maximal' T.isPGroup' hle).symm

theorem mem_ker_sylowConj_of_mem {e : Y} (he : e ∈ N) (h : ∀ T : Sylow p ↥N, ⟨e, he⟩ ∈ T) :
    e ∈ (sylowConj N p).ker := by
  rw [mem_ker_sylowConj]
  intro T t ht
  have : MulAut.conjNormal (H := N) e t = ⟨e, he⟩ * t * ⟨e, he⟩⁻¹ := Subtype.ext rfl
  rw [this]
  exact mul_mem (mul_mem (h T) ht) (inv_mem (h T))

theorem le_ker_sylowConj_of_normal [Fact p.Prime] {P : Subgroup Y} [P.Normal]
    (hP : IsPGroup p P) : P ≤ (sylowConj N p).ker := by
  intro x hx
  rw [mem_ker_sylowConj]
  intro T t ht
  set T' : Subgroup Y := (T : Subgroup ↥N).map N.subtype
  have hT' : IsPGroup p T' := T.isPGroup'.map _
  have hPT : IsPGroup p ↥(P ⊔ T') := hP.to_sup_of_normal_left hT'
  have hle : (T : Subgroup ↥N) ≤ (P ⊔ T').subgroupOf N := fun s hs =>
    mem_subgroupOf.mpr (mem_sup_right ⟨s, hs, rfl⟩)
  have heq : (P ⊔ T').subgroupOf N = T :=
    T.is_maximal' (hPT.comap_of_injective N.subtype N.subtype_injective) hle
  rw [← heq, mem_subgroupOf]
  change x * (t : Y) * x⁻¹ ∈ P ⊔ T'
  exact mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right ⟨t, ht, rfl⟩))
    (inv_mem (mem_sup_left hx))

end SylowAction

theorem exists_mem_normalizer_not_mem_A5 (P : Sylow 2 (alternatingGroup (Fin 5))) :
    ∃ g ∈ normalizer (P : Set (alternatingGroup (Fin 5))), g ∉ (P : Subgroup _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 15 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hP4 : Nat.card (P : Subgroup (alternatingGroup (Fin 5))) = 2 ^ 2 := by
    rw [P.card_eq_multiplicity, hcard, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  have hcomm : IsMulCommutative (P : Subgroup (alternatingGroup (Fin 5))) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hP4
  have hNC : normalizer (P : Set (alternatingGroup (Fin 5))) ≤
      centralizer (P : Set (alternatingGroup (Fin 5))) := fun g hg =>
    mem_centralizer_iff.mpr fun x hx => congrArg Subtype.val
      (hcomm.is_comm.comm ⟨x, hx⟩ ⟨g, h g hg⟩)
  have h2 := MonoidHom.not_dvd_card_ker_transferSylow P hNC
  rcases (alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)).eq_bot_or_eq_top_of_normal
      (MonoidHom.transferSylow P hNC).ker with hK | hK
  · have hc := (MonoidHom.ker_transferSylow_isComplement' P hNC).card_mul_card
    rw [hK, card_bot, hP4, hcard] at hc
    exact absurd hc (by norm_num)
  · rw [hK, card_top, hcard] at h2
    exact h2 (by norm_num)

end CFSG.ComponentClassification.GHarris
