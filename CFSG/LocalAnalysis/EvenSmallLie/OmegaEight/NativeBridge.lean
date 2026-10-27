
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal

section Field

variable {K : Type} [Field K] [Finite K]

end Field

theorem ns_ok : nsArr.size = 120 ∧ nsIdx.size = 256 ∧
    (∀ j < 120, nsArr[j]! < 256 ∧ qNat nsArr[j]! = true ∧ nsIdx[nsArr[j]!]! = j) ∧
    ∀ v < 256, qNat v = true → nsIdx[v]! < 120 ∧ nsArr[nsIdx[v]!]! = v := by
  have h := ns_check
  simp only [nsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1.1.1, h.1.1.2, fun j hj => ⟨(h.1.2 j hj).1.1, (h.1.2 j hj).1.2, (h.1.2 j hj).2⟩,
    fun v hv hq => ?_⟩
  rcases h.2 v hv with h' | h'
  · rw [hq] at h'
    exact absurd h' (by decide)
  · exact h'

section Vectors

variable {K : Type} [Field K]

variable [Finite K] (hK : Nat.card K = 2)
include hK

end Vectors

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

@[expose] def nsVec (j : Fin 120) : NS K :=
  ⟨vecK K nsArr[(j : ℕ)]!, by rw [quadPlus_vecK hK, (ns_ok.2.2.1 j j.2).2.1]; rfl⟩

theorem nsVec_val
    (j : Fin 120) : (nsVec hK j : Fin 4 ⊕ Fin 4 → K) = vecK K nsArr[(j : ℕ)]! :=
  rfl

theorem nsVec_bijective : Function.Bijective (nsVec hK) := by
  constructor
  · intro i j h
    have h1 := congrArg Subtype.val h
    rw [nsVec_val, nsVec_val] at h1
    have e := vecK_injective (ns_ok.2.2.1 i i.2).1 (ns_ok.2.2.1 j j.2).1 h1
    apply Fin.ext
    rw [← (ns_ok.2.2.1 i i.2).2.2, ← (ns_ok.2.2.1 j j.2).2.2, e]
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn, rfl⟩ := exists_vecK hK v
    obtain ⟨h1, h2⟩ := ns_ok.2.2.2 n hn (qNat_of_quadPlus hK hv)
    exact ⟨⟨_, h1⟩, Subtype.ext (by rw [nsVec_val, h2])⟩

@[expose] def nsEquiv
    : Fin 120 ≃ NS K := Equiv.ofBijective _ (nsVec_bijective hK)

theorem nsEquiv_apply
    (j : Fin 120) : nsEquiv hK j = nsVec hK j := rfl

@[expose] def act0
    : orthElementaryGroup (quadPlus 4 K) →* Equiv.Perm (Fin 120) where
  toFun g := (nsEquiv hK).symm.permCongr (nsPerm g)
  map_one' := by
    ext j
    simp [Equiv.permCongr_apply, nsPerm]
  map_mul' g h := by
    ext j
    simp [Equiv.permCongr_apply, nsPerm]

theorem nsEquiv_act0
    (g : orthElementaryGroup (quadPlus 4 K)) (j : Fin 120) :
    ((nsEquiv hK (act0 hK g j) : NS K) : Fin 4 ⊕ Fin 4 → K) =
      (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (nsVec hK j) := by
  simp [act0, Equiv.permCongr_apply, nsPerm, nsEquiv_apply]

end Action

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

theorem act0_eichGen
    {i : ℕ} (hi : i < 8) : act0 hK (eichGen K i) = gen1 i := by
  refine Equiv.ext fun j => Fin.ext ?_
  obtain ⟨hq, hb, hu, hw⟩ := pair0_ok hi
  have hx : nsArr[(j : ℕ)]! < 256 := (ns_ok.2.2.1 j j.2).1
  have hm : eichNat (pair0 i).1 (pair0 i).2 nsArr[(j : ℕ)]! < 256 := eichNat_lt hu hw hx
  have hval : ((eichGen K i : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (vecK K nsArr[(j : ℕ)]!) =
      vecK K (eichNat (pair0 i).1 (pair0 i).2 nsArr[(j : ℕ)]!) := eichler_vecK hK hq hb _
  have hqm : qNat (eichNat (pair0 i).1 (pair0 i).2 nsArr[(j : ℕ)]!) = true := by
    apply qNat_of_quadPlus hK
    rw [← hval, quadPlus_elementary, quadPlus_vecK hK, (ns_ok.2.2.1 j j.2).2.1]
    rfl
  obtain ⟨h1, h2⟩ := ns_ok.2.2.2 _ hm hqm
  have hact : act0 hK (eichGen K i) j = ⟨_, h1⟩ := by
    apply (nsEquiv hK).injective
    apply Subtype.ext
    rw [nsEquiv_act0, nsEquiv_apply, nsVec_val, nsVec_val, hval, h2]
  rw [hact, ← (rep_gen1 hi).apply j.2, copy0Arr_getElem! _ j.2, genArrs_getElem! hi,
    rootArr_getElem! _ j.2]
  rfl

theorem omega1T_le_range_act0 : omega1T ≤ (act0 hK).range := by
  rw [omega1T_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨eichGen K i, act0_eichGen hK hi⟩

theorem act0_range : (act0 hK).range = omega1T := by
  have := finite_elementaryGroup_four hK
  refine (Subgroup.eq_of_le_of_card_ge (omega1T_le_range_act0 hK) ?_).symm
  rw [card_omega1T, ← card_elementaryGroup_four hK]
  exact Nat.card_le_card_of_surjective _ (act0 hK).rangeRestrict_surjective

theorem act0_rangeRestrict_bijective
    : Function.Bijective (act0 hK).rangeRestrict := by
  have := finite_elementaryGroup_four hK
  exact (act0 hK).rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [act0_range, card_omega1T, card_elementaryGroup_four hK])

@[expose] def elementaryOmega1Equiv
    : orthElementaryGroup (quadPlus 4 K) ≃* omega1T :=
  (MulEquiv.ofBijective (act0 hK).rangeRestrict (act0_rangeRestrict_bijective hK)).trans
    (MulEquiv.subgroupCongr (act0_range hK))

end Action

theorem nonempty_mulEquiv_omegaT {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1) : Nonempty (X ≃* omegaT) := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ :=
    OrthogonalSplit.exists_mulEquiv_elementaryGroup_of_lieModel hX
  exact ⟨(e.trans (elementaryOmega1Equiv (by rw [hK]; norm_num))).trans
    omegaRestrictEquiv.symm⟩

end CFSG.EvenSmallLie.OmegaEight
