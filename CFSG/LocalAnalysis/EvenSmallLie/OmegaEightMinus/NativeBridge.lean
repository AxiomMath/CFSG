
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeBridgeBase

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModel
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (quadTail minusTailForm quadTail_apply
  polar_quadTail minusTailForm_apply minusTailIsometry)
open CFSG.EvenSmallLie.OmegaEight (ind ind_and ind_xor ind_injective charP_two_of_card_eq_two
  one_add_one_eq_zero)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry (elementaryIsometryEquiv)

theorem ns_ok : nsArr.size = 136 ∧ nsIdx.size = 256 ∧
    (∀ j < 136, nsArr[j]! < 256 ∧ qNat nsArr[j]! = true ∧ nsIdx[nsArr[j]!]! = j) ∧
    ∀ v < 256, qNat v = true → nsIdx[v]! < 136 ∧ nsArr[nsIdx[v]!]! = v := by
  have h := ns_check
  simp only [nsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1.1.1, h.1.1.2, fun j hj => ⟨(h.1.2 j hj).1.1, (h.1.2 j hj).1.2, (h.1.2 j hj).2⟩,
    fun v hv hq => ?_⟩
  rcases h.2 v hv with h' | h'
  · rw [hq] at h'
    exact absurd h' (by decide)
  · exact h'

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

@[expose] def nsVec (j : Fin 136) : NS K :=
  ⟨vecK K nsArr[(j : ℕ)]!, by rw [quad_vecK hK, (ns_ok.2.2.1 j j.2).2.1]; rfl⟩

theorem nsVec_val (j : Fin 136) :
    (nsVec hK j : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) = vecK K nsArr[(j : ℕ)]! :=
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
    obtain ⟨h1, h2⟩ := ns_ok.2.2.2 n hn (qNat_of_quad hK hv)
    exact ⟨⟨_, h1⟩, Subtype.ext (by rw [nsVec_val, h2])⟩

@[expose] def nsEquiv
    : Fin 136 ≃ NS K := Equiv.ofBijective _ (nsVec_bijective hK)

theorem nsEquiv_apply
    (j : Fin 136) : nsEquiv hK j = nsVec hK j := rfl

@[expose] def act0
    : orthElementaryGroup (qM K) →* Equiv.Perm (Fin 136) where
  toFun g := (nsEquiv hK).symm.permCongr (nsPerm g)
  map_one' := by
    ext j
    simp [Equiv.permCongr_apply, nsPerm]
  map_mul' g h := by
    ext j
    simp [Equiv.permCongr_apply, nsPerm]

theorem nsEquiv_act0 (g : orthElementaryGroup (qM K)) (j : Fin 136) :
    ((nsEquiv hK (act0 hK g j) : NS K) : (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) =
      (g : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _) (nsVec hK j) := by
  simp [act0, Equiv.permCongr_apply, nsPerm, nsEquiv_apply]

end Action

section Action

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
include hK

theorem act0_eichGen
    {i : ℕ} (hi : i < 10) : act0 hK (eichGen K i) = gen i := by
  refine Equiv.ext fun j => Fin.ext ?_
  obtain ⟨hq, hb, hu, hw⟩ := pair_ok hi
  have hx : nsArr[(j : ℕ)]! < 256 := (ns_ok.2.2.1 j j.2).1
  have hm := eichNat_lt hu hw hx
  have hval : ((eichGen K i : orthElementaryGroup (qM K)) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] _) (vecK K nsArr[(j : ℕ)]!) =
      vecK K (eichNat (gPairs.getD i (0, 0)).1 (gPairs.getD i (0, 0)).2 nsArr[(j : ℕ)]!) :=
    eichler_vecK hK hq hb _
  have hqm : qNat (eichNat (gPairs.getD i (0, 0)).1 (gPairs.getD i (0, 0)).2
      nsArr[(j : ℕ)]!) = true := by
    apply qNat_of_quad hK
    rw [← hval, quad_elementary, quad_vecK hK, (ns_ok.2.2.1 j j.2).2.1]
    rfl
  obtain ⟨h1, h2⟩ := ns_ok.2.2.2 _ hm hqm
  have hact : act0 hK (eichGen K i) j = ⟨_, h1⟩ := by
    apply (nsEquiv hK).injective
    apply Subtype.ext
    rw [nsEquiv_act0, nsEquiv_apply, nsVec_val, nsVec_val, hval, h2]
  rw [hact, ← (rep_gen (by omega : i < 11)).apply j.2, genArrs_getElem! hi,
    eichArr_getElem! _ j.2]

theorem omegaT_le_range_act0 : omegaT ≤ (act0 hK).range := by
  rw [omegaT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨eichGen K i, act0_eichGen hK hi⟩

theorem act0_range : (act0 hK).range = omegaT := by
  have := finite_elementaryGroup_qM hK
  refine (Subgroup.eq_of_le_of_card_ge (omegaT_le_range_act0 hK) ?_).symm
  rw [card_omegaT, ← card_elementaryGroup_qM hK]
  exact Nat.card_le_card_of_surjective _ (act0 hK).rangeRestrict_surjective

theorem act0_rangeRestrict_bijective
    : Function.Bijective (act0 hK).rangeRestrict := by
  have := finite_elementaryGroup_qM hK
  exact (act0 hK).rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [act0_range, card_omegaT, card_elementaryGroup_qM hK])

@[expose] def elementaryOmegaEquiv
    : orthElementaryGroup (qM K) ≃* omegaT :=
  (MulEquiv.ofBijective (act0 hK).rangeRestrict (act0_rangeRestrict_bijective hK)).trans
    (MulEquiv.subgroupCongr (act0_range hK))

end Action

theorem nonempty_mulEquiv_omegaT {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .POmegaMinus 4 2 1) : Nonempty (X ≃* omegaT) := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ := NonsplitOrthogonalCover.exists_mulEquiv_of_lieModel hX
  exact ⟨e.trans (elementaryOmegaEquiv hK)⟩

end CFSG.EvenSmallLie.OmegaEightMinus
