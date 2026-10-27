module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Cd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Pure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_E0_conj (F : Sec8T84Base) (hI : Asc82Step84IK) (hSw : Sec8T84OuterSwaps)
    (hKP : CFSG.Assembly.KProper Catalog G) {t : G} {L S : Subgroup G} {z g : G}
    {B E T T1 T2 V1 V2 F1 F2 : Subgroup G} (hE : Sec8E G t L S z g B E)
    (hgood : S ⊓ L ≤ normalizer (E : Set G)) (hST : S ⊓ normalizer (E : Set G) ≤ T)
    (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8) :
    ∃ u : G, F1 ⊔ F2 = E.map (MulAut.conj u).toMonoidHom := by
  have hctx := hE.ctx
  have ht : t * t = 1 := by
    rw [← pow_two, ← hctx.involution]
    exact pow_orderOf_eq_one t
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htS : t ∈ S := sec4_t_mem_S hctx.sylow hctx.involution
  have htN : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hE.t_norm e he, fun he => ?_⟩
    have h := hE.t_norm (t * e * t⁻¹) he
    have hkey : t * (t * e * t⁻¹) * t⁻¹ = e := by
      rw [hinv]
      calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
        _ = e := by rw [ht]; group
    rwa [hkey] at h
  have htT : t ∈ T := hST (Subgroup.mem_inf.mpr ⟨htS, htN⟩)
  obtain ⟨γ, hγS, B', hB'le, hB'e, hB'ne, hB'eq⟩ := sec8t84_B_swap F hI hSw hKP hctx
  have hSC : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hB'T0 : B' ≤ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨?_, hSC (hB'le hb).1⟩
    exact sec8t84_inv_L_le_T0 F hE hgood hST D hrk b (hB'le hb)
      (CFSG.Open.IsElemAbelian.mul_self_eq_one hB'e.1 hb)
  have hne : B' ≠ E ⊓ centralizer ({t} : Set G) := by
    rw [hE.cent_t]
    exact hB'ne
  have hB'E0 : B' ≤ F1 ⊔ F2 := sec8t84_cent_E16_le_E0 D hB'T0 hB'e hne
  have hB'E0c : B' ≤ (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) :=
    le_inf hB'E0 (fun b hb => (hB'T0 hb).2)
  have htE0 : ∀ e ∈ F1 ⊔ F2, t * e * t⁻¹ ∈ F1 ⊔ F2 := by
    intro e he
    have hmem : (⟨e, sec8t84_E0_le_T D he⟩ : ↥T) ∈ (F1 ⊔ F2).subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr he
    exact Subgroup.mem_subgroupOf.mp
      ((sec8t84_E0_normal D).conj_mem _ hmem ⟨t, htT⟩)
  have hB4 : Nat.card B = 16 := by
    have h := hctx.B_e16.2
    norm_num at h
    exact h
  exact sec8t84_conj_of_syl ht hE.elem (sec8t84_E0_isElemAb2 D) hE.t_norm htE0 hE.cent_t hB4
    (F.hSyl G t L S z g B E hE) (hSC hγS) hB'eq hB'E0c (sec8t84_E0_cent_card_le D)

end CFSG.OddStandard.SmallF3.Omega
