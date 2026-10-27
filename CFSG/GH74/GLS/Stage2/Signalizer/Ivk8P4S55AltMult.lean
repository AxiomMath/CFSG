module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Alternating.Multipliers CFSG.RankThree.PerfectCover

theorem card_center_dvd_of_alt {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K) {n : ℕ}
    (hn : 5 ≤ n) (e : (K ⧸ center K) ≃* alternatingGroup (Fin n)) :
    Nat.card (center K) ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin n))) := by
  have hS : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  let π : K →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center K := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have : Group.IsPerfect K := hK.1
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier π hπ (by rw [hker])
  have hd : Nat.card π.ker ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin n))) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rwa [hker] at hd

theorem multAlt55 : MultAlt55 := by
  refine ⟨fun K _ _ hK ⟨e⟩ => ?_, fun K _ _ hK ⟨e⟩ => ?_⟩
  · have h := card_center_dvd_of_alt hK (by norm_num) e
    rw [(hopfMultiplier_alternatingGroup_seven).2] at h
    exact h
  · have h := card_center_dvd_of_alt hK (by norm_num) e
    rw [card_hopfMultiplier_alternatingGroup (by norm_num : 8 ≤ 11)] at h
    exact h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
