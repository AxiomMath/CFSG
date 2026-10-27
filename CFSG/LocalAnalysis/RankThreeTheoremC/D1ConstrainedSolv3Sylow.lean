module

public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_index_inf_of_sylow {q : ℕ} [Fact q.Prime] {T D N : Subgroup G} (hTN : T ≤ N)
    (hDN : D ≤ N) (hT : IsPGroup q T) (hidx : ¬ q ∣ (T.subgroupOf N).index)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) : ¬ q ∣ ((T ⊓ D).subgroupOf D).index := by
  set K : Subgroup G := T ⊔ D with hK
  have hTK : T ≤ K := le_sup_left
  have hKN : K ≤ N := sup_le hTN hDN
  have hnormB : (D.subgroupOf K).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTD
  have hA : IsPGroup q (T.subgroupOf K) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hAidx : ¬ q ∣ (T.subgroupOf K).index := fun hd =>
    hidx (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T K N hTK hKN)))
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal (hA.toSylow hAidx) (N := D.subgroupOf K)
  have hPidx : ¬ q ∣ (P : Subgroup ↥(D.subgroupOf K)).index := P.not_dvd_index
  have hinf : (T ⊓ D).subgroupOf K = T.subgroupOf K ⊓ D.subgroupOf K := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hP, IsPGroup.toSylow_coe, ← hinf] at hPidx
  have h := Subgroup.relIndex_subgroupOf (H := T ⊓ D) (K := D) (L := K) le_sup_right
  change ¬ q ∣ (T ⊓ D).relIndex D
  rw [← h]
  exact hPidx

theorem not_dvd_index_inf_of_sylow_top {q : ℕ} [Fact q.Prime] (T : Sylow q G) {D : Subgroup G}
    (hTD : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) :
    ¬ q ∣ (((T : Subgroup G) ⊓ D).subgroupOf D).index := by
  refine not_dvd_index_inf_of_sylow le_top le_top T.isPGroup' ?_ hTD
  change ¬ q ∣ (T : Subgroup G).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

end CFSG.LocalAnalysis.RankThreeTheoremC
