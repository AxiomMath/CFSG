module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.LocalAnalysis.RankThreeUC.Focal

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.StrongP CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem IsStronglyPEmbedded.not_dvd_card_inf_conj (hM : IsStronglyPEmbedded p M) {g : G}
    (hg : g ∉ M) : ¬ p ∣ Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
  hM.2.2 g hg

theorem IsStronglyPEmbedded.mem_of_conj_mem [Fact p.Prime] {T : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hT : IsPGroup p T) (hTM : T ≤ M) {x g : G} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ ∈ T) : g ∈ M := by
  by_contra hg
  have hg' : g⁻¹ ∉ M := fun h => hg (by simpa using M.inv_mem h)
  refine hM.2.2 g⁻¹ hg' ?_
  have hU : zpowers x ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    exact hx1
  have hUp : IsPGroup p (zpowers x) := hT.to_le (zpowers_le.mpr hx)
  have hpU : p ∣ Nat.card (zpowers x) := by
    rcases hUp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hU
    · exact h
  refine hpU.trans (Subgroup.card_dvd_of_le (zpowers_le.mpr (Subgroup.mem_inf.mpr
    ⟨hTM hx, ?_⟩)))
  rw [mem_conjSub_iff]
  simpa using hTM hgx

theorem IsStronglyPEmbedded.exists_sylow_le_commutator [Fact p.Prime] (hperf : commutator G = ⊤)
    (hM : IsStronglyPEmbedded p M) :
    ∃ T : Sylow p G, (T : Subgroup G) ≤ M ∧ (T : Subgroup G) ≤ ⁅M, M⁆ := by
  obtain ⟨P, hP, hPM⟩ := hM.exists_isSylowOf_le
  let T : Sylow p G := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hTP : (T : Subgroup G) = P := rfl
  have hTM : (T : Subgroup G) ≤ M := hTP ▸ hPM
  refine ⟨T, hTM, ?_⟩
  have hfusion : ∀ x ∈ (T : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (T : Subgroup G) →
      Relation.ReflTransGen (fun y z => y ∈ (T : Subgroup G) ∧ z ∈ (T : Subgroup G) ∧
        ∃ N ∈ ({M} : Set (Subgroup G)), ∃ c ∈ N, z = c * y * c⁻¹) x (g * x * g⁻¹) := by
    intro x hx g hgx
    by_cases hx1 : x = 1
    · subst hx1
      simpa using Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hx, hgx, M, rfl, g,
        hM.mem_of_conj_mem T.isPGroup' hTM hx hx1 hgx, rfl⟩
  have := inf_commutator_le_of_fusion_control T (T₀ := ⁅M, M⁆) ({M} : Set (Subgroup G))
    (fun N hN => by rw [Set.mem_singleton_iff.mp hN]; exact hTM)
    (fun N hN => by rw [Set.mem_singleton_iff.mp hN]; exact inf_le_right) hfusion
  rwa [hperf, inf_top_eq] at this

theorem IsStronglyPEmbedded.not_dvd_relIndex_of_commutator_le [Fact p.Prime]
    (hperf : commutator G = ⊤) (hM : IsStronglyPEmbedded p M) {N : Subgroup G} (hNM : N ≤ M)
    (hcomm : ⁅M, M⁆ ≤ N) : ¬ p ∣ N.relIndex M := by
  obtain ⟨T, hTM, hTc⟩ := hM.exists_sylow_le_commutator hperf
  have hTN : (T : Subgroup G) ≤ N := hTc.trans hcomm
  intro hdvd
  have h1 : N.relIndex M ∣ (T : Subgroup G).relIndex M := relIndex_dvd_of_le_left M hTN
  have h2 : (T : Subgroup G).relIndex M ∣ (T : Subgroup G).index := by
    rw [← relIndex_top_right, ← relIndex_mul_relIndex (T : Subgroup G) M ⊤ hTM le_top]
    exact dvd_mul_right _ _
  exact T.not_dvd_index (hdvd.trans (h1.trans h2))

theorem IsStronglyPEmbedded.map_not_dvd_relIndex_of_commutator_le [Fact p.Prime]
    (hperf : commutator G = ⊤) (hM : IsStronglyPEmbedded p M) (g : G) {N : Subgroup G}
    (hNM : N ≤ M.map (MulAut.conj g).toMonoidHom)
    (hcomm : ⁅M.map (MulAut.conj g).toMonoidHom, M.map (MulAut.conj g).toMonoidHom⁆ ≤ N) :
    ¬ p ∣ N.relIndex (M.map (MulAut.conj g).toMonoidHom) :=
  (hM.conj g).not_dvd_relIndex_of_commutator_le hperf hNM hcomm

end CFSG.RankThree.PartOne
