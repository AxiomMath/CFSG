module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

theorem autFixInner_alternatingGroup {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (T : Sylow p (alternatingGroup (Fin (2 * p)))) :
    AutFixInner p (alternatingGroup (Fin (2 * p))) T := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  intro f hf
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (2 * p)
    (by omega) (by omega)).2 f
  let e : alternatingGroup (Fin (2 * p)) ≃* alternatingGroup (Fin (2 * p)) := MulEquiv.refl _
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  have hι : ∀ x, altPermEmbed e x = (x : Perm (Fin (2 * p))) := fun x => rfl
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hEab hEcard
  have hcomm : ∀ a ∈ (T : Subgroup (alternatingGroup (Fin (2 * p)))).map (altPermEmbed e),
      σ * a = a * σ := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ha
    have h1 := congrArg (fun g : alternatingGroup (Fin (2 * p)) => (g : Perm (Fin (2 * p))))
      (hf t ht)
    simp only [← hσ, MulAut.conjNormal_apply] at h1
    rw [hι]
    calc σ * (t : Perm (Fin (2 * p))) = (σ * t * σ⁻¹) * σ := by group
      _ = t * σ := by rw [h1]
  obtain ⟨i, j, hij⟩ := CFSG.AGLEmbeddingD2.AltSurvivor.exists_zpow_mul_zpow_eq
    (isCycle_of_moves hp (hEab.2 a₁ ha₁) hO₁ hm₁) (isCycle_of_moves hp (hEab.2 a₂ ha₂) hO₂ hm₂)
    hm₁ hm₂ hd (mem_or_mem_of_card hO₁ hO₂ hd (Fintype.card_fin _)) (hcomm a₁ ha₁)
    (hcomm a₂ ha₂)
  have hmem : σ ∈ (T : Subgroup (alternatingGroup (Fin (2 * p)))).map (altPermEmbed e) := by
    rw [hij]
    exact mul_mem (zpow_mem ha₁ i) (zpow_mem ha₂ j)
  obtain ⟨t₀, ht₀, hσt⟩ := Subgroup.mem_map.1 hmem
  refine ⟨t₀, ?_⟩
  rw [← hσ]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conj_apply]
  have : σ = (t₀ : Perm (Fin (2 * p))) := by rw [← hσt, hι]
  rw [this]
  simp

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem autFixInner_of_isAltTwoP_of_five_le (hp : p.Prime) (hp5 : 5 ≤ p) (hK : IsAltTwoP p K)
    (T : Sylow p K) : AutFixInner p K T := by
  obtain ⟨e⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow p (alternatingGroup (Fin (2 * p)))) := inferInstance
  exact AutFixInner.of_equiv_all hp e ⟨T₀, autFixInner_alternatingGroup hp hp5 T₀⟩ T

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
