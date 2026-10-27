module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin.KGC31

variable {K : Type} [Group K] {L V MK : Subgroup K}

theorem KConfig.eq_of_abelCent [Finite K] (h : KConfig K L V MK) {U Q N : Subgroup K}
    (hQ : Subgroup.centralizer (U : Set K) = Q) (hΩ : ∀ q ∈ Q, q * q = 1 → q ∈ U)
    (hN : Subgroup.normalizer (U : Set K) = N)
    (hNs : ∀ X : Subgroup K, X ≤ N → N ≤ Subgroup.normalizer (X : Set K) → ⁅X, X⁆ = X →
      ¬ X ≤ Q → X = N)
    {y t : K} (hy : y ∈ L) (ht : t ∈ V) (hU : CFSG.Quasithin.KGC31.orbSub y t = U) :
    V = U ∧ L = N := by
  have hUV : U ≤ V := hU ▸ orbSub_le (h.le_normalizer hy) ht
  have hVQ : V ≤ Q := by
    rw [← hQ]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨u, hUV hu⟩)).symm
  have hVU : V ≤ U := by
    intro v hv
    refine hΩ v (hVQ hv) ?_
    rw [← pow_two]
    exact h.elemAbelian.2 v hv
  have hVeq : V = U := le_antisymm hVU hUV
  have hNV : Subgroup.normalizer (V : Set K) = N := by
    rw [hVeq]
    exact hN
  have hLN : L ≤ N := hNV ▸ h.le_normalizer
  have hNL : N ≤ Subgroup.normalizer (L : Set K) :=
    hNV ▸ (h.normalizer_le_MK.trans h.MK_le_normalizer)
  have hLQ : ¬ L ≤ Q := by
    intro hle
    have hcent : L ≤ Subgroup.centralizer (V : Set K) := by
      rw [hVeq, hQ]
      exact hle
    have hbot : ⁅V, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcent
    exact h.ne_bot (h.eq_commutator.trans hbot)
  exact ⟨hVeq, hNs L hLN hNL h.perfect hLQ⟩

end CFSG.SectionRank.QTK.Insp443

end
