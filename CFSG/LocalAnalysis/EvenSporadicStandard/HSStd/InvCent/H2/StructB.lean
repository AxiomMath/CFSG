module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Stable

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem derived_le_component_or_rest [Finite G] (cfg : H2Cfg G t v J)
    (hF : fittingSubgroup G = ⊥) (hJE : ⁅J, J⁆ ≤ layer G) {L : Subgroup G} (hL : IsComponent L) :
    ⁅J, J⁆ ≤ L ∨ ⁅J, J⁆ ≤ Rest G L L := by
  have hR : Rest G L L ≤ centralizer (L : Set G) := by
    simpa [sup_idem] using rest_le_centralizer hL hL
  have hRest_le_layer : Rest G L L ≤ layer G := by
    rw [Rest]
    exact sSup_le fun _ hL' => CFSG.LocalCores.component_le_layer hL'.1
  have hlayer : layer G = L ⊔ Rest G L L := by
    rw [layer_eq_sup_rest hL hL, sup_idem]
  have hNR : L ⊓ Rest G L L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    refine eq_one_of_commute_of_simple (component_isSimple hF hL) (component_nonab hF hL) hx.1
      fun b hb => ?_
    exact mem_centralizer_iff.1 (hR hx.2) b hb
  have hdec : ∀ m ∈ layer G ⊓ centralizer ({t} : Set G),
      ∃ p ∈ L ⊓ centralizer ({t} : Set G),
        ∃ q ∈ Rest G L L ⊓ centralizer ({t} : Set G), m = p * q := by
    intro m hm
    have hm' : m ∈ L ⊔ Rest G L L := by rw [← hlayer]; exact hm.1
    obtain ⟨p, hpL, q, hqR, hm_eq⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (A := L) (B := Rest G L L) hR hm'
    have hcomm : t * (p * q) = (p * q) * t := by
      rw [← hm_eq]
      exact (mem_centralizer_singleton_iff.1 hm.2).symm
    obtain ⟨hpt, hqt⟩ := fixed_decomp (N := L) (R := Rest G L L) hNR
      (fun x hx => cfg.conj_mem_of_component hF hL hx)
      (fun x hx => cfg.conj_mem_rest hF hx) hpL hqR hcomm
    exact ⟨p, ⟨hpL, mem_centralizer_singleton_iff.2 hpt.symm⟩,
      q, ⟨hqR, mem_centralizer_singleton_iff.2 hqt.symm⟩, hm_eq⟩
  have hPQ : ∀ p ∈ L ⊓ centralizer ({t} : Set G),
      ∀ q ∈ Rest G L L ⊓ centralizer ({t} : Set G), p * q = q * p := by
    intro p hp q hq
    exact mem_centralizer_iff.1 (hR hq.1) p hp.1
  have hmain := simple_le_or_le_of_decomposition
    (B := ⁅J, J⁆) (M := layer G ⊓ centralizer ({t} : Set G))
    (P := L ⊓ centralizer ({t} : Set G))
    (Q := Rest G L L ⊓ centralizer ({t} : Set G))
    cfg.derived_isSimple cfg.derived_nonab
    (le_inf hJE cfg.derived_le_centralizer)
    (inf_le_inf (CFSG.LocalCores.component_le_layer hL) le_rfl)
    (inf_le_inf hRest_le_layer le_rfl)
    hPQ hdec
    (fun m hm b hb => cfg.derived_normalized hm.2 hb)
  rcases hmain with h | h
  · exact Or.inl (h.trans inf_le_left)
  · exact Or.inr (h.trans inf_le_left)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
