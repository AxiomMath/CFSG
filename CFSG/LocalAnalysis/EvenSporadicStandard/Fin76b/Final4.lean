
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final4Base

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransferJ

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bSwapInnerOnD_of_notZ2A6
    (hZ : Fin76bNotZ2A6) : Fin76bSwapInnerOnD := by
  intro G _ _ L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt
  have hcfg := hconf.cfg
  have hE2 : IsPGroup 2 E := hcfg.T₀_pgroup.to_le hconf.econfig.le
  obtain ⟨hz, hL64⟩ := hconf.lemma64
  have hBD := fin76bBetaData G L z t T₀ E Q x β B hconf hW
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)
  let K := ↥(centralizer ({β} : Set G))
  have htβ : t ∈ centralizer ({β} : Set G) := mem_centralizer_singleton_iff.2 hβt.symm
  have hyβ' : y ∈ centralizer ({β} : Set G) := mem_centralizer_singleton_iff.2 hyβ
  let DK : Subgroup K := (E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))
  have hDK_le : ∀ x : K, x ∈ DK → (x : G) ∈ E ∧ (x : G) ∈ centralizer ({β} : Set G) := fun x hx =>
    mem_subgroupOf.1 hx
  rcases hL64 with hZ2A6 | ⟨N₁, N₂, ⟨e₁⟩, ⟨e₂⟩, hcomm, hdisj, hnorm, hidx, hzN, hconj⟩
  · exact absurd hZ2A6 (hZ G L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt)
  · obtain ⟨d, hdD, hd⟩ := swap_inner_on_D_wreath (z := ⟨z, hz⟩) (t := ⟨t, htβ⟩)
      (y := ⟨y, hyβ'⟩) (Subtype.ext hcfg.z_sq) e₁ hcomm hdisj hidx hzN hconj
      (D := DK)
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ centralizer ({β} : Set G)
        ≤ centralizer ({β} : Set G))).toEquiv).trans hBD.1)
      (hE2.to_le (inf_le_left : E ⊓ centralizer ({β} : Set G) ≤ E)).comap_subtype hBD.2
      (fun x hx => Subtype.ext (hcfg.z_comm_of_mem_A
        (hconf.econfig.le.trans hcfg.T₀_le (hDK_le x hx).1)).symm)
      (mem_subgroupOf.2 ⟨hconf.econfig.t_mem, htβ⟩)
      (fun x hx => Subtype.ext (hcfg.t_central x (hconf.econfig.le (hDK_le x hx).1)).symm)
      (fun x hx => by
        obtain ⟨hxE, -⟩ := hDK_le x hx
        exact mem_subgroupOf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN (x : G)).1 hxE,
          (⟨y, hyβ'⟩ * x * ⟨y, hyβ'⟩⁻¹ : K).2⟩)
      (fun x hx => by
        obtain ⟨hxE, -⟩ := hDK_le x hx
        refine mem_subgroupOf.2 ⟨?_, (⟨y, hyβ'⟩⁻¹ * x * ⟨y, hyβ'⟩ : K).2⟩
        have h1 := (Subgroup.mem_normalizer_iff.1 hyN (y⁻¹ * (x : G) * y)).2 (by
          have : y * (y⁻¹ * (x : G) * y) * y⁻¹ = x := by group
          rw [this]
          exact hxE)
        exact h1)
      (Subtype.ext hyz)
    exact ⟨(d : G), mem_subgroupOf.1 hdD, fun e he =>
      congrArg Subtype.val (hd ⟨e, he.2⟩ (mem_subgroupOf.2 he))⟩

end CFSG.EvenSporadicStandard.Fin76b
