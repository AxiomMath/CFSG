module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  {EY : Subgroup (MulAut (↥L ⧸ center ↥L))}

namespace PullHyp

variable (h : PullHyp G L z t T EY)

include h in
theorem card_aut_pullE : Nat.card (MulAut ↥(pullE L EY)) = 1920 := by
  obtain ⟨e⟩ := h.equiv_EY_pullE
  rw [← Nat.card_congr (MulAut.congr e).toEquiv]
  exact h.facts.card_aut

include h in
theorem card_T : Nat.card ↥T = 512 := by
  let TH : Subgroup ↥(centralizer ({z} : Set G)) := T.subgroupOf (centralizer ({z} : Set G))
  let g : ↥TH →* MulAut (↥L ⧸ center ↥L) := (thetaH h.cfg.cent_le).domRestrict TH
  have hrange : g.range = (T.subgroupOf (centralizer ({z} : Set G))).map
      (thetaH h.cfg.cent_le) := MonoidHom.domRestrict_range TH (thetaH h.cfg.cent_le)
  have hker : Nat.card g.ker = 2 := by
    have e : ↥g.ker ≃ ↥(zpowers z) := by
      refine Equiv.ofBijective (fun x => ⟨((x.1 : ↥TH) : ↥(centralizer ({z} : Set G))).1,
        (h.ker _).1 (MonoidHom.mem_ker.1 x.2)⟩) ⟨?_, ?_⟩
      · intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext (Subtype.ext this))
      · rintro ⟨w, hw⟩
        have hwT : w ∈ T := by
          obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
          rw [← hk]
          exact zpow_mem h.cfg.z_mem k
        have hwH : w ∈ centralizer ({z} : Set G) := h.cfg.T_le hwT
        refine ⟨⟨⟨⟨w, hwH⟩, mem_subgroupOf.2 hwT⟩, ?_⟩, rfl⟩
        exact MonoidHom.mem_ker.2 ((h.ker ⟨w, hwH⟩).2 hw)
    rw [Nat.card_congr e, Nat.card_zpowers, h.cfg.z_order]
  have hmain := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, hrange, hker, h.facts.card_S] at hmain
  have hTT : Nat.card ↥T = Nat.card ↥TH :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.cfg.T_le).toEquiv).symm
  rw [hTT, ← hmain]

end PullHyp

variable [Finite G]

end CFSG.EvenSporadicStandard.Fin76b
