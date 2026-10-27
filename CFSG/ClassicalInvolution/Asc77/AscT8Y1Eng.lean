module

public import CFSG.ClassicalInvolution.Asc77.AscT8MinProof

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerJoin_conjSub_eqE {x n : G}
    (hconj : ∀ {L : Subgroup G} {m : G}, L ∈ layerSet Ω x → m ∈ cenZ x → conjSub m L ∈ layerSet Ω x)
    (hn : n ∈ cenZ x) : conjSub n (layerJoin Ω x) = layerJoin Ω x := by
  have key : ∀ d ∈ cenZ x, conjSub d (layerJoin Ω x) ≤ layerJoin Ω x := by
    intro d hd
    unfold layerJoin
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_layerJoin (hconj hL hd)
  refine le_antisymm (key n hn) ?_
  have h := conjSub_mono (n := n) (key n⁻¹ ((cenZ x).inv_mem hn))
  rwa [conjSub_conjSub_inv] at h

theorem oddCoreOf_layerJoin_le_of_good_pairE {x u v : G} {J : Subgroup G}
    (hgood : ∀ {E J₀ : Subgroup G}, IsMulCommutative E → (∀ w ∈ E, w ^ 2 = 1) → 4 ≤ Nat.card E →
      E ≤ cenZ x → (∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ J₀) →
        oddCoreOf (layerJoin Ω x) ≤ J₀)
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hne : u ≠ v) (hux : u ∈ cenZ x) (hvx : v ∈ cenZ x)
    (hgu : Subgroup.centralizer ({u} : Set G) ≤ J) (hgv : Subgroup.centralizer ({v} : Set G) ≤ J)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ J) :
    oddCoreOf (layerJoin Ω x) ≤ J := by
  refine hgood (E := Subgroup.closure ({u, v} : Set G))
    ⟨⟨fun a b => Subtype.ext (closure_pair_mul_comm huv a.2 b.2)⟩⟩
    (fun w hw => closure_pair_sq hu hv huv hw)
    (four_le_natCard_closure_pair hu hu1 hv1 hne) ?_ ?_
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hux
    · exact hvx
  · intro e he he1
    rcases mem_closure_pair_involutions hu hv huv he with h | h | h | h
    · exact absurd h he1
    · rw [h]
      exact hgu
    · rw [h]
      exact hgv
    · rw [h]
      exact hguv

end T8

end CFSG.ClassicalInvolution.Asc77
