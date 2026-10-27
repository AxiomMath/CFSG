module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem starNbr_of_exists (hΦ : ConjInvariant Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h : ∃ L₀ ∈ Φ, ∃ L₁ ∈ omegaStarNbr Φ L₀, L₁ ∉ omegaNbr Φ L₀) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨L₀, hL₀, L₁, hs, hn⟩ := h
  intro L hL
  obtain ⟨g, rfl⟩ := htr L₀ hL₀ L hL
  have hs' := omegaStarNbr_conj hΦ hs g
  refine ⟨conjSub g L₁, hs'.1, hs', fun h' => hn ?_⟩
  have h'' := omegaNbr_conj hΦ h' g⁻¹
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h''

theorem exists_starNbr_of_dstarConn
    (hconn : ∀ K ∈ Φ, ∀ J ∈ Φ, Relation.ReflTransGen (dstarAdj Φ) K J)
    (hD : ¬ Disconnected.DConnected Φ) :
    ∃ L₀ ∈ Φ, ∃ L₁ ∈ omegaStarNbr Φ L₀, L₁ ∉ omegaNbr Φ L₀ := by
  by_contra hno
  push Not at hno
  apply hD
  intro K hK J hJ
  have key : ∀ N, Relation.ReflTransGen (dstarAdj Φ) K N → N ∈ Φ ∧
      Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ Disconnected.dAdj Φ M N) K N := by
    intro N hN
    induction hN with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | @tail M N _ hMN ih =>
      refine ⟨hMN.1, ih.2.tail ⟨hMN.1, ?_⟩⟩
      rcases hMN.2 with h | h
      · exact Or.inl (hno M ih.1 N h)
      · exact Or.inr (hno N hMN.1 M h)
  exact (key J (hconn K hK J hJ)).2

theorem starNbr_of_dEdgeless (hΦ : ConjInvariant Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (hE : Disconnected.DEdgeless Φ)
    (h1 : ∃ L ∈ Φ, (omegaStarNbr Φ L).Nonempty) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨L₀, hL₀, L₁, hs⟩ := h1
  exact starNbr_of_exists hΦ htr ⟨L₀, hL₀, L₁, hs, fun hn => hE L₀ hL₀ L₁ hs.1 (Or.inl hn)⟩

theorem starNbr_of_exitS3 (hΦ : ConjInvariant Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (h : SecIdExitS3 Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L :=
  starNbr_of_dEdgeless hΦ htr h.1 h.2.1

end CFSG.ClassicalInvolution.Q3.TL4
