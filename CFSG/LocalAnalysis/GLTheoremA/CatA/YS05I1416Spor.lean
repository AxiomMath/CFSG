module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def I1416QSporS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      IsChevSimple q (PSimple p J) →
      (∃ A : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) → False

theorem i1416_elemAb_transfer {T U : Type} [Group T] [Group U] (φ : T ≃* U) {p : ℕ}
    (h : ∃ A : Subgroup (MulAut T), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    ∃ A : Subgroup (MulAut U), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A := by
  obtain ⟨A, hA, hle⟩ := h
  have hf : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  refine ⟨A.map (MulAut.congr φ).toMonoidHom, hA.map (MulAut.congr φ).toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective hf]
  exact hle

section AltCerts

theorem i1416AltSmall {G : Type} [Group G] [Finite G] {p : ℕ} {X K J : Subgroup G} {y : G} {n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : GLAPComponent p X K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ p = 1) (hncent : ¬ CentMod p K y)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hn : 5 ≤ n) (e : PSimple p K ≃* alternatingGroup (Fin n)) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (PSimple p J ≃* alternatingGroup (Fin m)) := by
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hJ' := glaPComponent_chevTransfer hp hyN hyp' hJ
  have hα : chevAut p K ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p K hyN hyp
  have hα1 : chevAut p K ⟨y, hyN⟩ ≠ 1 := fun h => hncent ((chevAut_eq_one_iff hp hK hyN).1 h)
  obtain ⟨hβI, ⟨e₁⟩⟩ := chevQ_transport hp e hJ'
  have hβ : MulAut.congr e (chevAut p K ⟨y, hyN⟩) ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e (chevAut p K ⟨y, hyN⟩) ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n p hn hp hp2 _ hβ hβ1 _ hβI
  obtain ⟨g₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp' hJ
  exact ⟨m, (le_max_left 5 p).trans hm, ⟨g₁.trans (e₁.trans f)⟩⟩

end AltCerts

end CFSG.LocalAnalysis.GLTheoremA
