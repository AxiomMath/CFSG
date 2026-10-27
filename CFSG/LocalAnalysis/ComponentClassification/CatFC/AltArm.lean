module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem parity_of_involution (n : ℕ) (τ : Equiv.Perm (Fin n)) (h : τ * τ = 1) :
    n ≡ (Finset.univ.filter fun x => τ x = x).card [MOD 2] := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End (Fin n) := ⇑τ
  have h2 : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) h
    exact this
  have h3 := Equiv.Perm.card_fixedPoints_modEq h2
  have hset : Function.fixedPoints f = ↑(Finset.univ.filter fun x => τ x = x) := by
    ext x
    simp [Function.mem_fixedPoints, Function.IsFixedPt, f]
  have h4 : Nat.card ↥(Function.fixedPoints f) = (Finset.univ.filter fun x => τ x = x).card := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h4] at h3
  simpa using h3

theorem alt_arm {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) :
    ∃ k : ℕ, 5 ≤ k ∧ k + 2 ≤ n ∧ Even (n - k) ∧
      Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin k)) := by
  classical
  have hσ2' : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ2 : ∀ y, σ (σ y) = y := fun y => congrArg (fun φ : MulAut S => φ y) hσ2'
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by decide)
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup S, P = D.map (fixedSubgroup σ).subtype := ⟨_, rfl⟩
  have hPF : P ≤ fixedSubgroup σ := hPdef ▸ Subgroup.map_subtype_le D
  have hPD : P.subgroupOf (fixedSubgroup σ) = D :=
    hPdef ▸ Subgroup.comap_map_eq_self_of_injective (fixedSubgroup σ).subtype_injective D
  have hP2 : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) := by
    rw [hPD]
    exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hPne : P ≠ ⊤ := by
    intro htop
    apply hσ1
    ext x
    have hx : x ∈ fixedSubgroup σ := hPF (htop ▸ Subgroup.mem_top x)
    exact hx
  have h : ProperFixedComponent σ P := ⟨hσ2, hPF, hP2, hPne⟩
  obtain ⟨h', hθ⟩ := h.map θ
  obtain ⟨τ, hτ2, -, hdeg, ⟨eA⟩⟩ :=
    exists_involution_of_properFixedComponent_alternating hn hn6 h'
  have hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) := by
    rw [hPD]
    exact hD.1
  obtain ⟨-, ⟨eP⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  obtain ⟨eθ⟩ := hθ
  let eD : (P.subgroupOf (fixedSubgroup σ)) ⧸ center (P.subgroupOf (fixedSubgroup σ)) ≃*
      ↥D ⧸ center ↥D :=
    quotientCenterEquiv (MulEquiv.subgroupCongr hPD)
  set k : ℕ := (Finset.univ.filter fun x => τ x = x).card with hk
  have hττ : τ * τ = 1 := by rw [← sq, ← hτ2, pow_orderOf_eq_one]
  have hmod := parity_of_involution n τ hττ
  have hkn : k ≠ n := by
    intro hkn
    have hfilter : (Finset.univ.filter fun x => τ x = x) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [← hk, hkn, Fintype.card_fin])
    have hτ1 : τ = 1 := by
      refine Equiv.ext fun x => ?_
      have hx : x ∈ Finset.univ.filter fun x => τ x = x := by
        rw [hfilter]
        exact Finset.mem_univ x
      exact (Finset.mem_filter.1 hx).2.trans (Equiv.Perm.one_apply x).symm
    rw [hτ1, orderOf_one] at hτ2
    exact absurd hτ2 (by decide)
  have hkle : k ≤ n := by
    rw [hk]
    simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun x => τ x = x)
  have hmod' : n % 2 = k % 2 := hmod
  refine ⟨k, hdeg, by omega, ⟨(n - k) / 2, by omega⟩, ?_⟩
  let eΩ : ↥(Finset.univ.filter fun x => τ x = x) ≃ Fin k :=
    Fintype.equivFinOfCardEq (Fintype.card_coe _)
  exact ⟨eD.symm.trans (eP.symm.trans (eθ.trans (eA.trans eΩ.altCongrHom)))⟩

end CFSG.ComponentClassification.CatFC
