module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open Equiv

theorem congr_conj {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z) (g : Y) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem no911_alt {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) : No911 Y := by
  rintro p V z ⟨hp, hpodd, -, hVc, hz1, hzz, hVz, ⟨O, hOH, hVO, hOodd, hOz, hON⟩, -⟩
  let c : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)
  let φ : MulAut Y ≃* Perm (Fin n) := (MulAut.congr e).trans c.symm
  have hφconj : ∀ g : Y, φ (MulAut.conj g) = ((e g : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro g
    show c.symm (MulAut.congr e (MulAut.conj g)) = _
    rw [congr_conj, MulEquiv.symm_apply_eq]
    ext x
    simp [c, MulAut.conjNormal_apply, MulAut.conj_apply]
  let H' : Subgroup (Perm (Fin n)) := (hbar Y V z).map φ.toMonoidHom
  have hinn : (MulAut.conj : Y →* MulAut Y).range ≤ hbar Y V z := le_trans le_sup_left le_sup_left
  have hAH : alternatingGroup (Fin n) ≤ H' := by
    intro a ha
    refine ⟨MulAut.conj (e.symm ⟨a, ha⟩), hinn ⟨e.symm ⟨a, ha⟩, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hφconj]
    simp
  have hzH : z ∈ hbar Y V z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let z' : Perm (Fin n) := φ z
  have hz'2 : orderOf z' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  let C' : Subgroup (Perm (Fin n)) := H' ⊓ centralizer ({z'} : Set (Perm (Fin n)))
  let O' : Subgroup (Perm (Fin n)) := O.map φ.toMonoidHom
  have hO'C : O' ≤ C' := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨⟨o, hOH ho, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    show φ o * z' = z' * φ o
    rw [← map_mul, ← map_mul, hOz o ho]
  have hnorm : (O'.subgroupOf C').Normal := by
    refine ⟨fun n' hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    obtain ⟨o, ho, hoeq⟩ := hn'
    obtain ⟨⟨c0, hc0, hc0eq⟩, hgz⟩ := g.2
    have hgz' : z' * (g : Perm (Fin n)) = (g : Perm (Fin n)) * z' :=
      Subgroup.mem_centralizer_iff.mp
        (show (g : Perm (Fin n)) ∈ centralizer ({z'} : Set (Perm (Fin n))) from hgz) z'
        (Set.mem_singleton z')
    have hc0z : c0 * z = z * c0 := by
      apply φ.injective
      rw [map_mul, map_mul]
      rw [MulEquiv.coe_toMonoidHom] at hc0eq
      rw [hc0eq]
      exact hgz'.symm
    refine ⟨c0 * o * c0⁻¹, hON c0 hc0 hc0z o ho, ?_⟩
    rw [MulEquiv.coe_toMonoidHom] at hoeq hc0eq ⊢
    rw [map_mul, map_mul, map_inv, hoeq, hc0eq]
    rfl
  have hcardO' : Nat.card ↥(O'.subgroupOf C') = Nat.card ↥O := by
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'C).toEquiv).trans ?_
    exact Nat.card_congr (Subgroup.equivMapOfInjective O φ.toMonoidHom φ.injective).toEquiv.symm
  have hle : O'.subgroupOf C' ≤ CFSG.oddCore ↥C' :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hnorm (hcardO' ▸ hOodd)
  have hcore := ComponentClassification.SymmetricLocal.involution_permutation_centralizer_odd_core
    hAH hz'2
  have hle3 : Nat.card ↥(O'.subgroupOf C') ≤ 3 := by
    by_cases h3 : Nat.card {ω // z' ω = ω} = 3
    · exact (Subgroup.card_le_of_le hle).trans (hcore.2 h3).2.1.le
    · have := hcore.1 h3
      rw [this] at hle
      have hb := le_bot_iff.mp hle
      rw [hb, Subgroup.card_bot]
      norm_num
  have hVle : Nat.card ↥V ≤ Nat.card ↥O :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hVO)
  rw [hVc, ← hcardO'] at hVle
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  nlinarith

theorem core911_alt : Core911Alt := by
  intro Y _ _ hs hna h
  obtain ⟨n, hn7, hn11, ⟨e⟩⟩ := h
  exact no911_alt (by omega) (by omega) e

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
