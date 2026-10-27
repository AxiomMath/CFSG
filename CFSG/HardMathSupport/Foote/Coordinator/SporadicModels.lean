module

public import CFSG.HardMathSupport.Foote.Coordinator.SporadicBase
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95M12
public import CFSG.Mathlib.GroupTheory.PerfectSubnormalIndex
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.Blueprint Subgroup
open CFSG.GH74.GLS.IVK CFSG.Sporadic.Schreier
open scoped commutatorElement

section Criteria

variable {Q : Type} [Group Q] {w : Q} {K : Subgroup Q}

theorem InnerComp5.commutator_eq (h : InnerComp5 Q w K) : ⁅K, K⁆ = K := by
  obtain ⟨e⟩ := h.sl5
  have hp : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = ⊤ :=
    isQuasisimple_sl25.1.commutator_eq_top
  let f : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* Q := K.subtype.comp e.symm.toMonoidHom
  have hrange : f.range = K := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hp]

theorem InnerComp5.card_eq (h : InnerComp5 Q w K) : Nat.card ↥K = 120 := by
  obtain ⟨e⟩ := h.sl5
  exact CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm

theorem InnerComp5.false_of_derived_le [Finite Q] (h : InnerComp5 Q w K) {F : Subgroup Q}
    (hF : Nat.card ↥F < 120)
    (hD : ∀ a ∈ centralizer ({w} : Set Q), ∀ b ∈ centralizer ({w} : Set Q), ⁅a, b⁆ ∈ F) :
    False := by
  have hKF : K ≤ F := by
    rw [← h.commutator_eq]
    exact Subgroup.commutator_le.mpr fun a ha b hb => hD a (h.le ha) b (h.le hb)
  have h1 : Nat.card ↥K ≤ Nat.card ↥F := Subgroup.card_le_of_le hKF
  rw [h.card_eq] at h1
  omega

theorem InnerComp5.false_of_model_class [Finite Q] (h : InnerComp5 Q w K) {M : Type} [Group M]
    {P R A : Subgroup M} {tX : M} (hM : Ivk73Model P R A tX) (θ : Q ≃* ↥P) {g : M}
    (hg : g ∈ R) (hgt : ((θ w : ↥P) : M) = g * tX * g⁻¹) : False := by
  have hnorm : ∀ x ∈ P, g * x * g⁻¹ ∈ P := hM.autModel.conj_mem g hg
  have hnorm' : ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun x hx => by
    simpa using hM.autModel.conj_mem g⁻¹ (R.inv_mem hg) x hx
  let ι : Q →* M := P.subtype.comp θ.toMonoidHom
  have hι : Function.Injective ι := fun a b hab => θ.injective (Subtype.ext hab)
  let A' : Subgroup M := A.map (MulAut.conj g).toMonoidHom
  have hcent := GHInv.map_conj_centralizerIn_of_norm hnorm hnorm' tX
  have hmem : ∀ x ∈ centralizer ({w} : Set Q),
      ι x ∈ (centralizerIn P tX).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    rw [hcent, mem_centralizerIn]
    refine ⟨(θ x).2, ?_⟩
    rw [← hgt]
    have := mem_centralizer_singleton_iff.mp hx
    have h2 : θ x * θ w = θ w * θ x := by rw [← map_mul, ← map_mul, this]
    exact congrArg Subtype.val h2
  refine h.false_of_derived_le (F := A'.comap ι) ?_ ?_
  · have hfinA : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hM.card_A]; norm_num)
    have hfinA' : Finite ↥A' :=
      Finite.of_equiv ↥A (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv
    have h1 : Nat.card ↥(A'.comap ι) ≤ Nat.card ↥A' :=
      Nat.card_le_card_of_injective (fun x => (⟨ι x.1, x.2⟩ : ↥A'))
        (fun a b hab => by
          apply Subtype.ext
          have h3 := congrArg Subtype.val hab
          exact hι h3)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hM.card_A] at h1
    omega
  · intro x hx y hy
    obtain ⟨a, ha, hax⟩ := hmem x hx
    obtain ⟨b, hb, hby⟩ := hmem y hy
    show ι ⁅x, y⁆ ∈ A'
    rw [map_commutatorElement, ← hax, ← hby]
    refine ⟨⁅a, b⁆, hM.derived a ha b hb, ?_⟩
    simp [commutatorElement_def, MulAut.conj_apply]
    group

end Criteria

theorem InnerComp5.false_of_perfect {Q : Type} [Group Q] [Finite Q] {w : Q} {K : Subgroup Q}
    (h : InnerComp5 Q w K) (hperf : Group.IsPerfect ↥(centralizer ({w} : Set Q)))
    (hN : Nat.card ↥(centralizer ({w} : Set Q)) = 1920) : False := by
  set B := K.subgroupOf (centralizer ({w} : Set Q)) with hB
  have hBcard : Nat.card ↥B = 120 := by
    rw [hB, ← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hidx : B.index = 2 ^ 4 := by
    have := Subgroup.card_mul_index B
    rw [hBcard, hN] at this
    omega
  have htop := h.comp.2.eq_top_of_index_eq_prime_pow hperf Nat.prime_two 4 hidx
  have : Nat.card ↥B = Nat.card ↥(centralizer ({w} : Set Q)) := by
    rw [hB, htop, Subgroup.card_top]
  omega

theorem InnerComp5.dvd_card_centralizer {Q : Type} [Group Q] {w : Q} {K : Subgroup Q}
    (h : InnerComp5 Q w K) : 120 ∣ Nat.card ↥(centralizer ({w} : Set Q)) := by
  rw [← h.card_eq]
  exact Subgroup.card_dvd_of_le h.le

theorem end415K_J2
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.J2) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  let θ : Q ≃* ↥j2P := eQ.trans j2PermEquiv
  rcases CFSG.GH74.GLS.IVK.Proofs2.j2_inv_cases ((θ w : ↥j2P) : Equiv.Perm (Fin 315)) (θ w).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact h.orderOf_eq) with
    ⟨hperf, hcard⟩ | ⟨g, hg, hgt⟩
  · have hperfQ := GHInv.isPerfect_centralizer_of_equiv j2P θ w (Subgroup.isPerfect_iff.1 hperf)
    have hc : Nat.card ↥(centralizer ({w} : Set Q)) = 1920 := by
      rw [GHInv.card_centralizer_eq_centralizerIn j2P θ w]
      exact hcard
    exact h.false_of_perfect hperfQ hc
  · exact h.false_of_model_class CFSG.GH74.GLS.IVK.j2_model θ hg hgt

theorem end415K_J3
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.J3) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  let θ : Q ≃* ↥j3P := eQ.trans j3PermEquiv
  have hord : orderOf ((θ w : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.orderOf_eq
  obtain ⟨hperf, hcard⟩ := j3_inner_centralizer_data _ (θ w).2 hord
  have hperfQ := GHInv.isPerfect_centralizer_of_equiv j3P θ w hperf
  have hc : Nat.card ↥(centralizer ({w} : Set Q)) = 1920 := by
    rw [GHInv.card_centralizer_eq_centralizerIn j3P θ w]
    exact hcard
  exact h.false_of_perfect hperfQ hc

theorem end415K_M12
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.M12) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  let θ : Q ≃* ↥CFSG.ComponentClassification.M12Cover.blockGroup := eQ.trans m12EquivD
  rcases CFSG.GH74.GLS.IVK.Proofs2.m12_inv_cases
      ((θ w : ↥CFSG.ComponentClassification.M12Cover.blockGroup) : Equiv.Perm (Fin 24)) (θ w).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact h.orderOf_eq) with
    ⟨g, hg, hgt⟩ | h192
  · exact h.false_of_model_class m12_model θ hg hgt
  · have hcard : Nat.card ↥(centralizer ({w} : Set Q)) = 192 := by
      rw [GHInv.card_centralizer_eq_centralizerIn _ θ w]
      exact h192
    have := h.dvd_card_centralizer
    rw [hcard] at this
    omega

end CFSG.HardMathSupport.Foote.Coordinator
