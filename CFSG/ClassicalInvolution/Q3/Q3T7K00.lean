module

public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7FUK0

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem HM.isClassicalMember3 (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : Q3.IsClassicalMember3 K z := by
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have h3 := hz'.toQ3 (by norm_num)
  have hz'2 : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [h3.orderOf_eq_two, pow_two] at this
  have : z' = z := (hz.unique z' h3.mem hz'2).resolve_left h3.ne_one
  rwa [this] at h3

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU {G : Type} [Group G] {Ω : Set (Subgroup G)} (hΩ : CFSG.ClassicalInvolution.Q3.Q3T7M.HM Ω) :
    CFSG.ClassicalInvolution.T7FU.HM (.sl2 3 1) Ω :=
  { toMod := hΩ, toGen := CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toGen hΩ }

namespace CentQ

theorem natCard_conjSub_eq (n : G) (H : Subgroup G) :
    Nat.card ↥(conjSub n H) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).symm.toEquiv

theorem le_centralizer_of_uniq {M : Subgroup G} {z : G} (hM : IsUniqueInvolution M z) :
    M ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hM.commute_of_mem hw).symm

theorem centralizer_eq_of_central {z t : G} (hc : t⁻¹ * z ∈ Subgroup.center G) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.centralizer ({z} : Set G) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.centralizer_eq_of_central hc

theorem comm_sylow_le_oddCoreOf (hΩ : HM Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt' : z ≠ t)
    (hzt : t⁻¹ * z ∈ X) {V : Subgroup G} (hV : IsSylow2In V J) : ⁅V, K⁆ ≤ oddCoreOf K :=
  CFSG.ClassicalInvolution.T7FU.CentQ.comm_sylow_le_oddCoreOf
    (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) h62 hXc hK hJ hz ht hzt' hzt hV

theorem conjSub_eq_of_mem_oddCore (hΩ : HM Ω) {M : Subgroup G} {z : G} (hM : M ∈ Ω)
    (hz : IsUniqueInvolution M z) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) : conjSub n M = M :=
  CFSG.ClassicalInvolution.T7FU.CentQ.conjSub_eq_of_mem_oddCore
    (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) hM hz hn

theorem isSylow2In_sup_of_odd {N Q A : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hQN0 : Q ⊓ N = ⊥)
    (hA2 : IsPGroup 2 A) (hAle : A ≤ Q ⊔ N) (hcard : Nat.card Q ≤ Nat.card A) :
    IsSylow2In A (Q ⊔ N) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.isSylow2In_sup_of_odd hQN hN hQN0 hA2 hAle hcard

theorem exists_conjSub_of_le_sup_odd {N Q Q' : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hQN0 : Q ⊓ N = ⊥)
    (hQ2 : IsPGroup 2 Q) (hQ'2 : IsPGroup 2 Q') (hcard : Nat.card Q' = Nat.card Q)
    (hle : Q' ≤ N ⊔ Q) : ∃ n ∈ N, conjSub n Q = Q' :=
  CFSG.ClassicalInvolution.T7FU.CentQ.exists_conjSub_of_le_sup_odd hQN hN hQN0 hQ2 hQ'2 hcard hle

theorem le_normalizer_of_congr (hΩ : HM Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt' : z ≠ t)
    (hzt : t⁻¹ * z ∈ X) : J ≤ Subgroup.normalizer (K : Set G) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.le_normalizer_of_congr
    (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) h62 hXc hK hJ hz ht hzt' hzt

theorem commutes_of_congr (hΩ : HM Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hzt : t⁻¹ * z ∈ X) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
  CFSG.ClassicalInvolution.T7FU.CentQ.commutes_of_congr
    (CFSG.ClassicalInvolution.Q3.Q3T7M.HM.toU hΩ) h62 hXc hK hJ hKJ hz ht hzt

end CentQ

end CFSG.ClassicalInvolution.Q3.Q3T7M
