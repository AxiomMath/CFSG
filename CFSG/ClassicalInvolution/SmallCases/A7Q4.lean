module

public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

namespace CFSG.ClassicalInvolution.A7Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_twin_mem_oddCoreOf (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {L : Subgroup G} (hL : L ∈ twinSet Ω K)
    (hsub : IsSubnormal L (Subgroup.centralizer ({z} : Set G))) :
    ∀ ℓ ∈ L, ⁅t, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  have hzL := isUniqueInvolution_of_mem_twinSet h.hz hL
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 L hL
  have hRsyl : IsSylow2In R J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ h.hJ.1 hR hRJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hzL hRN
  have hJnot : J ∉ twinSet Ω L := by
    rintro ⟨-, z₀, hz₀L, hz₀J⟩
    exact h.t_ne_z ((h.ht.eq hz₀J).trans (hzL.eq hz₀L).symm)
  have hV : IsSylow2In R (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hRJ hRC, hRsyl.2.1, fun V' hV' hV'p hRV' =>
      hRsyl.2.2 V' (hV'.trans inf_le_left) hV'p hRV'⟩
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ L hL.1 z hzL J h.hJ.1 hJnot t h.ht R hV htR with
    h1 | h1 | h1 | h1
  · rw [h1.1, Nat.card_zpowers, htord] at h8
    omega
  · rw [h1.1, Nat.card_zpowers, htord] at h8
    omega
  · exfalso
    obtain ⟨R', -, -, hcyc, -⟩ := h1.1
    obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_not_commute
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥R)
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have hc : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      rw [← ha, ← hb]
      exact (Commute.zpow_zpow_self g a b).eq
    exact hxy (congrArg Subtype.val hc)
  · intro ℓ hℓ
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub
      (h1.2 (Subgroup.commutator_mem_commutator htR hℓ))

end Gen

end CFSG.ClassicalInvolution.A7Q
