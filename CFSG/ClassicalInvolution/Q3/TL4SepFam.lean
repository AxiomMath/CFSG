module

public import CFSG.ClassicalInvolution.Q3.TL4SepSub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

structure TightFam (r : ℕ) (G : Type) [Group G] (Δ : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Δ
  inv : ∀ J ∈ Δ, ∃ u : G, IsUniqueInvolution J u
  gen : ∀ J ∈ Δ, Subgroup.closure {x : G | x ∈ J ∧ IsPGroup 2 (Subgroup.zpowers x)} = J
  twoGroup : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  quat : ∀ J ∈ Δ, ∀ P : Subgroup G, IsSylow2In P J →
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  tight : ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u →
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)
  noTwins : ∀ J ∈ Δ, ∀ J' ∈ Δ, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u →
    J = J'

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem TightFam.not_two_dvd_card_inf (h : TightFam r G Δ) {K J : Subgroup G} (hK : K ∈ Δ)
    (hJ : J ∈ Δ) (hne : K ≠ J) : ¬ 2 ∣ Nat.card ↥(K ⊓ J) := by
  intro h2
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hwo : orderOf w = 2 := by
    rw [← Subgroup.orderOf_mk w hw]
    exact hw2
  have hw2' : w * w = 1 := by
    rw [← pow_two, ← hwo]
    exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hwo
    omega
  obtain ⟨u, hu⟩ := h.inv K hK
  obtain ⟨v, hv⟩ := h.inv J hJ
  have h1 : w = u := (hu.unique w hw.1 hw2').resolve_left hw1
  have h2' : w = v := (hv.unique w hw.2 hw2').resolve_left hw1
  exact hne (h.noTwins K hK J hJ u hu (h1 ▸ h2' ▸ hv))

theorem TightFam.hypOmegaGen (h : TightFam r G Δ) (hr : 3 ≤ r) : HypOmegaGen Δ where
  conjInvariant := h.conjInvariant
  omega1 := by
    intro K hK
    refine ⟨h.inv K hK, ?_⟩
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
      (bot_le : ⊥ ≤ K)
    refine ⟨P, hP, fun hc => ?_⟩
    obtain ⟨e⟩ := h.quat K hK P hP
    have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
    have h2 : 2 ≤ 2 ^ (r - 2) :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨a, b, hab⟩ := Nobq.exists_not_commute_of_mulEquiv_quaternionGroup h2 e
    exact hab (hc.is_comm.comm a b)
  omega2 := fun K hK => Or.inl (h.gen K hK)
  omega3 := by
    intro K hK J hJ P Q hP hQ
    obtain ⟨e₁⟩ := h.quat K hK P hP
    obtain ⟨e₂⟩ := h.quat J hJ Q hQ
    exact (Nat.card_congr e₁.toEquiv).trans (Nat.card_congr e₂.toEquiv).symm
  omega4 := by
    intro K hK J hJ hne
    have h0 : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 0 :=
      padicValNat.eq_zero_of_not_dvd (h.not_two_dvd_card_inf hK hJ hne)
    rw [h0]
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  omega5 := by
    intro K hK J _ _ z hz v _ _ _ hvz
    exact h.tight K hK z hz (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem TightFam.toT4Hyp (h : TightFam r G Δ) (hr : 3 ≤ r)
    (hO : classicalInvolutionOddCore G = ⊥) : T4Hyp r G Δ :=
  T4Hyp.of_noTwins (h.hypOmegaGen hr) h.twoGroup h.quat h.tight h.noTwins hO

end CFSG.ClassicalInvolution.Q3.TL4
