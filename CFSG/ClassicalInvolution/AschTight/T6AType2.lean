module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem le_normalizer_of_commutator_le_oddCore {V J : Subgroup G} (h : ⁅V, J⁆ ≤ oddCoreOf J) :
    V ≤ Subgroup.normalizer (J : Set G) := by
  have key : ∀ v ∈ V, ∀ j ∈ J, v * j * v⁻¹ ∈ J := by
    intro v hv j hj
    have h1 : v * j * v⁻¹ * j⁻¹ ∈ J :=
      oddCoreOf_le_self J (h (Subgroup.commutator_mem_commutator hv hj))
    have e : v * j * v⁻¹ = (v * j * v⁻¹ * j⁻¹) * j := by group
    rw [e]
    exact J.mul_mem h1 hj
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨key v hv j, fun hj => ?_⟩
  have := key v⁻¹ (V.inv_mem hv) _ hj
  rwa [show v⁻¹ * (v * j * v⁻¹) * v⁻¹⁻¹ = j by group] at this

theorem omegaStarNbr_eq_empty_of_muIsoZ2 {Ω : Set (Subgroup G)} {W : Subgroup G}
    (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (he : DEdgeless Ω) (hZ : MuIsoZ2 Ω W) :
    ∀ J ∈ Ω, omegaStarNbr Ω J = ∅ := by
  intro J hJ
  by_contra hne
  obtain ⟨e₃⟩ := MuTab.muIsoS3_of_shape hP hW he ⟨J, hJ, Set.nonempty_iff_ne_empty.mpr hne⟩
  obtain ⟨e₂⟩ := hZ
  have h1 := Nat.card_congr (e₃.symm.trans e₂).toEquiv
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  omega

theorem allTypeTwo_of_omegaStarNbr_eq_empty {K : Subgroup G} {z : G} (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f (CoreAssembly.conjClass K))
    (he : DEdgeless (CoreAssembly.conjClass K))
    (hst : ∀ J ∈ CoreAssembly.conjClass K, omegaStarNbr (CoreAssembly.conjClass K) J = ∅)
    (hz : IsUniqueInvolution K z) : AllTypeTwo K z := by
  intro J hJ u w hu ⟨x, hx⟩ hwu _ Q hQ2 hQJ hQw
  have hL : conjSub x K ∈ CoreAssembly.conjClass K := ⟨x, rfl⟩
  have hLw : IsUniqueInvolution (conjSub x K) w := hx ▸ hz.conj x
  have hJL : J ≠ conjSub x K := by
    rintro rfl
    exact hwu (hLw.eq hu)
  have hJt : J ∉ twinSet (CoreAssembly.conjClass K) (conjSub x K) := by
    rintro ⟨-, z', h1, h2⟩
    exact hwu ((hLw.eq h1).trans (h2.eq hu))
  by_contra hQ
  push Not at hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at hQ
    omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy'
    omega
  have hy2 : (y : G) * y = 1 := by rw [← sq, ← hy', pow_orderOf_eq_one]
  have huQ : u ∈ Q := ((hu.unique y (hQJ y.2) hy2).resolve_left hy1) ▸ y.2
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ2 (le_inf hQJ hQw)
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  rcases l6_2 p f hp hq G _ hΩ (conjSub x K) hL w hLw J hJ hJt u hu V hV (hQV huQ) with
    ⟨hVe, -⟩ | ⟨hVe, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVc⟩
  · have h1 := Subgroup.card_le_of_le hQV
    rw [hVe, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hu.sq) hu.ne_one] at h1
    omega
  · have h1 := Subgroup.card_le_of_le hQV
    rw [hVe, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hu.sq) hu.ne_one] at h1
    omega
  · have hmem : J ∈ omegaStarNbr (CoreAssembly.conjClass K) (conjSub x K) :=
      ⟨hJ, hJL, V, hVU, hVJ, hVN⟩
    rw [hst _ hL] at hmem
    exact hmem
  · have hmem : J ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub x K) :=
      ⟨hJ, hJL, V, hVR, hVJ, le_normalizer_of_commutator_le_oddCore hVc⟩
    exact he _ hL J hJ (Or.inl hmem)

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
