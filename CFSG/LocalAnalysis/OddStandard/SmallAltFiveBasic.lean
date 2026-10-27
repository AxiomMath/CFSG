module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_le_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {X Q Q' : Subgroup G}
    (hQX : Q ≤ X) (hQ : Nat.card Q = p ^ (Nat.card X).factorization p) (hQ'X : Q' ≤ X)
    (hQ' : IsPGroup p Q') (hle : Q ≤ Q') : Q' = Q := by
  have hcard : Nat.card (Q.subgroupOf X) = p ^ (Nat.card X).factorization p := by
    rw [← hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv
  have h : Q'.subgroupOf X = Q.subgroupOf X := by
    have := (Sylow.ofCard _ hcard).is_maximal' (Q := Q'.subgroupOf X) hQ'.comap_subtype
      (by rw [Sylow.coe_ofCard]; exact fun x hx => hle hx)
    rwa [Sylow.coe_ofCard] at this
  rwa [subgroupOf_inj, inf_of_le_left hQ'X, inf_of_le_left hQX] at h

theorem card_eq_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {X T : Subgroup G}
    (hTX : T ≤ X) (hT : Nat.card T = p ^ (Nat.card X).factorization p)
    (hN : normalizer (T : Set G) ≤ X) : Nat.card T = p ^ (Nat.card G).factorization p := by
  obtain ⟨V, hTV⟩ := (IsPGroup.of_card hT).exists_le_sylow
  suffices hTV' : T = V by rw [hTV', Sylow.card_eq_multiplicity]
  by_contra hne
  have hlt : T.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hTV fun v hv => ?_)
    have : (⟨v, hv⟩ : V) ∈ T.subgroupOf V := h ▸ mem_top _
    exact this
  have : Group.IsNilpotent (V : Subgroup G) := V.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hTV] at hyN
  have hW := eq_of_le_of_isPGroup hTX hT (sup_le hTX (zpowers_le.mpr (hN hyN)))
    (V.isPGroup'.to_le (sup_le hTV (zpowers_le.mpr y.2))) le_sup_left
  exact hyT (hW ▸ mem_sup_right (mem_zpowers (y : G)) : (y : G) ∈ T)

theorem exists_mem_normalizer_conj [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {x y g : G} (hx : ∀ u ∈ (T : Subgroup G), u * x = x * u)
    (hy : ∀ u ∈ (T : Subgroup G), u * y = y * u) (hg : g⁻¹ * x * g = y) :
    ∃ n ∈ normalizer ((T : Subgroup G) : Set G), n⁻¹ * x * n = y := by
  subst hg
  obtain ⟨n, hn, h⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer x g
    (mem_centralizer_iff.mpr hx) (mem_centralizer_iff.mpr hy)
  exact ⟨n, hn, h.symm⟩

theorem hom_eq_one_of_factorization [Group.IsPerfect G] {H N : Subgroup G} [N.Normal]
    (hfac : ∀ g : G, ∃ c ∈ H, ∃ k ∈ N, g = c * k) {A : Type*} [CommGroup A] (ψ : H →* A)
    (hψ : ∀ h : H, (h : G) ∈ N → ψ h = 1) : ψ = 1 := by
  set f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype with hf_def
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [hf_def, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    simpa using hk
  have hker : f.ker ≤ ψ.ker := fun h hh => by
    rw [MonoidHom.mem_ker] at hh ⊢
    exact hψ h ((QuotientGroup.eq_one_iff _).mp hh)
  let Ψ : G →* A := (f.liftOfSurjective hf ⟨ψ, hker⟩).comp (QuotientGroup.mk' N)
  ext h
  have h1 : Ψ h = 1 :=
    Abelianization.commutator_subset_ker Ψ Group.IsPerfect.mem_commutator
  rw [MonoidHom.one_apply, ← h1]
  exact (MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨ψ, hker⟩ h).symm

theorem card_inf_eq_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {X N Q : Subgroup G}
    (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal) (hQX : Q ≤ X)
    (hQ : Nat.card Q = p ^ (Nat.card X).factorization p) :
    Nat.card (Q ⊓ N : Subgroup G) = p ^ (Nat.card N).factorization p := by
  set Q' := Q.subgroupOf X
  set K := N.subgroupOf X
  have hcard : Nat.card Q' = p ^ (Nat.card X).factorization p := by
    rw [← hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv
  have hS : ¬ p ∣ Q'.index := by
    have := (Sylow.ofCard Q' hcard).not_dvd_index
    rwa [Sylow.coe_ofCard] at this
  have hdvd : Q'.relIndex K ∣ Q'.index := by
    have h1 : Q'.relIndex K * K.index = (Q' ⊓ K).index := by
      have h := relIndex_inf_mul_relIndex Q' K ⊤
      rwa [inf_top_eq, relIndex_top_right, relIndex_top_right] at h
    have h2 : (Q' ⊓ K).relIndex Q' * Q'.index = (Q' ⊓ K).index :=
      relIndex_mul_index inf_le_left
    rw [inf_relIndex_left] at h2
    obtain ⟨m, hm⟩ := relIndex_dvd_index_of_normal K Q'
    have hpos : K.relIndex Q' ≠ 0 := index_ne_zero_of_finite
    refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) ?_⟩
    rw [h2, ← h1, hm]
    ring
  rw [relIndex_subgroupOf hNX] at hdvd
  have hP : IsPGroup p ((Q ⊓ N).subgroupOf N) :=
    ((IsPGroup.of_card hQ).to_le inf_le_left).comap_subtype
  have hPi : ¬ p ∣ ((Q ⊓ N).subgroupOf N).index := by
    change ¬ p ∣ (Q ⊓ N).relIndex N
    rw [inf_relIndex_right]
    exact fun h => hS (h.trans hdvd)
  rw [← (hP.toSylow hPi).card_eq_multiplicity]
  exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem eq_pow_of_mem_zpowers_of_orderOf_eq_two {s y : G} {a : ℕ} (hs : orderOf s = 2 ^ a)
    (hy : y ∈ zpowers s) (hy2 : orderOf y = 2) : y = s ^ 2 ^ (a - 1) := by
  have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  obtain _ | b := a
  · rw [pow_zero, orderOf_eq_one_iff] at hs
    exact absurd (by rw [hs, one_zpow]) hy1
  rw [Nat.add_sub_cancel]
  have hk : ((2 ^ (b + 1) : ℕ) : ℤ) ∣ k * 2 := by
    rw [← hs, orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_two, hyy]
  have hk' : ((2 ^ b : ℕ) : ℤ) ∣ k := by
    have e : ((2 ^ (b + 1) : ℕ) : ℤ) = ((2 ^ b : ℕ) : ℤ) * 2 := by push_cast; ring
    rw [e] at hk
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 hk
  obtain ⟨m, rfl⟩ := hk'
  have hu : s ^ 2 ^ b * s ^ 2 ^ b = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hs, pow_orderOf_eq_one]
  rw [zpow_mul, zpow_natCast] at hy1 ⊢
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · obtain ⟨q, rfl⟩ : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero h0
    rw [zpow_mul, zpow_two, hu, one_zpow] at hy1
    exact absurd rfl hy1
  · have hm : m = 2 * (m / 2) + 1 := by omega
    rw [hm, zpow_add, zpow_mul, zpow_two, hu, one_zpow, one_mul, zpow_one]

end CFSG.OddStandard
