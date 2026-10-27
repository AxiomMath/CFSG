module

public import CFSG.LargeExtraspecial.A2ModFrB4
public import CFSG.LargeExtraspecial.A2ModFrB5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {d x : G} (hd : d * d = 1)
    (hx : x ∈ Subgroup.zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem map_lr_eq_of_map_rootGroup {X : Type} [Group X] {n : ℕ} {K : Type} [Field K]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    (Ψ : spinGroup (quadMinus n K b c) →* X) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1)
    {d : X} (hd1 : d ≠ 1) (hd2 : d * d = 1)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    Ψ (lr n b c (succ_ne_of_lt n hi₀) true false) = d := by
  have hrg : (minusDatum n hirr).rootGroup (Pi.single i₀ 1) =
      ((minusFrame n b c).longRoot (succ_ne_of_lt n hi₀) true false).range :=
    minusRootGroup_single_of_lt n hirr hi₀
  rw [hrg] at hmem
  have hx : Ψ (lr n b c (succ_ne_of_lt n hi₀) true false) ∈ Subgroup.zpowers d := by
    rw [← hmem]
    exact Subgroup.mem_map_of_mem Ψ ⟨_, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hd2 hx with h | h
  · exfalso
    have hdm : d ∈ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi₀) true false).range.map Ψ := by
      rw [hmem]
      exact Subgroup.mem_zpowers d
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Subgroup.mem_map.mp hdm
    rcases eq_zero_or_eq_one hK (Multiplicative.toAdd a) with h0 | h0
    · rw [show a = .ofAdd 0 from by rw [← h0]; rfl, ofAdd_zero, map_one, map_one] at ha
      exact hd1 ha.symm
    · rw [show a = .ofAdd 1 from by rw [← h0]; rfl] at ha
      exact hd1 (ha.symm.trans h)
  · exact h

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}

theorem frame_finrank_commSpaceOf_top_le (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * n := by
  have h := map_lr_eq_of_map_rootGroup hirr hK Ψ hi₀ (hA.ne_one hd) (hA.mul_self hd) hmem
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · obtain rfl : n = 5 := by omega
    exact finrank_commSpaceOf_top_le_ten hirr hK Ψ hsurj hDc hA _ (h ▸ hd)
  · exact finrank_commSpaceOf_top_le_two_mul h6 hirr hK Ψ hsurj hDc hA _ (h ▸ hd)

theorem frame_finrank_commSpaceOf_top_le_nine (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hn : n = 4) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 9 := by
  subst hn
  have h := map_lr_eq_of_map_rootGroup hirr hK Ψ hi₀ (hA.ne_one hd) (hA.mul_self hd) hmem
  exact finrank_commSpaceOf_top_le_nine hirr hK Ψ hsurj hDc hA _ (h ▸ hd)

theorem frame_lieModel (hn : 4 ≤ n) (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Ψ : spinGroup (quadMinus n K b c) →* X) (hsurj : Function.Surjective Ψ)
    (hker : Ψ.ker ≤ Subgroup.center _) (hZ : Subgroup.center X = ⊥) :
    LieModel X .POmegaMinus n 2 1 :=
  lieModel_of_spin hn hirr hK Ψ hsurj hker hZ

theorem frame_two_mul_le_finrank_commSpaceOf_top [Finite X] (hA : A2Action D Q ρ) (hn : 4 ≤ n)
    (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Ψ : spinGroup (quadMinus n K b c) →* X) (hsurj : Function.Surjective Ψ)
    (hker : Ψ.ker ≤ Subgroup.center _) (hZ : Subgroup.center X = ⊥) :
    2 * n ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤) :=
  two_mul_le_finrank_commSpaceOf_top (frame_lieModel hn hK hirr Ψ hsurj hker hZ) hA.injective

theorem frame_finrank_commSpaceOf_top_eq [Finite X] (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center _)
    (hZ : Subgroup.center X = ⊥) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) = 2 * n :=
  le_antisymm (frame_finrank_commSpaceOf_top_le hDc hA hn hK hirr Ψ hsurj hi₀ hd hmem)
    (frame_two_mul_le_finrank_commSpaceOf_top hA (by omega) hK hirr Ψ hsurj hker hZ)

theorem frame_finrank_eq_of_irreducible [Finite X] (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ)
    (hirrV : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hn : 5 ≤ n) (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Ψ : spinGroup (quadMinus n K b c) →* X) (hsurj : Function.Surjective Ψ)
    (hker : Ψ.ker ≤ Subgroup.center _) (hZ : Subgroup.center X = ⊥) {i₀ : Fin (n - 1)}
    (hi₀ : i₀.val + 1 < n - 1) {d : X} (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) V = 2 * n ∧ LieModel X .POmegaMinus n 2 1 := by
  have h := frame_finrank_commSpaceOf_top_eq hDc hA hn hK hirr Ψ hsurj hker hZ hi₀ hd hmem
  rw [commSpaceOf_top_eq_top ρ hirrV (hA.isTypeA hd).2.1, finrank_top] at h
  exact ⟨h, frame_lieModel (by omega) hK hirr Ψ hsurj hker hZ⟩

theorem frame_irreducible_of_ten_le [Finite X] (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ)
    (hirrV : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : 10 ≤ finrank (ZMod 2) V) (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center _)
    (hZ : Subgroup.center X = ⊥) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    5 ≤ n ∧ finrank (ZMod 2) V = 2 * n ∧ LieModel X .POmegaMinus n 2 1 := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    have h := frame_finrank_commSpaceOf_top_le_nine hDc hA rfl hK hirr Ψ hsurj hi₀ hd hmem
    rw [commSpaceOf_top_eq_top ρ hirrV (hA.isTypeA hd).2.1, finrank_top] at h
    omega
  · exact ⟨h5, frame_finrank_eq_of_irreducible hDc hA hirrV h5 hK hirr Ψ hsurj hker hZ hi₀ hd
      hmem⟩

end CFSG.LargeExtraspecial.A2Mod.FrB
