module

public import CFSG.LargeExtraspecial.S5Four
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LargeExtraspecial.S10FlagB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem exists_odd_normal_of_isolated {X : Type u} [Group X] [Finite X] (t : X) (ht1 : t ≠ 1)
    (ht2 : t * t = 1)
    (hiso : ∀ g : X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧ ∀ g : X, g * t * g⁻¹ * t⁻¹ ∈ N := by
  let e : Shrink.{0} X ≃* X := Shrink.mulEquiv
  have : Finite (Shrink.{0} X) := Finite.of_equiv X e.toEquiv.symm
  let := Fintype.ofFinite (Shrink.{0} X)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (Shrink.{0} X) (e.symm t)
    (fun h => ht1 (by simpa using congrArg e h))
    (by rw [← map_mul, ht2, map_one])
    (fun g hg => by
      apply e.injective
      simpa using hiso (e g) (by simpa using congrArg e hg))
  refine ⟨N.map e.toMonoidHom, hNn.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hNodd
  · intro g
    exact ⟨e.symm g * e.symm t * (e.symm g)⁻¹ * (e.symm t)⁻¹, hN (e.symm g), by simp⟩

theorem commSpace_mul_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (x y : V ≃ₗ[ZMod 2] V) : commSpace (x * y) ≤ commSpace (x * y * x⁻¹) ⊔ commSpace x := by
  intro w hw
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
  have e : (x * y) v - v = ((x * y * x⁻¹) (x v) - x v) + (x v - v) := by
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem exists_conj_ne (X : Hyp10 S g t) : ∃ m : S.M, S.ρ m * t * (S.ρ m)⁻¹ ≠ t := by
  by_contra h
  push Not at h
  apply X.ht1
  refine S5.eq_one_of_mem_center_of_pow S (CFSG.Open.IsSubnormal.refl S.Mbar)
    (S.Lbar_le_Mbar g X.ht) (fun y hy => ?_) (k := 1) ?_
  · obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
    have h1 := h m
    calc t * S.ρ m = S.ρ m * t * (S.ρ m)⁻¹ * S.ρ m := by rw [h1]
      _ = S.ρ m * t := by group
  · rw [pow_one, _root_.sq]
    exact S4.mul_self_of_mem_Lbar S X.haQ X.ht

theorem false_of_order_three (X : Hyp10 S g t) {k : S.O} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hinv : ∀ s ∈ S.Lbar g, s * k * s⁻¹ = k ∨ s * k * s⁻¹ = k * k)
    (hdim : finrank (ZMod 2) (commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt)) <
      finrank (ZMod 2) S.Qt) : False := by
  have happ : ∀ x y : S.O, ∀ v, ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun _ _ _ => rfl
  have hks : ∀ s ∈ S.Lbar g, k * s = s * k ∨ k * s = s * (k * k) := by
    intro s hs
    rcases hinv s⁻¹ (inv_mem hs) with h | h
    · left
      calc k * s = s * (s⁻¹ * k * s⁻¹⁻¹) := by group
        _ = s * k := by rw [h]
    · right
      calc k * s = s * (s⁻¹ * k * s⁻¹⁻¹) := by group
        _ = s * (k * k) := by rw [h]
  have hsk : ∀ s ∈ S.Lbar g, s * k = k * s ∨ s * k = (k * k) * s := by
    intro s hs
    rcases hinv s hs with h | h
    · left
      calc s * k = s * k * s⁻¹ * s := by group
        _ = k * s := by rw [h]
    · right
      calc s * k = s * k * s⁻¹ * s := by group
        _ = (k * k) * s := by rw [h]
  have hinv1 : ∀ s ∈ S.Lbar g, ∀ v ∈ fixSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ fixSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro s hs v hv
    rw [mem_fixSpace] at hv ⊢
    rw [← happ]
    rcases hks s hs with h | h
    · rw [h, happ, hv]
    · rw [h, happ, happ, hv, hv]
  have hinv2 : ∀ s ∈ S.Lbar g, ∀ v ∈ commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro s hs v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    rw [map_sub, ← happ]
    rcases hsk s hs with h | h
    · rw [h, happ]
      exact sub_mem_commSpace _ _
    · rw [h, happ, happ]
      set u := (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w
      have e2 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u =
          ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) + ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
      rw [e2]
      exact add_mem (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)
  have he1 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hU2 : commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := fun h => by
    have := one_le_finrank_commSpace he1
    rw [h, finrank_bot] at this
    omega
  have hU1 : fixSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := fun h => by
    have h1 := finrank_commSpace_add_finrank_fixSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt)
    rw [h, finrank_bot] at h1
    omega
  have hbase : ∀ {U : Submodule (ZMod 2) S.Qt}, U ≠ ⊥ →
      (∀ s ∈ S.Lbar g, ∀ u ∈ U, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) →
      S.cl (g * S.z * g⁻¹) ∈ U := by
    intro U hU hinv
    have := cl_mem_of_invariant X.H 1 hU (by simpa using hinv)
    simpa using this
  have ha1 := hbase hU1 hinv1
  have ha2 := hbase hU2 hinv2
  obtain ⟨w, hw⟩ := mem_commSpace.mp ha2
  have hpow : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hk3, Subgroup.coe_one]
  exact cl_conj_z_ne_zero S X.haQ X.H.conj_ne
    (S5.eq_zero_of_apply_eq_of_sub_eq (by decide : Odd 3) hpow (mem_fixSpace.mp ha1) hw)

theorem finrank_commSpace_conj_mul_le (X : Hyp10 S g t) (m : S.M) :
    finrank (ZMod 2) (commSpace ((S.ρ m * t * (S.ρ m)⁻¹ * t⁻¹ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 8 := by
  set x : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  set y : S.Qt ≃ₗ[ZMod 2] S.Qt := ((t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hexy : ((S.ρ m * t * (S.ρ m)⁻¹ * t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = x * y := rfl
  rw [hexy]
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (S4.mul_self_of_mem_Lbar S X.haQ X.ht)
  have h1 := Submodule.finrank_mono (commSpace_mul_le x y)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (commSpace (x * y * x⁻¹))
    (commSpace x)
  have h3 : finrank (ZMod 2) (commSpace (x * y * x⁻¹)) = 4 := by
    rw [finrank_commSpace_conj]
    have hy : y = ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      simp only [y]
      rw [htt]
    rw [hy]
    exact finrank_commSpace_t X
  have h4 : finrank (ZMod 2) (commSpace x) = 4 := by
    simp only [x, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [finrank_commSpace_conj, finrank_commSpace_t X]
  omega

theorem exists_conj_commute_ne (X : Hyp10 S g t) : ∃ m : S.M, S.ρ m * t * (S.ρ m)⁻¹ ≠ t ∧
    (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹) := by
  classical
  by_contra hcon
  push Not at hcon
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g X.ht
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S X.haQ X.ht
  have htM1 : (⟨t, htM⟩ : S.Mbar) ≠ 1 := fun h => X.ht1 (congrArg Subtype.val h)
  have htM2 : (⟨t, htM⟩ : S.Mbar) * ⟨t, htM⟩ = 1 := Subtype.ext htt
  obtain ⟨N, hNn, hNodd, hN⟩ := exists_odd_normal_of_isolated _ htM1 htM2 (fun y hy => by
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp y.2
    have hy' : y = ⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩ := Subtype.ext hm.symm
    subst hy'
    by_contra hne
    exact hcon m (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hy))
  obtain ⟨K, hK⟩ : ∃ K : Subgroup S.O, K = N.map S.Mbar.subtype := ⟨_, rfl⟩
  have hKM : K ≤ S.Mbar := hK ▸ map_subtype_le N
  have hKodd : Odd (Nat.card K) := by
    rw [hK, Subgroup.card_map_of_injective S.Mbar.subtype_injective]
    exact hNodd
  have hmemK : ∀ m : S.M, S.ρ m * t * (S.ρ m)⁻¹ * t⁻¹ ∈ K := fun m => by
    rw [hK]
    exact ⟨_, hN ⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩, rfl⟩
  have hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ K, s * x * s⁻¹ ∈ K := by
    intro s hs x hx
    rw [hK] at hx ⊢
    obtain ⟨n, hn, rfl⟩ := hx
    have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar g hs
    refine ⟨⟨s, hsM⟩ * n * ⟨s, hsM⟩⁻¹, hNn.conj_mem n hn ⟨s, hsM⟩, ?_⟩
    simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨m₀, hm₀⟩ := exists_conj_ne X
  obtain ⟨k, hkdef⟩ : ∃ k : S.O, k = S.ρ m₀ * t * (S.ρ m₀)⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hkK : k ∈ K := hkdef ▸ hmemK m₀
  have hk1 : k ≠ 1 := fun h => hm₀ (by
    rw [hkdef] at h
    calc S.ρ m₀ * t * (S.ρ m₀)⁻¹ = S.ρ m₀ * t * (S.ρ m₀)⁻¹ * t⁻¹ * t := by group
      _ = t := by rw [h, one_mul])
  have hKbot : K ≠ ⊥ := fun h => hk1 (by rw [h] at hkK; exact (mem_bot.mp hkK))
  have hK3 : Nat.card K = 3 := S5.timmesfeld_5_4 X.H X.hNo X.C (by have := X.five_le_width; omega)
    hKM hKodd hKbot hnorm
  have hk3 : orderOf k = 3 := by
    have hdvd : orderOf k ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K hkK
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · exact h
  have hzK : zpowers k = K := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hkK) ?_
    rw [hK3, Nat.card_zpowers, hk3]
  have hKcases : ∀ x ∈ K, x = 1 ∨ x = k ∨ x = k * k := by
    intro x hx
    rw [← hzK, mem_zpowers_iff_mem_range_orderOf, hk3] at hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    interval_cases i <;> simp [pow_two]
  have hinv : ∀ s ∈ S.Lbar g, s * k * s⁻¹ = k ∨ s * k * s⁻¹ = k * k := by
    intro s hs
    rcases hKcases _ (hnorm s hs k hkK) with h | h | h
    · exact absurd (by
        calc k = s⁻¹ * (s * k * s⁻¹) * s := by group
          _ = 1 := by rw [h]; group) hk1
    · exact Or.inl h
    · exact Or.inr h
  have hk3' : k ^ 3 = 1 := by rw [← hk3]; exact pow_orderOf_eq_one k
  refine false_of_order_three X hk3' hk1 hinv ?_
  have h8 := finrank_commSpace_conj_mul_le X m₀
  rw [← hkdef] at h8
  rw [S.finrank_Qt_eq_two_mul_width]
  have := X.five_le_width
  omega

end CFSG.LargeExtraspecial.S10
