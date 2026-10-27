module

public import CFSG.GH74.GLS.IVK.Proofs2.C3L29Rank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6NI

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 CFSG.Glauberman.Dickson
  CFSG.Glauberman.Dickson.MaxUp

section PairID

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem sup_fixed_eq_top_of_inner_outer (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F)
    {z w : MulAut K} (hz : z ∈ innAut K) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hw : w ∈ innDiagSub e)
    (hwI : w ∉ innAut K) (hw2 : w ^ 2 = 1) (hcomm : z * w = w * z) :
    fixedSubgroup K z ⊔ fixedSubgroup K w = ⊤ := by
  have hw1 : w ≠ 1 := fun h => hwI (by rw [h]; exact one_mem _)
  have hwo : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨k, hk2, hkq, hkodd, ⟨ψ⟩⟩ := fixed_dihedral_data hF e hw hwo
  have hkodd' := hkodd hwI
  have hk3 : 3 ≤ k := by
    obtain ⟨j, hj⟩ := hkodd'
    omega
  have hk4 : k ≠ 4 := by
    rintro rfl
    exact absurd hkodd' (by decide)
  obtain ⟨dI, dD, hdI, hdD, hne', hI, hD⟩ := card_fixedSubgroup_inndiag hF e
  obtain ⟨u, hu⟩ := hz
  have huo : orderOf u = 2 := by
    have := orderOf_injective (MulAut.conj : K →* MulAut K) (conj_injective_of_L2 e) u
    rw [hu] at this
    exact this.symm.trans hzo
  subst hu
  have hCz : Nat.card ↥(fixedSubgroup K (MulAut.conj u)) = dI := hI u huo
  have hCw : Nat.card ↥(fixedSubgroup K w) = dD := hD w hw hwI hwo
  have hCw2k : Nat.card ↥(fixedSubgroup K w) = 2 * k := by
    have : NeZero k := ⟨by omega⟩
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  have hnd := not_dvd_of_pm_one (q := Nat.card F) (by omega) hdI hdD hne'
  have hKcard : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := card_eq_of_L2Field e hF
  have hdvdK : ∀ M : Subgroup K, Nat.card ↥M ∣ Nat.card K := fun M => Subgroup.card_subgroup_dvd_card M
  rcases overgroup_of_fixed_dihedral hF e ψ hkq hk3 hk4
    (fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w) le_sup_right with
    h | h | ⟨⟨e4⟩, hk⟩ | ⟨⟨e4⟩, hk⟩ | ⟨⟨e5⟩, hk⟩
  ·
    exfalso
    have hle : fixedSubgroup K (MulAut.conj u) ≤ fixedSubgroup K w := le_sup_left.trans (le_of_eq h)
    have := Subgroup.card_dvd_of_le hle
    rw [hCz, hCw] at this
    exact hnd.1 this
  · exact h
  ·
    exfalso
    subst hk
    have hle : fixedSubgroup K w ≤ fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w := le_sup_right
    set x : ↥(fixedSubgroup K w) := ψ.symm (DihedralGroup.r 1) with hx
    set s : ↥(fixedSubgroup K w) := ψ.symm (DihedralGroup.sr 0) with hs
    have hxo : orderOf x = 3 := by
      rw [hx, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hx3 : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hxo] at this
    have hsx : s * x * s⁻¹ = x⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, map_inv, hx, hs, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
      exact sr_zero_mul_r_one_mul_inv
    let ι : ↥(fixedSubgroup K w) →* ↥(fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w) :=
      Subgroup.inclusion hle
    have hιinj : Function.Injective ι := Subgroup.inclusion_injective hle
    refine alternating_four_not_inverted (e4 (ι s)) (e4 (ι x)) ?_ ?_ ?_
    · rw [← map_pow, ← map_pow, hx3, map_one, map_one]
    · intro h1
      have h2 : ι x = 1 := e4.injective (h1.trans (map_one e4).symm)
      have : x = 1 := hιinj (h2.trans (map_one ι).symm)
      rw [this, orderOf_one] at hxo
      omega
    · have h1 : e4 (ι (s * x * s⁻¹)) = e4 (ι x⁻¹) := by rw [hsx]
      simpa [map_mul, map_inv] using h1
  ·
    exfalso
    subst hk
    have hM24 : Nat.card ↥(fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w) = 24 := by
      rw [Nat.card_congr e4.toEquiv, card_perm_four]
    have hq57 : Nat.card F = 5 ∨ Nat.card F = 7 := by omega
    rcases hq57 with hq5 | hq7
    · have h60 : Nat.card K = 60 := by rw [hKcard, hq5]; norm_num
      have := hdvdK (fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w)
      rw [hM24, h60] at this
      omega
    · have hq' : Nat.card F = 7 ∨ Nat.card F = 9 := Or.inl hq7
      have hD4 : HasD4Centralizers K := fun v hv => (centralizer_dih_of_seven_nine hF hq' e hv).1
      have hQ8 : ∀ v : K, orderOf v = 2 → Nonempty (↥(centralizer ({MulAut.conj v} : Set (MulAut K)) ⊓
          innDiagSub e) ≃* DihedralGroup 8) := fun v hv => (centralizer_dih_of_seven_nine hF hq' e hv).2
      obtain ⟨V₀, u₁, u₂, hV₀4, hV₀comm, hu₁, hu₂, h₁, h₂, hu₁₂, hcomm12, hΓ1, hΓ2, hΓN, hΓ24⟩ :=
        exists_klein_data_of_equiv_perm4 hD4 e4
      have hmaps : ∀ k ∈ fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w,
          w k ∈ fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w := by
        have hle : fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w ≤
            (fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w).comap (w : K ≃* K).toMonoidHom := by
          refine sup_le (fun k hk => ?_) (fun k hk => ?_)
          · have hk' : (MulAut.conj u) k = k := hk
            have h1 : (MulAut.conj u) (w k) = w k := by
              calc (MulAut.conj u) (w k) = ((MulAut.conj u) * w) k := rfl
                _ = (w * (MulAut.conj u)) k := by rw [hcomm]
                _ = w k := by
                  show w ((MulAut.conj u) k) = w k
                  rw [hk']
            exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left h1)
          · have hk' : w k = k := hk
            exact Subgroup.mem_comap.2 (by
              show w k ∈ _
              rw [hk']
              exact Subgroup.mem_sup_right hk)
        intro k hk
        exact Subgroup.mem_comap.1 (hle hk)
      exact hwI (mem_innAut_of_maps_gamma e hD4 hQ8 hV₀4 hV₀comm hu₁ hu₂ h₁ h₂ hu₁₂ hcomm12 hΓ1 hΓ2
        hΓN hΓ24 hw hmaps)
  ·
    exfalso
    have hq9 : Nat.card F = 9 := by omega
    have hM60 : Nat.card ↥(fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w) = 60 := by
      rw [Nat.card_congr e5.toEquiv, card_alternatingFive']
    have hdvd := Subgroup.card_dvd_of_le (le_sup_left : fixedSubgroup K (MulAut.conj u) ≤
      fixedSubgroup K (MulAut.conj u) ⊔ fixedSubgroup K w)
    rw [hCz, hM60] at hdvd
    have hdD10 : dD = 10 := by omega
    have hdI8 : dI = 8 := by
      rcases hdI with h | h <;> rcases hdD with h' | h' <;> omega
    rw [hdI8] at hdvd
    omega

end PairID

end CFSG.GH74.GLS.IVK.Proofs2
