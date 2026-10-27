module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public section

namespace CFSG.Semidihedral.Principal

open CFSG.GorensteinWalter

variable {S : Type*} [Group S]

theorem dihedral_reflection_conj_zpow {r s : S} (hs : s * s = 1) (hrel : s * r * s = r⁻¹)
    (i : ℕ) (k : ℤ) : (s * r ^ i) * r ^ k * (s * r ^ i)⁻¹ = (r ^ k)⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h1 : (s * r ^ i) * r * (s * r ^ i)⁻¹ = r⁻¹ := by
    rw [show (s * r ^ i) * r * (s * r ^ i)⁻¹ = s * r * s⁻¹ by group, hsinv, hrel]
  rw [← conj_zpow, h1, inv_zpow]

theorem dihedral_rotation_involution_structure {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* S)) :
    (∃ r s : S, orderOf r = 2 ^ (n - 1) ∧ orderOf s = 2 ∧ s * r * s = r⁻¹ ∧
      Subgroup.closure {r, s} = ⊤) ∧
    ∀ r s : S, orderOf r = 2 ^ (n - 1) → orderOf s = 2 → s * r * s = r⁻¹ →
      Subgroup.closure {r, s} = ⊤ →
      (Subgroup.zpowers r).Normal ∧ (Subgroup.zpowers r).index = 2 ∧
      (∀ g : S, ∃! c : Fin 2 × Fin (2 ^ (n - 1)), g = s ^ (c.1 : ℕ) * r ^ (c.2 : ℕ)) ∧
      (r ^ 2 ^ (n - 2) ∈ Subgroup.zpowers r ∧ orderOf (r ^ 2 ^ (n - 2)) = 2 ∧
        ∀ a ∈ Subgroup.zpowers r, orderOf a = 2 → a = r ^ 2 ^ (n - 2)) ∧
      (∀ x : S, x ∉ Subgroup.zpowers r → orderOf x = 2) ∧
      r ^ 2 ^ (n - 2) ∈ Subgroup.center S ∧
      (n = 2 → IsKleinFour S) ∧
      (3 ≤ n → Subgroup.center S = Subgroup.zpowers (r ^ 2 ^ (n - 2))) ∧
      (∀ x : S, x ∉ Subgroup.zpowers r →
        Subgroup.centralizer {x} = Subgroup.closure {r ^ 2 ^ (n - 2), x} ∧
        IsKleinFour (Subgroup.closure {r ^ 2 ^ (n - 2), x})) ∧
      ∀ V : Subgroup S, IsKleinFour V →
        r ^ 2 ^ (n - 2) ∈ V ∧ Subgroup.centralizer (V : Set S) = V := by
  obtain ⟨e₀⟩ := hS
  have hMK : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hK1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
  set K := 2 ^ (n - 2) with hK
  set M := 2 ^ (n - 1) with hM
  have hM2 : 2 ≤ M := by omega
  have : NeZero M := ⟨by omega⟩
  have hcard : Nat.card S = 2 * M := by
    rw [← Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card]
  have : Finite S := Finite.of_equiv _ e₀.toEquiv
  refine ⟨?_, ?_⟩
  ·
    refine ⟨e₀ (DihedralGroup.r 1), e₀ (DihedralGroup.sr 0), ?_, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    · rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
    · rw [← map_mul, ← map_mul, ← map_inv]
      congr 1
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    · rw [eq_top_iff]
      intro g _
      obtain ⟨d, rfl⟩ := e₀.surjective g
      have hr : e₀ (DihedralGroup.r 1) ∈ Subgroup.closure
          {e₀ (DihedralGroup.r 1), e₀ (DihedralGroup.sr 0)} := Subgroup.subset_closure (by simp)
      have hs : e₀ (DihedralGroup.sr 0) ∈ Subgroup.closure
          {e₀ (DihedralGroup.r 1), e₀ (DihedralGroup.sr 0)} := Subgroup.subset_closure (by simp)
      cases d with
      | r j =>
        have h : e₀ (DihedralGroup.r j) = e₀ (DihedralGroup.r 1) ^ j.val := by
          rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
        rw [h]
        exact Subgroup.pow_mem _ hr _
      | sr j =>
        have h : e₀ (DihedralGroup.sr j) =
            e₀ (DihedralGroup.sr 0) * e₀ (DihedralGroup.r 1) ^ j.val := by
          rw [← map_pow, ← map_mul, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
            DihedralGroup.sr_mul_r, zero_add]
        rw [h]
        exact Subgroup.mul_mem _ hs (Subgroup.pow_mem _ hr _)
  intro r s hr hs hrel hgen
  have hrM : r ^ M = 1 := hr ▸ pow_orderOf_eq_one r
  have hss : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨e, he, -⟩ := exists_dihedral_mulEquiv hM2 hcard hgen hrM hss hrel
  have hsurj : Function.Surjective fun c : Fin 2 × Fin M => s ^ (c.1 : ℕ) * r ^ (c.2 : ℕ) := by
    intro g
    obtain ⟨d, rfl⟩ := e.surjective g
    rw [he]
    cases d with
    | r j => exact ⟨(0, ⟨j.val, ZMod.val_lt j⟩), by simp [dihedralWord]⟩
    | sr j => exact ⟨(1, ⟨j.val, ZMod.val_lt j⟩), by simp [dihedralWord]⟩
  have hbij := hsurj.bijective_of_nat_card_le (by simp [hcard])
  have hnf : ∀ g : S, ∃! c : Fin 2 × Fin M, g = s ^ (c.1 : ℕ) * r ^ (c.2 : ℕ) := by
    intro g
    obtain ⟨c, hc, hu⟩ := hbij.existsUnique g
    exact ⟨c, hc.symm, fun c' hc' => hu c' hc'.symm⟩
  have hAindex : (Subgroup.zpowers r).index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers r)
    rw [Nat.card_zpowers, hr, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) (by linarith)
  have hout : ∀ x : S, x ∉ Subgroup.zpowers r → ∃ i : ℕ, x = s * r ^ i := by
    intro x hx
    obtain ⟨c, hc, -⟩ := hnf x
    have h2 := c.1.isLt
    rcases (by omega : (c.1 : ℕ) = 0 ∨ (c.1 : ℕ) = 1) with h0 | h1
    · rw [h0, pow_zero, one_mul] at hc
      exact absurd (hc ▸ Subgroup.npow_mem_zpowers r _) hx
    · rw [h1, pow_one] at hc
      exact ⟨c.2, hc⟩
  have hinvol : ∀ x : S, x ∉ Subgroup.zpowers r → orderOf x = 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hout x hx
    refine orderOf_eq_prime ?_ fun h => hx (h ▸ Subgroup.one_mem _)
    rw [pow_two, ← mul_assoc, conj_pow_of_dihedral hss hrel i, inv_mul_cancel]
  have hzord : orderOf (r ^ K) = 2 := by
    have h := orderOf_pow_orderOf_div (x := r) (n := 2) (by rw [hr]; omega)
      (by rw [hr, hMK]; exact dvd_mul_right 2 K)
    rwa [hr, hMK, Nat.mul_div_cancel_left K (by norm_num)] at h
  have hzA : r ^ K ∈ Subgroup.zpowers r := Subgroup.npow_mem_zpowers r K
  have hz2 : r ^ K * r ^ K = 1 := by rw [← pow_two, ← hzord, pow_orderOf_eq_one]
  have hz1 : r ^ K ≠ 1 := fun h => by rw [h, orderOf_one] at hzord; norm_num at hzord
  have hzuniq : ∀ a ∈ Subgroup.zpowers r, orderOf a = 2 → a = r ^ K := by
    intro a ha ha2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : (r ^ k) ^ 2 = 1 := by rw [← ha2, pow_orderOf_eq_one]
    have hdvd : ((K : ℤ) * 2) ∣ k * 2 := by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr (show r ^ (k * 2) = 1 by
        rw [zpow_mul, zpow_ofNat]; exact h1)
      rw [hr, hMK] at h
      push_cast at h
      rwa [mul_comm (2 : ℤ)] at h
    obtain ⟨j, rfl⟩ := (mul_dvd_mul_iff_right (two_ne_zero : (2 : ℤ) ≠ 0)).mp hdvd
    have hpow : r ^ ((K : ℤ) * j) = (r ^ K) ^ (j % 2) := by
      rw [zpow_mul, zpow_natCast, ← zpow_mod_orderOf (r ^ K) j, hzord]
      rfl
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · rw [hpow, h0, zpow_zero, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
    · rw [hpow, h1, zpow_one]
  have hcomms : Commute s (r ^ K) := by
    have h := conj_pow_of_dihedral hss hrel K
    rw [inv_eq_of_mul_eq_one_right hz2] at h
    show s * r ^ K = r ^ K * s
    calc s * r ^ K = s * r ^ K * s * s := by rw [mul_assoc _ s s, hss, mul_one]
      _ = r ^ K * s := by rw [h]
  have hzcenter : r ^ K ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, -⟩ := hnf g
    rw [hc]
    exact ((hcomms.pow_left _).mul_left ((Commute.self_pow r K).pow_left _)).eq
  have hV4 : n = 2 → IsKleinFour S := by
    intro h2
    have hM2' : M = 2 := by rw [hM, h2]; norm_num
    have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
    refine ⟨by rw [hcard, hM2'], (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
    by_cases hgA : g ∈ Subgroup.zpowers r
    · have hdvd := orderOf_dvd_of_mem_zpowers hgA
      rw [hr, hM2'] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hg
      · exact h1
    · exact hinvol g hgA
  have hcenter : 3 ≤ n → Subgroup.center S = Subgroup.zpowers (r ^ K) := by
    intro h3
    have hM4 : 4 ≤ M := by
      rw [hM]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hD := DihedralGroup.center_eq_closure_of_even_ne_two (n := M) ⟨K, by omega⟩
      (by omega)
    rw [← Subgroup.map_center_eq e, hD, MonoidHom.map_zpowers]
    congr 1
    rw [MonoidHom.coe_ofClass, he]
    simp only [dihedralWord]
    rw [ZMod.val_natCast_of_lt (by omega : M / 2 < M), show M / 2 = K by omega]
  have hxinv : ∀ x : S, x ∉ Subgroup.zpowers r → ∀ a ∈ Subgroup.zpowers r,
      x * a * x⁻¹ = a⁻¹ := by
    intro x hx a ha
    obtain ⟨i, rfl⟩ := hout x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact dihedral_reflection_conj_zpow hss hrel i k
  have hcommA : ∀ x : S, x ∉ Subgroup.zpowers r → ∀ w ∈ Subgroup.zpowers r,
      w * x = x * w → w = 1 ∨ w = r ^ K := by
    intro x hx w hw hwx
    have hww : w⁻¹ = w := by rw [← hxinv x hx w hw, ← hwx, mul_inv_cancel_right]
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · refine Or.inr (hzuniq w hw (orderOf_eq_prime ?_ hw1))
      rw [pow_two, ← mul_eq_one_iff_eq_inv.mpr hww.symm]
  have hcentx : ∀ x : S, x ∉ Subgroup.zpowers r →
      Subgroup.centralizer {x} = Subgroup.closure {r ^ K, x} ∧
        IsKleinFour (Subgroup.closure {r ^ K, x}) := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← pow_two, ← hinvol x hx, pow_orderOf_eq_one]
    have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
    have hzx : r ^ K ≠ x := fun h => hx (h ▸ hzA)
    have hcomm : Commute (r ^ K) x := (Subgroup.mem_center_iff.mp hzcenter x).symm
    let V := kleinFourOfCommutingInvolutions (r ^ K) x hz2 hx2 hcomm
    have hVK4 : IsKleinFour V :=
      isKleinFour_kleinFourOfCommutingInvolutions _ _ hz2 hx2 hz1 hx1 hzx hcomm
    have hmemV : ∀ y : S, y ∈ V ↔ y = r ^ K * x ∨ y = r ^ K ∨ y = x ∨ y = 1 := fun y => by
      change y ∈ ({r ^ K * x, r ^ K, x, 1} : Set S) ↔ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hclV : Subgroup.closure {r ^ K, x} ≤ Subgroup.centralizer {x} := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | rfl
      · exact hcomm.eq
      · rfl
    have hCV : Subgroup.centralizer {x} ≤ V := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      rw [hmemV]
      by_cases hyA : y ∈ Subgroup.zpowers r
      · rcases hcommA x hx y hyA hy with h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
      · have hw : y * x⁻¹ ∈ Subgroup.zpowers r :=
          (Subgroup.mul_mem_iff_of_index_two hAindex).mpr (by simp [hyA, hx])
        have hwx : y * x⁻¹ * x = x * (y * x⁻¹) := by
          rw [inv_mul_cancel_right, ← mul_assoc, ← hy, mul_inv_cancel_right]
        have hy' : y = y * x⁻¹ * x := by rw [inv_mul_cancel_right]
        rcases hcommA x hx _ hw hwx with h | h
        · rw [hy', h, one_mul]
          exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hy', h]
          exact Or.inl rfl
    have hVcl : V ≤ Subgroup.closure {r ^ K, x} := by
      intro y hy
      have hzc : r ^ K ∈ Subgroup.closure {r ^ K, x} := Subgroup.subset_closure (by simp)
      have hxc : x ∈ Subgroup.closure {r ^ K, x} := Subgroup.subset_closure (by simp)
      rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ hzc hxc
      · exact hzc
      · exact hxc
      · exact Subgroup.one_mem _
    have hcl : Subgroup.closure {r ^ K, x} = V := le_antisymm (hclV.trans hCV) hVcl
    refine ⟨le_antisymm (hCV.trans hVcl) hclV, ?_⟩
    rw [hcl]
    exact hVK4
  have hfour : ∀ V : Subgroup S, IsKleinFour V →
      r ^ K ∈ V ∧ Subgroup.centralizer (V : Set S) = V := by
    intro V hV
    have hm : 1 ≤ n - 1 := by omega
    refine ⟨center_mem_kleinFour_of_dihedral_mulEquiv (m := n - 1) hm e.symm V hV hzcenter,
      le_antisymm (centralizer_kleinFour_le_of_dihedral_mulEquiv (m := n - 1) hm e.symm V hV) ?_⟩
    have := hV
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr IsKleinFour.isMulCommutative
  exact ⟨Subgroup.normal_of_index_eq_two hAindex, hAindex, hnf, ⟨hzA, hzord, hzuniq⟩, hinvol,
    hzcenter, hV4, hcenter, hcentx, hfour⟩

end CFSG.Semidihedral.Principal
