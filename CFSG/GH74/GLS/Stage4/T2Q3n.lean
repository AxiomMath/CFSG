module

public import CFSG.GH74.GLS.Stage4.T2FourK
public import CFSG.GH74.GLS.Stage4.T2Sing
public import CFSG.GH74.GLS.Stage4.T2HGal
public import CFSG.GH74.GLS.Stage4.Q3n.Setting

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.Assembly.LowTwoRank

section Q3n

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2q3n_setting_core (hr : pRank 2 G = 3) {n : ℕ} (hn : 3 ≤ n)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hBad : Ch6Bad3 G)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (hTD : T2TnsData z t K₁ K₂) :
    Nonempty (Stage4.Q3n.Q3nSetting G n) := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hn0 : n ≠ 0 := by omega
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := t2C_zz hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  obtain ⟨⟨e₁, hze₁⟩, -⟩ := t2C_coords hSet
  have hK₁inv := t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  have hnc := t2B_hnc hSet hRem hC₁
  have hone := hSet.one_class
  obtain ⟨H, w₁, w₂, hT, ε₁, ε₂, hε₁, hε₂, hq₁, hq₂, hcyc₁, hcyc₂, hcard₁, hcard₂, hform⟩ :=
    t2Four_of_rem hSet hRem hC₁ hSet.five
  have hcast : (((3 ^ n : ℕ)) : ℤ) = (3 : ℤ) ^ n := by push_cast; ring
  have hεeq : ε₂ = ε₁ := by
    have h12 : ε₁ ≡ ε₂ [ZMOD 4] := hq₁.symm.trans hq₂
    unfold Int.ModEq at h12
    rcases hε₁ with h | h <;> rcases hε₂ with h' | h' <;> rw [h, h'] at h12 ⊢ <;> first | rfl | omega
  have hm₁ : Nat.card ↥(H ⊓ K₁) % 4 = 2 := by
    have h1 := hcard₁
    have h2 := hq₁
    unfold Int.ModEq at h2
    rcases hε₁ with h | h <;> rw [h] at h1 h2 <;> omega
  set k : ℕ := Nat.card ↥(H ⊓ K₁) / 2 with hkdef
  have hk2 : 2 * k = Nat.card ↥(H ⊓ K₁) := by omega
  have hkodd : Odd k := Nat.odd_iff.2 (by omega)
  have hc₁ : Nat.card ↥(H ⊓ K₁) = 2 * k := hk2.symm
  have hc₂ : Nat.card ↥(H ⊓ K₂) = 2 * k := by
    have h1 := hcard₂
    rw [hεeq] at h1
    have h2 := hcard₁
    omega
  have hk_eq : 2 * (k : ℤ) = 3 ^ n + ε₁ := by
    have h1 := hcard₁
    rw [hcast] at h1
    omega
  have hk3 : ¬ 3 ∣ k := by
    intro h3
    obtain ⟨c, hc⟩ := dvd_pow_self (3 : ℤ) hn0
    rcases hε₁ with h | h <;> rw [h, hc] at hk_eq <;> omega
  obtain ⟨Q₁, Q₂, hQ₁H, hQ₂H, hQ₁c, hQ₂c, hQ₁e, hQ₂e, hQ₁₂, hdec⟩ :=
    hT.odd_part hSet.z_mem₁ hSet.z_mem₂ k hkodd hcyc₁ hcyc₂ hc₁ hc₂ hform
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hT.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  have hQcard : Nat.card ↥(Q₁ ⊔ Q₂) = k * k := by
    rw [t2H_card_sup_comm_disjoint Q₁ Q₂ hcommQ hQ₁₂, hQ₁c, hQ₂c]
  have hUQ : t2U z t ⊓ (Q₁ ⊔ Q₂) = ⊥ := t2U_inf_Q_eq_bot hT.zz hT.uu hT.zu_comm hkodd hQe
  have hUcard : Nat.card ↥(t2U z t) = 4 :=
    t2U_card hT.zz hT.uu hT.zu_comm hT.z_ne hT.u_ne hT.zu_ne
  have hUH : t2U z t ≤ H := t2U_le_of_mem hT.zz hT.uu hT.zu_comm hT.z_mem_H hT.u_mem_H
  have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
  have hHeq : H = t2U z t ⊔ (Q₁ ⊔ Q₂) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · exact sup_le hUH hQH
  have hHcard : Nat.card ↥H = 4 * (k * k) := by
    have hc : ∀ x ∈ t2U z t, ∀ y ∈ Q₁ ⊔ Q₂, x * y = y * x := fun x hx y hy =>
      hT.H_comm x (hUH hx) y (hQH hy)
    rw [hHeq, t2H_card_sup_comm_disjoint _ _ hc hUQ, hUcard, hQcard]
  have hH3 : ¬ 3 ∣ Nat.card ↥H := by
    rw [hHcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · omega
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h <;> exact hk3 h
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hRem.sq) hT.u_ne
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone t htord)
  have hconj : ∃ g : G, g⁻¹ * z * g = t := ⟨c⁻¹, by simpa using hc⟩
  obtain ⟨w₁', w₂', a, hW⟩ := hT.exists_weyl hr hodd₁ h3₁ e₁ hK₁inv hnc hconj hH3
    (fun a haN ha3 d1 d2 x hx hax => by
      by_contra hx1
      have ha1 : a ≠ 1 := by
        intro h1; apply hT.zu_ne
        rw [h1] at d1; simpa using d1
      exact hTD H w₁ w₂ hT Q₁ Q₂ k hkodd hQ₁H hQ₂H hQ₁e hQ₂e hdec hH3 a haN
        (orderOf_eq_prime ha3 ha1) x hx hx1 hax)
  have hF := hW.four
  obtain ⟨v, hv, hy2, hya⟩ := hW.exists_y hr
  obtain ⟨f, hf, hrange, hfr, hfs⟩ := hW.dihedral hv hy2 hya
  obtain ⟨P, hP⟩ := t2_bad3 hSet hBad
  have hzU : z ∈ t2U z t := Subgroup.subset_closure (by simp)
  have htU : t ∈ t2U z t := Subgroup.subset_closure (by simp)
  have hw₀ne : w₁' * w₂' ≠ 1 := fun h1 => hF.w₀_not_mem (h1 ▸ H.one_mem)
  have htK : t ∉ K₁ ⊔ K₂ := t2B_t_notin hSet hRem
  have htC₁ : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hRem.gen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  refine ⟨
    { z := z, z_ord := hzord, K₁ := K₁, K₂ := K₂,
      iso₁ := by
        obtain ⟨e⟩ := hSet.iso₁
        obtain ⟨e'⟩ := t2H_sl_galoisField hn0 hSet.card₁
        exact ⟨e.trans e'⟩,
      iso₂ := by
        obtain ⟨e⟩ := hSet.iso₂
        obtain ⟨e'⟩ := t2H_sl_galoisField hn0 hSet.card₂
        exact ⟨e.trans e'⟩,
      K_comm := hSet.comm, K_inter := hSet.inter_eq,
      K_normal := fun c hc x hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hx
        have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hT.C_norm₁ c hc a ha))
          (Subgroup.mem_sup_right (hT.C_norm₂ c hc b hb)),
      U := t2U z t, U_card := hUcard,
      U_exp := fun x hx => by
        rcases (t2U_mem hT.zz hT.uu hT.zu_comm).1 hx with h1 | h1 | h1 | h1
        · rw [h1]; simp
        · rw [h1]; exact hT.zz
        · rw [h1]; exact hT.uu
        · rw [h1]
          calc z * t * (z * t) = z * (t * z) * t := by group
            _ = z * (z * t) * t := by rw [← hT.zu_comm]
            _ = (z * z) * (t * t) := by group
            _ = 1 := by rw [hT.zz, hT.uu, one_mul],
      z_mem_U := hzU,
      C_eq := fun c hc => by
        have hcC₁ := hC₁ hc
        by_cases hcK : c ∈ K₁ ⊔ K₂
        · exact ⟨c, hcK, 1, Subgroup.one_mem _, by simp⟩
        · have h1 := t2C_outer_coset hSet.index_two hcC₁ htC₁ hcK htK
          refine ⟨c * t⁻¹, h1, t, htU, ?_⟩
          group,
      P := P, P_le := hP,
      H := H, Q := Q₁ ⊔ Q₂, ε := ε₁, k := k, ε_pm := hε₁,
      q_mod := by rw [← hcast]; exact hq₁,
      k_eq := hk_eq,
      H_comm := hT.H_comm, U_le_H := hUH, Q_le_H := hQH, U_inf_Q := hUQ, H_eq := hHeq,
      Q_card := by rw [hQcard, pow_two],
      w₀ := w₁' * w₂',
      w₀_ord := orderOf_eq_prime (by rw [pow_two]; exact hF.w₀_sq) hw₀ne,
      w₀_inv := hF.w₀_inv,
      w₀_cent := fun x hx => t2U_comm_all hF.zz hF.uu hF.zu_comm hF.w₀_z hF.w₀_u x hx,
      C0_eq := fun c hc => by
        have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.1 hc z hzU).symm
        have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.1 hc t htU).symm
        rcases hF.Y1 c (Subgroup.mem_centralizer_singleton_iff.2 hcz) hct with h1 | ⟨x, hx, h1⟩
        · exact ⟨c, h1, Or.inl rfl⟩
        · exact ⟨x, hx, Or.inr h1⟩,
      W := Subgroup.closure ({a, w₁' * v, w₁' * w₂'} : Set G),
      W_iso := ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)).symm⟩,
      W_norm_U := fun w hw => hW.W_le_normU hv hw,
      w₀_mem_W := Subgroup.subset_closure (by simp),
      w₀_central := fun w hw => by
        have hle : Subgroup.closure ({a, w₁' * v, w₁' * w₂'} : Set G) ≤
            Subgroup.centralizer ({w₁' * w₂'} : Set G) := by
          rw [Subgroup.closure_le]
          rintro x (rfl | rfl | rfl)
          · exact Subgroup.mem_centralizer_singleton_iff.2 hW.a_cent
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hF.y_w₀ hv)
          · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw),
      N_eq := fun g hg => hW.N_eq hr hv hy2 g hg,
      N_norm_H := fun g hg x hx => hF.normH hr hg x hx,
      a := a, a_mem := Subgroup.subset_closure (by simp),
      a_ord := orderOf_eq_prime hW.a_cube hW.a_ne_one,
      U_trans := hW.U_trans,
      nonsing := fun x hx hax => by
        by_contra hx1
        exact hTD H w₁' w₂' hF Q₁ Q₂ k hkodd hQ₁H hQ₂H hQ₁e hQ₂e hdec hH3 a hW.a_normH
          (orderOf_eq_prime hW.a_cube hW.a_ne_one) x hx hx1 hax,
      inv_fix := fun y hy hord hne =>
        hW.inv_fix_card hv hy2 hya hQ₁H hQ₂H hkodd hQ₁c hQ₂c hQ₁e hQ₂e hdec hy hord hne }⟩

theorem q3nSettingOf_of_order (hRemL : Ch6T2Rem) (hF1 : Ch6T2F1Gt9) (hOrd : Ch6P56bOrder) :
    Stage4.Q3n.Q3nSettingOf := by
  intro G _ _ hStd hr Gs _ n hn hAt hBad
  obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
  obtain ⟨t, hRem⟩ := hRemL G hStd hr Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ hSet
  have hC₁ := hF1 G hStd hr Gs n hn hAt hBad z K₁ K₂ F₁ F₂ hSet
  exact t2q3n_setting_core hr hn hSet hRem hBad hC₁
    (T2TnsData.of_order hOrd hStd hr (by omega) hAt hBad hSet hRem)

end Q3n

end CFSG.GH74.GLS.Stage4.Rest
