module

public import CFSG.GH74.GLS.LU.Local.FiveL84d
public import CFSG.GH74.GLS.LU.Local.FiveL84a
public import CFSG.GH74.GLS.LU.Local.FiveL84c

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L84

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg3.swap_case (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v₀ : G} (hv : v₀ ∈ NN z u)
    (hz : v₀ * z * v₀⁻¹ = z * u) (hX : cjL v₀ (XX t X₁) = Y) : v₀ * (z * u) * v₀⁻¹ = z := by
  have hmem : v₀ * (z * u) * v₀⁻¹ ∈ UU z u :=
    (Subgroup.mem_normalizer_iff.mp hv (z * u)).mp (zu_mem_UU z u)
  rcases mem_UU_cases c.hs.z_sq c.hs.u_sq c.hs.zu_comm hmem with h | h | h | h
  · exfalso
    apply c.zu_ne_one
    calc z * u = v₀⁻¹ * (v₀ * (z * u) * v₀⁻¹) * v₀ := by group
      _ = 1 := by rw [h]; group
  · exact h
  · exfalso; exact c.no_three_cycle hv hz hX h
  · exfalso
    have h2 : z * u = z := by
      calc z * u = v₀⁻¹ * (v₀ * (z * u) * v₀⁻¹) * v₀ := by group
        _ = v₀⁻¹ * (v₀ * z * v₀⁻¹) * v₀ := by rw [h, hz]
        _ = z := by group
    have hu1 : u ≠ 1 := fun h' => by
      have := c.hs.u_ord
      rw [h', orderOf_one] at this
      omega
    apply hu1
    exact mul_left_cancel (h2.trans (mul_one z).symm)

theorem Cfg3.comm_Y_conj (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v₀ : G}
    (hX : cjL v₀ (XX t X₁) = Y) : ∀ a ∈ Y, ∀ b ∈ cjL v₀ Y, a * b = b * a := by
  intro a ha b hb
  rw [← hX] at ha
  have ha' : v₀⁻¹ * a * v₀ ∈ XX t X₁ := mem_cjL.mp ha
  have hb' : v₀⁻¹ * b * v₀ ∈ Y := mem_cjL.mp hb
  have h := c.XX_comm _ ha' _ hb'
  calc a * b = v₀ * ((v₀⁻¹ * a * v₀) * (v₀⁻¹ * b * v₀)) * v₀⁻¹ := by group
    _ = v₀ * ((v₀⁻¹ * b * v₀) * (v₀⁻¹ * a * v₀)) * v₀⁻¹ := by rw [h]
    _ = b * a := by group

theorem Cfg3.XX_inf_N (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : ∀ x ∈ XX t X₁, x ∈ NN z u → x = 1 := by
  intro x hx hxN
  have h5 : x ^ 5 = 1 := c.b83.XY_ab.2 x (Subgroup.mem_sup_left hx)
  rcases c.b66.N_ord x hxN with h | h
  · have hd : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    rw [h] at hd
    omega
  · obtain ⟨k, hk⟩ := h ⟨x, Subgroup.mem_zpowers x⟩
    have hk' : x ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have hd : orderOf x ∣ Nat.gcd 5 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one hk')
    rw [hcop] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem Cfg3.five84w_of (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v₀ : G} (hv : v₀ ∈ NN z u)
    (hz : v₀ * z * v₀⁻¹ = z * u) (hX : cjL v₀ (XX t X₁) = Y) : Five84w z t u H X₁ Y v₀ := by
  have h3 := c.swap_case hv hz hX
  have hu1 : u ≠ 1 := fun h' => by
    have := c.hs.u_ord
    rw [h', orderOf_one] at this
    omega
  have hz2' : v₀ * v₀ * z * (v₀ * v₀)⁻¹ = z := by
    calc v₀ * v₀ * z * (v₀ * v₀)⁻¹ = v₀ * (v₀ * z * v₀⁻¹) * v₀⁻¹ := by group
      _ = z := by rw [hz, h3]
  have hv2 : IsPGroup 2 ↥(zpowers v₀) := by
    rcases c.b66.N_ord v₀ hv with h | h
    · exfalso
      have hv3 : v₀ ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one v₀
      have hv3' : v₀ * v₀ * v₀ = 1 := by rw [← hv3]; simp [pow_succ, mul_assoc]
      have : z * u = z := by
        calc z * u = v₀ * z * v₀⁻¹ := hz.symm
          _ = v₀ * (v₀ * v₀ * z * (v₀ * v₀)⁻¹) * v₀⁻¹ := by rw [hz2']
          _ = (v₀ * v₀ * v₀) * z * (v₀ * v₀ * v₀)⁻¹ := by group
          _ = z := by rw [hv3']; group
      exact hu1 (mul_left_cancel (this.trans (mul_one z).symm))
    · exact h
  have hYX : cjL v₀ Y = XX t X₁ := by
    have hC : cjL v₀ Y ≤ centralizer ({z} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (MulAut.conj v₀).toMonoidHom y = v₀ * y * v₀⁻¹ := by simp
      rw [hy']
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h1 : y * (z * u) = (z * u) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hy)
      calc v₀ * y * v₀⁻¹ * z = v₀ * y * v₀⁻¹ * (v₀ * (z * u) * v₀⁻¹) := by rw [h3]
        _ = v₀ * (y * (z * u)) * v₀⁻¹ := by group
        _ = v₀ * ((z * u) * y) * v₀⁻¹ := by rw [h1]
        _ = (v₀ * (z * u) * v₀⁻¹) * (v₀ * y * v₀⁻¹) := by group
        _ = z * (v₀ * y * v₀⁻¹) := by rw [h3]
    have hcard : Nat.card ↥(cjL v₀ Y) = 25 := by rw [card_cjL]; exact c.b83.Y_card
    have hSyl := c.isSylowIn_C hC hcard
    have hH : HInv H (cjL v₀ Y) := c.hinv_Y.conj (c.cjL_H hv)
    obtain ⟨w, hw, hR⟩ := c.b82.syl_inv _ hSyl hH
    rw [hR]
    apply c.eq_XX_of_comm_Y hw
    rw [← hR]
    exact fun a ha b hb => (c.comm_Y_conj hX b hb a ha).symm
  have hsq : v₀ ^ 2 ∈ H ⊔ zpowers t := by
    have hv2N : v₀ ^ 2 ∈ NN z u := pow_mem hv 2
    have hmem : v₀ ^ 2 ∈ normalizer ((XX t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) := by
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      · apply mem_normalizer_of_cjL_eq
        rw [pow_two, ← cjL_cjL, hX, hYX]
      · rw [pow_two]
        calc v₀ * v₀ * z = (v₀ * v₀ * z * (v₀ * v₀)⁻¹) * (v₀ * v₀) := by group
          _ = z * (v₀ * v₀) := by rw [hz2']
    rw [c.b82.NC_X] at hmem
    have hnormt : ∀ l ∈ zpowers t, ∀ e ∈ XX t X₁ ⊔ H, l * e * l⁻¹ ∈ XX t X₁ ⊔ H := by
      intro l hl e he
      have hcj : cjL t (XX t X₁ ⊔ H) = XX t X₁ ⊔ H := by rw [cjL_sup, c.t_XX, c.b66.t_normH]
      rcases mem_zpowers_of_sq_eq_one c.hs.t_sq hl with hl1 | hl1
      · rw [hl1]; simpa using he
      · rw [hl1]
        have := mem_cjL_self (g := t) he
        rwa [hcj] at this
    have hH_XX : ∀ l ∈ H, ∀ e ∈ XX t X₁, l * e * l⁻¹ ∈ XX t X₁ := fun l hl e he =>
      c.hinv_XX.mem hl he
    obtain ⟨m, hm, k, hk, hmk⟩ := mem_sup_of_normalizes hnormt hmem
    obtain ⟨x, hx, h, hh, rfl⟩ := mem_sup_of_normalizes hH_XX hm
    have htN : t ∈ NN z u := c.t_NN
    have hhN : h ∈ NN z u := c.H_le_NN hh
    have hkN : k ∈ NN z u := by
      have hkt : k ∈ zpowers t := hk
      exact (Subgroup.zpowers_le.mpr htN) hkt
    have hxN : x ∈ NN z u := by
      have : x = v₀ ^ 2 * (k⁻¹ * h⁻¹) := by rw [hmk]; group
      rw [this]
      exact mul_mem hv2N (mul_mem (inv_mem hkN) (inv_mem hhN))
    have hx1 : x = 1 := c.XX_inf_N x hx hxN
    rw [hmk, hx1, one_mul]
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  exact ⟨hv, hv2, hsq, hz, h3, hX, hYX⟩

end L84

theorem leaf84' : Leaf84' := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83
  have c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y := ⟨⟨ctx, b66, b82⟩, b83⟩
  obtain ⟨v₀, hv, hz, hX⟩ := c.exists_v0
  exact ⟨v₀, c.five84w_of hv hz hX⟩

end CFSG.GH74.GLS.LU.Local.Five
