module

public import CFSG.GH74.GLS.LU.Local.FiveL86b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L84c

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem mem_UU_cases {z u x : G} (hz : z * z = 1) (hu : u * u = 1) (hzu : z * u = u * z)
    (hx : x ∈ UU z u) : x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute (A := zpowers z) (B := zpowers u)
    (zpowers_comm' hzu)).mp hx
  rcases mem_zpowers_of_sq_eq_one hz ha with h1 | h1 <;>
    rcases mem_zpowers_of_sq_eq_one hu hb with h2 | h2 <;> simp [h1, h2]

theorem Cfg3.v0_cube (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v₀ : G} (hv : v₀ ∈ NN z u)
    (hz : v₀ * z * v₀⁻¹ = z * u) (h3 : v₀ * (z * u) * v₀⁻¹ = u) : v₀ ^ 3 = 1 := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have huz : u = z * (z * u) := by rw [← mul_assoc, hz2, one_mul]
  have hu : v₀ * u * v₀⁻¹ = z := by
    have e : v₀ * u * v₀⁻¹ = (v₀ * z * v₀⁻¹) * (v₀ * (z * u) * v₀⁻¹) := by
      conv_lhs => rw [huz]
      group
    rw [e, hz, h3]
    calc z * u * u = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  set a3 : G := v₀ * v₀ * v₀ with ha3
  have hpow3 : v₀ ^ 3 = a3 := by rw [ha3]; simp [pow_succ, mul_assoc]
  have hcyc : a3 * z * a3⁻¹ = z := by
    calc a3 * z * a3⁻¹ = v₀ * (v₀ * (v₀ * z * v₀⁻¹) * v₀⁻¹) * v₀⁻¹ := by rw [ha3]; group
      _ = z := by rw [hz, h3, hu]
  rcases c.b66.N_ord v₀ hv with h | h
  · rw [← h]; exact pow_orderOf_eq_one v₀
  · exfalso
    obtain ⟨k, hk⟩ := h ⟨v₀, Subgroup.mem_zpowers v₀⟩
    have hk' : v₀ ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3dvd : ¬ 3 ∣ 2 ^ k := fun hd => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
    have hr0 : 2 ^ k % 3 ≠ 0 := fun h0 => h3dvd (Nat.dvd_of_mod_eq_zero h0)
    have hr3 : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hprod : (v₀ ^ 3) ^ (2 ^ k / 3) * v₀ ^ (2 ^ k % 3) = 1 := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]; exact hk'
    generalize 2 ^ k / 3 = m at hprod
    generalize 2 ^ k % 3 = r at hprod hr0 hr3
    rw [hpow3] at hprod
    have hcomm3 : Commute a3 z := by
      show a3 * z = z * a3
      calc a3 * z = (a3 * z * a3⁻¹) * a3 := by group
        _ = z * a3 := by rw [hcyc]
    have hcommm : a3 ^ m * z = z * a3 ^ m := (Commute.pow_left hcomm3 m).eq
    have hvr : v₀ ^ r = (a3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hkey : v₀ ^ r * z * (v₀ ^ r)⁻¹ = z := by
      rw [hvr, inv_inv]
      calc (a3 ^ m)⁻¹ * z * a3 ^ m = (a3 ^ m)⁻¹ * (z * a3 ^ m) := by group
        _ = (a3 ^ m)⁻¹ * (a3 ^ m * z) := by rw [hcommm]
        _ = z := by group
    have hr12 : r = 1 ∨ r = 2 := by omega
    have hu1 : u ≠ 1 := fun h => by
      have := c.hs.u_ord
      rw [h, orderOf_one] at this
      omega
    rcases hr12 with h1 | h1
    · rw [h1, pow_one] at hkey
      apply hu1
      have h2 : z * u = z * 1 := by rw [← hz, hkey, mul_one]
      exact mul_left_cancel h2
    · rw [h1] at hkey
      apply c.hs.u_ne
      calc u = v₀ * (v₀ * z * v₀⁻¹) * v₀⁻¹ := by rw [hz, h3]
        _ = v₀ ^ 2 * z * (v₀ ^ 2)⁻¹ := by rw [pow_two]; group
        _ = z := hkey

theorem Cfg3.no_three_cycle (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {v₀ : G} (hv : v₀ ∈ NN z u)
    (hz : v₀ * z * v₀⁻¹ = z * u) (hX : cjL v₀ (XX t X₁) = Y) (h3 : v₀ * (z * u) * v₀⁻¹ = u) :
    False := by
  have hv3 : v₀ ^ 3 = 1 := c.v0_cube hv hz h3
  have hv3' : v₀ * v₀ * v₀ = 1 := by rw [← hv3]; simp [pow_succ, mul_assoc]
  set Y₂ : Subgroup G := cjL v₀ Y with hY₂
  have hYY2 : ∀ a ∈ Y, ∀ b ∈ Y₂, a * b = b * a := by
    intro a ha b hb
    rw [← hX] at ha
    have ha' : v₀⁻¹ * a * v₀ ∈ XX t X₁ := mem_cjL.mp ha
    have hb' : v₀⁻¹ * b * v₀ ∈ Y := mem_cjL.mp hb
    have h := c.XX_comm _ ha' _ hb'
    calc a * b = v₀ * ((v₀⁻¹ * a * v₀) * (v₀⁻¹ * b * v₀)) * v₀⁻¹ := by group
      _ = v₀ * ((v₀⁻¹ * b * v₀) * (v₀⁻¹ * a * v₀)) * v₀⁻¹ := by rw [h]
      _ = b * a := by group
  have hXX : XX t X₁ = cjL v₀ Y₂ := by
    rw [hY₂, ← hX, cjL_cjL, cjL_cjL]
    have : v₀ * v₀ * v₀ = 1 := hv3'
    rw [this, cjL_one]
  have hY2X : ∀ a ∈ Y₂, ∀ b ∈ XX t X₁, a * b = b * a := by
    intro a ha b hb
    have hb2 : b ∈ cjL v₀ Y₂ := by rw [← hXX]; exact hb
    have hb' : v₀⁻¹ * b * v₀ ∈ Y₂ := mem_cjL.mp hb2
    have ha' : v₀⁻¹ * a * v₀ ∈ Y := mem_cjL.mp ha
    have h := hYY2 _ ha' _ hb'
    calc a * b = v₀ * ((v₀⁻¹ * a * v₀) * (v₀⁻¹ * b * v₀)) * v₀⁻¹ := by group
      _ = v₀ * ((v₀⁻¹ * b * v₀) * (v₀⁻¹ * a * v₀)) * v₀⁻¹ := by rw [h]
      _ = b * a := by group
  have hXXc : ∀ a ∈ XX t X₁, ∀ b ∈ XX t X₁, a * b = b * a := fun a ha b hb =>
    c.b83.XY_ab.1 a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_left hb)
  have hA2 : ∀ x ∈ XX t X₁ ⊔ Y, ∀ w ∈ Y₂, x * w = w * x :=
    commute_sup_left (fun a ha w hw => (hY2X w hw a ha).symm) (fun b hb w hw => hYY2 b hb w hw)
  have hY2u : ∀ w ∈ Y₂, u * w * u⁻¹ = w := by
    intro w hw
    have hw' : v₀⁻¹ * w * v₀ ∈ Y := mem_cjL.mp hw
    have h1 : (v₀⁻¹ * w * v₀) * (z * u) = (z * u) * (v₀⁻¹ * w * v₀) :=
      Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hw')
    calc u * w * u⁻¹ = (v₀ * (z * u) * v₀⁻¹) * w * (v₀ * (z * u) * v₀⁻¹)⁻¹ := by rw [h3]
      _ = v₀ * ((z * u) * (v₀⁻¹ * w * v₀) * (z * u)⁻¹) * v₀⁻¹ := by group
      _ = v₀ * ((v₀⁻¹ * w * v₀) * (z * u) * (z * u)⁻¹) * v₀⁻¹ := by rw [← h1]
      _ = w := by group
  have hdisj : (XX t X₁ ⊔ Y) ⊓ Y₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hwA, hwY⟩
    have h1 : u * w * u⁻¹ = w⁻¹ := c.b83.u_inv w hwA
    have h2 := hY2u w hwY
    have h3' : w = w⁻¹ := h2.symm.trans h1
    have hsq : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← h3']
        _ = 1 := by group
    have h5 : w ^ 5 = 1 := c.b83.XY_ab.2 w hwA
    have : w = 1 := by
      calc w = w ^ 5 * (w * w)⁻¹ * (w * w)⁻¹ := by group
        _ = 1 := by rw [h5, hsq]; simp
    rw [this]; exact Subgroup.one_mem _
  have hcardY2 : Nat.card ↥Y₂ = 25 := by rw [hY₂, card_cjL]; exact c.b83.Y_card
  have hD : Nat.card ↥(XX t X₁ ⊔ Y ⊔ Y₂ : Subgroup G) = 5 ^ 6 := by
    rw [card_sup_of_commute_disjoint hA2 hdisj, c.b83.XY_card, hcardY2]; norm_num
  have hDC : XX t X₁ ⊔ Y ⊔ Y₂ ≤ CZ t X₁ := by
    have hle : XZ t X₁ ≤ XX t X₁ := inf_le_left
    have hcent : XX t X₁ ⊔ Y ⊔ Y₂ ≤ centralizer ((XX t X₁ : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => hXXc b hb a ha
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => c.XX_comm b hb a ha
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => (hY2X a ha b hb).symm
    exact hcent.trans (Subgroup.centralizer_le hle)
  have hdvd : 5 ^ 6 ∣ Nat.card ↥(CZ t X₁) := hD ▸ Subgroup.card_dvd_of_le hDC
  have hfac := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
    Nat.card_pos.ne').mp hdvd
  have := c.b83.C0_five
  omega

end L84c

end CFSG.GH74.GLS.LU.Local.Five
