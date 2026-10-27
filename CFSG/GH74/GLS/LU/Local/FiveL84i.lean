module

public import CFSG.GH74.GLS.LU.Local.FiveL84h
public import CFSG.GH74.GLS.LU.Local.FiveL84b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem eq_zpowers_of_card_five {L : Subgroup G} (hL : Nat.card ↥L = 5) {a : G} (ha : a ∈ L)
    (ha1 : a ≠ 1) : L = zpowers a := by
  have hord : orderOf a = 5 := by
    have hdvd : orderOf a ∣ 5 := by
      rw [← hL]
      exact (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥L) ▸ orderOf_dvd_natCard (⟨a, ha⟩ : ↥L))
    have hp : Nat.Prime 5 := by norm_num
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact (Subgroup.zpowers_le).2 ha
  · rw [Nat.card_zpowers, hord, hL]

theorem orderOf_eq_five_of_card {L : Subgroup G} (hL : Nat.card ↥L = 5) {a : G} (ha : a ∈ L)
    (ha1 : a ≠ 1) : orderOf a = 5 := by
  have := eq_zpowers_of_card_five hL ha ha1
  rw [this, Nat.card_zpowers] at hL
  exact hL

theorem Cfg2.X1_sup_w1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : X₁ ⊔ cjL w₁ X₁ = K₁ := by
  have hle : X₁ ≤ K₁ := c.b82.X₁_syl.1
  have hle' : cjL w₁ X₁ ≤ K₁ := by
    intro x hx
    have hx' : w₁⁻¹ * x * w₁ ∈ X₁ := mem_cjL.mp hx
    have : x = w₁ * (w₁⁻¹ * x * w₁) * w₁⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem c.b66.w₁_mem (hle hx')) (inv_mem c.b66.w₁_mem)
  exact c.sup_eq_K1 hle hle' c.card_X1 ((card_cjL w₁ X₁).trans c.card_X1)
    (fun h => c.w₁_not_normalizes_X1 h.symm)

theorem Cfg2.w1_mem_closure (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {a : G} (ha : a ∈ X₁)
    (ha1 : a ≠ 1) : w₁ ∈ Subgroup.closure ({a, w₁ * a * w₁⁻¹} : Set G) := by
  have h1 : X₁ = zpowers a := eq_zpowers_of_card_five c.card_X1 ha ha1
  have h2 : cjL w₁ X₁ = zpowers (w₁ * a * w₁⁻¹) := by
    rw [h1]
    exact MonoidHom.map_zpowers (MulAut.conj w₁).toMonoidHom a
  have h3 : Subgroup.closure ({a, w₁ * a * w₁⁻¹} : Set G) = zpowers a ⊔ zpowers (w₁ * a * w₁⁻¹) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [h3, ← h1, ← h2, c.X1_sup_w1]
  exact c.b66.w₁_mem

@[expose] def conjEquiv (H : Subgroup G) (n : G) (hn : cjL n H = H) : ↥H ≃* ↥H where
  toFun h := ⟨n * h * n⁻¹, by
    have : n * (h : G) * n⁻¹ ∈ cjL n H := mem_cjL_self h.2
    rwa [hn] at this⟩
  invFun h := ⟨n⁻¹ * h * n, by
    have : h.1 ∈ cjL n H := by rw [hn]; exact h.2
    exact mem_cjL.mp this⟩
  left_inv h := by ext; simp [mul_assoc]
  right_inv h := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem Cfg2.H_comm (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  obtain ⟨e⟩ := c.b66.H_iso
  intro a ha b hb
  have : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val this

omit [Finite G] in
theorem conj_u_of {z u v : G} (hu2 : u * u = 1)
    (hvz : v * z * v⁻¹ = z * u) (hvzu : v * (z * u) * v⁻¹ = z) : v * u * v⁻¹ = u := by
  have h1 : v * (z * u) * v⁻¹ = (v * z * v⁻¹) * (v * u * v⁻¹) := by group
  rw [hvzu, hvz] at h1
  have h2 : v * u * v⁻¹ = (z * u)⁻¹ * z := by
    calc v * u * v⁻¹ = (z * u)⁻¹ * ((z * u) * (v * u * v⁻¹)) := by group
      _ = (z * u)⁻¹ * z := by rw [← h1]
  rw [h2]
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [mul_inv_rev, hu]
  group

theorem Cfg2.cube_aux (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁)
    (hv : v ∈ NN z u) (hvz : v * z * v⁻¹ = z * u) (hvzu : v * (z * u) * v⁻¹ = z) :
    (w₁ * v) ^ 3 = 1 := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hvu : v * u * v⁻¹ = u := conj_u_of hu2 hvz hvzu
  have hw1z : w₁ * z * w₁⁻¹ = z := by
    have := c.hc.cz₁ c.b66.w₁_mem
    calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [this]
      _ = z := by group
  have hw1u : w₁ * u * w₁⁻¹ = u * z := c.b66.w₁_u
  set g : G := w₁ * v with hg
  have hgz : g * z * g⁻¹ = u := by
    have : g * z * g⁻¹ = w₁ * (v * z * v⁻¹) * w₁⁻¹ := by rw [hg]; group
    rw [this, hvz]
    have : w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
    rw [this, hw1z, hw1u]
    calc z * (u * z) = (z * u) * z := by group
      _ = (u * z) * z := by rw [hzu]
      _ = u * (z * z) := by group
      _ = u := by rw [hz2]; group
  have hgu : g * u * g⁻¹ = z * u := by
    have : g * u * g⁻¹ = w₁ * (v * u * v⁻¹) * w₁⁻¹ := by rw [hg]; group
    rw [this, hvu, hw1u, hzu]
  have hgzu : g * (z * u) * g⁻¹ = z := by
    have : g * (z * u) * g⁻¹ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
    rw [this, hgz, hgu]
    calc u * (z * u) = (u * z) * u := by group
      _ = (z * u) * u := by rw [hzu]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2]; group
  have hgN : g ∈ NN z u := mul_mem c.w₁_NN hv
  have hg3 : g ^ 3 * z * (g ^ 3)⁻¹ = z := by
    have e1 : g ^ 3 * z * (g ^ 3)⁻¹ = g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ := by
      rw [show g ^ 3 = g * g * g by rw [pow_succ, pow_succ, pow_one]]; group
    rw [e1, hgz]
    have e2 : g * (g * u * g⁻¹) * g⁻¹ = g * (z * u) * g⁻¹ := by rw [hgu]
    rw [e2, hgzu]
  rcases c.b66.N_ord g hgN with h3 | h2
  · rw [← h3]; exact pow_orderOf_eq_one g
  · exfalso
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨g, Subgroup.mem_zpowers g⟩
    have hk' : orderOf g = 2 ^ k := by
      have : orderOf (⟨g, Subgroup.mem_zpowers g⟩ : ↥(zpowers g)) = orderOf g := Subgroup.orderOf_mk g _
      rw [← this]; exact hk
    have hcomm : g * z * g⁻¹ = z := by
      by_cases hk0 : k = 0
      · have : g = 1 := by rw [hk0] at hk'; simpa using hk'
        rw [this]; group
      · have hlt : 1 < 2 ^ k := Nat.one_lt_two_pow hk0
        have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
        obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
        have hgm : g = (g ^ 3) ^ m := by
          rw [← pow_mul, ← pow_mod_orderOf, hk', hm, pow_one]
        have hc3 : Commute (g ^ 3) z := by
          have : g ^ 3 * z = z * g ^ 3 := by
            have := hg3
            calc g ^ 3 * z = (g ^ 3 * z * (g ^ 3)⁻¹) * g ^ 3 := by group
              _ = z * g ^ 3 := by rw [this]
          exact this
        have hcg : Commute g z := by
          have := hc3.pow_left m
          rwa [← hgm] at this
        exact hcg.mul_inv_cancel
    have : u = z := by rw [← hgz]; exact hcomm
    exact c.hs.u_ne this

theorem exists_natPow_of_mem_zpowers {a x : G} (hx : x ∈ zpowers a) : ∃ k : ℕ, x = a ^ k := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact ⟨k, rfl⟩

theorem exists_exp_of_hinv {L : Subgroup G} (hL : Nat.card ↥L = 5) {a : G} (ha : a ∈ L)
    (ha1 : a ≠ 1) (hH : HInv H L) {h : G} (hh : h ∈ H) : ∃ k : ℕ, h * a * h⁻¹ = a ^ k := by
  have hmem : h * a * h⁻¹ ∈ L := by
    have := hH h hh
    rw [← this]
    exact mem_cjL_self ha
  rw [eq_zpowers_of_card_five hL ha ha1] at hmem
  exact exists_natPow_of_mem_zpowers hmem

theorem Cfg3.exists_wt_ne (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {a : G} (ha : a ∈ X₁)
    (ha1 : a ≠ 1) : ∃ h ∈ H, wt a h ≠ wt (t * a * t⁻¹) h := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ : ∃ b : G, b = t * a * t⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hall
  have hbX : b ∈ XB t X₁ := by rw [hb]; exact mem_cjL_self ha
  have hb1 : b ≠ 1 := by
    intro h1
    apply ha1
    have : t⁻¹ * (t * a * t⁻¹) * t = t⁻¹ * 1 * t := by rw [← hb, h1]
    simpa [mul_assoc] using this
  have ha5 := orderOf_eq_five_of_card c.card_X1 ha ha1
  have hb5 := orderOf_eq_five_of_card c.card_X2 hbX hb1
  have ha5' : a ^ 5 = 1 := by simpa [ha5] using pow_orderOf_eq_one a
  have hb5' : b ^ 5 = 1 := by simpa [hb5] using pow_orderOf_eq_one b
  have hcomm : Commute a b := c.X1_comm_X2 a ha b hbX
  obtain ⟨d, hd⟩ : ∃ d : G, d = a * b := ⟨_, rfl⟩
  have hdXX : d ∈ XX t X₁ := by
    rw [hd]; exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbX)
  have hd1 : d ≠ 1 := by
    intro h1
    have hbi : b = a⁻¹ := by
      have : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [← hd, h1]
      simpa using this
    have hbX1 : b ∈ X₁ := by rw [hbi]; exact inv_mem ha
    have : b ∈ X₁ ⊓ XB t X₁ := ⟨hbX1, hbX⟩
    rw [c.X1_inf_X2] at this
    exact hb1 (Subgroup.mem_bot.mp this)
  have hd5 : d ^ 5 = 1 := by
    rw [hd, hcomm.mul_pow, ha5', hb5', one_mul]
  have hdord : orderOf d = 5 := orderOf_eq_prime hd5 hd1
  have hDcard : Nat.card ↥(zpowers d) = 5 := by rw [Nat.card_zpowers, hdord]
  have hDinv : HInv H (zpowers d) := by
    intro h hh
    obtain ⟨k, hk⟩ := exists_exp_of_hinv c.card_X1 ha ha1 c.hinv_X1 hh
    obtain ⟨k', hk'⟩ := exists_exp_of_hinv c.card_X2 hbX hb1 c.hinv_X2 hh
    have hw1 := wt_eq ha5 hk
    have hw2 := wt_eq hb5 hk'
    have hh' := hall h hh
    rw [hw1, hw2] at hh'
    have hkk : k' ≡ k [MOD 5] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hh').symm
    have hbk : b ^ k' = b ^ k := by
      rw [pow_eq_pow_iff_modEq, hb5]; exact hkk
    have hdh : h * d * h⁻¹ = d ^ k := by
      have e1 : h * d * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by rw [hd]; group
      rw [e1, hk, hk', hbk, hd, hcomm.mul_pow]
    have hle : cjL h (zpowers d) ≤ zpowers d := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      show h * d ^ n * h⁻¹ ∈ _
      rw [← conj_zpow, hdh, ← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) _
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cjL])
  rcases c.b82.X_inv_sub (zpowers d) ((Subgroup.zpowers_le).2 hdXX) hDcard hDinv with h1 | h1
  · have hdX1 : d ∈ X₁ := by rw [← h1]; exact Subgroup.mem_zpowers d
    have hbX1 : b ∈ X₁ := by
      have h2 : a⁻¹ * d ∈ X₁ := mul_mem (inv_mem ha) hdX1
      have e : a⁻¹ * d = b := by rw [hd]; group
      rwa [e] at h2
    have : b ∈ X₁ ⊓ XB t X₁ := ⟨hbX1, hbX⟩
    rw [c.X1_inf_X2] at this
    exact hb1 (Subgroup.mem_bot.mp this)
  · have hdX2 : d ∈ XB t X₁ := by rw [← h1]; exact Subgroup.mem_zpowers d
    have haX2 : a ∈ XB t X₁ := by
      have h2 : d * b⁻¹ ∈ XB t X₁ := mul_mem hdX2 (inv_mem hbX)
      have e : d * b⁻¹ = a := by rw [hd]; group
      rwa [e] at h2
    have : a ∈ X₁ ⊓ XB t X₁ := ⟨ha, haX2⟩
    rw [c.X1_inf_X2] at this
    exact ha1 (Subgroup.mem_bot.mp this)

end CFSG.GH74.GLS.LU.Local.Five
