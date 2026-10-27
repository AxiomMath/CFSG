module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

theorem line_double {W : Type} [CommGroup W] {u : ℤ → W} (hW : ∀ w : W, w ^ 2 = 1) (κ : ℤ)
    (hinj : ∀ i j, u i = u j → i % 7 = j % 7)
    (hT : ∀ a b c m : ℤ, u a * u b = u c → u (a + m) * u (b + m) = u (c + m))
    (hS : ∀ a b c : ℤ, u a * u b = u c → u (κ - a) * u (κ - b) = u (κ - c))
    {j k : ℤ} (h : u 0 * u j = u k) : (2 * k) % 7 = j % 7 := by
  have hsq : ∀ i, u i * u i = 1 := fun i => by rw [← pow_two]; exact hW _
  have h2 : u j * u k = u 0 := by
    calc u j * u k = u j * (u 0 * u j) := by rw [h]
      _ = u 0 * (u j * u j) := mul_left_comm _ _ _
      _ = u 0 := by rw [hsq, mul_one]
  have h3 : u 0 * u (k - j) = u (-j) := by
    have := hT j k 0 (-j) h2
    rwa [show j + -j = 0 by ring, show k + -j = k - j by ring, show 0 + -j = -j by ring] at this
  have h5 : u 0 * u (j - k) = u j := by
    have := hT _ _ _ (-κ) (hS 0 (k - j) (-j) h3)
    rwa [show κ - 0 + -κ = 0 by ring, show κ - (k - j) + -κ = j - k by ring,
      show κ - -j + -κ = j by ring] at this
  have h6 : u 0 * u k = u j := by
    calc u 0 * u k = u 0 * (u 0 * u j) := by rw [h]
      _ = (u 0 * u 0) * u j := (mul_assoc _ _ _).symm
      _ = u j := by rw [hsq, one_mul]
  have h7 : u (j - k) = u k := mul_left_cancel (h5.trans h6.symm)
  have := hinj _ _ h7
  omega

theorem no_inversion_of_order_seven {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W ≤ 16) {z s : MulAut W} (hz7 : z ^ 7 = 1) (hz1 : z ≠ 1)
    (hs : s * z * s⁻¹ = z⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf z = 7 := orderOf_eq_prime hz7 hz1
  set A : Subgroup (MulAut W) := Subgroup.zpowers z with hA
  have hAcard : Nat.card ↥A = 7 := by rw [hA, Nat.card_zpowers, hord]
  have hAodd : Odd (Nat.card ↥A) := by rw [hAcard]; decide
  have hAp : IsPGroup 7 ↥A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  set W₀ : Subgroup W := commV A with hW₀
  have hfixbot : commV A ⊓ fixV A = ⊥ := commV_inf_fixV_eq_bot_of_odd hW A hAodd
  have hzA : z ∈ A := Subgroup.mem_zpowers z
  have hfix : ∀ w ∈ W₀, z w = w → w = 1 := by
    intro w hw hzw
    have hstab : A ≤ MulAction.stabilizer (MulAut W) w :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hzw)
    have hmem : w ∈ fixV A := by
      intro a ha
      exact MulAction.mem_stabilizer_iff.mp (hstab ha)
    have : w ∈ commV A ⊓ fixV A := ⟨hw, hmem⟩
    rw [hfixbot] at this
    exact Subgroup.mem_bot.mp this
  have hAstab : A ≤ stabV W₀ := le_stabV_commV A
  have hzstab : z ∈ stabV W₀ := hAstab hzA
  have hW₀ne : ∃ w₀ ∈ W₀, w₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hz1
    ext w
    have h1 : z w * w⁻¹ ∈ W₀ := G6.mem_commV_of_mem hzA w
    have h2 := hcon _ h1
    simp only [MulAut.one_apply]
    exact mul_inv_eq_one.mp h2
  obtain ⟨w₀, hw₀, hw₀1⟩ := hW₀ne
  have hW₀card : Nat.card ↥W₀ = 8 := by
    let ρ : ↥A →* MulAut ↥W₀ := (resStab W₀).comp (Subgroup.inclusion hAstab)
    let _inst : MulAction ↥A ↥W₀ := MulAction.compHom ↥W₀ ρ
    have hmod := hAp.card_modEq_card_fixedPoints ↥W₀
    have hfixcard : Nat.card ↥(MulAction.fixedPoints ↥A ↥W₀) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, fun a => ?_⟩⟩⟩
      swap
      · show (ρ a) (1 : ↥W₀) = 1
        exact map_one _
      have hx1 : (x : ↥W₀) = 1 := by
        apply Subtype.ext
        apply hfix _ (x : ↥W₀).2
        have := x.2 ⟨z, hzA⟩
        have h2 := congrArg (fun q : ↥W₀ => (q : W)) this
        exact h2
      have hy1 : (y : ↥W₀) = 1 := by
        apply Subtype.ext
        apply hfix _ (y : ↥W₀).2
        have := y.2 ⟨z, hzA⟩
        have h2 := congrArg (fun q : ↥W₀ => (q : W)) this
        exact h2
      exact Subtype.ext (hx1.trans hy1.symm)
    rw [hfixcard] at hmod
    have hW₀2 : IsPGroup 2 ↥W₀ := fun w => ⟨1, Subtype.ext (by simpa using hW (w : W))⟩
    obtain ⟨d, hd⟩ := hW₀2.exists_card_eq
    have hle : Nat.card ↥W₀ ≤ 16 := (Subgroup.card_le_card_group W₀).trans hcard
    have hne1 : 1 < Nat.card ↥W₀ :=
      Finite.one_lt_card_iff_nontrivial.mpr
        ⟨⟨⟨w₀, hw₀⟩, 1, fun h => hw₀1 (by simpa using congrArg Subtype.val h)⟩⟩
    rw [hd] at hmod hle hne1 ⊢
    have hd4 : d ≤ 4 := by
      by_contra h5
      have : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hd1 : 1 ≤ d := by
      by_contra h0
      have : d = 0 := by omega
      subst this
      omega
    interval_cases d <;> simp_all [Nat.ModEq]
  have hfixed_zpow : ∀ (g : MulAut W) (x : W), g x = x → ∀ n : ℤ, (g ^ n) x = x := by
    intro g x hgx n
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut W) x :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hgx)
    exact MulAction.mem_stabilizer_iff.mp (hle (Subgroup.zpow_mem_zpowers g n))
  set u : ℤ → W := fun i => (z ^ i) w₀ with hu
  have hzpow_stab : ∀ i : ℤ, z ^ i ∈ stabV W₀ := fun i => (stabV W₀).zpow_mem hzstab i
  have hu_mem : ∀ i, u i ∈ W₀ := fun i => apply_mem_of_mem_stabV (hzpow_stab i) hw₀
  have hu_add : ∀ m i : ℤ, (z ^ m) (u i) = u (m + i) := by
    intro m i
    simp only [hu]
    rw [← MulAut.mul_apply, ← zpow_add]
  have hu_ne1 : ∀ i, u i ≠ 1 := by
    intro i h
    apply hw₀1
    have : (z ^ i) w₀ = (z ^ i) 1 := by rw [map_one]; exact h
    exact (z ^ i).injective this
  have hz7z : z ^ (7 : ℤ) = 1 := by rw [zpow_ofNat]; exact hz7
  have hinj : ∀ i j : ℤ, u i = u j → i % 7 = j % 7 := by
    intro i j hij
    by_contra hne
    have hm : (i - j) % 7 ≠ 0 := by omega
    have hfixw : (z ^ (i - j)) w₀ = w₀ := by
      have h1 : (z ^ (-j)) (u i) = (z ^ (-j)) (u j) := by rw [hij]
      rw [hu_add, hu_add] at h1
      have e1 : u (-j + i) = (z ^ (i - j)) w₀ := by
        simp only [hu]; congr 2; ring
      have e2 : u (-j + j) = w₀ := by
        simp only [hu]; rw [show -j + j = 0 by ring]; simp
      rw [e1, e2] at h1
      exact h1
    obtain ⟨n, q, hnq⟩ : ∃ n q : ℤ, n * (i - j) = 1 + 7 * q := by
      have : (i - j) % 7 = 1 ∨ (i - j) % 7 = 2 ∨ (i - j) % 7 = 3 ∨ (i - j) % 7 = 4 ∨
          (i - j) % 7 = 5 ∨ (i - j) % 7 = 6 := by omega
      rcases this with h | h | h | h | h | h
      · exact ⟨1, (i - j - 1) / 7, by omega⟩
      · exact ⟨4, (4 * (i - j) - 1) / 7, by omega⟩
      · exact ⟨5, (5 * (i - j) - 1) / 7, by omega⟩
      · exact ⟨2, (2 * (i - j) - 1) / 7, by omega⟩
      · exact ⟨3, (3 * (i - j) - 1) / 7, by omega⟩
      · exact ⟨6, (6 * (i - j) - 1) / 7, by omega⟩
    have hzeq : (z ^ (i - j)) ^ n = z := by
      rw [← zpow_mul, mul_comm, hnq, zpow_add, zpow_one, zpow_mul, hz7z, one_zpow, mul_one]
    have hzw : z w₀ = w₀ := by
      have := hfixed_zpow (z ^ (i - j)) w₀ hfixw n
      rwa [hzeq] at this
    exact hw₀1 (hfix w₀ hw₀ hzw)
  have hcover : ∀ x ∈ W₀, x ≠ 1 → ∃ i : ℤ, x = u i := by
    let g : Option (Fin 7) → ↥W₀ := fun o => o.elim 1 (fun i => ⟨u (i.val : ℤ), hu_mem _⟩)
    have hg_inj : Function.Injective g := by
      intro a b hab
      rcases a with _ | a <;> rcases b with _ | b
      · rfl
      · exfalso
        exact hu_ne1 (b.val : ℤ) (by simpa [g] using congrArg Subtype.val hab.symm)
      · exfalso
        exact hu_ne1 (a.val : ℤ) (by simpa [g] using congrArg Subtype.val hab)
      · have h1 := hinj _ _ (congrArg Subtype.val hab)
        have ha := a.2
        have hb := b.2
        have : (a : ℕ) = b := by omega
        rw [Fin.ext this]
    have hg_bij : Function.Bijective g :=
      hg_inj.bijective_of_nat_card_le (by rw [hW₀card]; simp [Nat.card_eq_fintype_card])
    intro x hx hx1
    obtain ⟨o, ho⟩ := hg_bij.2 ⟨x, hx⟩
    rcases o with _ | i
    · exfalso
      apply hx1
      simpa [g] using (congrArg Subtype.val ho).symm
    · exact ⟨i.val, by simpa [g] using (congrArg Subtype.val ho).symm⟩
  have hs' : s⁻¹ * z * s = z⁻¹ := by
    have h1 : z = s⁻¹ * z⁻¹ * s := by rw [← hs]; group
    have h2 : z⁻¹ = s⁻¹ * z * s := by
      conv_lhs => rw [h1]
      group
    exact h2.symm
  have hsA : s ∈ Subgroup.normalizer (A : Set (MulAut W)) := by
    refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have : s * z ^ k * s⁻¹ = z⁻¹ ^ k := by rw [← hs, conj_zpow]
      rw [this]
      exact A.zpow_mem (A.inv_mem hzA) k
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h1 : s⁻¹ * z ^ k * s⁻¹⁻¹ = (s⁻¹ * z * s⁻¹⁻¹) ^ k := conj_zpow.symm
      have h2 : s⁻¹ * z * s⁻¹⁻¹ = z⁻¹ := by simpa using hs'
      rw [h2] at h1
      rw [show s⁻¹ * z ^ k * s = z⁻¹ ^ k by simpa using h1]
      exact A.zpow_mem (A.inv_mem hzA) k
  have hsstab : s ∈ stabV W₀ := mem_stabV_commV hsA
  have hsw₀ : s w₀ ∈ W₀ := apply_mem_of_mem_stabV hsstab hw₀
  have hsw₀1 : s w₀ ≠ 1 := by
    intro h
    apply hw₀1
    have : s w₀ = s 1 := by rw [map_one]; exact h
    exact s.injective this
  obtain ⟨κ, hκ⟩ := hcover _ hsw₀ hsw₀1
  have hs_u : ∀ i : ℤ, s (u i) = u (κ - i) := by
    intro i
    have h1 : s * z ^ i = z ^ (-i) * s := by
      have : s * z ^ i * s⁻¹ = z ^ (-i) := by rw [← inv_zpow', ← hs, conj_zpow]
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h2 : s (u i) = (z ^ (-i)) (s w₀) := by
      simp only [hu]
      rw [← MulAut.mul_apply, h1, MulAut.mul_apply]
    rw [h2, hκ, hu_add]
    simp only [hu]
    congr 2
    ring
  have hS : ∀ a b c : ℤ, u a * u b = u c → u (κ - a) * u (κ - b) = u (κ - c) := by
    intro a b c h
    have := congrArg s h
    rwa [map_mul, hs_u, hs_u, hs_u] at this
  have hT : ∀ a b c m : ℤ, u a * u b = u c → u (a + m) * u (b + m) = u (c + m) := by
    intro a b c m h
    have := congrArg (z ^ m) h
    rw [map_mul, hu_add, hu_add, hu_add] at this
    rwa [add_comm m a, add_comm m b, add_comm m c] at this
  have hsq : ∀ i, u i * u i = 1 := fun i => by rw [← pow_two]; exact hW _
  have hE : ∃ k : ℤ, u 0 * u 1 = u k := by
    have hmem : u 0 * u 1 ∈ W₀ := W₀.mul_mem (hu_mem 0) (hu_mem 1)
    have hne : u 0 * u 1 ≠ 1 := by
      intro h
      have h1 : u 0 = u 1 := by
        calc u 0 = u 0 * (u 1 * u 1) := by rw [hsq, mul_one]
          _ = (u 0 * u 1) * u 1 := (mul_assoc _ _ _).symm
          _ = u 1 := by rw [h, one_mul]
      have := hinj _ _ h1
      omega
    obtain ⟨k, hk⟩ := hcover _ hmem hne
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hE
  have hk' : u 0 * u k = u 1 := by
    calc u 0 * u k = u 0 * (u 0 * u 1) := by rw [hk]
      _ = (u 0 * u 0) * u 1 := (mul_assoc _ _ _).symm
      _ = u 1 := by rw [hsq, one_mul]
  have h1 := line_double hW κ hinj hT hS hk
  have h2 := line_double hW κ hinj hT hS hk'
  omega

end CFSG.CGT.PushingUpLit.CGT6
