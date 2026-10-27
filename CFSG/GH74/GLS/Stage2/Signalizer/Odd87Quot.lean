module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem outAbelian_of_center_quotient {K : Type} [Group K] (hK : Group.IsPerfect K)
    (h : OutAbelian (K ⧸ center K)) : OutAbelian K := by
  intro α β
  have := hK
  have hinj := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  obtain ⟨y, hy⟩ := h (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K α)
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K β)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨k, hinj ?_⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hy]
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  show (QuotientGroup.mk k : K ⧸ center K) * QuotientGroup.mk x * (QuotientGroup.mk k)⁻¹ =
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (MulAut.conj k)
      (QuotientGroup.mk x)
  have := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
    (MulAut.conj k) x
  simp only [QuotientGroup.mk'_apply] at this
  rw [this, MulAut.conj_apply]
  simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]


theorem exists_odd_lift {K P : Type} [Group K] [Group P] (π : K →* P) (hπ : Function.Surjective π)
    (hk2 : IsPGroup 2 ↥π.ker) (y : P) (hy : Odd (orderOf y)) :
    ∃ k : K, π k = y ∧ k ^ orderOf y = 1 := by
  classical
  obtain ⟨k₀, hk₀⟩ := hπ y
  set m := orderOf y with hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hy; exact absurd hy (by decide)
    · exact h0
  have hw : k₀ ^ m ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk₀]; exact pow_orderOf_eq_one y
  obtain ⟨b, hb⟩ := hk2 ⟨k₀ ^ m, hw⟩
  have hb' : (k₀ ^ m) ^ (2 ^ b) = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  have hcop : Nat.Coprime m (2 ^ b) := (Nat.coprime_two_right.mpr hy).pow_right b
  obtain ⟨N0, hN1, hN2⟩ := Nat.chineseRemainder hcop 1 0
  set N := N0 + m * 2 ^ b with hN
  have hNm : N ≡ 1 [MOD m] := by
    have h0 : m * 2 ^ b ≡ 0 [MOD m] := (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right m _)
    have h := hN1.add h0
    rw [add_zero] at h
    exact h
  have hN2b : 2 ^ b ∣ N := by
    have h1 : 2 ^ b ∣ N0 := (Nat.modEq_zero_iff_dvd).1 hN2
    exact dvd_add h1 (dvd_mul_left _ _)
  have hNpos : 1 ≤ N := by
    have : 0 < m * 2 ^ b := Nat.mul_pos hmpos (pow_pos (by norm_num) b)
    omega
  refine ⟨k₀ ^ N, ?_, ?_⟩
  · rw [map_pow, hk₀]
    have hdvd : m ∣ N - 1 := (Nat.modEq_iff_dvd' hNpos).1 hNm.symm
    have h1 : y ^ (N - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
    calc y ^ N = y ^ (N - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hNpos]
      _ = y := by rw [h1, one_mul]
  · calc (k₀ ^ N) ^ m = (k₀ ^ m) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by
        obtain ⟨c, hc⟩ := hN2b
        rw [hc, pow_mul, hb', one_pow]

theorem odd_lift_unique {K P : Type} [Group K] [Group P] (π : K →* P)
    (hker : π.ker ≤ center K) (hk2 : IsPGroup 2 ↥π.ker) {m : ℕ} (hm : Odd m)
    {u v : K} (huv : π u = π v) (hu : u ^ m = 1) (hv : v ^ m = 1) : u = v := by
  have hz : u⁻¹ * v ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  have hzc : u⁻¹ * v ∈ center K := hker hz
  have hcomm : Commute u (u⁻¹ * v) := by
    exact Subgroup.mem_center_iff.mp hzc u
  have hvu : v = u * (u⁻¹ * v) := by group
  have hzm : (u⁻¹ * v) ^ m = 1 := by
    have h1 : v ^ m = u ^ m * (u⁻¹ * v) ^ m := by
      conv_lhs => rw [hvu]
      exact hcomm.mul_pow m
    rw [hv, hu, one_mul] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := hk2 ⟨u⁻¹ * v, hz⟩
  have hzc2 : (u⁻¹ * v) ^ (2 ^ c) = 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  have hcop : Nat.Coprime m (2 ^ c) := (Nat.coprime_two_right.mpr hm).pow_right c
  have h1 : (u⁻¹ * v) ^ (Nat.gcd m (2 ^ c)) = 1 := pow_gcd_eq_one.mpr ⟨hzm, hzc2⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  calc u = u * (u⁻¹ * v) := by rw [h1, mul_one]
    _ = v := by group


structure QuotCfg {P : Type} [Group P] (p : ℕ) (α : MulAut P) (Xh : Subgroup P) : Prop where
  simple : IsSimpleGroup P
  nonab : ∃ a b : P, a * b ≠ b * a
  prime : p.Prime
  odd : p ≠ 2
  pgroup : IsPGroup p ↥Xh
  ne_bot : Xh ≠ ⊥
  invol : ∀ s, α (α s) = s
  inv : ∀ x ∈ Xh, α x ∈ Xh
  comm : ∀ x ∈ Xh, x ∈ Subgroup.closure {w | ∃ y ∈ Xh, w = y * (α y)⁻¹}
  hodd : ∀ y, α y = y → Odd (orderOf y) → y ∈ normalizer (Xh : Set P)

theorem quotCfg_of_cellData {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}
    (h : CellData zb p X) (hOut : OutAbelian (↥(layer A) ⧸ center ↥(layer A))) :
    ∃ (α : MulAut (↥(layer A) ⧸ center ↥(layer A))) (Xh : Subgroup (↥(layer A) ⧸ center ↥(layer A))),
      QuotCfg p α Xh := by
  classical
  have hKn : (layer A).Normal := layer_normal
  have hOutK : OutAbelian ↥(layer A) := outAbelian_of_center_quotient h.quasi.1 hOut
  have hXK : X ≤ layer A :=
    x_le_layer_of_comm h.z2 h.A4 h.op h.gen fun x _ => comm_mem_sup_centralizer (layer A) hOutK x zb
  obtain ⟨π, α, hπ, hker, hcomm, hα2⟩ := exists_induced (layerAut zb) (layerAut_layerAut h.z2)
    (MulEquiv.refl (↥(layer A) ⧸ center ↥(layer A)))
  have hzbN : zb ∈ normalizer (X : Set A) := z_mem_normalizer_of_sig4A h.A4
  set X' : Subgroup ↥(layer A) := X.subgroupOf (layer A) with hX'
  set Xh : Subgroup (↥(layer A) ⧸ center ↥(layer A)) := X'.map π with hXh
  have hmemX' : ∀ k : ↥(layer A), k ∈ X' ↔ (k : A) ∈ X := fun k => Subgroup.mem_subgroupOf
  have hZ2 : IsPGroup 2 ↥π.ker := by
    rw [hker, h.Zcore]; exact CFSG.pCore_isPGroup
  have hX'p : IsPGroup p ↥X' := h.A4.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hXhp : IsPGroup p ↥Xh := hX'p.map π
  have hinvX : ∀ k : ↥(layer A), k ∈ X' → layerAut zb k ∈ X' := by
    intro k hk
    rw [hmemX', coe_layerAut]
    exact (Subgroup.mem_normalizer_iff.mp hzbN (k : A)).mp ((hmemX' k).mp hk)
  have hne : Xh ≠ ⊥ := by
    intro hbot
    apply h.nc
    have hcen : ∀ x ∈ X, ∀ k ∈ layer A, k * x = x * k := by
      intro x hx k hk
      have h1 : π ⟨x, hXK hx⟩ = 1 := by
        have : π ⟨x, hXK hx⟩ ∈ Xh := Subgroup.mem_map_of_mem π ((hmemX' _).mpr hx)
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have h2 : (⟨x, hXK hx⟩ : ↥(layer A)) ∈ center ↥(layer A) := by
        rw [← hker]; exact h1
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨k, hk⟩)
    rw [Subgroup.commutator_le]
    intro k hk x hx
    have : ⁅k, x⁆ = 1 := by rw [commutatorElement_def, hcen x hx k hk]; group
    rw [this]
    exact one_mem _
  have hinv : ∀ x ∈ Xh, α x ∈ Xh := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← hcomm]
    exact Subgroup.mem_map_of_mem π (hinvX x' hx')
  have hcommF : ∀ x ∈ Xh, x ∈ Subgroup.closure {w | ∃ y ∈ Xh, w = y * (α y)⁻¹} := by
    set S : Set (↥(layer A) ⧸ center ↥(layer A)) := {w | ∃ y ∈ Xh, w = y * (α y)⁻¹} with hS
    let T : Subgroup A := (Subgroup.comap π (Subgroup.closure S)).map (layer A).subtype
    have hle : ⁅X, zpowers zb⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro u hu g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hz2' : zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h.z2
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
        exact T.one_mem
      · rw [zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]
        have hk₁ : (⟨u, hXK hu⟩ : ↥(layer A)) ∈ X' := (hmemX' _).mpr hu
        refine ⟨⟨u, hXK hu⟩ * (layerAut zb ⟨u, hXK hu⟩)⁻¹, ?_, ?_⟩
        · rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, hcomm]
          exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem π hk₁, rfl⟩
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_layerAut,
            commutatorElement_def]
          group
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have hxA : (x' : A) ∈ ⁅X, zpowers zb⁆ := by
      rw [h.A4.comm]; exact (hmemX' x').mp hx'
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hle hxA)
    have : k = x' := Subtype.ext hkx
    rw [← this]
    exact Subgroup.mem_comap.mp hk
  have hnorm : ∀ g : ↥(layer A), (g : A) ∈ normalizer (X : Set A) →
      ∀ xh ∈ Xh, π g * xh * (π g)⁻¹ ∈ Xh := by
    intro g hg xh hxh
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hxh
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem π ?_
    rw [hmemX']
    simpa using (Subgroup.mem_normalizer_iff.mp hg (x' : A)).mp ((hmemX' x').mp hx')
  have hodd : ∀ y, α y = y → Odd (orderOf y) → y ∈ normalizer (Xh : Set (↥(layer A) ⧸ center ↥(layer A))) := by
    intro y hy hyo
    obtain ⟨k, hk, hkm⟩ := exists_odd_lift π hπ hZ2 y hyo
    have hker' : π.ker ≤ center ↥(layer A) := hker.le
    have hak : layerAut zb k = k := by
      refine odd_lift_unique π hker' hZ2 hyo ?_ ?_ ?_
      · rw [hcomm, hk, hy]
      · rw [← map_pow, hkm, map_one]
      · exact hkm
    have hkC : (k : A) ∈ centralizer ({zb} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := congrArg Subtype.val hak
      rw [coe_layerAut] at h2
      calc (k : A) * zb = (zb * (k : A) * zb⁻¹) * zb := by rw [h2]
        _ = zb * (k : A) := by group
    have hkN : (k : A) ∈ normalizer (X : Set A) := h.A4.inv _ (Subgroup.mem_top _) hkC
    have hkiN : ((k⁻¹ : ↥(layer A)) : A) ∈ normalizer (X : Set A) := by
      rw [Subgroup.coe_inv]; exact (normalizer (X : Set A)).inv_mem hkN
    rw [Subgroup.mem_normalizer_iff]
    intro xh
    constructor
    · intro hxh
      have := hnorm k hkN xh hxh
      rwa [hk] at this
    · intro hxh
      have := hnorm k⁻¹ hkiN _ hxh
      rw [map_inv, hk] at this
      simpa [mul_assoc] using this
  exact ⟨α, Xh, ⟨h.quasi.2.1, h.quasi.2.2, h.A4.prime, h.A4.odd, hXhp, hne, hα2, hinv, hcommF, hodd⟩⟩


theorem cell87_of_quot {F : (Y : Type) → [Group Y] → Prop}
    (hOut : ∀ (Y : Type) [Group Y] [Finite Y], F Y → OutAbelian Y)
    (hKL : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ∀ (p : ℕ) (α : MulAut Y) (Xh : Subgroup Y),
      QuotCfg p α Xh → False) : Cell87 F := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hFK
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  obtain ⟨α, Xh, hcfg⟩ := quotCfg_of_cellData hd (hOut _ hFK)
  exact hKL _ hFK p α Xh hcfg

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
