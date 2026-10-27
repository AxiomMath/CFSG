module

public import CFSG.GH74.GLS.LU.Local.FiveL86c
public import CFSG.GH74.GLS.LU.Local.FiveZstar
public import CFSG.GH74.GLS.LU.Local.CStruct2
public import CFSG.GH74.GLS.LU.Local.FiveGen2
public import CFSG.GH74.GLS.LU.Local.FiveGen3

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L85a

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.invol_in_CC (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {y : G}
    (hy : y ∈ centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G))
    (hy2 : y * y = 1) : y = 1 ∨ y = z := by
  rw [c.b82.CC_X2] at hy
  obtain ⟨x, hx, k, hk, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := K₁)
    (fun a ha b hb => (c.hc.comm b hb a (c.X2_le_K2 ha)).symm)).mp hy
  have hxk : Commute x k := (c.hc.comm k hk x (c.X2_le_K2 hx)).symm
  have hsq : x ^ 2 * k ^ 2 = 1 := by
    have : (x * k) ^ 2 = 1 := by rw [pow_two]; exact hy2
    rw [hxk.mul_pow] at this
    exact this
  have hx2K1 : x ^ 2 ∈ K₁ := by
    have := eq_inv_of_mul_eq_one_left hsq
    rw [this]; exact inv_mem (pow_mem hk 2)
  have hx2K2 : x ^ 2 ∈ K₂ := pow_mem (c.X2_le_K2 hx) 2
  have hx4 : x ^ 2 * x ^ 2 = 1 := c.K1_inf_K2_sq _ ⟨hx2K1, hx2K2⟩
  have hx5 : x ^ 5 = 1 := pow_five_of_card c.card_X2 hx
  have hx1 : x = 1 := by
    calc x = x ^ 5 * (x ^ 2 * x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx5, hx4]; simp
  subst hx1
  have hk2 : k * k = 1 := by simpa [pow_two] using hsq
  have hz : k ∈ zpowers z := by
    have hodd : Odd (p ^ f) := (c.ctx.prime.odd_of_ne_two c.ctx.odd).pow
    exact involution_mem_zpowers₁ c.hc hodd hk hk2
  rcases mem_zpowers_of_sq_eq_one c.hs.z_sq hz with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem Cfg2.z_isolated (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {g : G}
    (hg : g ∈ normalizer ((XB t X₁ : Subgroup G) : Set G))
    (hc2 : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) : g⁻¹ * z * g = z := by
  have hz2 : z * z = 1 := c.hs.z_sq
  have hy2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hyC : g⁻¹ * z * g ∈ centralizer ((XB t X₁ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgx : g * x * g⁻¹ ∈ XB t X₁ := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have hzK : (g * x * g⁻¹) * z = z * (g * x * g⁻¹) := c.hc.cz₂ (c.X2_le_K2 hgx)
    calc x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [hzK]
      _ = (g⁻¹ * z * g) * x := by group
  rcases c.invol_in_CC ⟨hyC, hc2⟩ hy2 with h | h
  · exfalso
    have : z = 1 := by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hord := c.hs.z_inv
    rw [this, orderOf_one] at hord
    omega
  · exact h

theorem Cfg2.H_two (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : IsPGroup 2 ↥H :=
  IsPGroup.of_card (n := 4) (by rw [c.H_card]; norm_num)

theorem Cfg2.z_mem_M (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    z ∈ normalizer ((XB t X₁ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_cjL_eq
  apply cjL_eq_of_comm
  intro a ha
  exact (c.hc.cz₂ (c.X2_le_K2 ha)).symm

theorem Cfg2.z_ne_one (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : z ≠ 1 := by
  intro h
  have := c.hs.z_inv
  rw [h, orderOf_one] at this
  omega

theorem Cfg2.X2_le_RR (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : XB t X₁ ≤ RR t X₁ := by
  have h5 : IsPGroup 5 ↥(XB t X₁) := IsPGroup.of_card (n := 1) (by rw [c.card_X2]; norm_num)
  have hM : XB t X₁ ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) := Subgroup.le_normalizer
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 5 hM (fun x hx => hx) h5

theorem Cfg2.N_X2_sub (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    normalizer ((XB t X₁ : Subgroup G) : Set G) ≤ RR t X₁ ⊔ K₁ ⊔ H := by
  set M₀ := normalizer ((XB t X₁ : Subgroup G) : Set G) with hM₀
  have hz2 : z * z = 1 := c.hs.z_sq
  have hzC : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨T, hTD, hT2, hzT, hTmax⟩ := exists_max_two_subgroup (M₀ ⊓ centralizer ({z} : Set G))
    ⟨c.z_mem_M, hzC⟩ hz2 c.z_ne_one
  have key := zStar_iso_sub (M₀ := M₀) c.z_mem_M hz2 c.z_ne_one (T := T) (hTD.trans inf_le_left)
    hT2 hzT (hTD.trans inf_le_right)
    (fun P hPM hP2 hPC hTP => hTmax P (le_inf hPM hPC) hP2 hTP)
    (fun g hg hgT => c.z_isolated hg (hTD.trans inf_le_right hgT))
  set O : Subgroup G := (CFSG.oddCore ↥M₀).map M₀.subtype with hO
  have hOodd : Odd (Nat.card ↥O) := by
    rw [hO, Nat.card_congr (Subgroup.equivMapOfInjective _ _ M₀.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore' _
  have hMnorm : M₀ ≤ normalizer (O : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨o, ho, rfl⟩
      have := (inferInstance : (CFSG.oddCore ↥M₀).Normal).conj_mem o ho ⟨x, hx⟩
      exact ⟨_, this, rfl⟩
    · rintro ⟨o, ho, hoy⟩
      have := (inferInstance : (CFSG.oddCore ↥M₀).Normal).conj_mem o ho ⟨x, hx⟩⁻¹
      refine ⟨_, this, ?_⟩
      have h2 : (o : G) = x * y * x⁻¹ := hoy
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, h2]
      group
  have hHO : HInv H O := fun h hh =>
    cjL_eq_of_mem_normalizer (hMnorm (c.H_le_normalizer_X2 hh))
  have hO5 : IsPGroup 5 ↥O :=
    isPGroup_five_of_noInv c.H_two hOodd hHO c.b82.no_inv_sub
  have hOR : O ≤ RR t X₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 5 (Subgroup.map_subtype_le _) hMnorm hO5
  intro m hm
  obtain ⟨cc, hcc, k, hk, rfl⟩ := key m hm
  have hcc' : cc ∈ XB t X₁ ⊔ K₁ ⊔ H := by
    have h0 : M₀ ⊓ centralizer ({z} : Set G) = XB t X₁ ⊔ K₁ ⊔ H := c.b82.NC_X2
    rw [← h0]; exact hcc
  have h1 : XB t X₁ ⊔ K₁ ⊔ H ≤ RR t X₁ ⊔ K₁ ⊔ H :=
    sup_le_sup_right (sup_le_sup_right c.X2_le_RR K₁) H
  have h2 : k ∈ RR t X₁ ⊔ K₁ ⊔ H := (le_sup_left.trans le_sup_left : RR t X₁ ≤ _) (hOR hk)
  exact mul_mem (h1 hcc') h2

theorem Cfg2.five_normal_in_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {N : Subgroup G} (hN : N ≤ K₁)
    (h5 : IsPGroup 5 ↥N) (hnorm : ∀ k ∈ K₁, ∀ n ∈ N, k * n * k⁻¹ ∈ N) : N = ⊥ := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardq : Nat.card (ZMod 5) = p ^ f := by rw [c.ctx.pf, Nat.card_zmod]
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc.sl₁ (ZMod 5) hcardq
  have hnN : K₁ ≤ normalizer (N : Set G) := by
    intro k hk
    apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
    exact fun n hn => hnorm k hk n hn
  have : (N.subgroupOf K₁).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hnN
  have hcardeq : Nat.card ↥(N.subgroupOf K₁) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp h5)
  rcases sl2_five_normal_cases e (N.subgroupOf K₁) with h | h | h
  · rw [h, Subgroup.card_bot] at hcardeq
    exact Subgroup.eq_bot_of_card_eq _ hcardeq.symm
  · exfalso
    have hc2 := sl2_five_center_card e
    rw [h, hc2] at hcardeq
    rw [← hcardeq] at hn
    have : (2 : ℕ) ∣ 5 ^ n := hn ▸ dvd_refl 2
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) this
    omega
  · exfalso
    have hc120 := sl2_five_card e
    rw [h, Subgroup.card_top, hc120] at hcardeq
    rw [← hcardeq] at hn
    have : (2 : ℕ) ∣ 5 ^ n := hn ▸ (by norm_num : (2 : ℕ) ∣ 120)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) this
    omega

theorem Cfg2.K1_le_normalizer_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    K₁ ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) :=
  le_normalizer_of_commute (fun a ha b hb => c.hc.comm a ha b (c.X2_le_K2 hb))

theorem Cfg2.K1_le_normalizer_RR (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    K₁ ≤ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
  c.K1_le_normalizer_X2.trans (normalizer_le_normalizer_RR t X₁)

theorem Cfg2.RR_inf_Cz (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    RR t X₁ ⊓ centralizer ({z} : Set G) = XB t X₁ := by
  apply le_antisymm
  · set A := RR t X₁ ⊓ centralizer ({z} : Set G) with hA
    have hA5 : IsPGroup 5 ↥A := (RR_pGroup t X₁).to_le inf_le_left
    have hAN : A ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) :=
      inf_le_left.trans (RR_le_normalizer t X₁)
    have hcentX := centralizes_of_five_group hA5 c.card_X2 hAN
    have hAC : ∀ a ∈ A, a ∈ centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
      fun a ha => ⟨Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcentX a ha x hx).symm), ha.2⟩
    intro a ha
    have haCC := hAC a ha
    rw [c.b82.CC_X2] at haCC
    obtain ⟨x, hx, k, hk, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := K₁)
      (fun a ha b hb => (c.hc.comm b hb a (c.X2_le_K2 ha)).symm)).mp haCC
    have hKA : ∀ k' ∈ K₁, ∀ b ∈ A, k' * b * k'⁻¹ ∈ A := by
      intro k' hk' b hb
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (c.K1_le_normalizer_RR hk') b).mp hb.1
        exact this
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hb.2
        have h2 := c.hc.cz₁ hk'
        calc k' * b * k'⁻¹ * z = k' * b * (k'⁻¹ * z) := by group
          _ = k' * b * (z * k'⁻¹) := by
              congr 1
              calc k'⁻¹ * z = k'⁻¹ * z * k' * k'⁻¹ := by group
                _ = k'⁻¹ * (z * k') * k'⁻¹ := by group
                _ = k'⁻¹ * (k' * z) * k'⁻¹ := by rw [h2]
                _ = z * k'⁻¹ := by group
          _ = k' * (b * z) * k'⁻¹ := by group
          _ = k' * (z * b) * k'⁻¹ := by rw [h1]
          _ = z * (k' * b * k'⁻¹) := by
              calc k' * (z * b) * k'⁻¹ = (k' * z) * b * k'⁻¹ := by group
                _ = (z * k') * b * k'⁻¹ := by rw [h2]
                _ = z * (k' * b * k'⁻¹) := by group
    have hN : A ⊓ K₁ = ⊥ := by
      apply c.five_normal_in_K1 inf_le_right
      · exact hA5.to_le inf_le_left
      · intro k' hk' n hn
        exact ⟨hKA k' hk' n hn.1, K₁.mul_mem (K₁.mul_mem hk' hn.2) (K₁.inv_mem hk')⟩
    have hkc : ∀ k' ∈ K₁, k' * k * k'⁻¹ * k⁻¹ = 1 := by
      intro k' hk'
      have h1 : k' * (x * k) * k'⁻¹ * (x * k)⁻¹ ∈ A := mul_mem (hKA k' hk' _ ha) (inv_mem ha)
      have hxk' : x * k' = k' * x := (c.hc.comm k' hk' x (c.X2_le_K2 hx)).symm
      have h2 : k' * (x * k) * k'⁻¹ * (x * k)⁻¹ = k' * k * k'⁻¹ * k⁻¹ := by
        have hx' : k' * x * k'⁻¹ = x := by rw [← hxk']; group
        calc k' * (x * k) * k'⁻¹ * (x * k)⁻¹ = (k' * x * k'⁻¹) * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ := by
              group
          _ = x * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ := by rw [hx']
          _ = k' * k * k'⁻¹ * k⁻¹ := by
              have hc0 : k' * k * k'⁻¹ * k⁻¹ ∈ K₁ :=
                K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hk' hk) (K₁.inv_mem hk')) (K₁.inv_mem hk)
              have hcomm : x * (k' * k * k'⁻¹ * k⁻¹) = (k' * k * k'⁻¹ * k⁻¹) * x :=
                (c.hc.comm _ hc0 x (c.X2_le_K2 hx)).symm
              calc x * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ = x * (k' * k * k'⁻¹ * k⁻¹) * x⁻¹ := by group
                _ = (k' * k * k'⁻¹ * k⁻¹) := by rw [hcomm]; group
      have h3 : k' * k * k'⁻¹ * k⁻¹ ∈ A ⊓ K₁ :=
        ⟨h2 ▸ h1, K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hk' hk) (K₁.inv_mem hk')) (K₁.inv_mem hk)⟩
      rw [hN] at h3
      exact h3
    have hkz : k ∈ zpowers z := by
      have hmem : (⟨k, hk⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨g', hg'⟩
        apply Subtype.ext
        show g' * k = k * g'
        have := hkc g' hg'
        calc g' * k = (g' * k * g'⁻¹ * k⁻¹) * k * g' := by group
          _ = k * g' := by rw [this]; group
      rw [← c.hc.cen₁]
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    have hk1 : k = 1 := by
      rcases mem_zpowers_of_sq_eq_one c.hs.z_sq hkz with h | h
      · exact h
      · exfalso
        obtain ⟨n, hn⟩ := RR_pGroup t X₁ ⟨x * k, ha.1⟩
        have hn' : (x * k) ^ (5 ^ n) = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        have hxz : Commute x z := (c.hc.cz₂ (c.X2_le_K2 hx))
        rw [h, hxz.mul_pow] at hn'
        have hz5 : z ^ (5 ^ n) = z := by
          have hodd : Odd (5 ^ n) := Odd.pow (by decide)
          obtain ⟨m, hm⟩ := hodd
          rw [hm, pow_succ, pow_mul, pow_two, c.hs.z_sq, one_pow, one_mul]
        rw [hz5] at hn'
        have hzX : z ∈ XB t X₁ := by
          have : z = (x ^ (5 ^ n))⁻¹ := eq_inv_of_mul_eq_one_right hn'
          rw [this]; exact inv_mem (pow_mem hx _)
        have h5 : z ^ 5 = 1 := pow_five_of_card c.card_X2 hzX
        have h2 : z ^ 2 = 1 := by rw [pow_two]; exact c.hs.z_sq
        apply c.z_ne_one
        calc z = z ^ 5 * ((z ^ 2)⁻¹) ^ 2 := by group
          _ = 1 := by rw [h5, h2]; simp
    rw [hk1, mul_one]
    exact hx
  · intro x hx
    exact ⟨c.X2_le_RR hx, Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₂ (c.X2_le_K2 hx))⟩

theorem Cfg2.z_inv_R (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    (∀ r ∈ RR t X₁, (z * r * z⁻¹) * r ∈ XB t X₁) ∧
      (∀ r ∈ RR t X₁, ∀ s ∈ RR t X₁, r * s * r⁻¹ * s⁻¹ ∈ XB t X₁) :=
  inverts_quotient_of_fixed (M₀ := normalizer ((XB t X₁ : Subgroup G) : Set G)) (R := RR t X₁)
    (X := XB t X₁) c.hs.z_sq c.z_mem_M (normalizer_le_normalizer_RR t X₁) le_rfl c.X2_le_RR
    (RR_le_normalizer t X₁) (by rw [c.card_X2]; decide) (by
      intro r hr hfix
      rw [← c.RR_inf_Cz]
      refine ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc r * z = (z * r * z⁻¹) * z := by rw [hfix]
        _ = z * r := by group)

theorem Cfg2.N_X2_eq (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    normalizer ((XB t X₁ : Subgroup G) : Set G) = RR t X₁ ⊔ K₁ ⊔ H :=
  le_antisymm c.N_X2_sub (sup_le (sup_le (RR_le_normalizer t X₁) c.K1_le_normalizer_X2)
    c.H_le_normalizer_X2)

end L85a

end CFSG.GH74.GLS.LU.Local.Five
