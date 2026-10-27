module

public import CFSG.GH74.GLS.LU.Local.FiveL85b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L85c

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.R2_le_normalizer' (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {A : Subgroup G}
    (hA : XB t X₁ ≤ A) (hAR : A ≤ RR t X₁) : RR t X₁ ≤ normalizer (A : Set G) := by
  intro r hr
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro a ha
  have h1 : r * a * r⁻¹ * a⁻¹ ∈ A := hA (c.z_inv_R.2 r hr a (hAR ha))
  have : r * a * r⁻¹ = (r * a * r⁻¹ * a⁻¹) * a := by group
  rw [this]
  exact mul_mem h1 ha

theorem Cfg3.u_inv_XY (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ w ∈ XB t X₁ ⊔ Y, u * w * u⁻¹ = w⁻¹ := by
  intro w hw
  have hcomm : ∀ a ∈ XB t X₁, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    c.XX_comm a ((le_sup_right : XB t X₁ ≤ XX t X₁) ha) b hb
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hcomm).mp hw
  have h1 := c.u_inv_X2 a ha
  have h2 : u * b * u⁻¹ = b⁻¹ := c.b83.u_inv b (Subgroup.mem_sup_right hb)
  have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
  rw [e, h1, h2]
  have hab : Commute a b := hcomm a ha b hb
  rw [mul_inv_rev]
  exact (hab.inv_inv).eq

theorem Cfg3.XY_inf_Cu (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    (XB t X₁ ⊔ Y) ⊓ centralizer ({u} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro w ⟨hw, hwu⟩
  have h1 := c.u_inv_XY w hw
  have h2 : u * w * u⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hwu
    calc u * w * u⁻¹ = (w * u) * u⁻¹ := by rw [this]
      _ = w := by group
  have h3 : w = w⁻¹ := h2.symm.trans h1
  have h5 : w ^ 5 = 1 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := Y)
      (fun a ha b hb => c.XX_comm a ((le_sup_right : XB t X₁ ≤ XX t X₁) ha) b hb)).mp hw
    have hab : Commute a b := c.XX_comm a ((le_sup_right : XB t X₁ ≤ XX t X₁) ha) b hb
    rw [hab.mul_pow, pow_five_of_card c.card_X2 ha, c.b83.Y_ab.2 b hb, one_mul]
  have hsq : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← h3]
      _ = 1 := by group
  have : w = 1 := by
    calc w = w ^ 5 * (w * w)⁻¹ * (w * w)⁻¹ := by group
      _ = 1 := by rw [h5, hsq]; simp
  rw [this]; exact Subgroup.one_mem _

theorem Cfg3.XY_le_RR (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : XB t X₁ ⊔ Y ≤ RR t X₁ :=
  sup_le c.X2_le_RR c.Y_le_RR

theorem Cfg3.Yw_le_RR (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : cjL w₁ Y ≤ RR t X₁ := by
  have h1 : cjL w₁ Y ≤ cjL w₁ (RR t X₁) := cjL_mono w₁ c.Y_le_RR
  rwa [c.cjL_w₁_RR] at h1

theorem Cfg3.D5_le_RR (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    XB t X₁ ⊔ Y ⊔ cjL w₁ Y ≤ RR t X₁ := sup_le c.XY_le_RR c.Yw_le_RR

theorem Cfg3.card_D5 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    Nat.card ↥(XB t X₁ ⊔ Y ⊔ cjL w₁ Y : Subgroup G) = 5 ^ 5 := by
  have hY'N : cjL w₁ Y ≤ normalizer ((XB t X₁ ⊔ Y : Subgroup G) : Set G) :=
    c.Yw_le_RR.trans (c.R2_le_normalizer' (le_sup_left : XB t X₁ ≤ XB t X₁ ⊔ Y) c.XY_le_RR)
  have h := card_sup_mul_card_inf' hY'N
  have hinf : cjL w₁ Y ⊓ (XB t X₁ ⊔ Y) = ⊥ := by
    rw [eq_bot_iff, ← c.XY_inf_Cu]
    intro w ⟨hw1, hw2⟩
    refine ⟨hw2, ?_⟩
    have : w ∈ centralizer ({u} : Set G) ⊓ RR t X₁ := by rw [← c.Yw_eq]; exact hw1
    exact this.1
  rw [hinf, Subgroup.card_bot, mul_one, c.card_Yw, c.W_card, sup_comm] at h
  rw [h]; norm_num

theorem Cfg2.card_cent_of_conj (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {a : G} (ha : IsConj z a) :
    Nat.card ↥(centralizer ({a} : Set G)) = 28800 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have : cjL g (centralizer ({z} : Set G)) = centralizer ({a} : Set G) := by
    ext x
    rw [mem_cjL, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← hg]
    constructor
    · intro h
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * x := by group
    · intro h
      calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
        _ = z * (g⁻¹ * x * g) := by group
  rw [← this, card_cjL]
  exact c.b82.card_C

theorem Cfg3.RR_cent_zu (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {r : G} (hr : r ∈ RR t X₁)
    (hc : (z * u) * r * (z * u)⁻¹ = r) : r ∈ Y := by
  have hzu : IsConj z (z * u) := by
    have h := c.hs.uz_conj
    rwa [show u * z = z * u from c.hs.zu_comm.symm] at h
  have hcard := c.card_cent_of_conj hzu
  have hP : IsPGroup 5 ↥(centralizer ({z * u} : Set G) ⊓ RR t X₁ : Subgroup G) :=
    (RR_pGroup t X₁).to_le inf_le_right
  have hle := card_le_of_five_le hP (inf_le_left : centralizer ({z * u} : Set G) ⊓ RR t X₁ ≤ _) hcard
  have hYP : Y ≤ centralizer ({z * u} : Set G) ⊓ RR t X₁ := le_inf c.b83.Y_syl.1 c.Y_le_RR
  have heq : Y = centralizer ({z * u} : Set G) ⊓ RR t X₁ :=
    Subgroup.eq_of_le_of_card_ge hYP (by rw [c.b83.Y_card]; exact hle)
  rw [heq]
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hr⟩
  calc r * (z * u) = ((z * u) * r * (z * u)⁻¹) * (z * u) := by rw [hc]
    _ = (z * u) * r := by group

omit [Finite G] in
theorem mem_of_three_rel {R D : Subgroup G} (hDR : D ≤ R) (hDn : R ≤ normalizer (D : Set G))
    (h5 : IsPGroup 5 ↥R) {r b c : G} (hr : r ∈ R) (hb : b ∈ R) (hc : c ∈ R)
    (h1 : b * r ∈ D) (h2 : c * b ∈ D) (h3 : c * r ∈ D) : r ∈ D := by
  have hDnormal : (D.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDR).mpr hDn
  have e1 : (QuotientGroup.mk ⟨b, hb⟩ : ↥R ⧸ D.subgroupOf R) * QuotientGroup.mk ⟨r, hr⟩ = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact h1
  have e2 : (QuotientGroup.mk ⟨c, hc⟩ : ↥R ⧸ D.subgroupOf R) * QuotientGroup.mk ⟨b, hb⟩ = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact h2
  have e3 : (QuotientGroup.mk ⟨c, hc⟩ : ↥R ⧸ D.subgroupOf R) * QuotientGroup.mk ⟨r, hr⟩ = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact h3
  set x : ↥R ⧸ D.subgroupOf R := QuotientGroup.mk ⟨r, hr⟩ with hx
  set y : ↥R ⧸ D.subgroupOf R := QuotientGroup.mk ⟨b, hb⟩ with hy
  set w : ↥R ⧸ D.subgroupOf R := QuotientGroup.mk ⟨c, hc⟩ with hw
  have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_left e1
  have hwy : w = y⁻¹ := eq_inv_of_mul_eq_one_left e2
  have hwx : w = x⁻¹ := eq_inv_of_mul_eq_one_left e3
  have hxx : x * x = 1 := by
    have : x⁻¹ = x := by
      calc x⁻¹ = w := hwx.symm
        _ = y⁻¹ := hwy
        _ = x := by rw [hyx, inv_inv]
    calc x * x = x * x⁻¹ := by rw [this]
      _ = 1 := by group
  obtain ⟨n, hn⟩ := h5 ⟨r, hr⟩
  have hxn : x ^ (5 ^ n) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, hn]; rfl
  have hodd : Odd (5 ^ n) := Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hx1 : x = 1 := by
    calc x = x ^ (5 ^ n) * (x * x)⁻¹ ^ j := by
          rw [hj]; group
      _ = 1 := by rw [hxn, hxx]; simp
  rw [hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx1
  exact hx1

theorem normalizer_sup_of {g : G} {A B : Subgroup G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_cjL_eq
  rw [cjL_sup, cjL_eq_of_mem_normalizer hA, cjL_eq_of_mem_normalizer hB]

theorem Cfg3.z_inv_Yw (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ y ∈ cjL w₁ Y, z * y * z⁻¹ = y⁻¹ := by
  intro y hy
  have hy0 : w₁⁻¹ * y * w₁ ∈ Y := mem_cjL.mp hy
  have hzw : z * w₁ = w₁ * z := (c.hc.cz₁ c.b66.w₁_mem).symm
  have h1 := c.z_inv_Y _ hy0
  calc z * y * z⁻¹ = w₁ * (z * (w₁⁻¹ * y * w₁) * z⁻¹) * w₁⁻¹ := by
        calc z * y * z⁻¹ = (z * w₁) * (w₁⁻¹ * y * w₁) * (z * w₁)⁻¹ := by group
          _ = (w₁ * z) * (w₁⁻¹ * y * w₁) * (w₁ * z)⁻¹ := by rw [hzw]
          _ = _ := by group
    _ = w₁ * (w₁⁻¹ * y * w₁)⁻¹ * w₁⁻¹ := by rw [h1]
    _ = y⁻¹ := by group

theorem Cfg3.u_cent_Yw (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ y ∈ cjL w₁ Y, u * y * u⁻¹ = y := by
  intro y hy
  have : y ∈ centralizer ({u} : Set G) ⊓ RR t X₁ := by rw [← c.Yw_eq]; exact hy
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp this.1
  calc u * y * u⁻¹ = (y * u) * u⁻¹ := by rw [h1]
    _ = y := by group

theorem Cfg3.RR_le_D5 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    RR t X₁ ≤ XB t X₁ ⊔ Y ⊔ cjL w₁ Y := by
  set D := XB t X₁ ⊔ Y ⊔ cjL w₁ Y with hD
  have hDR : D ≤ RR t X₁ := c.D5_le_RR
  have hXD : XB t X₁ ≤ D := le_sup_left.trans le_sup_left
  have hRD : RR t X₁ ≤ normalizer (D : Set G) := c.R2_le_normalizer' hXD hDR
  have hodd : Odd (Nat.card ↥D) := by rw [hD, c.card_D5]; decide
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hu_RR : u ∈ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    normalizer_le_normalizer_RR t X₁ (c.H_le_normalizer_X2 c.b66.u_mem)
  have hz_RR : z ∈ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    normalizer_le_normalizer_RR t X₁ c.z_mem_M
  have hX_comm_z : ∀ a ∈ XB t X₁, z * a * z⁻¹ = a := fun a ha => by
    have := c.hc.cz₂ (c.X2_le_K2 ha)
    calc z * a * z⁻¹ = (a * z) * z⁻¹ := by rw [← this]
      _ = a := by group
  have hu_D : u ∈ normalizer (D : Set G) := by
    refine normalizer_sup_of (normalizer_sup_of ?_ ?_) ?_
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha; rw [c.u_inv_X2 a ha]; exact inv_mem ha
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha; rw [c.b83.u_inv a (Subgroup.mem_sup_right ha)]; exact inv_mem ha
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha; rw [c.u_cent_Yw a ha]; exact ha
  have huz_D : u * z ∈ normalizer (D : Set G) := by
    refine normalizer_sup_of (normalizer_sup_of ?_ ?_) ?_
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha
      have e : u * z * a * (u * z)⁻¹ = u * (z * a * z⁻¹) * u⁻¹ := by group
      rw [e, hX_comm_z a ha, c.u_inv_X2 a ha]; exact inv_mem ha
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha
      have e : u * z * a * (u * z)⁻¹ = u * (z * a * z⁻¹) * u⁻¹ := by group
      have e2 : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
      rw [e, c.z_inv_Y a ha, e2, c.b83.u_inv a (Subgroup.mem_sup_right ha), inv_inv]; exact ha
    · apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
      intro a ha
      have e : u * z * a * (u * z)⁻¹ = u * (z * a * z⁻¹) * u⁻¹ := by group
      have e2 : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
      rw [e, c.z_inv_Yw a ha, e2, c.u_cent_Yw a ha]; exact inv_mem ha
  have hMu : u ∈ normalizer (D : Set G) ⊓ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    ⟨hu_D, hu_RR⟩
  have huz_RR : u * z ∈ normalizer ((RR t X₁ : Subgroup G) : Set G) := mul_mem hu_RR hz_RR
  have hMuz : u * z ∈ normalizer (D : Set G) ⊓ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    ⟨huz_D, huz_RR⟩
  have huz2 : (u * z) * (u * z) = 1 := by
    calc (u * z) * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hzu]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hu2, hz2, one_mul]
  have hfixu : ∀ r ∈ RR t X₁, u * r * u⁻¹ = r → r ∈ D := by
    intro r hr hfix
    have : r ∈ centralizer ({u} : Set G) ⊓ RR t X₁ := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hr⟩
      calc r * u = (u * r * u⁻¹) * u := by rw [hfix]
        _ = u * r := by group
    rw [← c.Yw_eq] at this
    exact (le_sup_right : cjL w₁ Y ≤ D) this
  have hfixuz : ∀ r ∈ RR t X₁, (u * z) * r * (u * z)⁻¹ = r → r ∈ D := by
    intro r hr hfix
    have hY : r ∈ Y := by
      apply c.RR_cent_zu hr
      rw [hzu]; exact hfix
    exact (le_sup_right.trans le_sup_left : Y ≤ D) hY
  have hF2 := (inverts_quotient_of_fixed (M₀ := normalizer (D : Set G) ⊓
    normalizer ((RR t X₁ : Subgroup G) : Set G)) (R := RR t X₁) (X := D) hu2 hMu inf_le_right
    inf_le_left hDR hRD hodd hfixu).1
  have hF3 := (inverts_quotient_of_fixed (M₀ := normalizer (D : Set G) ⊓
    normalizer ((RR t X₁ : Subgroup G) : Set G)) (R := RR t X₁) (X := D) huz2 hMuz inf_le_right
    inf_le_left hDR hRD hodd hfixuz).1
  intro r hr
  have hb : z * r * z⁻¹ ∈ RR t X₁ := (Subgroup.mem_normalizer_iff.mp hz_RR r).mp hr
  have hc : u * (z * r * z⁻¹) * u⁻¹ ∈ RR t X₁ := (Subgroup.mem_normalizer_iff.mp hu_RR _).mp hb
  have h1 : (z * r * z⁻¹) * r ∈ D := hXD (c.z_inv_R.1 r hr)
  have h2 : (u * (z * r * z⁻¹) * u⁻¹) * (z * r * z⁻¹) ∈ D := hF2 _ hb
  have h3 : (u * (z * r * z⁻¹) * u⁻¹) * r ∈ D := by
    have := hF3 r hr
    have e : (u * z) * r * (u * z)⁻¹ = u * (z * r * z⁻¹) * u⁻¹ := by group
    rwa [e] at this
  exact mem_of_three_rel hDR hRD (RR_pGroup t X₁) hr hb hc h1 h2 h3

theorem Cfg3.R_eq (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    RR t X₁ = XB t X₁ ⊔ Y ⊔ cjL w₁ Y := le_antisymm c.RR_le_D5 c.D5_le_RR

theorem Cfg3.R_card (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(RR t X₁) = 5 ^ 5 := by
  rw [c.R_eq]; exact c.card_D5

theorem Cfg3.Yw_ab (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    IsElemAb 5 (cjL w₁ Y) ∧ Nat.card ↥(cjL w₁ Y) = 25 := by
  refine ⟨⟨?_, ?_⟩, c.card_Yw⟩
  · intro a ha b hb
    have ha' : w₁⁻¹ * a * w₁ ∈ Y := mem_cjL.mp ha
    have hb' : w₁⁻¹ * b * w₁ ∈ Y := mem_cjL.mp hb
    have h := c.b83.Y_ab.1 _ ha' _ hb'
    calc a * b = w₁ * ((w₁⁻¹ * a * w₁) * (w₁⁻¹ * b * w₁)) * w₁⁻¹ := by group
      _ = w₁ * ((w₁⁻¹ * b * w₁) * (w₁⁻¹ * a * w₁)) * w₁⁻¹ := by rw [h]
      _ = b * a := by group
  · intro a ha
    have ha' : w₁⁻¹ * a * w₁ ∈ Y := mem_cjL.mp ha
    have h := c.b83.Y_ab.2 _ ha'
    have e : (w₁⁻¹ * a * w₁) ^ 5 = w₁⁻¹ * a ^ 5 * w₁ := by
      simpa using (conj_pow (a := w₁⁻¹) (b := a) (i := 5))
    calc a ^ 5 = w₁ * (w₁⁻¹ * a ^ 5 * w₁) * w₁⁻¹ := by group
      _ = 1 := by rw [← e, h]; group

end L85c

end CFSG.GH74.GLS.LU.Local.Five
