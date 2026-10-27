module

public import CFSG.GH74.GLS.LU.Local.FiveCfg
public import CFSG.GH74.GLS.LU.Local.FiveSL2
public import CFSG.GH74.GLS.LU.Local.FiveUtil

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Cfg2

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem mem_normalizer_of_cjL_eq {g : G} {A : Subgroup G} (h : cjL g A = A) :
    g ∈ normalizer (A : Set G) := by
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro x hx
  have : g * x * g⁻¹ ∈ cjL g A := mem_cjL_self hx
  rwa [h] at this

theorem cjL_eq_of_comm {g : G} {A : Subgroup G} (h : ∀ a ∈ A, g * a = a * g) : cjL g A = A := by
  ext x
  rw [mem_cjL]
  constructor
  · intro hy
    have h1 := h _ hy
    have : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    rw [this]; exact hy
  · intro hx
    have : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [h x hx]
        _ = x := by group
    rw [this]; exact hx

theorem Cfg2.X2_le_K2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : XB t X₁ ≤ K₂ := by
  have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) c.b82.X₁_syl.1
  rwa [c.hs.t_swap] at this

theorem Cfg2.XX_cent_z (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ XX t X₁, a * z = z * a := by
  have h1 : XX t X₁ ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₁ (c.b82.X₁_syl.1 ha)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₂ (c.X2_le_K2 ha)
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 ha)


theorem mem_zpowers_of_sq_eq_one {t x : G} (ht : t * t = 1) (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem cjL_vinv_of_HInv (hv2 : v * v ∈ H) {A : Subgroup G} (hA : HInv H A) :
    cjL v⁻¹ A = cjL v A := by
  calc cjL v⁻¹ A = cjL v⁻¹ (cjL (v * v) A) := by rw [hA _ hv2]
    _ = cjL (v⁻¹ * (v * v)) A := by rw [cjL_cjL]
    _ = cjL v A := by congr 1; group

theorem Cfg4.v_sq' (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : v * v ∈ H := by
  simpa [pow_two] using c.b84.v_sq

theorem Cfg2.t_XX (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : cjL t (XX t X₁) = XX t X₁ := by
  have h : cjL t (cjL t X₁) = X₁ := by rw [cjL_cjL, c.t_sq, cjL_one]
  rw [XX, cjL_sup, h, sup_comm]

theorem Cfg3.C_XY_zu (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ w ∈ XX t X₁ ⊔ Y, (z * u) * w * (z * u)⁻¹ = w → w ∈ Y := by
  intro w hw hfix
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute c.XX_comm).mp hw
  have hu : u * a * u⁻¹ = a⁻¹ := c.b83.u_inv a (Subgroup.mem_sup_left ha)
  have hza : ∀ x ∈ XX t X₁, z * x * z⁻¹ = x := fun x hx => by
    have := c.XX_cent_z x hx
    calc z * x * z⁻¹ = (z * x) * z⁻¹ := rfl
      _ = (x * z) * z⁻¹ := by rw [this]
      _ = x := by group
  have h1 : (z * u) * a * (z * u)⁻¹ = a⁻¹ := by
    calc (z * u) * a * (z * u)⁻¹ = z * (u * a * u⁻¹) * z⁻¹ := by group
      _ = z * a⁻¹ * z⁻¹ := by rw [hu]
      _ = a⁻¹ := hza _ (Subgroup.inv_mem _ ha)
  have hb' : (z * u) * b * (z * u)⁻¹ = b := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hb)
    calc (z * u) * b * (z * u)⁻¹ = (b * (z * u)) * (z * u)⁻¹ := by rw [this]
      _ = b := by group
  have h2 : a⁻¹ * b = a * b := by
    have e : (z * u) * (a * b) * (z * u)⁻¹ = ((z * u) * a * (z * u)⁻¹) * ((z * u) * b * (z * u)⁻¹) := by
      group
    rw [e, h1, hb'] at hfix
    exact hfix
  have h3 : a⁻¹ = a := mul_right_cancel h2
  have ha5 : a ^ 5 = 1 := c.b83.XY_ab.2 a (Subgroup.mem_sup_left ha)
  have hsq : a * a = 1 := mul_eq_one_iff_eq_inv.mpr h3.symm
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact hsq
  have ha1 : a = 1 := by
    calc a = a ^ 5 * (a ^ 2)⁻¹ * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha5, ha2]; simp
  rw [ha1, one_mul]
  exact hb

theorem Cfg3.t_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : cjL t Y = Y := by
  have htCZ : t ∈ CZ t X₁ := by
    rw [CZ, Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hztu : (z * u) * t = t * (z * u) := by
    calc (z * u) * t = z * (u * t) := by group
      _ = z * (t * u) := by rw [c.hs.ut]
      _ = (z * t) * u := by group
      _ = (t * z) * u := by rw [c.hs.zt_comm]
      _ = t * (z * u) := by group
  have hle : cjL t Y ≤ Y := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj t).toMonoidHom y = t * y * t⁻¹ := by simp [MulAut.conj_apply]
    rw [hy']
    have h1 : t * y * t⁻¹ ∈ XX t X₁ ⊔ Y := by
      have := TwoThin.pPrimeCoreOf_normalized (CZ t X₁) htCZ (o := y)
        (by rw [c.b83.W_eq]; exact Subgroup.mem_sup_right hy)
      rwa [c.b83.W_eq] at this
    apply c.C_XY_zu _ h1
    have hy2 := Subgroup.mem_centralizer_singleton_iff.mp (c.b83.Y_syl.1 hy)
    have hc : (z * u) * t = t * (z * u) := hztu
    have hyy : (z * u) * y * (z * u)⁻¹ = y := by
      calc (z * u) * y * (z * u)⁻¹ = (y * (z * u)) * (z * u)⁻¹ := by rw [hy2]
        _ = y := by group
    calc (z * u) * (t * y * t⁻¹) * (z * u)⁻¹
        = ((z * u) * t) * y * ((z * u) * t)⁻¹ := by group
      _ = (t * (z * u)) * y * (t * (z * u))⁻¹ := by rw [hc]
      _ = t * ((z * u) * y * (z * u)⁻¹) * t⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [hyy]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cjL])


theorem Cfg4.t_X3 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL t (X3 v X₁) = X4 v t X₁ := by
  have hv2 := c.v_sq'
  set t' : G := v⁻¹ * t * v with ht'
  have ht_eq : t = v * t' * v⁻¹ := by rw [ht']; group
  have hvz : v * z * v⁻¹ = z * u := c.b84.v_z
  have hz' : t' * z * t'⁻¹ = z := by
    have hzv : v⁻¹ * (z * u) * v = z := by
      calc v⁻¹ * (z * u) * v = v⁻¹ * (v * z * v⁻¹) * v := by rw [hvz]
        _ = z := by group
    have hztu : t * (z * u) * t⁻¹ = z * u := by
      have h1 : t * z * t⁻¹ = z := by
        have := c.hs.zt_comm
        calc t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [← this]
          _ = z := by group
      have h2 : t * u * t⁻¹ = u := by
        have := c.hs.ut
        calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [← this]
          _ = u := by group
      calc t * (z * u) * t⁻¹ = (t * z * t⁻¹) * (t * u * t⁻¹) := by group
        _ = z * u := by rw [h1, h2]
    calc t' * z * t'⁻¹ = v⁻¹ * (t * (v * z * v⁻¹) * t⁻¹) * v := by rw [ht']; group
      _ = v⁻¹ * (t * (z * u) * t⁻¹) * v := by rw [hvz]
      _ = v⁻¹ * (z * u) * v := by rw [hztu]
      _ = z := hzv
  have hXX : cjL t' (XX t X₁) = XX t X₁ := by
    have e1 : cjL t' (XX t X₁) = cjL v⁻¹ (cjL t (cjL v (XX t X₁))) := by
      rw [ht', ← cjL_cjL, ← cjL_cjL]
    have e2 : cjL v⁻¹ Y = XX t X₁ := by
      rw [← c.b84.v_X, cjL_cjL, inv_mul_cancel, cjL_one]
    rw [e1, c.b84.v_X, c.t_Y, e2]
  have hmem : t' ∈ normalizer ((XX t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨mem_normalizer_of_cjL_eq hXX, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc t' * z = (t' * z * t'⁻¹) * t' := by group
        _ = z * t' := by rw [hz'])⟩
  rw [c.b82.NC_X] at hmem
  have hH_XX : ∀ l ∈ H, ∀ e ∈ XX t X₁, l * e * l⁻¹ ∈ XX t X₁ := fun l hl e he =>
    c.hinv_XX.mem hl he
  have hnormt : ∀ l ∈ zpowers t, ∀ e ∈ XX t X₁ ⊔ H, l * e * l⁻¹ ∈ XX t X₁ ⊔ H := by
    intro l hl e he
    have hcj : cjL t (XX t X₁ ⊔ H) = XX t X₁ ⊔ H := by rw [cjL_sup, c.t_XX, c.b66.t_normH]
    rcases mem_zpowers_of_sq_eq_one c.t_sq hl with hl1 | hl1
    · rw [hl1]; simpa using he
    · rw [hl1]
      have := mem_cjL_self (g := t) he
      rwa [hcj] at this
  obtain ⟨m, hm, k, hk, hmk⟩ := mem_sup_of_normalizes hnormt hmem
  obtain ⟨x, hx, h, hh, rfl⟩ := mem_sup_of_normalizes hH_XX hm
  have hxh : ∀ A : Subgroup G, HInv H A → (∀ a ∈ A, x * a = a * x) → cjL (x * h) A = A := by
    intro A hA hxA
    rw [← cjL_cjL, hA h hh, cjL_eq_of_comm hxA]
  have hx1 : ∀ a ∈ X₁, x * a = a * x := fun a ha =>
    c.b83.XY_ab.1 x (Subgroup.mem_sup_left hx) a (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
  have hx2 : ∀ a ∈ XB t X₁, x * a = a * x := fun a ha =>
    c.b83.XY_ab.1 x (Subgroup.mem_sup_left hx) a
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha))
  have hx3 : ∀ a ∈ X3 v X₁, x * a = a * x := fun a ha => c.XX_comm x hx a (c.X3_le_Y ha)
  have hcjv : cjL v (cjL v X₁) = X₁ := by rw [cjL_cjL]; exact c.hinv_X1 _ hv2
  have hcjv' : cjL v (X3 v X₁) = X₁ := hcjv
  have hv1 : cjL v⁻¹ X₁ = X3 v X₁ := cjL_vinv_of_HInv hv2 c.hinv_X1
  have hcjt : ∀ A : Subgroup G, cjL t A = cjL v (cjL t' (cjL v⁻¹ A)) := by
    intro A
    rw [cjL_cjL, cjL_cjL, ← ht_eq]
  rcases mem_zpowers_of_sq_eq_one c.t_sq hk with hk1 | hk1
  ·
    exfalso
    rw [hk1, mul_one] at hmk
    have h1 : cjL t X₁ = X₁ := by
      rw [hcjt, hv1, hmk, hxh _ c.hinv_X3 hx3]
      exact hcjv'
    have h2 : cjL t X₁ = XB t X₁ := rfl
    have hne : X₁ ≠ XB t X₁ := by
      intro heq
      have : X₁ ⊓ XB t X₁ = X₁ := by rw [← heq, inf_idem]
      rw [c.X1_inf_X2] at this
      have h5 := c.card_X1
      rw [← this, Subgroup.card_bot] at h5
      omega
    exact hne (h1.symm.trans h2)
  ·
    rw [hk1] at hmk
    have hv3 : cjL v⁻¹ (X3 v X₁) = X₁ := by
      rw [X3, cjL_cjL, inv_mul_cancel, cjL_one]
    have h1 : cjL t' X₁ = XB t X₁ := by
      rw [hmk, ← cjL_cjL]
      have : cjL t X₁ = XB t X₁ := rfl
      rw [this]
      exact hxh _ c.hinv_X2 hx2
    rw [hcjt, hv3, h1]


theorem commute_sup_left {A B C : Subgroup G} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : ∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c = c * x := by
  intro x hx c hc
  have h : A ⊔ B ≤ Subgroup.centralizer (C : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun c' hc' => (hAC a ha c' hc').symm)
      (fun b hb => Subgroup.mem_centralizer_iff.mpr fun c' hc' => (hBC b hb c' hc').symm)
  exact (Subgroup.mem_centralizer_iff.mp (h hx) c hc).symm

theorem commute_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hAB).mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_of_commute hAB).mp hy
  have e1 : Commute a a' := hA a ha a' ha'
  have e2 : Commute b b' := hB b hb b' hb'
  have e3 : Commute a b' := hAB a ha b' hb'
  have e4 : Commute b a' := (hAB a' ha' b hb).symm
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [e4.eq]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1.eq, e2.eq]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e3.eq]
    _ = a' * b' * (a * b) := by group

theorem sup_pow_eq_one {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {n : ℕ}
    (hA : ∀ a ∈ A, a ^ n = 1) (hB : ∀ b ∈ B, b ^ n = 1) : ∀ x ∈ A ⊔ B, x ^ n = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hAB).mp hx
  rw [(Commute.mul_pow (hAB a ha b hb) n), hA a ha, hB b hb, one_mul]


theorem pow_five_of_card {X : Subgroup G} (hX : Nat.card ↥X = 5) {x : G} (hx : x ∈ X) : x ^ 5 = 1 := by
  have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
  rw [hX] at this
  simpa using congrArg Subtype.val this

theorem cjL_eq_of_mem_normalizer {g : G} {A : Subgroup G} (hg : g ∈ normalizer (A : Set G)) :
    cjL g A = A := by
  ext x
  rw [mem_cjL]
  have h1 := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)
  have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [this] at h1
  exact h1

theorem Cfg.K1_le_normalizer_RR (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    K₁ ≤ normalizer ((RR t X₁ : Subgroup G) : Set G) := by
  have h1 : K₁ ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) := by
    rw [c.b85.N_X2]
    exact (le_sup_right : K₁ ≤ RR t X₁ ⊔ K₁).trans le_sup_left
  exact h1.trans (normalizer_le_normalizer_RR t X₁)

theorem Cfg.K1_inf_RR (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) : K₁ ⊓ RR t X₁ = ⊥ := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (ZMod 5) = p ^ f := by rw [c.ctx.pf, Nat.card_zmod]
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc.sl₁ (ZMod 5) hcard
  have hN₀K : K₁ ⊓ RR t X₁ ≤ K₁ := inf_le_left
  have hnorm : K₁ ≤ normalizer ((K₁ ⊓ RR t X₁ : Subgroup G) : Set G) := by
    intro k hk
    apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
    intro n hn
    refine ⟨K₁.mul_mem (K₁.mul_mem hk hn.1) (K₁.inv_mem hk), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (c.K1_le_normalizer_RR hk) n).mp hn.2
    exact this
  have : ((K₁ ⊓ RR t X₁).subgroupOf K₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀K).mpr hnorm
  have hcardeq : Nat.card ↥((K₁ ⊓ RR t X₁).subgroupOf K₁) = Nat.card ↥(K₁ ⊓ RR t X₁ : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀K).toEquiv
  have hdvd : Nat.card ↥(K₁ ⊓ RR t X₁ : Subgroup G) ∣ 5 ^ 5 := by
    rw [← c.b85.R_card]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases sl2_five_normal_cases e ((K₁ ⊓ RR t X₁).subgroupOf K₁) with h | h | h
  · rw [h, Subgroup.card_bot] at hcardeq
    exact Subgroup.eq_bot_of_card_eq _ hcardeq.symm
  · exfalso
    have hc2 : Nat.card ↥(Subgroup.center ↥K₁) = 2 := sl2_five_center_card e
    rw [h, hc2] at hcardeq
    rw [← hcardeq] at hdvd
    have : (2 : ℕ) ∣ 5 ^ 5 := hdvd
    omega
  · exfalso
    have hc120 : Nat.card ↥K₁ = 120 := sl2_five_card e
    rw [h, Subgroup.card_top, hc120] at hcardeq
    rw [← hcardeq] at hdvd
    have : (120 : ℕ) ∣ 5 ^ 5 := hdvd
    omega

end Cfg2
end CFSG.GH74.GLS.LU.Local.Five
