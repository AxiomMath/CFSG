module

public import CFSG.GH74.GLS.LU.Local.FiveL86a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L86b

theorem X5_eq {G : Type} [Group G] (v w₁ : G) (X₁ : Subgroup G) :
    X5 v w₁ X₁ = cjL (w₁ * v) X₁ := by
  show cjL w₁ (cjL v X₁) = _
  rw [cjL_cjL]

theorem X6_eq {G : Type} [Group G] (v t w₁ : G) (X₁ : Subgroup G) :
    X6 v t w₁ X₁ = cjL (w₁ * v) (XB t X₁) := by
  show cjL w₁ (cjL v (XB t X₁)) = _
  rw [cjL_cjL]

theorem zpowers_comm' {G : Type} [Group G] {y₀ y₂ : G} (h : y₀ * y₂ = y₂ * y₀) :
    ∀ a ∈ zpowers y₀, ∀ b ∈ zpowers y₂, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow (show Commute y₀ y₂ from h) i j).eq

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.t_notin_H (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : t ∉ H := by
  intro ht
  have h1 : cjL t K₁ = K₁ := (c.b66.H_normK t ht).1
  have h2 : cjL t K₁ = K₂ := c.hs.t_swap
  exact c.hc.ne (h1.symm.trans h2)

theorem Cfg2.K1_inf_K2_sq (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ K₁ ⊓ K₂, x * x = 1 := by
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (c.hc.comm g g.2 x hx.2)
  have hz : x ∈ zpowers z := by
    rw [← c.hc.cen₁]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rcases mem_zpowers_of_sq_eq_one c.z_sq hz with h | h
  · rw [h]; simp
  · rw [h]; exact c.z_sq

theorem Cfg2.five_inf_K2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {A : Subgroup G} (hA : A ≤ K₁)
    (hcard : Nat.card ↥A = 5) : A ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx5 : x ^ 5 = 1 := pow_five_of_card hcard hx.1
  have hxx : x * x = 1 := c.K1_inf_K2_sq x ⟨hA hx.1, hx.2⟩
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hxx
  have : x = 1 := by
    calc x = x ^ 5 * (x ^ 2)⁻¹ * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx5, hx2]; simp
  rw [this]; exact Subgroup.one_mem _

theorem Cfg2.t_NN (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : t ∈ NN z u :=
  mem_NN_of_comm c.hs.zt_comm.symm c.hs.ut.symm

theorem Cfg2.w₂_mem (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : t * w₁ * t⁻¹ ∈ K₂ := by
  have h1 : t * w₁ * t⁻¹ ∈ cjL t K₁ := mem_cjL_self c.b66.w₁_mem
  have h2 : cjL t K₁ = K₂ := c.hs.t_swap
  rw [h2] at h1
  exact h1

theorem Cfg2.w₂_NN (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : t * w₁ * t⁻¹ ∈ NN z u :=
  mul_mem (mul_mem c.t_NN c.w₁_NN) (inv_mem c.t_NN)

theorem Cfg2.w₁_w₂_comm (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    w₁ * (t * w₁ * t⁻¹) = (t * w₁ * t⁻¹) * w₁ := c.hc.comm w₁ c.b66.w₁_mem _ c.w₂_mem

theorem Cfg2.W_le_NN (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹) ≤ NN z u :=
  sup_le (Subgroup.zpowers_le.mpr c.w₁_NN) (Subgroup.zpowers_le.mpr c.w₂_NN)

theorem Cfg2.W_le_normalizer_K2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹) ≤ normalizer (K₂ : Set G) := by
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · apply mem_normalizer_of_cjL_eq
    apply cjL_eq_of_comm
    intro a ha
    exact c.hc.comm w₁ c.b66.w₁_mem a ha
  · exact Subgroup.le_normalizer c.w₂_mem

theorem Cfg2.invSyl_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {D : Subgroup G} (hD : D ≤ K₁)
    (hcard : Nat.card ↥D = 5) (hH : HInv H D) : D = X₁ ∨ D = cjL w₁ X₁ := by
  set w₂ : G := t * w₁ * t⁻¹ with hw₂
  have hcomm : ∀ a ∈ D, ∀ b ∈ XB t X₁, a * b = b * a := fun a ha b hb =>
    c.hc.comm a (hD ha) b (c.X2_le_K2 hb)
  have hdisj : D ⊓ XB t X₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h0 := c.five_inf_K2 hD hcard
    have hx' : x ∈ D ⊓ K₂ := ⟨hx.1, c.X2_le_K2 hx.2⟩
    rw [h0] at hx'; exact hx'
  have hR_card : Nat.card ↥(D ⊔ XB t X₁ : Subgroup G) = 25 := by
    rw [card_sup_of_commute_disjoint hcomm hdisj, hcard, c.card_X2]
  have hRC : D ⊔ XB t X₁ ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₁ (hD ha)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact c.hc.cz₂ (c.X2_le_K2 ha)
  have hSyl : IsSylowIn 5 (D ⊔ XB t X₁) (centralizer ({z} : Set G)) := by
    refine ⟨hRC, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [hR_card]; norm_num)
    · have h1 := Subgroup.index_mul_card ((D ⊔ XB t X₁).subgroupOf (centralizer ({z} : Set G)))
      have h2 : Nat.card ↥((D ⊔ XB t X₁).subgroupOf (centralizer ({z} : Set G))) = 25 := by
        rw [← hR_card]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
      rw [h2, c.b82.card_C] at h1
      intro h5
      omega
  have hRH : HInv H (D ⊔ XB t X₁) := hH.sup c.hinv_X2
  obtain ⟨w, hw, hR⟩ := c.b82.syl_inv _ hSyl hRH
  have hwN : w ∈ NN z u := c.W_le_NN hw
  have hle : cjL w⁻¹ D ≤ XX t X₁ := by
    have h1 : D ≤ cjL w (XX t X₁) := by rw [← hR]; exact le_sup_left
    have h2 := cjL_mono w⁻¹ h1
    rwa [cjL_cjL, inv_mul_cancel, cjL_one] at h2
  have hcard' : Nat.card ↥(cjL w⁻¹ D) = 5 := by rw [card_cjL]; exact hcard
  have hH' : HInv H (cjL w⁻¹ D) := hH.conj (c.cjL_H (inv_mem hwN))
  have hDw : D = cjL w (cjL w⁻¹ D) := by rw [cjL_cjL, mul_inv_cancel, cjL_one]
  rcases c.b82.X_inv_sub _ hle hcard' hH' with h | h
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute (A := zpowers w₁) (B := zpowers w₂)
      (zpowers_comm' c.w₁_w₂_comm)).mp hw
    have hbK : b ∈ K₂ := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact zpow_mem c.w₂_mem k
    have hb1 : cjL b X₁ = X₁ := by
      apply cjL_eq_of_comm
      intro x hx
      exact (c.hc.comm x (c.b82.X₁_syl.1 hx) b hbK).symm
    have hD' : D = cjL a X₁ := by
      rw [hDw, h, ← hab, ← cjL_cjL, hb1]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [hD']
    obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
    · left
      have : w₁ ^ k = z ^ n := by
        have h2 : w₁ ^ (2 : ℤ) = z := by rw [zpow_two]; simpa [pow_two] using c.b66.w₁_sq
        rw [hn, zpow_mul, h2]
      rw [this]
      apply cjL_eq_of_comm
      intro x hx
      exact (Commute.zpow_left (show Commute z x from (c.hc.cz₁ (c.b82.X₁_syl.1 hx)).symm) n).eq
    · right
      have : w₁ ^ k = z ^ n * w₁ := by
        have h2 : w₁ ^ (2 : ℤ) = z := by rw [zpow_two]; simpa [pow_two] using c.b66.w₁_sq
        rw [hn, zpow_add_one, zpow_mul, h2]
      rw [this, ← cjL_cjL]
      have hK1 : cjL w₁ X₁ ≤ K₁ := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        have := mul_mem (mul_mem c.b66.w₁_mem (c.b82.X₁_syl.1 hx)) (inv_mem c.b66.w₁_mem)
        simpa [MulAut.conj_apply] using this
      apply cjL_eq_of_comm
      intro x hx
      exact (Commute.zpow_left (show Commute z x from (c.hc.cz₁ (hK1 hx)).symm) n).eq
  ·
    exfalso
    have hK2 : cjL w (XB t X₁) ≤ K₂ := by
      have h1 : cjL w K₂ = K₂ := cjL_eq_of_mem_normalizer (c.W_le_normalizer_K2 hw)
      rw [← h1]
      exact cjL_mono w (c.X2_le_K2)
    have hDK2 : D ≤ K₂ := by rw [hDw, h]; exact hK2
    have h0 := c.five_inf_K2 hD hcard
    have : D = ⊥ := by
      rw [eq_bot_iff, ← h0]; exact le_inf le_rfl hDK2
    rw [this, Subgroup.card_bot] at hcard
    omega

theorem Cfg2.not_normal_X1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ¬ K₁ ≤ normalizer (X₁ : Set G) := by
  intro hK
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardq : Nat.card (ZMod 5) = p ^ f := by rw [c.ctx.pf, Nat.card_zmod]
  obtain ⟨e⟩ := exists_mulEquiv_SL2 c.hc.sl₁ (ZMod 5) hcardq
  have hle : X₁ ≤ K₁ := c.b82.X₁_syl.1
  have : (X₁.subgroupOf K₁).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hK
  have hcardeq : Nat.card ↥(X₁.subgroupOf K₁) = 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans c.card_X1
  rcases sl2_five_normal_cases e (X₁.subgroupOf K₁) with h | h | h
  · rw [h, Subgroup.card_bot] at hcardeq; omega
  · have := sl2_five_center_card e
    rw [h] at hcardeq
    omega
  · have := sl2_five_card e
    rw [h, Subgroup.card_top] at hcardeq
    omega

theorem Cfg2.w₁_not_normalizes_X1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    cjL w₁ X₁ ≠ X₁ := by
  intro h
  apply c.not_normal_X1
  rw [← c.b82.K₁_gen, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact Subgroup.le_normalizer hx
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact mem_normalizer_of_cjL_eq h

theorem Cfg4.cjL_braid (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) {A : Subgroup G} (hA : HInv H A) :
    cjL (v * w₁ * v) A = cjL (w₁ * v * w₁) A := by
  obtain ⟨h, hh, hbr⟩ := c.braid
  rw [hbr, ← cjL_cjL, hA h hh]

theorem Cfg4.X5_ne (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL v (X5 v w₁ X₁) ≠ X5 v w₁ X₁ := by
  intro h
  rw [X5_eq, cjL_cjL] at h
  have e : v * (w₁ * v) = v * w₁ * v := by group
  rw [e, c.cjL_braid c.hinv_X1] at h
  have e2 : w₁ * v * w₁ = (w₁ * v) * w₁ := rfl
  rw [e2, ← cjL_cjL, cjL_inj] at h
  exact c.w₁_not_normalizes_X1 h

end L86b

end CFSG.GH74.GLS.LU.Local.Five
