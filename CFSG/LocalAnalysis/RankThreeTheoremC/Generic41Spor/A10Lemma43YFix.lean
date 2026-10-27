module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F A : Subgroup Y}

theorem a10y_F_normalizes (c : A10YCaseC Y P x t₁ t₂ J₁ J₂ F A A) {f : Y} (hf : f ∈ F) :
    f ∈ Subgroup.normalizer (A : Set Y) := by
  have h := c.data
  have hfC : f ∈ Subgroup.centralizer ({x} : Set Y) := h.F_le hf
  have h1 : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) (GLBConj f J₁) := by
    have h0 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj h.comp₁ f
    rwa [CFSG.LocalAnalysis.GLTheoremB.gLBConj_eq_of_mem_normalizer
      (Subgroup.le_normalizer hfC)] at h0
  have h2 : GLBConj f J₁ ≤ GLAPLayer 5 (Subgroup.centralizer ({x} : Set Y)) := le_sSup h1
  rw [h.layer] at h2
  have h3 : GLBConj f J₁ ≤ A := h2.trans (sup_le c.le₁ c.le₂)
  have h4 : GLBConj f J₁ ≤ GLBConj f A :=
    CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono f c.le₁
  have hA' : IsComponentOf (GLBConj f A) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremB.isComponentOf_gLBConj c.comp₁ f
  have hperf : ⁅GLBConj f J₁, GLBConj f J₁⁆ = GLBConj f J₁ := by
    have h5 := Subgroup.map_commutator (H₁ := J₁) (H₂ := J₁) (MulAut.conj f⁻¹).toMonoidHom
    change GLBConj f ⁅J₁, J₁⁆ = ⁅GLBConj f J₁, GLBConj f J₁⁆ at h5
    rw [← h5, CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect h.comp₁]
  have hne : GLBConj f J₁ ≠ ⊥ := by
    intro hbot
    have ht : f⁻¹ * t₁ * f ∈ GLBConj f J₁ := by
      rw [CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj]
      simpa [mul_assoc] using (Subgroup.mem_inf.1 h.t₁_mem).2
    rw [hbot, Subgroup.mem_bot] at ht
    have ht1 : t₁ = 1 := by
      have h6 := congrArg (fun z => f * z * f⁻¹) ht
      simpa [mul_assoc] using h6
    have h7 : orderOf t₁ = 1 := by rw [ht1]; exact orderOf_one
    rw [h.t₁_ord] at h7
    omega
  have heq : A = GLBConj f A :=
    a10y_comp_eq_of_perfect_le c.comp₁ hA' hperf hne h3 h4
  exact CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_iff_gLBConj_eq.2 heq.symm

omit [Finite Y] in
theorem a10y_fix_mem_sup {S R : Subgroup Y} (hc : ∀ a ∈ S, ∀ b ∈ R, a * b = b * a) {w : Y}
    (hw : w ∈ S ⊔ R) : ∃ a ∈ S, ∃ b ∈ R, a * b = w := by
  rw [Subgroup.sup_eq_closure] at hw
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hw
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, R.one_mem, mul_one y⟩
    · exact ⟨1, S.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, S.one_mem, 1, R.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, S.mul_mem hy₁ hy₂, z₁ * z₂, R.mul_mem hz₁ hz₂, ?_⟩
    have e := hc y₂ hy₂ z₁ hz₁
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [e]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, R.inv_mem hz, ?_⟩
    rw [hc y hy z hz, mul_inv_rev]

theorem a10y_fix_W (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {Z : Subgroup Y}
    (hFZ : ∀ f ∈ F, ∀ z ∈ Z, f * z * f⁻¹ ∈ Z)
    (hTZ : (zpowers t₁ ⊔ zpowers t₂) ⊓ Z = ⊥) (hxZ : x ∉ Z) {w : Y}
    (hwV : w ∈ zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x) (hwZ : w ∈ Z) : w = 1 := by
  haveI : IsMulCommutative P := h.P_comm
  have hVP := (a10y_V h).2.2.1
  have hcomm : ∀ a ∈ zpowers t₁ ⊔ zpowers t₂, ∀ b ∈ zpowers x, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm (s := P) (hVP (Subgroup.mem_sup_left ha)) (hVP (Subgroup.mem_sup_right hb))
  obtain ⟨t, ht, y, hy, rfl⟩ := a10y_fix_mem_sup hcomm hwV
  have hfix : ∀ f ∈ F, f * t * f⁻¹ = t := by
    intro f hf
    have hfx : Commute f x := Subgroup.mem_centralizer_singleton_iff.1 (h.F_le hf)
    have hfy : f * y * f⁻¹ = y := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (hfx.zpow_right j).mul_inv_cancel
    have h1 : f * (t * y) * f⁻¹ * (t * y)⁻¹ ∈ Z := Z.mul_mem (hFZ f hf _ hwZ) (Z.inv_mem hwZ)
    have h2 : f * (t * y) * f⁻¹ * (t * y)⁻¹ = (f * t * f⁻¹) * t⁻¹ := by
      calc f * (t * y) * f⁻¹ * (t * y)⁻¹ = (f * t * f⁻¹) * (f * y * f⁻¹) * y⁻¹ * t⁻¹ := by group
        _ = (f * t * f⁻¹) * t⁻¹ := by rw [hfy]; group
    have h3 : (f * t * f⁻¹) * t⁻¹ ∈ (zpowers t₁ ⊔ zpowers t₂) ⊓ Z :=
      ⟨(zpowers t₁ ⊔ zpowers t₂).mul_mem (h.F_norm f hf t ht)
        ((zpowers t₁ ⊔ zpowers t₂).inv_mem ht), h2 ▸ h1⟩
    rw [hTZ, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  have ht1 : t = 1 := h.F_fix t ht hfix
  rw [ht1, one_mul] at hwZ ⊢
  by_contra hne
  apply hxZ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hnd : ¬ ((5 : ℕ) : ℤ) ∣ j := by
    rw [← h.x_ord, orderOf_dvd_iff_zpow_eq_one]
    exact hne
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 Nat.prime_five).coprime_iff_not_dvd).2 hnd
  have hx5 : x ^ (5 : ℕ) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.x_ord] at this
  have hxe : x = (x ^ j) ^ b := by
    calc x = x ^ (a * ((5 : ℕ) : ℤ) + b * j) := by rw [hab, zpow_one]
      _ = (x ^ ((5 : ℕ) : ℤ)) ^ a * (x ^ j) ^ b := by rw [zpow_add, zpow_mul', zpow_mul']
      _ = (x ^ j) ^ b := by rw [zpow_natCast, hx5, one_zpow, one_mul]
  rw [hxe]
  exact Z.zpow_mem hwZ b

theorem a10y_CPA (c : A10YCaseC Y P x t₁ t₂ J₁ J₂ F A A) :
    P ⊓ Subgroup.centralizer (A : Set Y) = ⊥ := by
  have h := c.data
  have hFZ : ∀ f ∈ F, ∀ z ∈ Subgroup.centralizer (A : Set Y),
      f * z * f⁻¹ ∈ Subgroup.centralizer (A : Set Y) := by
    intro f hf z hz
    have hfn := a10y_F_normalizes c hf
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro a ha
    have ha' : f⁻¹ * a * f ∈ (A : Set Y) := (Subgroup.mem_set_normalizer_iff''.1 hfn a).1 ha
    have e := hz _ ha'
    calc a * (f * z * f⁻¹) = f * ((f⁻¹ * a * f) * z) * f⁻¹ := by group
      _ = f * (z * (f⁻¹ * a * f)) * f⁻¹ := by rw [e]
      _ = (f * z * f⁻¹) * a := by group
  have hxZ : x ∉ Subgroup.centralizer (A : Set Y) := by
    intro hx
    refine a10y_not_le_centralizer h h.comp₁ h.t₁_mem.2 h.t₁_ord c.comp₁ c.le₁ c.not₁ fun a ha => ?_
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx a ha)
  have hTZ : (zpowers t₁ ⊔ zpowers t₂) ⊓ Subgroup.centralizer (A : Set Y) = ⊥ := by
    rcases h.F_irr ((zpowers t₁ ⊔ zpowers t₂) ⊓ Subgroup.centralizer (A : Set Y)) inf_le_left
      (fun f hf a ha => ⟨h.F_norm f hf a ha.1, hFZ f hf a ha.2⟩) with hb | hT
    · exact hb
    · exfalso
      have ht₁ : t₁ ∈ (zpowers t₁ ⊔ zpowers t₂) ⊓ Subgroup.centralizer (A : Set Y) := by
        rw [hT]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)
      have ht₁A : t₁ ∈ A := c.le₁ h.t₁_mem.2
      have hcen := (a10y_comp_simple h c.comp₁).1
      have hmem : (⟨t₁, ht₁A⟩ : ↥A) ∈ center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 ht₁.2 (b : Y) b.2)
      rw [hcen, Subgroup.mem_bot] at hmem
      have h1 : t₁ = 1 := congrArg Subtype.val hmem
      have h2 := h.t₁_ord
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  rw [Subgroup.eq_bot_iff_forall]
  rintro c₀ ⟨hc₀P, hc₀Z⟩
  by_contra hc₀1
  obtain ⟨k, hk⟩ := a10y_sylow_pow h hc₀P
  obtain ⟨m, -, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hk)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hc₀1 (orderOf_eq_one_iff.1 (by rw [hmo, pow_zero]))
  have h5dvd : 5 ∣ orderOf c₀ := by rw [hmo]; exact dvd_pow_self 5 hm0
  have hne0 : orderOf c₀ ≠ 0 := by rw [hmo]; exact pow_ne_zero m (by norm_num)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : Y, c₁ = c₀ ^ (orderOf c₀ / 5) := ⟨_, rfl⟩
  have hord : orderOf c₁ = 5 := by rw [hc₁]; exact orderOf_pow_orderOf_div hne0 h5dvd
  have hc₁P : c₁ ∈ P := by rw [hc₁]; exact P.pow_mem hc₀P _
  have hc₁Z : c₁ ∈ Subgroup.centralizer (A : Set Y) := by
    rw [hc₁]; exact Subgroup.pow_mem _ hc₀Z _
  have hc₁5 : c₁ ^ 5 = 1 := by
    have := pow_orderOf_eq_one c₁
    rwa [hord] at this
  have hc₁V := (a10y_V h).2.2.2 c₁ hc₁P hc₁5
  have h1 := a10y_fix_W h hFZ hTZ hxZ hc₁V hc₁Z
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem a10y_P_le (hInn : KFactInnerAction) (c : A10YCaseC Y P x t₁ t₂ J₁ J₂ F A A) : P ≤ A := by
  intro q hq
  have h := c.data
  have hPA : P ⊓ A ≠ ⊥ := by
    intro hbot
    have ht : t₁ ∈ P ⊓ A := ⟨h.t₁_mem.1, c.le₁ h.t₁_mem.2⟩
    rw [hbot, Subgroup.mem_bot] at ht
    have h2 := h.t₁_ord
    rw [ht, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨g, hg, hgq⟩ := a10y_inner_action hInn h c.comp₁ hPA hq
  have hmemZ : g⁻¹ * q ∈ Subgroup.centralizer (A : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have e := hgq a ha
    calc a * (g⁻¹ * q) = (g⁻¹ * (g * a * g⁻¹)) * q := by group
      _ = (g⁻¹ * (q * a * q⁻¹)) * q := by rw [e]
      _ = (g⁻¹ * q) * a := by group
  have hmem : g⁻¹ * q ∈ P ⊓ Subgroup.centralizer (A : Set Y) :=
    ⟨P.mul_mem (P.inv_mem hg.1) hq, hmemZ⟩
  rw [a10y_CPA c, Subgroup.mem_bot] at hmem
  rw [← inv_mul_eq_one.1 hmem]
  exact hg.2

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
