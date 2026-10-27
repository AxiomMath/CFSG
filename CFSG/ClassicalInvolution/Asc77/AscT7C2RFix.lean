module

public import CFSG.ClassicalInvolution.Asc77.AscT7EC24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C2

variable {G : Type} [Group G]

theorem e_fixed {x₁ x₂ x₃ r t s : G} (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃)
    (c23 : Commute x₂ x₃) (o₂ : x₂ ^ 4 = 1) (o₃ : x₃ ^ 4 = 1)
    (r₁ : r * x₁ * r⁻¹ = x₁⁻¹) (r₂ : r * x₂ * r⁻¹ = x₂) (r₃ : r * x₃ * r⁻¹ = x₃ * x₁)
    (t₁ : t * x₁ * t⁻¹ = x₁) (t₂ : t * x₂ * t⁻¹ = x₂⁻¹) (t₃ : t * x₃ * t⁻¹ = x₃ * x₂)
    (s₁ : s * x₁ * s⁻¹ = x₁ * x₃) (s₂ : s * x₂ * s⁻¹ = x₂ * x₃) (s₃ : s * x₃ * s⁻¹ = x₃⁻¹) :
    r * (x₁ * x₂⁻¹ * x₃ ^ 2) * r⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 ∧
      t * (x₁ * x₂⁻¹ * x₃ ^ 2) * t⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 ∧
      s * (x₁ * x₂⁻¹ * x₃ ^ 2) * s⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := by
  have enf : x₁ * x₂⁻¹ * x₃ ^ 2 = x₁ ^ (1 : ℤ) * x₂ ^ (-1 : ℤ) * x₃ ^ (2 : ℤ) := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [enf, A3Mod.conj_nf_r c12 c13 r₁ r₂ r₃]
    norm_num
  · rw [enf, A3Mod.conj_nf_t c23 t₁ t₂ t₃]
    norm_num
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact o₂)
  · rw [enf, A3Mod.conj_nf_s c13 c23 s₁ s₂ s₃]
    norm_num
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact o₃)


section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem fixed_of_frame (c : Thompson.Ctx p f Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {ε : G} (hε : ε ∈ W)
    (h₁ : F.ρ.r * ε * F.ρ.r⁻¹ = ε) (h₂ : F.ρ'.r * ε * F.ρ'.r⁻¹ = ε)
    (h₃ : F.ρ₃.r * ε * F.ρ₃.r⁻¹ = ε) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) :
    r * ε * r⁻¹ = ε := by
  have ha := T7D.imgQ_mem F.ρ
  have ha' := T7D.imgQ_mem F.ρ'
  have ha₃ := T7D.imgQ_mem F.ρ₃
  have hmem : ∀ σ : Thompson.Rep Ω W, σ.r * ε * σ.r⁻¹ = ε →
      T7D.imgQ σ ∈ Thompson.muStab Ω W ε := fun σ h =>
    (c.mem_muStab_iff hε σ.hR σ.hr (q := T7D.imgQ σ) rfl).mpr h
  have hΔ : ∀ x ∈ Thompson.muDelta Ω W, x ∈ Thompson.muStab Ω W ε := fun x hx => by
    have hx' := S4.mem_closure_frame he ha ha' ha₃ hab hcomm hac hx
    refine (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr ?_ hx'
    rintro y (rfl | rfl | rfl)
    · exact hmem F.ρ h₁
    · exact hmem F.ρ' h₂
    · exact hmem F.ρ₃ h₃
  by_cases hrW : r ∈ W
  · have hWab := Thompson.commutes_of_mem_WSet c.hp c.hq c.hΩ c.hW
    rw [mul_inv_eq_iff_eq_mul]
    exact hWab r hrW ε hε
  · have hrq : Thompson.piG W r ∈ muGroup Ω W :=
      Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (Thompson.le_MGrp_of_mem_D hR hr))
    have hx : (⟨Thompson.piG W r, hrq⟩ : ↥(muGroup Ω W)) ∈ Thompson.muDelta Ω W :=
      ⟨R, hR, r, hr, hrW, rfl⟩
    exact (c.mem_muStab_iff hε hR hr (q := ⟨Thompson.piG W r, hrq⟩) rfl).mp (hΔ _ hx)

omit [Finite G] in
theorem mem_centerIn_of_forall {a : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (h : ∀ n ∈ Subgroup.normalizer (W : Set G), n * a * n⁻¹ = a) :
    a ∈ centerIn (Subgroup.normalizer (W : Set G)) := by
  refine ⟨⟨a, ha⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have h1 := h g g.2
  show (g : G) * a = a * (g : G)
  calc (g : G) * a = ((g : G) * a * (g : G)⁻¹) * g := by group
    _ = a * g := by rw [h1]

theorem exists_two_gen_W [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    ∃ a b : G, a ∈ W ∧ b ∈ W ∧ Subgroup.closure ({a, b} : Set G) = W := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, -, -, hFR, -, -, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have hm1 : m = 1 := by
    have h1 := Thompson.D_card hp hq hΩ hW F.ρ.hR
    have h2 : Nat.card ↥(F.ρ.R ⊓ W) = 4 * m := by rw [← h₁, Nat.card_zpowers, o₁]
    rw [h2, hFR, h8] at h1
    omega
  subst hm1
  have c12 : Commute x₁ x₂ := hWab x₁ m₁ x₂ m₂
  have c13 : Commute x₁ x₃ := hWab x₁ m₁ x₃ m₃
  have c23 : Commute x₂ x₃ := hWab x₂ m₂ x₃ m₃
  have o₂' : x₂ ^ 4 = 1 := by simpa [o₂] using pow_orderOf_eq_one x₂
  have o₃' : x₃ ^ 4 = 1 := by simpa [o₃] using pow_orderOf_eq_one x₃
  obtain ⟨hfr, hft, hfs⟩ := e_fixed c12 c13 c23 o₂' o₃' r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃
  have hεW : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W := W.mul_mem (W.mul_mem m₁ (W.inv_mem m₂)) (W.pow_mem m₃ 2)
  have hfix : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (x₁ * x₂⁻¹ * x₃ ^ 2) * r⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := fun R₀ hR₀ r hr =>
    fixed_of_frame c he F hab hcomm hac hεW hfr hft hfs hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hfW : n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr hεW
    have hfixc : ∀ σ : Thompson.Rep Ω W,
        σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by
      intro σ
      have hmemD : n⁻¹ * σ.r * n ∈ conjSub n⁻¹ σ.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ.r * n) * n⁻¹ = σ.r := by group
        rw [h1]
        exact σ.hr
      have := hfix _ (Thompson.conjSub_mem_D hΩ σ.hR hn') _ hmemD
      calc σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹
          = n * ((n⁻¹ * σ.r * n) * (x₁ * x₂⁻¹ * x₃ ^ 2) * (n⁻¹ * σ.r * n)⁻¹) * n⁻¹ := by group
        _ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by rw [this]
    rcases A3Mod.fixed_eq_one_or c12 c13 c23 o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂
        s₃ (hgen hfW) (hfixc F.ρ) (hfixc F.ρ') (hfixc F.ρ₃) with h | h
    · have h0 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := conj_eq_one_iff.mp h
      rw [h0]
      group
    · rw [h, pow_one]
  have hmemC : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ centerIn (Subgroup.normalizer (W : Set G)) :=
    mem_centerIn_of_forall (Subgroup.le_normalizer hεW) hcent
  have hmem : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) :=
    ⟨hεW, hmemC⟩
  rw [hd.hZ] at hmem
  have hε1 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := Subgroup.mem_bot.mp hmem
  have hx₂ : x₂ = x₃ ^ 2 * x₁ := by
    calc x₂ = x₃ ^ 2 * (x₁ * x₂⁻¹ * x₃ ^ 2)⁻¹ * x₁ := by group
      _ = x₃ ^ 2 * x₁ := by rw [hε1, inv_one, mul_one]
  refine ⟨x₁, x₃, m₁, m₃, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact m₁
    · exact m₃
  · refine hgen.trans ?_
    rw [Subgroup.closure_le]
    have hx₁ : x₁ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    have hx₃ : x₃ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    rintro y (rfl | rfl | rfl)
    · exact hx₁
    · rw [hx₂]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx₃ 2) hx₁
    · exact hx₃

end Frame

end T7C2

end CFSG.ClassicalInvolution.Asc77
