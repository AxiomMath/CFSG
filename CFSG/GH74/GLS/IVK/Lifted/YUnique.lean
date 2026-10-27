module

public import CFSG.GH74.GLS.IVK.Lifted.YGSide
public import CFSG.GH74.GLS.IVK.Lifted.YModel

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7

section Img2

theorem mem_sup_zpowers_iff_of_injective {H K : Type} [Group H] [Group K] (φ : H →* K)
    (hφ : Function.Injective φ) {P : Subgroup H} {P' : Subgroup K} (hP : ∀ x, x ∈ P ↔ φ x ∈ P')
    (hP' : P' ≤ φ.range) (τ ω : H) :
    ∀ x, x ∈ P ⊔ zpowers τ ⊔ zpowers ω ↔ φ x ∈ P' ⊔ zpowers (φ τ) ⊔ zpowers (φ ω) := by
  have hmap : P.map φ = P' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hP x).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := hP' hy
      exact ⟨x, (hP x).2 hy, rfl⟩
  intro x
  have h1 : (P ⊔ zpowers τ ⊔ zpowers ω).map φ = P' ⊔ zpowers (φ τ) ⊔ zpowers (φ ω) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hmap, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rw [← h1]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have := hφ hyx
    rw [← this]
    exact hy

end Img2

noncomputable def slEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    SpecialLinearGroup (Fin 2) R ≃* SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map f.toRingHom) (SpecialLinearGroup.map f.symm.toRingHom)
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem ivk_Y_unique_of_II4 (h44 : II4_44) (hII : II4_4_4_center) : IVK_Y_unique := by
  intro G _ _ z S K₁ K₂ t u q w hC hconcl Gs _ _ z' S' t' w' E₁ E₂ _hmodel hz'2 hZS' hdat hw
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := hC.m4 hII
  obtain ⟨F, hFf, hFfin, hFq, ⟨eG'⟩⟩ := hC.ch.hq₁
  have hFq' : Nat.card F = q := hFq
  have hodd : Odd (Nat.card F) := by
    rw [hFq']
    exact hC.ch.q_odd
  have h3 : 3 < Nat.card F := by
    rw [hFq']
    have := hC.ch.q_ge
    omega
  let eG : Hat K₁ ≃* SpecialLinearGroup (Fin 2) F :=
    eG'.trans (specialLinearGroupEquivStatedSL 2 F).symm
  obtain ⟨F', hF'f, hF'fin, hF'q, ⟨eM'⟩⟩ := hdat.sl2
  have hF'q' : Nat.card F' = q := hF'q
  let σ : F' ≃+* F := by
    letI : Fintype F' := Fintype.ofFinite F'
    letI : Fintype F := Fintype.ofFinite F
    exact FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF'q', hFq'])
  let eM : ↥E₁ ≃* SpecialLinearGroup (Fin 2) F :=
    eM'.trans ((specialLinearGroupEquivStatedSL 2 F').symm.trans (slEquivOfRingEquiv σ))
  have hdat' : Dat410 (Nat.card F) z' (S' : Subgroup Gs) t' w' E₁ E₂ := by
    rw [hFq']
    exact hdat
  obtain ⟨c', hc'τ, hc'ω, hc'B, hc'P⟩ := yconf_of_model hodd h3 hz'2 hZS' hdat' eM
  have hXC : K₁ ⊔ K₂ ⊔ S ≤ Cz z := sup_le (sup_le hM.K₁_le hM.K₂_le) hM.S_syl.1
  have hn : ((Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)).Normal := oz_subgroupOf_normal hXC
  obtain ⟨c, hcτ, hcω, hcX, hcP, hcS⟩ := yconf_of_G h44 hII hC hconcl hodd h3 eG
  have hwS : w ∈ S := hconcl.1
  have hwX : w ∈ K₁ ⊔ K₂ ⊔ S := Subgroup.mem_sup_right hwS
  have hww : w * w = 1 := by
    rcases hconcl.2.1 with h | h
    · rw [h]
      simp
    · exact mul_self_eq_one_of_orderOf_eq_two h
  have hcω1 : c.ω = 1 ↔ w = 1 := by
    have hmk := hcω ⟨w, hwX⟩ rfl
    rw [← hmk]
    constructor
    · intro h
      have hwO : w ∈ Oz z := (QuotientGroup.eq_one_iff (⟨w, hwX⟩ : ↥(K₁ ⊔ K₂ ⊔ S))).1 h
      exact eq_one_of_sq_eq_one_of_odd card_Oz_odd hwO hww
    · intro h
      have : (⟨w, hwX⟩ : ↥(K₁ ⊔ K₂ ⊔ S)) = 1 := Subtype.ext h
      rw [this]
      exact QuotientGroup.mk_one _
  have hωω : c.ω = 1 ↔ c'.ω = 1 := by
    rw [hc'ω, hcω1]
    exact hw.symm
  obtain ⟨ψ₀, hψτ, hψω, hψB, hψP⟩ := yconf_iso c c' hωω
  have hEz : IVK.Ez z' = E₁ ⊔ E₂ := hdat.Ez_eq
  have ht'S : t' ∈ (S' : Subgroup Gs) := hdat.t_mem
  have hw'S : w' ∈ (S' : Subgroup Gs) := hdat.w_mem
  have hXe : IVK.Ez z' ⊔ (S' : Subgroup Gs) = c'.X := by
    have hX' : c'.X = (E₁ ⊔ E₂) ⊔ zpowers t' ⊔ zpowers w' := by
      show c'.B ⊔ zpowers c'.τ ⊔ zpowers c'.ω = _
      rw [hc'B, hc'τ, hc'ω]
    rw [hX', hEz]
    apply le_antisymm
    · refine sup_le (le_sup_left.trans le_sup_left) ?_
      calc (S' : Subgroup Gs) = ((S' : Subgroup Gs) ⊓ IVK.Ez z') ⊔ zpowers t' ⊔ zpowers w' := hdat.prod
        _ ≤ (E₁ ⊔ E₂) ⊔ zpowers t' ⊔ zpowers w' :=
          sup_le_sup_right (sup_le_sup_right (inf_le_right.trans hEz.le) _) _
    · exact sup_le (sup_le le_sup_left ((zpowers_le.2 ht'S).trans le_sup_right))
        ((zpowers_le.2 hw'S).trans le_sup_right)
  have hS'eq : (S' : Subgroup Gs) = c'.P ⊔ zpowers t' ⊔ zpowers w' := by
    rw [hc'P, ← hEz]
    exact hdat.prod
  have hcXa : ∀ a : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S), a ∈ c.X := fun a =>
    hcX ▸ Subgroup.mem_top a
  let ψ₁ : (↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) ≃*
      ↥(IVK.Ez z' ⊔ (S' : Subgroup Gs)) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcX.symm)).trans
      (ψ₀.trans (MulEquiv.subgroupCongr hXe.symm))
  have hψ₁ : ∀ a, ((ψ₁ a : ↥(IVK.Ez z' ⊔ (S' : Subgroup Gs))) : Gs) =
      ((ψ₀ ⟨a, hcXa a⟩ : ↥c'.X) : Gs) := fun a => rfl
  let φ : (↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) →* Gs :=
    (IVK.Ez z' ⊔ (S' : Subgroup Gs)).subtype.comp ψ₁.toMonoidHom
  have hφ : ∀ a, φ a = ((ψ₀ ⟨a, hcXa a⟩ : ↥c'.X) : Gs) := fun a => rfl
  have hφinj : Function.Injective φ := fun a b h => ψ₁.injective (Subtype.ext h)
  have hPφ : ∀ a, a ∈ c.P ↔ φ a ∈ c'.P := fun a => by
    rw [hφ]
    exact hψP ⟨a, hcXa a⟩
  have hP'range : c'.P ≤ φ.range := by
    intro y hy
    have hyX : y ∈ IVK.Ez z' ⊔ (S' : Subgroup Gs) := hXe ▸ (c'.B_le_X (c'.P_le_B hy))
    exact ⟨ψ₁.symm ⟨y, hyX⟩, by simp [φ]⟩
  have hφτ : φ c.τ = t' := by
    rw [hφ]
    have := hψτ
    rw [hc'τ] at this
    exact this
  have hφω : φ c.ω = w' := by
    rw [hφ]
    have := hψω
    rw [hc'ω] at this
    exact this
  have hQ := mem_sup_zpowers_iff_of_injective φ hφinj hPφ hP'range c.τ c.ω
  rw [hφτ, hφω, ← hS'eq] at hQ
  refine ⟨hn, ψ₁, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro s hs
    have h1 : (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) ∈
        c.P ⊔ zpowers c.τ ⊔ zpowers c.ω := (hcS _).2 ⟨s, hs, rfl⟩
    have := (hQ _).1 h1
    exact this
  · intro a ha
    have h1 : a ∈ c.P ⊔ zpowers c.τ ⊔ zpowers c.ω := (hQ a).2 ha
    exact (hcS a).1 h1
  ·
    intro s hs
    have h1 : (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) ∈ c.P :=
      (hcP _).2 ⟨s, hs, rfl⟩
    have h2 := (hPφ _).1 h1
    have h3' : φ (QuotientGroup.mk s) ∈ (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂) := hc'P ▸ h2
    rw [← hEz] at h3'
    exact h3'.2
  · intro a haE haS
    have h1 : φ a ∈ c'.P := by
      rw [hc'P, ← hEz]
      exact ⟨haS, haE⟩
    exact (hcP a).1 ((hPφ a).2 h1)
  · intro s hs
    have h1 : (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = c.τ :=
      hcτ s hs
    have h2 : (⟨(QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)), hcXa _⟩ :
        ↥c.X) = ⟨c.τ, c.τ_mem_X⟩ := Subtype.ext h1
    show ((ψ₀ ⟨(QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)), hcXa _⟩ :
      ↥c'.X) : Gs) = t'
    rw [h2, hψτ, hc'τ]
  · intro s hs
    have h1 : (QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)) = c.ω :=
      hcω s hs
    have h2 : (⟨(QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)), hcXa _⟩ :
        ↥c.X) = ⟨c.ω, c.ω_mem_X⟩ := Subtype.ext h1
    show ((ψ₀ ⟨(QuotientGroup.mk s : ↥(K₁ ⊔ K₂ ⊔ S) ⧸ (Oz z).subgroupOf (K₁ ⊔ K₂ ⊔ S)), hcXa _⟩ :
      ↥c'.X) : Gs) = w'
    rw [h2, hψω, hc'ω]

end CFSG.GH74.GLS.IVK.Lifted
