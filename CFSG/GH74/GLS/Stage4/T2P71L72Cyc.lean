module

public import CFSG.GH74.GLS.Stage4.T2P71L72AbCyc
public import CFSG.GH74.GLS.Stage4.T2P71L72Env

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.F1Loc
  CFSG.Assembly.LowTwoRank

theorem sigma_unique {G : Type} [Group G] {F₁ : Type} [Field F₁] {φ : SL2 F₁ →* G}
    (hinj : Function.Injective φ) {σ τ : F₁ ≃+* F₁}
    (h : ∀ M : SL2 F₁, φ (Matrix.SpecialLinearGroup.map (σ : F₁ →+* F₁) M) =
      φ (Matrix.SpecialLinearGroup.map (τ : F₁ →+* F₁) M)) : σ = τ := by
  ext c
  have h1 := h (sl2U c)
  rw [map_sl2U, map_sl2U] at h1
  exact sl2U_injective (hinj h1)

section Cyc


variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {n : ℕ} {N : T2N3 G} {u : G}

theorem F_isCyclic (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hIVK : CFSG.GH74.GLS.IVK.IVK_4_1_R_L3)
    (h : P71Env Gs n N u) (hlt : Lt3 G n) (hn : 3 ≤ n) : IsCyclic ↥N.F := by
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  have hSec := h.sec5
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have : Finite F₁ := hS.finite₁
  have : Finite F₂ := hS.finite₂
  have hq : N.q₁ = N.q₂ := h.q₁.trans h.q₂.symm
  have hcard₁ : Nat.card F₁ = N.q₁ := by rw [h.q₁]; exact hS.card₁
  have hcard₂ : Nat.card F₂ = N.q₂ := by rw [h.q₂]; exact hS.card₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hcard₁]; exact hLoc.q₁_odd
  have hodd₂ : Odd (Nat.card F₂) := by rw [hcard₂]; exact hLoc.q₂_odd
  obtain ⟨φ₁, hφ₁, hrange₁, -, hX₁, -, hw₁, hHK₁⟩ := exists_coord_over h.coord hcard₁
  obtain ⟨φ₂, hφ₂, hrange₂, -, hX₂, -, hw₂, hHK₂⟩ :=
    exists_coord_over (N := N.swap.toT2N2.toT2N1) (Ch6Coord.swap h.coord) hcard₂
  have hrange₂' : φ₂.range = N.K₂ := hrange₂
  have hHK₂' : N.H ⊓ N.K₂ = (tSub F₂).map φ₂ := hHK₂
  have hFS : ∀ f ∈ N.F, ∀ s ∈ N.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N.S : Set G) := by
      rw [hF5.centS]; exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hex₁ : ∀ f : ↥N.F, ∃ σ : F₁ ≃+* F₁, ∀ M : SL2 F₁,
      (f : G) * φ₁ M * (f : G)⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ : F₁ →+* F₁) M) := fun f =>
    exists_sigma_fixed hSec hodd₁ hφ₁ hX₁ hHK₁ hw₁ f.2 (hFS f f.2)
  have hex₂ : ∀ f : ↥N.F, ∃ σ : F₂ ≃+* F₂, ∀ M : SL2 F₂,
      (f : G) * φ₂ M * (f : G)⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ : F₂ →+* F₂) M) := fun f =>
    exists_sigma_fixed (N := N.swap) (hSec.swap hq) hodd₂ hφ₂ hX₂ hHK₂ hw₂ f.2 (hFS f f.2)
  choose σ₁ hσ₁ using hex₁
  choose σ₂ hσ₂ using hex₂
  have hmul : ∀ f g : ↥N.F, σ₁ (f * g) = σ₁ f * σ₁ g := by
    intro f g
    apply sigma_unique hφ₁
    intro M
    have e1 := hσ₁ (f * g) M
    have e2 : ((f * g : ↥N.F) : G) * φ₁ M * ((f * g : ↥N.F) : G)⁻¹ =
        (f : G) * ((g : G) * φ₁ M * (g : G)⁻¹) * (f : G)⁻¹ := by
      show (f : G) * (g : G) * φ₁ M * ((f : G) * (g : G))⁻¹ = _
      group
    rw [e2, hσ₁ g M, hσ₁ f] at e1
    exact e1.symm
  have hone : σ₁ 1 = 1 := by
    apply sigma_unique hφ₁
    intro M
    have e1 := hσ₁ 1 M
    have : ((1 : ↥N.F) : G) * φ₁ M * ((1 : ↥N.F) : G)⁻¹ = φ₁ M := by simp
    rw [this] at e1
    rw [← e1]
    congr 1
  let θ : ↥N.F →* (F₁ ≃+* F₁) :=
    { toFun := σ₁
      map_one' := hone
      map_mul' := hmul }
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro f hf1
    have hσ1 : σ₁ f = 1 := hf1
    have hfodd : Odd (orderOf (f : G)) := hF5.F_odd f f.2
    have hfr : (f : G) ^ orderOf (f : G) = 1 := pow_orderOf_eq_one _
    have hσ2 : σ₂ f = 1 :=
      sigma₂_eq_one_of_sigma₁_eq_one_lt hL hL3 hIVK hn h.std hS hR hlt (N := N) (u := u) rfl rfl rfl
        h.q₁ h.q₂ hSec f.2 hfodd hfr hHK₁ (hσ₁ f) hφ₂ hHK₂' (hσ₂ f) hσ1
    have hc₁ : ∀ x ∈ N.K₁, x * (f : G) = (f : G) * x := by
      intro x hx
      rw [← hrange₁] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₁ (f : G) (σ₁ f) (hσ₁ f) hσ1 M
      calc φ₁ M * (f : G) = ((f : G) * φ₁ M * (f : G)⁻¹) * (f : G) := by rw [this]
        _ = (f : G) * φ₁ M := by group
    have hc₂ : ∀ x ∈ N.K₂, x * (f : G) = (f : G) * x := by
      intro x hx
      rw [← hrange₂'] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₂ (f : G) (σ₂ f) (hσ₂ f) hσ2 M
      calc φ₂ M * (f : G) = ((f : G) * φ₂ M * (f : G)⁻¹) * (f : G) := by rw [this]
        _ = (f : G) * φ₂ M := by group
    exact Subtype.ext (f_eq_one_of_trivial hSec f.2 (hFS f f.2) hfodd hc₁ hc₂)
  have : IsCyclic (F₁ ≃+* F₁) := CFSG.GH74.GLS.IVK.ringAut_isCyclic F₁
  exact isCyclic_of_injective θ hθ

theorem abCyc_of_cent (h : P71Env Gs n N u) (hcyc : IsCyclic ↥N.F) (P : Subgroup G)
    (hPC : P ≤ centralizer ({N.z} : Set G)) (hP3 : IsPGroup 3 ↥P) : AbCyc ↥P := by
  have hctx := h.ctx
  have hSec := h.sec5
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  set C : Subgroup G := centralizer ({N.z} : Set G) with hC
  set C₁ : Subgroup G := N.K₁ ⊔ N.K₂ ⊔ N.S with hC₁
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => hctx.FS f hf _ hLoc.z_mem_S
  have hFn : N.F ≤ normalizer (C₁ : Set G) := t2P53_F_normC₁ hctx.ctx hFz
  have hCeq : C = C₁ ⊔ N.F := T6.cent_z_eq hctx
  have hC₁C : C₁ ≤ C := by rw [hCeq]; exact le_sup_left
  have hFC : N.F ≤ C := by rw [hCeq]; exact le_sup_right
  have hCn : ∀ c ∈ C, ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁ := by
    intro c hc x hx
    have hcm : c ∈ C₁ ⊔ N.F := by rw [← hCeq]; exact hc
    obtain ⟨c₁, hc₁, f, hf, rfl⟩ := t2P53_split hFn hcm
    have h1 : f * x * f⁻¹ ∈ C₁ := (Subgroup.mem_normalizer_iff.1 (hFn hf) x).1 hx
    have : c₁ * f * x * (c₁ * f)⁻¹ = c₁ * (f * x * f⁻¹) * c₁⁻¹ := by group
    rw [this]
    exact C₁.mul_mem (C₁.mul_mem hc₁ h1) (C₁.inv_mem hc₁)
  let C₁' : Subgroup ↥C := C₁.subgroupOf C
  have hC₁'n : C₁'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : G) ∈ C₁ := hx
    have := hCn g g.2 x hx'
    show (g * x * g⁻¹ : ↥C) ∈ C₁.subgroupOf C
    exact this
  let ψ : ↥N.F →* (↥C ⧸ C₁') :=
    (QuotientGroup.mk' C₁').comp (Subgroup.inclusion hFC)
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      have hcm : (c : G) ∈ C₁ ⊔ N.F := by rw [← hCeq]; exact c.2
      obtain ⟨c₁, hc₁, f, hf, hcf⟩ := t2P53_split hFn hcm
      refine ⟨⟨f, hf⟩, ?_⟩
      show (QuotientGroup.mk (⟨f, hFC hf⟩ : ↥C) : ↥C ⧸ C₁') = QuotientGroup.mk c
      rw [QuotientGroup.eq]
      show ((⟨f, hFC hf⟩ : ↥C)⁻¹ * c : ↥C) ∈ C₁.subgroupOf C
      have : (((⟨f, hFC hf⟩ : ↥C)⁻¹ * c : ↥C) : G) = f⁻¹ * (c₁ * f) := by
        rw [← hcf]; rfl
      show (((⟨f, hFC hf⟩ : ↥C)⁻¹ * c : ↥C) : G) ∈ C₁
      rw [this]
      have hn' : f⁻¹ ∈ normalizer (C₁ : Set G) := (Subgroup.normalizer _).inv_mem (hFn hf)
      have := (Subgroup.mem_normalizer_iff.1 hn' c₁).1 hc₁
      simpa [mul_assoc] using this
  have hQcyc : IsCyclic (↥C ⧸ C₁') := isCyclic_of_surjective ψ hψ
  let ρ : ↥P →* (↥C ⧸ C₁') := (QuotientGroup.mk' C₁').comp (Subgroup.inclusion hPC)
  refine ⟨ρ.ker, inferInstance, ?_, ?_⟩
  ·
    have hker : ∀ x : ↥P, x ∈ ρ.ker → (x : G) ∈ C₁ := by
      intro x hx
      have : ρ x = 1 := hx
      have h1 : (QuotientGroup.mk (⟨(x : G), hPC x.2⟩ : ↥C) : ↥C ⧸ C₁') = 1 := this
      rw [QuotientGroup.eq_one_iff] at h1
      exact h1
    set E : Subgroup G := ρ.ker.map P.subtype with hE
    have hEK : E ≤ N.K₁ ⊔ N.K₂ := by
      rintro _ ⟨x, hx, rfl⟩
      have hxC₁ := hker x hx
      have hodd : Odd (orderOf (x : G)) := by
        obtain ⟨k, hk⟩ := hP3 x
        have hk' : (x : G) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hk')
      exact hctx.oddK _ hxC₁ hodd
    have hEp : IsPGroup 3 ↥E := hP3.to_le (by rintro _ ⟨x, -, rfl⟩; exact x.2 : E ≤ P)
    have hn0 : n ≠ 0 := by have := h.n_ge; omega
    have hab := t2F1_three_abelian hn0 hS hLoc rfl rfl h.q₁ h.q₂ E hEK hEp
    intro x hx y hy
    exact Subtype.ext (hab x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩)
  · exact isCyclic_of_injective (QuotientGroup.kerLift ρ) (QuotientGroup.kerLift_injective ρ)

end Cyc

end CFSG.GH74.GLS.Stage4.Rest.L72
