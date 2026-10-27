module

public import CFSG.GH74.GLS.Stage4.T2P52Done
public import CFSG.GH74.GLS.Stage4.T2P51
public import CFSG.GH74.GLS.Stage4.T2HOdd9

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Nine

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ S : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2_odd_cent_K₁_nine {q₁ q₂ : ℕ} (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hS : T2SCtx z K₁ K₂ S) (hF₁ : Nat.card F₁ = 9) {f : G}
    (hfn : ∀ x ∈ K₁, f * x * f⁻¹ ∈ K₁) (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ S, f * s = s * f) :
    ∀ y ∈ K₁, f * y * f⁻¹ = y := by
  have := hSet.finite₁
  obtain ⟨⟨e₁, hze₁⟩, -⟩ := t2C_coords hSet
  obtain ⟨hs₁, -⟩ := t2C_sylow_inf_K hSet hRem hS
  have hfm : f ∈ normalizer (K₁ : Set G) := Subgroup.mem_normalizer_fintype hfn
  let ρ : MulAut ↥K₁ := Subgroup.normalizerMonoidHom K₁ ⟨f, hfm⟩
  have hρ : ∀ y : ↥K₁, ((ρ y : ↥K₁) : G) = f * y * f⁻¹ := fun y => rfl
  have hρodd : Odd (orderOf ρ) := by
    have hdvd := orderOf_map_dvd K₁.normalizerMonoidHom (⟨f, hfm⟩ : Subgroup.normalizer (K₁ : Set G))
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hP : IsPGroup 2 ↥((S ⊓ K₁).subgroupOf K₁) := (hS.S2.to_le inf_le_left).comap_subtype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥K₁ := hP.toSylow hs₁
  have hPcoe : (P : Subgroup ↥K₁) = (S ⊓ K₁).subgroupOf K₁ := IsPGroup.toSylow_coe hP hs₁
  have hfix : ∀ p ∈ (P : Subgroup ↥K₁), ρ p = p := by
    intro p hp
    rw [hPcoe] at hp
    apply Subtype.ext
    rw [hρ]
    have := hfS (p : G) (Subgroup.mem_subgroupOf.1 hp).1
    calc f * (p : G) * f⁻¹ = (p : G) * f * f⁻¹ := by rw [this]
      _ = p := by group
  have h1 : ρ = 1 := t2H_oddAut_sl9 hF₁ e₁ P ρ hρodd hfix
  intro y hy
  have h2 := congrArg (fun r : MulAut ↥K₁ => ((r ⟨y, hy⟩ : ↥K₁) : G)) h1
  simpa [hρ] using h2

theorem t2_odd_cent_K₂_nine {q₁ q₂ : ℕ} (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hS : T2SCtx z K₁ K₂ S) (hF₂ : Nat.card F₂ = 9) {f : G}
    (hfn : ∀ x ∈ K₂, f * x * f⁻¹ ∈ K₂) (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ S, f * s = s * f) :
    ∀ y ∈ K₂, f * y * f⁻¹ = y := by
  have := hSet.finite₂
  obtain ⟨-, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  obtain ⟨-, hs₂⟩ := t2C_sylow_inf_K hSet hRem hS
  have hfm : f ∈ normalizer (K₂ : Set G) := Subgroup.mem_normalizer_fintype hfn
  let ρ : MulAut ↥K₂ := Subgroup.normalizerMonoidHom K₂ ⟨f, hfm⟩
  have hρ : ∀ y : ↥K₂, ((ρ y : ↥K₂) : G) = f * y * f⁻¹ := fun y => rfl
  have hρodd : Odd (orderOf ρ) := by
    have hdvd := orderOf_map_dvd K₂.normalizerMonoidHom (⟨f, hfm⟩ : Subgroup.normalizer (K₂ : Set G))
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hP : IsPGroup 2 ↥((S ⊓ K₂).subgroupOf K₂) := (hS.S2.to_le inf_le_left).comap_subtype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥K₂ := hP.toSylow hs₂
  have hPcoe : (P : Subgroup ↥K₂) = (S ⊓ K₂).subgroupOf K₂ := IsPGroup.toSylow_coe hP hs₂
  have hfix : ∀ p ∈ (P : Subgroup ↥K₂), ρ p = p := by
    intro p hp
    rw [hPcoe] at hp
    apply Subtype.ext
    rw [hρ]
    have := hfS (p : G) (Subgroup.mem_subgroupOf.1 hp).1
    calc f * (p : G) * f⁻¹ = (p : G) * f * f⁻¹ := by rw [this]
      _ = p := by group
  have h1 : ρ = 1 := t2H_oddAut_sl9 hF₂ e₂ P ρ hρodd hfix
  intro y hy
  have h2 := congrArg (fun r : MulAut ↥K₂ => ((r ⟨y, hy⟩ : ↥K₂) : G)) h1
  simpa [hρ] using h2

end Nine

section Main

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2_C_eq_C₁_nine
    (hSet : Ch6Setup G Gs 9 9 z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) :
    centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
  obtain ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    ch6T2P51 G Gs 9 9 z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ :=
    ch6T2P52 G Gs 9 9 z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂
  have hF1 : ∀ f ∈ F, f = 1 := by
    intro f hf
    have hodd : Odd (orderOf f) := hF5.F_odd f hf
    have hfS : ∀ s ∈ N.S, f * s = s * f := by
      intro s hs
      have hfC : f ∈ centralizer (N.S : Set G) := by
        rw [hF5.centS]; exact Subgroup.mem_sup_right hf
      exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
    have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
    have hfC' : f ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hfz
    obtain ⟨hn₁, hn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
    have hc₁ := t2_odd_cent_K₁_nine hSet hRem ctx.Sctx hSet.card₁ hn₁ hodd hfS
    have hc₂ := t2_odd_cent_K₂_nine hSet hRem ctx.Sctx hSet.card₂ hn₂ hodd hfS
    refine t2C_R_odd_trivial hSet hRem ctx f hfC' hodd ?_
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm k).1 hk
    have e1 := hc₁ a ha
    have e2 := hc₂ b hb
    calc f * (a * b) = (f * a * f⁻¹) * (f * b * f⁻¹) * f := by group
      _ = a * b * f := by rw [e1, e2]
  intro c hc
  have h1 := hF5.C_le hc
  have h2 : c ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    have hFb : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hF1
    rw [hFb, sup_bot_eq] at h1
    exact h1
  rw [← ctx.KS]
  exact h2

end Main

end CFSG.GH74.GLS.Stage4.Rest
