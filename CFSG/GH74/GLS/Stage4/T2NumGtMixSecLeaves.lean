module

public import CFSG.GH74.GLS.Stage4.T2LeafO
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecCtx
public import CFSG.GH74.GLS.Stage4.T2LeafC

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Lifted

section Leaves

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem mixSec_oddCent (hOC5 : T2OC5) (hOC3 : T2OC3)
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂)
    (hLoc : Ch6Loc5W N u) :
    ∀ m : G, Odd (orderOf m) → m ∈ centralizer ({z} : Set G) →
      (∀ s ∈ N.S, m * s * m⁻¹ ∈ N.S) → ∀ s ∈ N.S, m * s = s * m := by
  intro m hmodd hmC hmS
  have ctx := t2Ctx_ofW hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hmz : m * N.z = N.z * m := Subgroup.mem_centralizer_singleton_iff.1 hmC
  obtain ⟨hmn₁, hmn₂⟩ := t2Ctx_odd_normK ctx hmz hmodd
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have hSK₁ : ∀ s ∈ N.S, ∀ x ∈ N.K₁, s * x * s⁻¹ ∈ N.K₁ := fun s hs => hn₁ s (ctx.SC₁ hs)
  have hSK₂ : ∀ s ∈ N.S, ∀ x ∈ N.K₂, s * x * s⁻¹ ∈ N.K₂ := fun s hs => hn₂ s (ctx.SC₁ hs)
  have hP₁ : IsPGroup 2 ↥((N.S ⊓ N.K₁).subgroupOf N.K₁) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  have hP₂ : IsPGroup 2 ↥((N.S ⊓ N.K₂).subgroupOf N.K₂) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  have hgen : N.K₁ ⊔ N.K₂ ⊔ Subgroup.zpowers t =
      oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := hRem.gen
  have hlin₁ : ∀ h3 : 3 < Nat.card F₁, ∀ s ∈ N.S, ∃ hs : s ∈ normalizer (N.K₁ : Set G),
      (gammaOf hodd₁ h3 (MulAut.congr e₁ (Subgroup.normalizerMonoidHom N.K₁ ⟨s, hs⟩))).right = 1 := by
    intro h3 s hs
    exact t2L_lin_gen hodd₁ h3 e₁ hSet.comm (fun c hc => hn₁ c (hgen ▸ hc))
      (by obtain ⟨e, g, -, hact⟩ := hRem.diag₁; exact ⟨e, g, hact⟩) s
      (by rw [hgen]; exact ctx.SC₁ hs)
  have hlin₂ : ∀ h3 : 3 < Nat.card F₂, ∀ s ∈ N.S, ∃ hs : s ∈ normalizer (N.K₂ : Set G),
      (gammaOf hodd₂ h3 (MulAut.congr e₂ (Subgroup.normalizerMonoidHom N.K₂ ⟨s, hs⟩))).right = 1 := by
    intro h3 s hs
    exact t2L_lin_gen (K' := N.K₁) hodd₂ h3 e₂ (fun x hx y hy => (hSet.comm y hy x hx).symm)
      (fun c hc => hn₂ c (by rw [sup_comm N.K₂ N.K₁, hgen] at hc; exact hc))
      (by obtain ⟨e, g, -, hact⟩ := hRem.diag₂; exact ⟨e, g, hact⟩) s
      (by rw [sup_comm N.K₂ N.K₁, hgen]; exact ctx.SC₁ hs)
  obtain ⟨s₀, hs₀S, hs₀K⟩ : ∃ s₀ ∈ N.S, s₀ ∉ N.K₁ ⊔ N.K₂ := by
    by_contra hcon
    push Not at hcon
    have hSK : N.S ≤ N.K₁ ⊔ N.K₂ := fun s hs => hcon s hs
    have h1 : (N.S ⊓ (N.K₁ ⊔ N.K₂)).relIndex N.S = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact fun x hx => ⟨hx, hSK hx⟩
    have h2 := ctx.Sctx.SK
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have hkC₁ : ∀ k ∈ N.K₁ ⊔ N.K₂, k ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
    fun k hk => hSet.le_residual hk
  have hout₁ : ∃ s₀ ∈ N.S, ¬ ∃ k ∈ N.K₁, ∀ x ∈ N.K₁, s₀ * x * s₀⁻¹ = k * x * k⁻¹ := by
    refine ⟨s₀, hs₀S, ?_⟩
    rintro ⟨k, hk, hkx⟩
    have hyC₁ : k⁻¹ * s₀ ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hkC₁ k (Subgroup.mem_sup_left hk))) (ctx.SC₁ hs₀S)
    have hyK : k⁻¹ * s₀ ∉ N.K₁ ⊔ N.K₂ := by
      intro h
      apply hs₀K
      have : s₀ = k * (k⁻¹ * s₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) h
    exact t2C_not_cent_K₁ hSet hRem ctx.C hyC₁ hyK (fun x hx => by
      have := hkx x hx
      calc k⁻¹ * s₀ * x = k⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
        _ = k⁻¹ * (k * x * k⁻¹) * s₀ := by rw [this]
        _ = x * (k⁻¹ * s₀) := by group)
  have hout₂ : ∃ s₀ ∈ N.S, ¬ ∃ k ∈ N.K₂, ∀ x ∈ N.K₂, s₀ * x * s₀⁻¹ = k * x * k⁻¹ := by
    refine ⟨s₀, hs₀S, ?_⟩
    rintro ⟨k, hk, hkx⟩
    have hyC₁ : k⁻¹ * s₀ ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hkC₁ k (Subgroup.mem_sup_right hk))) (ctx.SC₁ hs₀S)
    have hyK : k⁻¹ * s₀ ∉ N.K₁ ⊔ N.K₂ := by
      intro h
      apply hs₀K
      have : s₀ = k * (k⁻¹ * s₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) h
    exact t2C_not_cent_K₂ hSet hRem ctx.C hyC₁ hyK (fun x hx => by
      have := hkx x hx
      calc k⁻¹ * s₀ * x = k⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
        _ = k⁻¹ * (k * x * k⁻¹) * s₀ := by rw [this]
        _ = x * (k⁻¹ * s₀) := by group)
  have hd₁ := t2L_oddcent_factor hOC5 hOC3 (F := F₁) hodd₁
    (by rw [hSet.card₁]; have := hSet.five; omega) e₁ hP₁ hs₁ ctx.Sctx.S2 hSK₁ hlin₁ hout₁ hmodd
    hmn₁ hmS
  have hd₂ := t2L_oddcent_factor hOC5 hOC3 (F := F₂) hodd₂
    (by rw [hSet.card₂]; have := hLoc.q₂_ge; omega) e₂ hP₂ hs₂ ctx.Sctx.S2 hSK₂ hlin₂ hout₂ hmodd
    hmn₂ hmS
  intro s hs
  have hdS : m * s * m⁻¹ * s⁻¹ ∈ N.S := N.S.mul_mem (hmS s hs) (N.S.inv_mem hs)
  have hdK : ∀ k ∈ N.K₁ ⊔ N.K₂, (m * s * m⁻¹ * s⁻¹) * k = k * (m * s * m⁻¹ * s⁻¹) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hx
    have h1 := hd₁ s hs a ha
    have h2 := hd₂ s hs b hb
    calc (m * s * m⁻¹ * s⁻¹) * (a * b) = ((m * s * m⁻¹ * s⁻¹) * a) * b := by group
      _ = (a * (m * s * m⁻¹ * s⁻¹)) * b := by rw [h1]
      _ = a * ((m * s * m⁻¹ * s⁻¹) * b) := by group
      _ = a * (b * (m * s * m⁻¹ * s⁻¹)) := by rw [h2]
      _ = (a * b) * (m * s * m⁻¹ * s⁻¹) := by group
  have hdz : m * s * m⁻¹ * s⁻¹ ∈ Subgroup.zpowers N.z :=
    t2C_centK_C₁ hSet hRem ctx.C _ (ctx.SC₁ hdS) hdK
  rcases t2C_zpowers_cases ctx.zz hdz with h | h
  · calc m * s = (m * s * m⁻¹ * s⁻¹) * s * m := by group
      _ = s * m := by rw [h]; group
  · exfalso
    refine t2L_odd_central_twist hmz ctx.zz ctx.z_ne hmodd (s := s) ?_
    calc m * s * m⁻¹ = (m * s * m⁻¹ * s⁻¹) * s := by group
      _ = N.z * s := by rw [h]

theorem mixSec_FComm (hC3 : T2C3)
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂)
    (hLoc : Ch6Loc5W N u) :
    ∀ f f' : G, Odd (orderOf f) → Odd (orderOf f') → (∀ s ∈ N.S, f * s = s * f) →
      (∀ s ∈ N.S, f' * s = s * f') → f * f' = f' * f := by
  intro f f' hodd hodd' hfS hfS'
  have ctx := t2Ctx_ofW hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
  have hfz' : f' * N.z = N.z * f' := hfS' N.z hLoc.z_mem_S
  obtain ⟨hfn₁, hfn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
  obtain ⟨hfn₁', hfn₂'⟩ := t2Ctx_odd_normK ctx hfz' hodd'
  obtain ⟨hFodd, hFall, -⟩ := t2C_cent_structure ctx.Sctx.S2 ctx.Sctx.Sidx ctx.Sctx.Sz ctx.Sctx.zS
    ctx.zz ctx.ZS
    (F := (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map (centralizer (N.S : Set G)).subtype) rfl
  set F : Subgroup G := (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map
    (centralizer (N.S : Set G)).subtype with hFdef
  have hfF : f ∈ F := hFall f (Subgroup.mem_centralizer_iff.2 (fun s hs => (hfS s hs).symm)) hodd
  have hfF' : f' ∈ F := hFall f' (Subgroup.mem_centralizer_iff.2 (fun s hs => (hfS' s hs).symm)) hodd'
  have hcF : f * f' * f⁻¹ * f'⁻¹ ∈ F :=
    F.mul_mem (F.mul_mem (F.mul_mem hfF hfF') (F.inv_mem hfF)) (F.inv_mem hfF')
  have hcodd : Odd (orderOf (f * f' * f⁻¹ * f'⁻¹)) := (hFodd _ hcF).1
  have hcz : (f * f' * f⁻¹ * f'⁻¹) * N.z = N.z * (f * f' * f⁻¹ * f'⁻¹) :=
    t2L_comm_cent (hfS _ hLoc.z_mem_S) (hfS' _ hLoc.z_mem_S)
  have hcC : f * f' * f⁻¹ * f'⁻¹ ∈ centralizer ({N.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcz
  have hP₁ : IsPGroup 2 ↥(N.S ⊓ N.K₁) := ctx.Sctx.S2.to_le inf_le_left
  have hP₂ : IsPGroup 2 ↥(N.S ⊓ N.K₂) := ctx.Sctx.S2.to_le inf_le_left
  have hc₁ := t2L_comm_factor hC3 (F := F₁) (by rw [hSet.card₁]; exact hSet.odd₁)
    (by rw [hSet.card₁]; have := hSet.five; omega) e₁ hSet.z_mem₁ hze₁ ctx.C.zc₁ hP₁ hs₁ hfn₁
    hfn₁' hfS hfS'
  have hc₂ := t2L_comm_factor hC3 (F := F₂) (by rw [hSet.card₂]; exact hSet.odd₂)
    (by rw [hSet.card₂]; have := hLoc.q₂_ge; omega) e₂ hSet.z_mem₂ hze₂ ctx.C.zc₂ hP₂ hs₂ hfn₂
    hfn₂' hfS hfS'
  have hcK : ∀ x ∈ N.K₁ ⊔ N.K₂, (f * f' * f⁻¹ * f'⁻¹) * x = x * (f * f' * f⁻¹ * f'⁻¹) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hx
    have h1 := hc₁ a ha
    have h2 := hc₂ b hb
    calc (f * f' * f⁻¹ * f'⁻¹) * (a * b) = ((f * f' * f⁻¹ * f'⁻¹) * a) * b := by group
      _ = (a * (f * f' * f⁻¹ * f'⁻¹)) * b := by rw [h1]
      _ = a * ((f * f' * f⁻¹ * f'⁻¹) * b) := by group
      _ = a * (b * (f * f' * f⁻¹ * f'⁻¹)) := by rw [h2]
      _ = (a * b) * (f * f' * f⁻¹ * f'⁻¹) := by group
  have hc1 : f * f' * f⁻¹ * f'⁻¹ = 1 := t2C_R_odd_trivial hSet hRem ctx _ hcC hcodd hcK
  calc f * f' = (f * f' * f⁻¹ * f'⁻¹) * f' * f := by group
    _ = f' * f := by rw [hc1]; group

theorem mixSec_FNormX₂ (hC3 : T2C3)
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂)
    (hLoc : Ch6Loc5M N u) (hCoord : Ch6Coord2 N) :
    ∀ f : G, Odd (orderOf f) → (∀ s ∈ N.S, f * s = s * f) →
      (∀ x ∈ N.X₂, f * x * f⁻¹ ∈ N.X₂) ∧ (∀ x ∈ N.X₂', f * x * f⁻¹ ∈ N.X₂') := by
  intro f hodd hfS
  have ctx := t2Ctx_ofW hSet hRem hLoc.toCh6Loc5W hz hK₁ hK₂ hq₁ hq₂
  have hnormH := t2MixSec_normH hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hodd hfS
  subst hz hK₁ hK₂ hq₁ hq₂
  have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
  obtain ⟨-, hfn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
  have hfH : f ∈ normalizer (N.H : Set G) := Subgroup.mem_normalizer_fintype hnormH
  have hfH' : ∀ h ∈ N.H, f⁻¹ * h * f ∈ N.H := fun h hh => by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hfH) h).1 hh
  obtain ⟨-, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  have hP₂ : IsPGroup 2 ↥((N.S ⊓ N.K₂).subgroupOf N.K₂) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  exact t2L_factor hLoc.q₂_odd hLoc.q₂_ge hCoord.coord₂ hLoc.card_X₂ hodd hfn₂ hfH'
    hLoc.H_norm_X₂ (hfS N.w₂ hLoc.w₂_memS) (fun h3 => by
      obtain ⟨F', _, _, hF'card, ⟨e⟩⟩ := hLoc.iso₂
      exact t2L_cent_of_q3 hC3 (hF'card.trans h3) e hP₂ hs₂ hfn₂ hfS)

end Leaves

end CFSG.GH74.GLS.Stage4.Rest
