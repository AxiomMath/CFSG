module

public import CFSG.GH74.GLS.Stage4.T2Ctx
public import CFSG.GH74.GLS.Stage4.T2Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Ch6T2OddCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
      ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
        Ch6Loc5 N u → Ch6Coord N →
          ∀ m : G, Odd (orderOf m) → m ∈ centralizer ({z} : Set G) →
            (∀ s ∈ N.S, m * s * m⁻¹ ∈ N.S) → ∀ s ∈ N.S, m * s = s * m

@[expose] def Ch6T2FComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
      ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
        Ch6Loc5 N u → Ch6Coord N →
          ∀ f f' : G, Odd (orderOf f) → Odd (orderOf f') → (∀ s ∈ N.S, f * s = s * f) →
            (∀ s ∈ N.S, f' * s = s * f') → f * f' = f' * f

@[expose] def Ch6T2FNormX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
      ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
        Ch6Loc5 N u → Ch6Coord N →
          ∀ f : G, Odd (orderOf f) → (∀ s ∈ N.S, f * s = s * f) →
            (∀ x ∈ N.X₁, f * x * f⁻¹ ∈ N.X₁) ∧ (∀ x ∈ N.X₁', f * x * f⁻¹ ∈ N.X₁') ∧
              (∀ x ∈ N.X₂, f * x * f⁻¹ ∈ N.X₂) ∧ (∀ x ∈ N.X₂', f * x * f⁻¹ ∈ N.X₂')

theorem ch6T2P52_of_leaves
    (hOC : Ch6T2OddCent) (hFC : Ch6T2FComm) (hFX : Ch6T2FNormX) :
    Ch6T2P52 := by
  intro G _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have hOC' := hOC G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have hFC' := hFC G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have hFX' := hFX G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have hnormH := fun {f : G} (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ N.S, f * s = s * f) =>
    t2Ctx_normH hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hodd hfS
  subst hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨q₁, q₂, z, S, K₁, K₂, H, X₁, X₁', X₂, X₂', w₁, w₂⟩ := N
  have hzz : z * z = 1 := ctx.zz
  have hSctx : T2SCtx z K₁ K₂ S := ctx.Sctx
  have hZS := ctx.ZS
  have hSC₁ := ctx.SC₁
  have hKS := ctx.KS
  have hC₁C := ctx.C₁C
  have hC₁norm := ctx.C₁norm
  obtain ⟨hFodd, hFall, hcentS⟩ := t2C_cent_structure hSctx.S2 hSctx.Sidx hSctx.Sz hSctx.zS hzz hZS
    (F := (pPrimeCore 2 ↥(centralizer (S : Set G))).map (centralizer (S : Set G)).subtype) rfl
  refine ⟨(pPrimeCore 2 ↥(centralizer (S : Set G))).map (centralizer (S : Set G)).subtype, ?_⟩
  set F : Subgroup G := (pPrimeCore 2 ↥(centralizer (S : Set G))).map (centralizer (S : Set G)).subtype
    with hFdef
  have hFodd' : ∀ f ∈ F, Odd (orderOf f) := fun f hf => (hFodd f hf).1
  have hFcentS : ∀ f ∈ F, ∀ s ∈ S, f * s = s * f := fun f hf => (hFodd f hf).2
  refine
    { F_def := rfl
      F_odd := hFodd'
      F_comm := fun x hx y hy => hFC' x y (hFodd' x hx) (hFodd' y hy) (hFcentS x hx) (hFcentS y hy)
      F_inter_K := ?_
      C_le := ?_
      centS := hcentS
      F_normH := ?_
      F_normX₁ := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).1
      F_normX₁' := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).2.1
      F_normX₂ := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).2.2.1
      F_normX₂' := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).2.2.2 }
  ·
    rw [eq_bot_iff]
    rintro f ⟨hfF, hfK⟩
    have hfz : f ∈ Subgroup.zpowers z :=
      t2C_cent_K hSet hRem hSctx f hfK (fun s hs => hFcentS f hfF s hs)
    rcases t2C_zpowers_cases hzz hfz with h | h
    · exact Subgroup.mem_bot.2 h
    · exfalso
      have hodd := hFodd' f hfF
      rw [h, hSet.central.1] at hodd
      exact absurd hodd (by decide)
  ·
    intro c hc
    obtain ⟨n, hnC, hnS, k, hk, hcnk⟩ :=
      t2C_frattini hC₁C hC₁norm hSC₁ hSctx.S2 hSctx.Sidx c hc
    obtain ⟨s, m, hnsm, hsn, hmn, hs2, hmodd⟩ := t2C_two_part n
    have hnnorm : n ∈ normalizer (S : Set G) :=
      Subgroup.mem_normalizer_fintype (fun y hy => hnS y hy)
    have hzn : Subgroup.zpowers n ≤ normalizer (S : Set G) := Subgroup.zpowers_le.2 hnnorm
    have hsnorm : ∀ y ∈ S, s * y * s⁻¹ ∈ S := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 (hzn hsn) y).1 hy
    have hmnorm : ∀ y ∈ S, m * y * m⁻¹ ∈ S := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 (hzn hmn) y).1 hy
    have hsS : s ∈ S := t2C_mem_of_normalizes hSctx.S2 hSctx.Sidx hsnorm hs2
    have hmC : m ∈ centralizer ({z} : Set G) := (Subgroup.zpowers_le.2 hnC) hmn
    have hmcent := hOC' m hmodd hmC hmnorm
    have hmCS : m ∈ centralizer (S : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun s hs => (hmcent s hs).symm)
    have hmF : m ∈ F := hFall m hmCS hmodd
    have hkJ : k ∈ K₁ ⊔ K₂ ⊔ S := by rw [hKS]; exact hk
    rw [hcnk, hnsm]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hsS))
        (Subgroup.mem_sup_right hmF))
      (Subgroup.mem_sup_left hkJ)
  ·
    intro f hf
    refine Subgroup.mem_normalizer_fintype (fun h hh => ?_)
    exact hnormH (hFodd' f hf) (hFcentS f hf) h hh

end CFSG.GH74.GLS.Stage4.Rest
