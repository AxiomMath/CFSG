module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecLeaves
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecDefs
public import CFSG.GH74.GLS.Stage4.T2SL3C
public import CFSG.GH74.GLS.Stage4.T2SL3O
public import CFSG.GH74.GLS.Stage4.T2SL5

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem ch6Mix_f5 :
    Ch6MixF5 := by
  intro G _ _ hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem hlt hmod N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  suffices h : ∃ F : Subgroup G, Ch6F5W (⟨N, F⟩ : T2N2 G) by
    obtain ⟨F, hF⟩ := h
    exact ⟨⟨N, F⟩, rfl, hF⟩
  have hLocW : Ch6Loc5W N u := hLoc.toCh6Loc5W
  have hOC' := mixSec_oddCent t2_oc5 t2_oc3 hSet hRem hz hK₁ hK₂ hq₁ hq₂ hLocW
  have hFC' := mixSec_FComm t2_c3 hSet hRem hz hK₁ hK₂ hq₁ hq₂ hLocW
  have hFX' := mixSec_FNormX₂ t2_c3 hSet hRem hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_ofW hSet hRem hLocW hz hK₁ hK₂ hq₁ hq₂
  have hnormH := fun {f : G} (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ N.S, f * s = s * f) =>
    t2MixSec_normH hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hodd hfS
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
      F_normX₂ := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).1
      F_normX₂' := fun f hf => (hFX' f (hFodd' f hf) (hFcentS f hf)).2 }
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
