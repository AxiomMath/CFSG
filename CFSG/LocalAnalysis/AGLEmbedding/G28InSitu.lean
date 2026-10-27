module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure G28InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ : Subgroup Y) (zb : Y)
    (V₀ : Subgroup Y) : Prop where
  z_mem : zb ∈ T
  z_center : zb ∈ Subgroup.centralizer (T : Set Y)
  z_order : orderOf zb = 3
  center_le : centerOf T ≤ Subgroup.zpowers zb
  card_T : Nat.card T = 3 ^ 6
  V_le : V₀ ≤ Y₀
  V_perfect : ⁅V₀, V₀⁆ = V₀
  V_normal : Y₀ ≤ Subgroup.normalizer (V₀ : Set Y)
  z_mem_V : zb ∈ V₀
  V_onto : ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V₀ →* CatGroup d), IsUThreeEightIndex d ∧
    Function.Surjective ψ
  V_quasi : ∀ W : Subgroup Y, W ≤ Y₀ → V₀ ≤ Subgroup.normalizer (W : Set Y) →
    V₀ ≤ W ∨ ⁅W, V₀⁆ = ⊥
  V_centralizer : Y₀ ⊓ Subgroup.centralizer (V₀ : Set Y) ≤ Subgroup.zpowers zb
  trichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ W ≤ Subgroup.zpowers zb ∨ V₀ ≤ W

@[expose] def KFactG28Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsGTwoEightIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ∃ (zb : Y) (V₀ : Subgroup Y), G28InSitu (T : Subgroup Y) Y₀ zb V₀

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem eq_of_map_eq_of_isPGroup {p : ℕ} [Fact p.Prime] {H R : Subgroup G} (hR : IsPGroup p R)
    {a b : H} (ha : (a : G) ∈ R) (hb : (b : G) ∈ R)
    (hab : QuotientGroup.mk' (primeComplementCore (G := H) p) a =
      QuotientGroup.mk' (primeComplementCore (G := H) p) b) : a = b := by
  have hp : p.Prime := Fact.out
  have hN : ((a⁻¹ * b : H) : G) ∈ GLBPrimeCore p H := by
    rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hab, inv_mul_cancel]
  have hRm : ((a⁻¹ * b : H) : G) ∈ R := by
    simpa using R.mul_mem (R.inv_mem ha) hb
  have hbot := inf_eq_bot_of_isPGroup hp hR (glbPrimeCore_coprime p H)
  have h1 : ((a⁻¹ * b : H) : G) ∈ R ⊓ GLBPrimeCore p H := ⟨hRm, hN⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have : a⁻¹ * b = 1 := Subtype.ext h1
  exact (inv_mul_eq_one.mp this)

end Lift

end CFSG.AGLEmbedding
