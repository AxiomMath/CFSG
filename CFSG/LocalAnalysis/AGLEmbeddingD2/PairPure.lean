module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open

variable {G : Type*} [Group G]

theorem centralizer_conj_eq_map (h x : G) :
    Subgroup.centralizer ({h * x * h⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj h).toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨h⁻¹ * y * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have e : h⁻¹ * y * h * x = h⁻¹ * (y * (h * x * h⁻¹)) * h := by group
    have e' : x * (h⁻¹ * y * h) = h⁻¹ * ((h * x * h⁻¹) * y) * h := by group
    rw [e, e', hy]
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    change h * z * h⁻¹ * (h * x * h⁻¹) = h * x * h⁻¹ * (h * z * h⁻¹)
    have e : h * z * h⁻¹ * (h * x * h⁻¹) = h * (z * x) * h⁻¹ := by group
    have e' : h * x * h⁻¹ * (h * z * h⁻¹) = h * (x * z) * h⁻¹ := by group
    rw [e, e', hz]

theorem not_dvd_card_inf_centralizer_conj [Finite G] {p : ℕ} {M : Subgroup G}
    (hstr : GLBStronglyEmbedded p M) {x h : G}
    (hx : Subgroup.centralizer ({x} : Set G) ≤ M) (hh : h ∉ M) :
    ¬ p ∣ Nat.card (M ⊓ Subgroup.centralizer ({h * x * h⁻¹} : Set G) : Subgroup G) := by
  intro hdvd
  have hh' : h⁻¹ ∉ M := fun h1 => hh (by simpa using M.inv_mem h1)
  apply hstr.2.2 h⁻¹ hh'
  refine hdvd.trans (Subgroup.card_dvd_of_le (inf_le_inf_left M ?_))
  rw [centralizer_conj_eq_map, GLBConj, inv_inv]
  exact Subgroup.map_mono hx

theorem D2Escape.centralizer_le_of_three_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hesc : D2Escape p P M A H R) (hD1 : D1For G)
    (hβ : p ∈ GLBBetaFour G) {x : G} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hrank : 3 ≤ Open.pRank p (Subgroup.centralizer ({x} : Set G) ⊓ M)) :
    Subgroup.centralizer ({x} : Set G) ≤ M :=
  hD1 p hβ P M hesc.maxTwoLocal_M
    ((CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore p (P : Subgroup G)).trans
      hesc.core_le) _ (CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one hx2 hx1)
    hrank

theorem D2Escape.false_of_pure_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hesc : D2Escape p P M A H R) (hD1 : D1For G)
    (hβ : p ∈ GLBBetaFour G) (hstr : GLBStronglyEmbedded p M) {x h : G} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hrank : 3 ≤ Open.pRank p (Subgroup.centralizer ({x} : Set G) ⊓ M))
    (hh : h ∉ M)
    (hdvd : p ∣ Nat.card (M ⊓ Subgroup.centralizer ({h * x * h⁻¹} : Set G) : Subgroup G)) :
    False :=
  not_dvd_card_inf_centralizer_conj hstr
    (hesc.centralizer_le_of_three_le_pRank hD1 hβ hx2 hx1 hrank) hh hdvd

theorem D2Escape.false_of_pureSubgroup {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hesc : D2Escape p P M A H R) (hD1 : D1For G)
    (hβ : p ∈ GLBBetaFour G) (hstr : GLBStronglyEmbedded p M) {V : Subgroup G}
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {x : G} (hxV : x ∈ V) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hrank : 3 ≤ Open.pRank p (Subgroup.centralizer ({x} : Set G) ⊓ M))
    (hall : ∀ y ∈ V, y ≠ 1 →
      p ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)) : False := by
  obtain ⟨h, hH, hhM⟩ := IsConcreteLE.not_le_iff_exists.mp hesc.not_le
  have hyV : h * x * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hHV hH) x).mp hxV
  have hy1 : h * x * h⁻¹ ≠ 1 := fun h1 => hx1 (by
    have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [e, h1]; group)
  exact hesc.false_of_pure_conj hD1 hβ hstr hx2 hx1 hrank hhM (hall _ hyV hy1)

theorem D2Escape.false_of_pureVector {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hesc : D2Escape p P M A H R) (hD1 : D1For G)
    (hβ : p ∈ GLBBetaFour G) (hstr : GLBStronglyEmbedded p M) {x : G}
    (hxV : x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H)) (hx1 : x ≠ 1)
    (hrank : 3 ≤ Open.pRank p (Subgroup.centralizer ({x} : Set G) ⊓ M))
    (hall : ∀ y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), y ≠ 1 →
      p ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)) : False :=
  hesc.false_of_pureSubgroup hD1 hβ hstr
    (CFSG.AGLEmbedding.le_normalizer_of_characteristic_pCoreOf
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)) hxV
    ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).2 x hxV) hx1 hrank hall

end CFSG.AGLEmbeddingD2
