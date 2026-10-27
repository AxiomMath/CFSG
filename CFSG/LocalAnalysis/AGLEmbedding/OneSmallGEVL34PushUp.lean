module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34PushUpEsc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph7
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Unique

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.eq_of_maxTwoLocal_of_l34 (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hQS : pCoreOf 2 M ⊓ pCoreOf 2 H ≠ ⊥)
    {J H₁ : Subgroup G} (hJH : J ≤ H)
    (hJM : ∀ h ∈ H, ∃ a ∈ J, ∃ b ∈ H ⊓ M, h = a * b)
    (htr : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
      ∃ n ∈ J ⊓ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ = s)
    (hH₁ : GLBIsMaxTwoLocal H₁) (hJH₁ : J ≤ H₁) (hRH₁ : R ≤ H₁) : H₁ = H := by
  have hH₁M : ¬ H₁ ≤ M := by
    intro hle
    apply hd.cfg.ext.not_le
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hJM h hh
    exact M.mul_mem (hle (hJH₁ ha)) hb.2
  have hfac := hd.mul_mem_of_l34_escape hβ hα h2 h3 hOut hExp hSh3 hO hz hB0 hp3 hL hOR hCz
    hH₁ hH₁M hRH₁ (fun t ht ht1 s hs hs1 => by
      obtain ⟨n, ⟨hnJ, hnN⟩, h1, h2', h3'⟩ := htr t ht ht1 s hs hs1
      exact ⟨n, ⟨hJH₁ hnJ, hnN⟩, h1, h2', h3'⟩)
  refine L34Squeeze.eq_of_factorizations (S := pCoreOf 2 H) (Q := pCoreOf 2 M)
    hd.cfg.ext.maxTwoLocal_H hH₁ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    hd.cfg.ext.toD1Escape.twoCore_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hQS (fun h hh => ?_) hfac
  obtain ⟨a, ha, b, hb, he⟩ := hJM h hh
  exact ⟨a, ⟨hJH ha, hJH₁ ha⟩, b, hb, he⟩

theorem D1OneSmallData.false_of_pushingUp_l34 (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hQS : pCoreOf 2 M ⊓ pCoreOf 2 H ≠ ⊥) (hcon : HasPrimeConstraint (G := M) 3)
    {V C J : Subgroup G} (hsyl : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hCV : C ≤ V) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf V).Characteristic) (hJH : J ≤ H)
    (hJM : ∀ h ∈ H, ∃ a ∈ J, ∃ b ∈ H ⊓ M, h = a * b)
    (htr : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
      ∃ n ∈ J ⊓ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ = s)
    (hJC : J ≤ Subgroup.normalizer (C : Set G)) : False := by
  have hNVC : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := V) (C.subgroupOf V)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCV] at h1
  have hC2 : IsPGroup 2 C := hsyl.2.1.to_le hCV
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hC2, rfl⟩
  obtain ⟨H₁, hNH₁, hH₁m⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hloc
  have hH₁ : GLBIsMaxTwoLocal H₁ :=
    ⟨hH₁m.1, fun K' hK' hMK => le_antisymm (hH₁m.2 hK' hMK) hMK⟩
  have hEq := hd.eq_of_maxTwoLocal_of_l34 hβ hα h2 h3 hOut hExp hSh3 hO hz hB0 hp3 hL hOR hCz
    hQS hJH hJM htr hH₁ (hJC.trans hNH₁) (hRV.trans (hNVC.trans hNH₁))
  have hNV : M ⊓ Subgroup.normalizer (V : Set G) ≤ H :=
    inf_le_right.trans (hNVC.trans (hNH₁.trans hEq.le))
  exact hd.false_of_hasPrimeConstraint_of_isSylowTwoOf hUE hOrb hExp hOut hSh3 hO hz hB0 hp3 hL
    hOR hcon hsyl hNV

end CFSG.AGLEmbedding
