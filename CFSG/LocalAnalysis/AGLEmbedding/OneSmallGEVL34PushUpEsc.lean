module

import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Esc

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

open CFSG.ComponentClassification in
theorem D1OneSmallData.mul_mem_of_l34_escape (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hH₁M : ¬ H₁ ≤ M) (hRH₁ : R ≤ H₁)
    (htr : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
      ∃ n ∈ H₁ ⊓ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ = s) :
    ∀ n ∈ H₁, ∃ a ∈ H ⊓ H₁, ∃ b ∈ H₁ ⊓ M, n = a * b := by
  subst hp3
  obtain ⟨Rbar₁, K₁, hcfg₁, hK₁, hnc, -, hN₁, hY₁⟩ := hd.exists_l34_escape_component hβ hα h2 h3
    hOut hExp hSh3 hO hz hB0 rfl hL hOR hH₁ hH₁M hRH₁ htr
  have hext₁ : D1Extremal 3 P M H₁ R := hd.cfg.ext.of_le hH₁ hRH₁ hH₁M
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) 3) with hπ₁
  set zH : H₁ := ⟨z, hRH₁ hz.1⟩ with hzHdef
  set Y₁ : Subgroup H₁ := Subgroup.centralizer ({zH} : Set H₁) ⊓ K₁.comap π₁ with hY₁def
  have hK₁n : K₁.Normal := hcfg₁.red.normal_of_rankOne hK₁ hnc
  obtain ⟨T₂, hT₂⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar₁
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK₁.2.1
      Subgroup.IsSubnormal.top)
  have htop : Subgroup.normalizer (((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊓
      K₁ : Subgroup _) : Set (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊔ K₁ = ⊤ := by
    rw [← hT₂]
    exact Sylow.normalizer_sup_eq_top T₂
  intro n hn
  have hnt : π₁ ⟨n, hn⟩ ∈ K₁ ⊔ Subgroup.normalizer
      (((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊓ K₁ : Subgroup _) :
        Set (H₁ ⧸ primeComplementCore (G := H₁) 3)) := by
    rw [sup_comm, htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, ν, hν, hkν⟩ := Subgroup.mem_sup_of_normal_left.mp hnt
  have hkY : k ∈ Y₁.map π₁ := hY₁ ▸ hk
  obtain ⟨y, hyY, rfl⟩ := hkY
  obtain ⟨m, hm, rfl⟩ := hN₁ hν
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have hyz : (y : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hyY.1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc'
  have h1 : π₁ ((y * m)⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hkν]; group
  have hoM : (((y * m)⁻¹ * ⟨n, hn⟩ : H₁) : G) ∈ M :=
    hext₁.toD1Escape.primeCore_le ((mk'_primeComplementCore_eq_one_iff 3 _).mp h1)
  refine ⟨(y : G), ⟨hCz hyz, y.2⟩, (m : G) * (((y * m)⁻¹ * ⟨n, hn⟩ : H₁) : G),
    ⟨H₁.mul_mem m.2 (((y * m)⁻¹ * ⟨n, hn⟩ : H₁)).2, M.mul_mem hmM hoM⟩, ?_⟩
  simp [mul_assoc]

end CFSG.AGLEmbedding
