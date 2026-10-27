module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ17
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ16

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Torus

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem J2_torus_comm (u : Fin Tag.D4.rank → Kˣ) (hu : u 2 = 1) {c : ModGL Tag.D4 K}
    (hc : c ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank))) :
    ∃ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      rootDiagUnit Tag.D4 u * c * (rootDiagUnit Tag.D4 u)⁻¹ = q * c := by
  obtain ⟨hQP, -, -, hMP, hQM, -, hfact, -⟩ :=
    parabolic_root_radical_Levi_factors Tag.D4 K ({2} : Set (Fin Tag.D4.rank))
  obtain ⟨⟨q₀, m₀⟩, ⟨hq₀, hm₀, hcm⟩, -⟩ := hfact c hc
  simp only at hq₀ hm₀ hcm
  subst hcm
  obtain ⟨b₀, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm₀
  have hl' : l ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl
  obtain ⟨A, rfl⟩ := hl'
  have h1 : rootDiagUnit Tag.D4 u * ρ 2 A * (rootDiagUnit Tag.D4 u)⁻¹ = ρ 2 A := by
    rw [torus_conj_rho u 2 A, hu, dconj_one_apply]
  have hcomm : rootDiagUnit Tag.D4 u * (rootDiagUnit Tag.D4 b₀ * ρ 2 A) *
      (rootDiagUnit Tag.D4 u)⁻¹ = rootDiagUnit Tag.D4 b₀ * ρ 2 A := by
    calc rootDiagUnit Tag.D4 u * (rootDiagUnit Tag.D4 b₀ * ρ 2 A) * (rootDiagUnit Tag.D4 u)⁻¹
        = (rootDiagUnit Tag.D4 u * rootDiagUnit Tag.D4 b₀) * ρ 2 A * (rootDiagUnit Tag.D4 u)⁻¹ := by
          group
      _ = (rootDiagUnit Tag.D4 b₀ * rootDiagUnit Tag.D4 u) * ρ 2 A * (rootDiagUnit Tag.D4 u)⁻¹ := by
          rw [rootDiagUnit_comm u b₀]
      _ = rootDiagUnit Tag.D4 b₀ * (rootDiagUnit Tag.D4 u * ρ 2 A * (rootDiagUnit Tag.D4 u)⁻¹) := by
          group
      _ = rootDiagUnit Tag.D4 b₀ * ρ 2 A := by rw [h1]
  refine ⟨(rootDiagUnit Tag.D4 u * q₀ * (rootDiagUnit Tag.D4 u)⁻¹) * q₀⁻¹,
    mul_mem (rootDiagUnit_conj_radical u hq₀) (inv_mem hq₀), ?_⟩
  calc rootDiagUnit Tag.D4 u * (q₀ * (rootDiagUnit Tag.D4 b₀ * ρ 2 A)) * (rootDiagUnit Tag.D4 u)⁻¹
      = (rootDiagUnit Tag.D4 u * q₀ * (rootDiagUnit Tag.D4 u)⁻¹) *
          (rootDiagUnit Tag.D4 u * (rootDiagUnit Tag.D4 b₀ * ρ 2 A) * (rootDiagUnit Tag.D4 u)⁻¹) := by
        group
    _ = (rootDiagUnit Tag.D4 u * q₀ * (rootDiagUnit Tag.D4 u)⁻¹) *
          (rootDiagUnit Tag.D4 b₀ * ρ 2 A) := by rw [hcomm]
    _ = ((rootDiagUnit Tag.D4 u * q₀ * (rootDiagUnit Tag.D4 u)⁻¹) * q₀⁻¹) *
          (q₀ * (rootDiagUnit Tag.D4 b₀ * ρ 2 A)) := by group

theorem J2_torus_comm_gamma (u : Fin Tag.D4.rank → Kˣ) (hu : u 2 = 1) {c : ModGL Tag.D4 K}
    (hc : c ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (a : Fin Tag.D4.rank → Kˣ) :
    ∃ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      rootDiagUnit Tag.D4 u * (c * rootDiagUnit Tag.D4 a) * (rootDiagUnit Tag.D4 u)⁻¹ =
        q * (c * rootDiagUnit Tag.D4 a) := by
  obtain ⟨q, hq, h⟩ := J2_torus_comm u hu hc
  refine ⟨q, hq, ?_⟩
  calc rootDiagUnit Tag.D4 u * (c * rootDiagUnit Tag.D4 a) * (rootDiagUnit Tag.D4 u)⁻¹
      = (rootDiagUnit Tag.D4 u * c * (rootDiagUnit Tag.D4 u)⁻¹) *
          (rootDiagUnit Tag.D4 u * rootDiagUnit Tag.D4 a * (rootDiagUnit Tag.D4 u)⁻¹) := by group
    _ = (q * c) * rootDiagUnit Tag.D4 a := by
        rw [h, rootDiagUnit_comm u a, mul_inv_cancel_right]
    _ = q * (c * rootDiagUnit Tag.D4 a) := by group

end Torus

section LayerComm

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem lconj_comm_conjL {Γ q : ModGL τ K} (hΓ : NormAll J Γ) (hq : q ∈ parabolicRadical τ K J)
    (u : Fin τ.rank → Kˣ)
    (h : rootDiagUnit τ u * Γ * (rootDiagUnit τ u)⁻¹ = q * Γ) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hΓ hd (conjL u hd z) = conjL u hd (lconj hΓ hd z) := by
  have hu : NormAll J (rootDiagUnit τ u) := NormAll.of_rootDiagUnit u
  have hq' : NormAll J q⁻¹ := NormAll.of_radical (inv_mem hq)
  have e : Γ * rootDiagUnit τ u = q⁻¹ * (rootDiagUnit τ u * Γ) := by
    have h1 : rootDiagUnit τ u * Γ = q * Γ * rootDiagUnit τ u := by
      calc rootDiagUnit τ u * Γ = (rootDiagUnit τ u * Γ * (rootDiagUnit τ u)⁻¹) * rootDiagUnit τ u := by
            group
        _ = q * Γ * rootDiagUnit τ u := by rw [h]
    rw [h1]; group
  calc lconj hΓ hd (conjL u hd z) = lconj hΓ hd (lconj hu hd z) := rfl
    _ = lconj (hΓ.mul hu) hd z := (lconj_mul hΓ hu hd z).symm
    _ = lconj (hq'.mul (hu.mul hΓ)) hd z := lconj_congr _ _ e hd z
    _ = lconj hq' hd (lconj (hu.mul hΓ) hd z) := lconj_mul _ _ hd z
    _ = lconj (hu.mul hΓ) hd z := lconj_radical (inv_mem hq) hd _
    _ = lconj hu hd (lconj hΓ hd z) := lconj_mul hu hΓ hd z
    _ = conjL u hd (lconj hΓ hd z) := rfl

end LayerComm

section J2

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem uTorus_char {μ : Kˣ} (i : degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 1) :
    ((rootChar (uTorus μ) i.1 : Kˣ) : K) = μ := by
  have hdeg : i.1 0 + i.1 1 + i.1 3 = 1 :=
    (parabolicDegree_J2 i.1).symm.trans (mem_degLayerRoots.1 i.2).2
  rw [rootChar_uTorus, hdeg, zpow_one]

theorem J2_not_typeN {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K} {Γ₁ Γ₂ c₁ c₂ : ModGL Tag.D4 K}
    {a₁ a₂ : Fin Tag.D4.rank → Kˣ}
    (G : A4Grp ({2} : Set (Fin Tag.D4.rank)) φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hc₂ : c₂ ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁) (hΓ₂ : Γ₂ = c₂ * rootDiagUnit Tag.D4 a₂) :
    Nat.card (fixSp (lconj G.n₁ (le_refl (1 : ℤ)))) ^ 2 ≠
        Nat.card (Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank)))
          (le_refl (1 : ℤ)))) ∧
      Nat.card (fixSp (lconj G.n₂ (le_refl (1 : ℤ)))) ^ 2 ≠
        Nat.card (Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank)))
          (le_refl (1 : ℤ)))) := by
  have hd : (1 : ℤ) ≤ 1 := le_refl 1
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set T₁ := lconj G.n₁ hd with hT₁
  set T₂ := lconj G.n₂ hd with hT₂
  have e12 : Nat.card (fixSp T₂) = Nat.card (fixSp T₁) :=
    card_fixSp_eq_of_conj T₁ T₂ (G.layerB hd) (G.layer_B₁ hd)
  have e23 : Nat.card (fixSp (T₁ * T₂)) = Nat.card (fixSp T₂) :=
    card_fixSp_eq_of_conj T₂ (T₁ * T₂) (G.layerB hd) (G.layer_B₂ hd)
  have hklein := klein_card T₁ T₂ (G.layer_inv₁ hd) (G.layer_inv₂ hd) (G.layer_comm hd)
  have hLcard : Nat.card (Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank))) hd)) =
      Nat.card K ^ 6 := by
    rw [card_layer hd]
    have h6 : (degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 1).ncard = 6 :=
      ncard_layer_J2_one
    rw [h6]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (fixSp T₁ ⊓ fixSp T₂ : Submodule (ZMod 3)
      (Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank))) hd))) =
      Nat.card K ^ k := by
    refine exists_card_pow hd (fun μ => uTorus μ) (fun μ i => uTorus_char i) _ ?_
    intro μ z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    obtain ⟨q₁, hq₁, h₁⟩ := J2_torus_comm_gamma (uTorus μ) (uTorus_two μ) hc₁ a₁
    obtain ⟨q₂, hq₂, h₂⟩ := J2_torus_comm_gamma (uTorus μ) (uTorus_two μ) hc₂ a₂
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSp]
      have := lconj_comm_conjL G.n₁ hq₁ (uTorus μ) (by rw [hΓ₁]; exact h₁) hd z
      rw [hT₁, this, mem_fixSp.1 hz1]
    · rw [mem_fixSp]
      have := lconj_comm_conjL G.n₂ hq₂ (uTorus μ) (by rw [hΓ₂]; exact h₂) hd z
      rw [hT₂, this, mem_fixSp.1 hz2]
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have key : Nat.card (fixSp T₁) ^ 2 ≠
      Nat.card (Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank))) hd)) := by
    intro h
    rw [hLcard] at h
    have hN : Nat.card (fixSp T₁) = Nat.card K ^ 3 := by
      have h' : Nat.card (fixSp T₁) ^ 2 = (Nat.card K ^ 3) ^ 2 := by
        rw [h, ← pow_mul]
      exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h'
    rw [e23, e12, hN, hLcard, hk] at hklein
    have h9 : Nat.card K ^ 9 = Nat.card K ^ (6 + 2 * k) := by
      calc Nat.card K ^ 9 = Nat.card K ^ 3 * Nat.card K ^ 3 * Nat.card K ^ 3 := by ring
        _ = Nat.card K ^ 6 * (Nat.card K ^ k) ^ 2 := hklein
        _ = Nat.card K ^ (6 + 2 * k) := by ring
    have := Nat.pow_right_injective hq2 h9
    omega
  refine ⟨key, fun h => key ?_⟩
  rw [← e12]
  exact h

end J2

end CFSG.LocalAnalysis.GLTheoremA
