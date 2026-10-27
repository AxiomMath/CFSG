module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedLevi
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedCent

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphRootSL2 CFSG.SeitzReduction
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] {k : Type} [Field k] [Algebra k K]

theorem WSL_conj_uSL (c : k) : WSL * uSL c * WSL⁻¹ = vSL (-c) := by
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_WSL, coe_uSL, coe_vSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_conj_vSL (c : k) : WSL * vSL c * WSL⁻¹ = uSL (-c) := by
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_WSL, coe_uSL, coe_vSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_inv_conj_vSL (c : k) : WSL⁻¹ * vSL c * WSL = uSL (-c) := by
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_WSL, coe_uSL, coe_vSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

section Theta

omit [Algebra k K]

theorem psi_uSL
    (h2 : (2 : K) = 0) (ι : k →+* K) (c : k) :
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) (uSL c) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (ι c) := by
  rw [MonoidHom.comp_apply, E6GraphLevi.map_uSL, thetaSL2_uSL h2]

theorem psi_vSL
    (h2 : (2 : K) = 0) (ι : k →+* K) (c : k) :
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) (vSL c) =
      pinnedX TwistTag.E6.tag K (-e6HighestRoot) (ι c) := by
  rw [MonoidHom.comp_apply, E6GraphLevi.map_vSL, thetaSL2_vSL h2]

theorem psi_HSL
    (ι : k →+* K) (t : kˣ) :
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) (HSL t) =
      thetaTorusHom K (Units.map ι.toMonoidHom t) := by
  rw [thetaSL2_comp_map_HSL, thetaTorusHom_apply]

theorem psi_WSL
    (ι : k →+* K) :
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) WSL = thetaSL2 K WSL := by
  rw [MonoidHom.comp_apply, CFSG.LieType.Chevalley.map_WSL]

theorem nTheta_mem_twisted
    (h2 : (2 : K) = 0) (ι : k →+* K) :
    thetaSL2 K WSL ∈ thetaRankOneGroup ι := by
  rw [thetaRankOneGroup_eq_range h2, ← psi_WSL ι]
  exact ⟨_, rfl⟩

theorem conj_mem_thetaRootGroup
    (h2 : (2 : K) = 0) (ι : k →+* K) (t : kˣ)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ thetaRootGroup ι) :
    thetaTorusHom K (Units.map ι.toMonoidHom t) * x *
      (thetaTorusHom K (Units.map ι.toMonoidHom t))⁻¹ ∈ thetaRootGroup ι := by
  obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 hx
  refine (mem_thetaRootGroup ι).2 ⟨(t : k) ^ 2 * c, ?_⟩
  rw [← psi_uSL h2, ← psi_uSL h2, ← psi_HSL, ← map_inv, ← map_mul, ← map_mul, HSL_conj_uSL]

theorem conj_mem_thetaNegRootGroup
    (h2 : (2 : K) = 0) (ι : k →+* K) (t : kˣ)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ thetaNegRootGroup ι) :
    thetaTorusHom K (Units.map ι.toMonoidHom t) * x *
      (thetaTorusHom K (Units.map ι.toMonoidHom t))⁻¹ ∈ thetaNegRootGroup ι := by
  obtain ⟨c, rfl⟩ := (mem_thetaNegRootGroup ι).1 hx
  refine (mem_thetaNegRootGroup ι).2 ⟨((t⁻¹ : kˣ) : k) ^ 2 * c, ?_⟩
  rw [← psi_vSL h2, ← psi_vSL h2, ← psi_HSL, ← map_inv, ← map_mul, ← map_mul, HSL_conj_vSL]

theorem nTheta_conj_thetaRootGroup
    (h2 : (2 : K) = 0) (ι : k →+* K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ thetaRootGroup ι) :
    thetaSL2 K WSL * x * (thetaSL2 K WSL)⁻¹ ∈ thetaNegRootGroup ι := by
  obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 hx
  refine (mem_thetaNegRootGroup ι).2 ⟨-c, ?_⟩
  rw [← psi_vSL h2, ← psi_uSL h2, ← psi_WSL ι, ← map_inv, ← map_mul, ← map_mul, WSL_conj_uSL]

theorem nTheta_conj_thetaNegRootGroup
    (h2 : (2 : K) = 0) (ι : k →+* K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ thetaNegRootGroup ι) :
    thetaSL2 K WSL * x * (thetaSL2 K WSL)⁻¹ ∈ thetaRootGroup ι := by
  obtain ⟨c, rfl⟩ := (mem_thetaNegRootGroup ι).1 hx
  refine (mem_thetaRootGroup ι).2 ⟨-c, ?_⟩
  rw [← psi_uSL h2, ← psi_vSL h2, ← psi_WSL ι, ← map_inv, ← map_mul, ← map_mul, WSL_conj_vSL]

theorem nTheta_inv_conj_thetaNegRootGroup
    (h2 : (2 : K) = 0) (ι : k →+* K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ thetaNegRootGroup ι) :
    (thetaSL2 K WSL)⁻¹ * x * thetaSL2 K WSL ∈ thetaRootGroup ι := by
  obtain ⟨c, rfl⟩ := (mem_thetaNegRootGroup ι).1 hx
  refine (mem_thetaRootGroup ι).2 ⟨-c, ?_⟩
  rw [← psi_uSL h2, ← psi_vSL h2, ← psi_WSL ι, ← map_inv, ← map_mul, ← map_mul,
    WSL_inv_conj_vSL]

theorem le_or_le_of_normalized_twisted
    (h2 : (2 : K) = 0) (h2k : (2 : k) = 0) (ι : k →+* K)
    {t : kˣ} (ht : t ≠ 1) {S : Subgroup (ModGL TwistTag.E6.tag K)}
    (hSX : S ≤ thetaRankOneGroup ι) (hS2 : ∀ s ∈ S, s * s = 1)
    (hSH : ∀ s ∈ S, thetaTorusHom K (Units.map ι.toMonoidHom t) * s *
      (thetaTorusHom K (Units.map ι.toMonoidHom t))⁻¹ ∈ S) :
    S ≤ thetaRootGroup ι ∨ S ≤ thetaNegRootGroup ι := by
  have hinj := injective_thetaSL2_comp_map h2 ι
  have hX : ∀ s ∈ S, ∃ Y, (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) Y = s :=
    fun s hs => by
      have h := hSX hs
      rw [thetaRankOneGroup_eq_range h2] at h
      exact h
  have key := E6EvenRootTorus.le_or_le_of_normalized_SL2
    (S := S.comap ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι))) h2k ht
    (fun Y hY => hinj (by rw [map_mul, map_one]; exact hS2 _ hY))
    (fun Y hY => by
      rw [mem_comap, map_mul, map_mul, map_inv, psi_HSL]
      exact hSH _ hY)
  rcases key with h | h
  · left
    intro s hs
    obtain ⟨Y, rfl⟩ := hX s hs
    obtain ⟨b, rfl⟩ := h Y hs
    rw [psi_uSL h2]
    exact (mem_thetaRootGroup ι).2 ⟨b, rfl⟩
  · right
    intro s hs
    obtain ⟨Y, rfl⟩ := hX s hs
    obtain ⟨c, rfl⟩ := h Y hs
    rw [psi_vSL h2]
    exact (mem_thetaNegRootGroup ι).2 ⟨c, rfl⟩

end Theta

theorem map_mem_parabolicRadical_twisted
    [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβ : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
        (β x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K))
    {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K setA) :
    (β x : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K setA := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨-, ⟨-, hNsup, hQnorm, huniq, hLH, -⟩⟩ :=
    even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨-, ⟨hXC, -⟩⟩ := even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  have hRG : thetaRootGroup (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    (le_sup_left : thetaRootGroup (algebraMap k K) ≤
      thetaRootGroup (algebraMap k K) ⊔ thetaNegRootGroup (algebraMap k K)).trans hXC
  have hR : ∀ y ∈ (thetaRootGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ), β y ∈ (thetaRootGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := fun y hy => hβ y hy
  have hN : ∀ γ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∀ y ∈ (thetaRootGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
        γ y ∈ (thetaRootGroup (algebraMap k K)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ)) →
      ∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈
        normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ →
      (γ y : ModGL TwistTag.E6.tag K) ∈
        normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ := by
    intro γ hγ y hy
    refine mem_inf.2 ⟨?_, (γ y).2⟩
    have hy' : y ∈ normalizer (((thetaRootGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hRG]
      exact (mem_inf.1 hy).1
    have h := E6EvenRootTorus.map_mem_normalizer γ hγ hy'
    rw [← Subgroup.subgroupOf_normalizer_eq hRG] at h
    exact h
  have hQ2 : IsPGroup 2 (parabolicRadical TwistTag.E6.tag K setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ : Subgroup (ModGL TwistTag.E6.tag K)) :=
    (isPGroup_posUnipotent (K := K) 2 TwistTag.E6.tag).to_le
      (inf_le_left.trans (parabolicRadical_le_posUnipotent setA))
  have hH : Odd (Nat.card (thetaTorus (algebraMap k K))) := by
    rw [card_thetaTorus_twisted h2, Nat.card_units, hk]
    exact E6EvenRootTorus.odd_two_pow_sub_one hf
  have hQN : parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
      normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ :=
    le_sup_left.trans hNsup.le
  have h := E6EvenRootTorus.map_mem_of_factor inf_le_right hNsup
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 hQnorm) huniq hLH hQ2 hH
    (fun S hSL hS2 hSn => eq_bot_of_le_subsystemGroup_inf (k := k) hf hk hK hσ S hSL hS2 hSn)
    β (hN β hR) (hN β.symm fun y hy => E6EvenRootTorus.symm_mem β hR hy) (x := x)
    (mem_inf.2 ⟨hx, x.2⟩)
  exact (mem_inf.1 h).1

theorem map_mem_graphFixedPosUnipotent
    [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y)
    (hR : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
        (α x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K))
    {u : graphFixedRootGroup TwistTag.E6 K σ}
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ) :
    (α u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, huniqC, -, hUR, -⟩⟩ :=
    even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨⟨q, l⟩, ⟨hq, hl, he⟩, -⟩ := huniqC u (mem_inf.2 ⟨hUR hu, u.2⟩)
  dsimp only at hq hl he
  have hqU : q ∈ graphFixedPosUnipotent TwistTag.E6 K σ :=
    mem_inf.2 ⟨parabolicRadical_le_posUnipotent setA (mem_inf.1 hq).1,
      graphFixedRootGroup_le _ _ _ (mem_inf.1 hq).2⟩
  obtain ⟨q', hq'⟩ : ∃ q' : graphFixedRootGroup TwistTag.E6 K σ,
      (q' : ModGL TwistTag.E6.tag K) = q := ⟨⟨q, (mem_inf.1 hq).2⟩, rfl⟩
  obtain ⟨l', hl'⟩ : ∃ l' : graphFixedRootGroup TwistTag.E6 K σ,
      (l' : ModGL TwistTag.E6.tag K) = l := ⟨⟨l, (mem_inf.1 hl).2⟩, rfl⟩
  have hul : u = q' * l' := Subtype.ext (by rw [he, Subgroup.coe_mul, hq', hl'])
  have hα := map_mem_parabolicRadical_twisted hf hk hK hσ α hR (x := q')
    (by rw [hq']; exact (mem_inf.1 hq).1)
  rw [hul, map_mul, hL l' (by rw [hl']; exact (mem_inf.1 hl).1), Subgroup.coe_mul]
  refine mul_mem (mem_inf.2 ⟨parabolicRadical_le_posUnipotent setA hα,
    graphFixedRootGroup_le _ _ _ (α q').2⟩) ?_
  have e : (l' : ModGL TwistTag.E6.tag K) = q⁻¹ * u := by rw [hl', he]; group
  rw [e]
  exact mul_mem (inv_mem hqU) hu

theorem neg_eleven_le_height
    {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) : -11 ≤ height γ := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  clear hγ
  revert n
  decide +kernel

omit [Algebra k K] in
theorem commute_negUnipotent
    [CharP K 2] {v : ModGL TwistTag.E6.tag K}
    (hv : v ∈ negUnipotent TwistTag.E6.tag K) (d : K) :
    pinnedX TwistTag.E6.tag K (-e6HighestRoot) d * v =
      v * pinnedX TwistTag.E6.tag K (-e6HighestRoot) d := by
  have hθ' : IsRoot TwistTag.E6.tag (-e6HighestRoot) := IsRoot.neg isRoot_e6HighestRoot
  have hle : negUnipotent TwistTag.E6.tag K ≤ centralizer
      ({pinnedX TwistTag.E6.tag K (-e6HighestRoot) d} : Set (ModGL TwistTag.E6.tag K)) := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ rfl
    by_cases hγθ : γ = -e6HighestRoot
    · subst hγθ
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · have hh : height (γ + -e6HighestRoot) < -11 := by
        rw [height_add, height_neg, height_e6HighestRoot]
        linarith [hγ.2]
      exact (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hγ.1 hθ'
        (fun hr => absurd (neg_eleven_le_height hr) (by omega))
        (fun h0 => by rw [h0] at hh; simp [height] at hh) c d).eq.symm
  exact mem_centralizer_iff.1 (hle hv) _ rfl

theorem map_mem_graphFixedNegUnipotent
    [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y)
    (hR' : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K) →
        (α x : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K))
    {v : graphFixedRootGroup TwistTag.E6 K σ}
    (hv : (v : ModGL TwistTag.E6.tag K) ∈ graphFixedNegUnipotent TwistTag.E6 K σ) :
    (α v : ModGL TwistTag.E6.tag K) ∈ graphFixedNegUnipotent TwistTag.E6 K σ := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, huniqC, -, -, -⟩⟩ :=
    even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨-, ⟨hXC, -, -, -, hcomm, -, -⟩⟩ :=
    even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  obtain ⟨n, hn⟩ : ∃ n : graphFixedRootGroup TwistTag.E6 K σ,
      (n : ModGL TwistTag.E6.tag K) = thetaSL2 K WSL :=
    ⟨⟨_, hXC (nTheta_mem_twisted h2 (algebraMap k K))⟩, rfl⟩
  have hnX : (n : ModGL TwistTag.E6.tag K) ∈ thetaRankOneGroup (algebraMap k K) := by
    rw [hn]
    exact nTheta_mem_twisted h2 _
  have hw : ((n⁻¹ * v * n : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
      centralizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun r hr => ?_, (n⁻¹ * v * n).2⟩
    obtain ⟨c, hc⟩ := (mem_thetaNegRootGroup (algebraMap k K)).1
      (nTheta_conj_thetaRootGroup h2 (algebraMap k K) hr)
    have h := commute_negUnipotent (mem_inf.1 hv).1 (algebraMap k K c)
    rw [hc, ← hn] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc r * ((n : ModGL TwistTag.E6.tag K)⁻¹ * v * n) =
        (n : ModGL TwistTag.E6.tag K)⁻¹ * ((n * r * (n : ModGL TwistTag.E6.tag K)⁻¹) * v) *
          n := by group
      _ = (n : ModGL TwistTag.E6.tag K)⁻¹ * (v * (n * r * (n : ModGL TwistTag.E6.tag K)⁻¹)) *
          n := by rw [h]
      _ = _ := by group
  obtain ⟨⟨q, l⟩, ⟨hq, hl, he⟩, -⟩ := huniqC _ hw
  dsimp only at hq hl he
  obtain ⟨q', hq'⟩ : ∃ q' : graphFixedRootGroup TwistTag.E6 K σ,
      (q' : ModGL TwistTag.E6.tag K) = q := ⟨⟨q, (mem_inf.1 hq).2⟩, rfl⟩
  obtain ⟨l', hl'⟩ : ∃ l' : graphFixedRootGroup TwistTag.E6 K σ,
      (l' : ModGL TwistTag.E6.tag K) = l := ⟨⟨l, (mem_inf.1 hl).2⟩, rfl⟩
  have hnl : n * l' = l' * n := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hl']
    exact hcomm _ hnX _ hl)
  have hv' : v = (n * q' * n⁻¹) * l' := by
    have e : n⁻¹ * v * n = q' * l' := Subtype.ext (by rw [he, Subgroup.coe_mul, hq', hl'])
    calc v = n * (n⁻¹ * v * n) * n⁻¹ := by group
      _ = n * (q' * l') * n⁻¹ := by rw [e]
      _ = (n * q' * n⁻¹) * (n * l' * n⁻¹) := by group
      _ = (n * q' * n⁻¹) * l' := by rw [hnl, mul_inv_cancel_right]
  have hnQ : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K setA →
        ((n * y * n⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
          graphFixedNegUnipotent TwistTag.E6 K σ := fun y hy => by
    refine mem_inf.2 ⟨?_, graphFixedRootGroup_le _ _ _ (n * y * n⁻¹).2⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn]
    exact thetaSL2_WSL_conj_mem_negUnipotent h2 hy
  set α' : MulAut (graphFixedRootGroup TwistTag.E6 K σ) :=
    MulAut.conj n⁻¹ * α * MulAut.conj n with hα'
  have hα'y : ∀ y, α' y = n⁻¹ * α (n * y * n⁻¹) * n := fun y => by
    rw [hα', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  have hα'R : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
        (α' x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) := fun x hx => by
    have h1 := hR' (n * x * n⁻¹) (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn]
      exact nTheta_conj_thetaRootGroup h2 _ hx)
    rw [hα'y]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h1 ⊢
    exact nTheta_inv_conj_thetaNegRootGroup h2 _ h1
  have hq'' := map_mem_parabolicRadical_twisted hf hk hK hσ α' hα'R (x := q')
    (by rw [hq']; exact (mem_inf.1 hq).1)
  have e : α (n * q' * n⁻¹) = n * α' q' * n⁻¹ := by rw [hα'y]; group
  rw [hv', map_mul, hL l' (by rw [hl']; exact (mem_inf.1 hl).1), e, Subgroup.coe_mul]
  refine mul_mem (hnQ _ hq'') ?_
  have e' : (l' : ModGL TwistTag.E6.tag K) =
      ((n * q' * n⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K)⁻¹ * v := by
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, hv']
    group
  rw [e']
  exact mul_mem (inv_mem (hnQ _ (by rw [hq']; exact (mem_inf.1 hq).1))) hv

abbrev a₁₆ : Fin TwistTag.E6.foldedTag.rank := (0 : Fin 4)

omit [Algebra k K] in
theorem fixedOrbitX_zero_mem
    (σ : K →+* K) (c : orbitField TwistTag.E6 K σ a₁₆) :
    ((fixedOrbitX TwistTag.E6 K σ a₁₆ c : graphFixedRootGroup TwistTag.E6 K σ) :
      ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA := by
  change ((orbitX TwistTag.E6 K σ a₁₆ c : adjointGroup TwistTag.E6.tag K) :
    ModGL TwistTag.E6.tag K) ∈ _
  rw [coe_orbitX]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
  refine subset_closure ⟨_, ?_, _, Or.inl rfl⟩
  have h := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a₁₆) m
  generalize (TwistTag.E6.perm ^ m) (TwistTag.E6.orbitMin a₁₆) = i at h
  change i ≠ e6Idx 1
  revert i
  decide

omit [Algebra k K] in
theorem eq_one_of_normalActor_fix
    [Finite K] {σ : K ≃+* K}
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (δ : K ≃+* K)
    (h : ∀ c, normalActor σ u δ (fixedOrbitX TwistTag.E6 K σ.toRingHom a₁₆ c) =
      fixedOrbitX TwistTag.E6 K σ.toRingHom a₁₆ c) : δ = 1 := by
  have hc : ∀ c, ((u a₁₆ : orbitField TwistTag.E6 K σ.toRingHom a₁₆) *
      orbitFieldRestrict TwistTag.E6 σ δ a₁₆ c : orbitField TwistTag.E6 K σ.toRingHom a₁₆) = c :=
    fun c => by
      have e := h c
      rw [normalActor_fixedOrbitX] at e
      have e' : ((fixedOrbitX TwistTag.E6 K σ.toRingHom a₁₆ ((u a₁₆ : orbitField TwistTag.E6 K
          σ.toRingHom a₁₆) * orbitFieldRestrict TwistTag.E6 σ δ a₁₆ c) :
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
          ((fixedOrbitX TwistTag.E6 K σ.toRingHom a₁₆ c :
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) :=
        congrArg Subtype.val e
      exact orbitX_injective σ.toRingHom a₁₆ (Subtype.ext e')
  have hu : (u a₁₆ : orbitField TwistTag.E6 K σ.toRingHom a₁₆) = 1 := by
    have e := hc 1
    rwa [map_one, mul_one] at e
  have hcard : (TwistTag.E6.orbit a₁₆).card = 2 := by decide
  have hmem : ∀ x : K, x ∈ orbitField TwistTag.E6 K σ.toRingHom a₁₆ := fun x => by
    rw [mem_orbitField, hcard, pow_two]
    exact hσσ x
  refine RingEquiv.ext fun x => ?_
  have e := congrArg Subtype.val (hc ⟨x, hmem x⟩)
  rw [hu, one_mul, coe_orbitFieldRestrict] at e
  exact e

omit [Algebra k K] in
theorem compatDiagAutHom_pow_card
    [Finite K] (σ : K →+* K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ) :
    compatDiagAutHom TwistTag.E6 K σ u ^ Nat.card Kˣ = 1 := by
  rw [← map_pow]
  convert map_one (compatDiagAutHom TwistTag.E6 K σ)
  funext a
  have hinj : Function.Injective (Units.map (orbitField TwistTag.E6 K σ a).subtype.toMonoidHom) :=
    fun x y hxy => Units.ext (Subtype.ext (by simpa using congrArg Units.val hxy))
  refine hinj ?_
  rw [Pi.pow_apply, map_pow, pow_card_eq_one', Pi.one_apply, map_one]

omit [Algebra k K] in
theorem compatDiagAutHom_fix_thetaTorusHom
    (σ : K →+* K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ) (s : Kˣ)
    {h : graphFixedRootGroup TwistTag.E6 K σ}
    (hh : (h : ModGL TwistTag.E6.tag K) = thetaTorusHom K s) :
    compatDiagAutHom TwistTag.E6 K σ u h = h := by
  apply Subtype.ext
  rw [coe_compatDiagAutHom, hh]
  change rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u) *
      rootDiagUnit TwistTag.E6.tag (Pi.mulSingle (e6Idx 1) s) *
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u))⁻¹ =
    rootDiagUnit TwistTag.E6.tag (Pi.mulSingle (e6Idx 1) s)
  rw [← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]

theorem exists_eq_compatDiagAutHom
    [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y)
    (hR : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
        (α x : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K))
    (hR' : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K) →
        (α x : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K)) :
    ∃ u, α = compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have := Fintype.ofFinite K
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hstab : α ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom :=
    ⟨E6EvenRootTorus.map_eq_of_le α fun y hy =>
      map_mem_graphFixedPosUnipotent hf hk hK hσ α hL hR hy,
    E6EvenRootTorus.map_eq_of_le α fun y hy =>
      map_mem_graphFixedNegUnipotent hf hk hK hσ α hL hR' hy⟩
  obtain ⟨u, δ, rfl⟩ := exists_normalActor_eq_E6 Nat.prime_two hf hK σ hσ hstab
  have hδ : δ = 1 := eq_one_of_normalActor_fix hσσ u δ fun c =>
    hL _ (fixedOrbitX_zero_mem σ.toRingHom c)
  refine ⟨u, ?_⟩
  rw [hδ, normalActor, fieldActor_one, mul_one]

theorem map_mem_thetaRankOneGroup_twisted
    [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y)
    {y : graphFixedRootGroup TwistTag.E6 K σ}
    (hy : (y : ModGL TwistTag.E6.tag K) ∈ thetaRankOneGroup (algebraMap k K)) :
    (α y : ModGL TwistTag.E6.tag K) ∈ thetaRankOneGroup (algebraMap k K) := by
  have hF := centralizer_twisted (k := k) hf hk hK hσ
  rw [← hF] at hy ⊢
  obtain ⟨-, hyc⟩ := mem_inf.1 hy
  refine mem_inf.2 ⟨(α y).2, mem_centralizer_iff.2 fun l hl => ?_⟩
  have e : (⟨l, (mem_inf.1 hl).2⟩ : graphFixedRootGroup TwistTag.E6 K σ) * y =
      y * ⟨l, (mem_inf.1 hl).2⟩ := Subtype.ext (mem_centralizer_iff.1 hyc l hl)
  have e' := congrArg α e
  rw [map_mul, map_mul, hL ⟨l, (mem_inf.1 hl).2⟩ (mem_inf.1 hl).1] at e'
  exact congrArg Subtype.val e'

theorem map_le_or_le_twisted
    [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hH : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) → α y = y)
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y)
    {S₀ : Subgroup (ModGL TwistTag.E6.tag K)} (hS₀X : S₀ ≤ thetaRankOneGroup (algebraMap k K))
    (hS₀2 : ∀ s ∈ S₀, s * s = 1)
    (hS₀H : ∀ (t : kˣ), ∀ s ∈ S₀, thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) * s *
      (thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t))⁻¹ ∈ S₀) :
    (∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ S₀ →
        (α y : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K)) ∨
      (∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ S₀ →
        (α y : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K)) := by
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2k : (2 : k) = 0 := two_eq_zero_of_card hf1 hk
  obtain ⟨-, ⟨hXC, -⟩⟩ := even_E6_graph_root_SL2_normalizer f hf1 k K hk hK σ hσ
  obtain ⟨t, ht⟩ := E6EvenRootTorus.exists_units_ne_one hf hk
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (ModGL TwistTag.E6.tag K),
      S = (S₀.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        ((graphFixedRootGroup TwistTag.E6 K σ).subtype.comp α.toMonoidHom) := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ S ↔ ∃ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ S₀ ∧ (α y : ModGL TwistTag.E6.tag K) = z := fun z => by
    rw [hS]
    exact Iff.rfl
  have hhG : thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
    hXC (thetaTorus_le_thetaRankOneGroup h2 _ ⟨t, rfl⟩)
  have hle := le_or_le_of_normalized_twisted h2 h2k (algebraMap k K) ht (S := S)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      exact map_mem_thetaRankOneGroup_twisted hf hk hK hσ α hL (hS₀X hy))
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      have hyy : y * y = 1 := Subtype.ext (by rw [Subgroup.coe_mul]; exact hS₀2 _ hy)
      rw [← Subgroup.coe_mul, ← map_mul, hyy, map_one]
      rfl)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      have hαh : α ⟨_, hhG⟩ = ⟨_, hhG⟩ := hH ⟨_, hhG⟩ ⟨t, rfl⟩
      refine (hmem _).2 ⟨⟨_, hhG⟩ * y * (⟨_, hhG⟩ : graphFixedRootGroup TwistTag.E6 K σ)⁻¹,
        hS₀H t _ hy, ?_⟩
      rw [map_mul, map_mul, map_inv, hαh]
      rfl)
  rcases hle with h | h
  · exact Or.inl fun y hy => h ((hmem _).2 ⟨y, hy, rfl⟩)
  · exact Or.inr fun y hy => h ((hmem _).2 ⟨y, hy, rfl⟩)

omit [Algebra k K] in
theorem thetaRootGroup_comm
    (ι : k →+* K) {a b : ModGL TwistTag.E6.tag K}
    (ha : a ∈ thetaRootGroup ι) (hb : b ∈ thetaRootGroup ι) : a * b = b * a := by
  obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 ha
  obtain ⟨d, rfl⟩ := (mem_thetaRootGroup ι).1 hb
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

omit [Algebra k K] in
theorem thetaNegRootGroup_comm
    (ι : k →+* K) {a b : ModGL TwistTag.E6.tag K}
    (ha : a ∈ thetaNegRootGroup ι) (hb : b ∈ thetaNegRootGroup ι) : a * b = b * a := by
  obtain ⟨c, rfl⟩ := (mem_thetaNegRootGroup ι).1 ha
  obtain ⟨d, rfl⟩ := (mem_thetaNegRootGroup ι).1 hb
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

theorem not_map_le_twisted
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) {T : Subgroup (ModGL TwistTag.E6.tag K)}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (h₁ : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
        (α y : ModGL TwistTag.E6.tag K) ∈ T)
    (h₂ : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K) →
        (α y : ModGL TwistTag.E6.tag K) ∈ T) : False := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, ⟨hXC, -⟩⟩ := even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  have ha : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ thetaRootGroup (algebraMap k K) :=
    (mem_thetaRootGroup _).2 ⟨1, by rw [map_one]⟩
  have hb : pinnedX TwistTag.E6.tag K (-e6HighestRoot) 1 ∈ thetaNegRootGroup (algebraMap k K) :=
    (mem_thetaNegRootGroup _).2 ⟨1, by rw [map_one]⟩
  set a : graphFixedRootGroup TwistTag.E6 K σ := ⟨_, hXC (Subgroup.mem_sup_left ha)⟩
  set b : graphFixedRootGroup TwistTag.E6 K σ := ⟨_, hXC (Subgroup.mem_sup_right hb)⟩
  have hcomm : α (a * b) = α (b * a) := by
    rw [map_mul, map_mul]
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hT _ (h₁ a ha) _ (h₂ b hb))
  have h := congrArg Subtype.val (α.injective hcomm)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact E6EvenRootTorus.pinnedX_theta_mul_ne h2 h

theorem eq_one_of_fix_twisted
    [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : ∃ n : ℕ, α ^ 2 ^ n = 1)
    (hH : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (y : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) → α y = y)
    (hL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → α y = y) :
    α = 1 := by
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  obtain ⟨-, ⟨hXC, -, -, -, hcommX, -, -⟩⟩ :=
    even_E6_graph_root_SL2_normalizer f hf1 k K hk hK σ.toRingHom hσ'
  have hRX : thetaRootGroup (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K) := le_sup_left
  have hVX : thetaNegRootGroup (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K) :=
    le_sup_right
  have hR2 : ∀ s ∈ thetaRootGroup (algebraMap k K), s * s = 1 := fun s hs => by
    obtain ⟨c, rfl⟩ := (mem_thetaRootGroup _).1 hs
    exact E6EvenRootTorus.pinnedX_mul_self h2 _ _
  have hV2 : ∀ s ∈ thetaNegRootGroup (algebraMap k K), s * s = 1 := fun s hs => by
    obtain ⟨c, rfl⟩ := (mem_thetaNegRootGroup _).1 hs
    exact E6EvenRootTorus.pinnedX_mul_self h2 _ _
  rcases map_le_or_le_twisted hf hk hK hσ' α hH hL hRX hR2
      (fun t s hs => conj_mem_thetaRootGroup h2 _ t hs) with hU | hU <;>
    rcases map_le_or_le_twisted hf hk hK hσ' α hH hL hVX hV2
      (fun t s hs => conj_mem_thetaNegRootGroup h2 _ t hs) with hV | hV
  · exact (not_map_le_twisted hf1 hk hK hσ' α (fun a ha b hb => thetaRootGroup_comm _ ha hb) hU
      hV).elim
  ·
    obtain ⟨u, rfl⟩ := exists_eq_compatDiagAutHom hf1 hk hK hσ _ hL hU hV
    obtain ⟨n, hn⟩ := hα
    have h1 := compatDiagAutHom_pow_card σ.toRingHom u
    have hodd : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units, hK, ← pow_mul]
      exact E6EvenRootTorus.odd_two_pow_sub_one (by omega)
    have hcop : Nat.Coprime (2 ^ n) (Nat.card Kˣ) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd)).pow_left n
    have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h1)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
    exact orderOf_eq_one_iff.1 hdvd
  ·
    exfalso
    obtain ⟨n, hn⟩ : ∃ n : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (n : ModGL TwistTag.E6.tag K) = thetaSL2 K WSL :=
      ⟨⟨_, hXC (nTheta_mem_twisted h2 _)⟩, rfl⟩
    have hnX : (n : ModGL TwistTag.E6.tag K) ∈ thetaRankOneGroup (algebraMap k K) := by
      rw [hn]
      exact nTheta_mem_twisted h2 _
    set β := MulAut.conj n * α with hβ
    have hβy : ∀ y, β y = n * α y * n⁻¹ := fun y => by
      rw [hβ, MulAut.mul_apply, MulAut.conj_apply]
    have hβL : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA → β y = y :=
      fun y hy => by
        rw [hβy, hL y hy]
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          hcommX _ hnX _ (mem_inf.2 ⟨hy, y.2⟩), mul_inv_cancel_right]
    have hβR : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (y : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) →
          (β y : ModGL TwistTag.E6.tag K) ∈ thetaRootGroup (algebraMap k K) := fun y hy => by
      rw [hβy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn]
      exact nTheta_conj_thetaNegRootGroup h2 _ (hU y hy)
    have hβV : ∀ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (y : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K) →
          (β y : ModGL TwistTag.E6.tag K) ∈ thetaNegRootGroup (algebraMap k K) := fun y hy => by
      rw [hβy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn]
      exact nTheta_conj_thetaRootGroup h2 _ (hV y hy)
    obtain ⟨u, hu⟩ := exists_eq_compatDiagAutHom hf1 hk hK hσ β hβL hβR hβV
    obtain ⟨t, ht⟩ := E6EvenRootTorus.exists_units_ne_one hf hk
    obtain ⟨h, hh⟩ : ∃ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (h : ModGL TwistTag.E6.tag K) =
          thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) :=
      ⟨⟨_, hXC (thetaTorus_le_thetaRankOneGroup h2 _ ⟨t, rfl⟩)⟩, rfl⟩
    have e1 : ((β h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
        ModGL TwistTag.E6.tag K) =
          (thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t))⁻¹ := by
      rw [hβy, hH h (by rw [hh]; exact ⟨t, rfl⟩), Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hn, hh]
      exact E6EvenRootTorus.nTheta_conj_thetaTorusHom _
    have e2 : β h = h := by
      rw [hu]
      exact compatDiagAutHom_fix_thetaTorusHom σ.toRingHom u _ hh
    have e4 : thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) =
        (thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t))⁻¹ :=
      calc thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) =
          (h : ModGL TwistTag.E6.tag K) := hh.symm
        _ = ((β h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) := by
          rw [e2]
        _ = _ := e1
    have e3 : thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t ^ 2) =
        thetaTorusHom K 1 := by
      rw [map_pow, pow_two, map_one]
      nth_rw 2 [e4]
      exact mul_inv_cancel _
    have hs := thetaTorusHom_injective h2 e3
    have hs1 : Units.map (algebraMap k K).toMonoidHom t = 1 := by
      by_contra hne
      exact RootTorus.sq_ne_one_of_two h2 hne hs
    exact ht (Units.ext ((algebraMap k K).injective (by simpa using congrArg Units.val hs1)))
  · exact (not_map_le_twisted hf1 hk hK hσ' α (fun a ha b hb => thetaNegRootGroup_comm _ ha hb)
      hU hV).elim

theorem autFix_twisted
    [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    AutFix
      ((thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      ((subsystemGroup TwistTag.E6.tag K setA ⊓
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
  fun α hα hQ hL => eq_one_of_fix_twisted hf hk hK hσ α hα (fun y hy => hQ y (mem_subgroupOf.2 hy))
    fun y hy => hL y (mem_subgroupOf.2 (mem_inf.2 ⟨hy, y.2⟩))

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
