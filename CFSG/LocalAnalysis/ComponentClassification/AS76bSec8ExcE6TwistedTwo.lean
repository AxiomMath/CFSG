module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedResidual
public import CFSG.LieType.Chevalley.E6EvenInvolutionUnitary

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.SeitzReduction
open CFSG.ComponentClassification.RankTwoExceptional.Exc

variable {K : Type} [Field K]

theorem centralizer_thetaRankOneGroup_twisted
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    graphFixedRootGroup TwistTag.E6 K σ ⊓
        centralizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) =
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  obtain ⟨-, ⟨-, hLC, -, -, hcomm, huniq, -⟩⟩ :=
    even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  refine le_antisymm (fun g hg => ?_) fun l hl =>
    mem_inf.2 ⟨hLC hl, mem_centralizer_iff.2 fun y hy => hcomm y hy l hl⟩
  obtain ⟨hgG, hgC⟩ := mem_inf.1 hg
  obtain ⟨⟨x, l⟩, ⟨hx, hl, hgxl⟩, -⟩ := huniq g ⟨centralizer_le_normalizer _ hgC, hgG⟩
  dsimp only at hx hl hgxl
  subst hgxl
  have hlC : l ∈ centralizer (thetaRankOneGroup (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) := mem_centralizer_iff.2 fun y hy => hcomm y hy l hl
  have hxC : x ∈ centralizer (thetaRankOneGroup (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) := by
    have e : x = (x * l) * l⁻¹ := by group
    rw [e]
    exact mul_mem hgC (inv_mem hlC)
  have hx1 : x = 1 := by
    have h0 := E6GraphRootSL2.thetaRankOneGroup_inf_eq_bot h2 (algebraMap k K)
      (C := centralizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)))
      le_rfl
    have h1 : x ∈ thetaRankOneGroup (algebraMap k K) ⊓ centralizer
        (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) := mem_inf.2 ⟨hx, hxC⟩
    rw [h0] at h1
    exact mem_bot.1 h1
  rw [hx1, one_mul]
  exact hl

theorem eq_one_or_eq_of_mem_zx_twisted
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {j : graphFixedRootGroup TwistTag.E6 K σ}
    (hjL : (j : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA)
    (hdc : ∀ w ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
      (∀ c ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        c * (j : ModGL TwistTag.E6.tag K) = j * c → w * c = c * w) → w = 1 ∨ w = j)
    {w : graphFixedRootGroup TwistTag.E6 K σ} (hw : w ∈ zx j) : w = 1 ∨ w = j := by
  obtain ⟨-, hwz, -⟩ := hw
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨-, ⟨hXC, -, -, -, hcomm, -, -⟩⟩ :=
    even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  have hF := centralizer_thetaRankOneGroup_twisted hf hk hK hσ
  have hjL0 : (j : ModGL TwistTag.E6.tag K) ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ :=
    mem_inf.2 ⟨hjL, j.2⟩
  have hwL : (w : ModGL TwistTag.E6.tag K) ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
    rw [← hF]
    refine mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyc : (⟨y, hXC hy⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈ cent j :=
      mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm y hy _ hjL0))
    exact (congrArg Subtype.val (hwz _ hyc)).symm
  rcases hdc _ hwL (fun c hc hcj => by
    have hcc : (⟨c, (mem_inf.1 hc).2⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈ cent j :=
      mem_centralizer_singleton_iff.2 (Subtype.ext hcj)
    exact congrArg Subtype.val (hwz _ hcc)) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem twFrameProd_eq_realize
    (h2 : (2 : K) = 0) :
    twFrameProd (K := K) frT = realize h2 E6EvenInvolution.slT1 ∧
      twFrameProd (K := K) frU = realize h2 E6EvenInvolution.sl2 ∧
      twFrameProd (K := K) frV = realize h2 E6EvenInvolution.sl3 := by
  refine ⟨?_, (E6EvenInvolution.realize_sl2 h2).symm, (E6EvenInvolution.realize_sl3 h2).symm⟩
  rw [E6EvenInvolution.realize_slT1 h2]
  simp only [twFrameProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem card_zx_twReps_two
    [Finite K] [CharP K 2] (hK : Nat.card K = 4) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2) (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) :
    ∀ x ∈ twReps σ.toRingHom hσσ, Nat.card (zx x) < 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ 1 := fun c => by rw [pow_one]; exact hσ c
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq le_rfl hK'
  obtain ⟨t₀, ht₀⟩ := exists_add_sigma_eq_one le_rfl hK' hσ' hσσ
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let _ : Algebra (ZMod 2) K := ι.toAlgebra
  have hk : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hL := (subsystemGroup_inf_eq_map_realize hK' hσ' h2).1
  obtain ⟨eT, eU, eV⟩ := twFrameProd_eq_realize (K := K) h2
  have key : ∀ {R : Matrix.SpecialLinearGroup (Fin 6) K} {x : graphFixedRootGroup TwistTag.E6 K
      σ.toRingHom}, (x : ModGL TwistTag.E6.tag K) = realize h2 R →
      (∀ {w}, w ∈ (E6GraphLevi.unitarySL σ.toRingHom).map (realize h2) →
        (∀ c ∈ (E6GraphLevi.unitarySL σ.toRingHom).map (realize h2),
          c * realize h2 R = realize h2 R * c → w * c = c * w) → w = 1 ∨ w = realize h2 R) →
      Nat.card (zx x) < 4 := by
    intro R x hx hdc
    have hjL : (x : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA := by
      rw [hx]
      exact E6EvenInvolution.realize_mem h2 R
    have : Nat.card (zx x) ≤ 2 := E6Sec8.card_le_two_of_forall fun w hw =>
      eq_one_or_eq_of_mem_zx_twisted (k := ZMod 2) le_rfl hk hK' hσ' hjL (fun w hw hc => by
        rw [hL] at hw
        rw [hx] at hc ⊢
        exact hdc hw (fun c hc' hcR => hc c (by rw [hL]; exact hc') hcR)) hw
    omega
  intro x hx
  simp only [twReps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact key eT fun hw hc => E6EvenInvolution.eq_one_or_eq_slT1 h2 hσ hσσ ht₀ hw hc
  · exact key eU fun hw hc => E6EvenInvolution.eq_one_or_eq_sl2 h2 hσ hσσ ht₀ hw hc
  · exact key eV fun hw hc => E6EvenInvolution.eq_one_or_eq_sl3 h2 hσ hσσ ht₀ hw hc

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
