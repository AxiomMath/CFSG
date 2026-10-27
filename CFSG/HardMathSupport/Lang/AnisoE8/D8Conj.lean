module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8Arith
public import CFSG.HardMathSupport.Lang.AnisoF4.B4SylowConj
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.CentralLift
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutLift
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8D8

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.CatLeafProof
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.HardMathSupport.Lang.AnisoF4

theorem cast_N8 {q : ℕ} (hq : 1 ≤ q) : (N8 q : ℤ) =
    (q : ℤ) ^ (8 * (8 - 1)) * ((q : ℤ) ^ 8 - 1) *
      ∏ i ∈ Finset.Icc 1 (8 - 1), ((q : ℤ) ^ (2 * i) - 1) := by
  simp only [N8, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq),
    Finset.prod_congr rfl fun i _ => Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

section Main


theorem factorization_N8_le_card_proj {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8) :
    (N8 (Nat.card K)).factorization p ≤
      (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K)))).factorization p := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := h2 ▸ ringChar.charP K
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K)
      (n := 8) (by norm_num)
    rw [← cast_N8 Nat.card_pos] at h
    have h' : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K))) = N8 (Nat.card K) := by
      exact_mod_cast h
    rw [h']
  · have h := CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadPlus_eq_ordD hℓ h2 hK
      (n := 8) (by norm_num)
    rw [h, ← hK]
    set q := Nat.card K with hq
    have h9 := nine_le_of_orderOf_eq_eight hp he
    have hdef : CFSG.Open.ordD 8 q = N8 q / Nat.gcd 4 (q ^ 8 - 1) := rfl
    have hg : Nat.gcd 4 (q ^ 8 - 1) ∣ N8 q := by
      refine (Nat.gcd_dvd_right _ _).trans ?_
      rw [N8]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
    have hgf : (Nat.gcd 4 (q ^ 8 - 1)).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdv
      have := Nat.le_of_dvd (by norm_num) (hdv.trans (Nat.gcd_dvd_left 4 _))
      omega
    rw [hdef, Nat.factorization_div hg, Finsupp.coe_tsub, Pi.sub_apply, hgf, Nat.sub_zero]

theorem card_statedProj_dvd_card_range {K : Type} [Field K] [Finite K]
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K))) :
    Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K))) ∣ Nat.card Ψ.range := by
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, -, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have h1 : Nat.card (spinGroup (quadPlus 8 K)) =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K))) *
        Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [e, hZ] at h
    exact h
  have h2 : Nat.card (spinGroup (quadPlus 8 K)) = Nat.card Ψ.range * Nat.card Ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
  have hk : 0 < Nat.card Ψ.ker := Nat.card_pos
  refine ⟨m, ?_⟩
  have : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K))) * (Nat.card Ψ.ker * m) =
      Nat.card Ψ.range * Nat.card Ψ.ker := by rw [← hm, ← h1, h2]
  nlinarith

theorem factorization_card_E8_le_card_d8 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k) :
    (Nat.card (adjointGroup .E8 K)).factorization p ≤
      (Nat.card ↥(⨆ k, e8D8Chain K k)).factorization p := by
  have hX : Nat.card ↥(⨆ k, e8D8Chain K k) = Nat.card Ψ.range := by rw [hrange]
  rw [hX, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
  exact (factorization_ordE8_le_N8 hp Nat.card_pos he).trans
    ((factorization_N8_le_card_proj hp he).trans
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (card_statedProj_dvd_card_range Ψ hker) p))

theorem exists_conj_plane_d8_of_psi {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    {e : adjointGroup .E8 K} (he1 : e ∈ ⨆ k, e8D8Chain K k) (heo : orderOf e = p)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k ∧
      e ∈ E₀.map (MulAut.conj g).toMonoidHom := by
  have hT : CFSG.LieType.SeitzGeneration.SylowTorus (adjointGroup .E8 K) p 2 :=
    CFSG.LieType.SeitzGeneration.sylowTorus_E8_eight K hp.out he
  have hE₀el : CFSG.Open.IsElemAbelian p E₀ :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus hT
        (IsPGroup.of_card (n := 2) hE₀c) a.2 b.2), fun x hx => hE₀p x hx⟩
  exact exists_conj_plane_le_of_factorization hT _
    (factorization_card_E8_le_card_d8 hp.out he Ψ hker hrange) he1 heo hE₀el hE₀c

end Main

end CFSG.HardMathSupport.Lang.AnisoE8
