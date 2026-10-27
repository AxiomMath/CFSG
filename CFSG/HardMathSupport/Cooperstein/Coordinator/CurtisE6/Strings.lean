module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringsAbstract
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Rank1
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTypeE6

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem lElt_eq' (c : K) : (lElt c : SL(2, K)) = WSL * uElt (-c) * WSL⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [lElt, uElt, WSL]

theorem uElt_inv' (c : K) : (uElt c : SL(2, K))⁻¹ = uElt (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← uElt_add, add_neg_cancel, uElt_zero]

theorem lElt_inv' (c : K) : (lElt c : SL(2, K))⁻¹ = lElt (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [lElt, Matrix.one_fin_two]

theorem yr_eq (s : N6) (c : K) :
    e6Data_valid.xm K (-Pi.single s 1) c =
      e6Data_valid.nm K s * e6Data_valid.xm K (Pi.single s 1) (-c) * (e6Data_valid.nm K s)⁻¹ := by
  rw [← rankOne6_l, lElt_eq', map_mul, map_mul, map_inv, rankOne6_u, rankOne6_w]

@[expose] noncomputable def D6 (K : Type) [Field K] [Finite K] [CharP K 2] :
    CurtisDatum ↥(e6Data_valid.minGroup K) (coxeterSystem TwistTag.E6.tag) 2 :=
  (e6CoverData K).datum

theorem xm_mem_X (s : N6) (c : K) : e6Data_valid.xm K (Pi.single s 1) c ∈ (D6 K).X s :=
  (e6CoverRankOne K).x_mem s c |> fun h => by
    exact h

theorem fixSub_stable_rankOne (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (s : N6)
    (Q : Subgroup ↥(e6Data_valid.minGroup K))
    (hx : ∀ (c : K), ∀ q ∈ Q, (e6Data_valid.xm K (Pi.single s 1) c)⁻¹ * q *
      e6Data_valid.xm K (Pi.single s 1) c ∈ Q)
    (hy : ∀ (c : K), ∀ q ∈ Q, (e6Data_valid.xm K (-Pi.single s 1) c)⁻¹ * q *
      e6Data_valid.xm K (-Pi.single s 1) c ∈ Q)
    (g : SL(2, K)) {w : V} (hw : w ∈ fixSub ρ Q) : ρ (rankOne6 K s g) w ∈ fixSub ρ Q := by
  have key : ∀ g : SL(2, K), ∀ w ∈ fixSub ρ Q, ρ (rankOne6 K s g) w ∈ fixSub ρ Q ∧
      ρ (rankOne6 K s g⁻¹) w ∈ fixSub ρ Q := by
    have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) := by
      rw [hcl]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx' =>
      rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · intro w hw
        have e1 : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uElt c := rfl
        rw [e1, uElt_inv', rankOne6_u, rankOne6_u]
        exact ⟨act_mem_fixSub ρ (hx c) hw, act_mem_fixSub ρ (hx (-c)) hw⟩
      · intro w hw
        have e1 : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
        rw [e1, lElt_inv', rankOne6_l, rankOne6_l]
        exact ⟨act_mem_fixSub ρ (hy c) hw, act_mem_fixSub ρ (hy (-c)) hw⟩
    | one =>
      intro w hw
      simp only [inv_one, map_one]
      exact ⟨by simpa using hw, by simpa using hw⟩
    | mul a b _ _ ha hb =>
      intro w hw
      obtain ⟨ha1, ha2⟩ := ha w hw
      obtain ⟨hb1, hb2⟩ := hb w hw
      refine ⟨?_, ?_⟩
      · rw [map_mul, ← act_mul]
        exact (ha _ hb1).1
      · rw [mul_inv_rev, map_mul, ← act_mul]
        exact (hb _ ha2).2
    | inv a _ ha =>
      intro w hw
      obtain ⟨h1, h2⟩ := ha w hw
      exact ⟨h2, by rw [inv_inv]; exact h1⟩
  exact (key g w hw).1

theorem Us_normalized (s : N6) :
    (∀ (c : K), ∀ q ∈ (D6 K).Us s, (e6Data_valid.xm K (Pi.single s 1) c)⁻¹ * q *
      e6Data_valid.xm K (Pi.single s 1) c ∈ (D6 K).Us s) ∧
    (∀ (c : K), ∀ q ∈ (D6 K).Us s, (e6Data_valid.xm K (-Pi.single s 1) c)⁻¹ * q *
      e6Data_valid.xm K (-Pi.single s 1) c ∈ (D6 K).Us s) := by
  set D := D6 K with hD
  refine ⟨fun c q hq => ?_, fun c q hq => ?_⟩
  · have := D.X_normUs s (e6Data_valid.xm K (Pi.single s 1) c)⁻¹ (inv_mem (xm_mem_X s c)) q hq
    simpa using this
  · rw [yr_eq s c]
    have h1 : (D.n s)⁻¹ * q * D.n s ∈ D.Us s := D.n_normUs' s q hq
    have h2 := D.X_normUs s (e6Data_valid.xm K (Pi.single s 1) (-c))⁻¹
      (inv_mem (xm_mem_X s _)) _ h1
    have h3 := D.n_normUs s _ h2
    have hn : D.n s = e6Data_valid.nm K s := nhat_e6 s
    rw [hn] at h3
    simpa [mul_assoc] using h3

theorem fix_of_highest {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (s : N6) {f : V}
    (hf : f ∈ fixSub ρ ((D6 K).Us s))
    (hfu : ∀ c : K, ρ (e6Data_valid.xm K (Pi.single s 1) c) f = f) : ∃ c : k, f = c • y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  set D := D6 K with hD
  have hfU : f ∈ D.fixU ρ := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
    obtain ⟨c, rfl⟩ := (e6CoverRankOne K).mem_lX_iff s |>.1 hx
    rw [← act_mul, hf v hv]
    exact hfu c
  exact D.fixU_eq_smul hρ hμ hfU

theorem string_of_highest {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (s : N6) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) = 2 ^ J'.card ∧
      (J' = ∅ → ∀ g, ρ (rankOne6 K s g) y = y) ∧
      (∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y, e ≠ 0 ∧ ∀ z : Kˣ,
        ρ (e6Data_valid.hm K s z) e =
          (algebraMap K k (z : K)) ^ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) • e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  set D := D6 K with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (K := K) s
  obtain ⟨J', hJ', hε, hfin, hemp, hwt⟩ := string_data hK (ρ.comp (rankOne6 K s)) ht.2.1
    (fixSub ρ (D.Us s))
    (fun g hg => ht.1 g (D.Us_le s hg))
    (fun g w hw => fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g hw)
    (by
      intro f hf hfu
      have hfU : f ∈ D.fixU ρ := by
        intro u hu
        obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
        obtain ⟨c, rfl⟩ := (e6CoverRankOne K).mem_lX_iff s |>.1 hx
        rw [← act_mul, hf v hv]
        have h' : ρ (rankOne6 K s (uElt c)) f = f := hfu c
        rw [rankOne6_u] at h'
        exact h'
      exact D.fixU_eq_smul hρ hμ hfU)
    (by
      intro c
      show ρ (rankOne6 K s (uElt c)) y = y
      rw [rankOne6_u]
      exact ht.1 _ (D.X_le s (xm_mem_X s c)))
    (fun z => χ (e6Data_valid.hm K s z))
    (by
      intro z
      show ρ (rankOne6 K s (dElt z)) y = χ (e6Data_valid.hm K s z) • y
      rw [rankOne6_d]
      exact ht.2.2.1 _ (e6_hm_mem_H s z))
  refine ⟨J', hJ', hε, hfin, hemp, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  exact ⟨e, he, he0, fun z => by rw [← rankOne6_d]; exact hed z⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
