module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringsAbstract
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Strings


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def rankOne (τ : Tag) (K : Type) [Field K] (s : Fin τ.rank) :
    SL(2, K) →* adjointGroup τ K :=
  (simpleRootSL2 τ K s).codRestrict (adjointGroup τ K)
    (fun A => simpleRootSL2_mem_adjointGroup s A)

theorem rankOne_u (s : Fin τ.rank) (c : K) : rankOne τ K s (uElt c) = xC τ K s c :=
  Subtype.ext (simpleRootSL2_uSL s c)

theorem rankOne_l (s : Fin τ.rank) (c : K) : rankOne τ K s (lElt c) = yC τ K s c :=
  Subtype.ext (simpleRootSL2_vSL s c)

theorem rankOne_d (s : Fin τ.rank) (z : Kˣ) : rankOne τ K s (dElt z) = dC τ K s z :=
  Subtype.ext (simpleRootSL2_HSL s z)

theorem rankOne_w (s : Fin τ.rank) : rankOne τ K s WSL = nC τ K s :=
  Subtype.ext (simpleRootSL2_WSL s)

theorem lElt_eq (c : K) : (lElt c : SL(2, K)) = WSL * uElt (-c) * WSL⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [lElt, uElt, WSL, Matrix.mul_fin_two]

theorem rankOne_l' (s : Fin τ.rank) (c : K) :
    yC τ K s c = nC τ K s * xC τ K s (-c) * (nC τ K s)⁻¹ := by
  rw [← rankOne_l, lElt_eq, map_mul, map_mul, map_inv, rankOne_u, rankOne_w]

theorem uElt_inv' (c : K) : (uElt c : SL(2, K))⁻¹ = uElt (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← uElt_add, add_neg_cancel, uElt_zero]

theorem lElt_inv' (c : K) : (lElt c : SL(2, K))⁻¹ = lElt (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [lElt, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem fixSub_stable_rankOne (ρ : Representation k (adjointGroup τ K) V) (s : Fin τ.rank)
    (Q : Subgroup (adjointGroup τ K))
    (hx : ∀ (c : K), ∀ q ∈ Q, (xC τ K s c)⁻¹ * q * xC τ K s c ∈ Q)
    (hy : ∀ (c : K), ∀ q ∈ Q, (yC τ K s c)⁻¹ * q * yC τ K s c ∈ Q)
    (g : SL(2, K)) {w : V} (hw : w ∈ fixSub ρ Q) : ρ (rankOne τ K s g) w ∈ fixSub ρ Q := by
  have key : ∀ g : SL(2, K), ∀ w ∈ fixSub ρ Q, ρ (rankOne τ K s g) w ∈ fixSub ρ Q ∧
      ρ (rankOne τ K s g⁻¹) w ∈ fixSub ρ Q := by
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
        rw [e1, uElt_inv', rankOne_u, rankOne_u]
        exact ⟨act_mem_fixSub ρ (hx c) hw, act_mem_fixSub ρ (hx (-c)) hw⟩
      · intro w hw
        have e1 : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
        rw [e1, lElt_inv', rankOne_l, rankOne_l]
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

theorem Us_normalized (s : Fin τ.rank) :
    (∀ (c : K), ∀ q ∈ (chevDatum τ K 2 hw).Us s,
      (xC τ K s c)⁻¹ * q * xC τ K s c ∈ (chevDatum τ K 2 hw).Us s) ∧
    (∀ (c : K), ∀ q ∈ (chevDatum τ K 2 hw).Us s,
      (yC τ K s c)⁻¹ * q * yC τ K s c ∈ (chevDatum τ K 2 hw).Us s) := by
  set D := chevDatum τ K 2 hw with hD
  refine ⟨fun c q hq => ?_, fun c q hq => ?_⟩
  · have := D.X_normUs s (xC τ K s c)⁻¹ (inv_mem (xC_mem_X s c)) q hq
    simpa using this
  · rw [rankOne_l']
    have h1 : (nC τ K s)⁻¹ * q * nC τ K s ∈ D.Us s := D.n_normUs' s q hq
    have h2 := D.X_normUs s (xC τ K s (-c))⁻¹ (inv_mem (xC_mem_X s _)) _ h1
    have h3 := D.n_normUs s _ h2
    have hn : D.n s = nC τ K s := rfl
    rw [hn] at h3
    simpa [mul_assoc] using h3

theorem fix_of_highest {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (s : Fin τ.rank) {f : V}
    (hf : f ∈ fixSub ρ ((chevDatum τ K 2 hw).Us s)) (hfu : ∀ c : K, ρ (xC τ K s c) f = f) :
    ∃ c : k, f = c • y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  set D := chevDatum τ K 2 hw with hD
  have hfU : f ∈ D.fixU ρ := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
    obtain ⟨c, rfl⟩ := mem_X_chevDatum.1 hx
    rw [← act_mul, hf v hv]
    exact hfu c
  exact D.fixU_eq_smul hρ hμ hfU

theorem string_of_highest {n : ℕ} (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (s : Fin τ.rank) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) = 2 ^ J'.card ∧
      (J' = ∅ → ∀ g, ρ (rankOne τ K s g) y = y) ∧
      (∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y, e ≠ 0 ∧ ∀ z : Kˣ,
        ρ (dC τ K s z) e =
          (algebraMap K k (z : K)) ^ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) • e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  set D := chevDatum τ K 2 hw with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (hw := hw) (K := K) s
  obtain ⟨J', hJ', hε, hfin, hemp, hwt⟩ := string_data hK (ρ.comp (rankOne τ K s)) ht.2.1
    (fixSub ρ (D.Us s))
    (fun g hg => D.Us_le s hg |> fun h => ht.1 g (D.Us_le s hg))
    (fun g w hw => fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g hw)
    (by
      intro f hf hfu
      have hfU : f ∈ D.fixU ρ := by
        intro u hu
        obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
        obtain ⟨c, rfl⟩ := mem_X_chevDatum.1 hx
        rw [← act_mul, hf v hv]
        have := hfu c
        simpa [rankOne_u] using this
      exact D.fixU_eq_smul hρ hμ hfU)
    (by
      intro c
      show ρ (rankOne τ K s (uElt c)) y = y
      rw [rankOne_u]
      exact ht.1 _ (D.X_le s (xC_mem_X s c)))
    (fun z => χ (dC τ K s z))
    (by
      intro z
      show ρ (rankOne τ K s (dElt z)) y = χ (dC τ K s z) • y
      rw [rankOne_d]
      exact ht.2.2.1 _ (dC_mem_H s z))
  refine ⟨J', hJ', hε, hfin, hemp, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  exact ⟨e, he, he0, fun z => by rw [← rankOne_d]; exact hed z⟩

end Strings

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
