module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld.CrossChar

section Form


theorem l154_realE6_of_form {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
    [h2 : CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154RealizedMarking (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨f, n₁, g, π, hf, hstd, hX⟩ := l154_layer_data S haT i v hΨ
  rcases hstd.hπ with h1 | h1
  ·
    haveI : Finite (frobeniusFixedField L 2 f) := finite_frobeniusFixedField hf
    have hL := hstd.stdLayer_eq_map_of_one (f := f) h1
    rw [hL, Subgroup.map_map] at hX
    have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
        (baseChangeGL (frobeniusFixedField L 2 f).subtype)) :=
      (MulAut.conj g).injective.comp (baseChangeGL_injective _)
    rw [hX] at hqi ⊢
    exact l154_realizedMarking_inner hf (card_frobeniusFixedField_pow hf) hj hqi
  ·
    haveI : Finite (K2 L 2 f) := finite_frobeniusFixedField (by omega)
    haveI := certificate123_of_kernel
    have hL := hstd.stdLayer_eq_range_of_rho (f := f) h1
    have hpsi : psi2 τ L 2 f = (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype).comp
        (e6Iota τ L f) := rfl
    rw [hL, MonoidHom.map_range, hpsi, ← MonoidHom.comp_assoc] at hX
    have hj : Function.Injective ((MulAut.conj g).toMonoidHom.comp
        (baseChangeGL (frobeniusFixedField L 2 (2 * f)).subtype)) :=
      (MulAut.conj g).injective.comp (baseChangeGL_injective _)
    rw [hX] at hqi ⊢
    exact l154_realizedMarking_outer hf hj hqi

end Form

section Kac


theorem l154_form_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup Tag.E7 L p₀)
    (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ}
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : L154E6Class a i) :
    ∃ v : WeylGroup Tag.E7, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E7 (e6Nodes Tag.E7) := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hc6 : c.length = 6 := hrank.symm.trans h6.1
  have h72 : kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset = 72 :=
    hncard.symm.trans h6.2
  have hCeq := kacCount_E7_six ((c.map (idxNode (r := Tag.E7.rank))).toFinset)
    (by rw [e7_card c hc, hc6]) h72
  refine ⟨v, ?_⟩
  rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE7 facts_E7 (J := e6Nodes Tag.E7)
    (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]

theorem l154_form_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup Tag.E8 L p₀)
    (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : L154E6Class a i) :
    ∃ v : WeylGroup Tag.E8, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hc6 : c.length = 6 := hrank.symm.trans h6.1
  have h72 : kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset = 72 :=
    hncard.symm.trans h6.2
  have hCeq := kacCount_E8_six ((c.map (idxNode (r := Tag.E8.rank))).toFinset)
    (by rw [e8_card c hc, hc6]) h72
  refine ⟨v, ?_⟩
  rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE8 facts_E8 (J := e6Nodes Tag.E8)
    (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]

end Kac

theorem l154_compRank_le {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) : compRank Ψ ≤ τ.rank := by
  unfold compRank
  calc Module.finrank ℚ ↥(Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ)) ≤
      Module.finrank ℚ (Fin τ.rank → ℚ) := Submodule.finrank_le _
    _ = τ.rank := by simp

section Excl


theorem l154_ncard_isRoot_E6 : {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}.ncard = 72 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6) fun _ => True
  simp only [and_true, decide_true, List.countP_true] at h
  rw [h, CFSG.Timmesfeld.ExceptionalOrders.rootList, List.length_map, List.length_range,
    Tag.rootCertificate_length]
  rfl

theorem l154_not_E6 {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : L154E6Class a i) : False := by
  have hsub : componentRoots (rootCharHom a) i ⊆ {γ | IsRoot Tag.E6 γ} := fun γ hγ => hγ.1.1
  have hfin : {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}.Finite :=
    Set.finite_of_ncard_pos (by rw [l154_ncard_isRoot_E6]; norm_num)
  have heq : componentRoots (rootCharHom a) i = {γ | IsRoot Tag.E6 γ} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [l154_ncard_isRoot_E6, h6.2]) hfin
  apply ha1
  have ha : a = 1 := by
    funext j
    have hj : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [heq]
      exact IsRoot.basis j
    have h1 := hj.1.2
    have h2 : rootChar a (Pi.single j 1) = a j := by
      simp [rootChar, Pi.single_apply]
    exact h2 ▸ h1
  rw [ha]
  exact rootDiagUnit_one

end Excl

theorem l154_rootDiagUnit_pow {τ : Tag} {L : Type} [Field L] {p : ℕ} {a : Fin τ.rank → Lˣ}
    (hap : ∀ i, a i ^ p = 1) : rootDiagUnit τ a ^ p = 1 := by
  have key : ∀ n : ℕ, rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]
  rw [key p, show a ^ p = 1 from funext fun i => by simpa using hap i, rootDiagUnit_one]

section Main


theorem l154RealE6_holds : L154RealE6 := by
  intro τ L _ _ _ p₀ S p a i hp _ hT hap ha1 hqi h6
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := l154_rootDiagUnit_pow hap
  have hle := l154_compRank_le (componentRoots (rootCharHom a) i)
  have h6r := h6.1
  cases τ with
  | G2 =>
    exfalso
    have hr : Tag.G2.rank = 2 := rfl
    omega
  | F4 =>
    exfalso
    have hr : Tag.F4.rank = 4 := rfl
    omega
  | D4 =>
    exfalso
    have hr : Tag.D4.rank = 4 := rfl
    omega
  | E6 => exact (l154_not_E6 ha1 i h6).elim
  | E7 =>
    obtain ⟨v, hv⟩ := l154_form_E7 S hp hpL hTp i h6
    exact l154_realE6_of_form S hT i v hv hqi
  | E8 =>
    obtain ⟨v, hv⟩ := l154_form_E8 S hp hpL hTp i h6
    exact l154_realE6_of_form S hT i v hv hqi

end Main

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
