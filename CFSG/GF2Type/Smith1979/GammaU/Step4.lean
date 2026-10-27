module

public import CFSG.GF2Type.Smith1979.GammaU.TripleCensus
public import CFSG.GF2Type.Smith1979.GammaU.ResConj

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

structure Step4Hyp (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop where
  frame : ∀ l, RowsSet (compOf i) l → l ∈ M
  theta : thetaU ∈ M
  noViol : ∀ N ≤ M, ¬ Viol.Violation N (compOf i) (compOf i)

@[expose] def ConfigOf (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (r : Array ℕ)
    (Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop :=
  ∃ n ∈ colPts r, ∃ De : Submodule (ZMod 2) V12,
    Hyp (vecOf n) De Le ∧ (∃ l ∈ Le, ∀ y, l y = linOfRows r y) ∧ vecOf a0 ∈ De ∧ Le ≤ M ∧
      Nat.card (candGrp i Le) = 1152

@[expose] def HasConfig (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (r : Array ℕ) : Prop :=
  ∃ Le, ConfigOf i M r Le

theorem candGrp_le {i : ℕ} {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step4Hyp i M)
    {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hLe : Le ≤ M) : candGrp i Le ≤ M := by
  rw [candGrp, Subgroup.closure_le]
  rintro l ((hl | hl) | hl)
  · exact hM.frame l hl
  · exact hLe hl
  · rw [Set.mem_singleton_iff] at hl
    rw [hl]
    exact hM.theta

theorem Step4Hyp.conj_resConj
    {i : ℕ} (hi : i = 0 ∨ i = 1) {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step4Hyp i M)
    {c : Array ℕ} (hc : c ∈ ResPair.resConj i) (h1 : mulR c (Viol.invR c) = idR)
    (h2 : mulR (Viol.invR c) c = idR) :
    Step4Hyp i (M.map (MulAut.conj (Viol.eqvOf c (Viol.invR c) h1 h2)⁻¹).toMonoidHom) := by
  have hi32 : i < 32 := by omega
  set e := Viol.eqvOf c (Viol.invR c) h1 h2
  have he := resConj_nlMem hi hc h1 h2
  refine ⟨fun l hl => ?_, ?_, fun N hN hv => ?_⟩
  · rw [mem_map_conj_inv]
    exact hM.frame _ ((he.norm l).2 hl)
  · rw [mem_map_conj_inv]
    rcases thetaU_conj he.mem with h | h
    · rw [h]; exact hM.theta
    · rw [h]; exact inv_mem hM.theta
  · apply hM.noViol (N.map (MulAut.conj e).toMonoidHom)
    · rintro _ ⟨x, hx, rfl⟩
      have := hN hx
      rw [mem_map_conj_inv] at this
      exact this
    · exact violation_conj Certificates.certificate16966 hi32 he hv

theorem mem_hyp10_of_hasConfig
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step4Hyp i M) (hN : ResPair.n2 i ≤ M)
    {r : Array ℕ} (hr : r ∈ unitaryElts i) (hc : HasConfig i M r) : r ∈ ResPair.hyp10 i := by
  by_contra hrH
  obtain ⟨Le, n, hn, De, H, hs, ha, hle, hcard⟩ := hc
  exact hM.noViol _ (sup_le hN (candGrp_le hM hle))
    (triple_census hi hr hrH hn H hs ha hcard)

end CFSG.GF2Type.Smith1979.GammaU.StepA
