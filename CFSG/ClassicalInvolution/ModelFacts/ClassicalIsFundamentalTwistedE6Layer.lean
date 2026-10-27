module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedCover
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Exceptional
open scoped commutatorElement

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem isSubnormal_orbitGroupC_totalFixedGroup (J' : Set.range D.classOrbit) :
    CFSG.Open.IsSubnormal (D.withOrbit J').orbitGroupC D.totalFixedGroup := by
  have h1 : (D.withOrbit J').orbitGroupC ≤ (D.withOrbit J').fixedGroup :=
    (D.withOrbit J').orbitGroupC_le_fixedGroup
  have h2 : (D.withOrbit J').fixedGroup ≤ D.orbitFixedJoin :=
    D.fixedGroup_withOrbit_le_orbitFixedJoin J'
  have h3 : D.orbitFixedJoin ≤ D.kernelFixedGroup := D.orbitFixedJoin_le_kernelFixedGroup
  have h4 : D.kernelFixedGroup ≤ D.totalFixedGroup := D.kernelFixedGroup_le_totalFixedGroup
  refine CFSG.Open.IsSubnormal.step h1 (D.withOrbit J').orbitGroupC_normal
    (CFSG.Open.IsSubnormal.step h2 ?_
      (CFSG.Open.IsSubnormal.step h3 ?_ (CFSG.Open.IsSubnormal.step h4 ?_
        (CFSG.Open.IsSubnormal.refl _))))
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_fixedGroup_withOrbit (h3 g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_orbitFixedJoin g.2 (Subgroup.mem_subgroupOf.1 hn))⟩
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_kernelFixedGroup g.2 (Subgroup.mem_subgroupOf.1 hn))⟩

theorem orbitGroupC_eq_bot_or_isQuasisimple (h3 : 3 < D.q) :
    D.orbitGroupC = ⊥ ∨ CFSG.Open.IsQuasisimple ↥D.orbitGroupC := by
  by_cases hne : D.orbits.Nonempty
  · right
    have hfin : D.orbits.Finite := by
      have : D.orbits = (thetaOrbit D.θ) '' D.simpleRootsJ := by
        ext O
        exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩, fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩⟩
      rw [this]
      exact (D.finite_roots.subset fun _ h => h.2).image _
    obtain ⟨-, -, h2, h1, -⟩ := orthogonal_semilinear_fixed_root_quasisimplicity D
    have hpos : 0 < D.orbits.ncard := (Set.ncard_pos hfin).2 hne
    have hq : CFSG.IsQuasisimple D.orbitGroup := by
      by_cases hc : 2 ≤ D.orbits.ncard
      · exact h2 hc
      · obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 (by omega : D.orbits.ncard = 1)
        have hOm : O ∈ D.orbits := by rw [hO]; exact Set.mem_singleton O
        refine h1 O hO ?_
        rw [D.card_orbitField hOm]
        exact h3.trans_le (Nat.le_self_pow (D.orbitCard_pos hOm).ne' _)
    have hq' : CFSG.Open.IsQuasisimple ↥D.orbitGroup := ⟨hq.1.commutator_eq_top, hq.2.1⟩
    exact (CFSG.ClassicalInvolution.RouteD.Exotic.open_isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup)).2 hq'
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : D.orbitGroup = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O, hO, -⟩
      rw [hne] at hO
      exact absurd hO (Set.notMem_empty O)
    rw [OrthogonalSemilinearFixedRootDatum.orbitGroupC, hbot]
    ext x
    simp

end Datum

section E6

variable (p e : ℕ) [Fact p.Prime]

theorem twistedE6_le_iSup_components (hp2 : p ≠ 2) (he : 1 ≤ e) (hq : 3 < p ^ e)
    {s : twistedE6Group p e}
    (hs : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s *
      twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s = 1)
    {R : Subgroup (twistedE6Group p e)} (hR : R ≤ ⁅R, R⁆)
    (hRs : R ≤ Subgroup.centralizer ({s} : Set (twistedE6Group p e))) :
    R ≤ ⨆ (Q : Subgroup (twistedE6Group p e))
      (_ : CFSG.Open.IsComponentOf Q
        (Subgroup.centralizer ({s} : Set (twistedE6Group p e)))), Q := by
  classical
  have hΦR := twistedE6Phi_mem_fixedPointsIn p e hp2 he
  have hx2 : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s ^ 2 = 1 := by
    rw [pow_two]
    exact hs
  obtain ⟨-, -, D, w, -, hw, -, -, -, hDe, -, -, hcent⟩ :=
    e6_exists_datum_conj_centralizer p hp2
      (isAlgebraic_zmod_of_isAlgClosure p (GaloisField p (2 * e))
        (AlgebraicClosure (GaloisField p (2 * e)))) he (hΦR s) hx2
  obtain ⟨ψ, hker, hXs, hH, hPr⟩ :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.exists_cover_of_conj_centralizer
      (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))))
      (ker_twistedE6Phi_le_center p e _) _ _ inf_le_left hΦR
      (range_twistedE6Phi p e hp2 he) w hw s _ hcent
  have hq3 : ∀ J' : Set.range D.classOrbit, 3 < (D.withOrbit J').q := by
    intro J'
    show 3 < p ^ D.e
    rw [hDe]
    exact hq
  have hT : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroupC = ⊥ ∨
      (CFSG.Open.IsSubnormal (D.withOrbit J').orbitGroupC D.totalFixedGroup ∧
        CFSG.Open.IsQuasisimple ↥(D.withOrbit J').orbitGroupC) := by
    intro J'
    rcases orbitGroupC_eq_bot_or_isQuasisimple (D.withOrbit J') (hq3 J') with h | h
    · exact Or.inl h
    · exact Or.inr ⟨isSubnormal_orbitGroupC_totalFixedGroup D J', h⟩
  have hTr : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroupC ≤ ψ.range := by
    intro J'
    rcases hT J' with h | ⟨hs', hq'⟩
    · rw [h]
      exact bot_le
    · exact hPr _ (CFSG.ClassicalInvolution.Balance.Bootstrap.le_of_isSubnormal_open hs')
        (CFSG.ClassicalInvolution.Balance.Bootstrap.commutator_eq_of_isQuasisimple hq')
  have hRX : R.map ψ ≤ D.totalFixedGroup := by
    rintro _ ⟨r', hr', rfl⟩
    exact hH r' (hRs hr')
  have hRperf : ⁅R.map ψ, R.map ψ⁆ = R.map ψ := by
    rw [← Subgroup.map_commutator, le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hR]
  have hRT := le_iSup_orbitGroupC_of_isPerfect D hRX (Subgroup.isPerfect_iff.2 hRperf)
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.le_iSup_components_of_map_le ψ hker s hXs hH
    (fun J' => (D.withOrbit J').orbitGroupC) hTr hT hR hRT

end E6

end CFSG.ClassicalInvolution.ModelFacts
