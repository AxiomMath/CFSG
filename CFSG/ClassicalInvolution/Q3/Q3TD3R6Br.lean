module

public import CFSG.ClassicalInvolution.Q3.Q3TY34
public import CFSG.ClassicalInvolution.RouteD.TWED6Bridge
public import CFSG.ClassicalInvolution.Q3.Q3TY18

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.RouteD.TWE.D6 (exists_tilted_bridge)
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups commutatorElement


section Spin

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

theorem exists_tilted_bridge_spin3 (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 13 ≤ Module.finrank (GaloisField 3 1) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V))
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ 4, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕)
    (hadj : ∀ a < 4, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 4, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 4 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R 3) Rtw) (hcommtw : ∀ a, a ≤ 2 → Commutes (R a) Rtw)
    (hcommtw' : Commutes (R 4) Rtw) :
    ∃ T ∈ 𝓕, (∀ a < 3, Commutes T (R a)) ∧ ¬ Commutes T (R 4) ∧ ¬ Commutes T Rtw := by
  classical
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hdim9 : 9 ≤ Module.finrank (GaloisField 3 1) V := by omega
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen3 (u := 1) hdim9 cq hRf hRtwf hadj hcomm
    hadjtw hcommtw hcommtw'
  have hex : ∀ a, ∃ i, a ≤ 4 → IsFundamental Q ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ 4
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < 4, ModelAdj (scalars (GaloisField 3 1) V) ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < 4, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer (((R a).map (spinAction Q) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer (((R a).map (spinAction Q) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim9 (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain Q 5 (fun a => (R a).map (spinAction Q)) i := by
    refine ⟨fun a ha => hi a (by omega), fun a ha => (hdata a (by omega)).1,
      fun a ha => (hdata a (by omega)).2.1, fun a ha => (hdata a (by omega)).2.2, fun a ha => ?_,
      fun a b hab hb x hx y hy => ?_⟩
    · obtain ⟨W, hW⟩ := hlin a (by omega)
      exact hasSingularVector_of_linearPair3 (hi a (by omega)) (hi (a + 1) (by omega))
        (hdata a (by omega)).1 (hdata a (by omega)).2.1 (hdata a (by omega)).2.2
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
    · have hcV := (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))
      rcases orth_or_twin hodd (hi a (by omega)) (hi b (by omega)) hcV with h | h
      · exact h x hx y hy
      · exact absurd h.symm (hdist a b hab (by omega) _ _ (hi a (by omega)) (hi b (by omega)))
  have h5 : IsFundamental Q (Rtw.map (spinAction Q)) (i 4) :=
    htwin (i 4) itw (hi 4 le_rfl) hitw ▸ hitw
  obtain ⟨S, hS, hc3, hn4, hn5⟩ := exists_tilted_bridge hodd hQ hdim hVchain h5
  obtain ⟨T, hT, rfl⟩ := cq.surj S hS
  exact ⟨T, hT, fun a ha => (cq.commutes_iff hT).mp (hc3 a ha),
    fun h => hn4 ((cq.commutes_iff hT).mpr h), fun h => hn5 ((cq.commutes_iff hT).mpr h)⟩

end Spin

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_tilted_bridge_group3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {tY : StatedLieTag} {nY : ℕ}
    [Finite (modelUniv tY nY 3 1 Nat.prime_three).K] (e : Layer03 Ω x tY nY)
    (hY : YData3 tY nY)
    (hbridge : ∀ {R : ℕ → Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
      {Rtw : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      (∀ a ≤ 4, R a ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) →
      Rtw ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D →
      (∀ a < 4, ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) (R a)
        (R (a + 1))) →
      (∀ a < 4, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1))) →
      (∀ a b, a + 1 < b → b ≤ 4 → Commutes (R a) (R b)) →
      ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) (R 3) Rtw →
      (∀ a, a ≤ 2 → Commutes (R a) Rtw) → Commutes (R 4) Rtw →
      ∃ T ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
        (∀ a < 3, Commutes T (R a)) ∧ ¬ Commutes T (R 4) ∧ ¬ Commutes T Rtw)
    {M : Subgroup G} (nd : DNodes3 6 Ω M) (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {x}) :
    ∃ N ∈ centralizingMembers Ω {x}, (∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a)) ∧
      ¬ Commutes N (nd.J ⟨4, by norm_num⟩) ∧ ¬ Commutes N (nd.J ⟨5, by norm_num⟩) := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hmem : ∀ a : Fin 6, ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω x (nd.J a) = R.map e.φ := fun a => e.mem _ (hx a)
  choose R hRf hLR using hmem
  let jn : ℕ → Fin 6 := fun a => ⟨min a 5, by omega⟩
  have hjn : ∀ a, a < 6 → (jn a).val = a := fun a h => by
    simp only [jn]
    omega
  have hadjn : ∀ a, a < 4 → DNodes3.Adj (jn a) (jn (a + 1)) := fun a h => by
    rw [DNodes3.adj_def, hjn a (by omega), hjn (a + 1) (by omega)]
    omega
  have hnadj : ∀ a b, a + 1 < b → b ≤ 4 → ¬ DNodes3.Adj (jn a) (jn b) := fun a b hab hb => by
    rw [DNodes3.adj_def, hjn a (by omega), hjn b (by omega)]
    omega
  have hne : ∀ a b, a < 6 → b < 6 → a ≠ b → jn a ≠ jn b := fun a b ha hb hab h => by
    have := congrArg Fin.val h
    rw [hjn a ha, hjn b hb] at this
    exact hab this
  have h4 : jn 4 = ⟨4, by norm_num⟩ := Fin.ext (hjn 4 (by omega))
  have h5 : jn 5 = ⟨5, by norm_num⟩ := Fin.ext (hjn 5 (by omega))
  have hcommR : ∀ a b : ℕ, a < 6 → b < 6 → Commutes (nd.J (jn a)) (nd.J (jn b)) →
      Commutes (R (jn a)) (R (jn b)) := fun a b ha hb hc =>
    (e.commutes_iff hY hΩ hex hP1 hO3 (hx _) (hx _) (hRf _) (hLR _) (hLR _)).mp hc
  have hadjR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes3.Adj (jn a) (jn b) →
      ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab =>
      e.modelAdj hY hΩ hex hP1 hO3 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) (nd.cl _)
        (nd.cl _) (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w _ _)
        (nd.conjSub_w hab)
  have hlinR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes3.Adj (jn a) (jn b) →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab => by
      obtain ⟨W, hW⟩ := nd.pair_of_adj hab
      exact e.pair_to_model hY hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) hW
  have hadj35 : DNodes3.Adj (jn 3) (jn 5) := by
    rw [DNodes3.adj_def, hjn 3 (by omega), hjn 5 (by omega)]
    omega
  have hn45 : ¬ DNodes3.Adj (jn 4) (jn 5) := by
    rw [DNodes3.adj_def, hjn 4 (by omega), hjn 5 (by omega)]
    omega
  have hnadjtw : ∀ a, a ≤ 2 → ¬ DNodes3.Adj (jn a) (jn 5) := fun a ha => by
    rw [DNodes3.adj_def, hjn a (by omega), hjn 5 (by omega)]
    omega
  obtain ⟨T, hT, hc, hn4, hn5⟩ := hbridge (R := fun a => R (jn a)) (Rtw := R (jn 5))
    (fun a ha => hRf _) (hRf _)
    (fun a ha => hadjR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a ha => hlinR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a b hab hb => hcommR a b (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a b (by omega) (by omega) (by omega)) (hnadj a b hab hb)))
    (hadjR 3 5 (by omega) (by omega) hadj35)
    (fun a ha => hcommR a 5 (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a 5 (by omega) (by omega) (by omega)) (hnadjtw a ha)))
    (hcommR 4 5 (by omega) (by omega)
      (nd.commutes_of_not_adj (hne 4 5 (by omega) (by omega) (by omega)) hn45))
  obtain ⟨N, hN, hNT⟩ := e.comp T hT
  have hjnfin : ∀ a : Fin 6, jn a.val = a := fun a => Fin.ext (hjn a.val a.isLt)
  refine ⟨N, hN, fun a ha => ?_, ?_, ?_⟩
  · have hTa := hc a.val ha
    rw [hjnfin a] at hTa
    exact (e.commutes_iff hY hΩ hex hP1 hO3 hN (hx a) hT hNT (hLR a)).mpr hTa
  · intro h
    apply hn4
    have := (e.commutes_iff hY hΩ hex hP1 hO3 hN (hx ⟨4, by norm_num⟩) hT hNT (hLR _)).mp h
    rw [h4]
    exact this
  · intro h
    apply hn5
    have := (e.commutes_iff hY hΩ hex hP1 hO3 hN (hx ⟨5, by norm_num⟩) hT hNT (hLR _)).mp h
    exact this

theorem exists_tilted_bridge_d6_3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaPlus 6).1
      (twinYModel 3 .POmegaPlus 6).2) Ω x) {M : Subgroup G} (nd : DNodes3 6 Ω M)
    (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {x}) :
    ∃ N ∈ centralizingMembers Ω {x}, (∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a)) ∧
      ¬ Commutes N (nd.J ⟨4, by norm_num⟩) ∧ ¬ Commutes N (nd.J ⟨5, by norm_num⟩) := by
  classical
  have hmod : twinYModel 3 .POmegaPlus 6 = (.POmegaMinus, 7) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaMinus 7 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := Q3TY.yData3_minus (by norm_num : 4 ≤ 7) hadm
  have : Finite (modelUniv .POmegaMinus 7 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc (hx ⟨0, by norm_num⟩) hshape
  have cq := centralQuot3_minus hadm
  have hQ : (polarBilin (quadMinus 7 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField 3 1) (minusCoeffs_irr 3 1)
  have hdim : 13 ≤ Module.finrank (GaloisField 3 1)
      (Fin (7 - 1) ⊕ Fin (7 - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 7 (by norm_num)]
    norm_num
  exact exists_tilted_bridge_group3 hΩ hex hP1 hO3 e hY
    (fun {R} {Rtw} hRf hRtwf hadj hlin hcomm hadjtw hcommtw hcommtw' =>
      exists_tilted_bridge_spin3 hQ hdim cq hRf hRtwf hadj hlin hcomm hadjtw hcommtw hcommtw')
    nd hx

end Group

end CFSG.ClassicalInvolution.Q3.Q3TD
