module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import CFSG.ClassicalInvolution.RouteD.TypeELocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiagC
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Bridge

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_aniso_perp_fam (hQ : (polarBilin Q).Nondegenerate) (p : ℕ → HypPair Q) (n : ℕ)
    (ho : ∀ a b, a < n → b < n → a ≠ b → (p a).Orth (p b))
    (hd : 2 * n + 1 ≤ Module.finrank K V) : ∃ c : V, Q c ≠ 0 ∧ ∀ a < n, c ∈ (p a).perp := by
  obtain ⟨C, hC, hnd, hdim⟩ := fam_perp hQ p n ho
  have hpos : 0 < Module.finrank K C := by omega
  have hCbot : C ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨c₀, hc₀C, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCbot
  obtain ⟨y, hyC, hy⟩ := hnd.exists_polar_ne_zero hc₀C hc₀
  have hex : ∃ c ∈ C, Q c ≠ 0 := by
    by_cases h1 : Q c₀ = 0
    · by_cases h2 : Q y = 0
      · refine ⟨c₀ + y, C.add_mem hc₀C hyC, ?_⟩
        rw [QuadraticMap.map_add Q, h1, h2, zero_add, zero_add]
        exact hy
      · exact ⟨y, hyC, h2⟩
    · exact ⟨c₀, hc₀C, h1⟩
  obtain ⟨c, hcC, hQc⟩ := hex
  exact ⟨c, hQc, fun a ha => (hC c).mp hcC a ha⟩

theorem exists_tilted_bridge (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 13 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hc : VChain Q 5 L i) {L5 : Subgroup (V ≃ₗ[K] V)} (h5 : IsFundamental Q L5 (i 4)) :
    ∃ S : Subgroup (V ≃ₗ[K] V), S ∈ fundSet Q ∧ (∀ a < 3, Commutes S (L a)) ∧
      ¬ Commutes S (L 4) ∧ ¬ Commutes S L5 := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, hpl, hL⟩ := exists_chain_pairs true hodd hc (by norm_num : 2 ≤ 5)
  have ho : ∀ a b, a < 6 → b < 6 → a ≠ b → (p a).Orth (p b) :=
    fun a b ha hb hab => horth a b (by omega) (by omega) hab
  obtain ⟨c, hQc, hcp⟩ := exists_aniso_perp_fam hQ p 6 ho (by omega)
  have hc5 := HypPair.mem_perp.mp (hcp 5 (by omega))
  have h1 : polar Q (p 5).e ((p 5).f + c) = 1 := by
    rw [polar_add_right, (p 5).polar_ef, hc5.1, add_zero]
  obtain ⟨q', hq'e, hq'f⟩ : ∃ q' : HypPair Q, q'.e = (p 5).e ∧
      q'.f = (p 5).f + c - Q c • (p 5).e := by
    refine ⟨HypPair.ofPolarEqOne (p 5).Q_e h1, rfl, ?_⟩
    show (p 5).f + c - Q ((p 5).f + c) • (p 5).e = _
    rw [QuadraticMap.map_add Q, (p 5).Q_f, zero_add]
    simp [hc5.2]
  have hq'orth : ∀ a < 5, (p a).Orth q' := by
    intro a ha
    have h5a := mem_perp_of_orth (ho a 5 (by omega) (by omega) (by omega))
    refine orth_of_mem_perp (by rw [hq'e]; exact h5a.1) ?_
    rw [hq'f]
    exact Submodule.sub_mem _ (Submodule.add_mem _ h5a.2 (hcp a (by omega)))
      (Submodule.smul_mem _ _ h5a.1)
  set F : OFrame Q := mkFrame (p 4) (swapPair q') (orth_swapPair (hq'orth 4 (by norm_num)))
    with hF
  have hcomm : ∀ a < 3, Commutes F.La.range (L a) := by
    intro a ha
    rw [hL a (by omega)]
    refine commutes_of_span_orth F _ ?_
    rw [frame_span_eq, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair, hF]
    refine polar_eq_zero_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_)
      (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    · exact polar_hypPlane_of_orth (horth 4 a (by omega) (by omega) (by omega)) x hx y hy
    · exact polar_hypPlane_of_orth (horth 4 (a + 1) (by omega) (by omega) (by omega)) x hx y hy
    · exact polar_hypPlane_of_orth (hq'orth a (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hq'orth (a + 1) (by omega)).symm x hx y hy

  have hiS : negSpace (F.La (-1)) = hypPlane (p 4) ⊔ hypPlane q' := by
    rw [negSpace_La_neg_one h2, frame_span_eq]
    simp only [hF, mkFrame, hypPlane_swapPair]
  have hf4 : IsFundamental Q (L 4)
      ((oFrame true (p 4) (p 5) (horth 4 5 (by omega) (by omega) (by omega))).La (-1)) := by
    rw [hL 4 (by omega)]
    exact IsFundamental.of_frame _
  have hi4 : i 4 = (oFrame true (p 4) (p 5) (horth 4 5 (by omega) (by omega) (by omega))).La (-1) :=
    IsFundamental.involution_unique hodd (hc.fund 4 (by omega)) hf4
  have hn4 : negSpace (i 4) = hypPlane (p 4) ⊔ hypPlane (p 5) := by
    rw [hi4, negSpace_La_neg_one h2, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair]
  have hne : i 4 ≠ F.La (-1) := by
    intro heq
    have hf5 : (p 5).f ∈ negSpace (F.La (-1)) := by
      rw [← heq, hn4]
      exact Submodule.mem_sup_right (f_mem_hypPlane (p 5))
    rw [hiS] at hf5
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hf5
    obtain ⟨b₁, b₂, rfl⟩ := (mem_hypPlane_iff q').mp hb
    obtain ⟨a₁, a₂, rfl⟩ := (mem_hypPlane_iff (p 4)).mp ha
    have hc4 := HypPair.mem_perp.mp (hcp 4 (by omega))
    have hpc := congrArg (fun v => polar Q v c) hab
    simp only [polar_add_left, polar_smul_left_eq, hc4.1, hc4.2, hq'e, hq'f, hc5.1, hc5.2,
      polar_sub_left, polar_self] at hpc
    have hb2 : b₂ * (2 * Q c) = 0 := by linear_combination hpc
    have hb20 : b₂ = 0 := by
      rcases mul_eq_zero.mp hb2 with h | h
      · exact h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h2
        · exact absurd h' hQc
    have ho45 := horth 4 5 (by omega) (by omega) (by omega)
    have hpe := congrArg (fun v => polar Q v (p 5).e) hab
    simp only [polar_add_left, polar_smul_left_eq, ho45.ee, ho45.fe, hq'e, hb20, zero_mul,
      HypPair.polar_fe, polar_self, (p 5).Q_e, smul_zero, mul_zero, add_zero] at hpe
    exact one_ne_zero hpe.symm
  have hx : (p 5).e ∈ negSpace (F.La (-1)) := by
    rw [hiS]
    exact Submodule.mem_sup_right (hq'e ▸ e_mem_hypPlane q')
  have hy : (p 5).f ∈ negSpace (i 4) := by
    rw [hn4]
    exact Submodule.mem_sup_right (f_mem_hypPlane (p 5))
  have hxy : polar Q (p 5).e (p 5).f ≠ 0 := by
    rw [(p 5).polar_ef]
    exact one_ne_zero
  exact ⟨F.La.range, ⟨_, IsFundamental.of_frame F⟩, hcomm,
    not_commutes_of_nonorth hodd (IsFundamental.of_frame F) (hc.fund 4 (by omega)) hne hx hy hxy,
    not_commutes_of_nonorth hodd (IsFundamental.of_frame F) h5 hne hx (hn4 ▸ hy) hxy⟩
end Bridge

section SpinBridge

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD

theorem exists_tilted_bridge_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 13 ≤ Module.finrank (GaloisField p f) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ 4, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕)
    (hadj : ∀ a < 4, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 4, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 4 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R 3) Rtw) (hcommtw : ∀ a, a ≤ 2 → Commutes (R a) Rtw)
    (hcommtw' : Commutes (R 4) Rtw) :
    ∃ T ∈ 𝓕, (∀ a < 3, Commutes T (R a)) ∧ ¬ Commutes T (R 4) ∧ ¬ Commutes T Rtw := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim9 : 9 ≤ Module.finrank (GaloisField p f) V := by omega
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen (u := 1) hp2 hq hdim9 cq hRf hRtwf hadj hcomm
    hadjtw hcommtw hcommtw'
  have hex : ∀ a, ∃ i, a ≤ 4 → IsFundamental Q ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ 4
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < 4, ModelAdj (scalars (GaloisField p f) V) ((R a).map (spinAction Q))
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
      exact hasSingularVector_of_linearPair hp2 (by omega) (hi a (by omega))
        (hi (a + 1) (by omega)) (hdata a (by omega)).1 (hdata a (by omega)).2.1
        (hdata a (by omega)).2.2 ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
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

end SpinBridge

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}


theorem exists_tilted_bridge_group [Finite G] (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {t : StatedLieTag} {n : ℕ} (e : Layer0 p f Ω x t n)
    (hY : YData p f t n)
    (hF : OrthFacts (fundamentalSubgroups t (modelUniv t n p f Fact.out).D) (GaloisField p f))
    (hbridge : ∀ {R : ℕ → Subgroup (modelUniv t n p f Fact.out).K}
      {Rtw : Subgroup (modelUniv t n p f Fact.out).K},
      (∀ a ≤ 4, R a ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D) →
      Rtw ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      (∀ a < 4, ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) (R a) (R (a + 1))) →
      (∀ a < 4, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1))) →
      (∀ a b, a + 1 < b → b ≤ 4 → Commutes (R a) (R b)) →
      ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) (R 3) Rtw →
      (∀ a, a ≤ 2 → Commutes (R a) Rtw) → Commutes (R 4) Rtw →
      ∃ T ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
        (∀ a < 3, Commutes T (R a)) ∧ ¬ Commutes T (R 4) ∧ ¬ Commutes T Rtw)
    {M : Subgroup G} (nd : DNodes p f 6 Ω M) (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {x}) :
    ∃ N ∈ centralizingMembers Ω {x}, (∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a)) ∧
      ¬ Commutes N (nd.J ⟨4, by norm_num⟩) ∧ ¬ Commutes N (nd.J ⟨5, by norm_num⟩) := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hmem : ∀ a : Fin 6, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
      locImg Ω x (nd.J a) = R.map e.φ := fun a => e.mem _ (hx a)
  choose R hRf hLR using hmem
  let jn : ℕ → Fin 6 := fun a => ⟨min a 5, by omega⟩
  have hjn : ∀ a, a < 6 → (jn a).val = a := fun a h => by
    simp only [jn]
    omega
  have hadjn : ∀ a, a < 4 → DNodes.Adj (jn a) (jn (a + 1)) := fun a h => by
    rw [DNodes.adj_def, hjn a (by omega), hjn (a + 1) (by omega)]
    omega
  have hnadj : ∀ a b, a + 1 < b → b ≤ 4 → ¬ DNodes.Adj (jn a) (jn b) := fun a b hab hb => by
    rw [DNodes.adj_def, hjn a (by omega), hjn b (by omega)]
    omega
  have hne : ∀ a b, a < 6 → b < 6 → a ≠ b → jn a ≠ jn b := fun a b ha hb hab h => by
    have := congrArg Fin.val h
    rw [hjn a ha, hjn b hb] at this
    exact hab this
  have h4 : jn 4 = ⟨4, by norm_num⟩ := Fin.ext (hjn 4 (by omega))
  have h5 : jn 5 = ⟨5, by norm_num⟩ := Fin.ext (hjn 5 (by omega))
  have hcommR : ∀ a b : ℕ, a < 6 → b < 6 → Commutes (nd.J (jn a)) (nd.J (jn b)) →
      Commutes (R (jn a)) (R (jn b)) := fun a b ha hb hc =>
    (e.commutes_iff hY hΩ hP1 (hx _) (hx _) (hRf _) (hLR _) (hLR _)).mp hc
  have hadjR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes.Adj (jn a) (jn b) →
      ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab =>
      e.modelAdj hY hΩ hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) (nd.cl _) (nd.cl _)
        (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _)
        (nd.conjSub_w h2 hab)
  have hlinR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes.Adj (jn a) (jn b) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab => by
      obtain ⟨W, hW⟩ := nd.pair_of_adj hab
      exact e.pair_to_model hF hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) hW
  have hadj35 : DNodes.Adj (jn 3) (jn 5) := by
    rw [DNodes.adj_def, hjn 3 (by omega), hjn 5 (by omega)]
    omega
  have hn45 : ¬ DNodes.Adj (jn 4) (jn 5) := by
    rw [DNodes.adj_def, hjn 4 (by omega), hjn 5 (by omega)]
    omega
  have hnadjtw : ∀ a, a ≤ 2 → ¬ DNodes.Adj (jn a) (jn 5) := fun a ha => by
    rw [DNodes.adj_def, hjn a (by omega), hjn 5 (by omega)]
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
    exact (e.commutes_iff hY hΩ hP1 hN (hx a) hT hNT (hLR a)).mpr hTa
  · intro h
    apply hn4
    have := (e.commutes_iff hY hΩ hP1 hN (hx ⟨4, by norm_num⟩) hT hNT (hLR _)).mp h
    rw [h4]
    exact this
  · intro h
    apply hn5
    have := (e.commutes_iff hY hΩ hP1 hN (hx ⟨5, by norm_num⟩) hT hNT (hLR _)).mp h
    exact this

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.D6
