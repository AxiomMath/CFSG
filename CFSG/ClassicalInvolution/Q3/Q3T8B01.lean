module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Claims


@[expose] def C26_1H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)

@[expose] def C26_2H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → ¬ MuIsoS4 Ω W

@[expose] def C26_2_uH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∀ x ∈ T, x * u = u * x

@[expose] def S26ActH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∃ ε : ℕ, ε ≤ 1 ∧
            ∀ x ∈ omegaNbrGen Ω K, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (omegaNbrGen Ω K)

@[expose] def S26XEdgelessH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
        DEdgeless (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)))

@[expose] def S26XTopH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
        (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
          oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))

@[expose] def C26_3_S4H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
        SectionLieTypeU 3 1 Ω (omegaNbrGen Ω K) .PSL 3 ∨
          SectionCompU 3 1 Ω (omegaNbrGen Ω K) Q3.CompData.m11

end Claims

section Chain261


theorem outerFusionAllH :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
        omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K) → T8R.OuterFusion K J S R T z t := by
  intro G _ _ _ Ω K J S R T W z t hs hX
  exact T8R.outerFusion hs hX

theorem c26_1_of_outerH : C26_1H := by
  have h := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.outerFusionAllH
  intro G _ _ _ Ω K J S R T W z t hs hX
  exact T8R.false_of_hX hs hX (T8R.extraTrans hs hX) (T8R.extraTrans (T8R.Std8.symm' hs)
    (T8R.eq_sup_oddCoreOf_swap hs hX)) (h G Ω K J S R T W z t hs hX)

theorem c26_1H_proved : C26_1H := c26_1_of_outerH

theorem c26_2_u_of_actH (h : S26ActH) : C26_2_uH := by
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4 P hPD M hMΩ hPM hMK hMJ u hu
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  have hPsyl : IsSylow2In P M := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ
      hPD.1 hPM
  obtain ⟨ε, hε, hact⟩ := h G Ω K J S R T W z t hs hXne hS4 P hPD M hMΩ hPM hMK hMJ u hu
  have huW : u ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hMΩ hPD hPsyl hu).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun M' (_ : M' ∈ omegaNbr Ω K) => M') J hs.hJ
  have htε : t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem (hWS htW) ε
  intro x hx
  have hxX : x ∈ omegaNbrGen Ω K := hJX (hTJ hx)
  have hc := hact x hxX
  have hvS : u * t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem (hWS huW) htε
  have hcS : ⁅u * t ^ ε, x⁆ ∈ (S : Subgroup G) := by
    rw [commutatorElement_def]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hvS (hTS hx)) ((S : Subgroup G).inv_mem hvS))
      ((S : Subgroup G).inv_mem (hTS hx))
  have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅u * t ^ ε, x⁆) :=
    (S.isPGroup').to_le ((Subgroup.zpowers_le).mpr hcS)
  have hc1 : ⁅u * t ^ ε, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc hc2
  have hcomm : (u * t ^ ε) * x = x * (u * t ^ ε) := by
    rw [commutatorElement_def] at hc1
    calc (u * t ^ ε) * x = (u * t ^ ε * x * (u * t ^ ε)⁻¹ * x⁻¹) * (x * (u * t ^ ε)) := by
          group
      _ = x * (u * t ^ ε) := by rw [hc1, one_mul]
  have htx : t ^ ε * x = x * t ^ ε := by
    interval_cases ε
    · simp
    · rw [pow_one]
      exact hs.ht.commute_of_mem (hTJ hx)
  have h2 : (u * x) * t ^ ε = (x * u) * t ^ ε := by
    calc (u * x) * t ^ ε = u * (x * t ^ ε) := by rw [mul_assoc]
      _ = u * (t ^ ε * x) := by rw [htx]
      _ = (u * t ^ ε) * x := by rw [mul_assoc]
      _ = x * (u * t ^ ε) := hcomm
      _ = (x * u) * t ^ ε := by rw [mul_assoc]
  exact (mul_right_cancel h2).symm

theorem c26_2_of_uH (h : C26_2_uH) : C26_2H := by
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4
  obtain ⟨φ⟩ := hS4
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hP : PartIHyp Ω := ⟨hΩ, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, hnot⟩ := s26_exists_third hs φ
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hMΩ
  have hcent := h G Ω K J S R T W z t hs hXne ⟨φ⟩ P hPD M hMΩ hPM.1 hMK hMJ u hu
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hTΩ hTJ
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hrel : σ.r * u * σ.r⁻¹ = t * u :=
    c.conj_involution σ ρP (fun h => hMJ h.symm) hnot hs.ht hu
  have hcomm : σ.r * u = u * σ.r := hcent t' ht'
  have hcu : σ.r * u * σ.r⁻¹ = u := by
    rw [hcomm]
    group
  rw [hcu] at hrel
  apply hs.ht.ne_one
  have : t * u = 1 * u := by rw [← hrel, one_mul]
  exact mul_right_cancel this

end Chain261

section ChainSection


theorem s26XMuZ2_provedH :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
        omegaNbrGen Ω K ≠ ⊤ → MuIsoS4 Ω W →
          ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
            MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W' := by
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4
  obtain ⟨φ⟩ := hS4
  exact s26XMuZ2_of_data hs φ hXne

theorem s26XEdgeless_of_muZ2H (h752 : L7_5_2) : S26XEdgelessH := by
  have hZ := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.s26XMuZ2_provedH
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hXne hS4
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  exact s26_dEdgeless_of_muIsoZ2 h752 hGen.modU ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩ hW' hZ2

theorem s26_top_notMem_of_c26_1H (h1 : C26_1H) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hs : Std8 Ω K J S R T W z t) :
    (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
      oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)) := by
  intro htopΦ
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  obtain ⟨L', hL', hL'top⟩ := htopΦ
  have hJ' : J.subgroupOf X ∈ restrictFamily Ω X := ⟨J, hs.hJ.1, hJX, rfl⟩
  have hc : ∀ L'' ∈ restrictFamily Ω X, Nat.card (↥L'' ⧸ classicalInvolutionOddCore ↥L'') =
      Nat.card SL(2, GaloisField 3 1) := by
    intro L'' hL''
    obtain ⟨z', hz'⟩ := (Q3T6.hypOmegaModU_restrict hs.stand.modU X).classical L'' hL''
    exact Sect.natCard_quot_member hz'
  have hJtop := s26_map_top_of_card hc hL' hJ' hL'top
  apply h1 G Ω K J S R T W z t hs
  refine le_antisymm ?_ (sup_le hJX (oddCoreOf_le_self X))
  intro x hx
  have hxtop : (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ⟨x, hx⟩ ∈
      (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
    rw [hJtop]
    trivial
  obtain ⟨j', hj', hj'x⟩ := Subgroup.mem_map.mp hxtop
  have hn : j'⁻¹ * ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥X := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj'x
    exact hj'x
  have hnG : ((j'⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ oddCoreOf X :=
    Subgroup.mem_map_of_mem X.subtype hn
  have hjJ : (j' : G) ∈ J := Subgroup.mem_subgroupOf.mp hj'
  have hx' : x = (j' : G) * ((j'⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    simp
  rw [hx']
  exact Subgroup.mul_mem_sup hjJ hnG

theorem s26XTop_of_c26_1H (h1 : C26_1H) : S26XTopH := by
  intro G _ _ _ Ω K J S R T W z t hs _ _
  exact s26_top_notMem_of_c26_1H h1 hs

theorem c26_3_S4_of_xH (hE : S26XEdgelessH) (hT : S26XTopH) :
    C26_3_S4H := by
  have hZ := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.s26XMuZ2_provedH
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4
  have hΩU : HypOmegaModU (.sl2 3 1) Ω := hs.stand.modU
  have hA : ∀ L ∈ Ω, AEmpty Ω L := hs.stand.aEmpty
  have hn : CITBelowT (.sl2 3 1) (Nat.card G) := hs.stand.below
  have hih : IH8T 3 1 (Nat.card G) := hs.stand.ih
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hXp : X ≠ ⊤ := hXne
  have hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω X)) :=
    hE G Ω K J S R T W z t hs hXne hS4
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := hT G Ω K J S R T W z t hs hXne hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hXne hS4
  have hcardX : Nat.card ↥X < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group X)
      (fun h => hXp (Subgroup.eq_top_of_card_eq X h))
  have hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < Nat.card G :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) hcardX
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hΩU hA
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hΦne : (oddQuotientFamily (restrictFamily Ω X)).Nonempty :=
    ⟨_, ⟨J.subgroupOf X, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩⟩
  have hne : (restrictFamily Ω X).Nonempty := ⟨J.subgroupOf X, J, hs.hJ.1, hJX, rfl⟩
  have hL : layerHull Ω X = X := s26_layerHull_omegaNbrGen Ω K
  have hcls : InClassU (.sl2 3 1) (restrictFamily Ω X) := inClassU_restrict_hull hΩU hL hne
  have hΛU : HypOmegaModU (.sl2 3 1) (restrictFamily Ω X) := Q3T6.hypOmegaModU_restrict hΩU X
  have hΛg : HypOmegaGen (restrictFamily Ω X) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛU
  have hconj : ConjInvariant (oddQuotientFamily (restrictFamily Ω X)) :=
    conjInvariant_oddQuotientFamily hΛU.conjInvariant
  have hno : ∀ A ∈ oddQuotientFamily (restrictFamily Ω X),
      ∀ B ∈ oddQuotientFamily (restrictFamily Ω X), ¬ Commutes A B := by
    intro A hA' B hB' hAB
    by_cases hEq : A = B
    · subst hEq
      obtain ⟨K₁, hK₁, rfl⟩ := hA'
      obtain ⟨x, hx, y, hy, hxy⟩ := Q3T6.exists_noncomm_map_of_mem hΛg hK₁
      exact hxy (hAB _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
    · exact hDE A hA' B hB' (dAdj_of_commutes hB' hEq hAB)
  obtain ⟨ι, -, ⟨D₀⟩⟩ := (hn ↥X hcardX _ hcls).toLieSystemU
  have : Subsingleton ι := Q3T6.subsingleton_of_noCommute D₀ hno
  obtain ⟨L₀, hL₀⟩ := hΦne
  obtain ⟨i₀, -⟩ := D₀.fundamental L₀ hL₀
  have : Unique ι := uniqueOfSubsingleton i₀
  let D := D₀.reindex (Equiv.ofUnique (Fin 1) ι)
  have hΦne' : (oddQuotientFamily (restrictFamily Ω X)).Nonempty := ⟨L₀, hL₀⟩
  have hnt : Nontrivial (↥X ⧸ classicalInvolutionOddCore ↥X) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hno L₀ hL₀ L₀ hL₀ (fun a _ b _ => Subsingleton.elim _ _)
  have hexcl : ∀ (t' : StatedLieTag) (k : ℕ), S1911.IsT6Tag t' k → ¬ (t' = .PSL ∧ k = 3) →
      CompIs 3 1 (D.kind 0) t' k → False := by
    intro t' k htag hnot hc
    obtain ⟨e, he, hft, hadm, hc'⟩ := hc
    have hsimple : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X) :=
      Q3T6.isSimpleGroup_of_systemU (by norm_num) D 0 hconj htag hft hadm he hc' hGen.oddCore
    have htrans : ∀ K' ∈ oddQuotientFamily (restrictFamily Ω X),
        ∀ L' ∈ oddQuotientFamily (restrictFamily Ω X),
          ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g K' = L' := by
      rcases dConnected_or_transitive3 hih.thm4 hlt hGen.modU hGen.oddCore hGen.aEmpty with
        hc3 | ht
      · exfalso
        apply htop
        have hall : omegaGen (oddQuotientFamily (restrictFamily Ω X)) = L₀ := by
          refine le_antisymm (iSup₂_le fun L hL' => ?_) (le_omegaGen hL₀)
          rw [eq_of_dConnected_of_dEdgeless3 hc3 hDE hL' hL₀]
        rw [← hGen.gen, hall]
        exact hL₀
      · exact ht
    have hrows := hih.muTable (by norm_num) (by norm_num) (↥X ⧸ classicalInvolutionOddCore ↥X)
      hlt _ hGen.modU hGen.aEmpty hΦne' htrans W' hW'
    have hS3 : MuIsoS3 (oddQuotientFamily (restrictFamily Ω X)) W' := by
      refine hrows.2.1.mpr ?_
      have hpi : piSign 3 1 = false := by decide
      rw [hpi]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hcomp : CompIs 3 1 (D.kind 0) t' k := ⟨e, he, hft, hadm, hc'⟩
      rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd ⟨rfl, rfl⟩ hnot
      · exact Or.inl ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩
      · exact Or.inr (Or.inl ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩)
      · exact Or.inr (Or.inr ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩)
    exact false_of_muIsoZ2_of_muIsoS3 hZ2 hS3
  rcases tag_cases_of_sysData D hconj hno hΦne' htop with ⟨t', k, htag, hc⟩ | hc
  · by_cases hL3 : t' = .PSL ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hL3
      exact Or.inl ⟨D, hc⟩
    · exfalso
      refine hexcl t' k ?_ hL3 hc
      rcases htag with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr ⟨D, hc⟩

end ChainSection

section Chain262


theorem s26Act_of_secH (h3 : C26_3_S4H) : S26ActH := by
  intro G _ _ _ Ω K J S R T W z t hs hXne hS4 P hPD M hMΩ hPM hMK hMJ u hu
  obtain ⟨b, c, n, hn, hbo, hco, hbu, hct, hbW, hcW, hcT, hbK, hbJ, hbc, huW, htW, hfac⟩ :=
    s26_setup hs hPD hMΩ hPM hMK hMJ hu
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hTJ : T ≤ J := hs.hT.2.1
  have hbX : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := s26_conjSub_omegaNbrGen hΩ hbK
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hbN : b ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbX
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hcJ : c ∈ J := hTJ hcT
  have hcX : c ∈ X := hJX hcJ
  have htX : t ∈ X := hJX hs.ht.mem
  have huN : u ∈ Subgroup.normalizer (X : Set G) :=
    hbu ▸ (Subgroup.normalizer (X : Set G)).pow_mem hbN _
  have htN : t ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer htX
  let β : MulAut (↥X ⧸ classicalInvolutionOddCore ↥X) := s26Act X ⟨b, hbN⟩
  let ū : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  let tbar : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  have hβū : β ū = ū := by
    refine s26Act_mk X ⟨b, hbN⟩ ⟨c, hcX⟩ ⟨c, hcX⟩ ?_
    show c = b * c * b⁻¹
    rw [hbc]
    group
  have hb2 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 ^ (n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hbo]
    exact pow_orderOf_eq_one b
  have hβ2 : β ^ 2 ^ (n + 1) = 1 := by
    rw [← map_pow, hb2, map_one]
  have hβu : β ^ 2 ^ n = s26Act X ⟨u, huN⟩ := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hbu
  have hūt : ū ^ 2 ^ n = tbar := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ n =
      ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
    rw [← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hct
  have ht1 : tbar ≠ 1 := by
    intro h1
    have h2 : (⟨t, htX⟩ : ↥X) ∈ classicalInvolutionOddCore ↥X := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : t ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨htX, h2⟩
    exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h3
      (isPGroup_zpowers_of_mul_self_eq_one hs.ht.sq hs.ht.ne_one))
  have hū2 : ū ^ 2 ^ (n + 1) = 1 := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ (n + 1) = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 2 ^ (n + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hco]
      exact pow_orderOf_eq_one c
    rw [this]
    rfl
  have hord : orderOf ū = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hūt]; exact ht1) hū2
  have hJ' : (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      oddQuotientFamily (restrictFamily Ω X) := ⟨J.subgroupOf X, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩
  have hūJ' : ū ∈ (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    ⟨⟨c, hcX⟩, hcJ, rfl⟩
  have hdich : β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj tbar := by
    rcases h3 G Ω K J S R T W z t hs hXne hS4 with ⟨D, hD⟩ | ⟨D, hD⟩
    · have := s26_dich_of_sysDataU D (Or.inl hD) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
    · have := s26_dich_of_sysDataU D (Or.inr hD) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
  have hact : s26Act X ⟨t, htN⟩ = MulAut.conj tbar := s26Act_eq_conj X ⟨t, htX⟩
  rw [hβu] at hdich
  rcases hdich with h | h
  · refine ⟨0, by norm_num, fun x hx => ?_⟩
    have := s26_comm_mem_oddCore_of_act_eq_one X ⟨u, huN⟩ h hx
    simpa using this
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have h1 : s26Act X (⟨u, huN⟩ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, h, hact, ← map_mul]
      have : tbar * tbar = 1 := by
        show ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) *
          ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1
        rw [← QuotientGroup.mk_mul]
        have : (⟨t, htX⟩ : ↥X) * ⟨t, htX⟩ = 1 := Subtype.ext hs.ht.sq
        rw [this]
        rfl
      rw [this, map_one]
    have := s26_comm_mem_oddCore_of_act_eq_one X
      ⟨u * t, (Subgroup.normalizer (X : Set G)).mul_mem huN htN⟩ h1 hx
    simpa using this

theorem c26_2_u_of_secH (h3 : C26_3_S4H) : C26_2_uH :=
  c26_2_u_of_actH (s26Act_of_secH h3)

theorem c26_2_of_xH (hE : S26XEdgelessH) (hT : S26XTopH) : C26_2H :=
  c26_2_of_uH (c26_2_u_of_secH (c26_3_S4_of_xH hE hT))

theorem c26_2_provedH : C26_2H :=
  c26_2_of_xH (s26XEdgeless_of_muZ2H l7_5_2_proved) (s26XTop_of_c26_1H c26_1H_proved)

theorem c26_2B_proved : C26_2B := by
  intro G _ _ _ Ω K J S R T W z t h hX
  exact c26_2_provedH G Ω K J S R T W z t h.std hX

end Chain262

section SupX


theorem sup_omegaNbrGen_ne_top {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hX : omegaNbrGen Ω K ≠ ⊤) : K ⊔ omegaNbrGen Ω K ≠ ⊤ := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hKN : K ≤ Subgroup.normalizer ((omegaNbrGen Ω K : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_iff_conjSub_eq.mpr (s26_conjSub_omegaNbrGen hΩ (conjSub_eq_self_of_mem hk))
  have hle : K ⊔ omegaNbrGen Ω K ≤ Subgroup.normalizer ((omegaNbrGen Ω K : Subgroup G) : Set G) :=
    sup_le hKN Subgroup.le_normalizer
  intro htop
  have hnormal : (omegaNbrGen Ω K).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.mp (hle (by rw [htop]; exact Subgroup.mem_top g))
      x).mp hx⟩
  have hJX : J ≤ omegaNbrGen Ω K := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  rcases Subgroup.Normal.eq_bot_or_eq_top (omegaNbrGen Ω K) with h | h
  · have ht : t ∈ omegaNbrGen Ω K := hJX hs.ht.mem
    rw [h] at ht
    exact hs.ht.ne_one ((Subgroup.mem_bot).mp ht)
  · exact hX h

end SupX

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
