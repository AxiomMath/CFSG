module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Comp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Lift
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def NoPlane3 (Q : Type) [Group Q] : Prop :=
  ∀ D : Subgroup (MulAut Q), CFSG.Open.IsElemAbelian 3 D → Nat.card D ≠ 3 ^ 2

theorem noPlane3_alternatingGroup_five : NoPlane3 (alternatingGroup (Fin 5)) := by
  intro D _ hDc
  obtain ⟨hinj, hsurj⟩ := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  let e : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5))) ⟨hinj, hsurj⟩
  have hdvd : Nat.card D ∣ Nat.card (MulAut (alternatingGroup (Fin 5))) :=
    Subgroup.card_subgroup_dvd_card D
  have hP : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [← Nat.card_congr e.toEquiv, hP, hDc] at hdvd
  norm_num at hdvd

namespace KSNotAll24

theorem le_hyperGamma_of_range_ne {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (f : MulAut X) (hf : f ∈ E) (hf1 : f ≠ 1) (J : Subgroup X)
    (hJfix : ∀ g ∈ Subgroup.zpowers f, ∀ y ∈ J, g y = y)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J)
    (hD : Nat.card (resHom J E hJE).range ≠ 3 ^ 2) : J ≤ seitzHyperGamma 3 E := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥E →* MulAut J := resHom J E hJE with hρ
  have hρker : ∀ g : ↥E, g ∈ ρ.ker → ∀ y ∈ J, g.1 y = y := by
    intro g hg y hy
    have h : ρ g = 1 := MonoidHom.mem_ker.1 hg
    exact congrArg (fun φ : MulAut J => ((φ ⟨y, hy⟩ : J) : X)) h
  have hfker : (⟨f, hf⟩ : ↥E) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    ext y
    exact hJfix f (Subgroup.mem_zpowers f) y y.2
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = 3 ^ 3 := by
    rw [Subgroup.card_ker_mul_card_range, hEc]
  have hker1 : Nat.card ρ.ker ≠ 1 := by
    intro h1
    have h2 := Subgroup.card_eq_one.1 h1
    rw [h2] at hfker
    exact hf1 (congrArg Subtype.val (Subgroup.mem_bot.1 hfker))
  have hkerdvd : 3 ^ 2 ∣ Nat.card ρ.ker := by
    have hDdvd : Nat.card ρ.range ∣ 3 ^ 3 := Dvd.intro_left _ hcard
    obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hDdvd
    rw [hDi] at hcard
    interval_cases i
    · norm_num at hcard ⊢
      omega
    · norm_num at hcard ⊢
      omega
    · exact absurd hDi hD
    · norm_num at hcard
      exact absurd hcard hker1
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ρ.ker) 3 hkerdvd
  set F : Subgroup (MulAut X) := (K₀.map ρ.ker.subtype).map E.subtype with hF
  have hFc : Nat.card F = 3 ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK₀]
  have hFE : F ≤ E := Subgroup.map_subtype_le _
  have hFfix : J ≤ fixedPoints F := by
    intro y hy φ hφ
    rw [hF, Subgroup.mem_map] at hφ
    obtain ⟨a, ha, rfl⟩ := hφ
    rw [Subgroup.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact hρker _ b.2 y hy
  exact hFfix.trans (fixedPoints_le_hyperGamma hFE (relIndex_eq_three hFE hEc hFc))

theorem card_range_ne_nine {X : Type} [Group X] [Finite X] (E : Subgroup (MulAut X))
    (hE : CFSG.Open.IsElemAbelian 3 E) (J : Subgroup X) (hperf : commutator J = ⊤)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) (hno : NoPlane3 (J ⧸ Subgroup.center J)) :
    Nat.card (resHom J E hJE).range ≠ 3 ^ 2 := by
  intro h9
  have hinj := quotCenterHom_injective hperf
  have hD := isElemAbelian_range hE (resHom J E hJE)
  have hD' : CFSG.Open.IsElemAbelian 3 ((resHom J E hJE).range.map (quotCenterHom J)) :=
    CFSG.SectionRank.isElemAbelian_map hD (quotCenterHom J)
  apply hno _ hD'
  rw [Subgroup.card_map_of_injective hinj]
  exact h9

theorem not_three_dvd_card_of_perfect {J : Type} [Group J] [Finite J] (hJ : commutator J = ⊤)
    (h3 : ¬ 3 ∣ Nat.card (J ⧸ Subgroup.center J)) : ¬ 3 ∣ Nat.card J := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  have hcent : ∀ x ∈ (P : Subgroup J), x ∈ Subgroup.center J := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hxk : x ^ (3 ^ k) = 1 := congrArg Subtype.val hk
    have hq : (QuotientGroup.mk x : J ⧸ Subgroup.center J) ^ (3 ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one]
    have hd1 : orderOf (QuotientGroup.mk x : J ⧸ Subgroup.center J) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one hq
    have hd2 := orderOf_dvd_natCard (QuotientGroup.mk x : J ⧸ Subgroup.center J)
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (J ⧸ Subgroup.center J)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    have h1 : orderOf (QuotientGroup.mk x : J ⧸ Subgroup.center J) = 1 :=
      Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h1)
  have hN : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J) := by
    intro y _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_center_iff.1 (hcent x hx)) y).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hN
  set φ := MonoidHom.transferSylow P hN with hφ
  have hker : φ.ker = ⊤ := by
    have hcomm : commutator J ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply Subtype.ext
      have hxy : (φ a : J) * (φ b : J) = (φ b : J) * (φ a : J) :=
        (Subgroup.mem_center_iff.1 (hcent (φ a : J) (φ a).2) (φ b : J)).symm
      show (φ a : J) * (φ b : J) * (φ a : J)⁻¹ * (φ b : J)⁻¹ = 1
      rw [hxy]
      group
    rw [hJ] at hcomm
    exact top_le_iff.1 hcomm
  have hcard := hcompl.card_mul
  rw [hker, Subgroup.card_top] at hcard
  have hP1 : Nat.card (P : Subgroup J) = 1 := by
    have hpos : 0 < Nat.card J := Nat.card_pos
    nlinarith
  exact absurd (Sylow.dvd_card_of_dvd_card P h) (by rw [hP1]; norm_num)

theorem le_hyperGamma_of_coprime {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (f : MulAut X) (hf : f ∈ E) (hf1 : f ≠ 1) (J : Subgroup X)
    (hJfix : ∀ g ∈ Subgroup.zpowers f, ∀ y ∈ J, g y = y)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) (h3 : ¬ 3 ∣ Nat.card J) :
    J ≤ seitzHyperGamma 3 E := by
  classical
  by_cases hD : Nat.card (resHom J E hJE).range = 3 ^ 2
  swap
  · exact le_hyperGamma_of_range_ne E hE hEc f hf hf1 J hJfix hJE hD
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥E →* MulAut J := resHom J E hJE with hρ
  have hDel : CFSG.Open.IsElemAbelian 3 ρ.range := isElemAbelian_range hE ρ
  haveI : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  haveI : Nontrivial ρ.range := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hD]
    norm_num
  haveI : IsElementaryAbelian 3 ρ.range :=
    { is_comm := hDel.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hDel.2 x x.2) }
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := ρ.range) (H := J)
    h3
  have hT : (⊤ : Subgroup J) ≤ (seitzHyperGamma 3 E).comap J.subtype := by
    rw [← hgen]
    refine iSup₂_le fun B hB => ?_
    intro y hy
    set ρD : ↥E →* ρ.range := ρ.rangeRestrict with hρD
    set F'' : Subgroup (MulAut X) := (B.comap ρD).map E.subtype with hF''
    have hF''E : F'' ≤ E := Subgroup.map_subtype_le _
    have hrel : F''.relIndex E = 3 := by
      have h1 : F''.subgroupOf E = B.comap ρD :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
      rw [Subgroup.relIndex, h1, Subgroup.index_comap_of_surjective B ρ.rangeRestrict_surjective]
      exact hB
    have hfix : (y : X) ∈ fixedPoints F'' := by
      intro φ hφ
      rw [hF'', Subgroup.mem_map] at hφ
      obtain ⟨b, hb, rfl⟩ := hφ
      have hy' := hy ⟨ρD b, hb⟩
      have hyJ : ρ b y = y := hy'
      have := congrArg (fun z : J => (z : X)) hyJ
      exact this
    exact fixedPoints_le_hyperGamma hF''E hrel hfix
  intro x hx
  exact hT (Subgroup.mem_top (⟨x, hx⟩ : ↥J))

end KSNotAll24

@[expose] def TwE6ComponentType {X : Type} [Group X] (J : Subgroup X) : Prop :=
  (¬ 3 ∣ Nat.card (Subgroup.center J) ∧
      ∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1) ∨
    NoPlane3 (J ⧸ Subgroup.center J) ∨ ¬ 3 ∣ Nat.card J

open KSNotAll24 in
theorem component_le_hyperGamma_of_plane' (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (f : MulAut X) (hf : f ∈ E) (hf1 : f ≠ 1)
    (J : Subgroup X) (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)))
    (hJT : TwE6ComponentType J) (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) :
    J ≤ seitzHyperGamma 3 E := by
  rcases hJT with ⟨hJ3, d, e, hdp, hex⟩ | hno | hcop
  · exact component_le_hyperGamma_of_plane hS E hE hEc f hf hf1 J hJ hJ3 d e hdp hex hJE
  · exact le_hyperGamma_of_range_ne E hE hEc f hf hf1 J
      (fun g hg y hy => hJ.1 hy g hg) hJE (card_range_ne_nine E hE J hJ.2.2.1 hJE hno)
  · exact le_hyperGamma_of_coprime E hE hEc f hf hf1 J
      (fun g hg y hy => hJ.1 hy g hg) hJE hcop

section Structure

set_option linter.unusedSectionVars false

@[expose] noncomputable def twE6MatFixDim (K : Type) [Field K] (σ : K ≃+* K)
    (h : twistedE6InndiagGL K σ) : ℕ :=
  Module.finrank K (LinearMap.ker (((h : ModGL TwistTag.E6.tag K) :
    Module.End K (RootModule TwistTag.E6.tag K)) - 1))

end Structure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
