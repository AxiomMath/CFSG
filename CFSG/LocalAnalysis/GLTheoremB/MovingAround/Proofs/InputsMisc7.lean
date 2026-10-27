module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc5
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
import CFSG.Quasithin.Vol2.Ch11SKFIto

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185 (fixerAut mem_fixerAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Two

theorem fixerAut_eq_sylowFixingAut {K : Type} [Group K] (S : Subgroup K) :
    fixerAut S = CFSG.ClassicalInvolution.sylowFixingAut S := by
  ext α
  rw [mem_fixerAut, CFSG.ClassicalInvolution.mem_sylowFixingAut]

theorem eq_bot_of_normal_of_odd {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (N : Subgroup K) (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  haveI := hs
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hoddK : Odd (Nat.card K) := by
      rw [h, Subgroup.card_top] at hodd
      exact hodd
    haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddK
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

theorem hasNormalPComplement_two_fixerAut_of_simple {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (S : Subgroup K)
    (hS : CFSG.Open.fusionIsSylowIn 2 S ⊤) : CFSG.HasNormalPComplement 2 ↥(fixerAut S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 K := ⟨S, hS.2.1, fun {Q} hQ hle => hS.2.2 Q le_top hQ hle⟩
  obtain ⟨N, hN, hodd, hq⟩ := CFSG.ClassicalInvolution.GlaubermanAut.exists_normal_two_complement
    (fun N hN hodd => eq_bot_of_normal_of_odd hs hnab N hN hodd) hS.2.1 (Sylow.not_dvd_index S')
  rw [fixerAut_eq_sylowFixingAut]
  exact ⟨N, hN, Nat.coprime_two_left.2 hodd, hq⟩

theorem input7_10_1ResTwo_holds : InputsMisc5.Input7_10_1ResTwo := by
  intro K _ _ hs hnab _ _ S hS
  exact hasNormalPComplement_two_fixerAut_of_simple hs hnab S hS

end Two

section General

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem hasNormalPComplement_of_not_dvd_card {G : Type*} [Group G] [Finite G] [hp : Fact p.Prime]
    (h : ¬ p ∣ Nat.card G) : CFSG.HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, ?_, fun g => ⟨0, ?_⟩⟩
  · rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 h
  · haveI := QuotientGroup.subsingleton_quotient_top (G := G)
    exact Subsingleton.elim _ _

theorem hasNormalPComplement_fixerAut_of_forall_inner [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : Subgroup.center K = ⊥) (P : Sylow p K)
    (h : ∀ α : MulAut K, α ^ p = 1 → (∀ x ∈ (P : Subgroup K), α x = x) → α ∈ inner K) :
    CFSG.HasNormalPComplement p ↥(fixerAut (P : Subgroup K)) := by
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_exists]
  refine CFSG.Quasithin.Vol2.Ch11.SecS.KF.ito_normalPComplement hp2 fun c hc => ?_
  have hc' : (c : MulAut K) ^ p = 1 := by simpa using congrArg Subtype.val hc
  exact InputsMisc5.mem_center_fixerAut_of_inner hZ P c ⟨1, by rw [pow_one]; exact hc⟩
    (h c hc' (mem_fixerAut.1 c.2))

theorem hasNormalPComplement_fixerAut_of_hom [hp : Fact p.Prime] (hZ : Subgroup.center K = ⊥)
    (P : Sylow p K) {G' : Type*} [Group G'] [Finite G'] (ψ : MulAut K →* G')
    (hG' : CFSG.HasNormalPComplement p G')
    (h : ∀ α : MulAut K, (∃ k : ℕ, α ^ p ^ k = 1) → ψ α = 1 →
      (∀ x ∈ (P : Subgroup K), α x = x) → α ∈ inner K) :
    CFSG.HasNormalPComplement p ↥(fixerAut (P : Subgroup K)) := by
  obtain ⟨MO, hMOn, hMOc, hMOq⟩ := hG'
  haveI := hMOn
  set C : Subgroup (MulAut K) := fixerAut (P : Subgroup K) with hC
  let π : ↥C →* G' := ψ.comp C.subtype
  let N : Subgroup ↥C := MO.comap π
  haveI hNn : N.Normal := Subgroup.Normal.comap hMOn π
  refine InputsMisc5.hasNormalPComplement_of_normal (N := N) ?_ ?_
  · intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨k, hk⟩ := hMOq (QuotientGroup.mk (π c))
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show π (c ^ p ^ k) ∈ MO
      rw [map_pow]
      exact hk
  · refine InputsMisc5.hasNormalPComplement_of_pElements_central fun n hn => ?_
    obtain ⟨k, hk⟩ := hn
    have hck : (n : ↥C) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hπ1 : π n = 1 := by
      refine InputsMisc5.eq_one_of_pow_of_coprime (k := k) hMOc n.2 ?_
      rw [← map_pow, hck, map_one]
    have hinner : ((n : ↥C) : MulAut K) ∈ inner K :=
      h _ ⟨k, by simpa using congrArg Subtype.val hck⟩ hπ1 (mem_fixerAut.1 (n : ↥C).2)
    have hcen := InputsMisc5.mem_center_fixerAut_of_inner hZ P (n : ↥C) ⟨k, hck⟩ hinner
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hcen (m : ↥C)

theorem hasNormalPComplement_fixerAut_of_mulEquiv {M : Type} [Group M] [Finite M] (e : K ≃* M)
    (P : Subgroup K)
    (h : CFSG.HasNormalPComplement p ↥(fixerAut (P.map (e : K →* M)))) :
    CFSG.HasNormalPComplement p ↥(fixerAut P) := by
  have hmaps : ∀ α : ↥(fixerAut P), MulAut.congr e (α : MulAut K) ∈ fixerAut (P.map (e : K →* M)) := by
    intro α
    refine mem_fixerAut.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show e ((α : MulAut K) (e.symm (e x))) = e x
    rw [e.symm_apply_apply, (mem_fixerAut.1 α.2) x hx]
  let g : ↥(fixerAut P) →* ↥(fixerAut (P.map (e : K →* M))) :=
    ((MulAut.congr e).toMonoidHom.comp (fixerAut P).subtype).codRestrict _ hmaps
  refine InputsMisc5.hasNormalPComplement_of_injective g ?_ h
  intro a b hab
  apply Subtype.ext
  exact (MulAut.congr e).injective (congrArg Subtype.val hab)

theorem hasNormalPComplement_of_isMulCommutative {G : Type*} [Group G] [Finite G] [Fact p.Prime]
    (h : IsMulCommutative G) : CFSG.HasNormalPComplement p G :=
  InputsMisc5.hasNormalPComplement_of_pElements_central fun g _ =>
    Subgroup.mem_center_iff.2 fun x => h.is_comm.comm x g

end General

section Residues

open CFSG.Open (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

@[expose] def ResOddPSL : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedClassicalModel K .PSL n ℓ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p ∣ ℓ ^ f - 1 →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn p P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement p ↥(fixerAut P)

@[expose] def ResOddPSU : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedClassicalModel K .PSU n ℓ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p ∣ ℓ ^ f + 1 →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn p P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement p ↥(fixerAut P)

@[expose] def ResOddE6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (ℓ f : ℕ), ChevalleyExceptionalModel K .E6 ℓ f →
    3 ∣ ℓ ^ f - 1 →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn 3 P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement 3 ↥(fixerAut P)

@[expose] def ResOddTwE6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (ℓ f : ℕ), ChevalleyExceptionalModel K .twistedE6 ℓ f →
    3 ∣ ℓ ^ f + 1 →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn 3 P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement 3 ↥(fixerAut P)

@[expose] def ResOddD4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (ℓ f : ℕ), StatedClassicalModel K .POmegaPlus 4 ℓ f →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn 3 P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement 3 ↥(fixerAut P)

@[expose] def ResOddTrivial : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K → ¬ p ∣ Nat.card K →
      CFSG.HasNormalPComplement p (Outer K)

@[expose] def ResOddTrivialLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : CFSG.Open.StatedLieTag) (n ℓ f : ℕ), CFSG.Open.StatedLieAdmissible t n ℓ f →
      CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K → CFSG.HasNormalPComplement p (Outer K)

theorem input7_10_1ResOdd_of_nonab (hnonab : InputsMisc5.Input7_10_1ResOddNonab)
    (htriv : ResOddTrivial) : InputsMisc5.Input7_10_1ResOdd := by
  intro p hp hp2 K _ _ hs hnab hcat hO P hP hc
  rcases hc with rfl | hPnab
  · exfalso
    apply hO
    refine htriv p hp hp2 K hs hnab hcat fun hpK => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpK
    have hz : IsPGroup p (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
    have hbot := hP.2.2 (Subgroup.zpowers g) le_top hz bot_le
    have hg1 : g = 1 := by
      have := Subgroup.mem_zpowers g
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [hg1, orderOf_one] at hg
    exact hp.one_lt.ne hg
  · exact hnonab p hp hp2 K hs hnab hcat hO P hP hPnab

end Residues

section Triality

theorem isMulCommutative_outer_trialityD4 {T : Type} [Group T] {ℓ f : ℕ}
    (hT : CFSG.Blueprint.ChevalleyExceptionalModel T .trialityD4 ℓ f) :
    IsMulCommutative (Outer T) := by
  obtain ⟨⟨hℓ, hf, -⟩, hm⟩ := hT
  have hm' : CFSG.Blueprint.TwistedChevalleyModel T .D4 (ℓ ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hm'
  have key : ∃ Θ : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      Θ.ker = inner (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) ∧ IsCyclic (K ≃+* K) := by
    by_cases h2 : ℓ = 2
    · subst h2
      obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨Θ, hker, hcyc⟩
    · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ
      exact ⟨Θ, hker, hcyc⟩
  obtain ⟨Θ, hker, hcyc⟩ := key
  have hC := (QuotientGroup.lift _ Θ hker.ge).isMulCommutative_of_isCyclic_of_ker_le_center
    (by
      intro x hx
      rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self, Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _)
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
  rw [map_mul, map_mul]
  exact hC.is_comm.comm _ _

end Triality

section Dispatch

open CFSG.Open (StatedLieTag StatedClassicalModel)
open CFSG.Blueprint (classicalTags chevalleyExceptionalTags ChevalleyExceptionalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

theorem input7_10_1ResOddNonab_of_residues (hPSL : ResOddPSL) (hPSU : ResOddPSU) (hE6 : ResOddE6)
    (hTwE6 : ResOddTwE6) (hD4 : ResOddD4) : InputsMisc5.Input7_10_1ResOddNonab := by
  intro p hp hp2 K _ _ hs hnab hcat _ P hP hPnab
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup K := hs
  have hZ := InputsMisc5.center_eq_bot_of_simple hs hnab
  let S : Sylow p K := ⟨P, hP.2.1, fun {Q} hQ hle => hP.2.2 Q le_top hQ hle⟩
  have hSidx : ¬ p ∣ P.index := Sylow.not_dvd_index S
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    exact hPnab ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hpK : p ∣ Nat.card K := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP.2.1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hP1 ((Subgroup.eq_bot_iff_card P).2 hk)
    exact (hk ▸ dvd_pow_self p hk0).trans (Subgroup.card_subgroup_dvd_card P)
  have hout : ¬ p ∣ Nat.card (Outer K) → CFSG.HasNormalPComplement p ↥(fixerAut P) := fun h =>
    InputsMisc5.hasNormalPComplement_fixerAut_of_outer hZ S (hasNormalPComplement_of_not_dvd_card h)
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · apply hout
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [classicalTags] at h
      · simp [chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine hout fun hd => ?_
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · have hcl : t ∈ classicalTags → StatedClassicalModel K t n ℓ f := hmodel.statedClassicalModel
      have hch : t ∈ chevalleyExceptionalTags → ChevalleyExceptionalModel K t ℓ f :=
        hmodel.chevalleyExceptionalModel
      by_cases hdiv : p ∣ lieOrderDivisor t n (ℓ ^ f)
      · rcases CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.cases_of_dvd_lieOrderDivisor
            hp hp2 hdiv with
          ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩ | ⟨rfl, rfl, h3q⟩ | ⟨rfl, rfl, h3q⟩
        · exact hPSL K hs hnab n ℓ f (hcl (by simp [classicalTags])) p hp hp2 hpn hpq P hP hPnab
        · exact hPSU K hs hnab n ℓ f (hcl (by simp [classicalTags])) p hp hp2 hpn hpq P hP hPnab
        · exact hE6 K hs hnab ℓ f (hch (by simp [chevalleyExceptionalTags])) h3q P hP hPnab
        · exact hTwE6 K hs hnab ℓ f (hch (by simp [chevalleyExceptionalTags])) h3q P hP hPnab
      · by_cases hD4' : t = .POmegaPlus ∧ n = 4 ∧ p = 3
        · obtain ⟨rfl, rfl, rfl⟩ := hD4'
          exact hD4 K hs hnab ℓ f (hcl (by simp [classicalTags])) P hP hPnab
        · by_cases hT3 : t = .trialityD4 ∧ p = 3
          · obtain ⟨rfl, rfl⟩ := hT3
            exact InputsMisc5.hasNormalPComplement_fixerAut_of_outer hZ S
              (hasNormalPComplement_of_isMulCommutative
                (isMulCommutative_outer_trialityD4 (hch (by simp [chevalleyExceptionalTags]))))
          · exact hasNormalPComplement_fixerAut_of_forall_inner hp2 hZ S fun α hαp hαS =>
              CFSG.AGLEmbedding.OuterSylow.mem_inner_of_lie_model_cyc
                CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
                CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds
                hadm hmodel ht hp hp2 hpK hdiv hD4' hT3 hP.2.1 hSidx hαp hαS
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    apply hout
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem resOddTrivial_of_lie (hLie : ResOddTrivialLie) : ResOddTrivial := by
  intro p hp hp2 K _ _ hs hnab hcat hpK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup K := hs
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · apply hasNormalPComplement_of_not_dvd_card
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [classicalTags] at h
      · simp [chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine hasNormalPComplement_of_not_dvd_card fun hd => ?_
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · exact hLie K hs hnab t n ℓ f hadm hmodel ht p hp hp2 hpK
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    apply hasNormalPComplement_of_not_dvd_card
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

end Dispatch

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7
