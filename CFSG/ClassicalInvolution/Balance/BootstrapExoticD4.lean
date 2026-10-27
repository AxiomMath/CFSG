module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4Sl3
public import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2
public import CFSG.ClassicalInvolution.Balance.QNineShape
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectExc
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Tags
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairModels
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.ClassicalInvolution.RouteD.LocalPair
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.TwistedD4
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section NoSurjection

variable {K F : Type} [Field K] [Finite K] [Field F] [Finite F]

omit [Finite K] in
theorem steinberg_sl2Upper_add (a b : K) :
    CFSG.LieType.Steinberg.sl2Upper (a + b) =
      CFSG.LieType.Steinberg.sl2Upper a * CFSG.LieType.Steinberg.sl2Upper b := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem not_surjective_sl2_of_card_lt (h4 : 4 ≤ Nat.card K)
    (hcard : Nat.card SL(2, F) < Nat.card K) (hF : 1 < Nat.card SL(2, F))
    (ψ : SL(2, K) →* SL(2, F)) : ¬Function.Surjective ψ := by
  intro hsurj
  have hq : CFSG.IsQuasisimple SL(2, K) :=
    ModelFacts.native_isQuasisimple (isQuasisimple_specialLinearGroup_two h4)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
    (MonoidHom.normal_ker ψ).isSubnormal with h | h
  · have hsub : Subsingleton SL(2, F) := ⟨fun a b => by
      obtain ⟨u, rfl⟩ := hsurj a
      obtain ⟨v, rfl⟩ := hsurj b
      have hu : u ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top u
      have hv : v ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top v
      rw [MonoidHom.mem_ker.1 hu, MonoidHom.mem_ker.1 hv]⟩
    have := Finite.card_le_one_iff_subsingleton.2 hsub
    omega
  · have hinj : Function.Injective fun c : K => ψ (CFSG.LieType.Steinberg.sl2Upper c) := by
      intro c d hcd
      have hmul : CFSG.LieType.Steinberg.sl2Upper (c - d) *
          CFSG.LieType.Steinberg.sl2Upper d = CFSG.LieType.Steinberg.sl2Upper c := by
        rw [← steinberg_sl2Upper_add, sub_add_cancel]
      have hker : CFSG.LieType.Steinberg.sl2Upper (c - d) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : ψ (CFSG.LieType.Steinberg.sl2Upper (c - d)) *
            ψ (CFSG.LieType.Steinberg.sl2Upper d) = ψ (CFSG.LieType.Steinberg.sl2Upper d) := by
          rw [← map_mul, hmul]
          exact hcd
        exact mul_eq_right.1 h1
      have hc := h hker
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
      obtain ⟨r, -, hr⟩ := hc
      have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hr
      simp [CFSG.LieType.Steinberg.coe_sl2Upper] at h01
      exact sub_eq_zero.1 h01.symm
    have := Nat.card_le_card_of_injective _ hinj
    omega

end NoSurjection

section Lift

variable {A B C X : Type*} [Group A] [Group B] [Group C] [Group X]

theorem exists_hom_of_range_eq (f : A →* X) (g : B →* X) (hrange : f.range = g.range)
    (φ : B →* C) (hker : g.ker ≤ φ.ker) : ∃ ψ : A →* C, ψ.range = φ.range := by
  classical
  have hmem : ∀ a : A, ∃ b : B, g b = f a := fun a => by
    have : f a ∈ g.range := hrange ▸ ⟨a, rfl⟩
    exact this
  choose b hb using hmem
  have hφ : ∀ b₁ b₂ : B, g b₁ = g b₂ → φ b₁ = φ b₂ := fun b₁ b₂ h => by
    have h1 : b₁⁻¹ * b₂ ∈ g.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker h1
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  refine ⟨{ toFun := fun a => φ (b a), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · have h1 : g (b 1) = g 1 := by rw [hb, map_one, map_one]
    simpa using hφ _ _ h1
  · intro a a'
    have h1 : g (b (a * a')) = g (b a * b a') := by rw [hb, map_mul f, map_mul g, hb, hb]
    show φ (b (a * a')) = φ (b a) * φ (b a')
    rw [hφ _ _ h1, map_mul]
  · ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨b a, rfl⟩
    · rintro ⟨b₀, rfl⟩
      have h1 : g b₀ ∈ f.range := hrange ▸ ⟨b₀, rfl⟩
      obtain ⟨a, ha⟩ := h1
      exact ⟨a, by
        show φ (b a) = φ b₀
        exact hφ _ _ (by rw [hb, ha])⟩

end Lift

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_surjective_of_locImg (hΩ : InClass p f Ω) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {A : Type} [Group A] (u : A →* locQuot Ω x)
    (hu : u.range = locImg Ω x L) :
    ∃ ψ : A →* SL(2, GaloisField p f), Function.Surjective ψ := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hLY : L ≤ locLayer Ω x := le_centralizingLayer hL
  let τ : ↥L →* locQuot Ω x :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).comp
      (Subgroup.inclusion hLY)
  have hτ : τ.range = locImg Ω x L := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLY l, l.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m.1, hm⟩, rfl⟩
  have hker : τ.ker ≤ classicalInvolutionOddCore ↥L := by
    have h1 : τ.ker =
        (classicalInvolutionOddCore ↥(locLayer Ω x)).comap (Subgroup.inclusion hLY) := by
      ext l
      simp [τ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [h1]
    refine CFSG.ComponentClassification.OddCore.maximal ↥L _
      (Subgroup.Normal.comap inferInstance _) ?_
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥(locLayer Ω x)).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hLY))
  let φ : ↥L →* SL(2, GaloisField p f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥L))
  have hφker : τ.ker ≤ φ.ker := fun l hl => by
    have h1 : l ∈ classicalInvolutionOddCore ↥L := hker hl
    rw [MonoidHom.mem_ker]
    have h2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥L) l = 1 :=
      (QuotientGroup.eq_one_iff l).2 h1
    show e (QuotientGroup.mk' (classicalInvolutionOddCore ↥L) l) = 1
    rw [h2, map_one]
  obtain ⟨ψ, hψ⟩ := exists_hom_of_range_eq u τ (hu.trans hτ.symm) φ hφker
  have hφs : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥L))
  exact ⟨ψ, MonoidHom.range_eq_top.1 (hψ.trans (MonoidHom.range_eq_top.2 hφs))⟩

end Local

section Datum

variable {K : Type} [Field K] (σ : K →+* K)

theorem twistedDatum_weylAction_zero :
    weylAction (twistedDatum σ).isFiniteType (simple .G2 g2Short) (g2Hex 0) = g2Hex 2 :=
  (simple_smul (τ := .G2) g2Short (g2Hex 0)).trans g2Hex_reflect_zero

theorem twistedDatum_isLongest_hex_two (h0 : ModelFacts.IsLongestRoot (twistedDatum σ) (g2Hex 0)) :
    ModelFacts.IsLongestRoot (twistedDatum σ) (g2Hex 2) := by
  have h := ModelFacts.IsLongest.map_weylAction h0 (simple .G2 g2Short)
  rwa [twistedDatum_weylAction_zero] at h

theorem twistedDatum_isPartner_hex :
    ModelFacts.IsPartner (twistedDatum σ).isFiniteType (g2Hex 0) (g2Hex 2) := by
  have h : ModelFacts.IsPartner (twistedDatum σ).isFiniteType (g2Hex 0)
      (weylAction (twistedDatum σ).isFiniteType (simple .G2 g2Short) (g2Hex 0)) := by
    rw [g2Hex_zero]
    exact ModelFacts.isPartner_single_reflection (hA := (twistedDatum σ).isFiniteType)
      (i := g2Long) (j := g2Short)
      (by show Tag.G2.cartan g2Long g2Short * Tag.G2.cartan g2Short g2Long = 3; decide)
  rwa [twistedDatum_weylAction_zero] at h

theorem exists_hom_range_short_trialityD4 (hσ : ∀ c, σ (σ (σ c)) = c)
    {n : Fin (twistedDatum σ).rank → ↥(twistedGroup σ)}
    {H : Fin (twistedDatum σ).rank → Subgroup ↥(twistedGroup σ)}
    (hct : IsCTGroupDatum (coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum σ).isFiniteType) (twistedDatum σ).roots
      (twistedDatum σ).rootGroup n H)
    (g : ↥(twistedGroup σ)) (w : WeylGroup .G2) :
    ∃ ι : SL(2, K) →* ↥(twistedGroup σ),
      ι.range = conjSub g ((twistedDatum σ).rootGroup (w • Pi.single (ng 1) 1) ⊔
        (twistedDatum σ).rootGroup (-(w • Pi.single (ng 1) 1))) := by
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne hct w
  have hb : (Pi.single (ng 1) 1 : Fin Tag.G2.rank → ℤ) ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_single .G2 (ng 1)
  have h2 : (twistedDatum σ).rootGroup (w • Pi.single (ng 1) 1) ⊔
      (twistedDatum σ).rootGroup (-(w • Pi.single (ng 1) 1)) =
      (rankOne (twistedRootGroup σ) (ng 1)).map (MulAut.conj h).toMonoidHom := (hh _ hb).symm
  refine ⟨((MulAut.conj (g * h)).toMonoidHom).comp (slShort σ hσ), ?_⟩
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := MonoidHom.ext fun y => by simp [mul_assoc]
  rw [MonoidHom.range_comp, ← ModelFacts.rankOne_short_eq_range hσ]
  unfold conjSub
  rw [h2, Subgroup.map_map _ (MulAut.conj g).toMonoidHom (MulAut.conj h).toMonoidHom, hcomp]

end Datum

section Model

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_standardPair_partner_trialityD4 {n e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n p e)
    {γ : Fin (modelUniv .trialityD4 n p e hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D γ) :
    ∃ δ : Fin (modelUniv .trialityD4 n p e hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D δ ∧
      ModelFacts.IsPartner (modelUniv .trialityD4 n p e hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p e) W
        ((modelUniv .trialityD4 n p e hp.out).D.rootGroup γ ⊔
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-γ))
        ((modelUniv .trialityD4 n p e hp.out).D.rootGroup δ ⊔
          (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-δ)) := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  obtain ⟨_, _, hct, -⟩ := ModelFacts.hasBruhatDatum .trialityD4 n p e hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := ModelFacts.cartanOK .trialityD4 n p e hp.out trivial hadm
  have h0 : ModelFacts.IsLongestRoot
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)) (g2Hex 0) := by
    rw [g2Hex_zero]
    exact ModelFacts.isLongestRoot_single .trialityD4 n p e hp.out trivial hadm (ng 0) rfl
  obtain ⟨W, hW⟩ := d4_standardPair_base hσ
  have hcard : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) =
      Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    exact ModelFacts.card_fixedField_iterateFrobenius he
  obtain ⟨eF⟩ := ModelFacts.nonempty_ringEquiv_of_natCard_eq hcard
  exact ModelFacts.exists_standardPair_partner hct hirr hratio h0
    (twistedDatum_isLongest_hex_two _ h0) (twistedDatum_isPartner_hex _)
    ⟨W, LinearBlockStandardPair.of_ringEquiv eF hW⟩ hγ

theorem leviBlockImage_conj_rankOne_trialityD4 {n e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n p e)
    {γ : Fin (modelUniv .trialityD4 n p e hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D γ)
    (g : (modelUniv .trialityD4 n p e hp.out).K) :
    LeviBlockImage p e (conjSub g ((modelUniv .trialityD4 n p e hp.out).D.rootGroup γ ⊔
      (modelUniv .trialityD4 n p e hp.out).D.rootGroup (-γ))) := by
  obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_trialityD4 hadm hγ
  exact Or.inl ⟨_, _, ModelFacts.linearBlockStandardPair_map_conj hW g⟩

theorem fundamental_trialityD4_cases {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .trialityD4) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      LeviBlockImage p e R ∨
        ∃ ι : SL(2, GaloisField p (3 * e)) →* (modelUniv t n p e Fact.out).K, ι.range = R := by
  subst ht
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have he : 1 ≤ e := hadm.2.1
  have hroot : IsRoot .G2 γ := by
    have h : γ ∈ (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)).roots := by
      rcases hγ with h | ⟨h', -⟩ | ⟨-, h⟩
      · exact h.1
      · exact absurd h' (by decide)
      · exact h
    rwa [twistedDatum_roots] at h
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hroot
  by_cases hj : j = ng 0
  · subst hj
    left
    have h0 : ModelFacts.IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D
        (Pi.single (ng 0) 1) :=
      ModelFacts.isLongestRoot_single .trialityD4 n p e hp.out trivial hadm (ng 0) rfl
    have hlong : ModelFacts.IsLongestRoot (modelUniv .trialityD4 n p e hp.out).D γ := by
      rw [← hw]
      exact ModelFacts.IsLongest.map_weylAction h0 w
    exact leviBlockImage_conj_rankOne_trialityD4 hadm hlong g
  · have hj' : j = ng 1 := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
    subst hj'
    subst hw
    right
    have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), pow_mul']
    have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
      hK (fun c => iterateFrobenius_def p e c)
    obtain ⟨_, _, hct, -⟩ := ModelFacts.hasBruhatDatum .trialityD4 n p e hp.out trivial hadm
    exact exists_hom_range_short_trialityD4 _ hσ hct g w

end Model

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem eq_three_and_two_of_pow_eq_nine (h9 : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h9
  have hdvd : p ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
    exact dvd_pow_self p hf
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)
  refine ⟨hp3, ?_⟩
  subst hp3
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ f = 3 ^ 2 by rw [h9])

theorem exists_member_leviBlockImage_of_trialityD4 (hΩ : InClass p f Ω) (h9 : p ^ f = 9)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (ht : D.tag i = .trialityD4) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨hp3, hf2⟩ := eq_three_and_two_of_pow_eq_nine h9
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨-, h⟩
    · exact h
    · omega
  have he2 : D.exp i = 2 := hexp.trans hf2
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  refine ⟨L, hL, ?_⟩
  rcases fundamental_trialityD4_cases (D.admissible i) ht R hR with hlev | ⟨ι, hι⟩
  · rw [hLR]
    exact LeviBlockImage.congr_exp hexp (LeviBlockImage.map (by rw [hexp, h9]; norm_num) hlev
      (D.hom i) (D.ker_le_center i))
  · exfalso
    obtain ⟨ψ, hψ⟩ := exists_surjective_of_locImg hΩ hL ((D.hom i).comp ι)
      (by rw [MonoidHom.range_comp, hι, hLR])
    have hKcard : Nat.card (GaloisField p (3 * D.exp i)) = 729 := by
      rw [GaloisField.card p _ (by omega), he2, hp3]
      norm_num
    have hFcard : Nat.card (GaloisField p f) = 9 := by
      rw [GaloisField.card p f (by omega), h9]
    have hSL : Nat.card SL(2, GaloisField p f) = 720 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFcard]
      norm_num
    exact not_surjective_sl2_of_card_lt (by omega) (by omega) (by omega) ψ hψ

end Component

end CFSG.ClassicalInvolution.Balance
