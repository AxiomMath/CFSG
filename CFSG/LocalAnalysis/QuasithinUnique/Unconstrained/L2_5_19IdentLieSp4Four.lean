module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentA8
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial

section Setting

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.card_cent_eq (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X) :
    Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X ⊓
        Subgroup.centralizer ({(hs.conjAut : MulAut ↥X)} : Set (MulAut ↥X))) := by
  have hι := conj_injective_of_center_bot (hs.center_eq_bot_of_simple hsimple)
  rw [← hs.map_conj_eq_inner_inf_centralizer hsimple, Subgroup.card_map_of_injective hι]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

end Setting

open Ident

theorem tabIdentFor_sp4Four :
    TabIdentFor @FamSp4Four := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, hmodel⟩ := hX
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := id hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
  have := hsimple
  have : Finite (MulAut ↥X) :=
    Finite.of_injective (fun β : MulAut ↥X => (β : ↥X → ↥X)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hZ := hs.center_eq_bot_of_simple hsimple
  obtain ⟨L, hLW, hL, ⟨eL⟩⟩ := hs.exists_socle_conjAut hsimple
  have ha : orderOf (hs.conjAut : MulAut ↥X) = 2 := hs.orderOf_conjAut
  obtain ⟨p, f', hp, hp2, hf', hsrc⟩ := hs.ktype.exists_psl_two_source_quot eL
  let φ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X) ≃*
      StatedProj (StatedSp 2 F) := (innerEquiv hZ).symm.trans φ0
  obtain ⟨σ, hσ, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two
    (by norm_num : 1 ≤ 2) hF
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, -⟩ :=
    even_symplectic_two_exterior_square_automorphism (f := 2) (by norm_num) hF
  obtain ⟨ρ, -, -, -, -, -, -, -, -, -, -, -, -, hrow⟩ :=
    faithful_even_symplectic_socle_small_source_involution_selector
      (isSimpleGroup_inner hZ) (hs.exists_noncomm_inner hsimple)
      (centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL hp hp2 hf' (Or.inl hsrc)
      (r := 2) (e := 2) le_rfl (by norm_num) (by norm_num) hF φ
  obtain ⟨ρ₂, hinj₂, -, -, hlet⟩ := hrow φ σ hσ γ hγ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperm, -, h, -, -, hWC, -⟩ := hlet
  obtain ⟨e6⟩ := hperm
  have hC720 : Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) = 720 := by
    rw [hs.card_cent_eq hsimple]
    rw [← Subgroup.card_map_of_injective hinj₂, hWC,
      Subgroup.card_map_of_injective (MulAut.conj (SpChain.spInner 2 F h)).injective,
      Nat.card_congr e6.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hKC : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hs.comp.1
  have hdvd : Nat.card ↥K ∣ 720 := hC720 ▸ Subgroup.card_dvd_of_le hKC
  have hA6 : IsA6 K := isA6_of_card_dvd hs.ktype (by norm_num) hdvd (by norm_num) (by norm_num)
  have hK360 : Nat.card ↥K = 360 := hA6.card_eq
  have hKeq : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    set C := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
    set R := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C with hRdef
    have hKR : K ≤ R := le_perfectResidualOf hs.perfect_K hs.comp.1
    have hRC : R ≤ C := perfectResidualOf_le C
    have hRperf : ⁅R, R⁆ = R := perfectResidualOf_perfect C
    have hR720 : Nat.card ↥R ≤ 720 := by
      rw [← hC720]
      exact Subgroup.card_le_of_le hRC
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hKR
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        have : 0 < Nat.card ↥R := Nat.card_pos
        rw [hm, h0, mul_zero] at this
        exact lt_irrefl _ this
      · exact h0
    have hm2 : m ≤ 2 := by
      rw [hK360] at hm
      omega
    have hm1 : m = 1 := by
      by_contra hne1
      have hm2' : m = 2 := by omega
      subst hm2'
      have hRcard : Nat.card ↥R = 2 * Nat.card ↥K := by rw [hm, hK360]
      have hle := commutator_le_of_card_eq_two_mul hKR hRcard
      rw [hRperf] at hle
      have : Nat.card ↥R ≤ Nat.card ↥K := Subgroup.card_le_of_le hle
      rw [hRcard] at this
      omega
    subst hm1
    refine Subgroup.eq_of_le_of_card_ge hKR ?_
    rw [hm, mul_one]
  refine ⟨?_, hKeq, fun hbig => ?_, fun hl => ?_, fun _ => ?_⟩
  · rw [hZ]
    exact (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup ↥X))
  · have h1 := hbig.card_ge
    rw [hK360] at h1
    omega
  · have h1 := hl.card_eq
    rw [hK360] at h1
    omega
  · exact Or.inl ⟨hA6, hmodel⟩

end CFSG.QuasithinUnique.Id2519
