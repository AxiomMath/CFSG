module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Coprime

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem le_trivialOnQuot_of_sylCent (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {M : Subgroup G} (hM : M ∈ Ω)
    (hT : ∃ T : Subgroup G, IsSylow2In T M ∧ T ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ trivialOnQuot M := by
  intro a ha
  refine TwinADescent3.mem_tq_of_sylCent hΩ h2 hM ?_
  obtain ⟨T, hT, hTA⟩ := hT
  exact ⟨T, hT, hTA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))⟩

theorem exists_isSylow2In_inf_centralizer_A {J : Subgroup G} {z : G} (hA2 : IsPGroup 2 ↥A)
    (hAJ : A ≤ trivialOnQuot J) (hAz : ∀ a ∈ A, a * z = z * a) :
    ∃ P : Subgroup G, IsSylow2In P (J ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      P ≤ Subgroup.centralizer (A : Set G) := by
  set D : Subgroup G := J ⊓ Subgroup.centralizer ({z} : Set G) with hD
  set O : Subgroup G := oddCoreIn J ⊓ D with hO
  have hAz' : A ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAz a ha)
  have hOD : O ≤ D := inf_le_right
  have hOnorm : D ≤ Subgroup.normalizer (O : Set G) := by
    intro d hd
    have key : ∀ d ∈ D, ∀ h ∈ O, d * h * d⁻¹ ∈ O := by
      intro d hd h hh
      have hdJ' : d ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hd.1
      exact ⟨conj_mem_oddCoreIn_of_mem_normalizer hdJ' hh.1, D.mul_mem (D.mul_mem hd hh.2)
        (D.inv_mem hd)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key d hd h hh, fun hh => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hh
    simpa [mul_assoc] using this
  have hOodd : Odd (Nat.card O) :=
    (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hOle : O ≤ oddCoreOf D := le_oddCoreOf_of_normal hOD hOnorm hOodd
  have hcomm : ⁅A, D⁆ ≤ oddCoreOf D := by
    refine le_trans (Subgroup.commutator_le.mpr fun a ha x hx => ?_) hOle
    have haJ := hAJ ha
    have h1 : ⁅a, x⁆ ∈ oddCoreIn J := (mem_trivialOnQuot_iff.mp haJ).2 x hx.1
    have haN : a ∈ Subgroup.normalizer (J : Set G) := (mem_trivialOnQuot_iff.mp haJ).1
    have h2J : ⁅a, x⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp haN x).mp hx.1) (J.inv_mem hx.1)
    have h2z : ⁅a, x⁆ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.centralizer {z}).mul_mem
        ((Subgroup.centralizer {z}).mul_mem
          ((Subgroup.centralizer {z}).mul_mem (hAz' ha) hx.2) ((Subgroup.centralizer {z}).inv_mem
            (hAz' ha))) ((Subgroup.centralizer {z}).inv_mem hx.2)
    exact ⟨h1, h2J, h2z⟩
  exact AscE184Sect.exists_isSylow2In_centralizer hA2 hcomm

end Coprime

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {C : Subgroup G}

@[expose] def coreFam (Ω : Set (Subgroup G)) (C : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) ∧ L = tightCore (J ⊓ C)}

theorem isSylow2In_core_iff {K : Subgroup G} (hK : ∃ P : Subgroup G, IsSylow2In P K ∧ P ≤ C)
    {V : Subgroup G} : IsSylow2In V (tightCore (K ⊓ C)) ↔ IsSylow2In V K ∧ V ≤ C := by
  obtain ⟨P, hP, hPC⟩ := hK
  have hPK : P ≤ tightCore (K ⊓ C) := le_tightCore_of_isPGroup (le_inf hP.1 hPC) hP.2.1
  constructor
  · intro hV
    have hVK : V ≤ K := hV.1.trans ((tightCore_le _).trans inf_le_left)
    have hVc : V ≤ C := hV.1.trans ((tightCore_le _).trans inf_le_right)
    have hle : Nat.card P ≤ Nat.card V := hV.natCard_le hP.2.1 hPK
    exact ⟨hP.of_natCard_le hV.2.1 hVK hle, hVc⟩
  · rintro ⟨hVK, hVc⟩
    exact ⟨le_tightCore_of_isPGroup (le_inf hVK.1 hVc) hVK.2.1, hVK.2.1,
      fun V' hV'K hV'2 hVV' =>
        hVK.2.2 V' (hV'K.trans ((tightCore_le _).trans inf_le_left)) hV'2 hVV'⟩

theorem mem_USet_of_core {U : Subgroup G} (hU : U ∈ USet (coreFam Ω C)) :
    U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨K, hK, hKC, rfl⟩ := hL
  have hRK : IsSylow2In R K := ((isSylow2In_core_iff hKC).mp hRL).1
  exact ⟨R, mem_RSet_of_isSylow2In hK hRK, hUR, hcyc, hidx⟩

theorem clauses_coreFam {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (C : Subgroup G) :
    TwinEdge.Fam.Clauses (coreFam Ω C) := by
  refine
    { omega1 := ?_, omega2 := ?_, omega3 := ?_, omega4 := ?_, omega5 := ?_ }
  · rintro _ ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩
    obtain ⟨z, hz, hzm, hS, hnc⟩ := TwinEdge.Fam.member_data hΩ hJ hP hPC
    exact ⟨⟨z, isUniqueInvolution_mono hz ((tightCore_le _).trans inf_le_left) hzm⟩, P, hS, hnc⟩
  · rintro _ ⟨J, hJ, -, rfl⟩
    exact Or.inl (tightCore_tightCore _)
  · rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ Q Q' hQ hQ'
    obtain ⟨-, -, -, hS₁, -⟩ := TwinEdge.Fam.member_data hΩ hJ₁ hP₁ hP₁C
    obtain ⟨-, -, -, hS₂, -⟩ := TwinEdge.Fam.member_data hΩ hJ₂ hP₂ hP₂C
    rw [TwinEdge.Fam.natCard_eq_of_isSylow2In hS₁ hQ, TwinEdge.Fam.natCard_eq_of_isSylow2In hS₂ hQ']
    exact hΩ.omega3 J₁ hJ₁ J₂ hJ₂ P₁ P₂ hP₁ hP₂
  · rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ hne
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 J₁ hJ₁ J₂ hJ₂ hJJ
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hle₂ : tightCore (J₂ ⊓ C) ≤ J₂ := (tightCore_le _).trans inf_le_left
    have hle : tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) ≤ J₁ ⊓ J₂ := inf_le_inf hle₁ hle₂
    have hdvd : Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) ∣ Nat.card ↥(J₁ ⊓ J₂) :=
      Subgroup.card_dvd_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpos' : Nat.card ↥(J₁ ⊓ J₂) ≠ 0 := Nat.card_pos.ne'
    have hval : padicValNat 2 (Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C))) ≤
        padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) := by
      rw [← padicValNat_dvd_iff_le hpos']
      exact (pow_padicValNat_dvd).trans hdvd
    refine ⟨hval.trans h1, fun heq => ?_⟩
    have h2dvd : 2 ∣ Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) :=
      dvd_of_one_le_padicValNat heq.ge
    have hJJ1 : padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) = 1 :=
      le_antisymm h1 (one_le_padicValNat_of_dvd hpos' (h2dvd.trans hdvd))
    have hcomm := h2 hJJ1
    have hc12 : ⁅J₁, J₂⁆ ≤ J₂ := hcomm.trans (inf_le_right.trans (oddCoreOf_le_self J₂))
    have hc21 : ⁅J₂, J₁⁆ ≤ J₁ := by
      rw [Subgroup.commutator_comm]
      exact hcomm.trans (inf_le_left.trans (oddCoreOf_le_self J₁))
    have hN1 : tightCore (J₂ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₁ ⊓ C) : Set G) :=
      TwinEdge.Fam.tightCore_inf_le_normalizer C hc21
    have hN2 : tightCore (J₁ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₂ ⊓ C) : Set G) :=
      TwinEdge.Fam.tightCore_inf_le_normalizer C hc12
    have hcR : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤
        tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have hb' : b * a⁻¹ * b⁻¹ ∈ tightCore (J₁ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN1 hb) a⁻¹).mp (Subgroup.inv_mem _ ha)
        have := Subgroup.mul_mem _ ha hb'
        simpa [mul_assoc] using this
      · have ha' : a * b * a⁻¹ ∈ tightCore (J₂ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN2 ha) b).mp hb
        exact Subgroup.mul_mem _ ha' (Subgroup.inv_mem _ hb)
    have hcJ : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf J₁ ⊓ oddCoreOf J₂ :=
      (Subgroup.commutator_mono hle₁ hle₂).trans hcomm
    have hRo : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₁ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_left) (hcJ.trans inf_le_left)).trans (inf_oddCoreOf_le hle₁)
    have hRo' : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₂ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_right) (hcJ.trans inf_le_right)).trans (inf_oddCoreOf_le hle₂)
    exact le_inf hRo hRo'
  · rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ hne z hz v hv hnc hv2 hvz
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨z₀, hz₀, hz₀m, -, -⟩ := TwinEdge.Fam.member_data hΩ hJ₁ hP₁ hP₁C
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hzz : z = z₀ := hz.eq (isUniqueInvolution_mono hz₀ hle₁ hz₀m)
    subst hzz
    have hvJ₂C : v ∈ J₂ ⊓ C := tightCore_le _ hv
    have hnc' : ¬ ∀ w ∈ J₂, v * w = w * v := fun h =>
      hnc fun w hw => h w (((tightCore_le _).trans inf_le_left) hw)
    have hn := hΩ.omega5 J₁ hJ₁ J₂ hJ₂ hJJ z hz₀ v hvJ₂C.1 hnc' hv2 hvz
    have hvC : v ∈ C := hvJ₂C.2
    have hconj : conjSub v (J₁ ⊓ C) = J₁ ⊓ C := by
      rw [conjSub_inf, tl3_conjSub_eq_of_mem_normalizer hn, conjSub_eq_self_of_mem hvC]
    exact mem_normalizer_of_conjSub_eq
      (conjSub_tightCore_of_mem_normalizer (mem_normalizer_of_conjSub_eq hconj))

end Core

section AEmpty

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem not_mem_omegaNbr_of_core (hΩ : HypOmegaGen Ω) (hA2 : IsPGroup 2 ↥A)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G))
    (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z)
    (hzK : z ∈ tightCore (K ⊓ Subgroup.centralizer (A : Set G)))
    (h : ¬ ∃ T : Subgroup G, IsSylow2In T (tightCore (J ⊓ Subgroup.centralizer (A : Set G))) ∧
        T ≤ Subgroup.normalizer ((tightCore (K ⊓ Subgroup.centralizer (A : Set G)) :
          Subgroup G) : Set G)) :
    J ∉ omegaNbr Ω K := by
  rintro ⟨-, -, R', hR', hR'J, hR'N⟩
  have hR'syl : IsSylow2In R' J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hR' hR'J
  have hR'z : R' ≤ Subgroup.centralizer ({z} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' hz hR'N
  have hzA : ∀ a ∈ A, a * z = z * a := fun a ha =>
    ((Subgroup.mem_centralizer_iff.mp ((tightCore_le _).trans inf_le_right hzK)) a ha)
  have hAJ := le_trivialOnQuot_of_sylCent hΩ h2 hJ hJC
  obtain ⟨P, hPD, hPc⟩ := exists_isSylow2In_inf_centralizer_A hA2 hAJ hzA
  have hR'D : R' ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := le_inf hR'J hR'z
  have hle : Nat.card R' ≤ Nat.card P := hPD.natCard_le hR'syl.2.1 hR'D
  have hPJ : IsSylow2In P J := hR'syl.of_natCard_le hPD.2.1 (hPD.1.trans inf_le_left) hle
  have hPJc : IsSylow2In P (tightCore (J ⊓ Subgroup.centralizer (A : Set G))) :=
    (isSylow2In_core_iff hJC).mpr ⟨hPJ, hPc⟩
  have h3 : 3 ≤ Nat.card P := by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hR'
    omega
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ hKJ hz hPJ.1 hPJ.2.1 h3
      (hPD.1.trans inf_le_right)
  have hPKc : P ≤ Subgroup.normalizer
      ((tightCore (K ⊓ Subgroup.centralizer (A : Set G)) : Subgroup G) : Set G) := by
    intro b hb
    have hb' : b ∈ Subgroup.normalizer
        ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf' (hPK hb) (Subgroup.le_normalizer (hPc hb))
    exact mem_normalizer_of_conjSub_eq (conjSub_tightCore_of_mem_normalizer hb')
  exact h ⟨P, hPJc, hPKc⟩

@[expose] def NbrCore (Ω : Set (Subgroup G)) (C : Subgroup G) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) → K ≠ J → ∀ z : G,
    IsUniqueInvolution K z → z ∈ tightCore (K ⊓ C) →
      (¬ ∃ T : Subgroup G, IsSylow2In T (tightCore (J ⊓ C)) ∧
        T ≤ Subgroup.normalizer ((tightCore (K ⊓ C) : Subgroup G) : Set G)) → J ∉ omegaNbr Ω K

theorem nbrCore_centralizer (hΩ : HypOmegaGen Ω) (hA2 : IsPGroup 2 ↥A)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    NbrCore Ω (Subgroup.centralizer (A : Set G)) :=
  fun _ hK _ hJ hJC hKJ _ hz hzK h =>
    not_mem_omegaNbr_of_core hΩ hA2 h2 hK hJ hJC hKJ hz hzK h

variable {C X : Subgroup G}

theorem cfg64_of_core (hΩ : HypOmegaGen Ω) (hN : NbrCore Ω C)
    (hcX : ∀ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) → tightCore (J ⊓ C) ≤ X)
    {K J : Subgroup G} (hK : K ∈ Ω) (hKC : ∃ P : Subgroup G, IsSylow2In P K ∧ P ≤ C) (hJ : J ∈ Ω)
    (hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) {zK zJ u v : ↥X} {R T : Subgroup ↥X}
    (h : Cfg64 (restrictFamily (coreFam Ω C) X) ((tightCore (K ⊓ C)).subgroupOf X)
      ((tightCore (J ⊓ C)).subgroupOf X) zK zJ u v R T) :
    Cfg64 Ω K J (zK : G) (zJ : G) (u : G) (v : G) (R.map X.subtype) (T.map X.subtype) := by
  have hKc : tightCore (K ⊓ C) ∈ coreFam Ω C := ⟨K, hK, hKC, rfl⟩
  have hJc : tightCore (J ⊓ C) ∈ coreFam Ω C := ⟨J, hJ, hJC, rfl⟩
  have hKY : tightCore (K ⊓ C) ≤ X := hcX K hK hKC
  have hJY : tightCore (J ⊓ C) ≤ X := hcX J hJ hJC
  have hKl : tightCore (K ⊓ C) ≤ K := (tightCore_le _).trans inf_le_left
  have hJl : tightCore (J ⊓ C) ≤ J := (tightCore_le _).trans inf_le_left
  have hKJ : K ≠ J := fun e => h.hKJ (by rw [e])
  have hzKc : IsUniqueInvolution (tightCore (K ⊓ C)) (zK : G) :=
    isUniqueInvolution_of_subgroupOf h.hz hKY
  have hzJc : IsUniqueInvolution (tightCore (J ⊓ C)) (zJ : G) :=
    isUniqueInvolution_of_subgroupOf h.hj hJY
  have hzK : IsUniqueInvolution K (zK : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hK hKl hzKc
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hJ hJl hzJc
  have hnbrJ : ¬ ∃ T' : Subgroup G, IsSylow2In T' (tightCore (J ⊓ C)) ∧
      T' ≤ Subgroup.normalizer ((tightCore (K ⊓ C) : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notJ ⟨subgroupOf_mem_restrictFamily hJc hJY, h.hKJ.symm, T'.subgroupOf X,
      mem_RSet_restrict hJc hJY hT', Subgroup.subgroupOf_mono X hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hKY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hnbrK : ¬ ∃ T' : Subgroup G, IsSylow2In T' (tightCore (K ⊓ C)) ∧
      T' ≤ Subgroup.normalizer ((tightCore (J ⊓ C) : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notK ⟨subgroupOf_mem_restrictFamily hKc hKY, h.hKJ, T'.subgroupOf X,
      mem_RSet_restrict hKc hKY hT', Subgroup.subgroupOf_mono X hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hJY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hUmap : (Subgroup.zpowers u).map X.subtype = Subgroup.zpowers (u : G) :=
    MonoidHom.map_zpowers _ _
  have hVmap : (Subgroup.zpowers v).map X.subtype = Subgroup.zpowers (v : G) :=
    MonoidHom.map_zpowers _ _
  have hUG : Subgroup.zpowers (u : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hU
    rw [hUmap] at h1
    exact mem_USet_of_core h1
  have hVG : Subgroup.zpowers (v : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hV
    rw [hVmap] at h1
    exact mem_USet_of_core h1
  have hUK : Subgroup.zpowers (u : G) ≤ K := by
    rw [← hUmap]
    refine (Subgroup.map_mono h.hUK).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact hKl
  have hVJ : Subgroup.zpowers (v : G) ≤ J := by
    rw [← hVmap]
    refine (Subgroup.map_mono h.hVJ).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
    exact hJl
  have hUV : Commutes (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
    rw [← hUmap, ← hVmap]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (h.hUV a ha b hb)
  have hRKc : IsSylow2In (R.map X.subtype) (tightCore (K ⊓ C)) := by
    have := (isSylow2In_map_subtype_iff (Y := X)).mpr h.hR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
  have hTJc : IsSylow2In (T.map X.subtype) (tightCore (J ⊓ C)) := by
    have := (isSylow2In_map_subtype_iff (Y := X)).mpr h.hT
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  have hUVmap : (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map X.subtype =
      Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) := by
    rw [Subgroup.map_sup, hUmap, hVmap]
  exact
    { hΩ := hΩ
      hK := hK
      hJ := hJ
      hKJ := hKJ
      hz := hzK
      hj := hzJ
      notJ := hN K hK J hJ hJC hKJ _ hzK hzKc.mem hnbrJ
      notK := hN J hJ K hK hKC hKJ.symm _ hzJ hzJc.mem hnbrK
      hU := hUG
      hUK := hUK
      hV := hVG
      hVJ := hVJ
      hUV := hUV
      hR := ((isSylow2In_core_iff hKC).mp hRKc).1
      hT := ((isSylow2In_core_iff hJC).mp hTJc).1
      huR := by
        rw [← hUmap]
        exact Subgroup.map_mono h.huR
      hvT := by
        rw [← hVmap]
        exact Subgroup.map_mono h.hvT
      hRN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hRN
      hTN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hTN }

theorem aEmpty_restrict_coreFam (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hN : NbrCore Ω C) (hXC : X ≤ C)
    (hcX : ∀ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ C) → tightCore (J ⊓ C) ≤ X)
    (hΛ : HypOmegaGen (restrictFamily (coreFam Ω C) X)) :
    ∀ L ∈ restrictFamily (coreFam Ω C) X, AEmpty (restrictFamily (coreFam Ω C) X) L := by
  rintro K₁ hK₁ J₁ hJs hJn zK zJ hzK hzJ
  have hK₁' := hK₁
  have hJ₁' := hJs.1
  obtain ⟨Kc, hKc, hKcY, rfl⟩ := hK₁
  obtain ⟨Jc, hJc, hJcY, rfl⟩ := hJs.1
  obtain ⟨K, hK, hKC, rfl⟩ := hKc
  obtain ⟨J, hJ, hJC, rfl⟩ := hJc
  obtain ⟨u, v, R, T, hcfg⟩ := exists_cfg64 hΛ hK₁' hJ₁' hzK hzJ hJs hJn
  have hcfgG := cfg64_of_core hΩ hN hcX hK hKC hJ hJC hcfg
  have hstar : J ∈ omegaStarNbr Ω K :=
    ⟨hJ, hcfgG.hKJ.symm, Subgroup.zpowers (v : G), hcfgG.hV, hcfgG.hVJ,
      hcfgG.symm.U_le_normalizer⟩
  obtain ⟨g, hg, hgK⟩ := hA K hK J hstar hcfgG.notJ (zK : G) (zJ : G) hcfgG.hz hcfgG.hj
  obtain ⟨ρ, hρ, hρK⟩ := exists_mem_sup_conj_of_cfg64 hcfgG hg hgK
  rw [← Subgroup.map_sup] at hρ
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hρ
  refine ⟨ρ₁, sup_le hcfg.R_le_Y hcfg.T_le_Y hρ₁, ?_⟩
  have hρK' : conjSub (ρ₁ : G) K = J := hρK
  have hρC : (ρ₁ : G) ∈ C := hXC ρ₁.2
  rw [conjSub_subgroupOf X ρ₁ (tightCore (K ⊓ C))]
  show (conjSub (ρ₁ : G) (tightCore (K ⊓ C))).subgroupOf X = (tightCore (J ⊓ C)).subgroupOf X
  congr 1
  rw [conjSub_tightCore, conjSub_inf, hρK', conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hρC)]

end AEmpty

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
