module

public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.ModelFacts.CF3Transfer
public import CFSG.ClassicalInvolution.Uniform.U5Glue
public import CFSG.ClassicalInvolution.Uniform.U5ModelA
public import CFSG.GH74.Generic.S1.KL3SL3
public import CFSG.LieType.HighestRoot.ModelCenter

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (StdDich3 conj_eq_of_normalizes_image
  neg_one_eq_commutator_sl2)
open scoped MatrixGroups commutatorElement


section General

variable {Z : Type} [Group Z] [Finite Z] {Ψ : Set (Subgroup Z)}

theorem zLink3_exists_sylow (hcard : ∀ L ∈ Ψ, Nat.card L = 24) {M₁ M₂ : Subgroup Z}
    (h : M₂ ∈ omegaNbr Ψ M₁) :
    ∃ Q : Subgroup Z, Q ≤ M₂ ∧ Nat.card Q = 8 ∧ Q ≤ Subgroup.normalizer (M₁ : Set Z) := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h
  obtain ⟨J', hJ'Ω, P, rfl⟩ := hR
  refine ⟨_, hRJ, ?_, hRN⟩
  rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity,
    hcard J' hJ'Ω, two_pow_factorization_24]

theorem zLink3_exact (hΩ : HypOmegaModU (.sl2 3 1) Ψ) (hcard : ∀ L ∈ Ψ, Nat.card L = 24) :
    ExactMembers Ψ := by
  intro L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2
  have h1 : Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = 24 :=
    (Nat.card_congr e.toEquiv).trans natCard_sl2_galoisField_three
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥L)
  rw [hcard L hL, h1] at h2
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem zLink3_not_twin (hnt : ∀ M ∈ Ψ, ∀ M' ∈ twinSet Ψ M, M' = M) {M₁ M₂ : Subgroup Z}
    (h1 : M₁ ∈ Ψ) (h2 : M₂ ∈ omegaNbr Ψ M₁) {u : Z} (hu : IsUniqueInvolution M₁ u) :
    ¬ IsUniqueInvolution M₂ u := fun hv => h2.2.1 (hnt M₁ h1 M₂ ⟨h2.1, u, hu, hv⟩)

end General

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem zLink3_mem_sylow {J Q : Subgroup X} {v : X} (hQJ : Q ≤ J) (hQ8 : Nat.card Q = 8)
    (hv : IsUniqueInvolution J v) : v ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card Q by rw [hQ8]; norm_num)
  have hxJ : (x : X) ∈ J := hQJ x.2
  have hx2 : (x : X) * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg Subtype.val h
  have hx1 : (x : X) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext h
    rw [h', orderOf_one] at hx
    omega
  have := (hv.unique x hxJ hx2).resolve_left hx1
  rw [← this]
  exact x.2

theorem zLink3_comm_of_sylow {K J Q : Subgroup X} {u v : X} (hQJ : Q ≤ J) (hQ8 : Nat.card Q = 8)
    (hQN : Q ≤ Subgroup.normalizer (K : Set X)) (hu : IsUniqueInvolution K u)
    (hv : IsUniqueInvolution J v) : u * v = v * u := by
  have h := conj_eq_of_mem_normalizer hu (hQN (zLink3_mem_sylow hQJ hQ8 hv))
  calc u * v = (v * u * v⁻¹) * v := by rw [h]
    _ = v * u := by group

end Sylow

section Model

theorem zLink3_model_range {t : StatedLieTag} {k : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t k 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hComm : ModelFacts.CommutingFundamentalGeneration 3 t k 1)
    {X : Type} [Group X] [Finite X] (ψ : (compModel 3 1 t k).G →* X)
    (hker : ψ.ker ≤ Subgroup.center (compModel 3 1 t k).G)
    {R₁ R₂ : Subgroup (compModel 3 1 t k).G} (hR₁ : R₁ ∈ (compModel 3 1 t k).fund)
    (hR₂ : R₂ ∈ (compModel 3 1 t k).fund) (h24₁ : Nat.card (R₁.map ψ) = 24)
    (h24₂ : Nat.card (R₂.map ψ) = 24) (hne : R₁.map ψ ≠ R₂.map ψ)
    (hQex : ∃ Q : Subgroup X, Q ≤ R₂.map ψ ∧ Nat.card Q = 8 ∧
      Q ≤ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X))
    (hv : padicValNat 2 (Nat.card ↥(R₁.map ψ ⊓ R₂.map ψ)) ≤ 1)
    {z w : X} (hz : IsUniqueInvolution (R₁.map ψ) z) (hw : IsUniqueInvolution (R₂.map ψ) w)
    (htwin : ¬ IsUniqueInvolution (R₂.map ψ) z) :
    ψ.range ≤ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
      Subgroup.centralizer ({z * w} : Set X) := by
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := hQex
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hMfin : Finite (compModel 3 1 t k).G :=
    ModelFacts.finite_modelUniv hp2 Nat.prime_three (ih8_isFundTag_mf hfund) hadm
  obtain ⟨eR₁⟩ :=
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR₁
  obtain ⟨eR₂⟩ :=
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR₂
  obtain ⟨uI, hinj₁⟩ := uniqueInvolution_map ψ eR₁ h24₁
  obtain ⟨uJ, hinj₂⟩ := uniqueInvolution_map ψ eR₂ h24₂
  have hψz : ψ (sl2Inv eR₁) = z := uI.eq hz
  have hψw : ψ (sl2Inv eR₂) = w := uJ.eq hw
  have hzJN : ψ (sl2Inv eR₂) ∈ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X) :=
    hQN (zLink3_mem_sylow hQJ hQ8 uJ)
  have hconjz : ψ (sl2Inv eR₂) * z * (ψ (sl2Inv eR₂))⁻¹ = z := conj_eq_of_mem_normalizer hz hzJN
  obtain ⟨A₀, B₀, hAB⟩ := neg_one_eq_commutator_sl2 hFcard
  have hcom : ⁅((eR₁.symm A₀ : R₁) : (compModel 3 1 t k).G),
      ((eR₁.symm B₀ : R₁) : (compModel 3 1 t k).G)⁆ = sl2Inv eR₁ := by
    have h1 := map_commutatorElement R₁.subtype (eR₁.symm A₀) (eR₁.symm B₀)
    have h2 := map_commutatorElement eR₁.symm A₀ B₀
    rw [hAB] at h2
    simp only [Subgroup.coe_subtype] at h1
    rw [← h1, ← h2]
    rfl
  have hN : ∀ r ∈ R₁, ∃ r' ∈ R₁, ψ r' = ψ (sl2Inv eR₂) * ψ r * (ψ (sl2Inv eR₂))⁻¹ := by
    intro r hr
    have := (Subgroup.mem_normalizer_iff.mp hzJN _).mp (Subgroup.mem_map_of_mem ψ hr)
    obtain ⟨r', hr', hr'e⟩ := this
    exact ⟨r', hr', hr'e⟩
  have hconj := conj_eq_of_normalizes_image ψ hker hinj₁ (eR₁.symm A₀).2 (eR₁.symm B₀).2 hcom hN
    (by rw [hψz]; exact hconjz)
  have hc₁c₂ : sl2Inv eR₁ * sl2Inv eR₂ = sl2Inv eR₂ * sl2Inv eR₁ := by
    calc sl2Inv eR₁ * sl2Inv eR₂
        = (sl2Inv eR₂ * sl2Inv eR₁ * (sl2Inv eR₂)⁻¹) * sl2Inv eR₂ := by rw [hconj]
      _ = sl2Inv eR₂ * sl2Inv eR₁ := by group
  have h192 : Nat.card ↥(Q ⊔ R₁.map ψ) = 192 := by
    rcases card_sup_of_sylow_normalizes h24₁ hQ8 hQJ hQN hv with ⟨h, -⟩ | ⟨-, hc⟩
    · exact h
    · exfalso
      have : Nontrivial ↥(R₁.map ψ ⊓ Q) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : ↥(R₁.map ψ ⊓ Q))
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hx2 : x * x = 1 := by
        have h := pow_card_eq_one' (G := ↥(R₁.map ψ ⊓ Q)) (x := (⟨x, hx⟩ : ↥(R₁.map ψ ⊓ Q)))
        rw [hc] at h
        have h' := congrArg Subtype.val h
        simpa [pow_two] using h'
      have hxz : x = z := (hz.unique x hx.1 hx2).resolve_left hx1'
      have hxJ : x = ψ (sl2Inv eR₂) := (uJ.unique x (hQJ hx.2) hx2).resolve_left hx1'
      exact htwin (by rw [hxz.symm.trans hxJ]; exact uJ)
  have hDich : StdDich3 t k :=
    T3CII.stdDich3_all ModelFacts.stdDich3Orth ModelFacts.stdDich3Exc t k hfund hadm hG2 hD4
  have hR₁l := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR₁
  have hR₂l := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR₂
  rcases hDich R₁ hR₁l R₂ hR₂l (sl2Inv eR₁) (sl2Inv eR₂) (sl2Inv_mem eR₁) (sl2Inv_mem eR₂)
    (orderOf_sl2Inv hodd eR₁) (orderOf_sl2Inv hodd eR₂) hc₁c₂ with hRS | hcm | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd (by rw [hRS]) hne
  ·
    have hKJ : Commutes (R₁.map ψ) (R₂.map ψ) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcm x hx y hy]
    have hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
      CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t k 3 1 Nat.prime_three hp2
        hfund hadm x (hker hx) hx3
    have hG3 : ∀ R ∈ fundamentalSubgroups t (modelUniv t k 3 1 Nat.prime_three).D,
        ModelFacts.Gen3 R :=
      fun R hR => ModelFacts.gen3_of_mem_longestFundamental3 (p := 3) (e := 1) (by norm_num)
        hfund hadm hG2 hD4 (ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR)
    have key := ModelFacts.range_le_iSup_of_commutingPair3 ψ hker hk3 hG3 hComm hR₁ hR₂
      (u₁ := z) (u₂ := ψ (sl2Inv eR₂)) hz.mem uJ.mem (uniqueInvolution_comm hz)
      (uniqueInvolution_comm uJ) (fun y hy => (hKJ y hy _ uJ.mem).symm)
      (fun y hy => hKJ z hz.mem y hy)
    rw [hψw] at key
    refine key.trans (iSup₂_le fun R hR => iSup_le fun hP => ?_)
    rcases hP with h | h | h
    · exact le_sup_of_le_left (le_sup_of_le_left fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h y hy).symm)
    · exact le_sup_of_le_left (le_sup_of_le_right fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h y hy).symm)
    · exact le_sup_of_le_right fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h y hy).symm
  ·
    exfalso
    obtain ⟨θ, hrange, -, h1, h2⟩ := CFSG.ClassicalInvolution.WeakCT.pair_normalize hW
    have hRW : R₁ ≤ W := by
      rw [← h1, ← hrange]
      exact Subgroup.map_le_range θ _
    have hSW : R₂ ≤ W := by
      rw [← h2, ← hrange]
      exact Subgroup.map_le_range θ _
    have hle : Q ⊔ R₁.map ψ ≤ (ψ.comp θ).range := by
      rw [MonoidHom.range_comp, hrange]
      exact sup_le (hQJ.trans (Subgroup.map_mono hSW)) (Subgroup.map_mono hRW)
    have hdvd : Nat.card ↥(Q ⊔ R₁.map ψ) ∣ Nat.card SL(3, GaloisField 3 1) :=
      (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_dvd_of_surjective
        (f := (ψ.comp θ).rangeRestrict) (MonoidHom.rangeRestrict_surjective _))
    rw [h192, CFSG.GH74.Generic.S1.kl3_card_sl3 hFcard] at hdvd
    norm_num at hdvd
  ·
    exfalso
    obtain ⟨θ, hrange, -, h1, h2⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hW
    have hRW : R₁ ≤ W := by
      rw [← h1, ← hrange]
      exact Subgroup.map_le_range θ _
    have hSW : R₂ ≤ W := by
      rw [← h2, ← hrange]
      exact Subgroup.map_le_range θ _
    have hle : Q ⊔ R₁.map ψ ≤ (ψ.comp θ).range := by
      rw [MonoidHom.range_comp, hrange]
      exact sup_le (hQJ.trans (Subgroup.map_mono hSW)) (Subgroup.map_mono hRW)
    have hdvd : Nat.card ↥(Q ⊔ R₁.map ψ) ∣ Nat.card (Phan.Su (GaloisField 3 2) 3 1 3) :=
      (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_dvd_of_surjective
        (f := (ψ.comp θ).rangeRestrict) (MonoidHom.rangeRestrict_surjective _))
    rw [h192, card_su_three_three] at hdvd
    norm_num at hdvd

theorem zLink3_model_class {t : StatedLieTag} {k : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t k 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {X : Type} [Group X] (ψ : (compModel 3 1 t k).G →* X)
    {R₁ R : Subgroup (compModel 3 1 t k).G} (hR₁ : R₁ ∈ (compModel 3 1 t k).fund)
    (hR : R ∈ (compModel 3 1 t k).fund) : ∃ g : X, R.map ψ = conjSub g (R₁.map ψ) := by
  obtain ⟨g, hg⟩ :=
    ModelFacts.fundamentalSingleClass t k 3 1 Nat.prime_three hfund hadm hG2 hD4 R₁ hR₁ R hR
  refine ⟨ψ g, ?_⟩
  have h : R = conjSub g R₁ := hg
  rw [h]
  exact AscQuot.map_conjSub ψ g R₁

end Model

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
