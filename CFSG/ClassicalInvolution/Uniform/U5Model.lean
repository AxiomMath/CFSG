module

public import CFSG.ClassicalInvolution.Uniform.U5ModelA
public import CFSG.ClassicalInvolution.ModelFacts.CF3Transfer
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.GH74.Generic.S1.KL3SL3
public import CFSG.ClassicalInvolution.Uniform.U5Glue
public import CFSG.LieType.HighestRoot.ModelCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (StdDich3 conj_eq_of_normalizes_image
  neg_one_eq_commutator_sl2)
open scoped MatrixGroups commutatorElement

section Facts

@[expose] def CompGen3Twin (c : Q3.CompData) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ψ : c.G →* X), ψ.ker ≤ Subgroup.center c.G →
    ∀ R₁ ∈ c.fund, ∀ R₂ ∈ c.fund, Nat.card (R₁.map ψ) = 24 → Nat.card (R₂.map ψ) = 24 →
      R₁.map ψ ≠ R₂.map ψ → Commutes (R₁.map ψ) (R₂.map ψ) →
      ∀ z : X, IsUniqueInvolution (R₁.map ψ) z → IsUniqueInvolution (R₂.map ψ) z →
      ∀ A : Subgroup X, IsElemAbelian2 A 2 → A ≤ R₁.map ψ ⊔ R₂.map ψ → z ∈ A →
        ψ.range ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range

@[expose] def TwinGen3 : Prop :=
  ∀ (t : StatedLieTag) (k : ℕ), IsFundTag t → StatedLieAdmissible t k 3 1 →
    t ≠ .G2 → t ≠ .trialityD4 → CompGen3Twin (compModel 3 1 t k)

@[expose] def G2D4Gen3 : Prop :=
  ∀ (t : StatedLieTag) (k : ℕ), (t = .G2 ∨ t = .trialityD4) → IsFundTag t →
    StatedLieAdmissible t k 3 1 → CompGen3 (compModel 3 1 t k)

end Facts

section Model



theorem compGen3_model {t : StatedLieTag} {k : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t k 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hComm : ModelFacts.CommutingFundamentalGeneration 3 t k 1)
    (hTwin : CompGen3Twin (compModel 3 1 t k)) : CompGen3 (compModel 3 1 t k) := by
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hQex hv htw z hz A hA hAKJ hzA
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := hQex
  by_cases htwin : IsUniqueInvolution (R₂.map ψ) z
  · exact hTwin X ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne (htw z hz htwin) z hz htwin A hA hAKJ hzA
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
  have hzJQ : ψ (sl2Inv eR₂) ∈ Q := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card Q by rw [hQ8]; norm_num)
    have hxJ : (x : X) ∈ R₂.map ψ := hQJ x.2
    have hx2 : (x : X) * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx, pow_two] at h
      exact congrArg Subtype.val h
    have hx1 : (x : X) ≠ 1 := by
      intro h
      have h' : x = 1 := Subtype.ext h
      rw [h', orderOf_one] at hx
      omega
    have := (uJ.unique x hxJ hx2).resolve_left hx1
    rw [← this]
    exact x.2
  have hzJN : ψ (sl2Inv eR₂) ∈ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X) := hQN hzJQ
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
    have hA4 : Nat.card A = 4 := by simpa using hA.1
    have hzJA : ψ (sl2Inv eR₂) ∈ A :=
      mem_of_four_group ψ eR₁ eR₂ h24₁ h24₂ hKJ hz htwin hA.2 hA4 hAKJ hzA
    have hzJ1 : ψ (sl2Inv eR₂) ≠ 1 := uJ.ne_one
    have hzzJ1 : z * ψ (sl2Inv eR₂) ≠ 1 := by
      intro h
      apply htwin
      have h' : ψ (sl2Inv eR₂) = z⁻¹ := eq_inv_of_mul_eq_one_right h
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
      rw [h'.trans hzi] at uJ
      exact uJ
    have hbound : ∀ a ∈ A, a ≠ 1 →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t k 3 1 Nat.prime_three).D,
        (∀ y ∈ R.map ψ, a * y = y * a) →
        R.map ψ ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range := by
      intro a ha ha1 R _ hR y hy
      have hle : Subgroup.centralizer ({a} : Set X) ⊓ ψ.range ≤
          ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range :=
        le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
      exact hle ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hR y hy).symm,
        Subgroup.map_le_range ψ R hy⟩
    refine key.trans (iSup₂_le fun R hR => iSup_le fun hP => ?_)
    rcases hP with h | h | h
    · exact hbound z hzA hz.ne_one R hR h
    · exact hbound _ hzJA hzJ1 R hR h
    · exact hbound _ (A.mul_mem hzA hzJA) hzzJ1 R hR h
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

end Model

end CFSG.ClassicalInvolution.Uniform
