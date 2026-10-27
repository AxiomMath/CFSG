module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsFieldW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FieldSqA

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace GrS4

variable {G : Type} [Group G] [Finite G]

theorem isElemTwo_eight_of_commuting {a₁ a₂ w : G} (h11 : a₁ * a₁ = 1) (h22 : a₂ * a₂ = 1)
    (hww : w * w = 1) (h1 : a₁ ≠ 1) (h12 : a₂ ≠ 1) (h2 : a₂ ≠ a₁) (c12 : a₁ * a₂ = a₂ * a₁)
    (c1w : a₁ * w = w * a₁) (c2w : a₂ * w = w * a₂) (hw : w ∉ zpowers a₁ ⊔ zpowers a₂) :
    IsElemTwo (zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers w) ∧
      Nat.card ↥(zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers w) = 2 ^ 3 := by
  have hE₁ : IsElemTwo (zpowers a₁) := isElemTwo_zpowers h11
  have hc₁ : Nat.card ↥(zpowers a₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h11) h1
  have hcz : ∀ {x y : G}, x * y = y * x → ∀ e ∈ zpowers x, e * y = y * e := by
    intro x y hxy e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left hxy k)
  obtain ⟨hE₂, hc₂⟩ := isElemTwo_sup_zpowers hE₁ h22 (fun h => by
    rcases eq_one_or_eq_of_mem_zpowers h11 h with h' | h'
    · exact h12 h'
    · exact h2 h') (fun e he => hcz c12 e he)
  have hE₂w : ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, e * w = w * e := by
    intro e he
    have hle : zpowers a₁ ⊔ zpowers a₂ ≤ centralizer ({w} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hcz c1w x hx))
        (fun x hx => mem_centralizer_singleton_iff.mpr (hcz c2w x hx))
    exact mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE₃, hc₃⟩ := isElemTwo_sup_zpowers hE₂ hww hw hE₂w
  exact ⟨hE₃, by rw [hc₃, hc₂, hc₁]; norm_num⟩

end GrS4

theorem l34Lemma46FieldSquareStep_of_inputs
    (hRank : L34CenterRankFact) (hSqC : L34SquareCenterFact) (hWit : L34OuterWitnessFact) :
    L34Lemma46FieldSquareStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl b hbS
    hba hbZ hr
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hJa hJc
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨g, hg⟩ := hba
  have hbb : b * b = 1 := by
    rw [hg, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  have hbN : b ∈ normalizer (J : Set G) := hS.1 hbS
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzz⟩ := GrS4.exists_sq_ne_one_of_exponent_eq_four hexp
    rw [h, mem_bot] at hz
    rw [hz, one_mul] at hzz
    exact hzz rfl
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have hZK : ∀ {z : G}, z ∈ zStarIn J → z ∈ coreActionKernel J := fun hz => by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h] at hz
    exact (mem_inf.mp hz).2
  have hZab : ∀ u ∈ S ⊓ zStarIn J, ∀ v ∈ S ⊓ zStarIn J, u * v = v * u := fun u hu v hv =>
    GrS4.mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hu).1 (hZK (mem_inf.mp hu).2)
      (mem_inf.mp hv).1 (map_subtype_le _ (mem_inf.mp hv).2)
  by_cases hbK : b ∈ withKernel J
  · exact absurd (GrS4.three_le_pRank_centralizer_of_mem_withKernel hSqC hJ hL34 hS hnc hbS hbK
      hbb) (not_le.mpr hr)
  have hbZZ : ∀ z ∈ S ⊓ zStarIn J, b * z * b⁻¹ ∈ S ⊓ zStarIn J := fun z hz =>
    mem_inf.mpr ⟨mul_mem (mul_mem hbS (mem_inf.mp hz).1) (inv_mem hbS),
      GrS4.conj_mem_zStarIn hbN (mem_inf.mp hz).2⟩
  have hbacomm : b * a = a * b := hcent b hbS
  by_cases hmove : ∃ f ∈ S ⊓ zStarIn J, f * f = 1 ∧ b * f * b⁻¹ ≠ f
  · obtain ⟨f, hfZ, hff, hbf⟩ := hmove
    obtain ⟨e, heZ, hee⟩ := GrS4.exists_sq_ne_one_of_exponent_eq_four hexp
    have hZ4 : ∀ z ∈ S ⊓ zStarIn J, z ^ 4 = 1 := fun z hz => by
      have h := Monoid.pow_exponent_eq_one (⟨z, hz⟩ : ↥(S ⊓ zStarIn J))
      rw [hexp] at h
      exact congrArg Subtype.val h
    have h4 : Nat.card ↥(omegaOne (S ⊓ zStarIn J)) ≤ 4 := by
      have h := hRank G J (S ⊓ J) hJ hL34 hP
      rwa [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)] at h
    obtain ⟨z, hzZ, hzb, hzz⟩ := GrS4.exists_sq_eq_of_moves hZab h4 hZ4 heZ hee haZ haa ha1
      hbacomm hbZZ hbb hfZ hff hbf
    exact ⟨z, mem_inf.mpr ⟨(mem_inf.mp hzZ).1, mem_centralizer_singleton_iff.mpr hzb⟩, hzz⟩
  · exfalso
    push Not at hmove
    have hbP : b ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp hbN y]
      constructor
      · rintro ⟨hyS, hyJ⟩
        exact ⟨mul_mem (mul_mem hbS hyS) (inv_mem hbS), hyJ⟩
      · rintro ⟨hyS, hyJ⟩
        refine ⟨?_, hyJ⟩
        have h := mul_mem (mul_mem (inv_mem hbS) hyS) hbS
        rwa [show b⁻¹ * (b * y * b⁻¹) * b = y by group] at h
    obtain ⟨w, hwP, hww, hwb, hwZ⟩ := hWit G J (S ⊓ J) b hJ hL34 hP hbN hbP hbb hbK
    obtain ⟨a₁, ha₁, a₂, ha₂, h11, h22, h1, h2, h12⟩ :=
      GrS4.exists_two_involutions_of_not_isCyclic (hS2.to_le inf_le_left) hZab hnc
    have hcw : ∀ z ∈ S ⊓ zStarIn J, z * w = w * z := fun z hz =>
      GrS4.mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hz).1 (hZK (mem_inf.mp hz).2)
        (mem_inf.mp hwP).1 (mem_inf.mp hwP).2
    have hfix : ∀ z ∈ S ⊓ zStarIn J, z * z = 1 → z * b = b * z := fun z hz hzz => by
      have h := hmove z hz hzz
      calc z * b = b * z * b⁻¹ * b := by rw [h]
        _ = b * z := by group
    have hE2Z : zpowers a₁ ⊔ zpowers a₂ ≤ S ⊓ zStarIn J :=
      sup_le (zpowers_le.mpr ha₁) (zpowers_le.mpr ha₂)
    obtain ⟨hE, hEc⟩ := GrS4.isElemTwo_eight_of_commuting h11 h22 hww h1 h2 (Ne.symm h12)
      (hZab a₁ ha₁ a₂ ha₂) (hcw a₁ ha₁) (hcw a₂ ha₂) (fun h => hwZ (mem_inf.mp (hE2Z h)).2)
    have hEle : zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers w ≤ S ⊓ J ⊓ centralizer ({b} : Set G) := by
      have hZP : ∀ {z : G}, z ∈ S ⊓ zStarIn J → z ∈ S ⊓ J := fun hz =>
        mem_inf.mpr ⟨(mem_inf.mp hz).1, map_subtype_le _ (mem_inf.mp hz).2⟩
      refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
      · exact mem_inf.mpr ⟨hZP ha₁, mem_centralizer_singleton_iff.mpr (hfix a₁ ha₁ h11)⟩
      · exact mem_inf.mpr ⟨hZP ha₂, mem_centralizer_singleton_iff.mpr (hfix a₂ ha₂ h22)⟩
      · exact mem_inf.mpr ⟨hwP, mem_centralizer_singleton_iff.mpr hwb⟩
    exact absurd (GrS4.le_pRank_of_isElemTwo hEle hE hEc) (not_le.mpr hr)

end CFSG.ComponentClassification.GrSLit
