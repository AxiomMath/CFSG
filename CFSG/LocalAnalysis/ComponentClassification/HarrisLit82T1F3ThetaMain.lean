module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaProps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarBridge
public import CFSG.Timmesfeld.Final.Simple

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.TBLit

theorem generalizedFitting_subgroup_eq_genFittingFStar (H : Type) [Group H] :
    ComponentClassification.GeneralizedFitting.subgroup H = Open.genFittingFStar H := by
  rw [← CFSG.generalizedFitting_eq_componentClassification,
    ClassicalInvolution.Q3.PhilipHall.InductionBridge.genFittingFStar_eq_generalizedFitting]

theorem coprime_three_of_forall {H : Type} [Group H] [Finite H] {t : H}
    (h : ∀ y ∈ oddCentralizerCore t, y ^ 3 = 1 → y = 1) :
    Nat.Coprime (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({t} : Set H)))) 3 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(pPrimeCore 2 ↥(centralizer ({t} : Set H)))) 3 h3
  have hmem : (((z : ↥(centralizer ({t} : Set H))) : H)) ∈ oddCentralizerCore t :=
    ⟨z, z.2, rfl⟩
  have hord : orderOf (((z : ↥(centralizer ({t} : Set H))) : H)) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have h1 := h _ hmem (by rw [← hord]; exact pow_orderOf_eq_one _)
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)


theorem isThetaBalanced_M11 : IsThetaBalanced ↥Blueprint.NativeSporadic.M11 := by
  intro H _ _ ⟨e⟩ t ht
  have hG : CFSG.generalizedFitting H = Open.genFittingFStar H :=
    (ClassicalInvolution.Q3.PhilipHall.InductionBridge.genFittingFStar_eq_generalizedFitting
      H).symm
  let e' : CFSG.generalizedFitting H ≃* ↥Blueprint.NativeSporadic.M11 :=
    (MulEquiv.subgroupCongr hG).trans e
  have : IsSimpleGroup ↥Blueprint.NativeSporadic.M11 :=
    ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
  have hs : IsSimpleGroup (CFSG.generalizedFitting H) := e'.isSimpleGroup
  obtain ⟨a, b, hab⟩ : ∃ a b : ↥Blueprint.NativeSporadic.M11, a * b ≠ b * a :=
    Burgoyne.exists_ne_commute_of_sq_dvd_card Nat.prime_two
      (by rw [ClassicalInvolution.Q3.card_m11_kernel]; norm_num)
  have hnab : ∃ a b : CFSG.generalizedFitting H, a * b ≠ b * a :=
    ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩
  have h0 := CatalogueU.sporadicOddCoreFree_M11 H hs hnab ⟨e'⟩ t ht
  rw [TBLit.oddCore_eq_pPrimeCore_two] at h0
  rw [h0, Subgroup.card_bot]
  exact Nat.coprime_one_left 3

theorem harris82ThetaBalanceThreeOne_holds : Harris82ThetaBalanceThreeOne := by
  intro K _ _ hK
  rcases hK with ⟨⟨τ, n, f, hL⟩, hPSL⟩ | ⟨eM⟩
  · intro H _ _ ⟨e⟩ t ht
    have hτ : ¬ (τ = .PSL ∧ n = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hPSL f hL
    have : IsSimpleGroup K := Timmesfeld.isSimpleGroup_of_lieModel hL
    obtain ⟨a, b, hab⟩ := Burgoyne.exists_ne_commute_of_lieModel_three hL hτ
    let θ : ComponentClassification.GeneralizedFitting.subgroup H ≃* K :=
      (MulEquiv.subgroupCongr (generalizedFitting_subgroup_eq_genFittingFStar H)).trans e
    have hsimple : IsSimpleGroup (ComponentClassification.GeneralizedFitting.subgroup H) :=
      θ.isSimpleGroup
    have hnab : ∃ a b : ComponentClassification.GeneralizedFitting.subgroup H, a * b ≠ b * a :=
      ⟨θ.symm a, θ.symm b, fun h => hab (by simpa using congrArg θ h)⟩
    have hLG := LieType.CurtisTits.lieModel_of_mulEquiv θ.symm hL
    exact coprime_three_of_forall fun y hy hy3 =>
      Burgoyne.eq_one_of_pow_three_of_lieModel_three H hsimple hnab hLG hτ t ht hy hy3
  · obtain ⟨eM⟩ := eM
    intro H _ _ ⟨e⟩ t ht
    exact isThetaBalanced_M11 H ⟨e.trans eM⟩ t ht

theorem harris82OddCoreThreeTwo_holds : Harris82OddCoreThreeTwo := by
  intro X _ _ ⟨τ, n, hL⟩ t ht
  have hadm := Burgoyne.lieAdmissible_of_lieModel hL
  have hτ : ¬ (τ = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 (by norm_num)
  have : IsSimpleGroup X := Timmesfeld.isSimpleGroup_of_lieModel hL
  obtain ⟨a, b, hab⟩ := Burgoyne.exists_ne_commute_of_lieModel_three hL hτ
  have htop : Open.genFittingFStar X = ⊤ :=
    StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup ⟨a, b, hab⟩
  let θ : ComponentClassification.GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr ((generalizedFitting_subgroup_eq_genFittingFStar X).trans htop)).trans
      Subgroup.topEquiv
  have hsimple : IsSimpleGroup (ComponentClassification.GeneralizedFitting.subgroup X) :=
    θ.isSimpleGroup
  have hnab : ∃ a b : ComponentClassification.GeneralizedFitting.subgroup X, a * b ≠ b * a :=
    ⟨θ.symm a, θ.symm b, fun h => hab (by simpa using congrArg θ h)⟩
  have hLG := LieType.CurtisTits.lieModel_of_mulEquiv θ.symm hL
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1
    (Burgoyne.oddCentralizerCore_eq_bot_of_lieModel_three_one X hsimple hnab hLG t ht)

theorem harris82ThetaBalanceThree_holds : Harris82ThetaBalanceThree :=
  harris82ThetaBalanceThree_of_split harris82ThetaBalanceThreeOne_holds
    harris82OddCoreThreeTwo_holds

end CFSG.ComponentClassification.HarrisLit.T1
