module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.Rank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.RankThree.PartOne.KD4L.TriDescent
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.RankThree.PartOne.KD4T.Certs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section TriD4


theorem ssTw_finite_graphFixedRootGroup_D4 {K : Type} [Field K] [Finite K] (σ : K →+* K) :
    Finite (graphFixedRootGroup TwistTag.D4 K σ) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact Finite.of_injective (fun x => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective

theorem noL34Layer_conj_graphFixedD4_of_ne_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hx3 : (MulAut.conj x) ^ 3 = 1) (hx1 : x ≠ 1) : NoL34Layer (MulAut.conj x) := by
  haveI := ssTw_finite_graphFixedRootGroup_D4 σ.toRingHom
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  intro A hA hT
  have hne : (MulAut.conj x : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ 1 := by
    intro h
    exact hx1 (mulAut_conj_injective_of_center_eq_bot hZ (h.trans (map_one _).symm))
  obtain ⟨E, hE, hlt⟩ := ssTw_pumpup_exists_elemAbelian_gt_nine hZ ⟨hx3, hne, A, hA, hT⟩
  have h9 := card_le_nine_of_graphFixedRootGroup_ne_three hℓ hℓ3 hf hK (σ := σ.toRingHom) hσ E hE
  omega

theorem chevalleyExceptionalModel_trialityD4_of_equiv {S : Type} [Group S] {ℓ d : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k] [Finite k] (hk : Nat.card k = (ℓ ^ d) ^ 3)
    (σ₀ : k ≃+* k) (hσ₀ : ∀ c, σ₀ c = c ^ (ℓ ^ d))
    (e : S ≃* graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) :
    ChevalleyExceptionalModel S .trialityD4 ℓ d := by
  obtain ⟨E⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4 hℓ hd k
    hk σ₀.toRingHom hσ₀
  exact ⟨⟨hℓ, hd, rfl⟩, k, inferInstance, inferInstance, hk, σ₀.toRingHom, hσ₀,
    ⟨e.trans E.symm⟩⟩

theorem noL34Layer_conj_graphFixedD4
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hx3 : (MulAut.conj x) ^ 3 = 1) :
    NoL34Layer (MulAut.conj x) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ3 : ℓ ≠ 3 := by omega
  by_cases hx1 : x = 1
  · subst hx1
    haveI := ssTw_finite_graphFixedRootGroup_D4 σ.toRingHom
    rw [map_one]
    obtain ⟨hs, hnab⟩ := CFSG.RankThree.PartOne.KD4L.isSimple_graphFixedRootGroup_triality hℓ hf hK
      1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
    have hM : ChevalleyExceptionalModel ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
        .trialityD4 ℓ f :=
      chevalleyExceptionalModel_trialityD4_of_equiv hℓ hf hK σ hσ (MulEquiv.refl _)
    have hL34 : ¬ IsLThreeFour ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      not_isLThreeFour_of_lieModel_odd hO hℓ2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    have hfix : fixSubgroup (1 : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = ⊤ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => mem_fixSubgroup.2 rfl⟩
    let e : ↥(fixSubgroup (1 : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (MulEquiv.subgroupCongr hfix).trans Subgroup.topEquiv
    exact noL34Layer_of_fixed_equiv _ e hs hnab hL34
  · exact noL34Layer_conj_graphFixedD4_of_ne_one hℓ hℓ3 hf hK σ hσ hx3 hx1

end TriD4

end CFSG.HardMathSupport.Dickson.Sec6
