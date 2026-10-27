module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxConj

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem pair_normal_form {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K)
    (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (d₁ d₂ : ModGL Tag.E6 K) (hd₁ : d₁ ∈ e6InndiagGL K) (hd₂ : d₂ ∈ e6InndiagGL K)
    (hd₁3 : d₁ ^ 3 = 1) (hd₂3 : d₂ ^ 3 = 1) (hcomm : d₁ * d₂ = d₂ * d₁)
    (s t : ↥(e6Data_valid.minGroup K₁))
    (hs : (e6Isogeny K₁ s : ModGL Tag.E6 K₁) = baseChangeGL (algebraMap K K₁) d₁)
    (ht : (e6Isogeny K₁ t : ModGL Tag.E6 K₁) = baseChangeGL (algebraMap K K₁) d₂)
    (hst : s * t ≠ t * s) :
    ∃ c₂ ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      ∃ (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (w : WeylGroup Tag.E6),
        (∀ i, a i ^ 3 = 1) ∧ w ∈ rootCharStabilizer a ∧ rootChar a (e6Shift w) ≠ 1 ∧
        c₂ * baseChangeGL (algebraMap K (AlgebraicClosure K)) d₁ * c₂⁻¹ = rootDiagUnit Tag.E6 a ∧
        c₂ * baseChangeGL (algebraMap K (AlgebraicClosure K)) d₂ * c₂⁻¹ =
          rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w := by
  classical
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hX : ∀ (d : ModGL Tag.E6 K) (g : ↥(e6Data_valid.minGroup K₁)),
      (e6Isogeny K₁ g : ModGL Tag.E6 K₁) = baseChangeGL (algebraMap K K₁) d →
      baseChangeGL (algebraMap K (AlgebraicClosure K)) d =
        e6ScToBar K₁ (algebraMap K₁ (AlgebraicClosure K)) g := by
    intro d g hg
    change _ = baseChangeGL (algebraMap K₁ (AlgebraicClosure K))
      ((e6Isogeny K₁ g : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁)
    rw [hg, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq]
  have hX₁ := hX d₁ s hs
  have hX₂ := hX d₂ t ht
  have hmemC : ∀ g : ↥(e6Data_valid.minGroup K₁),
      e6ScToBar K₁ (algebraMap K₁ (AlgebraicClosure K)) g ∈
        adjointGroup Tag.E6 (AlgebraicClosure K) :=
    fun g => CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ (e6Isogeny K₁ g).2
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      A = (Subgroup.closure ({d₁, d₂} : Set (ModGL Tag.E6 K))).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K))) := ⟨_, rfl⟩
  have hcommD := PairAux.closure_pair_commute hcomm
  have hexpD := PairAux.closure_pair_pow_eq_one hcomm hd₁3 hd₂3
  have hA : A ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hAdef, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · change baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
        adjointGroup Tag.E6 (AlgebraicClosure K)
      rw [hX₁]
      exact hmemC s
    · change baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
        adjointGroup Tag.E6 (AlgebraicClosure K)
      rw [hX₂]
      exact hmemC t
  have hAfin : (A : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite := by
    rw [hAdef, Subgroup.coe_map]
    exact (Set.toFinite _).image _
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rw [hAdef]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hcommD g hg h hh]
  have hAexp : ∀ x ∈ A, x ^ 3 = 1 := by
    rw [hAdef]
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hexpD g hg, map_one]
  have hx₀ : baseChangeGL (algebraMap K (AlgebraicClosure K)) d₁ ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hy₀ : baseChangeGL (algebraMap K (AlgebraicClosure K)) d₂ ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨c₂, hc₂, a, b, w, hap, hw, hca, hcb⟩ :=
    PairAux.exists_conj_pair_normal_form_bar h3 hA hAfin hAcomm hAexp hx₀ hy₀
  refine ⟨c₂, hc₂, a, b, w, hap, hw, fun h1 => hst ?_, hca, hcb⟩
  rw [hX₁] at hca
  rw [hX₂] at hcb
  exact PairAux.commute_of_rootChar_e6Shift_eq_one _ hc₂ hca hcb hw h1

theorem pair_normal_form_tw {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K)
    (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (d₁ d₂ : ModGL TwistTag.E6.tag K) (hd₁ : d₁ ∈ e6InndiagGL K) (hd₂ : d₂ ∈ e6InndiagGL K)
    (hd₁3 : d₁ ^ 3 = 1) (hd₂3 : d₂ ^ 3 = 1) (hcomm : d₁ * d₂ = d₂ * d₁)
    (s t : ↥(e6Data_valid.minGroup K₁))
    (hs : (e6Isogeny K₁ s : ModGL Tag.E6 K₁) = baseChangeGL (algebraMap K K₁) d₁)
    (ht : (e6Isogeny K₁ t : ModGL Tag.E6 K₁) = baseChangeGL (algebraMap K K₁) d₂)
    (hst : s * t ≠ t * s) :
    ∃ c₂ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ (a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) (w : WeylGroup Tag.E6),
        (∀ i, a i ^ 3 = 1) ∧ w ∈ rootCharStabilizer a ∧ rootChar a (e6Shift w) ≠ 1 ∧
        c₂ * baseChangeGL (algebraMap K (AlgebraicClosure K)) d₁ * c₂⁻¹ =
          rootDiagUnit TwistTag.E6.tag a ∧
        c₂ * baseChangeGL (algebraMap K (AlgebraicClosure K)) d₂ * c₂⁻¹ =
          rootDiagUnit TwistTag.E6.tag b *
            canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w :=
  pair_normal_form h3 K₁ d₁ d₂ hd₁ hd₂ hd₁3 hd₂3 hcomm s t hs ht hst

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
