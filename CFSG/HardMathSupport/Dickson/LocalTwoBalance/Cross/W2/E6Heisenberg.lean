module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Pair
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.LangStep
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Frame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwFrame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem e6HeisenbergDiagThreeBalance_holds : E6HeisenbergDiagThreeBalance := by
  intro K _ _ h3 h2 h4 K₁ _ hroot D hDd hD hcard hnoniso H hH
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := four_le_of_not_three_dvd Finite.one_lt_card h3 h2
  have hinj := e6InndiagConj_injective K hK4
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold E6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hD.2 _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hD.2 _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨e6InndiagConj K g₁, hg₁⟩ ⟨e6InndiagConj K g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL Tag.E6 K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form h3 K₁ (g₁ : ModGL Tag.E6 K) (g₂ : ModGL Tag.E6 K) g₁.2 g₂.2 hd₁3
      hd₂3 hcomm s t hs1.symm ht1.symm hst
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ (f : ℕ) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp ι₀ = ι₀ := by
    refine RingHom.ext fun c => ?_
    change Fr (ι₀ c) = ι₀ c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFix : Units.map (entrywiseHom Fr) (baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K)) =
      baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) := by
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hpq : Nat.Coprime 3 (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (by rw [← hf, ← Nat.card_eq_fintype_card]; exact h3)
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) * c₂⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ := E6Heis.lang_step_single (L := L) (ℓ := ℓ) (f : ℕ) f.pos hpq
    (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup Tag.E6 L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL Tag.E6 K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    rw [← hconj, ← hcb]
    group
  exact E6Heis.balance_of_frame h3 hK4 hFr hg0C hu a b' ha3 hw hsh hT hu' g₁ g₂ hga' hg₂' D hg₁ hg₂
    H hH

theorem twistedE6HeisenbergDiagThreeBalance_holds : TwistedE6HeisenbergDiagThreeBalance := by
  intro ℓ f hℓ hℓ3 hf hq2 K _ _ hK σ hσ K₁ _ hroot D hDd hD hcard hnoniso H hH
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq4 : 4 ≤ ℓ ^ f :=
    four_le_of_not_three_dvd (le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)) h3 hq2
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold TwistedE6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hD.2 _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hD.2 _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨twistedE6InndiagConj K σ g₁, hg₁⟩ ⟨twistedE6InndiagConj K σ g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL TwistTag.E6.tag K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form_tw h3K K₁ (g₁ : ModGL TwistTag.E6.tag K)
      (g₂ : ModGL TwistTag.E6.tag K) (twistedE6InndiagGL_le_e6InndiagGL K σ g₁.2)
      (twistedE6InndiagGL_le_e6InndiagGL K σ g₂.2) hd₁3 hd₂3 hcomm s t hs1.symm ht1.symm hst
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hFix : twistHom TwistTag.E6 L Fr (baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K)) =
      baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ g₁.2))).2
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) * c₂⁻¹ =
      rootDiagUnit TwistTag.E6.tag a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ :=
    E6Heis.lang_step_single_tw (L := L) (ℓ := ℓ) f hf (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup TwistTag.E6.tag L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup TwistTag.E6.tag L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    have e1 : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
        z⁻¹ * (c₂ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * c₂⁻¹) * z := by group
    rw [e1, hcb]
    exact hconj
  exact E6Heis.balance_of_frame_tw hℓ hf hK σ hσ h3 hq4 hFr hg0C hu a b' ha3 hw hsh hT hu' g₁ g₂
    hga' hg₂' D hg₁ hg₂ H hH

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
