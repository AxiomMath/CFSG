module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOUnitary
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamTw
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.SeitzReduction.SymplecticPilot (ctuEmbed ctuBlock ctuBlockEquiv ctuGramEquiv uModelSU
  complSpEquiv)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_twoUnitary6Cover_normalized {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (h : UnitaryFieldData 2 1 F)
      (ε : h.fixedField ≃+* K) (Φ : uGroup6 h →* G),
      Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧ Φ.ker ≤ center (uGroup6 h) ∧
      ∀ s : StatedSp 3 h.fixedField, Φ (uEmbed6 h s) = levi6Hom e ε s := by
  obtain ⟨F, _, _, hF1, Φ₀, hE₀, hker₀⟩ := exists_twoSu6Cover hw e hXJ hcyc hX₀ hk
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * 1) (by
    rw [hF1, ← pow_mul, mul_comm])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 1 F := unitaryFieldData_of_card (by omega) hF1
  have eS : StatedSU 6 (2 ^ 1) F =
      gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h 6
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 6) (by norm_num) (by omega)
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)),
      Function.Surjective π' → π'.ker ≤ center E' → Odd (Nat.card π'.ker) →
        ∃ s : gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) →* E',
          ∀ g, π' (s g) = g := by
    intro E' _ _ π' hπ' hcen hodd
    have hkerE : (eM.symm.toMonoidHom.comp π').ker = π'.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ eM.symm.injective]
    obtain ⟨s, hs⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_section_statedSU_of_coprime hF1
        (m := 6) (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num))
        (π := eM.symm.toMonoidHom.comp π') (eM.symm.surjective.comp hπ') (hkerE ▸ hcen)
        (fun _ => Nat.coprime_two_left.2 (hkerE ▸ hodd))
    refine ⟨s.comp eM.symm.toMonoidHom, fun g => eM.symm.injective ?_⟩
    exact hs (eM.symm g)
  have hoddZ : Odd (Nat.card (center (StatedSU 6 (2 ^ 1) F))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr
      (CFSG.LieType.Universal.Unitary.equivStatedSU hF1 6)).toEquiv]
    exact CFSG.SeitzReduction.SymplecticPilot.odd_card_center_SU hF1 le_rfl (by norm_num)
      (by decide)
  have hodd₁ : Odd (Nat.card Φ₁.ker) := by
    have h1 : Nat.card (center (gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) =
        Nat.card (center (StatedSU 6 (2 ^ 1) F)) :=
      Nat.card_congr (Subgroup.centerCongr eM.symm).toEquiv
    exact Odd.of_dvd_nat (h1 ▸ hoddZ) (Subgroup.card_dvd_of_le hker₁)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ := exists_twoGraphLift_of_oddClosed hw e hXJ hcyc hX₀
    (κ := .unitary6) (by decide) hk hsplit Φ₁ hE₁ hker₁ hodd₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary6_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ = Φ₂ (barSU6 h g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hw.card_eq, pow_one]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀']
    rfl
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr', hk', -, hn'⟩ := exists_normalized_coverU h e ε Φ₂ hker₂ hc hD
  exact ⟨F, inferInstance, inferInstance, inferInstance, h, ε, Φ', hr'.trans hE₂, hk', hn'⟩


theorem spModelIdx_three_eq_sp6ToSLIdx :
    (CFSG.SeitzReduction.SymplecticPilot.spModelIdx 3 : Fin 3 ⊕ Fin 3 ≃ Fin (2 * 3)) =
      sp6ToSLIdx := by
  ext u
  rcases u with i | i
  · rw [CFSG.SeitzReduction.SymplecticPilot.spModelIdx_inl_val, sp6ToSLIdx_inl,
      Fin.val_castAdd]
  · rw [CFSG.SeitzReduction.SymplecticPilot.spModelIdx_inr_val, sp6ToSLIdx_inr,
      Fin.val_natAdd]

theorem coe_uModelSU_eq_uEmbed6 {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)
    [CharP h.fixedField 2]
    (hC₀ : ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin (2 * 3)) (Fin (2 * 3)) F) =
      blockSwapJ (2 * 3) 3) (s : StatedSp 3 h.fixedField) :
    ((uModelSU h hC₀ s : gramSU h ((graphGram6 F : GL (Fin 6) F) :
        Matrix (Fin (2 * 3)) (Fin (2 * 3)) F)) : GL (Fin 6) F) =
      (uEmbed6 h s : GL (Fin 6) F) := by
  apply Units.ext
  rw [CFSG.SeitzReduction.SymplecticPilot.coe_uModelSU, coe_uEmbed6,
    CFSG.SeitzReduction.SymplecticPilot.coe_spModelSL, coe_sp6ToSL6,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, spModelIdx_three_eq_sp6ToSLIdx]
  rfl

theorem exists_twoUnitary6BlockCover {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
      (Φ : ctuBlock (unitaryInvolution F 2 1) 0 ({3} : Finset (Fin 4)) →* G),
      Nat.card F = (2 ^ 1) ^ 2 ∧ Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧
      Φ.ker ≤ center (ctuBlock (unitaryInvolution F 2 1) 0 ({3} : Finset (Fin 4))) ∧
      ∀ g, Φ (twoUniIota (Nat.zero_le 1) hι g) = ((e.symm (c3LeviHom K g) : L) : G) := by
  obtain ⟨F, _, _, _, h, ε, Φ, hr, hker, hn⟩ :=
    exists_twoUnitary6Cover_normalized hw e hXJ hcyc hX₀ hk
  have := fixedField_charP h
  have hF : Nat.card F = (2 ^ 1) ^ 2 := by rw [h.card]; norm_num
  set ι : K →+* F := h.fixedField.subtype.comp (ε.symm : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
    exact (h.mem_fixedField).1 (ε.symm c).2
  have hC₀ : ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin (2 * 3)) (Fin (2 * 3)) F) =
      blockSwapJ (2 * 3) 3 := coe_graphGram6 F
  set Ψ := ctuGramEquiv (m := 3) h hC₀ (RingEquiv.refl F) with hΨ
  set β := ctuBlockEquiv (unitaryInvolution F 2 1) (Nat.zero_le 1) (3 : Fin (3 + 1)) with hβ
  set Φ' : ctuBlock (unitaryInvolution F 2 1) 0 ({3} : Finset (Fin 4)) →* G :=
    Φ.comp (Ψ.toMonoidHom.comp β.toMonoidHom) with hΦ'
  have hr' : Φ'.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (Ψ.surjective.comp β.surjective), ← MonoidHom.range_eq_map, hr]
  have hker' : Φ'.ker ≤ center (ctuBlock (unitaryInvolution F 2 1) 0 ({3} : Finset (Fin 4))) :=
    ker_comp_mulEquiv_le_center Φ hker (β.trans Ψ)
  refine ⟨F, inferInstance, inferInstance, inferInstance, ι, hι, Φ', hF, hr', hker', fun g => ?_⟩
  have h1 : β (twoUniIota (Nat.zero_le 1) hι g) =
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι g :=
    CFSG.SeitzReduction.SymplecticPilot.ctuBlockEquiv_ctuEmbed (Nat.zero_le 1) hι
      (3 : Fin (3 + 1)) g (twoUniIota (Nat.zero_le 1) hι g).2
  have h2 := CFSG.SeitzReduction.SymplecticPilot.ctuGramEquiv_ctuEmbed h hC₀ (RingEquiv.refl F)
    hι ε.symm (fun c => rfl) g
  have h3 : Ψ (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι g) =
      uEmbed6 h (statedSpMap (ε.symm : K →+* h.fixedField) 3 g) :=
    Subtype.ext ((congrArg Subtype.val h2).trans (coe_uModelSU_eq_uEmbed6 h hC₀ _))
  have h4 : statedSpCongr ε 3 (statedSpMap (ε.symm : K →+* h.fixedField) 3 g) = g :=
    (statedSpCongr ε 3).apply_symm_apply g
  change Φ (Ψ (β (twoUniIota (Nat.zero_le 1) hι g))) = _
  rw [h1, h3, hn, levi6Hom]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, h4, coe_subtype]
  rfl

theorem twoGraphCoverInput_unitary6_of_values
    (hV : ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
      Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
        (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
        TwoUniBlockValues .unitary6 (Nat.zero_le 1) ι hι) :
    TwoGraphCoverInput .unitary6 := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨F, _, _, _, ι, hι, Φ, hF, hr, hker, hn⟩ :=
    exists_twoUnitary6BlockCover hw e hXJ hcyc hX₀ hk
  exact ⟨_, inferInstance, inferInstance, twoUniIota (Nat.zero_le 1) hι, Φ, hr, hker, hn,
    twoGraphCoverModel_twoUniIota hK hF (Nat.zero_le 1) hι (hV K F hK hF ι hι)⟩

theorem twoOverlapInvAt_unitary6_of_values
    (hV : ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
      Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
        (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
        TwoUniBlockValues .unitary6 (Nat.zero_le 1) ι hι) :
    TwoOverlapInvAt .unitary6 :=
  twoOverlapInvAt_of_coverInput (twoGraphCoverInput_unitary6_of_values hV)

end CFSG.SeitzReduction.F4Pilot
