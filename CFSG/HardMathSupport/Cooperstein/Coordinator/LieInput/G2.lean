module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.ChevLink
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.LeviBlock CFSG.LieType.CurtisTits

section G2


theorem set_fin_two_cases {I : Set (Fin 2)} (hI : I ≠ Set.univ) : I = ∅ ∨ ∃ i, I = {i} := by
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
  · exact absurd (Set.eq_univ_of_forall fun i => by fin_cases i <;> assumption) hI
  · exact Or.inr ⟨0, Set.ext fun i => by fin_cases i <;> simp [h0, h1]⟩
  · exact Or.inr ⟨1, Set.ext fun i => by fin_cases i <;> simp [h0, h1]⟩
  · exact Or.inl (Set.ext fun i => by fin_cases i <;> simp [h0, h1])

theorem leviOb_g2 {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {Y : Type} [Group Y] (π : ↥(adjointGroup .G2 F) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center ↥(adjointGroup .G2 F))
    (I : Set (Fin (Tag.rank .G2))) (hI : I ≠ Set.univ) :
    LeviOb (g2Datum F) (torus (τ := .G2) F) π I := by
  have hct := g2_isCTGroupDatum F
  have hext := g2_steinbergExtras F
  have hT : Group.IsSolvable ↥(⨆ k, torus (τ := .G2) F k) :=
    Group.isSolvable_of_comm (fun a b => (isMulCommutative_torus hext).is_comm.comm a b)
  rcases set_fin_two_cases hI with rfl | ⟨i, rfl⟩
  · refine ⟨0, fun j => j.elim0, ⨆ k, torus (τ := .G2) F k, le_rfl, le_sup_left, hT,
      fun j => j.elim0, fun j => j.elim0, ?_⟩
    exact (leviM_empty (g2Datum F)).le.trans bot_le
  · obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := F) i
    have hM := leviM_singleton (g2Datum F) i
    refine ⟨1, fun _ => rankOne (g2Datum F).rootGroup i, ⨆ k, torus (τ := .G2) F k, le_rfl,
      le_sup_left, hT, fun _ => ⟨hM.ge, ?_, chev_of_sl2_image hF4 π hker _ eL⟩,
      fun a b hab => (hab (Subsingleton.elim a b)).elim, ?_⟩
    · exact torus_le_normalizer_rankOne (g2Datum F) hct i
    · exact (hM.le.trans (le_sup_of_le_right (le_iSup (fun _ : Fin 1 =>
        rankOne (g2Datum F).rootGroup i) 0)))

theorem simpleStmt_of_g2 {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {Y : Type} [Group Y] [Finite Y] (hcl : IsClassicalTwoOrG2 Y)
    (e : Y ≃* AdjointQuotient .G2 F) : SimpleStmt Y := by
  have hK : Finite ↥(adjointGroup .G2 F) := generated_group_finite .G2 _
  have hb := borelQuotient_g2 e
  have hqK : CFSG.IsQuasisimple ↥(adjointGroup .G2 F) :=
    isQuasisimple_g2_of_three_le_card F (by omega)
  have hcen : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 F)))) := by
    intro a b h
    have h1 := e.symm.injective h
    have h2 : (QuotientGroup.mk a : ↥(adjointGroup .G2 F) ⧸ _) = QuotientGroup.mk b := h1
    rw [QuotientGroup.eq, hcen, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  let φ := MulEquiv.ofBijective _ ⟨hinj, hb.surj⟩
  have hq : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv φ hqK
  have hZ : Subgroup.center Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨k, rfl⟩ := φ.surjective y
    have : k ∈ Subgroup.center ↥(adjointGroup .G2 F) := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply φ.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hy (φ k')
    rw [hcen, Subgroup.mem_bot] at this
    rw [this, map_one]
  have hX := CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    hcl
  have hrad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup Y) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y hX
  exact simpleStmt_of_borelQuotient hq hZ hcl hrad hb
    (fun π' hπ' I hI => leviOb_g2 hF4 π' (fun z hz => hπ'.ker_central z hz) I hI)
    (fun I hI => centOb_adjoint hI)

theorem simpleStmt_of_g2_index {Y : Type} [Group Y] [Finite Y] (hcl : IsClassicalTwoOrG2 Y)
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hdq : d.1 = .G2 q) (hp : q.p = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : SimpleStmt Y := by
  obtain ⟨d, hv⟩ := d
  have hdq' : d = .G2 q := hdq
  subst hdq'
  have hK : Nat.card (GaloisField 2 q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 q.exponent q.exponent_pos.ne', hp]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp
    (GaloisField 2 q.exponent) hK
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hF4 : 4 ≤ Nat.card (GaloisField 2 q.exponent) := by
    rw [hK]
    have h2 : q.card % 2 = 0 := by
      rw [TauCeti.PrimePower.card_def, hp]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 q.exponent_pos.ne')
    omega
  exact simpleStmt_of_g2 hF4 hcl (e.trans b.symm)

end G2

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
