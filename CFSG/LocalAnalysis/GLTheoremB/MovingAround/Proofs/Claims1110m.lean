module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110l2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusGL
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Two
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveSetOrbit
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110fb
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110k2
public import Certificates.Certificate13502

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m

open CFSG.Open

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem statedScalars_eq_bot_of_card_two_d4cls {F : Type} [Field F] (hF : Nat.card F = 2) :
    StatedScalars ι F = ⊥ := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite F
  have hc : Fintype.card Fˣ = 1 := by rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  haveI : Subsingleton Fˣ := Fintype.card_le_one_iff_subsingleton.mp hc.le
  unfold StatedScalars
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [Subsingleton.elim u 1, map_one]
  exact Subgroup.one_mem _

theorem nonempty_statedProj_equiv_of_card_two_d4cls {F : Type} [Field F] (hF : Nat.card F = 2)
    (H : Subgroup (GL ι F)) : Nonempty (StatedProj H ≃* H) := by
  have h : (StatedScalars ι F).subgroupOf H = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two_d4cls hF, Subgroup.bot_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem glMap_injective_d4cls {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (e : F →+* F')) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun M : GL ι F' => (M : Matrix ι ι F') i j) h
  simp only [Matrix.GeneralLinearGroup.map_apply, RingHom.coe_coe] at h1
  exact e.injective h1

theorem nonempty_statedOmega_plus_equiv_d4cls {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    (n : ℕ) :
    Nonempty (↥(StatedOmega (StatedQuadPlus n F)) ≃* ↥(StatedOmega (StatedQuadPlus n F'))) := by
  have hQ : ∀ v : Fin n ⊕ Fin n → F,
      StatedQuadPlus n F' (fun i => e (v i)) = e (StatedQuadPlus n F v) := by
    intro v
    simp only [StatedQuadPlus, map_sum, map_mul]
  rw [CFSG.Quasithin.G11.Harris.L2.statedOmega_map_eq e _ _ hQ]
  exact ⟨Subgroup.equivMapOfInjective _ _ (glMap_injective_d4cls e)⟩

theorem nonempty_statedOmega_minus_equiv_d4cls {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    (n : ℕ) (b c : F) :
    Nonempty (↥(StatedOmega (StatedQuadMinus n F b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus n F' (e b) (e c)))) := by
  have hQ : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      StatedQuadMinus n F' (e b) (e c) (fun i => e (v i)) = e (StatedQuadMinus n F b c v) := by
    intro v
    simp only [StatedQuadMinus, map_sum, map_mul, map_add, map_pow]
  rw [CFSG.Quasithin.G11.Harris.L2.statedOmega_map_eq e _ _ hQ]
  exact ⟨Subgroup.equivMapOfInjective _ _ (glMap_injective_d4cls e)⟩

theorem nonempty_ringEquiv_zmod_two_d4cls {F : Type} [Field F] (hF : Nat.card F = 2) :
    Nonempty (F ≃+* ZMod 2) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 2) (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF])⟩

theorem nonempty_equiv_omegaPlus_of_model_d4cls {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n 2 1) :
    Nonempty (G ≃* ↥(StatedOmega (StatedQuadPlus n (ZMod 2)))) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
  obtain ⟨f⟩ := nonempty_statedProj_equiv_of_card_two_d4cls hF2 (StatedOmega (StatedQuadPlus n F))
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two_d4cls hF2
  obtain ⟨g⟩ := nonempty_statedOmega_plus_equiv_d4cls σ n
  exact ⟨(e.trans f).trans g⟩

theorem eq_one_of_irreducible_zmod_two_d4cls (b c : ZMod 2) (h : ∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) :
    b = 1 ∧ c = 1 := by
  revert h
  revert b c
  decide

theorem nonempty_equiv_omegaMinus_of_model_d4cls {G : Type} [Group G] {n : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n 2 1) :
    Nonempty (G ≃* ↥(StatedOmega (StatedQuadMinus n (ZMod 2) 1 1))) := by
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
  obtain ⟨f⟩ := nonempty_statedProj_equiv_of_card_two_d4cls hF2
    (StatedOmega (StatedQuadMinus n F b c))
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two_d4cls hF2
  obtain ⟨g⟩ := nonempty_statedOmega_minus_equiv_d4cls σ n b c
  have hbc' : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hbc (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  obtain ⟨hb, hc⟩ := eq_one_of_irreducible_zmod_two_d4cls _ _ hbc'
  rw [hb, hc] at g
  exact ⟨(e.trans f).trans g⟩

end Transport

section D4Facts

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs PSimple)
open CFSG.LocalAnalysis.GLTheoremA (chev2Spor chev2Small chev2L34)

theorem isChevSimple_two_of_lieModel_D4_d4cls {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) : IsChevSimple 2 D := by
  let q₂ : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (TauCeti.LieTypeIndex.D 4 q₂).Valid := by simp
  have hm : CFSG.Models.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q₂, hv⟩) .POmegaPlus 4 2 1 :=
    CFSG.Models.lieModel_D 4 q₂ hv (MulEquiv.refl _)
  obtain ⟨f⟩ := nonempty_equiv_omegaPlus_of_model_d4cls
    (Claims1110l.statedClassicalModel_of_lieModel_D4 hm)
  obtain ⟨g⟩ := nonempty_equiv_omegaPlus_of_model_d4cls
    (Claims1110l.statedClassicalModel_of_lieModel_D4 hD)
  refine Or.inl ⟨.lie ⟨.D 4 q₂, hv⟩, ?_, ⟨g.trans f.symm⟩⟩
  show (TauCeti.LieTypeIndex.D 4 q₂).characteristic = 2
  rw [TauCeti.LieTypeIndex.characteristic_D]

theorem card_le_of_catalogIs_chev2Spor_d4cls
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T] [Finite T]
    (h : catalogIs T chev2Spor) : Nat.card T ≤ 25920 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact absurd hi (by simp [chev2Spor, chev2Small, chev2L34])
  | sporadic s => exact absurd hi (by simp [chev2Spor, chev2Small, chev2L34])
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by
      rcases hi with hi | hi
      · exact hi
      · exact absurd hi (by simp [chev2L34])
    rw [Nat.card_congr e.toEquiv]
    rcases hn' with rfl | rfl | rfl <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide
  | lie d =>
    rw [hb d T ⟨e⟩]
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      rcases r with _ | _ | _ | r
      · simp [chev2Spor, chev2Small, chev2L34] at hi
      · have hq : q.card = 7 ∨ q.card = 8 := by simpa [chev2Spor, chev2Small, chev2L34] using hi
        show CFSG.Open.orderA 1 q.card ≤ 25920
        rcases hq with hq | hq <;> rw [hq] <;> decide
      · have hq : q.card = 4 := by simpa [chev2Spor, chev2Small, chev2L34] using hi
        show CFSG.Open.orderA 2 q.card ≤ 25920
        rw [hq]
        decide
      · simp [chev2Spor, chev2Small, chev2L34] at hi
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [chev2Spor, chev2Small, chev2L34] at hi
      · simp [chev2Spor, chev2Small, chev2L34] at hi
      · have hq : q.card = 3 := by simpa [chev2Spor, chev2Small, chev2L34] using hi
        show CFSG.Open.orderTwistedA 2 q.card ≤ 25920
        rw [hq]
        decide
      · have hq : q.card = 2 := by simpa [chev2Spor, chev2Small, chev2L34] using hi
        show CFSG.Open.orderTwistedA 3 q.card ≤ 25920
        rw [hq]
        decide
      · simp [chev2Spor, chev2Small, chev2L34] at hi
    | _ => simp [chev2Spor, chev2Small, chev2L34] at hi

theorem exists_comp_of_pumpup_d4cls {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    {x : MulAut K} (hx : Lemma1314.PumpupVia 5 D K x) :
    ∃ J₁ : Subgroup K,
      GLAPComponent 5 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) J₁ ∧
        Nonempty (PSimple 5 J₁ ≃* D) := by
  obtain ⟨-, J1, hJ1, ⟨eJ⟩⟩ := hx
  refine ⟨J1, ?_, ⟨?_⟩⟩
  · rw [show CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x = Lemma1314.fixSub x from
      Subgroup.ext fun _ => Iff.rfl]
    exact hJ1
  · exact (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
      (Inputs1419.quotCenterEquivOfBot (Claims1110l.center_eq_bot_of_lieModel_D4 hD))

theorem dvd_card_of_pumpup_d4cls {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    {x : MulAut K} (hx : Lemma1314.PumpupVia 5 D K x) : 174182400 ∣ Nat.card K := by
  obtain ⟨-, J1, -, ⟨eJ⟩⟩ := hx
  rw [← Claims1110l.card_of_lieModel_D4_two hD, ← Nat.card_congr eJ.toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J1)

theorem dvd_card_quot_of_pumpup_d4cls {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hO : GLAPPrimeCore 5 K = ⊥) {x : MulAut K} (hx : Lemma1314.PumpupVia 5 D K x) :
    2 ^ 12 * 3 ^ 5 * 7 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have h1 := dvd_card_of_pumpup_d4cls hD hx
  have hZ := SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_five hO
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have h2 : Nat.card K = Nat.card (K ⧸ Subgroup.center K) * 5 ^ k := by
    rw [← hk]
    exact (Subgroup.center K).card_eq_card_quotient_mul_card_subgroup
  have h3 : 2 ^ 12 * 3 ^ 5 * 7 ∣ Nat.card (K ⧸ Subgroup.center K) * 5 ^ k := by
    rw [← h2]
    exact (show 2 ^ 12 * 3 ^ 5 * 7 ∣ 174182400 by norm_num).trans h1
  have hcop : Nat.Coprime (2 ^ 12 * 3 ^ 5 * 7) (5 ^ k) :=
    Nat.Coprime.pow_right _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_right h3

end D4Facts

section Spor

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs PSimple)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)

theorem false_of_crow_d4cls (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    (hrow : CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CRow s 5) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (f : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic s).Group) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  obtain ⟨J1, hJ1, ⟨e1⟩⟩ := exists_comp_of_pumpup_d4cls hD hx
  obtain ⟨t, ht, I, hI, ⟨eI⟩⟩ :=
    Inputs1419b.exists_spor_comp hOut Nat.prime_five (by norm_num) hK f hx.1 hJ1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hβ5 : MulAut.conj t ^ 5 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hβ1 : MulAut.conj t ≠ 1 := by
    intro h1
    have htc : t ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : t * g * t⁻¹ = g := by
        have := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ g) h1
        simpa [MulAut.conj_apply] using this
      calc g * t = t * g * t⁻¹ * t := by rw [h2]
        _ = t * g := by group
    rw [hcen, Subgroup.mem_bot] at htc
    rw [htc, orderOf_one] at ht
    norm_num at ht
  have hI' : GLAPComponent 5 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj t)) I := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj]
    exact hI
  have hT := hrow (K ⧸ Subgroup.center K) ⟨f⟩ Nat.prime_five (by norm_num) _ hβ5 hβ1 I hI'
  let eID : PSimple 5 I ≃* D := eI.symm.trans e1
  have hchev : IsChevSimple 2 (PSimple 5 I) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr eID.symm
      (isChevSimple_two_of_lieModel_D4_d4cls hD)
  have hc := card_le_of_catalogIs_chev2Spor_d4cls hb (hT hchev)
  rw [Nat.card_congr eID.toEquiv, Claims1110l.card_of_lieModel_D4_two hD] at hc
  norm_num at hc

theorem false_of_sporTypes_d4cls (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    {Good : ∀ (T : Type) [Group T], Prop}
    (htab : CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables.SporTypes 5 Good s)
    (hG : ∀ (T : Type) [Group T], Good T → Nat.card T ≠ 174182400) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (f : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic s).Group) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  obtain ⟨J1, hJ1, ⟨e1⟩⟩ := exists_comp_of_pumpup_d4cls hD hx
  obtain ⟨t, ht, I, hI, ⟨eI⟩⟩ :=
    Inputs1419b.exists_spor_comp hOut Nat.prime_five (by norm_num) hK f hx.1 hJ1
  have h := htab (K ⧸ Subgroup.center K) ⟨f⟩ t ht I hI
  apply hG _ h
  rw [Nat.card_congr (eI.symm.trans e1).toEquiv, Claims1110l.card_of_lieModel_D4_two hD]

end Spor

section Free

theorem isOmegaTwo_of_catalog_D_two_d4cls (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 5 K = ⊥) {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D m q).Valid) (hq : q.card = 2)
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie ⟨.D m q, hv⟩).Group) :
    4 ≤ m ∧ IsOmegaTwo true m K := by
  obtain ⟨hp, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 1)
    Nat.prime_two (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D m q hv e
  rw [hp, hf] at hm
  have hr : 4 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hZ := SchurFacts.center_eq_bot_of_lieModel_omega hGA Nat.prime_five (by norm_num) hK hO
    (Or.inl rfl) hm
  have hcls : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus m 2 1 :=
    hm.2.elim id fun h0 => absurd h0.1 (by omega)
  obtain ⟨g⟩ := nonempty_equiv_omegaPlus_of_model_d4cls hcls
  exact ⟨hr, show Nonempty (K ≃* _) from ⟨(Inputs1419.quotCenterEquivOfBot hZ).symm.trans g⟩⟩

theorem isOmegaTwo_of_catalog_twistedD_two_d4cls (hGA : GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 5 K = ⊥) {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedD m q).Valid) (hq : q.card = 2)
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD m q, hv⟩).Group) :
    4 ≤ m ∧ IsOmegaTwo false m K := by
  obtain ⟨hp, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 1)
    Nat.prime_two (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_twistedD m q hv e
  rw [hp, hf] at hm
  have hr : 4 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hZ := SchurFacts.center_eq_bot_of_lieModel_omega hGA Nat.prime_five (by norm_num) hK hO
    (Or.inr rfl) hm
  have hcls : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus m 2 1 :=
    hm.2.elim id fun h0 => absurd h0.1 (by omega)
  obtain ⟨g⟩ := nonempty_equiv_omegaMinus_of_model_d4cls hcls
  exact ⟨hr, show Nonempty (K ≃* _) from ⟨(Inputs1419.quotCenterEquivOfBot hZ).symm.trans g⟩⟩

theorem lieModel_of_catalog_D4_32_d4cls (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq : q.card = 32)
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) :
    CFSG.Models.LieModel K .POmegaPlus 4 2 5 := by
  obtain ⟨hp, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 5)
    Nat.prime_two (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [hp, hf] at hm
  have hq' : CFSG.IsQuasisimple K := ⟨Group.isPerfect_def.mpr hK.1, hK.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK⟩
  have hdvd := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hq'
    (MulEquiv.refl _) hm
  have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 5 = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders, Nat.even_iff]
  have hx : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 5 = (1, 1) := rfl
  rw [hg, hx] at hdvd
  have hZ : Subgroup.center K = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one (by simpa using hdvd))
  have hcls : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus 4 2 5 :=
    hm.2.elim id fun h0 => absurd h0.1 (by norm_num)
  exact ⟨hm.1, Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (Inputs1419.quotCenterEquivOfBot hZ) hcls)⟩

end Free

section Small

theorem not_three_dvd_orderSuzuki_d4cls (m : ℕ) :
    ¬ 3 ∣ CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) := by
  intro h
  have h1 : ((CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) : ℕ) : ZMod 3) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 3) 3 _).2 h
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have h2 : (2 : ZMod 3) ^ (2 * m + 1) = 2 := by
    rw [pow_succ, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow, one_mul]
  unfold CFSG.Open.orderSuzuki at h1
  push_cast [Nat.cast_sub hq1] at h1
  rw [h2] at h1
  exact absurd h1 (by decide)

theorem false_of_suzuki_tits_d4cls (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {K : Type} [Group K] [Finite K] (hO : GLAPPrimeCore 5 K = ⊥) {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ m, d.1 = .suzuki m) ∨ d.1 = .tits)
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  have h1 := dvd_card_quot_of_pumpup_d4cls hD hO hx
  rw [hb d _ ⟨e⟩] at h1
  rcases hd with ⟨m, hm⟩ | ht
  · rw [hm] at h1
    have h3 : 3 ∣ CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) :=
      (show 3 ∣ 2 ^ 12 * 3 ^ 5 * 7 by norm_num).trans h1
    exact not_three_dvd_orderSuzuki_d4cls m h3
  · rw [ht] at h1
    have h3 : 2 ^ 12 ∣ CFSG.Open.orderTits :=
      (show 2 ^ 12 ∣ 2 ^ 12 * 3 ^ 5 * 7 by norm_num).trans h1
    exact absurd h3 (by decide)

end Small

section Reduction

@[expose] def NoD4UpOn (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K →
    GLAPPrimeCore 5 K = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, P d.1 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, ¬ Lemma1314.PumpupVia 5 D K x

theorem NoD4UpOn.or {P Q : TauCeti.LieTypeIndex → Prop} (hP : NoD4UpOn P) (hQ : NoD4UpOn Q) :
    NoD4UpOn fun d => P d ∨ Q d := by
  intro K _ _ hK hO d hd he D _ hD x hx
  rcases hd with hd | hd
  · exact hP K hK hO d hd he D hD x hx
  · exact hQ K hK hO d hd he D hD x hx

theorem NoD4UpOn.mono {P Q : TauCeti.LieTypeIndex → Prop} (hPQ : ∀ d, P d → Q d)
    (hQ : NoD4UpOn Q) : NoD4UpOn P :=
  fun K _ _ hK hO d hd he D _ hD x hx => hQ K hK hO d (hPQ d.1 hd) he D hD x hx

@[expose] def D4UpFreeIdx : TauCeti.LieTypeIndex → Prop
  | .D r q => q.card = 2 ∨ (r = 4 ∧ q.card = 32)
  | .twistedD _ q => q.card = 2
  | _ => False

@[expose] def D4UpChev2RestIdx (d : TauCeti.LieTypeIndex) : Prop :=
  d.characteristic = 2 ∧ ¬ D4UpFreeIdx d

@[expose] def D4UpSzTitsIdx (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ m, d = .suzuki m) ∨ d = .tits

theorem noD4UpOn_szTits_d4cls (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    NoD4UpOn D4UpSzTitsIdx :=
  fun _ _ _ _ hO _ hd ⟨e⟩ _ _ hD _ hx => false_of_suzuki_tits_d4cls hb hO hd e hD hx

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables (SporTypes)
open CFSG.LocalAnalysis.GLTheoremA.Chev2Rows (CRow)

theorem inputD4UpClassChev2Spor_of_noD4UpOn_d4cls
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hCo1 : CRow .Co1 5) (hTh : CRow .Th 5) (hHN : CRow .HN 5)
    (hB5 : SporTypes 5 (fun T _ => Nat.card T = 44352000 ∨ ¬ 7 ∣ 5 * Nat.card T) .B)
    (hM5 : SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M)
    (hC : NoD4UpOn D4UpChev2RestIdx) : Claims1110l.InputD4UpClassChev2Spor := by
  intro K _ _ hK hO hcase D _ hD x hx
  rcases hcase with ⟨s, hs, ⟨f⟩⟩ | ⟨d, ⟨e⟩, hd2⟩
  · exfalso
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact false_of_crow_d4cls hb hOut hCo1 hD hK.1 f hx
    · exact false_of_crow_d4cls hb hOut hTh hD hK.1 f hx
    · exact false_of_crow_d4cls hb hOut hHN hD hK.1 f hx
    · refine false_of_sporTypes_d4cls hOut hB5 (fun T _ h hc => ?_) hD hK.1 f hx
      rw [hc] at h
      rcases h with h | h
      · norm_num at h
      · exact h (by norm_num)
    · refine false_of_sporTypes_d4cls hOut hM5 (fun T _ h hc => ?_) hD hK.1 f hx
      rw [hc] at h
      norm_num at h
  · by_cases hfree : D4UpFreeIdx d.1
    · obtain ⟨d, hv⟩ := d
      cases d with
      | D r q =>
        rcases hfree with hq | ⟨rfl, hq⟩
        · obtain ⟨hr, hΩ⟩ := isOmegaTwo_of_catalog_D_two_d4cls hGA hK.1 hO hv hq e
          exact Or.inl ⟨true, r, hr, hΩ⟩
        · exact Or.inr (lieModel_of_catalog_D4_32_d4cls hGA hK.1 hv hq e)
      | twistedD r q =>
        obtain ⟨hr, hΩ⟩ := isOmegaTwo_of_catalog_twistedD_two_d4cls hGA hK.1 hO hv hfree e
        exact Or.inl ⟨false, r, hr, hΩ⟩
      | _ => exact hfree.elim
    · exact (hC K hK hO d ⟨hd2, hfree⟩ ⟨e⟩ D hD x hx).elim

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m
