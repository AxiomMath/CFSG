module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBArith
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicCoverReduce
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.GH74.GLS.LU.Local.FiveCbarF
public import CFSG.Models.Blueprint

public section

namespace CFSG.HardMathSupport.Dickson.I271.B3BLeaf

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder three_dvd_tableOrder_cases)
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  (exists_noncomm_quotient_center_of_quasisimple)

theorem card_mulAut_dvd_of_centerQuot {M Q : Type*} [Group M] [Group.IsPerfect M] [Group Q]
    (e : M ⧸ Subgroup.center M ≃* Q) : Nat.card (MulAut M) ∣ Nat.card (MulAut Q) :=
  Subgroup.card_dvd_of_injective
    ((MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom M))
    ((MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective M))

theorem card_dvd_card_mulAut_of_center_eq_bot {Y : Type*} [Group Y]
    (hZ : Subgroup.center Y = ⊥) : Nat.card Y ∣ Nat.card (MulAut Y) := by
  refine Subgroup.card_dvd_of_injective (MulAut.conj : Y →* MulAut Y) fun a b hab => ?_
  have h : ∀ x : Y, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut Y => φ x) hab
    simpa only [MulAut.conj_apply] using this
  have hc : b⁻¹ * a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [← h g]
      _ = b⁻¹ * a * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem card_mulAut_le_of_outer' {G : Type*} [Group G] [Finite G] {k : ℕ}
    (h : Nat.card (Outer G) ≤ k) : Nat.card (MulAut G) ≤ k * Nat.card G := by
  have h1 := (inner G).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (inner G) ≤ Nat.card G := by
    have hsurj : Function.Surjective
        (MonoidHom.rangeRestrict (MulAut.conj : G →* MulAut G)) :=
      MonoidHom.rangeRestrict_surjective _
    exact Nat.card_le_card_of_surjective _ hsurj
  rw [h1]
  exact Nat.mul_le_mul h h2

theorem alt_case {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hA : AltCentralQuotient L) (h7 : ¬ 7 ∣ Nat.card L)
    (haut : 3 ^ 8 ∣ Nat.card (MulAut L)) : False := by
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.alt_data hA hq
  have hcard : Nat.card L = Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.center L) :=
    (Subgroup.center L).card_eq_card_quotient_mul_card_subgroup
  have hAn : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rw [Nat.card_congr e.toEquiv, hAn] at hcard
  have hn6 : n ≤ 6 := by
    by_contra hlt
    push Not at hlt
    apply h7
    rw [hcard]
    refine Dvd.dvd.mul_right ?_ _
    have h7f : 7 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨c, hc⟩ : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hdiv : n.factorial / 2 = c := by omega
    rw [hdiv]
    rw [hc] at h7f
    exact ((Nat.Prime.dvd_mul (by norm_num)).1 h7f).resolve_left (by norm_num)
  have hdvd := card_mulAut_dvd_of_centerQuot e
  interval_cases n
  · rw [CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five] at hdvd
    exact absurd (haut.trans hdvd) (by norm_num)
  · rw [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at hdvd
    exact absurd (haut.trans hdvd) (by norm_num)

theorem spor_case (hSpM : SporadicMultipliers) (hOut : SporadicOuterLeTwo)
    (hOrd : SporadicOrdersTable) {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hS : SporCentralQuotient L) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (h7 : ¬ 7 ∣ Nat.card L) (haut : 3 ^ 8 ∣ Nat.card (MulAut L)) : False := by
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hs := eq_of_three_dvd_sporadicMultiplierOrder
    (h3.trans (card_center_dvd_sporadicMultiplierOrder hSpM hq s e))
  have hcard : Nat.card L = Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.center L) :=
    (Subgroup.center L).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, hOrd s] at hcard
  have h7s : ¬ 7 ∣ sporOrd s := fun h => h7 (by rw [hcard]; exact Dvd.dvd.mul_right h _)
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h7s (by decide +kernel)
  ·
    have hsimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group := by
      haveI := hq.2
      exact e.symm.isSimpleGroup
    have hnab : ∃ a b : (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group,
        a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := exists_noncomm_quotient_center_of_quasisimple hq
      refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
      rw [map_mul, map_mul]
      exact h
    haveI : Finite (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group :=
      Finite.of_equiv _ e.toEquiv
    haveI : Finite (MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) :=
      Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
    have hZS := center_eq_bot_of_isSimpleGroup hnab
    have hOutS := hOut _ hsimple hnab TauCeti.SporadicName.J3 ⟨MulEquiv.refl _⟩
    have hdvdAut := haut.trans (card_mulAut_dvd_of_centerQuot e)
    have hSord : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group =
        orderJ3 := hOrd TauCeti.SporadicName.J3
    have hle := card_mulAut_le_of_outer' hOutS
    obtain ⟨m, hm⟩ := card_dvd_card_mulAut_of_center_eq_bot hZS
    have hpos : 0 < Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group :=
      Nat.card_pos
    have hm2 : m ≤ 2 := by
      have h2 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group * m ≤
          Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group * 2 := by
        rw [← hm, mul_comm]
        exact hle
      exact Nat.le_of_mul_le_mul_left h2 hpos
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        have : 0 < Nat.card
            (MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) := Nat.card_pos
        rw [hm, h0, mul_zero] at this
        exact lt_irrefl _ this
      · exact h0
    rw [hm, hSord] at hdvdAut
    interval_cases m <;> exact absurd hdvdAut (by decide +kernel)
  all_goals exact h7s (by decide +kernel)

theorem untwistedModel_of_all {τ : CFSG.Blueprint.Chevalley.Tag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) {S : Type} [Group S]
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    CFSG.Blueprint.UntwistedChevalleyModel S τ (q.p ^ q.exponent) := by
  have hK := CFSG.TauCetiBridge.card_fieldOf q Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨φ⟩ := hB q hv (CFSG.TauCetiBridge.fieldOf q 1) hK
  exact ⟨CFSG.TauCetiBridge.fieldOf q 1, inferInstance, inferInstance, hK.trans q.card_def,
    ⟨e.trans φ.symm⟩⟩

theorem twistedModel_of_all {t : CFSG.Blueprint.Chevalley.TwistTag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.TwistedBridgeAll t c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hm : 0 < t.order) {S : Type} [Group S]
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    CFSG.Blueprint.TwistedChevalleyModel S t (q.p ^ q.exponent) := by
  obtain ⟨φ⟩ := hB q hv (CFSG.TauCetiBridge.fieldOf q t.order)
    (CFSG.TauCetiBridge.card_fieldOf q hm) (CFSG.TauCetiBridge.frobOf q t.order)
    (CFSG.TauCetiBridge.frobOf_apply q t.order)
  refine ⟨CFSG.TauCetiBridge.fieldOf q t.order, inferInstance, inferInstance, ?_,
    CFSG.TauCetiBridge.frobOf q t.order, ?_, ⟨e.trans φ.symm⟩⟩
  · rw [CFSG.TauCetiBridge.card_fieldOf q hm, q.card_def]
  · intro x
    rw [CFSG.TauCetiBridge.frobOf_apply, q.card_def]

theorem blueprint_of_models (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) {G : Type}
    [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags ∨ t = .E6 ∨ t = .twistedE6 ∨ t = .G2)
    (h : CFSG.Models.LieModel G t n p f) : CFSG.Blueprint.LieModel G t n p f := by
  rcases ht with ht | rfl | rfl | rfl
  · exact CFSG.Models.LieModel.toBlueprint ht h
  · obtain ⟨hadm, hc | ⟨hn, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h
    · exact False.elim hc.2
    · subst hn
      cases d with
      | E6 q =>
        obtain ⟨rfl, rfl⟩ := hd
        exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hadm,
          untwistedModel_of_all hB.e6 q hv e⟩)
      | _ => exact False.elim hd
  · obtain ⟨hadm, hc | ⟨hn, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h
    · exact False.elim hc.2
    · subst hn
      cases d with
      | twistedE6 q =>
        obtain ⟨rfl, rfl⟩ := hd
        exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hadm,
          twistedModel_of_all hB.twistedE6 q hv (by decide) e⟩)
      | _ => exact False.elim hd
  · obtain ⟨hadm, hc | ⟨hn, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h
    · exact False.elim hc.2
    · subst hn
      cases d with
      | G2 q =>
        obtain ⟨rfl, rfl⟩ := hd
        exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hadm,
          untwistedModel_of_all hB.g2 q hv e⟩)
      | _ => exact False.elim hd

theorem tag_of_three_dvd {t : StatedLieTag} {n p f : ℕ} (h3t : 3 ∣ tableOrder t n p f) :
    t ∈ CFSG.Blueprint.classicalTags ∨ t = .E6 ∨ t = .twistedE6 ∨ t = .G2 := by
  rcases three_dvd_tableOrder_cases h3t with
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl (by decide)

theorem lie_survivor {t : StatedLieTag} {n p f X : ℕ} (hadm : StatedLieAdmissible t n p f)
    (h3t : 3 ∣ tableOrder t n p f)
    (hX : X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f))
    (hpow : p ^ (lieSylowExponent t n * f) ∣ X) (hXB : X ∣ orderBabyMonster)
    (h7X : ¬ 7 ∣ X) : t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  rcases three_dvd_tableOrder_cases h3t with
    ⟨rfl, h3n, h3q⟩ | ⟨rfl, h3n, h3q⟩ | ⟨rfl, h3q⟩ | ⟨rfl, h3q⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  ·
    exfalso
    obtain ⟨hp, hf, hn2, -⟩ := hadm
    rcases (show n = 3 ∨ 6 ≤ n by omega) with rfl | hn6
    · exact psl_three_false hp hf h3q hX (by simpa [lieSylowExponent] using hpow) hXB h7X
    · exact h7X (seven_dvd_psl hn6 hX)
  ·
    exfalso
    obtain ⟨hp, hf, hn3, hne⟩ := hadm
    rcases (show n = 3 ∨ 6 ≤ n by omega) with rfl | hn6
    · exact psu_three_false hp hf (fun h => hne (by rw [h])) h3q hX
        (by simpa [lieSylowExponent] using hpow) hXB h7X
    · exact h7X (seven_dvd_psu hn6 hX)
  · exact (h7X (seven_dvd_e6 hX)).elim
  · exact (h7X (seven_dvd_twistedE6 hX)).elim
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact (not_dead hX hXB h7X dead_orthogonal_odd).elim
  · exact (not_dead hX hXB h7X dead_g2).elim
  · exact (not_dead hX hXB h7X dead_unitary_four).elim

theorem lie_case (hGA : GriessAllModelsStatement) (hLO : LieOrderFormulasInput)
    (hBA : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hL : LieCentralQuotient L) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (h7 : ¬ 7 ∣ Nat.card L) (hB : Nat.card L ∣ orderBabyMonster)
    (haut : 3 ^ 8 ∣ Nat.card (MulAut L)) : False := by
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  obtain ⟨idx, ⟨e⟩⟩ := hL
  obtain ⟨t, n, p, f, hm⟩ := exists_lieModel idx
  have hadm : StatedLieAdmissible t n p f := hm.1
  have hq' : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq⟩
  have hdvd := center_dvd_table hGA hq' e hm
  have h3t : 3 ∣ tableOrder t n p f := h3.trans hdvd
  have hmB := blueprint_of_models hBA (tag_of_three_dvd h3t) hm
  obtain ⟨-, hX, hsyl⟩ := hLO _ t n p f hadm hmB
  have hXcard : Nat.card (TauCeti.CFSGIndex.lie idx).Group = Nat.card (L ⧸ Subgroup.center L) :=
    (Nat.card_congr e.toEquiv).symm
  have hXL : Nat.card (TauCeti.CFSGIndex.lie idx).Group ∣ Nat.card L := by
    rw [hXcard]
    exact Subgroup.card_quotient_dvd_card _
  have h7X : ¬ 7 ∣ Nat.card (TauCeti.CFSGIndex.lie idx).Group := fun h => h7 (h.trans hXL)
  have hpow : p ^ (lieSylowExponent t n * f) ∣ Nat.card (TauCeti.CFSGIndex.lie idx).Group := by
    rw [← hsyl]
    exact Nat.ordProj_dvd _ _
  obtain ⟨rfl, rfl, rfl, rfl⟩ := lie_survivor hadm h3t hX hpow (hXL.trans hB) h7X
  have hL2 : CFSG.GH74.GLS.HasL2Model (TauCeti.CFSGIndex.lie idx).Group (fun r => r = 9) :=
    ⟨3, 2, Nat.prime_three, by norm_num, by norm_num, hmB⟩
  obtain ⟨b⟩ := CFSG.GH74.GLS.C3.Layer1.Back.nonempty_alt6_of_hasL2Model9 hL2
  have hdvd' := card_mulAut_dvd_of_centerQuot (e.trans b)
  rw [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at hdvd'
  exact absurd (haut.trans hdvd') (by norm_num)

theorem b3b_leaf_catalogue (hGA : GriessAllModelsStatement) (hLO : LieOrderFormulasInput)
    (hBA : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hSpM : SporadicMultipliers) (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (h7 : ¬ 7 ∣ Nat.card L) (hB : Nat.card L ∣ orderBabyMonster)
    (haut : 3 ^ 8 ∣ Nat.card (MulAut L)) : False := by
  rcases centralQuotient_family hq hK with hA | hL | hS
  · exact alt_case hq hA h7 haut
  · exact lie_case hGA hLO hBA hq hL h3 h7 hB haut
  · exact spor_case hSpM hOut hOrd hq hS h3 h7 haut

end CFSG.HardMathSupport.Dickson.I271.B3BLeaf
