module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Cut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpO3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSyl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpRk
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSL
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpDataProof

open CFSG.Open K421MonoProof K421OrbProof K421AbsProof K421SylProof K421LinProof K421SpProof
  K421SpCWProof K421SpSylProof

theorem two_le_pRank_of_rankTwoAt {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {x : X}
    (h : RankTwoAt p x) : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨A, B, _, _, _, _, φ, hφ, hle, hA, hB⟩ := h
  exact K421SpRkProof.two_le_pRank_of_prod hA hB φ hφ hle

section Types

theorem exists_le_two_weight : ∀ u v : V3, Indep u v →
    ∃ a b : ZMod 3, a • u + b • v ≠ 0 ∧ nz (a • u + b • v) ≤ 2 := by
  unfold Indep nz
  decide +kernel

variable {G : Type} [Group G] [Finite G] {D : Mono81 G}

theorem exists_type_sp (hSP : SignedPerms D)
    (hconj : ∀ E : Subgroup G, IsElemAbelian 3 E →
      ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ D.A0) {e : G} (he : orderOf e = 3) :
    ∃ t : Fin 3, IsType D e t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsElemAbelian 3 (Subgroup.zpowers e) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have hx3 : (⟨x, hx⟩ : Subgroup.zpowers e) ^ Nat.card (Subgroup.zpowers e) = 1 :=
      pow_card_eq_one'
    rw [Nat.card_zpowers, he] at hx3
    simpa using congrArg Subtype.val hx3
  obtain ⟨g, hg⟩ := hconj _ hE
  have heA : g * e * g⁻¹ ∈ D.A0 := by
    have := hg (Subgroup.mem_map.2 ⟨e, Subgroup.mem_zpowers e, rfl⟩)
    simpa [MulAut.conj_apply] using this
  obtain ⟨x, hx⟩ := D.mem_A0_iff.1 heA
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, D.av_zero] at hx
    have he1 : e = 1 := by
      have h1 : e = g⁻¹ * (g * e * g⁻¹) * g := by group
      rw [h1, hx]
      group
    rw [he1, orderOf_one] at he
    omega
  obtain ⟨t, -, ht⟩ := isType_of_conj hSP hx0 hx
  exact ⟨t, ht⟩

theorem exists_type_ne_two_of_card_nine (hSP : SignedPerms D)
    (hconj : ∀ E : Subgroup G, IsElemAbelian 3 E →
      ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ D.A0)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    ∃ c ∈ E, c ≠ 1 ∧ ∃ t : Fin 3, t ≠ 2 ∧ IsType D c t := by
  obtain ⟨g, hg⟩ := hconj E hE
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h9]
  obtain ⟨u, v, huv, hu, hv⟩ := exists_indep D hg hcard
  obtain ⟨c₁, d₁, hx0, hle⟩ := exists_le_two_weight u v huv
  have hxH := av_span_mem D hu hv c₁ d₁
  obtain ⟨e, heE, hex⟩ := Subgroup.mem_map.1 hxH
  have hge : g * e * g⁻¹ = D.av (c₁ • u + d₁ • v) := by simpa [MulAut.conj_apply] using hex
  refine ⟨e, heE, ?_, ?_⟩
  · intro he1
    rw [he1] at hge
    have : D.av (c₁ • u + d₁ • v) = 1 := by rw [← hge]; group
    exact hx0 (D.av_inj (this.trans D.av_zero.symm))
  · obtain ⟨t, hnz, hty⟩ := isType_of_conj hSP hx0 hge
    refine ⟨t, ?_, hty⟩
    intro ht2
    subst ht2
    simp at hnz
    omega

end Types

section Classes

variable {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}

theorem caseAWit (hp : p.Prime) (hpF : p ∣ Nat.card F + 1) (h4 : 4 ≤ Nat.card F) (t : Fin 3)
    (ht : t ≠ 2 ∨ ¬ 3 ∣ Nat.card F - 1) :
    RankTwoAt p ((monoSp F).av (rep t)) ∧ SimpleAt p ((monoSp F).av (rep t)) := by
  have hpS := K421SpSLProof.sl2_dvd_card_of_dvd_succ hpF
  have hS := K421SpSLProof.isSimpleGroup_sl2_charTwo h4
  have hne := K421SpSLProof.sl2_card_ne_of_dvd_succ hp hpF h4
  haveI : Fintype F := Fintype.ofFinite F
  fin_cases t
  · exact ⟨rankTwoAt_rep0 hpS, (simpleAt_rep01 hS hpS hne).1⟩
  · by_cases h3 : 3 ∣ Nat.card F - 1
    · obtain ⟨ω, hω⟩ := K421SpCountProof.spc_exists_root (F := F) h3
      exact ⟨rankTwoAt_rep1_split hω hpS, (simpleAt_rep01 hS hpS hne).2⟩
    · have hT : p ∣ Nat.card ↥(Tall F) := by
        rw [card_Tall, tc, if_neg h3]
        exact hpF
      exact ⟨rankTwoAt_rep1 hT hpS, (simpleAt_rep01 hS hpS hne).2⟩
  · have h3 : ¬ 3 ∣ Nat.card F - 1 := ht.resolve_left (fun h => h rfl)
    have hT : p ∣ Nat.card ↥(Tall F) := by
      rw [card_Tall, tc, if_neg h3]
      exact hpF
    exact ⟨rankTwoAt_rep2 hT, simpleAt_rep2 hS hpS hne⟩

theorem data421_of_equiv (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : p ∣ Nat.card F + 1)
    {S : Type} [Group S] [Finite S] (ε : S ≃* ↥(SpI F)) : Data421 S p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpF
    omega
  have hSP : SignedPerms (monoSp F) := signedPerms_monoSp F
  have hconj : ∀ E : Subgroup ↥(SpI F), IsElemAbelian 3 E →
      ∃ g : ↥(SpI F), E.map (MulAut.conj g).toMonoidHom ≤ (monoSp F).A0 :=
    fun E hE => hconj_sp F hE
  have hcaseA : ∀ {x : S} {t : Fin 3}, IsType (monoSp F) (ε x) t →
      (t ≠ 2 ∨ ¬ 3 ∣ Nat.card F - 1) →
      2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({x} : Set S)) ∧
        ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer ({x} : Set S)) := by
    intro x t hty ht
    obtain ⟨n, hn⟩ := hty
    obtain ⟨hR, hSi⟩ := caseAWit hp hpF h4 t ht
    have hR' : RankTwoAt p x := (RankTwoAt.conj hn hR).of_equiv ε
    have hS' : SimpleAt p x := (SimpleAt.conj hn hSi).of_equiv ε
    exact ⟨two_le_pRank_of_rankTwoAt hR', hS'.not_isPSolvable⟩
  refine ⟨?_, ?_⟩
  · intro D hD
    obtain ⟨x, hx, rfl⟩ := exists_zpowers_of_card_three hD
    have hx' : orderOf (ε x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    obtain ⟨t, hty⟩ := exists_type_sp hSP hconj hx'
    rw [centralizer_zpowers_eq]
    by_cases hc : t ≠ 2 ∨ ¬ 3 ∣ Nat.card F - 1
    · left
      obtain ⟨h1, h2⟩ := hcaseA hty hc
      exact ⟨by omega, h2⟩
    · right
      have ht2 : t = 2 := by
        by_contra h
        exact hc (Or.inl h)
      have h3 : 3 ∣ Nat.card F - 1 := by
        by_contra h
        exact hc (Or.inr h)
      have hN : Nat.card F % 3 = 1 := by omega
      subst ht2
      refine ⟨sylowShape_of_type_two hN ε hty, ?_⟩
      obtain ⟨n, hn⟩ := hty
      have hpS := K421SpSLProof.sl2_dvd_card_of_dvd_succ hpF
      have h1 : RankOneAt p x := ((K421SpProof.rankOneAt_rep2 hpS).conj hn).of_equiv ε
      have h2 := h1.one_le_pRank
      omega
  · intro E hE h9
    have hE' : IsElemAbelian 3 (E.map ε.toMonoidHom) :=
      K21bTransProof.isElemAbelian_map_inj ε.injective hE
    have h9' : Nat.card (E.map ε.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ε.injective, h9]
    obtain ⟨c', hc'E, hc'1, t, ht2, hty⟩ := exists_type_ne_two_of_card_nine hSP hconj hE' h9'
    obtain ⟨c, hcE, rfl⟩ := Subgroup.mem_map.1 hc'E
    have hc3 : c ^ 3 = 1 := hE.2 c hcE
    have hc1 : c ≠ 1 := fun h => hc'1 (by rw [h, map_one])
    have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hty' : IsType (monoSp F) (ε c) t := hty
    refine ⟨Subgroup.zpowers c, (Subgroup.zpowers_le).2 hcE, by rw [Nat.card_zpowers, hcord], ?_⟩
    rw [centralizer_zpowers_eq]
    obtain ⟨h1, h2⟩ := hcaseA hty' (Or.inl ht2)
    exact ⟨by omega, h2⟩

end Classes

section Transport

theorem exists_equiv_of_isSpSix {c : ℕ → Prop} {S : Type} [Group S] (h : IsSpSix c S) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      c (Nat.card F) ∧ Nonempty (S ≃* CFSG.Open.StatedSp 3 F) := by
  obtain ⟨Q, hQp, hc, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d0, hv⟩ := d
  dsimp only at hd
  subst hd
  haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
  haveI hFin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hFcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) = Q.card := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic ⟨.B 3 Q, hv⟩ = Q.p from
        TauCeti.LieTypeIndex.characteristic_B 3 Q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B 3 Q, hv⟩ = Q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_B 3 Q]
    exact (TauCeti.PrimePower.card_def Q).symm
  have hev : 2 ∣ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) := by
    rw [hFcard, TauCeti.PrimePower.card_def, hQp]
    exact dvd_pow_self 2 Q.exponent_pos.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) 2 := by
    haveI : Fintype ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) := Fintype.ofFinite _
    refine charP_of_card_eq_prime_pow (f := Q.exponent) ?_
    rw [← Nat.card_eq_fintype_card, hFcard, TauCeti.PrimePower.card_def, hQp]
  let eB := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 Q hv hQp le_rfl
  exact ⟨_, inferInstance, hFin, hchar, by rw [hFcard]; exact hc,
    ⟨(e.trans eB).trans (K421RProof.statedSpEquivProj hev).symm⟩⟩

end Transport

theorem K421DataSp_holds : K421DataSp := by
  intro S _ _ p hp hp5 h
  obtain ⟨F, _, _, _, hc, ⟨e⟩⟩ := exists_equiv_of_isSpSix h
  exact data421_of_equiv hp hp5 hc (e.trans (spIEquiv F).symm)

end K421SpDataProof

end CFSG.LocalAnalysis.RankThreeUC.S15
