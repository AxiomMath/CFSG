module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz6b
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.LinearAutCubeProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318LocalExc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310r

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsL2EightIndex Gen2318Index
  Gen2318 IsLieQuot Seitz2313Even)
open CFSG.HardMathSupport.Dickson.I271 (actPre autImage actHom mem_actPre actHom_mk
  coe_normalizerMonoidHom actPre_le_left eq_top_of_sup_center_eq_top pRank_actPre)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns (gammaPrimeIn)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open GL83.CompFam

set_option linter.unusedSectionVars false

section Tools

variable {G : Type} [Group G] [Finite G]

theorem twoLocalRank_quot_le {m : ℕ} (hS : GLStanding G m 3) (C : Subgroup G) :
    GLATwoLocalRank 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) ≤ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine csSup_le' fun k hk => ?_
  obtain ⟨H, ⟨T, hT, hT2, rfl⟩, rfl⟩ := hk
  refine CFSG.SectionRank.pRank_le (by norm_num) fun F hF hFel => ?_
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hFel
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) (InputsSeitz6.le_of_normalizes_bar hS C hFel hT2 hT hF hj)

theorem gammaPrimeIn_le_glbCore {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 2 ≤ k)
    (B K : Subgroup X) : gammaPrimeIn 3 k B K ≤ GLBCore 3 2 B :=
  iSup₂_le fun _ hE => inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore hE.1 (hk.trans hE.2)))

end Tools

section Lift


variable {X : Type} [Group X] [Finite X]

theorem le_gammaPrime_of_fixed2 {k : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hFam : ∀ P ∈ Fam, k ≤ CFSG.Open.pRank 3 (actPre B K P))
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K |
      (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} = ⊤) :
    K ≤ gammaPrimeIn 3 k B K := by
  set Γ : Subgroup X := gammaPrimeIn 3 k B K with hΓ
  set Γ₀ : Subgroup ↥K := Γ.subgroupOf K with hΓ₀
  set S : Set (↥K ⧸ Subgroup.center ↥K) :=
    {s | (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} with hS
  have hlift : ∀ s ∈ S, ∃ k' ∈ Γ₀, (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨⟨P, hP, hs⟩, hs2⟩
    obtain ⟨k', rfl, j', hk⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift.exists_twoElem_lift
        (Subgroup.center ↥K) s hs2
    refine ⟨k', ?_, rfl⟩
    show (k' : X) ∈ Γ
    have hcent : (k' : X) ∈ Subgroup.centralizer (actPre B K P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨hqN, hqB, hqP⟩ := mem_actPre.1 hq
      set k'' : ↥K := K.normalizerMonoidHom ⟨q, hqN⟩ k' with hk''
      have h1 : (QuotientGroup.mk k'' : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' := by
        have := hs _ hqP
        rwa [actHom_mk] at this
      have h2 : ∃ j : ℕ, k'' ^ (2 ^ j) = 1 := ⟨j', by rw [hk'', ← map_pow, hk, map_one]⟩
      have h3 : k'' = k' :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift.twoElem_unique hodd h2 ⟨j', hk⟩ h1
      have h4 : (k'' : X) = q * (k' : X) * q⁻¹ := coe_normalizerMonoidHom K ⟨q, hqN⟩ k'
      have h5 : q * (k' : X) * q⁻¹ = (k' : X) := by rw [← h4, h3]
      calc q * (k' : X) = q * (k' : X) * q⁻¹ * q := by group
        _ = (k' : X) * q := by rw [h5]
    have hle : K ⊓ Subgroup.centralizer (actPre B K P : Set X) ≤ Γ :=
      le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank 3 E) =>
        K ⊓ Subgroup.centralizer (E : Set X)) (actPre B K P) ⟨actPre_le_left, hFam P hP⟩ le_rfl
    exact hle ⟨k'.2, hcent⟩
  have hle : Subgroup.closure S ≤ Γ₀.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k', hk', rfl⟩ := hlift s hs
    exact ⟨k', hk', rfl⟩
  have hsup : Γ₀ ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈ Subgroup.closure S := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : Γ₀ = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ Γ₀ := by rw [htop]; exact Subgroup.mem_top _
  exact this

theorem le_gammaPrime_of_seitz {k : ℕ} {B K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hBel : IsElemAbelian 3 B)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E₀ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hE₀ : E₀ ≤ autImage B K)
    (hEel : IsElemAbelian 3 E₀) {m : ℕ} (hm : Nat.card E₀ = 3 ^ m) (hm1 : 1 ≤ m)
    (hc : k ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + (m - 1))
    (hU : ∃ U : Subgroup (↥K ⧸ Subgroup.center ↥K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
      ∀ φ ∈ E₀, ∀ u ∈ U, φ u ∈ U) :
    K ≤ gammaPrimeIn 3 k B K := by
  have hE0 : E₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hm
    have := Nat.one_lt_pow (by omega : m ≠ 0) (by norm_num : 1 < 3)
    omega
  have hgenS := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.seitz2313Even_holds 3 Nat.prime_three
    (by norm_num) _ d ⟨e⟩ hs E₀ hEel hE0 hU
  refine le_gammaPrime_of_fixed2 hperf hodd {F | F ≤ E₀ ∧ F.relIndex E₀ = 3} ?_ ?_
  · rintro F ⟨hFE, hFi⟩
    have h1 := Subgroup.relIndex_mul_card F E₀
    rw [inf_of_le_left hFE, hFi, hm] at h1
    have hFcard : Nat.card F = 3 ^ (m - 1) := by
      have h3 : 3 * Nat.card F = 3 * 3 ^ (m - 1) := by
        rw [h1, ← pow_succ']
        congr 1
        omega
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    rw [pRank_actPre Nat.prime_three hBel hperf (hFE.trans hE₀) hFcard]
    exact hc
  · exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift.closure_fixed2_eq_top_of_seitz _
      (fun F hF => hF) hgenS

end Lift

section Cases


variable {G : Type} [Group G] [Finite G]

theorem le_M_of_gen2318 (hG : Gen2318) {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    (hi : Gen2318Index i.1) : Kc ≤ M := by
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hS : GLStanding G m 3 := h.standing
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have hKG : CFSG.Open.IsKGroup ↥(Cg u) := Prop1310a5b.isKGroup_centralizer_of_standing hS hu1
  have hKQ : CFSG.Open.IsKGroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) := isKGroup_barX_quotient hKG
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hrk : GLATwoLocalRank 3 (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) ≤
      CFSG.Open.pRank 3 (barX 3 (Cg u) B) := by
    rw [hBtrk, hBm]
    exact twoLocalRank_quot_le hS (Cg u)
  have hLie : IsLieQuot ↥(barX 3 (Cg u) Kc) Gen2318Index :=
    ⟨i, hi, ⟨(Lemma1315b.centerQuotEquiv eK.symm).trans e⟩⟩
  obtain ⟨-, hgam⟩ := hG _ hKQ _ _ hKt hBtel hBtN hrk (InputsSeitz6.cen_bar_ne_bot hBel huB hu1 Kc) hLie
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (hgam.trans (gammaPrimeIn_le_glbCore (by norm_num) _ _))

theorem le_M_of_plane {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope i.1)
    {F : Subgroup (MulAut (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)))}
    (hF : F ≤ autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) (hF9 : 9 ≤ Nat.card F)
    {V : Subgroup (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))}
    (hV : IsPGroup 2 ↥V) (hVF : ∀ φ ∈ F, ∀ x ∈ V, φ x ∈ V) (hV1 : V ≠ ⊥) : Kc ≤ M := by
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hFel : IsElemAbelian 3 F :=
    elem_mono (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBtel) hF
  obtain ⟨r, hr⟩ := GL83.CompFam.exists_card_eq_pow hFel
  have hr2 : 2 ≤ r := by
    by_contra hcon
    have : 3 ^ r ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hr] at hF9
    omega
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
    Inputs245b.isPGroup_center_of_component hp (glaPPrimeCore_quotient_eq_bot hp) hKt
  have hodd : Odd (Nat.card (Subgroup.center ↥(barX 3 (Cg u) Kc))) := by
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    rw [hj]
    exact Odd.pow (by decide)
  have hc1 := InputsSeitz6.one_le_pRank_cen_bar hBel huB hu1 Kc
  have hgam := le_gammaPrime_of_seitz (k := 2) hKt.2.2.1 hBtel hodd hs
    ((Lemma1315b.centerQuotEquiv eK.symm).trans e) hF hFel hr (by omega) (by omega) ⟨V, hV1, hV, hVF⟩
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (hgam.trans (gammaPrimeIn_le_glbCore le_rfl _ _))

end Cases

section Gen


open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ in
theorem gen2318_of_griess (hGA : GriessMultipliersAllModels) : Gen2318 :=
  gen2318_of_inputs hGA
    (star2313Even_of_inputs LinearAutCubeProof.linearAutCube_holds
      Star2313UnitaryProof.star2313UnitaryInput_holds)
    gen2318TwoLocal_holds gen2318OutThreePrime_holds
    (gen2318RankFour_of_sylow' gen2318RankFourSylowUniq_holds) gen2318E64Core_holds
    (gen2318E68Outer_of_inputs hGA e68FieldFix_holds gen2318TwoLocal_holds
      (gen2318RankFour_of_sylow' gen2318RankFourSylowUniq_holds))

end Gen

@[expose] def NoPlaneTwoSub {S : Type*} [Group S] (A : Subgroup (MulAut S)) : Prop :=
  ∀ F : Subgroup (MulAut S), F ≤ A → 9 ≤ Nat.card F → ∀ V : Subgroup S, IsPGroup 2 ↥V →
    (∀ φ ∈ F, ∀ x ∈ V, φ x ∈ V) → V = ⊥

@[expose] def Rank3CuResExcThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          (∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧ i.1 ≠ .tits ∧ ¬ IsL2EightIndex i.1 ∧
              (IsSixIndex i.1 → ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range) ∧
              ((Subgroup.center (barOf 3 Kc) ≠ ⊥ ∧
                  CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 i.1) ∨
                IsD2SeitzException 3 i.1) ∧
              ¬ Gen2318Index i.1 ∧
              (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope i.1 →
                NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)))) →
          Kc ≤ M

section Reduce


theorem rank3CuResExcTwo_of_three (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcThree) :
    InputsSeitz6.Rank3CuResExcTwo := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  obtain ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest⟩ := htype
  by_cases hg : Gen2318Index i.1
  · exact le_M_of_gen2318 (gen2318_of_griess hGA) h h139b hU hu hu1 hKc hN i e hg
  by_cases hpl : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope i.1 ∧
      ¬ NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc))
  · obtain ⟨hs, hno⟩ := hpl
    unfold NoPlaneTwoSub at hno
    push Not at hno
    obtain ⟨F, hF, hF9, V, hV, hVF, hV1⟩ := hno
    exact le_M_of_plane h h139b hU hu hu1 hKc hN i e hs hF hF9 hV hVF hV1
  · exact hX h h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest, hg, fun hs => by
        by_contra hc
        exact hpl ⟨hs, hc⟩⟩

end Reduce

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310r

end
