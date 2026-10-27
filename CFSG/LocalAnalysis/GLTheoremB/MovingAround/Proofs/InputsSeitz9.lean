module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz8b
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerEx
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6FourOut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz9

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth (c3 u1 c3_pow_three)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section FourSL2

theorem exists_cartan_hyp_of_four_sl2 {F : Type} [Field F] {G : Type} [Group G] (h2 : (2 : F) = 0)
    (ψ : Fin 4 → SL(2, F) →* G) (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ∃ A₀ H₀ : Subgroup G, IsElemAbelian 3 A₀ ∧ Nat.card A₀ = 3 ^ 4 ∧ H₀ ≤ A₀ ∧
      Nat.card H₀ = 3 ^ 3 ∧ ∃ t : G, t ≠ 1 ∧ t * t = 1 ∧ ∀ h ∈ H₀, h * t = t * h := by
  classical
  have hx3 : ∀ i, ψ i c3 ^ 3 = 1 := fun i => by rw [← map_pow, c3_pow_three, map_one]
  have hcc : ∀ i j, i ≠ j → Commute (ψ i c3) (ψ j c3) := fun i j hij => hc i j hij c3 c3
  have hind := TwE6FourRankAux.indep_four hψ hc
  set Φ := TwE6FourRankAux.fourHom (ψ 0 c3) (ψ 1 c3) (ψ 2 c3) (ψ 3 c3) (hx3 0) (hx3 1) (hx3 2) (hx3 3)
    (hcc 0 1 (by decide)) (hcc 0 2 (by decide)) (hcc 0 3 (by decide)) (hcc 1 2 (by decide))
    (hcc 1 3 (by decide)) (hcc 2 3 (by decide)) with hΦ
  have hΦinj : Function.Injective Φ := TwE6FourRankAux.fourHom_injective _ _ _ _ _ _ _ _ _ _ _ _ _ _ hind
  let j : (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) × Multiplicative (ZMod 3) →*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ×
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :=
    (MonoidHom.fst _ _).prod ((MonoidHom.snd _ _).prod 1)
  have hjapp : ∀ x, j x = (x.1, (x.2, 1)) := fun x => rfl
  have hj : Function.Injective j := by
    intro x y hxy
    rw [hjapp, hjapp] at hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
    exact Prod.ext h1 (Prod.mk.inj h2).1
  have hΦjinj : Function.Injective (Φ.comp j) := by
    rw [MonoidHom.coe_comp]
    exact hΦinj.comp hj
  have hΦj : ∀ x, (Φ.comp j) x = ψ 0 c3 ^ (Multiplicative.toAdd x.1.1).val *
      ψ 1 c3 ^ (Multiplicative.toAdd x.1.2).val * ψ 2 c3 ^ (Multiplicative.toAdd x.2).val := by
    intro x
    rw [MonoidHom.comp_apply, hjapp, hΦ, TwE6FourRankAux.fourHom_apply]
    simp
  refine ⟨Φ.range, (Φ.comp j).range, ?_, ?_, ?_, ?_, ψ 3 u1, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 b.2
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hx
      have hs3 : s ^ 3 = 1 :=
        Prod.ext (Prod.ext (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pow_three_eq_one_of_multiplicative_zmod _)
          (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pow_three_eq_one_of_multiplicative_zmod _))
          (Prod.ext (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pow_three_eq_one_of_multiplicative_zmod _)
          (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pow_three_eq_one_of_multiplicative_zmod _))
      rw [← map_pow, hs3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
    simp only [Nat.card_prod, TwE6FourRankAux.card_multiplicative_zmod_three]
    norm_num
  · rintro _ ⟨x, rfl⟩
    exact ⟨j x, rfl⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦjinj).toEquiv]
    simp only [Nat.card_prod, TwE6FourRankAux.card_multiplicative_zmod_three]
    norm_num
  · intro h
    exact F4InnerExAux.u1_ne_one (hψ 3 (h.trans (map_one (ψ 3)).symm))
  · rw [← map_mul, ← sq, F4InnerExAux.u1_sq h2, map_one]
  · rintro _ ⟨x, rfl⟩
    rw [hΦj]
    exact ((((hc 0 3 (by decide) c3 u1).pow_left _).mul_left
      ((hc 1 3 (by decide) c3 u1).pow_left _)).mul_left ((hc 2 3 (by decide) c3 u1).pow_left _)).eq

end FourSL2

section F4Two

theorem nonempty_equiv_adjointF4_two {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq2 : q.p = 2) (hqe : q.exponent = 1)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :
    Nonempty (S ≃* ↥(adjointGroup Tag.F4 (ZMod 2))) := by
  have hK2 : Nat.card (ZMod 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe, Nat.card_zmod, pow_one]
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq2 (ZMod 2) hK2
  exact ⟨(eS.trans eB.symm).trans (Gen2318OutAux.adjointEquiv Tag.F4 (ZMod 2))⟩

theorem hyp_four_f4Two {S : Type} [Group S] [Finite S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq2 : q.p = 2) (hqe : q.exponent = 1)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :
    (∃ A : Subgroup S, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4) ∧
    ∀ D : Subgroup S, IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
      ∃ H : Subgroup S, H ≤ D ∧ Nat.card H = 3 ^ 3 ∧
        ∃ t : S, t ≠ 1 ∧ t * t = 1 ∧ ∀ h ∈ H, h * t = t * h := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_equiv_adjointF4_two hv hq2 hqe eS
  obtain ⟨ι, hinj, hc⟩ :=
    CFSG.RankThree.Chevalley.even_higher_ordinary_exceptional_four_commuting_faithful_SL2 (ZMod 2) Tag.F4
      (Or.inl rfl)
  obtain ⟨ψ, hψ, hψc⟩ := F4FourSL2Aux.transport e.symm ι hinj hc
  obtain ⟨A₀, H₀, hA₀el, hA₀c, hH₀A₀, hH₀c, t₀, ht₀1, ht₀2, ht₀H⟩ :=
    exists_cartan_hyp_of_four_sl2 (F := ZMod 2) (by decide) ψ hψ hψc
  refine ⟨⟨A₀, hA₀el, hA₀c⟩, fun D hD hDc => ?_⟩
  have hUS : I102UniqAux.ThreeUniq4 S :=
    I102UniqAux.threeUniq4_of_injective e.toMonoidHom e.injective
      (I102UniqAux.threeUniq4_adjointF4_two (K := ZMod 2) (Nat.card_zmod 2))
  obtain ⟨g, hg⟩ := CartanConjAux.conj_eq_of_sylow_unique (p := 3) (n := 4) (N := (⊤ : Subgroup S))
    (fun P E' F' h1 h2 h3 h4 h5 h6 _ _ => hUS P P.isPGroup' E' F' h1 h2 h3 h4 h5 h6)
    hA₀el hD hA₀c hDc le_top le_top
  refine ⟨H₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, g * t₀ * g⁻¹, ?_, ?_, ?_⟩
  · rw [hg]
    exact Subgroup.map_mono hH₀A₀
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hH₀c]
  · intro h
    apply ht₀1
    calc t₀ = g⁻¹ * (g * t₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc g * t₀ * g⁻¹ * (g * t₀ * g⁻¹) = g * (t₀ * t₀) * g⁻¹ := by group
      _ = 1 := by rw [ht₀2]; group
  · rintro _ ⟨h, hh, rfl⟩
    have hht := ht₀H h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * t₀ * g⁻¹) = g * (h * t₀) * g⁻¹ := by group
      _ = g * (t₀ * h) * g⁻¹ := by rw [hht]
      _ = g * t₀ * g⁻¹ * (g * h * g⁻¹) := by group

theorem hyp_four_f4Two_sub {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq2 : q.p = 2) (hqe : q.exponent = 1)
    (eL : ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) {D : Subgroup G} (hDL : D ≤ L)
    (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 4) :
    ∃ H : Subgroup G, H ≤ D ∧ Nat.card H = 3 ^ 3 ∧
      ∃ t ∈ L, t ≠ 1 ∧ t * t = 1 ∧ ∀ h ∈ H, h * t = t * h := by
  have hD' : IsElemAbelian 3 (D.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hD L
  have hD'c : Nat.card (D.subgroupOf L) = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv, hDc]
  obtain ⟨H', hH'D, hH'c, t, ht1, ht2, htH⟩ := (hyp_four_f4Two hv hq2 hqe eL).2 _ hD' hD'c
  refine ⟨H'.map L.subtype, ?_, ?_, t, t.2, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hH'D hh)
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hH'c]
  · intro h
    exact ht1 (Subtype.ext h)
  · exact congrArg Subtype.val ht2
  · rintro _ ⟨h, hh, rfl⟩
    exact congrArg Subtype.val (htH h hh)

theorem f4Two_inner_of_cube_one
    (β : MulAut ↥(adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (ZMod 2))) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : ↥(adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (ZMod 2)) →*
      MulAut ↥(adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (ZMod 2))).range := by
  haveI : CharP (ZMod 2) CFSG.LieType.Ree.ReeTag.F4.prime := (inferInstance : CharP (ZMod 2) 2)
  have hKcard : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨-, hB, ⟨Θ, hΘ, -, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := 1) le_rfl (ZMod 2) hKcard
  obtain ⟨⟨g, k⟩, hgk⟩ := (hB β).exists
  have hΘβ := hΘ β g (k : ℕ) hgk
  have h3 : Θ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  rw [hΘβ, ← ofAdd_nsmul, ofAdd_eq_one] at h3
  have key : ∀ x : ZMod (2 * 1), (3 : ℕ) • x = 0 → x = 0 := by decide
  have hk0 : ((k : ℕ) : ZMod (2 * 1)) = 0 := key _ h3
  have hΘ1 : Θ β = 1 := by rw [hΘβ, hk0, ofAdd_zero]
  have hmem : β ∈ Θ.ker := MonoidHom.mem_ker.2 hΘ1
  rw [hker] at hmem
  exact hmem

end F4Two

section InnerCases

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_f4Two (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : Bal209F4Aux.IsF4TwoIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  have hconj := Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  obtain ⟨d0, hv⟩ := d
  cases d0 with
  | F4 q =>
    obtain ⟨hq2, hqe⟩ : q.p = 2 ∧ q.exponent = 1 := hd
    have hs : Seitz2313Cover.EvenScope (.F4 q) := hq2
    obtain ⟨eC⟩ := nonempty_equiv_adjointF4_two hv hq2 hqe eK
    have hinn : ∀ E : Subgroup (MulAut ↥K), IsElemAbelian 3 E →
        E ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := fun E hE =>
      Gen2318OutAux.transport_mem_range (C := ↥(adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (ZMod 2))) eC
        (fun β hβ => f4Two_inner_of_cube_one β hβ) E (fun x hx => hE.2 x hx)
    have hAel := InputsSeitz3.isElemAbelian_autIm hB K
    have hAc : Nat.card (InputsSeitz3.autIm B K) = 3 ^ CFSG.Open.pRank 3 B :=
      (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
    set D : Subgroup ↥K := (InputsSeitz3.autIm B K).comap (MulAut.conj : ↥K →* MulAut ↥K) with hDdef
    have hDmap : D.map MulAut.conj = InputsSeitz3.autIm B K := Subgroup.map_comap_eq_self (hinn _ hAel)
    have hDc : Nat.card D = 3 ^ CFSG.Open.pRank 3 B := by
      rw [← hAc, ← hDmap, Subgroup.card_map_of_injective hconj]
    have hDel : IsElemAbelian 3 D := InputsSeitz7.isElemAbelian_comap_of_injective hconj hAel
    obtain ⟨D₄, hD₄c, -, hD₄D⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 4)
      (H := ⊥) (L := D) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hDc]; exact Nat.pow_dvd_pow 3 hB4) bot_le
    have hD₄el : IsElemAbelian 3 D₄ := GL83.CompFam.elem_mono hDel hD₄D
    obtain ⟨H, hHD, hHc, t, ht1, ht2, htH⟩ := (hyp_four_f4Two hv hq2 hqe eK).2 D₄ hD₄el hD₄c
    refine InputsSeitz7.le_glbCore_of_e27_inv hB hs eK le_rfl hC (F := H.map MulAut.conj) ?_ ?_ ht1 ht2 ?_
    · rw [← hDmap]
      exact Subgroup.map_mono (hHD.trans hD₄D)
    · rw [Subgroup.card_map_of_injective hconj, hHc]
    · rintro _ ⟨x, hx, rfl⟩
      show MulAut.conj x t = t
      rw [MulAut.conj_apply, htH x hx, mul_inv_cancel_right]
  | _ => exact absurd hd (by simp [Bal209F4Aux.IsF4TwoIndex])

theorem le_glbCore_of_twE6Four (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X} (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsTwistedE6FourIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hAel : IsElemAbelian 3 (CFSG.HardMathSupport.Dickson.I271.autImage B K) := isElemAbelian_autImage hB
  have hstab := InputsSeitz7.card_stab_eq (B := B) (K := K) hperf
  rw [hC, Subgroup.card_bot, mul_one, inf_eq_left.2 hBN, GL83.PiGen.card_eq_pow_pRank hB] at hstab
  have hinn := twE6FourOut_holds _ d hd ⟨e⟩ _ hAel
  obtain ⟨E₀, hE₀c, -, hE₀A⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 4) (H := ⊥)
    (L := CFSG.HardMathSupport.Dickson.I271.autImage B K) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [← hstab]; exact Nat.pow_dvd_pow 3 hB4) bot_le
  have hE₀el : IsElemAbelian 3 E₀ := CFSG.HardMathSupport.Solomon.Coordinator.i271_isElemAbelian_of_le hAel hE₀A
  obtain ⟨-, hrank⟩ := twE6FourRank_of_sylow twE6FourSylowRankUnique_holds _ d hd ⟨e⟩
  obtain ⟨U, hU0, hU2, hUinv⟩ := hrank E₀ hE₀el hE₀c (hE₀A.trans hinn)
  have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
    rw [hC]
    exact pRank_bot_eq_zero' hp
  exact (InputsSeitz7.le_gammaPrime_of_seitz_rank seitz2313Even_holds (k := 2) hperf hB
    (InputsSeitz7.odd_card_center_of_core hcore hK) (isTwistedE6FourIndex_evenScope hd) e hE₀A hE₀el hE₀c
    (by norm_num) (by rw [hc0]; omega) ⟨U, hU0, hU2, hUinv⟩).trans (InputsSeitz7.gammaPrimeIn_le_glbCore le_rfl B K)

end InnerCases

section F4Eight

theorem exists_not_innerAt_of_not_le_f4Eight {X : Type} [Group X] {B K : Subgroup X}
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    ∃ b ∈ B, b ∈ Subgroup.normalizer (K : Set X) ∧ ¬ Bal209F4Aux.InnerAt K b := by
  by_contra hall
  push Not at hall
  apply hout
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨k, hk, hkc⟩ := hall n (Subgroup.mem_subgroupOf.1 hn) n.2
  refine ⟨⟨k, hk⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hc := Subgroup.mem_centralizer_iff.1 hkc x x.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (k : X) * x * k⁻¹ = k * (x * (k⁻¹ * n)) * (n : X)⁻¹ := by group
    _ = k * ((k⁻¹ * n) * x) * (n : X)⁻¹ := by rw [hc]
    _ = n * x * (n : X)⁻¹ := by group

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_f4Eight_outer (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsF4EightIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  have hconj := Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  have hs : Seitz2313Cover.EvenScope d.1 := by
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | F4 q => exact hd.1
    | _ => exact absurd hd (by simp [IsF4EightIndex])
  obtain ⟨b, hbB, hbN, hbout⟩ := exists_not_innerAt_of_not_le_f4Eight hout
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  obtain ⟨hLs, hLq, -, ⟨d', hd', ⟨eL'⟩⟩⟩ := f4Fixed_holds X K b hK ⟨d, hd, ⟨e⟩⟩ hbN hb3 hbout
  set L : Subgroup X := K ⊓ Subgroup.centralizer ({b} : Set X) with hLdef
  have hZL : Subgroup.center ↥L = ⊥ := by
    haveI := hLs
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => ?_
    have h1 := (commutator_eq_bot_iff ↥L).2 hc
    rw [hLq.1] at h1
    obtain ⟨a, c, hac⟩ := exists_pair_ne ↥L
    have ha : a ∈ (⊥ : Subgroup ↥L) := h1 ▸ Subgroup.mem_top a
    have hc' : c ∈ (⊥ : Subgroup ↥L) := h1 ▸ Subgroup.mem_top c
    exact hac ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hc').symm)
  obtain ⟨d0', hv'⟩ := d'
  obtain ⟨q', rfl, hq'2, hq'e⟩ : ∃ q' : TauCeti.PrimePower, d0' = .F4 q' ∧ q'.p = 2 ∧ q'.exponent = 1 := by
    cases d0' with
    | F4 q' => exact ⟨q', rfl, hd'.1, hd'.2⟩
    | _ => exact absurd hd' (by simp [Bal209F4Aux.IsF4TwoIndex])
  let eL : ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q', hv'⟩).Group :=
    (InputsSeitz3.equivCenterQuot hZL).trans eL'
  have hbK : b ∉ K := fun h => hbout ⟨b, h, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  have hb1 : b ≠ 1 := fun h => hbK (h ▸ K.one_mem)
  obtain ⟨A₀, hA₀el, hA₀c⟩ := (hyp_four_f4Two hv' hq'2 hq'e eL).1
  have h5 : 5 ≤ CFSG.Open.pRank 3 B := by
    have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
    have hEel : IsElemAbelian 3 (Subgroup.zpowers b) := F4InnerExAux.isElemAbelian_zpowers hb3
    have hEc : Nat.card (Subgroup.zpowers b) = 3 ^ 1 := by rw [Nat.card_zpowers, hbo, pow_one]
    have hFel : IsElemAbelian 3 (A₀.map L.subtype) := CFSG.SectionRank.isElemAbelian_map hA₀el _
    have hFc : Nat.card (A₀.map L.subtype) = 3 ^ 4 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hA₀c]
    have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ A₀.map L.subtype, x * y = y * x := by
      rintro x hx _ ⟨y, -, rfl⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hyb : Commute b (y : X) := Subgroup.mem_centralizer_iff.1 y.2.2 b (Set.mem_singleton b)
      exact (hyb.zpow_left i).eq
    have hdisj : Subgroup.zpowers b ⊓ A₀.map L.subtype = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ A₀.map L.subtype) ∣ 3 := by
        rw [← pow_one 3, ← hEc]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers b ⊓ A₀.map L.subtype = Subgroup.zpowers b :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hEc, h3, pow_one])
        have hbE : b ∈ Subgroup.zpowers b ⊓ A₀.map L.subtype := by
          rw [heq]
          exact Subgroup.mem_zpowers b
        obtain ⟨y, -, hy⟩ := hbE.2
        apply hbK
        rw [← hy]
        exact y.2.1
    have h := InputsSeitz.add_le_pRank_of_commute hp hEel hFel hcomm hdisj hEc hFc
    rw [hrk]
    omega
  obtain ⟨-, -, -, -, ⟨Θ, hΘ⟩, -⟩ := F4InnerExAux.chevalley_data hK.2.2 ⟨d, hd, ⟨e⟩⟩
  haveI : Finite (MulAut ↥K) := CartanConjAux.finite_mulAut ↥K
  haveI := CartanConjAux.inn_normal ↥K
  have hidx : (MulAut.conj : ↥K →* MulAut ↥K).range.index ∣ 2 * 3 := by
    have h1 : (MulAut.conj : ↥K →* MulAut ↥K).range.index ∣ Θ.ker.index := Subgroup.index_dvd_of_le hΘ
    have h2 : Θ.ker.index ∣ 2 * 3 := by
      rw [Subgroup.index_ker]
      have h := Subgroup.card_subgroup_dvd_card Θ.range
      rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    exact h1.trans h2
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card A = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  have hle3 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range) := by
    refine InputsSeitz7.card_le_three_mul_inf (fun h9 => ?_) (fun h0 => ?_) hAel.isPGroup
    · have := Nat.le_of_dvd (by norm_num) (h9.trans hidx)
      omega
    · rw [h0] at hidx
      norm_num at hidx
  set A₁ := A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range with hA₁def
  have hA₁el : IsElemAbelian 3 A₁ := GL83.CompFam.elem_mono hAel inf_le_left
  obtain ⟨r, hr⟩ := GL83.CompFam.exists_card_eq_pow hA₁el
  have hr4 : 4 ≤ r := by
    rw [hAc, hr, ← pow_succ'] at hle3
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle3
    omega
  set D : Subgroup ↥K := A₁.comap (MulAut.conj : ↥K →* MulAut ↥K) with hDdef
  have hDmap : D.map MulAut.conj = A₁ := Subgroup.map_comap_eq_self inf_le_right
  have hDc : Nat.card D = 3 ^ r := by
    rw [← hr, ← hDmap, Subgroup.card_map_of_injective hconj]
  have hDel : IsElemAbelian 3 D := InputsSeitz7.isElemAbelian_comap_of_injective hconj hA₁el
  have hβA : K.normalizerMonoidHom ⟨b, hbN⟩ ∈ A := ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hbB, rfl⟩
  have hDL : D.map K.subtype ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k.2, ?_⟩
    have hkA : MulAut.conj k ∈ A := (hk : MulAut.conj k ∈ A₁).1
    set β := K.normalizerMonoidHom ⟨b, hbN⟩ with hβdef
    have hcomm : β * MulAut.conj k = MulAut.conj k * β :=
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨_, hβA⟩ ⟨_, hkA⟩)
    have h1 : MulAut.conj (β k) = MulAut.conj k := by
      have e1 : MulAut.conj (β k) = β * MulAut.conj k * β⁻¹ := by
        ext x
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [e1, hcomm, mul_inv_cancel_right]
    have h2 : β k = k := hconj h1
    have h3 : b * (k : X) * b⁻¹ = k := by
      have h4 := congrArg Subtype.val h2
      rwa [hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
    show (k : X) ∈ Subgroup.centralizer ({b} : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * (k : X) = (y * k * y⁻¹) * y := by group
      _ = k * y := by rw [h3]
  obtain ⟨D₄, hD₄c, -, hD₄D⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 4) (H := ⊥) (L := D)
    (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hDc]; exact Nat.pow_dvd_pow 3 hr4) bot_le
  have hD₄el : IsElemAbelian 3 D₄ := GL83.CompFam.elem_mono hDel hD₄D
  obtain ⟨H, hHD, hHc, t, htL, ht1, ht2, htH⟩ := hyp_four_f4Two_sub hv' hq'2 hq'e eL
    ((Subgroup.map_mono hD₄D).trans hDL) (CFSG.SectionRank.isElemAbelian_map hD₄el _)
    (by rw [Subgroup.card_map_of_injective K.subtype_injective, hD₄c])
  have hHK : H ≤ K.subtype.range := by
    rw [Subgroup.range_subtype]
    exact hHD.trans (Subgroup.map_subtype_le D₄)
  set HK : Subgroup ↥K := H.comap K.subtype with hHKdef
  have hHKmap : HK.map K.subtype = H := Subgroup.map_comap_eq_self hHK
  have hHKc : Nat.card HK = 3 ^ 3 := by
    rw [← hHc, ← hHKmap, Subgroup.card_map_of_injective K.subtype_injective]
  have hHKD : HK ≤ D := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hHD hx
    have hyx' : y = x := Subtype.ext hyx
    exact hD₄D (hyx' ▸ hy)
  let tK : ↥K := ⟨t, htL.1⟩
  refine InputsSeitz7.le_glbCore_of_e27_inv hB hs eK le_rfl hC (F := HK.map MulAut.conj) ?_ ?_ (t := tK)
    ?_ ?_ ?_
  · exact (Subgroup.map_mono hHKD).trans (hDmap.le.trans inf_le_left)
  · rw [Subgroup.card_map_of_injective hconj, hHKc]
  · intro h
    exact ht1 (congrArg Subtype.val h)
  · exact Subtype.ext ht2
  · rintro _ ⟨x, hx, rfl⟩
    show MulAut.conj x tK = tK
    have hxt : x * tK = tK * x := Subtype.ext (htH _ hx)
    rw [MulAut.conj_apply, hxt, mul_inv_cancel_right]

end F4Eight

section Residual

@[expose] def Input23_19ExcThreeRest3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 → ¬ Gen2318Index d.1 →
        ¬ InputsSeitz7.IsSpTwoIndex d → ¬ InputsSeitz7.IsUnitaryTwoIndex d →
        ¬ InputsSeitz7.IsSpEightIndex d → ¬ InputsSeitz7.IsUnitaryEightIndex d →
        ¬ InputsSeitz7.IsUThreeEightIndex d →
        ¬ InputsSeitz8.IsOrthTwoIndex d → ¬ InputsSeitz8.IsTriD4TwoIndex d →
        ¬ InputsSeitz8.IsG2EightIndex d → ¬ InputsSeitz7.IsUSixIndex d →
        ¬ InputsSeitz8.IsOmegaEightTwoIndex d → ¬ IsD4FourIndex d.1 →
        ¬ Bal209F4Aux.IsF4TwoIndex d.1 → ¬ IsTwistedE6FourIndex d.1 → ¬ IsF4EightIndex d.1 →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ((Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 ∧
            B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨
          B ⊓ Subgroup.centralizer (K : Set X) = ⊥) →
        K ≤ GLBCore 3 2 B

theorem not_coverIndex_rest3 {d : TauCeti.ValidLieTypeIndex}
    (hd : Bal209F4Aux.IsF4TwoIndex d.1 ∨ IsTwistedE6FourIndex d.1 ∨ IsF4EightIndex d.1) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 := by
  obtain ⟨d0, hv⟩ := d
  cases d0 with
  | F4 q => exact id
  | twistedE6 q =>
    rintro ⟨-, h3⟩
    rcases hd with hd | ⟨hq2, hqe⟩ | hd
    · exact hd
    · rw [TauCeti.PrimePower.card_def, hq2, hqe] at h3
      norm_num at h3
    · exact hd
  | _ => simp_all [Bal209F4Aux.IsF4TwoIndex, IsTwistedE6FourIndex, IsF4EightIndex]

theorem input23_19ExcThreeRest2_of_rest3 (h : Input23_19ExcThreeRest3) :
    InputsSeitz8.Input23_19ExcThreeRest2 := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hsix hrest
  obtain ⟨e⟩ := hd
  have hC : ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 →
      B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
    fun hnc => hrest.resolve_left fun hc => hnc hc.2.1
  by_cases hF2 : Bal209F4Aux.IsF4TwoIndex d.1
  · exact le_glbCore_of_f4Two hcore hB hB4 hrk hK d e hF2 hBN (hC (not_coverIndex_rest3 (Or.inl hF2)))
  by_cases hE4 : IsTwistedE6FourIndex d.1
  · exact le_glbCore_of_twE6Four hcore hB hB4 hK d e hE4 hBN
      (hC (not_coverIndex_rest3 (Or.inr (Or.inl hE4))))
  by_cases hF8 : IsF4EightIndex d.1
  · exact le_glbCore_of_f4Eight_outer hcore hB hB4 hrk hK d e hF8 hBN
      (hC (not_coverIndex_rest3 (Or.inr (Or.inr hF8)))) (hsix (Or.inl hF8))
  exact h X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d ⟨e⟩ hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hsix hrest

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz9

end
