module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz10b
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6IsoPlaneLarge

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz12

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

set_option linter.unusedSectionVars true

section Statement

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.LieType.Chevalley (twistedE6RootGroup twistedE6Inn twistedE6Diag)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10 (IsOrthEightIndex)


@[expose] def Input23_19CoverCase : Prop :=
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
        ¬ OuterFourAux.IsD4EightIndex d.1 →
        (IsOrthEightIndex d → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (OuterFourInAux.IsTwE6EightIndex d.1 → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 →
            (∀ c, σ c = c ^ (2 ^ 3)) → ∀ θ : ↥K ≃* twistedE6RootGroup L σ,
              ¬ (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
                twistedE6Inn L σ ⊔ twistedE6Diag L σ) →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        Subgroup.center ↥K ≠ ⊥ → CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 →
          B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        K ≤ GLBCore 3 2 B

end Statement

section Index

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem twistedE6_of_coverCase {d : TauCeti.ValidLieTypeIndex} (hexc : ExcIndex 3 d.1)
    (htits : d.1 ≠ .tits) (hl28 : ¬ IsL2EightIndex d.1) (hg : ¬ Gen2318Index d.1)
    (hU38 : ¬ InputsSeitz7.IsUThreeEightIndex d) (hU6 : ¬ InputsSeitz7.IsUSixIndex d)
    (hci : CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3) ∧
      d.1 = .twistedE6 q := by
  have hB : ∀ (r : ℕ) (q : TauCeti.PrimePower), d.1 ≠ .B r q := by
    intro r q h
    rw [h] at hci
    exact hci
  have hU : ∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 3 q := by
    intro q h
    rw [h] at hci
    exact absurd hci.1 (by norm_num)
  obtain ⟨-, h⟩ := Claims1310r.residual_index hexc htits hl28 (Or.inl hci) hg hB hU
  rcases h with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · exact absurd ⟨q, hq.1, Or.inl hq.2, hd⟩ hU6
  · exact absurd ⟨q, hq.1, Or.inr hq.2, hd⟩ hU6
  · exact absurd ⟨q, hq.1, hq.2, hd⟩ hU38
  · exact ⟨q, hq.1, Or.inl hq.2, hd⟩
  · exact ⟨q, hq.1, Or.inr hq.2, hd⟩

end Index

section Centre

open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

theorem tableOrder_twistedE6_dvd (p f : ℕ) :
    CFSG.RankThree.PartTwo.Sec4.Census.tableOrder .twistedE6 0 p f ∣ 12 := by
  have h1 : (genericOrders .twistedE6 0 p f).1 ∣ 3 := Nat.gcd_dvd_left _ _
  have h2 : (genericOrders .twistedE6 0 p f).2 = 1 := rfl
  have h3 : (exceptionalOrders .twistedE6 0 p f).1 ∣ 2 ∧
      (exceptionalOrders .twistedE6 0 p f).2 ∣ 2 := by
    by_cases hpf : p = 2 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := hpf
      exact ⟨by decide, by decide⟩
    · have : exceptionalOrders .twistedE6 0 p f = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      rw [this]
      exact ⟨one_dvd _, one_dvd _⟩
  rw [CFSG.RankThree.PartTwo.Sec4.Census.tableOrder, h2, mul_one]
  exact (Nat.mul_dvd_mul h1 (Nat.mul_dvd_mul h3.1 h3.2)).trans (by norm_num)

theorem card_center_eq_three_of_twistedE6
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) :
    Nat.card (Subgroup.center K) = 3 := by
  have hm := CFSG.RankThree.PartTwo.Sec4.Census.lieModel_of_namesTag (t := .twistedE6)
    ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hdvd : Nat.card (Subgroup.center K) ∣ 12 :=
    (CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA
      (CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hK) e hm).trans
      (tableOrder_twistedE6_dvd _ _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hZp
  have ha1 : a ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ Nat.card (Subgroup.center K) := by
      rw [ha]
      exact pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hZ (Subgroup.eq_bot_of_card_eq _ (by rw [ha, pow_zero]))
  rw [ha, show a = 1 by omega, pow_one]

end Centre

section Rank

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration


theorem six_le_pRank_of_twistedE6Cover {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid} (hq : q.card % 3 = 2)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.twistedE6 q, hv⟩)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) : 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  classical
  obtain ⟨F, _, σ, hF, hσ, ⟨e'⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hF]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul])
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact hσ x
  have h3 : 3 ∣ q.p ^ q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    omega
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect TwistTag.E6 q.prime_p
    q.exponent_pos F hF σ.toRingHom hσ''
  let e2 : ↥(twistedE6RootGroup F σ) ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    (MulEquiv.subgroupCongr hΓ).symm
  set π : K →* ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    e2.toMonoidHom.comp (e'.toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))) with hπ
  have hπs : Function.Surjective π :=
    e2.surjective.comp (e'.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center K := by
    intro x
    change e2 (e' (e (QuotientGroup.mk x))) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
  haveI : Finite ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    Subtype.finite
  exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.six_le_pRank_of_cover_twE6 σ.toRingHom
    q.exponent_pos h3 hF hσ'' π hπs hker hZ

end Rank

section Engine

open CFSG.LieType.SeitzGeneration (Cat PlaneGen)

theorem le_glbCore_of_largePlane {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B K : Subgroup X} {z : X} (hperf : commutator ↥K = ⊤)
    (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hzB : z ∈ B)
    (hzK : z ∈ K) (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z)
    (hΩ : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z)
    {d : TauCeti.ValidLieTypeIndex} (e : ↥K ⧸ Subgroup.center ↥K ≃* Cat d)
    (hB : p ^ 5 ≤ Nat.card B)
    (hplane : ∀ Ē : Subgroup (MulAut (Cat d)), IsElemAbelian p Ē → p ^ 4 ≤ Nat.card Ē →
      ∃ E : Subgroup (MulAut (Cat d)), E ≤ Ē ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        PlaneGen E) :
    K ≤ GLBCore p 2 B := by
  have hperf' : Group.IsPerfect ↥K := ⟨hperf⟩
  obtain ⟨E4, hE4el, hE4card, hE4B⟩ :=
    GL83.I243.exists_elemAbelian_image (n := 4) hp hBN hBel hzB hzp hCB hB
  set ρ : MulAut ↥K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K) with hρdef
  have hρ : Function.Injective ρ := (MulAut.congr e).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _)
  obtain ⟨E', hE'le, -, hE'card, hE'gen⟩ := hplane (E4.map ρ) (hE4el.map ρ)
    (by rw [Subgroup.card_map_of_injective hρ, hE4card])
  set E : Subgroup (MulAut ↥K) := (E'.comap ρ) ⊓ E4 with hE
  have hmapE : E.map ρ = E' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hx4, rfl⟩ := hE'le hy
      exact ⟨x, ⟨hy, hx4⟩, rfl⟩
  have hEel : IsElemAbelian p E := hE4el.mono inf_le_right
  have hEcard : Nat.card E = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hρ (K := E), hmapE, hE'card]
  have hcl := GL83.I243.closure_fix_lift (p := p) hperf' e (fun E'' => PlaneGen E'')
    (fun E'' _ _ hQ => hQ) E hEel hEcard (by rw [hmapE]; exact hE'gen)
  refine GL83.I243.le_core_of_closure hp hp2 hperf hBel hBN hzB hzK hzc hzp hΩ ?_
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono ?_
  rintro k ⟨ε, hε, hε1, hk⟩
  obtain ⟨f, hfB, hf⟩ := hE4B ε (Subgroup.mem_inf.mp hε).2
  refine ⟨f, hfB, ?_, ?_⟩
  · intro hfz
    apply hε1
    have hfc : f ∈ Subgroup.centralizer (K : Set X) := (Subgroup.zpowers_le.mpr hzc) hfz
    ext y
    rw [hf y, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hfc (y : X) y.2
    rw [← this, mul_inv_cancel_right]
  · have hc := Subgroup.mem_center_iff.mp hk
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h1 := congrArg (fun a : ↥K => (a : X)) (hc ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf] at h1
    exact h1

end Engine

section Main

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.LieType.SeitzGeneration (Cat)


theorem input23_19CoverCase_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Input23_19CoverCase := by
  intro X _ _ _ hcore B hB hB4 hrk K hK _ hsmall hBN d hd hexc htits hl28 hg _ _ _ _ hU38 _ _ _
    hU6 _ _ _ _ _ _ _ _ _ hZ hci _
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨q, hq2, hqf, hdq⟩ := twistedE6_of_coverCase hexc htits hl28 hg hU38 hU6 hci
  obtain ⟨e⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdd : dd = .twistedE6 q := hdq
  subst hdd
  have hq : q.card % 3 = 2 := by
    rw [TauCeti.PrimePower.card_def, hq2]
    rcases hqf with h | h <;> rw [h] <;> norm_num
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hZp : IsPGroup 3 (Subgroup.center ↥K) :=
    Inputs245b.isPGroup_center_of_component hp hcore hK
  have hZ3 : Nat.card (Subgroup.center ↥K) = 3 :=
    card_center_eq_three_of_twistedE6 hGA hK.2.2 e hZp hZ
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B :=
    GL83.PiGen.card_eq_pow_pRank hB
  have hSC : ∀ y ∈ Subgroup.centralizer (B : Set X), y ^ 3 = 1 → y ∈ B := by
    intro y hy hy3
    have hyel : IsElemAbelian 3 (Subgroup.zpowers y) := isElemAbelian_zpowers hy3
    have hBy : B ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup X) : Set X) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hy)
    have hA := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hB hyel hBy
    have hrank : CFSG.Open.pRank 3 (B ⊔ Subgroup.zpowers y) ≤ CFSG.Open.pRank 3 B :=
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp le_top).trans hrk.symm.le
    have heq := CFSG.PreuniquenessRankFour.Helpers.elementary_subgroup_eq_of_rank_bound 3 hp hA
      le_sup_left _ hBc hrank
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  obtain ⟨z, hzB, hzK, hzc, hzo⟩ := GL83.I243.exists_mem_center_of_normalizes hp hB hSC hBN
    (by rw [hZ3])
  have hC3 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) ≤ 3 := by
    have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) := hB.mono inf_le_left
    have hCc := GL83.PiGen.card_eq_pow_pRank hCel
    rw [hCc, inf_eq_left.2 hBN, hBc, ← pow_add] at hsmall
    have hlt := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hsmall
    rw [hCc]
    calc 3 ^ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) ≤ 3 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := pow_one 3
  have hCz : B ⊓ Subgroup.centralizer (K : Set X) = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzB, hzc⟩))
      (by rw [Nat.card_zpowers, hzo]; exact hC3)).symm
  have hCB' : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z := by
    intro b hb hbc
    rw [← hCz]
    exact Subgroup.mem_inf.mpr ⟨hb, hbc⟩
  have hzZ : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hzc (y : X) y.2)
  have hZz : Subgroup.zpowers (⟨z, hzK⟩ : ↥K) = Subgroup.center ↥K :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
      (by rw [hZ3, Nat.card_zpowers, Subgroup.orderOf_mk, hzo])
  have hΩ : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ 3 = 1 →
      c ∈ Subgroup.zpowers z := by
    intro c hcK hcc _
    have hcZ : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hcc (y : X) y.2)
    rw [← hZz] at hcZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcZ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have h6 : 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    six_le_pRank_of_twistedE6Cover hq e (by rw [hZ3])
  have hKX : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥K)
    exact CFSG.SectionRank.le_pRank hp.one_lt le_top (hE.map K.subtype)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective, hEc])
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact le_glbCore_of_largePlane hp (by norm_num) hperf hB hBN hzB hzK hzc hzo hCB' hΩ e hB5
    (fun Ē hĒ hc => CFSG.LieType.SeitzGeneration.ExcHighThree.exists_planeGen_of_large_twE6 hv hq
      hĒ hc)

theorem input23_19CoverCase_holds :
    Input23_19CoverCase :=
  input23_19CoverCase_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz12
