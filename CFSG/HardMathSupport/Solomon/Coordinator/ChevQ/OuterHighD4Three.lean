module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Sylow
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Closing
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Top
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Maximal
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.LargeExtraspecial.S3cMain
public import CFSG.LargeExtraspecial.S3cOddCore
public import CFSG.LargeExtraspecial.S3cSix
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightF4
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S4Three
public import CFSG.LargeExtraspecial.S4TwoA
public import CFSG.LargeExtraspecial.S4TwoD
public import CFSG.LargeExtraspecial.S4TwoG
public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCubeUnitary
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import Certificates.Certificate10050
public import Certificates.Certificate8117

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

open CFSG.LieType.Seitz CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section GraphPair

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

theorem conj_injective_D4 :
    Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)) :=
  OuterFourSeitz.conj_injective_adjointD4

theorem apply_eq_of_comm_conj {α : MulAut ↥(adjointGroup Tag.D4 K)}
    {x : ↥(adjointGroup Tag.D4 K)} (h : α * MulAut.conj x = MulAut.conj x * α) : α x = x := by
  apply conj_injective_D4
  have h2 : α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]
  rw [← h2, h, mul_inv_cancel_right]

theorem isTwoPow_of_card {q : TauCeti.PrimePower} {k : ℕ} (hk : 1 ≤ k) (h : q.card = 2 ^ k) :
    IsTwoPow q k := by
  have h8 : q.p ^ q.exponent = 2 ^ k := by rw [← TauCeti.PrimePower.card_def, h]
  have hdvd : q.p ∣ 2 ^ k := h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hp2 : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  rw [hp2] at h8
  exact ⟨hp2, Nat.pow_right_injective (le_refl 2) h8⟩

@[expose] def D4ThreeOuterCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → Nat.card K ≠ 2 → Nat.card K ≠ 4 →
    Nat.card K ≠ 8 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
      seitzHyperGamma 3 E = ⊤

theorem seitzGoodOuterHighD4Three_of_model (h : D4ThreeOuterCubes) :
    OuterHigh2.SeitzGoodOuterHighD4Three := by
  intro p hp hp2 S _ _ _ _ d hP he hpd _ hx _ _ E hE hc hout
  obtain ⟨hp3, q, hdq⟩ := hP
  subst hp3
  obtain ⟨d, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨ψ⟩ := he
  obtain ⟨K, _, _, hK, hKchar, ⟨φ⟩⟩ := exists_catEquiv_D4 q hv
  let θ : S ≃* ↥(adjointGroup Tag.D4 K) := ψ.trans φ
  have hq3 : q.p ≠ 3 := fun h3 => hpd (by simp [h3])
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact hq3
  have h2 : Nat.card K ≠ 2 := by
    intro h2
    have hq := isTwoPow_of_card le_rfl (by rw [← hK, h2]; norm_num : q.card = 2 ^ 1)
    exact hx (Or.inl ⟨rfl, Or.inr ⟨hq, rfl⟩⟩)
  have h4 : Nat.card K ≠ 4 := by
    intro h4
    have hq := isTwoPow_of_card (by norm_num) (by rw [← hK, h4]; norm_num : q.card = 2 ^ 2)
    exact hx (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hq⟩)))))⟩)
  have h8 : Nat.card K ≠ 8 := by
    intro h8
    have hq := isTwoPow_of_card (by norm_num) (by rw [← hK, h8]; norm_num : q.card = 2 ^ 3)
    exact hx (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hq⟩)))))⟩)
  obtain ⟨hE', hc'⟩ := OuterFourSeitz.map_congr_data θ hE hc
  have hout' : ¬ E.map (MulAut.congr θ).toMonoidHom ≤
      (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range :=
    fun h' => hout (OuterFourSeitz.le_range_conj_of_map_congr θ h')
  exact OuterFourSeitz.seitzHyperGamma_eq_top_of_congr θ (h K hK3 h2 h4 h8 _ hE' hc' hout')

@[expose] def D4ThreeFieldCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → Nat.card K ≠ 8 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      (∃ α ∈ E, D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1) →
      seitzHyperGamma 3 E = ⊤

@[expose] def D4ThreeGraphFieldCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      (∀ α ∈ E, ¬ D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1) →
      (∃ β ∈ E, D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1) →
      seitzHyperGamma 3 E = ⊤

@[expose] def D4ThreeGraphCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → Nat.card K ≠ 2 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
      (∀ α ∈ E,
        α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
          D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      seitzHyperGamma 3 E = ⊤

theorem d4ThreeOuterCubes_of_types (hF : D4ThreeFieldCubes) (hGF : D4ThreeGraphFieldCubes)
    (hG : D4ThreeGraphCubes) : D4ThreeOuterCubes := by
  intro K _ _ hK3 h2 h4 h8 E hE hc hout
  by_cases hF' : ∃ α ∈ E, D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1
  · exact hF K hK3 h8 E hE hc hF'
  push Not at hF'
  by_cases hGF' : ∃ β ∈ E, D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1
  · exact hGF K hK3 E hE hc hF' hGF'
  push Not at hGF'
  refine hG K hK3 h2 h4 E hE hc hout fun α hα hαin => ?_
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.outer_cube_normal_form_cases α (hE.2 α hα) hαin
  rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact absurd ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩ (hF' α hα)
  · exact absurd ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩ (hGF' α hα)
  · exact ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩

theorem d4EightGraphCubes_of_graphCubes (h : D4ThreeGraphCubes) :
    OuterFourSeitz.D4EightGraphCubes := by
  intro K _ _ hK E hE hc hinn hG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) hK
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
  exact h K hK3 (by rw [hK]; norm_num) (by rw [hK]; norm_num) E hE hc hinn hG

end GraphPair

section Planes

variable {S : Type} [Group S] [Finite S]

theorem apply_mem_fixedSubgroup_of_comm {β e : MulAut S} (h : e * β = β * e) {u : S}
    (hu : u ∈ fixedSubgroup β) : e u ∈ fixedSubgroup β := by
  rw [mem_fixedSubgroup] at hu ⊢
  have h1 := congrArg (fun φ : MulAut S => φ u) h
  simp only [MulAut.mul_apply, hu] at h1
  exact h1.symm

@[expose] def restrictFixed {β e : MulAut S} (h : e * β = β * e) : MulAut (fixedSubgroup β) where
  toFun u := ⟨e u, apply_mem_fixedSubgroup_of_comm h u.2⟩
  invFun u := ⟨e⁻¹ u, apply_mem_fixedSubgroup_of_comm (by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]) u.2⟩
  left_inv u := Subtype.ext (MulAut.inv_apply_self _ e (u : S))
  right_inv u := Subtype.ext (MulAut.apply_inv_self _ e (u : S))
  map_mul' u v := Subtype.ext (map_mul e (u : S) v)

@[expose] def restrictFixedHom {E : Subgroup (MulAut S)} {β : MulAut S}
    (hc : ∀ e ∈ E, e * β = β * e) : E →* MulAut (fixedSubgroup β) where
  toFun e := restrictFixed (hc e e.2)
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem fixedSubgroup_le_seitzHyperGamma_of_planes {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) {β : MulAut S} (hβE : β ∈ E)
    (hβ1 : β ≠ 1)
    (hgen : ∀ P : Subgroup (MulAut (fixedSubgroup β)), IsElemAbelian 3 P → Nat.card P = 3 ^ 2 →
      Subgroup.closure {u : fixedSubgroup β | ∃ e ∈ P, e ≠ 1 ∧ e u = u} = ⊤) :
    fixedSubgroup β ≤ seitzHyperGamma 3 E := by
  classical
  have hc27 : Nat.card E = 27 := hcard.trans (by norm_num)
  have hc : ∀ e ∈ E, e * β = β * e := fun e he =>
    CFSG.RankThree.PartTwo.Sec4.E27.comm_of_isElemAbelian hE he hβE
  set ρ := restrictFixedHom hc with hρ
  have hzp : ∀ e ∈ Subgroup.zpowers β, ∀ u ∈ fixedSubgroup β, e u = u := by
    intro e he u hu
    have hle : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut S) u :=
      Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hu)
    have h1 := hle he
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1
  by_cases hker : ∃ e ∈ E, e ∉ Subgroup.zpowers β ∧ ∀ u ∈ fixedSubgroup β, e u = u
  · obtain ⟨e, heE, heβ, hfix⟩ := hker
    intro u hu
    exact CFSG.RankThree.PartTwo.Sec4.E27.mem_seitzHyperGamma_of_fixed hE hc27 hβE heE hβ1 heβ hu
      (hfix u hu)
  push Not at hker
  have hkerle : ρ.ker.map E.subtype ≤ Subgroup.zpowers β := by
    rintro _ ⟨e, he, rfl⟩
    by_contra hne
    obtain ⟨u, hu, hne'⟩ := hker e e.2 hne
    exact hne' (congrArg (fun φ : MulAut (fixedSubgroup β) =>
      ((φ ⟨u, hu⟩ : fixedSubgroup β) : S)) (MonoidHom.mem_ker.1 he))
  have hβker : (⟨β, hβE⟩ : E) ∈ ρ.ker :=
    MonoidHom.mem_ker.2 (MulEquiv.ext fun u => Subtype.ext u.2)
  have hk3 : Nat.card ρ.ker ≤ 3 := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    refine (Subgroup.card_le_of_le hkerle).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE.2 β hβE))
  have hk2 : 1 < Nat.card ρ.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hβker
    exact hβ1 (congrArg Subtype.val hβker)
  have hkd : Nat.card ρ.ker ∣ 27 := hc27 ▸ Subgroup.card_subgroup_dvd_card ρ.ker
  have hk : Nat.card ρ.ker = 3 := by
    interval_cases h : Nat.card ρ.ker
    · exact absurd hkd (by norm_num)
    · rfl
  have hr : Nat.card ρ.range = 3 ^ 2 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hk, hc27] at h1
    omega
  have hPel : IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨ea, hea⟩ := a.2
      obtain ⟨eb, heb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hea, ← heb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (CFSG.RankThree.PartTwo.Sec4.E27.comm_of_isElemAbelian hE ea.2 eb.2)
    · obtain ⟨e, rfl⟩ := hx
      rw [← map_pow]
      have h1 : e ^ 3 = 1 := Subtype.ext (hE.2 _ e.2)
      rw [h1, map_one]
  have hgen' := hgen ρ.range hPel hr
  have hle : Subgroup.closure {u : fixedSubgroup β | ∃ e ∈ ρ.range, e ≠ 1 ∧ e u = u} ≤
      (seitzHyperGamma 3 E).comap (fixedSubgroup β).subtype := by
    rw [Subgroup.closure_le]
    rintro u ⟨_, ⟨e, rfl⟩, he1, heu⟩
    have heβ : (e : MulAut S) ∉ Subgroup.zpowers β := by
      intro h
      exact he1 (MulEquiv.ext fun v => Subtype.ext (hzp _ h v v.2))
    exact CFSG.RankThree.PartTwo.Sec4.E27.mem_seitzHyperGamma_of_fixed hE hc27 hβE e.2 hβ1 heβ
      u.2 (congrArg Subtype.val heu)
  intro u hu
  exact hle (hgen' ▸ Subgroup.mem_top (⟨u, hu⟩ : fixedSubgroup β))

theorem fixedSubgroup_le_seitzHyperGamma_of_cat (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    {β : MulAut S} (hβE : β ∈ E) (hβ1 : β ≠ 1) (d : TauCeti.ValidLieTypeIndex)
    (hpd : 3 ≠ d.1.characteristic) (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (φ : fixedSubgroup β ≃* (TauCeti.CFSGIndex.lie d).Group) :
    fixedSubgroup β ≤ seitzHyperGamma 3 E := by
  refine fixedSubgroup_le_seitzHyperGamma_of_planes hE hcard hβE hβ1 fun P hP hPc => ?_
  set P' := P.map (MulAut.congr φ).toMonoidHom with hP'
  have hP'el : IsElemAbelian 3 P' := CFSG.Open.IsElemAbelian.map hP _
  have hP'c : Nat.card P' = 3 ^ 2 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hPc]
  have hgen := hS2 d 3 Nat.prime_three (by norm_num) hpd hexc P' hP'el hP'c
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective, ← hgen,
    MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨_, ⟨e, heP, rfl⟩, he1, hek⟩, rfl⟩
  refine ⟨e, heP, fun h => he1 (by rw [h, map_one]), ?_⟩
  have h1 : φ (e (φ.symm k)) = k := hek
  show e (φ.symm k) = φ.symm k
  apply φ.injective
  rw [h1, MulEquiv.apply_symm_apply]

theorem eq_top_of_fixed_escape_of_mem {P : Type*} [Group P] [Finite P] {N : Subgroup (MulAut P)}
    {R : Subgroup P} (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤)
    (hker : ∀ ι ∈ N, (∀ x ∈ R, ι x = x) → ι = 1) {α ι ψa ψb : MulAut P} (hι1 : ι ≠ 1)
    (hιN : ι ∈ N) (hψa : ψa ∈ N) (hFa : fixedSubgroup (ψa * α * ψa⁻¹) = R)
    (hFb : fixedSubgroup (ψb * (α * ι) * ψb⁻¹) = R) {H : Subgroup P}
    (hHa : fixedSubgroup α ≤ H) (hHb : fixedSubgroup (α * ι) ≤ H) : H = ⊤ := by
  rw [fixedSubgroup_conj] at hFa hFb
  have hmaxα : ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤ := by
    intro M hM
    have hle : R ≤ M.map ψa.toMonoidHom := by
      rw [← hFa]
      exact Subgroup.map_mono hM
    have hMeq : M = (M.map ψa.toMonoidHom).comap ψa.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective ψa.injective M).symm
    rcases hmax _ hle with h | h
    · left
      rw [hMeq, h, ← hFa]
      exact Subgroup.comap_map_eq_self_of_injective ψa.injective _
    · right
      rw [hMeq, h]
      exact Subgroup.comap_top _
  rcases hmaxα H hHa with h | h
  · exfalso
    have hle : fixedSubgroup (α * ι) ≤ fixedSubgroup α := h ▸ hHb
    have hcard : Nat.card (fixedSubgroup (α * ι)) = Nat.card (fixedSubgroup α) := by
      have h1 := congrArg (fun H : Subgroup P => Nat.card H) hFb
      have h2 := congrArg (fun H : Subgroup P => Nat.card H) hFa
      rw [Subgroup.card_map_of_injective ψb.injective] at h1
      rw [Subgroup.card_map_of_injective ψa.injective] at h2
      rw [h1, h2]
    have heq : fixedSubgroup (α * ι) = fixedSubgroup α :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hιfix : ∀ x ∈ fixedSubgroup α, ι x = x := by
      intro x hx
      have hx' : x ∈ fixedSubgroup (α * ι) := heq ▸ hx
      have h1 : (α * ι) x = x := hx'
      have h2 : α x = x := hx
      simp only [MulAut.mul_apply] at h1
      exact α.injective (h1.trans h2.symm)
    have hι'fix : ∀ x ∈ R, (ψa * ι * ψa⁻¹) x = x := by
      intro x hx
      rw [← hFa] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      show (ψa * ι * ψa⁻¹) (ψa y) = ψa y
      simp [MulAut.mul_apply, hιfix y hy]
    have h1 := hker _ (N.mul_mem (N.mul_mem hψa hιN) (N.inv_mem hψa)) hι'fix
    apply hι1
    have h2 : ψa⁻¹ * (ψa * ι * ψa⁻¹) * ψa = ι := by group
    rw [← h2, h1]
    simp
  · exact h

end Planes

section Cubes

set_option linter.unusedSectionVars false

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.HardMathSupport.Lang.E6Descent (d4Graph_zero exists_frobenius_of_cube
  cube_normal_form_sigma_cube mem_inner_of_normal_form_one)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {K : Type} [Field K] [Finite K]

theorem mem_inner_of_hasNF_zero_one {u : MulAut ↥(adjointGroup Tag.D4 K)} (hu : HasNF u 0 1)
    (hu3 : u ^ 3 = 1) : u ∈ inner ↥(adjointGroup Tag.D4 K) := by
  obtain ⟨g, a, rfl⟩ := hu
  exact mem_inner_of_normal_form_one g a hu3

theorem sigma_cube_of_hasNF {u : MulAut ↥(adjointGroup Tag.D4 K)} {ε : ℕ} {σ : K ≃+* K}
    (hu : HasNF u ε σ) (hu3 : u ^ 3 = 1) : σ ^ 3 = 1 := by
  obtain ⟨g, a, rfl⟩ := hu
  exact cube_normal_form_sigma_cube hu3

theorem eq_or_eq_sq_of_cube {σ σ' : K ≃+* K} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hσ'3 : σ' ^ 3 = 1) (hσ'1 : σ' ≠ 1) : σ' = σ ∨ σ' = σ ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨e, T, -, hef, hT, hT3, hσT⟩ := exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  exact eq_or_sq_of_mem_powers hT3 hσT (eq_T_or_sq_of_cube hK n.pos hef T hT σ' hσ'3 hσ'1)

theorem exists_inner_of_zero_pair {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) {u v : MulAut ↥(adjointGroup Tag.D4 K)} (huE : u ∈ E) (hvE : v ∈ E)
    {σu σv : K ≃+* K} (hu : HasNF u 0 σu) (hv : HasNF v 0 σv) (hu1 : u ≠ 1)
    (hvu : v ∉ Subgroup.zpowers u) :
    ∃ k : ↥(adjointGroup Tag.D4 K), k ≠ 1 ∧ MulAut.conj k ∈ E := by
  have hu3 : u ^ 3 = 1 := hE.2 u huE
  have hv3 : v ^ 3 = 1 := hE.2 v hvE
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  suffices h : ∃ w ∈ E, w ≠ 1 ∧ HasNF w 0 1 by
    obtain ⟨w, hwE, hw1, hw⟩ := h
    obtain ⟨k, rfl⟩ := mem_inner_of_hasNF_zero_one hw (hE.2 w hwE)
    exact ⟨k, fun hk => hw1 (by rw [hk, map_one]), hwE⟩
  by_cases hσu : σu = 1
  · exact ⟨u, huE, hu1, hσu ▸ hu⟩
  by_cases hσv : σv = 1
  · exact ⟨v, hvE, hv1, hσv ▸ hv⟩
  have hσu3 := sigma_cube_of_hasNF hu hu3
  rcases eq_or_eq_sq_of_cube hσu3 hσu (sigma_cube_of_hasNF hv hv3) hσv with h | h
  · refine ⟨v * (u * u), mul_mem hvE (mul_mem huE huE), fun hw => hvu ?_, ?_⟩
    · rw [eq_inv_of_mul_eq_one_left hw]
      exact Subgroup.inv_mem _ (mul_mem (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u))
    · have h' := hv.mul (hu.mul hu)
      rw [h, ← pow_three, hσu3] at h'
      exact h'
  · refine ⟨v * u, mul_mem hvE huE, fun hw => hvu ?_, ?_⟩
    · rw [eq_inv_of_mul_eq_one_left hw]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
    · have h' := hv.mul hu
      rw [h, sq, ← pow_three', hσu3] at h'
      exact h'

theorem exists_hasNF_zero_mul {u v : MulAut ↥(adjointGroup Tag.D4 K)} {εu εv : ℕ}
    {σu σv : K ≃+* K} (hu : HasNF u εu σu) (hv : HasNF v εv σv) (hεu : εu < 3) (hεv : εv < 3)
    (hεv0 : εv ≠ 0) : ∃ w ∈ Subgroup.zpowers v, ∃ σ' : K ≃+* K, HasNF (u * w) 0 σ' := by
  by_cases h0 : εu = 0
  · subst h0
    exact ⟨1, Subgroup.one_mem _, σu, by rw [mul_one]; exact hu⟩
  by_cases hεε : εu = εv
  · refine ⟨v * v, mul_mem (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v), σu * (σv * σv), ?_⟩
    have h' := (hu.mul (hv.mul hv)).mod_three
    rwa [show (εu + (εv + εv)) % 3 = 0 by omega] at h'
  · refine ⟨v, Subgroup.mem_zpowers v, σu * σv, ?_⟩
    have h' := (hu.mul hv).mod_three
    rwa [show (εu + εv) % 3 = 0 by omega] at h'

theorem exists_inner_ne_one_of_cube {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3) :
    ∃ k : ↥(adjointGroup Tag.D4 K), k ≠ 1 ∧ MulAut.conj k ∈ E := by
  classical
  obtain ⟨x₁, hx₁E, hx₁1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [hbot, Subgroup.card_bot] at hc
    norm_num at hc
  have hx₁3 : x₁ ^ 3 = 1 := hE.2 x₁ hx₁E
  obtain ⟨x₂, hx₂E, hx₂1⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers x₁ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx : E ≤ Subgroup.zpowers x₁)
    rw [hc, Nat.card_zpowers] at h1
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx₁3)
    omega
  have hcl9 : Nat.card (Subgroup.closure ({x₁, x₂} : Set (MulAut ↥(adjointGroup Tag.D4 K)))) =
      3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hE hx₁E hx₂E hx₁1 hx₂1
  set C := Subgroup.closure ({x₁, x₂} : Set (MulAut ↥(adjointGroup Tag.D4 K))) with hC
  obtain ⟨x₃, hx₃E, hx₃C⟩ : ∃ x ∈ E, x ∉ C := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx : E ≤ C)
    rw [hc, hcl9] at h1
    omega
  obtain ⟨g₁, a₁, σ₁, ε₁, hε₁, -, h₁⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma x₁ hx₁3
  obtain ⟨g₂, a₂, σ₂, ε₂, hε₂, -, h₂⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma x₂ (hE.2 x₂ hx₂E)
  obtain ⟨g₃, a₃, σ₃, ε₃, hε₃, -, h₃⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma x₃ (hE.2 x₃ hx₃E)
  have n₁ : HasNF x₁ ε₁ σ₁ := ⟨g₁, a₁, h₁⟩
  have n₂ : HasNF x₂ ε₂ σ₂ := ⟨g₂, a₂, h₂⟩
  have n₃ : HasNF x₃ ε₃ σ₃ := ⟨g₃, a₃, h₃⟩
  have hz₁ : Subgroup.zpowers x₁ ≤ C :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hz₂ : Subgroup.zpowers x₂ ≤ C :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hesc : ∀ w ∈ C, x₃ * w ∉ C := by
    intro w hw h
    apply hx₃C
    have h1 := mul_mem h (inv_mem hw)
    rwa [mul_inv_cancel_right] at h1
  by_cases h0 : ε₁ = 0
  · subst h0
    by_cases h20 : ε₂ = 0
    · subst h20
      exact exists_inner_of_zero_pair hE hx₁E hx₂E n₁ n₂ hx₁1 hx₂1
    · obtain ⟨w, hw, σ', hw'⟩ := exists_hasNF_zero_mul n₃ n₂ hε₃ hε₂ h20
      exact exists_inner_of_zero_pair hE hx₁E (mul_mem hx₃E (Subgroup.zpowers_le.2 hx₂E hw)) n₁
        hw' hx₁1 fun h => hesc w (hz₂ hw) (hz₁ h)
  · obtain ⟨w₂, hw₂, σ₂', n₂'⟩ := exists_hasNF_zero_mul n₂ n₁ hε₂ hε₁ h0
    obtain ⟨w₃, hw₃, σ₃', n₃'⟩ := exists_hasNF_zero_mul n₃ n₁ hε₃ hε₁ h0
    have hw₂E : w₂ ∈ E := Subgroup.zpowers_le.2 hx₁E hw₂
    have hw₃E : w₃ ∈ E := Subgroup.zpowers_le.2 hx₁E hw₃
    refine exists_inner_of_zero_pair hE (mul_mem hx₂E hw₂E) (mul_mem hx₃E hw₃E) n₂' n₃' ?_ ?_
    · intro h
      apply hx₂1
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem hw₂
    · intro h
      have hcl : x₂ * w₂ ∈ C :=
        mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (hz₁ hw₂)
      exact hesc w₃ (hz₁ hw₃) (Subgroup.zpowers_le.2 hcl h)

@[expose] def d4Index (q : TauCeti.PrimePower) : TauCeti.ValidLieTypeIndex :=
  ⟨.D 4 q, by simp [TauCeti.LieTypeIndex.valid_iff]⟩

@[expose] def trialityIndex (q : TauCeti.PrimePower) : TauCeti.ValidLieTypeIndex :=
  ⟨.trialityD4 q, by simp [TauCeti.LieTypeIndex.valid_iff]⟩

theorem nonempty_subfieldGroup_equiv_d4 {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) (T : K ≃+* K)
    (hT3 : T ^ 3 = 1) (hTc : Nat.card (fixSubfield T) = ℓ ^ e) :
    Nonempty (↥(subfieldGroup Tag.D4 T) ≃*
      (TauCeti.CFSGIndex.lie (d4Index ⟨ℓ, e, hℓ, he⟩)).Group) := by
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
    (fixSubfield T) ⟨ℓ, e, hℓ, he⟩ (d4Index ⟨ℓ, e, hℓ, he⟩).2
    (by rw [hTc, TauCeti.PrimePower.card_def])
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 (fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact ⟨(fixedD4Equiv T hT3).trans
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ)⟩

theorem nonempty_fixed_d4Twist_equiv_triality {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = (ℓ ^ e) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) :
    Nonempty (↥(fixedSubgroup (d4Twist 1 T)) ≃*
      (TauCeti.CFSGIndex.lie (trialityIndex ⟨ℓ, e, hℓ, he⟩)).Group) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcharK : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (k := e * 3)
      (by omega) (by rw [hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨-, -, hHC, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    ℓ e hℓ he K hK Ω 1 (Or.inl rfl) T.toRingHom
    (fun c => by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hT, pow_one])
    (iterateFrobenius Ω ℓ e) (fun c => by rw [iterateFrobenius_def])
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_trialityD4_of_field
    ⟨ℓ, e, hℓ, he⟩ (trialityIndex ⟨ℓ, e, hℓ, he⟩).2 K (by rw [hK, TauCeti.PrimePower.card_def]) T
    (fun c => by rw [hT, TauCeti.PrimePower.card_def])
  exact ⟨(CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroupTwistedEntrywiseAutOneEquiv
    TwistTag.D4 T).trans ((MulEquiv.subgroupCongr hHC).trans φ.symm)⟩

theorem nonempty_fixed_d4Twist_equiv_triality' {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = (ℓ ^ e) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) {τ : K ≃+* K}
    (hτ : τ = T ∨ τ = T⁻¹) :
    Nonempty (↥(fixedSubgroup (d4Twist 1 τ)) ≃*
      (TauCeti.CFSGIndex.lie (trialityIndex ⟨ℓ, e, hℓ, he⟩)).Group) := by
  obtain ⟨φ⟩ := nonempty_fixed_d4Twist_equiv_triality hℓ he hK T hT
  rcases hτ with rfl | rfl
  · exact ⟨φ⟩
  · refine ⟨(OuterFourSeitz.fixedTwistSwapEquiv T⁻¹).trans ?_⟩
    rw [inv_inv]
    exact φ

theorem fixed_le_of_conj_cat (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) {R : Subgroup ↥(adjointGroup Tag.D4 K)} (hR : R ≠ ⊤)
    (d : TauCeti.ValidLieTypeIndex) (hpd : 3 ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (φ₀ : ↥R ≃* (TauCeti.CFSGIndex.lie d).Group) {γ ψ : MulAut ↥(adjointGroup Tag.D4 K)}
    (hF : fixedSubgroup (ψ * γ * ψ⁻¹) = R) (hγE : γ ∈ E) :
    fixedSubgroup γ ≤ seitzHyperGamma 3 E := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [fixedSubgroup_conj_one] at hF
    exact hR hF.symm
  have hF' := hF
  rw [fixedSubgroup_conj] at hF'
  exact fixedSubgroup_le_seitzHyperGamma_of_cat hS2 hE hc hγE hγ1 d hpd hexc
    ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      ((MulEquiv.subgroupCongr hF').trans φ₀))

theorem seitzHyperGamma_eq_top_of_field (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hK3 : ringChar K ≠ 3) (hK8 : Nat.card K ≠ 8)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) {α : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E)
    (hαT : D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1) : seitzHyperGamma 3 E = ⊤ := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  obtain ⟨g, a, σ, ε, -, hσ3, ⟨hε0, hσ1⟩, hα⟩ := hαT
  subst hε0
  have hNF : HasNF α 0 σ := ⟨g, a, hα⟩
  rw [d4Graph_zero, mul_one] at hα
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ := exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  have hK' : Nat.card K = (ringChar K ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  have hordT : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  have hq0 : Nat.card (fixSubfield T) = ringChar K ^ e := card_fixSubfield_eq_pow hK hef T hT3 hT1
  have h2 : Nat.card (fixSubfield T) ≠ 2 := by
    intro h2
    apply hK8
    rw [hK', ← hq0, h2]
    norm_num
  have hbig : 2 < Nat.card (fixSubfield T) := by
    have : 2 ≤ Nat.card (fixSubfield T) := Finite.one_lt_card
    omega
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  let L := AlgebraicClosure K
  obtain ⟨ψa, hψa, hFa⟩ :=
    exists_conj_fixedSubgroup_D4_field hK hK4 he0 hef T σ hT hT3 hσT L g a α hα hα3
  obtain ⟨k, hk1, hkE⟩ := exists_inner_ne_one_of_cube hE hc
  have hα'E : α * MulAut.conj k ∈ E := mul_mem hαE hkE
  obtain ⟨g₂, a₂, hα'⟩ : HasNF (α * MulAut.conj k) 0 σ := by
    simpa only [add_zero, mul_one] using hNF.mul (hasNF_conj k)
  rw [d4Graph_zero, mul_one] at hα'
  obtain ⟨ψb, -, hFb⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 he0 hef T σ hT hT3 hσT L g₂ a₂
    _ hα' (hE.2 _ hα'E)
  obtain ⟨φ₀⟩ := nonempty_subfieldGroup_equiv_d4 hℓ he0 T hT3 hq0
  have hpd : 3 ≠ (d4Index ⟨ringChar K, e, hℓ, he0⟩).1.characteristic := by
    simp only [d4Index, TauCeti.LieTypeIndex.characteristic_D]
    exact fun h => hK3 h.symm
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 (d4Index ⟨ringChar K, e, hℓ, he0⟩).1 := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException, d4Index]
  have hne := subfieldGroup_ne_top_D4 hT1
  have hHa := fixed_le_of_conj_cat hS2 hE hc hne _ hpd hexc φ₀ hFa hαE
  have hHb := fixed_le_of_conj_cat hS2 hE hc hne _ hpd hexc φ₀ hFb hα'E
  have hdeg : entryDegreeBound Tag.D4 = 2 := by simp [entryDegreeBound]
  have hι1 : MulAut.conj k ≠ 1 := fun h => hk1 (conj_injective_D4 (by rw [h, map_one]))
  have hιN : MulAut.conj k ∈ matrixInner Tag.D4 K L := by
    have h := conj_mul_rootDiagAut_mem_matrixInner L k 1
    rwa [show rootDiagAut Tag.D4 K 1 = 1 from map_one (rootDiagAutHom Tag.D4 K), mul_one] at h
  refine eq_top_of_fixed_escape_of_mem (N := matrixInner Tag.D4 K L)
    (subfieldMaximal_D4_of_card_ne_two T Nat.prime_three (by norm_num) hordT h2) ?_ hι1 hιN hψa
    hFa hFb hHa hHb
  intro ι' hι'N hι'fix
  refine eq_one_of_mem_matrixInner_of_fix_subfield (fixSubfield T) (by rw [hdeg]; exact hbig)
    hι'N ?_
  intro x hx
  apply hι'fix
  have h1 := fixedFieldImage_le (σ := T) hx
  rw [mem_fixedSubgroup]
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  exact ((mem_entrywiseFixedGroup).1 h1).2

theorem seitzHyperGamma_eq_top_of_graphField (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hK3 : ringChar K ≠ 3) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3) {β : MulAut ↥(adjointGroup Tag.D4 K)}
    (hβE : β ∈ E) (hβT : D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1) : seitzHyperGamma 3 E = ⊤ := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  haveI := inner_normal ↥(adjointGroup Tag.D4 K)
  obtain ⟨g, a, σ, ε, hεlt, hσ3, ⟨hε0, hσ1⟩, hβ⟩ := hβT
  have hε12 : ε = 1 ∨ ε = 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ := exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  have hK' : Nat.card K = (ringChar K ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  have hσ' : σ = T ∨ σ = T⁻¹ := by
    rcases hσT with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm)
  have hβ3 : β ^ 3 = 1 := hE.2 β hβE
  obtain ⟨ψa, hFa⟩ := exists_conj_fixedSubgroup_D4_graphField hK hK4 he0 hef T σ hT hT3 hT1 hσ'
    hε12 g a β hβ3 hβ
  obtain ⟨k, hk1, hkE⟩ := exists_inner_ne_one_of_cube hE hc
  have hβ'E : β * MulAut.conj k ∈ E := mul_mem hβE hkE
  obtain ⟨g₂, a₂, hβ'⟩ : HasNF (β * MulAut.conj k) ε σ := by
    simpa only [add_zero, mul_one] using (show HasNF β ε σ from ⟨g, a, hβ⟩).mul (hasNF_conj k)
  obtain ⟨ψb, hFb⟩ := exists_conj_fixedSubgroup_D4_graphField hK hK4 he0 hef T σ hT hT3 hT1 hσ'
    hε12 g₂ a₂ _ (hE.2 _ hβ'E) hβ'
  obtain ⟨φ₀⟩ := nonempty_fixed_d4Twist_equiv_triality' hℓ he0 hK' T hT (d4GfTwist_eq_or T σ ε)
  have hpd : 3 ≠ (trialityIndex ⟨ringChar K, e, hℓ, he0⟩).1.characteristic := by
    simp only [trialityIndex, TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact fun h => hK3 h.symm
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
      (trialityIndex ⟨ringChar K, e, hℓ, he0⟩).1 := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException, trialityIndex]
  have hne := fixedSubgroup_d4Twist_ne_top (d4GfTwist T σ ε)
  have hHa := fixed_le_of_conj_cat hS2 hE hc hne _ hpd hexc φ₀ hFa hβE
  have hHb := fixed_le_of_conj_cat hS2 hE hc hne _ hpd hexc φ₀ hFb hβ'E
  have hι1 : MulAut.conj k ≠ 1 := fun h => hk1 (conj_injective_D4 (by rw [h, map_one]))
  refine OuterFourSeitz.eq_top_of_fixed_escape (N := inner ↥(adjointGroup Tag.D4 K))
    (D4TwistedSubfieldMaximal_of_entry D4TwF2Entry.D4TwF2EntryProp_holds K hK3 _
      (OuterFourSeitz.orderOf_d4GfTwist hT3 hT1 σ ε)) ?_ hι1 ⟨k, rfl⟩ hFa hFb hHa hHb
  intro ι' hι' hfix
  obtain ⟨z, rfl⟩ := hι'
  have hz : z = 1 := by
    refine eq_one_of_commute_fixed_twisted_D4 (d4GfTwist T σ ε) fun u hu => ?_
    have h1 := hfix u hu
    rw [MulAut.conj_apply] at h1
    calc z * u = (z * u * z⁻¹) * z := by group
      _ = u * z := by rw [h1]
  rw [hz, map_one]

theorem d4ThreeFieldCubes_holds (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) :
    D4ThreeFieldCubes := by
  intro K _ _ hK3 hK8 E hE hc hF
  obtain ⟨α, hαE, hαT⟩ := hF
  exact seitzHyperGamma_eq_top_of_field hS2 hK3 hK8 hE hc hαE hαT

theorem d4ThreeGraphFieldCubes_holds (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) :
    D4ThreeGraphFieldCubes := by
  intro K _ _ hK3 E hE hc _ hGF
  obtain ⟨β, hβE, hβT⟩ := hGF
  exact seitzHyperGamma_eq_top_of_graphField hS2 hK3 hE hc hβE hβT

theorem seitzGoodOuterHighD4Three_of_graphCubes (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hG : D4ThreeGraphCubes) : OuterHigh2.SeitzGoodOuterHighD4Three :=
  seitzGoodOuterHighD4Three_of_model
    (d4ThreeOuterCubes_of_types (d4ThreeFieldCubes_holds hS2) (d4ThreeGraphFieldCubes_holds hS2) hG)

end Cubes

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
