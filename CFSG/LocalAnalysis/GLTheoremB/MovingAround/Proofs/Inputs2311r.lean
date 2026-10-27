module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311q2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Sylow
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Closing
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Top
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311r

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

section Abstract

variable {G : Type*} [Group G]

theorem conj_mulAut_conj_inputs2311r (ψ : MulAut G) (g : G) :
    ψ * MulAut.conj g * ψ⁻¹ = MulAut.conj (ψ g) := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    MulAut.apply_inv_self, map_inv]

theorem conj_mem_innerAut_iff_inputs2311r (ψ β : MulAut G) :
    ψ * β * ψ⁻¹ ∈ CFSG.Fischer.innerAut G ↔ β ∈ CFSG.Fischer.innerAut G := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨ψ⁻¹ g, ?_⟩
    have h1 := conj_mulAut_conj_inputs2311r ψ⁻¹ g
    rw [inv_inv] at h1
    rw [← h1]
    change ψ⁻¹ * MulAut.conj g * ψ = β
    rw [hg]
    group
  · rintro ⟨g, rfl⟩
    exact ⟨ψ g, (conj_mulAut_conj_inputs2311r ψ g).symm⟩

end Abstract

section Frame

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem isA2Type_conj_inputs2311r (ψ : MulAut ↥(adjointGroup Tag.D4 K)) {β : MulAut ↥(adjointGroup Tag.D4 K)}
    (h : IsA2Type β) : IsA2Type (ψ * β * ψ⁻¹) := by
  obtain ⟨φ, B, hB3, hB1, hφ⟩ := h
  refine ⟨φ * ψ⁻¹, B, hB3, hB1, ?_⟩
  rw [show φ * ψ⁻¹ * (ψ * β * ψ⁻¹) * (φ * ψ⁻¹)⁻¹ = φ * β * φ⁻¹ by group]
  exact hφ

theorem gammaP_frameD_eq_inputs2311r {B : SL2 K} (hB3 : B ^ 3 = 1) :
    gammaP K B (frameD K B) = frameDiag B * frameD K B := by
  have h := Inputs2311m.frameD_mul_inv_gammaP_frameD (K := K) hB3
  calc gammaP K B (frameD K B) = (frameD K B * (gammaP K B (frameD K B))⁻¹)⁻¹ * frameD K B := by group
    _ = frameDiag B * frameD K B := by rw [h, inv_inv]

end Frame

section Residual

@[expose] def D4NonsplitGraphPlanes :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 → Nat.card K % 3 = 2 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 ↥E →
      Nat.card E = 3 ^ 2 → gammaP K (orderThreeSL K) ∈ E →
      (∀ β ∈ E, β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) → IsA2Type β) →
      (∀ c : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c = c →
        MulAut.conj (frameDiag (orderThreeSL K)) ∉ E.map (MulAut.congr (MulAut.conj c)).toMonoidHom) →
      ∀ x : ↥(adjointGroup Tag.D4 K), x ≠ 1 → MulAut.conj x ∈ E →
        Commute x (frameD K (orderThreeSL K)) → uniPlaneClosure (ringChar K) E = ⊤

@[expose] def D4PlanesRest3Tri :
    Prop :=
  UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ ¬ InnerPlane d p E ∧
    ¬ Inputs2311k.D4GraphG2Plane d p E ∧ ¬ Inputs2311m.D4GraphA2FramePlane d p E ∧
    ¬ Inputs2311m.TrialityBorelPairPlane d p E ∧ IsTrialityIndex d.1

end Residual

section Reduction

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_dFour_graphNonsplit_of (h : D4NonsplitGraphPlanes) :
    UniSeitzPlanes fun d p E => p = 3 ∧ d.1.characteristic ≠ 2 ∧ ¬ InnerPlane d p E ∧
      ¬ Inputs2311k.D4GraphG2Plane d p E ∧ ¬ Inputs2311m.D4GraphA2FramePlane d p E ∧
      ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.card % 3 = 2 ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
          ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K),
            ∀ α ∈ E.map (MulAut.congr e).toMonoidHom, α ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) →
              D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, hchar2, hin, hg2, hfr, q, hq, hq2, K, hF, hfin, hK, e, hG⟩
  obtain rfl : d = .D 4 q := hq
  have hchar : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_D]
  have hK' : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK'
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq2' : q.p ≠ 2 := fun h => hchar2 (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have hK2 : ringChar K ≠ 2 := by rw [hring]; exact hq2'
  have hK3 : ringChar K ≠ 3 := by rw [hring]; exact hq3
  obtain ⟨-, -, hK5⟩ := Inputs2311q.ringChar_facts_inputs2311q hK2 hK3
  have h5 : 5 ≤ ringChar K := by
    have h2 := q.prime_p.two_le
    have h4 : q.p ≠ 4 := fun h => by have := q.prime_p; rw [h] at this; norm_num at this
    rw [hring]
    omega
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq2
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  haveI hE'ea : CFSG.IsElementaryAbelian 3 ↥E' :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card E' = 3 ^ 2 := by rw [hE', card_map_congr, hc]
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E', β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) := by
    by_contra hcon
    push Not at hcon
    apply hin
    intro φ hφ
    obtain ⟨g, hg⟩ := hcon _ (Subgroup.mem_map_of_mem _ hφ)
    refine ⟨e.symm g, ?_⟩
    have h1 : (MulAut.congr e).toMonoidHom (MulAut.conj (e.symm g)) = (MulAut.congr e).toMonoidHom φ := by
      rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hg]
    exact (MulAut.congr e).injective h1
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hG β hβE hβout
  subst hσ1
  have hβNF : HasNF β ε 1 := ⟨g, a, hβeq⟩
  obtain ⟨ι, hιE, hι1, ⟨x, rfl⟩⟩ := exists_inner_ne_one_of_graph hc' hG hβE (by omega) hβNF
  have hx1 : x ≠ 1 := fun h => hι1 (by rw [h, map_one])
  have hA2 : ∀ α ∈ E', α ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) → IsA2Type α := by
    intro α hαE hαout
    have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
    rcases ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
        ClassOdd.g2ThreeClass_holds K h5 α hα3 (hG α hαE hαout) with ⟨ψ, hψ⟩ | hA
    · exfalso
      apply hg2
      have hmapψ : ∀ φ ∈ E', (MulAut.congr ψ).toMonoidHom φ ∈
          E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
        intro φ hφ
        obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
        exact ⟨φ₀, hφ₀, Inputs2311k.mulAut_congr_trans_excD4 e ψ φ₀⟩
      have hγ : d4Graph K 1 ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
        have hα' := hmapψ α hαE
        rw [Inputs2311q.mulAut_congr_self_inputs2311q] at hα'
        rcases hψ with h | h
        · rwa [h] at hα'
        · rw [h] at hα'
          have h4 : d4Graph K 2 * d4Graph K 2 = d4Graph K 1 := by
            rw [← d4Graph_add, show (2 : ℕ) + 2 = 1 + 3 from rfl, d4Graph_add, d4Graph_three, mul_one]
          rw [← h4]
          exact Subgroup.mul_mem _ hα' hα'
      have hx' : MulAut.conj (ψ x) ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
        have := hmapψ _ hιE
        rwa [mulAut_congr_conj] at this
      have hψx1 : ψ x ≠ 1 := fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm))
      exact ⟨rfl, hchar2, q, rfl, K, hF, hfin, hK, e.trans ψ, hγ, ψ x, hψx1, hx'⟩
    · exact hA
  obtain ⟨ψ, B, hB3, hB1, hψ⟩ := hA2 β hβE hβout
  have h3 : 3 ∣ Nat.card K + 1 := by omega
  obtain ⟨S, hS⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_conj_eq_orderThreeSL h3 hB3 hB1
  set Ψ : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.conj (sl2At K ⟨2, by decide⟩ S) * ψ with hΨ
  set f₁ := (e.trans ψ).trans (MulAut.conj (sl2At K ⟨2, by decide⟩ S)) with hf₁
  have hcongr₁ : ∀ φ₀ : MulAut (Cat ⟨.D 4 q, hv⟩), (MulAut.congr f₁).toMonoidHom φ₀ =
      Ψ * (MulAut.congr e).toMonoidHom φ₀ * Ψ⁻¹ := by
    intro φ₀
    rw [hf₁, Inputs2311k.mulAut_congr_trans_excD4, Inputs2311k.mulAut_congr_trans_excD4,
      Inputs2311q.mulAut_congr_self_inputs2311q, Inputs2311q.mulAut_congr_self_inputs2311q, hΨ]
    group
  set E₁ := E.map (MulAut.congr f₁).toMonoidHom with hE₁
  have hmap₁ : ∀ φ ∈ E', Ψ * φ * Ψ⁻¹ ∈ E₁ := by
    intro φ hφ
    obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
    exact ⟨φ₀, hφ₀, hcongr₁ φ₀⟩
  have hα₀E₁ : gammaP K (orderThreeSL K) ∈ E₁ := by
    have hβ' := hmap₁ β hβE
    have e1 : Ψ * β * Ψ⁻¹ = MulAut.conj (sl2At K ⟨2, by decide⟩ S) * (ψ * β * ψ⁻¹) *
        (MulAut.conj (sl2At K ⟨2, by decide⟩ S))⁻¹ := by
      rw [hΨ]
      group
    rcases hψ with hψ' | hψ'
    · rwa [e1, hψ', conj_gammaP, hS] at hβ'
    · have e2 : MulAut.conj (sl2At K ⟨2, by decide⟩ S) * (gammaP K B)⁻¹ *
          (MulAut.conj (sl2At K ⟨2, by decide⟩ S))⁻¹ =
          (MulAut.conj (sl2At K ⟨2, by decide⟩ S) * gammaP K B *
            (MulAut.conj (sl2At K ⟨2, by decide⟩ S))⁻¹)⁻¹ := by group
      rw [e1, hψ', e2, conj_gammaP, hS] at hβ'
      have := Subgroup.inv_mem _ hβ'
      rwa [inv_inv] at this
  set x₁ := sl2At K ⟨2, by decide⟩ S * ψ x * (sl2At K ⟨2, by decide⟩ S)⁻¹ with hx₁def
  have hx₁E₁ : MulAut.conj x₁ ∈ E₁ := by
    have := hmap₁ _ hιE
    rwa [conj_mulAut_conj_inputs2311r, hΨ, MulAut.mul_apply, MulAut.conj_apply] at this
  have hx₁1 : x₁ ≠ 1 := by
    intro h0
    rw [hx₁def, conj_eq_one_iff] at h0
    exact hx1 (ψ.injective (h0.trans (map_one ψ).symm))
  haveI hE₁ea : CFSG.IsElementaryAbelian 3 ↥E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr f₁ hE)
  have hx₁3 : x₁ ^ 3 = 1 := by
    apply conj_injective_adj
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx₁E₁
  have hαx₁ : gammaP K (orderThreeSL K) x₁ = x₁ := by
    apply conj_injective_adj
    have hcomm : gammaP K (orderThreeSL K) * MulAut.conj x₁ =
        MulAut.conj x₁ * gammaP K (orderThreeSL K) := by
      have := hE₁ea.toIsMulCommutative.is_comm.comm (⟨_, hα₀E₁⟩ : E₁) ⟨_, hx₁E₁⟩
      exact congrArg Subtype.val this
    rw [← conj_mulAut_conj_inputs2311r, hcomm, mul_inv_cancel_right]
  obtain ⟨c, hcα, hcd⟩ := nonsplitSylowCentral_holds K hqK (by omega) x₁ hαx₁ hx₁3
  have hcα' : gammaP K (orderThreeSL K) c⁻¹ = c⁻¹ := by rw [map_inv, hcα]
  set f₂ := f₁.trans (MulAut.conj c⁻¹) with hf₂
  have hcongr₂ : ∀ φ₀ : MulAut (Cat ⟨.D 4 q, hv⟩), (MulAut.congr f₂).toMonoidHom φ₀ =
      (MulAut.conj c⁻¹ * Ψ) * (MulAut.congr e).toMonoidHom φ₀ * (MulAut.conj c⁻¹ * Ψ)⁻¹ := by
    intro φ₀
    rw [hf₂, Inputs2311k.mulAut_congr_trans_excD4, hcongr₁, Inputs2311q.mulAut_congr_self_inputs2311q]
    group
  set E₂ := E.map (MulAut.congr f₂).toMonoidHom with hE₂
  haveI hE₂ea : CFSG.IsElementaryAbelian 3 ↥E₂ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr f₂ hE)
  have hc₂ : Nat.card E₂ = 3 ^ 2 := by rw [hE₂, card_map_congr, hc]
  have hstep₂ : ∀ φ₀ : MulAut (Cat ⟨.D 4 q, hv⟩), (MulAut.congr f₂).toMonoidHom φ₀ =
      (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom ((MulAut.congr f₁).toMonoidHom φ₀) := fun φ₀ =>
    Inputs2311k.mulAut_congr_trans_excD4 f₁ (MulAut.conj c⁻¹) φ₀
  have hα₀E₂ : gammaP K (orderThreeSL K) ∈ E₂ := by
    obtain ⟨φ₀, hφ₀, hφ₀α⟩ := hα₀E₁
    refine ⟨φ₀, hφ₀, ?_⟩
    rw [hstep₂, hφ₀α]
    exact Inputs2311q.mulAut_congr_conj_of_fixed_inputs2311q hcα'
  set x₂ := c⁻¹ * x₁ * c with hx₂def
  have hx₂E₂ : MulAut.conj x₂ ∈ E₂ := by
    obtain ⟨φ₀, hφ₀, hφ₀x⟩ := hx₁E₁
    refine ⟨φ₀, hφ₀, ?_⟩
    rw [hstep₂, hφ₀x, mulAut_congr_conj, MulAut.conj_apply, inv_inv]
  have hx₂1 : x₂ ≠ 1 := by
    intro h0
    apply hx₁1
    have e : x₁ = c * x₂ * c⁻¹ := by rw [hx₂def]; group
    rw [e, h0]
    group
  have hA2₂ : ∀ β' ∈ E₂, β' ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) → IsA2Type β' := by
    rintro _ ⟨φ₀, hφ₀, rfl⟩ hout
    rw [hcongr₂] at hout ⊢
    have hout' : (MulAut.congr e).toMonoidHom φ₀ ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) :=
      fun hmem => hout ((conj_mem_innerAut_iff_inputs2311r _ _).2 hmem)
    exact isA2Type_conj_inputs2311r _ (hA2 _ (Subgroup.mem_map_of_mem _ hφ₀) hout')
  have hnf₂ : ∀ c' : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c' = c' →
      MulAut.conj (frameDiag (orderThreeSL K)) ∉ E₂.map (MulAut.congr (MulAut.conj c')).toMonoidHom := by
    intro c' hc' hΔ
    apply hfr
    have hstep₃ : ∀ φ₀ : MulAut (Cat ⟨.D 4 q, hv⟩), (MulAut.congr (f₂.trans (MulAut.conj c'))).toMonoidHom φ₀ =
        (MulAut.congr (MulAut.conj c')).toMonoidHom ((MulAut.congr f₂).toMonoidHom φ₀) := fun φ₀ =>
      Inputs2311k.mulAut_congr_trans_excD4 f₂ (MulAut.conj c') φ₀
    refine ⟨rfl, hchar2, q, rfl, K, hF, hfin, hK, f₂.trans (MulAut.conj c'), ?_, ?_⟩
    · obtain ⟨φ₀, hφ₀, hφ₀α⟩ := hα₀E₂
      refine ⟨φ₀, hφ₀, ?_⟩
      rw [hstep₃, hφ₀α]
      exact Inputs2311q.mulAut_congr_conj_of_fixed_inputs2311q hc'
    · obtain ⟨_, ⟨φ₀, hφ₀, rfl⟩, hφ₀Δ⟩ := hΔ
      exact ⟨φ₀, hφ₀, by rw [hstep₃]; exact hφ₀Δ⟩
  have htop := h K hK2 hK3 hqK E₂ hE₂ea hc₂ hα₀E₂ hA2₂ hnf₂ x₂ hx₂1 hx₂E₂ hcd
  rw [hring] at htop
  rw [hchar]
  exact (uniPlaneGen_map_congr f₂ q.p E).1 htop

theorem d4PlanesRest3_of_rest4 (h : D4NonsplitGraphPlanes ∧
    D4PlanesRest3Tri) : Inputs2311q.D4PlanesRest3 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg, hf, hb, hs⟩
  rcases hR.2 with ⟨-, hp3, -, -, ⟨q, hq, K, hF, hfin, hK, e, hG⟩, -⟩ | ⟨hin', -⟩ | ⟨-, -, htri, -⟩
  · have hq2 : q.card % 3 = 2 := by
      have h1 : q.card % 3 ≠ 1 := fun h1 => hs ⟨q, hq, h1⟩
      have h0 : q.card % 3 ≠ 0 := by
        intro h0
        have hdvd : 3 ∣ q.p ^ q.exponent := by
          rw [← TauCeti.PrimePower.card_def]
          exact Nat.dvd_of_mod_eq_zero h0
        have h3p : 3 = q.p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
          (Nat.prime_three.dvd_of_dvd_pow hdvd)
        apply hpd
        rw [hq, TauCeti.LieTypeIndex.characteristic_D, hp3, h3p]
      omega
    exact uniSeitzPlanes_dFour_graphNonsplit_of h.1 d p hp hp2 hpd hex E hE hc
      ⟨hp3, hR.1.1.1, hin, hg, hf, q, hq, hq2, K, hF, hfin, hK, e, hG⟩
  · exact absurd hin' hin
  · exact h.2 d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg, hf, hb, htri⟩

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311r
