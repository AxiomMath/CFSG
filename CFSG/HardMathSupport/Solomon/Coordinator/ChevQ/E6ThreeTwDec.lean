module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDecSplit
public import CFSG.GH74.Generic.S1.RCard
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDecRho

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3 card_fixSubfield_twisted)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [Group G]

theorem twDec_conj_eq_of_commute {b y : G} (h : Commute b y) : b * y * b⁻¹ = y := by
  rw [h.eq]
  group

theorem twDec_prod_conj₀ {l₀ l₁ l₂ r : G} (h1 : Commute l₁ r) (h2 : Commute l₂ r) :
    l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₀ * r * l₀⁻¹ := by
  have e : l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₀ * (l₁ * (l₂ * r * l₂⁻¹) * l₁⁻¹) * l₀⁻¹ := by
    group
  rw [e, twDec_conj_eq_of_commute h2, twDec_conj_eq_of_commute h1]

theorem twDec_prod_conj₁ {l₀ l₁ l₂ r : G} (h0 : Commute l₀ l₁) (h0' : Commute l₀ r)
    (h2 : Commute l₂ r) : l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₁ * r * l₁⁻¹ := by
  have e : l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₀ * (l₁ * (l₂ * r * l₂⁻¹) * l₁⁻¹) * l₀⁻¹ := by
    group
  rw [e, twDec_conj_eq_of_commute h2]
  exact twDec_conj_eq_of_commute ((h0.mul_right h0').mul_right h0.inv_right)

theorem twDec_prod_conj₂ {l₀ l₁ l₂ r : G} (h0 : Commute l₀ l₂) (h0' : Commute l₀ r)
    (h1 : Commute l₁ l₂) (h1' : Commute l₁ r) :
    l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₂ * r * l₂⁻¹ := by
  have e : l₀ * l₁ * l₂ * r * (l₀ * l₁ * l₂)⁻¹ = l₀ * (l₁ * (l₂ * r * l₂⁻¹) * l₁⁻¹) * l₀⁻¹ := by
    group
  rw [e, twDec_conj_eq_of_commute ((h1.mul_right h1').mul_right h1.inv_right)]
  exact twDec_conj_eq_of_commute ((h0.mul_right h0').mul_right h0.inv_right)

end Group

section Model


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {ℓ f : ℕ}

theorem twConjSU_mul (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K 3))
    (y w : unitarySU ℓ f K 3) :
    conjSU h (A * ⟨y, unitarySU_le_primeFormUnitary h y.2⟩) w = conjSU h A (y * w * y⁻¹) := by
  apply Subtype.ext
  rw [coe_conjSU, coe_conjSU]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

theorem twDec_layerProd_conj {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    (x : Fin 3 → unitarySU ℓ f K 3) (i : Fin 3) (w : unitarySU ℓ f K 3) :
    twLayerProd ρ x * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (twLayerProd ρ x)⁻¹ =
      ((ρ i (x i) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
          ((ρ i (x i) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)⁻¹ := by
  have hmem : ∀ (j : Fin 3) (y : unitarySU ℓ f K 3),
      ((ρ j y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ L j := fun j y => by
    rw [← hρ j]
    exact ⟨_, ⟨y, rfl⟩, rfl⟩
  fin_cases i
  · exact twDec_prod_conj₀ (hcomm 1 0 (by decide) _ (hmem 1 _) _ (hmem 0 w))
      (hcomm 2 0 (by decide) _ (hmem 2 _) _ (hmem 0 w))
  · exact twDec_prod_conj₁ (hcomm 0 1 (by decide) _ (hmem 0 _) _ (hmem 1 _))
      (hcomm 0 1 (by decide) _ (hmem 0 _) _ (hmem 1 w))
      (hcomm 2 1 (by decide) _ (hmem 2 _) _ (hmem 1 w))
  · exact twDec_prod_conj₂ (hcomm 0 2 (by decide) _ (hmem 0 _) _ (hmem 2 _))
      (hcomm 0 2 (by decide) _ (hmem 0 _) _ (hmem 2 w))
      (hcomm 1 2 (by decide) _ (hmem 1 _) _ (hmem 2 _))
      (hcomm 1 2 (by decide) _ (hmem 1 _) _ (hmem 2 w))

theorem twDec_of_aut (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    {s : twistedE6RootGroup K σ} (hs : (s : ModGL TwistTag.E6.tag K) = h₀)
    {ε : MulAut (twistedE6RootGroup K σ)} (hε : ε ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hcomm : ε * MulAut.conj s = MulAut.conj s * ε)
    (hrange : ∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range) :
    ∃ ĝ ∈ twistedE6InndiagGL K σ,
      (∀ c : twistedE6RootGroup K σ,
        ((ε c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * (c : ModGL _ K) * ĝ⁻¹) ∧
        ĝ * h₀ = h₀ * ĝ ∧ ∀ i, ∀ l ∈ L i, ĝ⁻¹ * l * ĝ ∈ L i := by
  rw [← range_twistedE6InndiagConj] at hε
  obtain ⟨g, rfl⟩ := hε
  refine ⟨g, g.2, fun c => twistedE6InndiagConj_apply g c, ?_, ?_⟩
  · have h1 := twInndiag_commute hℓ hf hK hσ hcomm
    rw [hs] at h1
    exact h1
  · intro i l hl
    rw [← hρ i] at hl
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hl
    have hx : (ρ i x) ∈ (ρ i).range.map (twistedE6InndiagConj K σ g).toMonoidHom := by
      rw [hrange i]
      exact ⟨x, rfl⟩
    obtain ⟨y, ⟨x', rfl⟩, hy⟩ := hx
    have hy' := congrArg (fun z : twistedE6RootGroup K σ => (z : ModGL TwistTag.E6.tag K)) hy
    simp only [MulEquiv.coe_toMonoidHom, twistedE6InndiagConj_apply] at hy'
    have hmem : ((ρ i x' : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ L i := by
      rw [← hρ i]
      exact ⟨_, ⟨x', rfl⟩, rfl⟩
    simp only [Subgroup.subtype_apply]
    rw [← hy']
    have e : (g : ModGL TwistTag.E6.tag K)⁻¹ * ((g : ModGL TwistTag.E6.tag K) *
        ((ρ i x' : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
          (g : ModGL TwistTag.E6.tag K)⁻¹) * (g : ModGL TwistTag.E6.tag K) =
        ((ρ i x' : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
      group
    rw [e]
    exact hmem

theorem twTorusModel_of_certs {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (h3c : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
    (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) :
    ∃ (ℓ f : ℕ) (h : UnitaryFieldData ℓ f K)
      (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ),
      ℓ ^ f = q ∧ TwLayerAct K σ h₀ L h ρ ∧ TwTorusAct K σ h₀ T h ρ := by
  classical
  obtain ⟨q', Fr, g₀, pic⟩ := hl.picture
  obtain ⟨ℓ, f, hU, rfl⟩ := CFSG.GH74.Generic.S1.rcard_exists_unitaryFieldData hK
  have hq' : q' = ℓ ^ f := by
    have h1 := pic.card_eq
    rw [hK] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  subst hq'
  have hℓ : ℓ.Prime := hU.prime
  have hf : 1 ≤ f := hU.one_le
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hU.charP
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ3 : ℓ ≠ 3 := by
    intro h3'
    apply h3c
    rw [ringChar.eq K ℓ, h3']
  have hq1 : ℓ ^ f % 3 = 2 := by omega
  haveI : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  haveI : IsAlgClosure (fixSubfield σ) (AlgebraicClosure K) :=
    IsAlgClosure.ofAlgebraic (fixSubfield σ) K (AlgebraicClosure K)
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  choose Φ Hc hΘ hFix using fun i : Fin 3 =>
    twFrame_theta (Ω := AlgebraicClosure K) hf hkc pic.Fr_apply i
  have F : TwFrameFacts ℓ f Fr Φ Hc := ⟨hΘ, hFix⟩
  choose ρ hρ using fun i : Fin 3 => exists_twRho hU pic hl.L_le F i
  have hinj : ∀ i, Function.Injective (ρ i) := fun i => twRho_injective hU (hρ i)
  have hρL : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i :=
    fun i => twRho_range hU pic F (hρ i)
  have hex : ∀ (i : Fin 3), ∀ τ ∈ twTorusHat K σ g₀,
      ∃ (γ : primeFormUnitary hU (idGram K 3)) (d : Fin 3 → (AlgebraicClosure K)ˣ),
        (∀ X, twLinePsi K g₀ τ * twFrame (AlgebraicClosure K) i X * (twLinePsi K g₀ τ)⁻¹ =
          twFrame (AlgebraicClosure K) i (conjDiag3 d X)) ∧
          TwDiagRealizes (Hc i) d (γ : GL (Fin 3) K) := by
    intro i τ hτ
    obtain ⟨hτC, hτH⟩ := mem_twTorusHat.1 hτ
    obtain ⟨-, hθ⟩ := twLinePsi_inndiag hℓ hf pic hτC
    exact F.exists_realizes hU hℓ3 hq1 i hτH hθ
  choose! A hA using hex
  have hact : ∀ i, ∀ τ ∈ twTorusHat K σ g₀, ∀ w : unitarySU ℓ f K 3,
      τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
        ((ρ i (conjSU hU (A i τ) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
    intro i τ hτ w
    obtain ⟨d, hd, hreal⟩ := hA i τ hτ
    apply twLinePsi_injective K g₀
    rw [map_mul, map_mul, map_inv, hρ i w, hρ i (conjSU hU (A i τ) w)]
    exact TwFrameFacts.act hU i hd hreal w
  have hAcomm : ∀ i, ∀ τ ∈ twTorusHat K σ g₀, ∀ τ' ∈ twTorusHat K σ g₀,
      A i τ * A i τ' = A i τ' * A i τ := by
    intro i τ hτ τ' hτ'
    obtain ⟨d, -, hreal⟩ := hA i τ hτ
    obtain ⟨d', -, hreal'⟩ := hA i τ' hτ'
    exact Subtype.ext (hreal.commute hreal')
  refine ⟨ℓ, f, hU, ρ, rfl, ⟨hinj, hρL, ?_⟩, ⟨twTorusHat K σ g₀, A, ?_, twTorusHat_comm,
    hAcomm, hact, ?_⟩⟩
  ·
    intro s hs ε hε hcomm hrange i
    obtain ⟨ĝ, hĝ, hεĝ, hĝcomm, hnorm⟩ := twDec_of_aut hℓ hf hK hσ hρL hs hε hcomm hrange
    obtain ⟨τ, hτ, x, hx⟩ := twDec_decomp hℓ hf hl pic hρL hĝ hĝcomm hnorm
    refine ⟨A i τ * ⟨x i, unitarySU_le_primeFormUnitary hU (x i).2⟩, fun w => ?_⟩
    apply Subtype.ext
    rw [hεĝ, hx, twConjSU_mul, ← hact i τ hτ]
    have e : τ * twLayerProd ρ x * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (τ * twLayerProd ρ x)⁻¹ = τ * (twLayerProd ρ x *
          ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
            (twLayerProd ρ x)⁻¹) * τ⁻¹ := by
      group
    rw [e, twDec_layerProd_conj hl.L_commute hρL x i w]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  ·
    intro x hx
    exact mem_twTorusHat.2 ⟨twRootGroup_le_inndiagGL (hl.T_le hx), ((pic.mem_T x).1 hx).2⟩
  ·
    intro s hs ε hε hcomm hrange
    obtain ⟨ĝ, hĝ, hεĝ, hĝcomm, hnorm⟩ := twDec_of_aut hℓ hf hK hσ hρL hs hε hcomm hrange
    obtain ⟨τ, hτ, x, hx⟩ := twDec_decomp hℓ hf hl pic hρL hĝ hĝcomm hnorm
    exact ⟨τ, hτ, x, fun c => by rw [hεĝ c, hx]⟩

end Model

section Final

set_option linter.unusedSectionVars false


theorem twTorusModel_holds : TwTorusModel := by
  intro K _ _ σ q h3c hσ hK h3 hq2 h₀ L T n hl
  exact twTorusModel_of_certs σ q h3c hσ hK h3 hq2 h₀ L T n hl

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
