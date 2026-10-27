module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyParity
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToralBasic
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.GapsOrthExcl
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.LieType.Steinberg.CentralExt.UnitaryLift
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Universal.Spin
open scoped commutatorElement MatrixGroups

section Lift

variable {p e : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]
  {KY X : Type} [Group KY] [Finite KY] [Group X]

theorem exists_uni_of_map (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ e) ^ 2) (hq : 5 ≤ p ^ e)
    (ψ : KY →* X) (hker : ψ.ker ≤ Subgroup.center KY) (hker2 : ∀ x ∈ ψ.ker, x * x = 1)
    {R₁ R₂ : Subgroup KY} (hR₁ : ⁅R₁, R₁⁆ = R₁) (hR₂ : ⁅R₂, R₂⁆ = R₂)
    (h : ∃ W, UnitaryBlockStandardPair K p e W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, UnitaryBlockStandardPair K p e W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  have hq2 : p ^ e ≠ 2 := by omega
  have hWsup := CFSG.ClassicalInvolution.RouteD.typeU_standardPair_eq_sup hK hq2 hW
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : Su K p e 3 →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπ2 : IsPGroup 2 ψ.rangeRestrict.ker := by
    intro g
    refine ⟨1, ?_⟩
    have := hker2 g (by rw [← MonoidHom.ker_rangeRestrict]; exact g.2)
    simpa [pow_two] using Subtype.ext this
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := p) (f := e) hK 3
  let ε := CFSG.LieType.Universal.Unitary.conjEquiv P hP
  obtain ⟨β, hβ⟩ := CFSG.LieType.Steinberg.exists_lift_SU_three hK hp2 hπ hπker hπ2
    (θ'.comp ε.toMonoidHom)
  let β' : Su K p e 3 →* KY := β.comp ε.symm.toMonoidHom
  have hψβ : ∀ s, ψ (β' s) = θ s := by
    intro s
    have h1 := DFunLike.congr_fun hβ (ε.symm s)
    have := congrArg Subtype.val h1
    simpa [β', θ'] using this
  have hψ : ψ.comp β' = θ := MonoidHom.ext hψβ
  have hperf : ∀ B : Subgroup (Su K p e 3), B ≤ ⁅B, B⁆ → ⁅B.map β', B.map β'⁆ = B.map β' :=
    fun B hB => by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map β') (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
        B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha)) (B.inv_mem hb)) hB)
  have hB12 : (B12 K p e).map β' = R₁ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker
      (hperf _ (CFSG.ClassicalInvolution.RouteD.B12_perfect_su hK hq)) hR₁
      (by rw [Subgroup.map_map, hψ, hU])
  have hB23 : (B23 K p e).map β' = R₂ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker
      (hperf _ (CFSG.ClassicalInvolution.RouteD.B23_perfect_su hK hq)) hR₂
      (by rw [Subgroup.map_map, hψ, hV])
  have hid : (MulAut.conj (1 : Su K p e 3)⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  refine ⟨β'.range, β', 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hψβ, MonoidHom.mem_ker.mp hs, map_one]
  · rw [hid, Subgroup.map_id, hB12]
  · rw [hid, Subgroup.map_id, hB23]

end Lift

section Abstract

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}

structure SpinCtx (p e : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (GaloisField p e) V] [FiniteDimensional (GaloisField p e) V]
    (Q : QuadraticForm (GaloisField p e) V) (𝔉 : Set (Subgroup (spinGroup Q))) : Prop where
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ e
  hQ : (polarBilin Q).Nondegenerate
  fin : Finite (spinGroup Q)
  hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1
  hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup Q))
  perf : ∀ R ∈ 𝔉, ⁅R, R⁆ = R
  inj : ∀ R ∈ 𝔉, ∀ r ∈ R, spinAction Q r = 1 → r = 1
  map : ∀ R ∈ 𝔉, ∃ i, IsFundamental Q (R.map (spinAction Q)) i

namespace SpinCtx

variable {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx p e Q 𝔉)

include S

theorem odd_card : Odd (Nat.card (GaloisField p e)) :=
  (odd_and_five_le_card_galoisField S.hp2 S.hq).1

theorem one_le : 1 ≤ e := by
  rcases Nat.eq_zero_or_pos e with rfl | h
  · have := S.hq
    simp at this
  · exact h

theorem card_eq : Nat.card (GaloisField p e) = p ^ e :=
  GaloisField.card p e (by have := S.one_le; omega)

theorem card_eq' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
  card_galoisField_two_mul p e S.one_le

theorem four_le : 4 ≤ Nat.card (GaloisField p e) := by
  have := (odd_and_five_le_card_galoisField S.hp2 S.hq).2
  omega

theorem perf_le {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) : ⁅R, R⁆ = R := S.perf R hR

theorem eq_of_map_eq {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : R₁.map (spinAction Q) = R₂.map (spinAction Q)) : R₁ = R₂ :=
  ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) (ker_spinAction_le_center Q)
    (S.perf_le h₁) (S.perf_le h₂) h

theorem commutes_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉)
    (h : Commutes (R₁.map (spinAction Q)) (R₂.map (spinAction Q))) : Commutes R₁ R₂ :=
  RouteD.Gaps.commutes_of_map_commutes (ker_spinAction_le_center Q) (S.perf_le h₁) h

theorem linear_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map (spinAction Q))
      (R₂.map (spinAction Q))) : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  have := S.fin
  exact RouteD.Gaps.exists_lin_of_map S.four_le S.hC (spinAction Q) (ker_spinAction_le_center Q)
    (S.perf_le h₁) (S.perf_le h₂) h

theorem unitary_of_map {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (h : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map (spinAction Q))
      (R₂.map (spinAction Q))) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have := S.fin
  exact exists_uni_of_map S.hp2 S.card_eq' S.hq (spinAction Q) (ker_spinAction_le_center Q)
    S.hker2 (S.perf_le h₁) (S.perf_le h₂) h

theorem map_eq_of_orderOf {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) {c : spinGroup Q}
    (hcR : c ∈ R) (ho : orderOf c = 2) {i : _ ≃ₗ[GaloisField p e] _}
    (hI : IsFundamental Q (R.map (spinAction Q)) i) : spinAction Q c = i := by
  have h2' : spinAction Q c ^ 2 = 1 := by
    rw [← map_pow, ← ho, pow_orderOf_eq_one, map_one]
  have h1 : spinAction Q c ≠ 1 := fun h1 => by
    have := S.inj R hR c hcR h1
    rw [this, orderOf_one] at ho
    omega
  exact hI.eq_of_orderOf_eq_two S.odd_card ⟨c, hcR, rfl⟩ (orderOf_eq_prime h2' h1)

theorem mem_normalizer {R₁ R₂ : Subgroup (spinGroup Q)} {c₁ c₂ : spinGroup Q}
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁)
    {i₁ i₂ : _ ≃ₗ[GaloisField p e] _}
    (hI₁ : IsFundamental Q (R₁.map (spinAction Q)) i₁)
    (hI₂ : IsFundamental Q (R₂.map (spinAction Q)) i₂) (e₁ : spinAction Q c₁ = i₁)
    (e₂ : spinAction Q c₂ = i₂) (hcπ : i₁ * i₂ = i₂ * i₁) :
    i₂ ∈ Subgroup.normalizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  have hsq : ∀ c : spinGroup Q, orderOf c = 2 → c * c = 1 := fun c hc => by
    rw [← pow_two]
    exact hc ▸ pow_orderOf_eq_one c
  have hfin : ∀ {L : Subgroup (V ≃ₗ[GaloisField p e] V)} {i : V ≃ₗ[GaloisField p e] V},
      IsFundamental Q L i → Module.finrank (GaloisField p e) (minusSp i) = 4 := by
    rintro L i ⟨Fr, -, rfl⟩
    exact (congrArg (fun W : Submodule (GaloisField p e) V => Module.finrank (GaloisField p e) W)
      (negSpace_La_neg_one h2 Fr)).trans (Frame.finrank_span Fr)
  have hii₁ : spinAction Q c₁ * spinAction Q c₁ = 1 := by
    rw [← map_mul, hsq c₁ ho₁, map_one]
  have hii₂ : spinAction Q c₂ * spinAction Q c₂ = 1 := by
    rw [← map_mul, hsq c₂ ho₂, map_one]
  have he₁ : Even (Module.finrank (GaloisField p e) (minusSp (spinAction Q c₁))) := by
    rw [e₁, hfin hI₁]
    exact ⟨2, rfl⟩
  have he₂ : Even (Module.finrank (GaloisField p e) (minusSp (spinAction Q c₂))) := by
    rw [e₂, hfin hI₂]
    exact ⟨2, rfl⟩
  have hpar := even_finrank_inf_minusSp_of_spin_commute S.hQ hc hii₁ hii₂ he₁ he₂
  rw [e₁, e₂] at hpar
  exact (mem_normalizer_iff_even S.odd_card hI₁ hI₂ hcπ).mpr hpar

end SpinCtx

theorem SpinCtx.dichotomy {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx p e Q 𝔉)
    {R₁ R₂ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) {c₁ c₂ : spinGroup Q}
    (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2)
    (hc : c₁ * c₂ = c₂ * c₁) :
    R₁ = R₂ ∨ Commutes R₁ R₂ ∨ (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have hodd := S.odd_card
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  have e₁ := S.map_eq_of_orderOf h₁ hc₁ ho₁ hI₁
  have e₂ := S.map_eq_of_orderOf h₂ hc₂ ho₂ hI₂
  have hcπ : i₁ * i₂ = i₂ * i₁ := by
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hL : R₁.map (spinAction Q) = R₂.map (spinAction Q)
  · exact Or.inl (S.eq_of_map_eq h₁ h₂ hL)
  · right
    by_cases hii : i₁ = i₂
    · left
      obtain ⟨L', hL', hne', hcomm', huniq⟩ := hI₁.exists_twin hodd
      have hL₂ : R₂.map (spinAction Q) = L' := by
        rcases huniq (R₂.map (spinAction Q)) (by rw [hii]; exact hI₂) with h | h
        · exact absurd h.symm hL
        · exact h
      exact S.commutes_of_map h₁ (by rw [hL₂]; exact hcomm')
    · have hcc := IsFundamental.commute_iff hodd hI₁ hI₂ hcπ hL
      by_cases hcent : i₂ ∈ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _)
      · left
        exact S.commutes_of_map h₁ (hcc.mpr hcent)
      · right
        have hN := S.mem_normalizer ho₁ ho₂ hc hI₁ hI₂ e₁ e₂ hcπ
        rcases (lemma_6_10_dichotomy S.card_eq S.card_eq' hodd hI₁ hI₂ hcπ hN hcent).2 with
          ⟨-, hlin⟩ | ⟨-, huni⟩
        · exact Or.inl (S.linear_of_map h₁ h₂ ⟨_, hlin⟩)
        · exact Or.inr (S.unitary_of_map h₁ h₂ ⟨_, huni⟩)

theorem SpinCtx.sign {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx p e Q 𝔉)
    {R₁ R₂ R₃ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    {c₁ c₂ c₃ : spinGroup Q} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂) (hc₃ : c₃ ∈ R₃)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (ho₃ : orderOf c₃ = 2)
    (h₁₂ : c₁ * c₂ = c₂ * c₁) (h₃₂ : c₃ * c₂ = c₂ * c₃) (h₁₃ : c₁ * c₃ = c₃ * c₁)
    (hR₁₃ : Commutes R₁ R₃) (hne₁₂ : R₁ ≠ R₂) (hne₃₂ : R₃ ≠ R₂) (hnc₁₂ : ¬ Commutes R₁ R₂)
    (hnc₃₂ : ¬ Commutes R₃ R₂) :
    ((∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R₃) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₂ R₃) := by
  have hodd := S.odd_card
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  obtain ⟨i₃, hI₃⟩ := S.map R₃ h₃
  have e₁ := S.map_eq_of_orderOf h₁ hc₁ ho₁ hI₁
  have e₂ := S.map_eq_of_orderOf h₂ hc₂ ho₂ hI₂
  have e₃ := S.map_eq_of_orderOf h₃ hc₃ ho₃ hI₃
  have k₁₂ : i₁ * i₂ = i₂ * i₁ := by rw [← e₁, ← e₂, ← map_mul, ← map_mul, h₁₂]
  have k₃₂ : i₃ * i₂ = i₂ * i₃ := by rw [← e₃, ← e₂, ← map_mul, ← map_mul, h₃₂]
  have k₁₃ : i₁ * i₃ = i₃ * i₁ := by rw [← e₁, ← e₃, ← map_mul, ← map_mul, h₁₃]
  have hL : ∀ x ∈ R₁.map (spinAction Q), ∀ y ∈ R₃.map (spinAction Q), x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hR₁₃ x hx y hy]
  have hN₁ := S.mem_normalizer ho₁ ho₂ h₁₂ hI₁ hI₂ e₁ e₂ k₁₂
  have hN₃ := S.mem_normalizer ho₃ ho₂ h₃₂ hI₃ hI₂ e₃ e₂ k₃₂
  have hL₁₂ : R₁.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    hne₁₂ (S.eq_of_map_eq h₁ h₂ h)
  have hL₃₂ : R₃.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    hne₃₂ (S.eq_of_map_eq h₃ h₂ h)
  have hC₁ : i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hc => hnc₁₂ (S.commutes_of_map h₁
      ((IsFundamental.commute_iff hodd hI₁ hI₂ k₁₂ hL₁₂).mpr hc))
  have hC₃ : i₂ ∉ Subgroup.centralizer ((R₃.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hc => hnc₃₂ (S.commutes_of_map h₃
      ((IsFundamental.commute_iff hodd hI₃ hI₂ k₃₂ hL₃₂).mpr hc))
  rcases lemma_6_11_signs S.card_eq S.card_eq' hodd hI₁ hI₂ hI₃ k₁₂ k₃₂ k₁₃ hL hN₁ hN₃ hC₁ hC₃ with
    ⟨-, -, hl₁, hl₃⟩ | ⟨-, -, hu₁, hu₃⟩
  · exact Or.inl ⟨S.linear_of_map h₁ h₂ ⟨_, hl₁⟩, S.linear_of_map h₂ h₃ ⟨_, hl₃⟩⟩
  · exact Or.inr ⟨S.unitary_of_map h₁ h₂ ⟨_, hu₁⟩, S.unitary_of_map h₂ h₃ ⟨_, hu₃⟩⟩

theorem false_of_linear_of_unitary {p e : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {U V : Subgroup X} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hl : ∃ W, LinearBlockStandardPair (GaloisField p e) W U V)
    (hu : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W U V) : False := by
  obtain ⟨W₀, hl⟩ := hl
  obtain ⟨W₁, hu⟩ := hu
  have hodd := (odd_and_five_le_card_galoisField hp2 hq).1
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hc : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hc' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
  have hq2 : p ^ e ≠ 2 := by omega
  have e1 := RouteD.Gaps.linear_eq_sup hl
  have e2 := RouteD.Gaps.unitary_eq_sup hc' hq2 hu
  rw [e1] at hl
  rw [e2] at hu
  exact RouteD.Gaps.not_linear_and_unitary hc hc' hodd hl hu

theorem SpinCtx.sign_linear {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx p e Q 𝔉)
    {R₁ R₂ R₃ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    {c₁ c₂ c₃ : spinGroup Q} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂) (hc₃ : c₃ ∈ R₃)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (ho₃ : orderOf c₃ = 2)
    (h₁₂ : c₁ * c₂ = c₂ * c₁) (h₃₂ : c₃ * c₂ = c₂ * c₃) (h₁₃ : c₁ * c₃ = c₃ * c₁)
    (hR₁₃ : Commutes R₁ R₃) (hne₁₂ : R₁ ≠ R₂) (hne₃₂ : R₃ ≠ R₂) (hnc₁₂ : ¬ Commutes R₁ R₂)
    (hnc₃₂ : ¬ Commutes R₃ R₂) (hlin : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) :
    ∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R₃ := by
  rcases S.sign h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂ with
    ⟨-, h⟩ | ⟨⟨W, hu⟩, -⟩
  · exact h
  · exact (false_of_linear_of_unitary S.hp2 S.hq hlin ⟨_, hu⟩).elim

end Abstract

section Tags

variable {p : ℕ} [Fact p.Prime]

theorem spinCtx_pOmegaPlus {n e : ℕ} (hn : 4 ≤ n) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    SpinCtx p e (quadPlus n (GaloisField p e))
      (longestFundamental (plusDatum n (GaloisField p e) (by omega))) := by
  have hm3 : 3 ≤ n := by omega
  have hCQ := RouteD.Gaps.centralQuot_plus (p := p) (f := e) hp2 hn hm3 hq
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n (GaloisField p e))) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  exact
    { hp2 := hp2, hq := hq, hQ := nondegenerate_polarBilin_quadPlus n (GaloisField p e),
      fin := inferInstance, hker2 := OrthAut.plus_hker2 n,
      hC := RouteD.Gaps.not_dvd_card_center_plus hp2 hm3,
      perf := fun R hR => hCQ.perf R (longestFundamental_subset .POmegaPlus _ hR),
      inj := fun R hR => hCQ.inj R (longestFundamental_subset .POmegaPlus _ hR),
      map := fun R hR => hCQ.map_mem R (longestFundamental_subset .POmegaPlus _ hR) }

theorem spinCtx_pOmegaOdd {n e : ℕ} (hm3 : 3 ≤ n) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    SpinCtx p e (quadOdd n (GaloisField p e))
      (longestFundamental (oddDatum n (GaloisField p e))) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have hCQ := RouteD.Gaps.centralQuot_odd (p := p) (f := e) hp2 hm3 hq
  have : Finite (spinGroup (quadOdd n (GaloisField p e))) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  exact
    { hp2 := hp2, hq := hq, hQ := nondegenerate_polarBilin_quadOdd n (GaloisField p e) h2,
      fin := inferInstance, hker2 := OrthAut.odd_hker2 h2 n,
      hC := RouteD.Gaps.not_dvd_card_center_odd hp2 hm3,
      perf := fun R hR => hCQ.perf R (longestFundamental_subset .POmegaOdd _ hR),
      inj := fun R hR => hCQ.inj R (longestFundamental_subset .POmegaOdd _ hR),
      map := fun R hR => hCQ.map_mem R (longestFundamental_subset .POmegaOdd _ hR) }

theorem spinCtx_pOmegaMinus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    SpinCtx p e (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2)
      (longestFundamental (Spin.Twisted.minusDatum n (minusCoeffs_irr p e))) := by
  have hn : 4 ≤ n := hadm.2.2
  have hirr := minusCoeffs_irr p e
  have hY := RouteD.yData_minus (p := p) (f := e) hn hp2 hadm (by omega)
  have hF := RouteD.Exotic.fundCorr_minus (p := p) (f := e) hp2 hq hadm
  have : Finite (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hker := ker_spinAction_le_center
    (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2)
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadMinus n (GaloisField p e)
      (minusCoeffs p e).1 (minusCoeffs p e).2))) := by
    intro hdvd
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hζp : (ζ : spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one ζ
      rw [hζ] at h1
      simpa using congrArg (fun x : Subgroup.center (spinGroup (quadMinus n (GaloisField p e)
        (minusCoeffs p e).1 (minusCoeffs p e).2)) => (x : spinGroup (quadMinus n (GaloisField p e)
          (minusCoeffs p e).1 (minusCoeffs p e).2))) h1
    have h1 := (OrthAut.minus_center_facts hirr hp2 hn).1 _ ζ.2 hζp
    have h0 : ζ = 1 := Subtype.ext h1
    rw [h0, orderOf_one] at hζ
    exact (Fact.out : p.Prime).one_lt.ne hζ
  exact
    { hp2 := hp2, hq := hq,
      hQ := nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p e) hirr,
      fin := inferInstance, hker2 := OrthAut.minus_hker2 hirr, hC := hC,
      perf := fun R hR => le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
        R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb))
        (hY.perfR R (longestFundamental_subset .POmegaMinus _ hR)),
      inj := fun R hR r hr h1 => hY.central R (longestFundamental_subset .POmegaMinus _ hR) r hr
        (hker (MonoidHom.mem_ker.mpr h1)),
      map := fun R hR => hF.1 R (longestFundamental_subset .POmegaMinus _ hR) }

theorem standardPairDichotomy_pOmegaPlus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    StandardPairDichotomy p .POmegaPlus n e := by
  have hn : 4 ≤ n := hadm.2.2
  unfold StandardPairDichotomy
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := e) (by omega : 3 ≤ n)]
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx_pOmegaPlus hn hp2 hq).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

theorem standardPairDichotomy_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    StandardPairDichotomy p .POmegaOdd n e := by
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx_pOmegaOdd hadm.2.2.1 hp2 hq).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

theorem standardPairDichotomy_pOmegaMinus {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : StandardPairDichotomy p .POmegaMinus n e := by
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx_pOmegaMinus hadm hp2 hq).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

end Tags

end CFSG.ClassicalInvolution.ModelFacts
