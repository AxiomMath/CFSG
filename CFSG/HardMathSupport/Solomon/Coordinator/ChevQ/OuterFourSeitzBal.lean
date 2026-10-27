module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridge
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightUniform
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightField
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalD4Eight
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux
open CFSG.HardMathSupport.Lang.D4Three (d4Graph d4P coe_d4Graph)
open scoped commutatorElement

section Semilin

set_option linter.unusedSectionVars false


open CFSG.HardMathSupport.Dickson.Bal207
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {F : Type} [Field F] [Finite F]

theorem exactNormalAut_D4_eq_mul (a : Fin Tag.D4.rank → Fˣ) (σ : F ≃+* F) :
    exactNormalAut Tag.D4 F a σ 0 =
      exactNormalAut Tag.D4 F a 1 0 * entrywiseAdjointAut Tag.D4 σ := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_exactNormalAut, coe_exactNormalAut, coe_entrywiseAdjointAut,
    CFSG.HardMathSupport.Lang.E6Descent.exactQ_D4]
  have hid : Units.map (entrywiseHom (1 : F ≃+* F).toRingHom)
      (Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 F)) =
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 F) :=
    Units.ext (entrywise_id _)
  rw [hid]

theorem entrywiseAdjointAut_D4_eq (σ : F ≃+* F) :
    entrywiseAdjointAut Tag.D4 σ = exactNormalAut Tag.D4 F 1 σ 0 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_entrywiseAdjointAut, coe_exactNormalAut, rootDiagUnit_one,
    CFSG.HardMathSupport.Lang.E6Descent.exactQ_D4]
  simp only [one_mul, mul_one, inv_one]

theorem congr_conj_mem {F₀ : Type} [Field F₀]
    (ψ : ↥(adjointGroup Tag.D4 F) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F₀))
    (g : ↥(adjointGroup Tag.D4 F)) :
    MulAut.congr ψ (MulAut.conj g) ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
  rw [mulAut_congr_conj]
  exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _

theorem congr_entrywise_mem (hF : Nat.card F = 8) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 8)
    (ψ : ↥(adjointGroup Tag.D4 F) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F₀))
    {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) :
    MulAut.congr ψ (entrywiseAdjointAut Tag.D4 σ) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
  have h1 : SemilinD4EightAut ↥(adjointGroup Tag.D4 F) (entrywiseAdjointAut Tag.D4 σ) :=
    ⟨F, inferInstance, inferInstance, (D4Graph.isoAdj F).symm, hF,
      D4Graph.congr_entrywiseAdjointAut_mem σ⟩
  refine h1.mulAut_congr_mem_image ?_ hF₀ ψ
  rw [← entrywiseAdjointAut_pow, hσ3, entrywiseAdjointAut_one]

theorem ringChar_eq_two_of_card (hF : Nat.card F = 2 ^ 3) : ringChar F = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3) (by norm_num) hF
  exact ringChar.eq F 2

theorem congr_exactNormalAut_mem (hF : Nat.card F = 2 ^ 3) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 8)
    (ψ : ↥(adjointGroup Tag.D4 F) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F₀))
    (a : Fin Tag.D4.rank → Fˣ) {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) :
    MulAut.congr ψ (exactNormalAut Tag.D4 F a σ 0) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
  obtain ⟨d, hd⟩ := CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
    (ringChar_eq_two_of_card hF) a
  rw [exactNormalAut_D4_eq_mul, hd, map_mul]
  exact mul_mem (congr_conj_mem ψ d) (congr_entrywise_mem (by rw [hF]; norm_num) hF₀ ψ hσ3)

theorem d4Graph_pow_three (ε : ℕ) : d4Graph F ε ^ 3 = 1 := by
  rw [pow_three, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_mod_three,
    show (ε + (ε + ε)) % 3 = 0 by omega, CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero]

theorem fixSubgroup_d4Graph_eq {ε : ℕ} (hε : ε = 1 ∨ ε = 2) :
    fixSubgroup (d4Graph F ε) = fixSubgroup (d4Graph F 1) := by
  rcases hε with rfl | rfl
  · rfl
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_d4Graph_two

noncomputable def fixSubgroupD4GraphEquivG2 (hF : Nat.card F = 2 ^ 3) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2) : ↥(fixSubgroup (d4Graph F ε)) ≃* ↥(adjointGroup Tag.G2 F) :=
  (MulEquiv.subgroupCongr (fixSubgroup_d4Graph_eq hε)).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 F
      (by rw [hF]; norm_num))

theorem card_fixSubgroup_d4Graph (hF : Nat.card F = 2 ^ 3) {ε : ℕ} (hε : ε = 1 ∨ ε = 2) :
    Nat.card ↥(fixSubgroup (d4Graph F ε)) = ordG2 8 := by
  rw [Nat.card_congr (fixSubgroupD4GraphEquivG2 hF hε).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
  norm_num

theorem card_adjointGroup_D4_eight (hF : Nat.card F = 2 ^ 3) :
    Nat.card ↥(adjointGroup Tag.D4 F) = ordD 4 (2 ^ 3) := by
  have hm : StatedClassicalModel ↥(adjointGroup Tag.D4 F) .POmegaPlus 4 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, le_rfl⟩, F, inferInstance, inferInstance, hF,
      ⟨(D4Graph.isoAdj F).symm⟩⟩
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl

theorem d4Graph_not_inner (hF : Nat.card F = 2 ^ 3) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (c : ↥(adjointGroup Tag.D4 F)) : MulAut.conj c ≠ d4Graph F ε := by
  intro hc
  have hcfix : c ∈ fixSubgroup (d4Graph F ε) := by
    rw [mem_fixSubgroup, ← hc, MulAut.conj_apply, mul_inv_cancel_right]
  have hZ : (⟨c, hcfix⟩ : fixSubgroup (d4Graph F ε)) ∈
      Subgroup.center ↥(fixSubgroup (d4Graph F ε)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have hu : (MulAut.conj c) (u : ↥(adjointGroup Tag.D4 F)) = u := by
      rw [hc]; exact u.2
    rw [MulAut.conj_apply] at hu
    show (u : ↥(adjointGroup Tag.D4 F)) * c = c * u
    calc (u : ↥(adjointGroup Tag.D4 F)) * c = c * u * c⁻¹ * c := by rw [hu]
      _ = c * u := by group
  have hZ0 : Subgroup.center ↥(fixSubgroup (d4Graph F ε)) = ⊥ :=
    D4FixedAux.center_eq_bot_of_mulEquiv (fixSubgroupD4GraphEquivG2 hF hε)
      center_adjointGroup_eq_bot
  rw [hZ0, Subgroup.mem_bot] at hZ
  have hc1 : c = 1 := congrArg Subtype.val hZ
  have htop : fixSubgroup (d4Graph F ε) = ⊤ := by
    rw [← hc, hc1, map_one]
    exact (Subgroup.eq_top_iff' _).2 fun x => rfl
  have h1 := card_fixSubgroup_d4Graph hF hε
  rw [htop, Subgroup.card_top, card_adjointGroup_D4_eight hF] at h1
  exact absurd h1 (by decide)

theorem d4Graph_not_semilin (hF : Nat.card F = 2 ^ 3) {ε : ℕ} (hε : ε = 1 ∨ ε = 2) :
    ¬ SemilinD4EightAut ↥(adjointGroup Tag.D4 F) (d4Graph F ε) := by
  rintro ⟨F₀, _, _, e₀, hF₀, hE⟩
  obtain ⟨-, J, hJ, -, hJm⟩ :=
    d4Eight_field_comps hF₀ e₀ (d4Graph_pow_three ε) (d4Graph_not_inner hF hε) hE
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.G2 F) :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card F (by rw [hF]; norm_num)
  have hq' : CFSG.Open.IsQuasisimple ↥(fixSubgroup (d4Graph F ε)) := by
    obtain ⟨hperf, hsimp, -⟩ :=
      CFSG.IsQuasisimple.of_mulEquiv (fixSubgroupD4GraphEquivG2 hF hε) hq
    exact ⟨hperf.commutator_eq_top, hsimp⟩
  have hcomp : CFSG.Open.IsComponentOf (fixSubgroup (d4Graph F ε)) (fixSubgroup (d4Graph F ε)) :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq'⟩
  have hJeq := hJ _ hcomp
  have hcJ := (CFSG.Timmesfeld.card_statedClassicalModel_two hJm).2.2.2.1 rfl
  rw [← hJeq, card_fixSubgroup_d4Graph hF hε] at hcJ
  exact absurd hcJ (by decide)

theorem not_semilin_of_graphNF (hF : Nat.card F = 2 ^ 3) {α : MulAut ↥(adjointGroup Tag.D4 F)}
    {g : ↥(adjointGroup Tag.D4 F)} {a : Fin Tag.D4.rank → Fˣ} {σ : F ≃+* F} {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε)) (h3 : α ^ 3 = 1) :
    ¬ SemilinD4EightAut ↥(adjointGroup Tag.D4 F) α := by
  rintro ⟨F₀, _, _, e₀, hF₀, hE⟩
  have hσ3 : σ ^ 3 = 1 := CFSG.HardMathSupport.Lang.E6Descent.cube_normal_form_sigma_cube (hα ▸ h3)
  set ψ := coordinatePlusWitnessEquiv F₀ e₀ with hψ
  have hN := congr_conj_mem ψ g
  have hM := congr_exactNormalAut_mem hF hF₀ ψ a hσ3
  have hγ : MulAut.congr ψ (d4Graph F ε) ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
    have e1 : d4Graph F ε = (exactNormalAut Tag.D4 F a σ 0)⁻¹ * (MulAut.conj g)⁻¹ * α := by
      rw [hα]; group
    rw [e1, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (mul_mem (inv_mem hM) (inv_mem hN)) hE
  exact d4Graph_not_semilin hF hε ⟨F₀, inferInstance, inferInstance, e₀, hF₀, hγ⟩

theorem congr_eq_of_graphAutD4_formula {S : Type} [Group S] {φ : MulAut S} {K₁ : Type} [Field K₁]
    (e : S ≃* ↥(adjointGroup Tag.D4 K₁)) {x : ↥(adjointGroup Tag.D4 K₁)}
    {a : Fin Tag.D4.rank → K₁ˣ} {σ : K₁ ≃+* K₁} {ε : ℕ}
    (hpt : ∀ h : ↥(adjointGroup Tag.D4 K₁), ∃ h' : ↥(adjointGroup Tag.D4 K₁),
      (h' : ModGL Tag.D4 K₁) =
        (MulAut.conj (x : ModGL Tag.D4 K₁) * (exactNormalAutGL Tag.D4 K₁ a σ 0 *
          MulAut.conj (d4PMat K₁ ^ ε))) (h : ModGL Tag.D4 K₁) ∧
        MulAut.congr e φ h = h') :
    MulAut.congr e φ = MulAut.conj x * (exactNormalAut Tag.D4 K₁ a σ 0 * d4Graph K₁ ε) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  obtain ⟨h', hh', he⟩ := hpt h
  rw [he, hh']
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, coe_d4Graph]
  rfl

theorem nonSemilin_of_graphAutD4 {S : Type} [Group S] {φ : MulAut S} (h3 : φ ^ 3 = 1)
    (hG : GraphAutD4 S φ) : ¬ SemilinD4EightAut S φ := by
  obtain ⟨K₁, _, _, e, x, a, σ, ε, hK₁, hε, hpt⟩ := hG
  have heq := congr_eq_of_graphAutD4_formula e hpt
  have h3' : MulAut.congr e φ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  intro hS
  exact not_semilin_of_graphNF hK₁ hε heq h3' (hS.of_mulEquiv e)

end Semilin


section Transfer

open scoped Pointwise

variable {X : Type} [Group X]

theorem le_sup_of_elemAbelian [Finite X] {K J S B E : Subgroup X} (hJK : J ≤ K)
    (hSJ : S ≤ Subgroup.normalizer (J : Set X)) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hcop : Nat.Coprime 3 (Nat.card S))
    (hE : IsElemAbelian 3 E) (hBE : B ≤ E) (hEY : E ≤ J ⊔ S ⊔ B) : E ≤ K ⊔ B := by
  have hJS : ((J ⊔ S : Subgroup X) : Set X) = (J : Set X) * (S : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left J S hSJ
  have hfwd : ∀ b ∈ B, ∀ n ∈ (J ⊔ S : Subgroup X), b * n * b⁻¹ ∈ (J ⊔ S : Subgroup X) := by
    intro b hb n hn
    have hn' : n ∈ (J : Set X) * (S : Set X) := hJS ▸ hn
    obtain ⟨j, hj, s, hs, rfl⟩ := hn'
    have hj' : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hBJ hb) j).1 hj
    have hs' : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hBS hb) s).1 hs
    have e1 : b * (j * s) * b⁻¹ = (b * j * b⁻¹) * (b * s * b⁻¹) := by group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_left hj') (Subgroup.mem_sup_right hs')
  have hBN : B ≤ Subgroup.normalizer ((J ⊔ S : Subgroup X) : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hfwd b hb n, fun h => ?_⟩
    have h1 := hfwd b⁻¹ (inv_mem hb) _ h
    rwa [show b⁻¹ * (b * n * b⁻¹) * b⁻¹⁻¹ = n by group] at h1
  have hY : ((J ⊔ S ⊔ B : Subgroup X) : Set X) = ((J ⊔ S : Subgroup X) : Set X) * (B : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (J ⊔ S) B hBN
  intro e he
  have he' : e ∈ ((J ⊔ S : Subgroup X) : Set X) * (B : Set X) := hY ▸ (hEY he)
  obtain ⟨n, hn, b, hb, rfl⟩ := he'
  have hnE : n ∈ E := by
    have h1 := mul_mem he (inv_mem (hBE hb))
    rwa [mul_inv_cancel_right] at h1
  have hn3 : n ^ 3 = 1 := hE.2 n hnE
  have hn' : n ∈ (J : Set X) * (S : Set X) := hJS ▸ hn
  obtain ⟨j, hj, s, hs, rfl⟩ := hn'
  have hs3 : s ^ 3 ∈ J := by
    have hsj1 : s * j * s⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hSJ hs) j).1 hj
    have hsj2 : s * s * j * (s * s)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.1 (hSJ (mul_mem hs hs)) j).1 hj
    have hn3' : j * s * (j * s) * (j * s) = 1 := by rw [← pow_three']; exact hn3
    have key : s ^ 3 = (s * s * j * (s * s)⁻¹)⁻¹ * (s * j * s⁻¹)⁻¹ * j⁻¹ *
        (j * s * (j * s) * (j * s)) := by group
    rw [key, hn3', mul_one]
    exact mul_mem (mul_mem (inv_mem hsj2) (inv_mem hsj1)) (inv_mem hj)
  have hcop' : Nat.Coprime 3 (orderOf s) := by
    have hdvd : orderOf s ∣ Nat.card S := by
      have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : S)
      rwa [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
  have hsJ : s ∈ J := hm ▸ pow_mem hs3 m
  exact mul_mem (Subgroup.mem_sup_left (hJK (mul_mem hj hsJ))) (Subgroup.mem_sup_right hb)

theorem sLOB_of_bal207Corr (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) [Finite X]
    (hKG : CFSG.Open.IsKGroup X) {K B : Subgroup X} {a : X} (hSC : IsSCp 3 (K ⊔ B) B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (ha : a ∈ B)
    (hJq : CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)))
    {P : TauCeti.LieTypeIndex → Prop}
    (hP : ∀ d, P d → Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d)
    (hJL : IsLieQuot ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) P) :
    B ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) ∧
      IsStronglyLocallyOneBalanced 3 B a (K ⊓ Subgroup.centralizer ({a} : Set X)) := by
  have hBel : IsElemAbelian 3 B := hSC.2.1
  set J := K ⊓ Subgroup.centralizer ({a} : Set X) with hJdef
  have hBJ : B ≤ Subgroup.normalizer (J : Set X) := fun b hb =>
    Bal209F4Aux.mem_normalizer_inf_centralizer (hBN hb) (hBN ha) (by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (Bal209F4Aux.commute_of_elemAbelian hBel hb ha)]
      exact Subgroup.one_mem _)
  refine ⟨hBJ, fun S hS hcop hBS' => ?_⟩
  have hSJ : S ≤ Subgroup.normalizer (J : Set X) := fun s hs => (Subgroup.mem_inf.1 (hS hs)).1
  have hBS : B ≤ Subgroup.normalizer (S : Set X) := fun b hb =>
    hBS' (Subgroup.mem_inf.2 ⟨hb, hBJ hb⟩)
  set Y := J ⊔ S ⊔ B with hYdef
  have hJY : J ≤ Y := le_sup_left.trans le_sup_left
  have hSY : S ≤ Y := le_sup_right.trans le_sup_left
  have hBY : B ≤ Y := le_sup_right
  have hYJ : Y ≤ Subgroup.normalizer (J : Set X) :=
    sup_le (sup_le Subgroup.le_normalizer hSJ) hBJ
  have hJn : (J.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).2 hYJ
  have hcomp : CFSG.Open.IsComponentOf (J.subgroupOf Y) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hJn.isSubnormal,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY) hJq⟩
  have hBel' : IsElemAbelian 3 (B.subgroupOf Y) :=
    SeitzHyperGoodInAux.isElemAbelian_comap_of_injective Y.subtype Subtype.val_injective hBel
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf Y) := by
    refine ⟨le_top, hBel', fun E _ hE hBE => ?_⟩
    have hE' : IsElemAbelian 3 (E.map Y.subtype) := CFSG.SectionRank.isElemAbelian_map hE Y.subtype
    have hBE' : B ≤ E.map Y.subtype := fun b hb =>
      Subgroup.mem_map.2 ⟨⟨b, hBY hb⟩, hBE (Subgroup.mem_subgroupOf.2 hb), rfl⟩
    have hEY : E.map Y.subtype ≤ J ⊔ S ⊔ B := Subgroup.map_subtype_le E
    have hEq : E.map Y.subtype = B :=
      hSC.2.2 _ (le_sup_of_elemAbelian inf_le_left hSJ hBJ hBS hcop hE' hBE' hEY) hE' hBE'
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : X) ∈ E.map Y.subtype := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rwa [hEq] at hx'
    · intro hx
      have hx' : (x : X) ∈ E.map Y.subtype := by rw [hEq]; exact hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx'
      have hzx' : z = x := Subtype.ext hzx
      rw [← hzx']
      exact hz
  have hBN' : B.subgroupOf Y ≤ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro b' hb'
    have hN := Subgroup.mem_normalizer_iff.1 (hBJ (Subgroup.mem_subgroupOf.1 hb'))
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hLie' : IsLieQuot ↥(J.subgroupOf Y) P :=
    Bal209F4Aux.isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY).symm hJL
  have hbal := CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr.of_index h207 (hKG.subgroup Y)
    Nat.prime_three (by decide) hcomp hSC' hBN' hP hLie'
  have hS'N : S.subgroupOf Y ≤ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro s' hs'
    have hN := Subgroup.mem_normalizer_iff.1 (hSJ (Subgroup.mem_subgroupOf.1 hs'))
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcard : Nat.Coprime 3 (Nat.card (S.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]
    exact hcop
  have hB'N' : B.subgroupOf Y ⊓ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.normalizer ((S.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro b' hb'
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hb').1
    have hN := Subgroup.mem_normalizer_iff.1 (hBS hbB)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcent := hbal (S.subgroupOf Y) hS'N hcard hB'N'
  refine Subgroup.commutator_le.2 (fun h hh s hs => ?_)
  have hcomm : h * s = s * h := by
    have hsY : (⟨s, hSY hs⟩ : ↥Y) ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.2 hs
    have hhY : (⟨h, hJY hh⟩ : ↥Y) ∈ J.subgroupOf Y := Subgroup.mem_subgroupOf.2 hh
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hcent hsY) _ hhY)
  rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  exact Subgroup.one_mem _

theorem not_isCyclic_pairSub_of {B : Subgroup X} {x y : X} (hxy : Commute x y)
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hx : x ∉ Subgroup.zpowers y) : ¬ IsCyclic ↥(Bal209F4Aux.pairSub hxy) := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hxA : x ∈ Bal209F4Aux.pairSub hxy := Bal209F4Aux.mem_pairSub.2 ⟨1, 0, by simp⟩
  have hyA : y ∈ Bal209F4Aux.pairSub hxy := Bal209F4Aux.mem_pairSub.2 ⟨0, 1, by simp⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hxA⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hyA⟩)
  have hxm : x = (g : X) ^ m := by
    have h1 := congrArg Subtype.val hm
    simpa using h1.symm
  have hyn : y = (g : X) ^ n := by
    have h1 := congrArg Subtype.val hn
    simpa using h1.symm
  have hGB : (g : X) ∈ B := Bal209F4Aux.pairSub_le hxy hxB hyB g.2
  have hG3 : (g : X) ^ 3 = 1 := hB.2 _ hGB
  have hG3z : (g : X) ^ (3 : ℤ) = 1 := by simpa using hG3
  have hG1 : (g : X) ≠ 1 := by
    intro h
    rw [h, one_zpow] at hyn
    exact hy1 hyn
  have hn3 : ¬ (3 : ℤ) ∣ n := by
    rintro ⟨k, rfl⟩
    apply hy1
    rw [hyn, zpow_mul, hG3z, one_zpow]
  have hGy : (g : X) ∈ Subgroup.zpowers y :=
    Bal209F4Aux.mem_of_zpow_mem hG3 hG1 hn3 (by rw [← hyn]; exact Subgroup.mem_zpowers y)
  apply hx
  rw [hxm]
  exact Subgroup.zpow_mem _ hGy m

theorem exists_pow_of_mem_pairSub {x y : X} {hxy : Commute x y} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) {a : X} (ha : a ∈ Bal209F4Aux.pairSub hxy) :
    ∃ n m : ℕ, n < 3 ∧ m < 3 ∧ a = x ^ n * y ^ m := by
  obtain ⟨i, j, rfl⟩ := Bal209F4Aux.mem_pairSub.1 ha
  refine ⟨(i % 3).toNat, (j % 3).toNat, by omega, by omega, ?_⟩
  have hi : x ^ i = x ^ (i % 3).toNat := by
    rw [zpow_eq_zpow_emod' i hx3, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    norm_num
  have hj : y ^ j = y ^ (j % 3).toNat := by
    rw [zpow_eq_zpow_emod' j hy3, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    norm_num
  rw [hi, hj]

end Transfer

section Powers

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree

variable {F : Type} [Field F]

theorem hasNF_pow {α : MulAut ↥(adjointGroup Tag.D4 F)} {ε : ℕ} {σ : F ≃+* F} (h : HasNF α ε σ) :
    ∀ n : ℕ, HasNF (α ^ n) (n * ε) (σ ^ n)
  | 0 => by
    have h0 := hasNF_conj (K := F) 1
    rw [map_one] at h0
    simpa using h0
  | n + 1 => by
    have h1 := (hasNF_pow h n).mul h
    rw [← pow_succ, ← pow_succ, show n * ε + ε = (n + 1) * ε by ring] at h1
    exact h1

theorem d4ElemType_of_hasNF [Finite F] {α : MulAut ↥(adjointGroup Tag.D4 F)} {ε : ℕ} {σ : F ≃+* F}
    (h : HasNF α ε σ) (h3 : α ^ 3 = 1) {c : ℕ → (F ≃+* F) → Prop} (hc : c (ε % 3) σ) :
    D4ElemType α c := by
  obtain ⟨g, a, hα⟩ := h.mod_three
  exact ⟨g, a, σ, ε % 3, Nat.mod_lt _ (by norm_num),
    CFSG.HardMathSupport.Lang.E6Descent.cube_normal_form_sigma_cube (hα ▸ h3), hc, hα⟩

theorem sigma_cube_of_hasNF [Finite F] {α : MulAut ↥(adjointGroup Tag.D4 F)} {ε : ℕ} {σ : F ≃+* F}
    (h : HasNF α ε σ) (h3 : α ^ 3 = 1) : σ ^ 3 = 1 := by
  obtain ⟨g, a, hα⟩ := h
  exact CFSG.HardMathSupport.Lang.E6Descent.cube_normal_form_sigma_cube (hα ▸ h3)

theorem eq_one_of_entrywise_eq_one [Finite F] {σ : F ≃+* F} (h : entrywiseAdjointAut Tag.D4 σ = 1) :
    σ = 1 := by
  refine RingEquiv.ext fun c => ?_
  have h1 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 F) =>
    φ (adjX Tag.D4 F ⟨0, by decide⟩ c)) h
  simp only [MulAut.one_apply] at h1
  rw [entrywiseAdjointAut_D4_eq, exactNormalAut_adjX,
    CFSG.HardMathSupport.Lang.E6Descent.exactPerm_D4] at h1
  simp only [Equiv.Perm.one_apply, Pi.one_apply, Units.val_one, one_mul] at h1
  exact adjX_injective ⟨0, by decide⟩ h1

end Powers

section Fixed

set_option linter.unusedSectionVars false


open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)
open CFSG.LieType.SeitzGeneration.ExcWideThree

@[expose] def IsTriD4TwoIndex : TauCeti.LieTypeIndex → Prop
  | .trialityD4 q => IsTwoPow q 1
  | _ => False

theorem isTriD4Two_bal (d : TauCeti.LieTypeIndex) (hd : IsTriD4TwoIndex d) :
    Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d := by
  cases d <;> simp_all [IsTriD4TwoIndex, Bal207Index,
    CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]

theorem isD4Two_bal (d : TauCeti.LieTypeIndex) (hd : IsD4TwoIndex d) :
    Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d := by
  cases d <;> simp_all [IsD4TwoIndex, Bal207Index,
    CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]

theorem center_eq_bot_of_d4EightComp {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex) :
    Subgroup.center ↥K = ⊥ := by
  have hKq : CFSG.IsQuasisimple K := D4FixedAux.isQuasisimple_of_open_aux hK.2.2
  obtain ⟨d, hdD4, ⟨eL⟩⟩ := hLie
  obtain ⟨d₀, hv⟩ := d
  cases d₀ with
  | D r q =>
    obtain ⟨rfl, hq⟩ := hdD4
    have hLM : CFSG.Models.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩)
        .POmegaPlus 4 2 3 := by
      have hmod := CFSG.Models.lieModel_D 4 q hv (MulEquiv.refl _)
      rw [hq.1, hq.2] at hmod
      exact hmod
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hKq eL hLM
    have h1 : (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 3).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 3).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 3).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 3).2) = 1 := by
      have hE8 : Even (8 : ℕ) := by decide
      simp [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
        hE8]
    rw [h1] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h)
  | _ => exact hdD4.elim

theorem d4GraphFieldFixed {X : Type} [Group X] [Finite X] {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hK : CFSG.Open.IsComponentOf K ⊤)
    (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex) (hA3 : a ^ 3 = 1)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F))
    (hGF : D4ElemType (MulAut.congr e (actHom K ⟨a, ha⟩)) fun ε σ => ε ≠ 0 ∧ σ ≠ 1) :
    IsSimpleGroup ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
      CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
      IsLieQuot ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) IsTriD4TwoIndex := by
  classical
  have hZK := center_eq_bot_of_d4EightComp hK hLie
  let eKq : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)
  let eD : K ≃* ↥(adjointGroup Tag.D4 F) := eKq.trans e
  set β : MulAut ↥(adjointGroup Tag.D4 F) := MulAut.congr eD (D4FixedAux.conjOnNormal K a ha)
    with hβdef
  have hβact : MulAut.congr e (actHom K ⟨a, ha⟩) = β := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have h2 : eD.symm (e (QuotientGroup.mk k)) = k := (MulEquiv.symm_apply_eq eD).2 rfl
    simp only [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h2]
    rfl
  obtain ⟨g, a', σ, ε, hεlt, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hGF
  rw [hβact] at hβeq
  have hε : ε = 1 ∨ ε = 2 := by omega
  have hβ3 : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, D4FixedAux.conjOnNormal_pow_three K a ha hA3, map_one]
  obtain ⟨T, hT, hT3, hT1, hσT⟩ := exists_frobenius_eight hF hσ3 hσ1
  obtain ⟨ψ, hFψ⟩ := graphField_conj_fixed hF hT hT3 hT1 hσT hε hβ3 hβeq
  obtain ⟨e₀⟩ := nonempty_fixed_d4Twist_equiv_cat' hF T hT (d4GfTwist_eq_or T σ ε)
  have E1 : ↥(fixedSubgroup (D4FixedAux.conjOnNormal K a ha)) ≃*
      ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    (MulEquiv.subgroupCongr (D4FixedAux.fixedSubgroup_conjOnNormal K a ha)).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have E2 : ↥(fixedSubgroup (D4FixedAux.conjOnNormal K a ha)) ≃* ↥(fixedSubgroup β) :=
    (Subgroup.equivMapOfInjective _ eD.toMonoidHom eD.injective).trans
      (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_congr eD (D4FixedAux.conjOnNormal K a ha)))
  have E3 : ↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (ψ * β * ψ⁻¹)) :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_conj ψ β))
  let Ffix : ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃*
      (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    E1.symm.trans (E2.trans (E3.trans ((MulEquiv.subgroupCongr hFψ).trans e₀)))
  have hmodel := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4 valid_trialityD4_two
  have hsC : IsSimpleGroup (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity _ _ _ hmodel).2
  have hcardC : Nat.card (TauCeti.CFSGIndex.lie trialityTwoIndex).Group = ordTrialityD4 2 :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmodel
  haveI : Finite (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcardC]; decide)
  obtain ⟨u, v, huv⟩ : ∃ u v : (TauCeti.CFSGIndex.lie trialityTwoIndex).Group, u * v ≠ v * u :=
    exists_noncomm_of_four_dvd (by rw [hcardC]; decide)
  have hsJ : IsSimpleGroup ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    (MulEquiv.isSimpleGroup_congr Ffix).2 hsC
  have hZJ : Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X))) with h | h
    · exact h
    · exfalso
      apply huv
      have hc : Ffix.symm u ∈ Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
        h ▸ Subgroup.mem_top _
      have h1 := Subgroup.mem_center_iff.1 hc (Ffix.symm v)
      apply Ffix.symm.injective
      rw [map_mul, map_mul]
      exact h1.symm
  have hperf : commutator ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (commutator ↥(K ⊓ Subgroup.centralizer ({a} : Set X))) with h | h
    · exfalso
      apply huv
      have hm : ⁅Ffix.symm u, Ffix.symm v⁆ ∈ commutator ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
        Subgroup.commutator_mem_commutator trivial trivial
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      apply Ffix.symm.injective
      rw [map_mul, map_mul]
      exact hm
    · exact h
  have hquasi : CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    ⟨hperf, (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZJ).trans
      QuotientGroup.quotientBot)).2 hsJ⟩
  let eFix : (↥(K ⊓ Subgroup.centralizer ({a} : Set X))) ⧸
      Subgroup.center ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃*
      (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).trans Ffix
  exact ⟨hsJ, hquasi, ⟨trialityTwoIndex, ⟨rfl, rfl⟩, ⟨eFix⟩⟩⟩

end Fixed


section Main

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree

@[expose] def D4EightGraphComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K OuterFourAux.IsD4EightIndex →
    IsSCp 3 (K ⊔ B) B → B ≤ Subgroup.normalizer (K : Set X) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ 3 →
    ∀ (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) (a b : X)
      (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X)),
      a ∈ B → b ∈ B →
      D4ElemType (MulAut.congr e (actHom K ⟨a, ha⟩)) (fun ε σ => ε ≠ 0 ∧ σ = 1) →
      D4ElemType (MulAut.congr e (actHom K ⟨b, hb⟩)) (fun ε σ => ε = 0 ∧ σ ≠ 1) →
      ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J

theorem bal2010D4_of_graphComp (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr)
    (hG : D4EightGraphComp) : OuterFourAux.Bal2010D4 IsGraphAutFour FieldAutD4 := by
  classical
  intro X _ _ hKG K B hKc hSC hBN hLie hGr hFd
  have hBel : IsElemAbelian 3 B := hSC.2.1
  obtain ⟨φ₁, hφ₁, hG1⟩ := hGr
  obtain ⟨φ₂, hφ₂, hF2⟩ := hFd
  obtain ⟨x, hxN, hxB, rfl⟩ := mem_autImage.1 hφ₁
  obtain ⟨y, hyN, hyB, rfl⟩ := mem_autImage.1 hφ₂
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hact3 : ∀ {z : X} (hz : z ∈ Subgroup.normalizer (K : Set X)), z ^ 3 = 1 →
      actHom K ⟨z, hz⟩ ^ 3 = 1 := by
    intro z hz hz3
    have h1 : (⟨z, hz⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hz3)
    rw [← map_pow, h1, map_one]
  obtain ⟨hsY, -, h3Y, -⟩ := d4FieldFixed_holds X K y hyN hKc hLie hy3 hF2
  obtain ⟨F, _, _, e₀, σ, γ, hF, hσ1, hmat⟩ := hF2
  set e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F) := e₀.trans γ with he
  have hα₂ : MulAut.congr e (actHom K ⟨y, hyN⟩) = entrywiseAdjointAut Tag.D4 σ := by
    refine MulEquiv.ext fun g => ?_
    obtain ⟨g', hg', hg''⟩ := hmat g
    have h1 : MulAut.congr e (actHom K ⟨y, hyN⟩) g =
        (γ * MulAut.congr e₀ (actHom K ⟨y, hyN⟩) * γ⁻¹) g := rfl
    rw [h1, hg'']
    exact Subtype.ext hg'
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  have hy3' : MulAut.congr e (actHom K ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow, hact3 hyN hy3, map_one]
  have hNF₂ : MulAut.congr e (actHom K ⟨y, hyN⟩) =
      MulAut.conj 1 * (exactNormalAut Tag.D4 F 1 σ 0 * d4Graph F 0) := by
    rw [hα₂, entrywiseAdjointAut_D4_eq, CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero, map_one,
      one_mul, mul_one]
  have hσ3 : σ ^ 3 = 1 :=
    CFSG.HardMathSupport.Lang.E6Descent.cube_normal_form_sigma_cube (hNF₂ ▸ hy3')
  have hHNF₂ : HasNF (MulAut.congr e (actHom K ⟨y, hyN⟩)) 0 σ := ⟨1, 1, hNF₂⟩
  have hx3' : MulAut.congr e (actHom K ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow, hact3 hxN hx3, map_one]
  have hns : ¬ CFSG.HardMathSupport.Dickson.Bal207.SemilinD4EightAut ↥(adjointGroup Tag.D4 F)
      (MulAut.congr e (actHom K ⟨x, hxN⟩)) := by
    intro h
    apply nonSemilin_of_graphAutD4 (hact3 hxN hx3) hG1
    have h' := h.of_mulEquiv e.symm
    rwa [CFSG.HardMathSupport.Dickson.Bal207.mulAut_congr_symm_congr] at h'
  obtain ⟨g₁, a₁, σ₁, ε₁, hε₁, hα₁⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.exists_graph_of_not_semilin_adjoint hF _ hx3' hns
  have hHNF₁ : HasNF (MulAut.congr e (actHom K ⟨x, hxN⟩)) ε₁ σ₁ := ⟨g₁, a₁, hα₁⟩
  have hy1 : y ≠ 1 := by
    intro h1
    apply hσ1
    apply eq_one_of_entrywise_eq_one
    rw [← hα₂]
    have h2 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set X)) = 1 := Subtype.ext h1
    rw [h2, map_one, map_one]
  have hxy' : x ∉ Subgroup.zpowers y := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hns
    have hpow : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set X)) =
        (⟨y, hyN⟩ : Subgroup.normalizer (K : Set X)) ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hpow, map_zpow, map_zpow, hα₂]
    refine ⟨F, inferInstance, inferInstance, (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj F).symm, hF8, ?_⟩
    rw [map_zpow]
    exact zpow_mem (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.congr_entrywiseAdjointAut_mem σ) k
  have hxy : Commute x y := Bal209F4Aux.commute_of_elemAbelian hBel hxB hyB
  have hAB : Bal209F4Aux.pairSub hxy ≤ B := Bal209F4Aux.pairSub_le hxy hxB hyB
  have hnc : ¬ IsCyclic ↥(Bal209F4Aux.pairSub hxy) :=
    not_isCyclic_pairSub_of hxy hBel hxB hyB hy1 hxy'
  have hpK : 3 ∣ Nat.card K := h3Y.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hloc : IsCompLocallyBalanced 3 1 (Bal209F4Aux.pairSub hxy) K :=
    CFSG.HardMathSupport.Dickson.Bal207.isCompLocallyBalanced_of_abs
      (P := fun p d => p = 3 ∧ CFSG.HardMathSupport.Dickson.Bal207.IsD4EightIdx d)
      (fun p d hd => CFSG.HardMathSupport.Dickson.Bal207.bal207LocalBalRow_d4Eight p d hd)
      Nat.prime_three _ hKc.2.2
      (Bal209F4Aux.isLieQuot_mono hLie fun d hd => ⟨rfl, by
        cases d <;> simp_all [OuterFourAux.IsD4EightIndex,
          CFSG.HardMathSupport.Dickson.Bal207.IsD4EightIdx]⟩)
  have hb : ∀ a ∈ Bal209F4Aux.pairSub hxy, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
    intro a ha ha1 J hJ
    have haB : a ∈ B := hAB ha
    have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN haB
    have ha3 : a ^ 3 = 1 := hBel.2 a haB
    obtain ⟨n, m, hn, hm, rfl⟩ := exists_pow_of_mem_pairSub hx3 hy3 ha
    have hact : actHom K ⟨x ^ n * y ^ m, haN⟩ =
        actHom K ⟨x, hxN⟩ ^ n * actHom K ⟨y, hyN⟩ ^ m := by
      have h1 : (⟨x ^ n * y ^ m, haN⟩ : Subgroup.normalizer (K : Set X)) =
          (⟨x, hxN⟩ : Subgroup.normalizer (K : Set X)) ^ n *
            (⟨y, hyN⟩ : Subgroup.normalizer (K : Set X)) ^ m :=
        Subtype.ext (by simp)
      rw [h1, map_mul, map_pow, map_pow]
    have hNF : HasNF (MulAut.congr e (actHom K ⟨x ^ n * y ^ m, haN⟩)) (n * ε₁ + m * 0)
        (σ₁ ^ n * σ ^ m) := by
      rw [hact, map_mul, map_pow, map_pow]
      exact (hasNF_pow hHNF₁ n).mul (hasNF_pow hHNF₂ m)
    have h3a : MulAut.congr e (actHom K ⟨x ^ n * y ^ m, haN⟩) ^ 3 = 1 := by
      rw [← map_pow, hact3 haN ha3, map_one]
    by_cases hε0 : (n * ε₁ + m * 0) % 3 = 0
    ·
      have hn0 : n = 0 := by rcases hε₁ with rfl | rfl <;> omega
      subst hn0
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact ha1 (by simp)
      have hσm : σ₁ ^ 0 * σ ^ m ≠ 1 := by
        rw [pow_zero, one_mul]
        intro h
        apply hσ1
        rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
        · simpa using h
        · have e1 : σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
          rw [e1, hσ3, h, inv_one, mul_one]
      have hFa : FieldAutD4 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x ^ 0 * y ^ m, haN⟩) :=
        fieldAutD4_of_fieldType hF e (hact3 haN ha3) (d4ElemType_of_hasNF hNF h3a ⟨hε0, hσm⟩)
      obtain ⟨hsimp, hquasi, -, hLieF⟩ := d4FieldFixed_holds X K _ haN hKc hLie ha3 hFa
      have hJeq := Bal209F4Aux.eq_of_glaPComponent hsimp hJ
      subst hJeq
      exact sLOB_of_bal207Corr h207 hKG hSC hBN haB hquasi isD4Two_bal hLieF
    · by_cases hσ' : σ₁ ^ n * σ ^ m = 1
      ·
        exact hG X hKG K B hKc hLie hSC hBN F hF e _ y haN hyN haB hyB
          (d4ElemType_of_hasNF hNF h3a ⟨hε0, hσ'⟩)
          (d4ElemType_of_hasNF hHNF₂ hy3' ⟨rfl, hσ1⟩) J hJ
      ·
        obtain ⟨hsimp, hquasi, hLieT⟩ := d4GraphFieldFixed haN hKc hLie ha3 hF e
          (d4ElemType_of_hasNF hNF h3a ⟨hε0, hσ'⟩)
        have hJeq := Bal209F4Aux.eq_of_glaPComponent hsimp hJ
        subst hJeq
        exact sLOB_of_bal207Corr h207 hKG hSC hBN haB hquasi isTriD4Two_bal hLieT
  have hc : ∃ a ∈ Bal209F4Aux.pairSub hxy, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X),
      Nat.Coprime 3 (orderOf w) → (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨y, Bal209F4Aux.mem_pairSub.2 ⟨0, 1, by simp⟩, hy1, fun w hwN _ hwB J hJ => ?_⟩
    have hJeq := Bal209F4Aux.eq_of_glaPComponent hsY hJ
    subst hJeq
    exact Bal209F4Aux.mem_normalizer_inf_centralizer hwN hyN (hwB y hyB)
  exact CFSG.HardMathSupport.Dickson.I271.i202Full_holds X 3 Nat.prime_three (by decide) K B
    (Bal209F4Aux.pairSub hxy) hKc.2.2 hpK hBN hBel hSC hAB hnc hloc hb hc

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz
