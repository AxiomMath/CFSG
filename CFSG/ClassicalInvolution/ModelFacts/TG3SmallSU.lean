module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Small
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSUGen
public import CFSG.ClassicalInvolution.Asc77.WP3SCURank
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral
public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGU
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Module
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section Pure

theorem centralizer_sup_eq_top_of_equiv {G Y : Type*} [Group G] [Group Y] (e : G ≃* Y) (a b : G)
    (h : Subgroup.centralizer ({e a} : Set Y) ⊔ Subgroup.centralizer ({e b} : Set Y) = ⊤) :
    Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G) = ⊤ := by
  have hmap : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
    intro x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hz']
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
      refine Subgroup.mem_centralizer_singleton_iff.mpr (e.injective ?_)
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy'
  have hsup : (Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G)).map
      e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, hmap, hmap, h]
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ (Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G)).map
      e.toMonoidHom := by
    rw [hsup]
    trivial
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := e.injective hyx
  rwa [this] at hy

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_smul_one_of_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    {n : ℕ} (hn3 : 3 ≤ n) {z : Su K p f n} (hz : z ∈ Subgroup.center (Su K p f n)) :
    ∃ μ : K, suMat z = μ • (1 : Matrix (Fin n) (Fin n) K) := by
  have hU : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.eq_smul_one_of_commute hU hp hn3
    (suMat z) fun y hy => ?_
  have hy' : y ∈ SUid (unitaryInvolution K p f) n := by
    rw [SUid_eq_statedSU hK]
    exact hy
  have := Subgroup.mem_center_iff.mp hz ⟨y, hy'⟩
  have h3 := congrArg (fun x : Su K p f n => suMat x) this
  simp only [suMat_mul] at h3
  exact h3.symm

theorem not_mem_center_of_isLongRootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hf : 1 ≤ f) {n : ℕ} (hn3 : 3 ≤ n) {hn : 2 ≤ n} {L : Subgroup (Su K p f n)}
    {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) : i ∉ Subgroup.center (Su K p f n) := by
  intro hz
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_mem_center hK hp hf hn3 hz
  have hdim := h.finrank_minusSpaceSU h2
  have hsq : μ * μ = 1 := by
    have h1 : suMat i * suMat i = (μ * μ) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [hμ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [h.coe_mul_self] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3.symm
  rcases mul_self_eq_one_iff.mp hsq with rfl | rfl
  · have : minusSpaceSU i = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [mem_minusSpaceSU, hμ, one_smul, Matrix.one_mulVec] at hv
      have h3 : (2 : K) • v = 0 := by
        rw [two_smul]
        nth_rewrite 1 [hv]
        exact neg_add_cancel v
      exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3).resolve_left h2)
    rw [this, finrank_bot] at hdim
    omega
  · have : minusSpaceSU i = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [mem_minusSpaceSU, hμ, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [this, finrank_top, Module.finrank_fin_fun] at hdim
    omega

theorem exists_sq_eq_neg_one_unitary_three (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) :
    ∃ c : K, c * c = -1 ∧ unitaryInvolution K p f c = -c := by
  obtain ⟨ι, hι0, hι⟩ := exists_unitaryInvolution_eq_neg hK
  have hcube : ι ^ 3 = -ι := by rw [← h3, ← unitaryInvolution_apply, hι]
  refine ⟨ι, ?_, hι⟩
  have h1 : ι * (ι * ι + 1) = 0 := by linear_combination hcube
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hι0)

theorem negBlock_four_two : negBlock K 4 2 = -negBlock K 4 0 := by
  rw [negBlock_eq_diagonal, negBlock_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext a
  fin_cases a <;> simp

end Pure

section Struct

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_twin_gen (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f) {c : K}
    (hc : c * c = -1) (hσc : unitaryInvolution K p f c = -c)
    {L₁ L₂ : Subgroup (Su K p f 4)} {i₁ i₂ : Su K p f 4}
    (h₁ : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num) L₁ i₁)
    (h₂ : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num) L₂ i₂) (hR : L₁ ≠ L₂)
    (hcen : i₂ * i₁⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    Commutes L₁ L₂ ∧ i₁ ∉ Subgroup.center (Su K p f 4) ∧ i₂ ∉ Subgroup.center (Su K p f 4) ∧
      ∀ r₁ ∈ L₁, ∀ r₂ ∈ L₂, r₁ * r₁ = i₁ → r₂ * r₂ = i₂ →
        Subgroup.centralizer ({i₁} : Set (Su K p f 4)) ⊔
          Subgroup.centralizer ({(r₁ * r₂)} : Set (Su K p f 4)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hsq₁ : i₁ * i₁ = 1 := h₁.mul_self
  have hcen' : i₁ * i₂ ∈ Subgroup.center (Su K p f 4) := by
    have h1 : i₁ * i₂ = i₂ * i₁⁻¹ := by
      have hc' := Subgroup.mem_center_iff.mp hcen i₁
      have hinv : i₁⁻¹ = i₁ := inv_eq_of_mul_eq_one_right hsq₁
      rw [hinv] at hc' ⊢
      have h3 := congrArg (fun x => x * i₁) hc'
      simp only [mul_assoc, hsq₁, mul_one] at h3
      exact h3
    rw [h1]
    exact hcen
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_mem_center hK hp hf (by norm_num : 3 ≤ 4) hcen'
  have hM₁ : suMat i₁ * suMat i₁ = 1 := h₁.coe_mul_self
  have hM₂ : suMat i₂ * suMat i₂ = 1 := h₂.coe_mul_self
  have hprod : suMat i₁ * suMat i₂ = μ • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [← suMat_mul, hμ]
  have hM : suMat i₂ = μ • suMat i₁ := by
    calc suMat i₂ = (suMat i₁ * suMat i₁) * suMat i₂ := by rw [hM₁, Matrix.one_mul]
      _ = suMat i₁ * (suMat i₁ * suMat i₂) := by rw [Matrix.mul_assoc]
      _ = μ • suMat i₁ := by rw [hprod, Matrix.mul_smul, Matrix.mul_one]
  have hμ2 : μ * μ = 1 := by
    have h1 : suMat i₂ * suMat i₂ = (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      conv_lhs => rw [hM]
      rw [Matrix.smul_mul, Matrix.mul_smul, hM₁, smul_smul]
    rw [hM₂] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3.symm
  have hneg : suMat i₂ = -suMat i₁ := by
    rcases mul_self_eq_one_iff.mp hμ2 with h | h
    · exfalso
      apply hR
      have : i₂ = i₁ := by
        apply suMat_injective
        rw [hM, h, one_smul]
      rw [h₁.eq_longRootGroupSU h2, h₂.eq_longRootGroupSU h2, this]
    · rw [hM, h, neg_smul, one_smul]
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [hneg, Matrix.mul_neg, Matrix.neg_mul]
  have hV : eigSpace (suMat i₁) (-1) ⊓ eigSpace (suMat i₂) (-1) = ⊥ := by
    have e : eigSpace (suMat i₂) (-1) = eigSpace (suMat i₁) 1 := by
      ext v
      rw [mem_eigSpace_neg_one, mem_eigSpace_one, hneg, Matrix.neg_mulVec, neg_inj]
    rw [e]
    exact (isCompl_eigSpace h2 hM₁).inf_eq_bot
  have hcomm : Commutes L₁ L₂ := fun x hx y hy => by
    rw [h₁.eq_longRootGroupSU h2] at hx
    rw [h₂.eq_longRootGroupSU h2] at hy
    exact mul_comm_of_inf_eq_bot_su h2 hM₁ hM₂ hcc hV hx hy
  refine ⟨hcomm, not_mem_center_of_isLongRootSU2 hK hp hf (by norm_num) h₁,
    not_mem_center_of_isLongRootSU2 hK hp hf (by norm_num) h₂, fun r₁ hr₁ r₂ hr₂ hrr₁ hrr₂ => ?_⟩
  obtain ⟨g₁, hL₁, hi₁⟩ := h₁
  set φ : Su K p f 4 ≃* Su K p f 4 := MulAut.conj g₁⁻¹ with hφ
  have hφapp : ∀ x, φ x = g₁⁻¹ * x * g₁⁻¹⁻¹ := fun x => MulAut.conj_apply _ _
  have hφi₁ : φ i₁ = rootInvSU K p f (show 2 ≤ 4 by norm_num) := by
    rw [hφapp, hi₁]
    group
  have hφr₁ : φ r₁ ∈ rootSU2 K p f (show 2 ≤ 4 by norm_num) := by
    rw [hL₁, mem_map_conj_iff_of_group] at hr₁
    rwa [hφapp, inv_inv]
  obtain ⟨A₁, hA₁⟩ := hφr₁
  have hsuφi₂ : suMat (φ i₂) = negBlock K 4 2 := by
    have e1 : suMat (φ i₁) = negBlock K 4 0 := by
      rw [hφi₁, suMat_rootInvSU]
    have e2 : suMat (φ i₂) = -suMat (φ i₁) := by
      rw [hφapp, hφapp, suMat_mul, suMat_mul, suMat_mul, suMat_mul, hneg, Matrix.mul_neg,
        Matrix.neg_mul]
    rw [e2, e1, negBlock_four_two]
  have hφL₂ : (L₂.map φ.toMonoidHom) = (blockEmb K p f 4 2 2 (by norm_num)).range := by
    rw [range_blockEmb_eq_longRootGroupSU h2 (by norm_num : 2 + 2 ≤ 4), ← hsuφi₂]
    exact (h₂.conj g₁⁻¹).eq_longRootGroupSU h2
  have hφr₂ : φ r₂ ∈ (blockEmb K p f 4 2 2 (by norm_num)).range := by
    rw [← hφL₂]
    exact Subgroup.mem_map_of_mem _ hr₂
  obtain ⟨A₂, hA₂⟩ := hφr₂
  have hA₁sq : A₁ * A₁ = negOneSU K p f := by
    apply blockEmb_injective (K := K) (p := p) (f := f) (m := 4) (k := 2) (i := 0) (by norm_num)
    rw [map_mul, hA₁, ← map_mul, hrr₁, hφi₁]
    rfl
  have hA₂sq : A₂ * A₂ = negOneSU K p f := by
    apply blockEmb_injective (K := K) (p := p) (f := f) (m := 4) (k := 2) (i := 2) (by norm_num)
    rw [map_mul, hA₂, ← map_mul, hrr₂]
    apply suMat_injective
    rw [hsuφi₂, suMat_blockEmb, suMat_negOneSU]
    rfl
  refine centralizer_sup_eq_top_of_equiv φ i₁ (r₁ * r₂) ?_
  rw [hφi₁, map_mul, ← hA₁, ← hA₂]
  exact su4_std_gen hK hp hc hσc A₁ A₂ hA₁sq hA₂sq

end Struct

section Model


theorem compGen3Twin_psu_four (hadm : StatedLieAdmissible .PSU 4 3 1) :
    CompGen3Twin (compModel 3 1 .PSU 4) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hfin : Finite (compModel 3 1 .PSU 4).G :=
    finite_modelUniv (t := .PSU) hp2 Nat.prime_three trivial hadm
  have : Finite (Generic.modelUniv .PSU 4 3 1 Fact.out).K := hfin
  obtain ⟨e, hfund⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨c, hcsq, hσc⟩ := exists_sq_eq_neg_one_unitary_three (K := GaloisField 3 (2 * 1)) (p := 3)
    (f := 1) hK (by norm_num)
  have key : ∀ {R₁ R₂ : Subgroup (Generic.modelUniv .PSU 4 3 1 Fact.out).K},
      R₁ ∈ Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU 4 3 1 Fact.out).D →
      R₂ ∈ Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU 4 3 1 Fact.out).D →
      ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)), R₁ ≠ R₂ →
        sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (Generic.modelUniv .PSU 4 3 1 Fact.out).K →
        Commutes R₁ R₂ ∧ sl2Inv e₁ ∉ Subgroup.center (Generic.modelUniv .PSU 4 3 1 Fact.out).K ∧
          sl2Inv e₂ ∉ Subgroup.center (Generic.modelUniv .PSU 4 3 1 Fact.out).K ∧
          ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₁ = sl2Inv e₁ → r₂ * r₂ = sl2Inv e₂ →
            Subgroup.centralizer ({sl2Inv e₁} : Set (Generic.modelUniv .PSU 4 3 1 Fact.out).K) ⊔
              Subgroup.centralizer
                ({(r₁ * r₂)} : Set (Generic.modelUniv .PSU 4 3 1 Fact.out).K) = ⊤ := by
    intro R₁ R₂ hR₁ hR₂ e₁ e₂ hne hc
    obtain ⟨i₁, hi₁⟩ := (hfund R₁).mp hR₁
    obtain ⟨i₂, hi₂⟩ := (hfund R₂).mp hR₂
    have hord : ∀ {R : Subgroup (Generic.modelUniv .PSU 4 3 1 Fact.out).K} (eR : R ≃* SL(2, 𝔽₃)),
        orderOf (e (sl2Inv eR)) = 2 := by
      intro R eR
      rw [MulEquiv.orderOf_eq e]
      exact orderOf_eq_prime (by rw [pow_two]; exact sl2Inv_mul_self hodd eR)
        (sl2Inv_ne_one hodd eR)
    have hi₁e : e (sl2Inv e₁) = i₁ := hi₁.eq_of_orderOf_eq_two hK hp2
      (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₁)) (hord e₁)
    have hi₂e : e (sl2Inv e₂) = i₂ := hi₂.eq_of_orderOf_eq_two hK hp2
      (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂)) (hord e₂)
    have hne' : R₁.map e.toMonoidHom ≠ R₂.map e.toMonoidHom := by
      intro h
      exact hne (by rw [Subgroup.map_injective e.injective h])
    have hc' : i₂ * i₁⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
      rw [← hi₁e, ← hi₂e]
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    obtain ⟨hcomm, hnc₁, hnc₂, hgen⟩ := su4_twin_gen hK hp2 le_rfl hcsq hσc hi₁ hi₂ hne' hc'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm (e x) (Subgroup.mem_map_of_mem _ hx) (e y) (Subgroup.mem_map_of_mem _ hy)
    · intro hz
      apply hnc₁
      rw [← hi₁e]
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    · intro hz
      apply hnc₂
      rw [← hi₂e]
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    · intro r₁ hr₁ r₂ hr₂ hrr₁ hrr₂
      refine centralizer_sup_eq_top_of_equiv e _ _ ?_
      rw [map_mul, hi₁e]
      exact hgen (e r₁) (Subgroup.mem_map_of_mem _ hr₁) (e r₂) (Subgroup.mem_map_of_mem _ hr₂)
        (by rw [← map_mul, hrr₁, hi₁e]) (by rw [← map_mul, hrr₂, hi₂e])
  refine compGen3Twin_small_of_gen₂ (G := (Generic.modelUniv .PSU 4 3 1 Fact.out).K)
    (Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU 4 3 1 Fact.out).D) ?_ ?_ ?_
  · intro R hR
    exact nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU) trivial hadm
      (by decide) (by decide) hR
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc
    obtain ⟨hcomm, hnc₁, hnc₂, -⟩ := key hR₁ hR₂ e₁ e₂ hne hc
    exact ⟨hcomm, hnc₁, hnc₂⟩
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc r₁ hr₁ r₂ hr₂ hsq₁ hsq₂
    obtain ⟨-, -, -, hgen⟩ := key hR₁ hR₂ e₁ e₂ hne hc
    exact hgen r₁ hr₁ r₂ hr₂ hsq₁ hsq₂

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
