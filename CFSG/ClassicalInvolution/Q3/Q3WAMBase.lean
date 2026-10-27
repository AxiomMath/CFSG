module

public import CFSG.ClassicalInvolution.RouteD.MultiModelSL
public import CFSG.ClassicalInvolution.RouteD.MultiModelSU
public import CFSG.ClassicalInvolution.RouteD.MultiModelSp
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Abstract

variable {M : Type} [Group M]

theorem linkedIn_of_layer3 {F : Set (Subgroup M)} (hF : ∀ R ∈ F, ∀ g : M, conjSub g R ∈ F)
    (hnab : ∀ R ∈ F, ¬ Commutes R R) {R₀ L : Subgroup M}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hLC : L ≤ Subgroup.centralizer (R₀ : Set M))
    (hRL : ∀ R ∈ F, Commutes R R₀ → R ≤ L)
    {R₁ R₂ : Subgroup M} (h₁ : R₁ ∈ F) (h₂ : R₂ ∈ F) (c₁ : Commutes R₁ R₀)
    (c₂ : Commutes R₂ R₀) : LinkedIn F R₀ R₁ R₂ := by
  classical
  set Λ : Set (Subgroup M) := {R | R ∈ F ∧ Commutes R R₀} with hΛ
  have hΛL : ∀ R ∈ Λ, R ≤ L := fun R hR => hRL R hR.1 hR.2
  have hconj : ∀ g ∈ L, ∀ R ∈ Λ, conjSub g R ∈ Λ := by
    intro g hg R hR
    refine ⟨hF R hR.1 g, fun x hx y hy => ?_⟩
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ R, x = g * x' * g⁻¹ :=
      ⟨g⁻¹ * x * g, mem_conjSub_iff.mp hx, by group⟩
    have hgy : y * g = g * y := Subgroup.mem_centralizer_iff.mp (hLC hg) y hy
    have e1 : g⁻¹ * y = y * g⁻¹ := by
      calc g⁻¹ * y = g⁻¹ * y * g * g⁻¹ := by group
        _ = g⁻¹ * (g * y) * g⁻¹ := by rw [mul_assoc g⁻¹ y g, hgy]
        _ = y * g⁻¹ := by group
    have hxy : x' * y = y * x' := hR.2 x' hx' y hy
    calc g * x' * g⁻¹ * y = g * x' * (g⁻¹ * y) := by group
      _ = g * (x' * y) * g⁻¹ := by rw [e1]; group
      _ = g * (y * x') * g⁻¹ := by rw [hxy]
      _ = (g * y) * x' * g⁻¹ := by group
      _ = (y * g) * x' * g⁻¹ := by rw [← hgy]
      _ = y * (g * x' * g⁻¹) := by group
  set B : Set (Subgroup M) := {R | R ∈ Λ ∧ LinkedIn F R₀ R₁ R} with hB
  have hR₁Λ : R₁ ∈ Λ := ⟨h₁, c₁⟩
  have hR₂Λ : R₂ ∈ Λ := ⟨h₂, c₂⟩
  have hR₁B : R₁ ∈ B := ⟨hR₁Λ, Relation.ReflTransGen.refl⟩
  have hcomm : ∀ R ∈ Λ, R ∉ B → ∀ R' ∈ B, Commutes R R' := by
    intro R hR hRB R' hR'
    by_contra hnc
    exact hRB ⟨hR, hR'.2.tail ⟨hR'.1.1, hR.1, hR'.1.2, hR.2, fun h => hnc (Commutes.symm h)⟩⟩
  let H : Subgroup M := ⨆ R : ↥B, R.1
  let H' : Subgroup M := ⨆ R : ↥(Λ \ B), R.1
  have hHL : H ≤ L := iSup_le fun R => hΛL R.1 R.2.1
  have hH'L : H' ≤ L := iSup_le fun R => hΛL R.1 R.2.1
  have hHH' : Commutes H H' := commutes_iSup_iSup fun i j =>
    (hcomm j.1 j.2.1 j.2.2 i.1 i.2).symm
  have hle_sup : ∀ R ∈ Λ, R ≤ H ⊔ H' := by
    intro R hR
    by_cases hRB : R ∈ B
    · exact (le_iSup (fun R : ↥B => R.1) ⟨R, hRB⟩).trans le_sup_left
    · exact (le_iSup (fun R : ↥(Λ \ B) => R.1) ⟨R, hR, hRB⟩).trans le_sup_right
  let M₀ : Subgroup M := ⨆ R : ↥Λ, R.1
  have hM₀L : M₀ ≤ L := iSup_le fun R => hΛL R.1 R.2
  have hM₀norm : ∀ g ∈ L, ∀ n ∈ M₀, g * n * g⁻¹ ∈ M₀ := by
    intro g hg n hn
    induction hn using Subgroup.iSup_induction' with
    | hp R x hx =>
      exact (le_iSup (fun R : ↥Λ => R.1) ⟨conjSub g R.1, hconj g hg R.1 R.2⟩)
        (conj_mem_conjSub hx)
    | h1 => simp
    | hmul u v _ _ hu hv =>
      have e : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [e]
      exact M₀.mul_mem hu hv
  have hM₀normal : (M₀.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hM₀norm g g.2 n hn
  have hnoncentral : ∀ N : Subgroup M, N ≤ L → R₁ ≤ N → ¬ N.subgroupOf L ≤ Subgroup.center ↥L := by
    intro N hNL hR₁N hcen
    apply hnab R₁ h₁
    intro x hx y hy
    have := Subgroup.mem_center_iff.mp
      (hcen (show (⟨x, hΛL R₁ hR₁Λ hx⟩ : ↥L) ∈ N.subgroupOf L from hR₁N hx))
      ⟨y, hΛL R₁ hR₁Λ hy⟩
    exact congrArg Subtype.val this.symm
  have hLM₀ : L ≤ M₀ := by
    rcases normal_eq_top_or_le_center hLq hM₀normal with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exact absurd h (hnoncentral M₀ hM₀L (le_iSup (fun R : ↥Λ => R.1) ⟨R₁, hR₁Λ⟩))
  have hLHH' : L ≤ H ⊔ H' := hLM₀.trans (iSup_le fun R => hle_sup R.1 R.2)
  have hnormlz : H ⊔ H' ≤ Subgroup.normalizer (H : Set M) := by
    refine sup_le Subgroup.le_normalizer fun w hw => ?_
    rw [Subgroup.mem_normalizer_iff]
    have hfix : ∀ w ∈ H', ∀ h ∈ H, w * h * w⁻¹ = h := by
      intro w hw h hh
      have := hHH' h hh w hw
      calc w * h * w⁻¹ = (h * w) * w⁻¹ := by rw [this]
        _ = h := by group
    intro n
    constructor
    · intro hn
      rw [hfix w hw n hn]
      exact hn
    · intro hn
      have h2 := hfix w⁻¹ (H'.inv_mem hw) _ hn
      have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hn
  have hHnormal : (H.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hnormlz (hLHH' g.2)) n).mp hn
  have hR₁H : R₁ ≤ H := le_iSup (fun R : ↥B => R.1) ⟨R₁, hR₁B⟩
  have hLH : L ≤ H := by
    rcases normal_eq_top_or_le_center hLq hHnormal with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exact absurd h (hnoncentral H hHL hR₁H)
  by_contra hnl
  have hR₂nB : R₂ ∉ B := fun hB' => hnl hB'.2
  apply hnab R₂ h₂
  intro x hx y hy
  have hxH' : x ∈ H' := (le_iSup (fun R : ↥(Λ \ B) => R.1) ⟨R₂, hR₂Λ, hR₂nB⟩) hx
  have hyH : y ∈ H := hLH (hΛL R₂ hR₂Λ hy)
  exact (hHH' y hyH x hxH').symm

end Abstract

theorem sl2_not_comm_field (F : Type) [Field F] : ¬ ∀ a b : SL(2, F), a * b = b * a := by
  intro h
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F 1)
      (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F 1))
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

section Nonabelian



theorem not_commutes_self_modelFund3 {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t n 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 t n 1) :
    ¬ Commutes R R := by
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
    (by norm_num) hfund hadm hG2 hD4 hR
  intro hab
  apply sl2_not_comm_field (GaloisField 3 1)
  intro A B
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hab _ (e.symm A).2 _ (e.symm B).2)

end Nonabelian

section SL

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD.Exotic Module



theorem linkedIn_modelFund_psl3 {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1)
    {R R₁ R₂ : Subgroup (modelUniv .PSL n 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 .PSL n 1)
    (hR₁ : R₁ ∈ ModelFund 3 .PSL n 1) (hR₂ : R₂ ∈ ModelFund 3 .PSL n 1) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund 3 .PSL n 1) R R₁ R₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 1 ≤ m := by have := hadm.2.2.1; omega
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSL (m + 1) 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSL from trivial) hadm (by decide) (by decide) hS
  obtain ⟨i₀, h₀⟩ := (mem_modelFund_psl_iff hm R).mp hR
  obtain ⟨i₁, h₁⟩ := (mem_modelFund_psl_iff hm R₁).mp hR₁
  obtain ⟨i₂, h₂'⟩ := (mem_modelFund_psl_iff hm R₂).mp hR₂
  have n01 : R ≠ R₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : R ≠ R₂ := fun e' => hnab hR (e' ▸ c₂)
  have n12 : R₁ ≠ R₂ := fun e' => hnab hR₁ (e' ▸ c₃)
  have hn3 : 3 ≤ m + 1 := by
    by_contra hlt
    exact n01 (isLongRootSL2_eq_of_two h2 (by have := hadm.2.2.1; omega) h₀ h₁)
  obtain ⟨S, hS, sc, sn₁, sn₂⟩ := exists_link_sl h2 hn3 h₀ h₁ h₂' n01 n02 n12 c₁ c₂ c₃
  have hSF : S ∈ ModelFund 3 .PSL (m + 1) 1 := (mem_modelFund_psl_iff hm S).mpr hS
  exact (Relation.ReflTransGen.single ⟨hR₁, hSF, c₁.symm, sc, fun h => sn₁ h.symm⟩).tail
    ⟨hSF, hR₂, sc, c₂.symm, sn₂⟩

theorem eq_of_commutes_commutes_psl_small3 {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1)
    (hn4 : n ≤ 4) {R R₁ R₂ : Subgroup (modelUniv .PSL n 3 1 Fact.out).K}
    (hR : R ∈ ModelFund 3 .PSL n 1) (hR₁ : R₁ ∈ ModelFund 3 .PSL n 1)
    (hR₂ : R₂ ∈ ModelFund 3 .PSL n 1) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂) : R₁ = R₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 1 ≤ m := by have := hadm.2.2.1; omega
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSL (m + 1) 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSL from trivial) hadm (by decide) (by decide) hS
  obtain ⟨i₀, h₀⟩ := (mem_modelFund_psl_iff hm R).mp hR
  obtain ⟨i₁, h₁⟩ := (mem_modelFund_psl_iff hm R₁).mp hR₁
  obtain ⟨i₂, h₂'⟩ := (mem_modelFund_psl_iff hm R₂).mp hR₂
  have n01 : R ≠ R₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : R ≠ R₂ := fun e' => hnab hR (e' ▸ c₂)
  by_cases hn2 : m + 1 = 2
  · exact isLongRootSL2_eq_of_two h2 hn2 h₁ h₂'
  have hn3 : 3 ≤ m + 1 := by have := hadm.2.2.1; omega
  have h4 := four_le_of_commutes h2 hn3 h₀ h₁ n01 c₁
  exact eq_of_commutes_commutes_four h2 (by omega) h₀ h₁ h₂' n01 n02 c₁ c₂

end SL

section SU

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.RouteD.Exotic
  Matrix Module



theorem linkedIn_modelFund_psu3 {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1)
    {R R₁ R₂ : Subgroup (modelUniv .PSU n 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 .PSU n 1)
    (hR₁ : R₁ ∈ ModelFund 3 .PSU n 1) (hR₂ : R₂ ∈ ModelFund 3 .PSU n 1) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund 3 .PSU n 1) R R₁ R₂ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 hf
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSU n 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSU from trivial) hadm (by decide) (by decide) hS
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  obtain ⟨V₀, m₀, d₀, hV₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R).mp hR)
  obtain ⟨V₁, m₁, d₁, hV₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R₁).mp hR₁)
  obtain ⟨V₂, m₂, d₂, hV₂⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R₂).mp hR₂)
  have n01 : V₀ ≠ V₁ := fun e' => hnab hR (by
    have : R.map φ.toMonoidHom = R₁.map φ.toMonoidHom := by rw [hV₀, hV₁, e']
    exact (Subgroup.map_injective hinj this) ▸ c₁)
  have n02 : V₀ ≠ V₂ := fun e' => hnab hR (by
    have : R.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by rw [hV₀, hV₂, e']
    exact (Subgroup.map_injective hinj this) ▸ c₂)
  have n12 : V₁ ≠ V₂ := fun e' => hnab hR₁ (by
    have : R₁.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by rw [hV₁, hV₂, e']
    exact (Subgroup.map_injective hinj this) ▸ c₃)
  have o01 := (commutes_planeGroupU_iff hK hp2 hn hn3 m₀ d₀ m₁ d₁ n01).mp
    (hV₀ ▸ hV₁ ▸ (commutes_map_equiv φ).mpr c₁)
  have o02 := (commutes_planeGroupU_iff hK hp2 hn hn3 m₀ d₀ m₂ d₂ n02).mp
    (hV₀ ▸ hV₂ ▸ (commutes_map_equiv φ).mpr c₂)
  have o12 := (commutes_planeGroupU_iff hK hp2 hn hn3 m₁ d₁ m₂ d₂ n12).mp
    (hV₁ ▸ hV₂ ▸ (commutes_map_equiv φ).mpr c₃)
  obtain ⟨V, mV, dV, hV0, hV1, hV2, ho0, hn1, hn2⟩ := exists_link_su hK m₁ d₁ m₂ d₂ o01 o02 o12
  set S : Subgroup (modelUniv .PSU n 3 1 Fact.out).K :=
    (planeGroupU (GaloisField 3 (2 * 1)) 3 1 V).map φ.symm.toMonoidHom with hS
  have hSφ : S.map φ.toMonoidHom = planeGroupU (GaloisField 3 (2 * 1)) 3 1 V := by
    rw [hS, Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by ext y; simp
    rw [this, Subgroup.map_id]
  have hSF : S ∈ ModelFund 3 .PSU n 1 :=
    (hφ S).mpr (hSφ ▸ planeGroupU_mem hK hp2 hn mV dV)
  have sc : Commutes S R := by
    rw [← commutes_map_equiv φ, hSφ, hV₀]
    exact (commutes_planeGroupU_iff hK hp2 hn hn3 mV dV m₀ d₀ hV0).mpr ho0
  have sn₁ : ¬ Commutes S R₁ := by
    rw [← commutes_map_equiv φ, hSφ, hV₁]
    exact fun h => hn1 ((commutes_planeGroupU_iff hK hp2 hn hn3 mV dV m₁ d₁ hV1).mp h)
  have sn₂ : ¬ Commutes S R₂ := by
    rw [← commutes_map_equiv φ, hSφ, hV₂]
    exact fun h => hn2 ((commutes_planeGroupU_iff hK hp2 hn hn3 mV dV m₂ d₂ hV2).mp h)
  exact (Relation.ReflTransGen.single ⟨hR₁, hSF, c₁.symm, sc, fun h => sn₁ h.symm⟩).tail
    ⟨hSF, hR₂, sc, c₂.symm, sn₂⟩

theorem eq_of_commutes_commutes_psu_small3 {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1)
    (hn4 : n ≤ 4) {R R₁ R₂ : Subgroup (modelUniv .PSU n 3 1 Fact.out).K}
    (hR : R ∈ ModelFund 3 .PSU n 1) (hR₁ : R₁ ∈ ModelFund 3 .PSU n 1)
    (hR₂ : R₂ ∈ ModelFund 3 .PSU n 1) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂) : R₁ = R₂ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 hf
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSU n 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSU from trivial) hadm (by decide) (by decide) hS
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  obtain ⟨V₀, m₀, d₀, hV₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R).mp hR)
  obtain ⟨V₁, m₁, d₁, hV₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R₁).mp hR₁)
  obtain ⟨V₂, m₂, d₂, hV₂⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ R₂).mp hR₂)
  have n01 : V₀ ≠ V₁ := fun e' => hnab hR (by
    have : R.map φ.toMonoidHom = R₁.map φ.toMonoidHom := by rw [hV₀, hV₁, e']
    exact (Subgroup.map_injective hinj this) ▸ c₁)
  have n02 : V₀ ≠ V₂ := fun e' => hnab hR (by
    have : R.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by rw [hV₀, hV₂, e']
    exact (Subgroup.map_injective hinj this) ▸ c₂)
  have o01 := (commutes_planeGroupU_iff hK hp2 hn hn3 m₀ d₀ m₁ d₁ n01).mp
    (hV₀ ▸ hV₁ ▸ (commutes_map_equiv φ).mpr c₁)
  have o02 := (commutes_planeGroupU_iff hK hp2 hn hn3 m₀ d₀ m₂ d₂ n02).mp
    (hV₀ ▸ hV₂ ▸ (commutes_map_equiv φ).mpr c₂)
  have h4 : 4 ≤ n := by
    have hsum := finrank_sup_of_disjoint (disjoint_of_orth m₁ o01)
    have hle := Submodule.finrank_le (V₀ ⊔ V₁)
    rw [Module.finrank_fin_fun] at hle
    omega
  obtain rfl : n = 4 := by omega
  have hV : V₁ = V₂ := eq_of_orth_orth_four hK m₀ d₀ d₁ d₂ o01 o02
  apply Subgroup.map_injective hinj
  rw [hV₁, hV₂, hV]

end SU

section Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.RouteD.Exotic



theorem linkedIn_modelFund_psp3 {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1)
    {R R₁ R₂ : Subgroup (modelUniv .PSp n 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 .PSp n 1)
    (hR₁ : R₁ ∈ ModelFund 3 .PSp n 1) (hR₂ : R₂ ∈ ModelFund 3 .PSp n 1) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund 3 .PSp n 1) R R₁ R₂ := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSp n 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSp from trivial) hadm (by decide) (by decide) hS
  have hR' := (mem_modelFund_psp_iff hadm R).mp hR
  have hR₁' := (mem_modelFund_psp_iff hadm R₁).mp hR₁
  have hR₂' := (mem_modelFund_psp_iff hadm R₂).mp hR₂
  obtain ⟨P₀, hP₀, rfl⟩ := hR'
  obtain ⟨P₁, hP₁, rfl⟩ := hR₁'
  obtain ⟨P₂, hP₂, rfl⟩ := hR₂'
  have n01 : P₀ ≠ P₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : P₀ ≠ P₂ := fun e' => hnab hR (e' ▸ c₂)
  have n12 : P₁ ≠ P₂ := fun e' => hnab hR₁ (e' ▸ c₃)
  obtain ⟨S, hS, sc, sn₁, sn₂⟩ := exists_link_psp h2 hP₀ hP₁ hP₂
    ((commutes_planeGroup_iff h2 hP₀ hP₁ n01).mp c₁)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ n02).mp c₂)
    ((commutes_planeGroup_iff h2 hP₁ hP₂ n12).mp c₃)
  have hSF : S ∈ ModelFund 3 .PSp n 1 := (mem_modelFund_psp_iff hadm S).mpr hS
  exact (Relation.ReflTransGen.single ⟨hR₁, hSF, c₁.symm, sc, fun h => sn₁ h.symm⟩).tail
    ⟨hSF, hR₂, sc, c₂.symm, sn₂⟩

theorem eq_of_commutes_commutes_psp_two3 (hadm : StatedLieAdmissible .PSp 2 3 1)
    {R R₁ R₂ : Subgroup (modelUniv .PSp 2 3 1 Fact.out).K} (hR : R ∈ ModelFund 3 .PSp 2 1)
    (hR₁ : R₁ ∈ ModelFund 3 .PSp 2 1) (hR₂ : R₂ ∈ ModelFund 3 .PSp 2 1) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) : R₁ = R₂ := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hnab := fun {S} (hS : S ∈ ModelFund 3 .PSp 2 1) =>
    not_commutes_self_modelFund3 (show IsFundTag .PSp from trivial) hadm (by decide) (by decide) hS
  obtain ⟨P₀, hP₀, rfl⟩ := (mem_modelFund_psp_iff hadm R).mp hR
  obtain ⟨P₁, hP₁, rfl⟩ := (mem_modelFund_psp_iff hadm R₁).mp hR₁
  obtain ⟨P₂, hP₂, rfl⟩ := (mem_modelFund_psp_iff hadm R₂).mp hR₂
  have n01 : P₀ ≠ P₁ := fun e' => hnab hR (e' ▸ c₁)
  have n02 : P₀ ≠ P₂ := fun e' => hnab hR (e' ▸ c₂)
  rw [eq_of_orth_orth_two hP₀ hP₁ hP₂ ((commutes_planeGroup_iff h2 hP₀ hP₁ n01).mp c₁)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ n02).mp c₂)]

end Sp

end CFSG.ClassicalInvolution.Q3.Q3W
