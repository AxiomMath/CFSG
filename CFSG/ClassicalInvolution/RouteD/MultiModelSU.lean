module

public import CFSG.ClassicalInvolution.RouteD.MultiModelLayer

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
  Matrix Module
open scoped MatrixGroups

section Geometry

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem exists_link_su (hK : Nat.card K = (p ^ f) ^ 2)
    {V₀ V₁ V₂ : Submodule K (Fin n → K)} (h₁ : Nondeg (unitaryInvolution K p f) V₁)
    (d₁ : finrank K V₁ = 2) (h₂ : Nondeg (unitaryInvolution K p f) V₂) (d₂ : finrank K V₂ = 2)
    (o01 : Orth (unitaryInvolution K p f) V₀ V₁) (o02 : Orth (unitaryInvolution K p f) V₀ V₂)
    (o12 : Orth (unitaryInvolution K p f) V₁ V₂) :
    ∃ V : Submodule K (Fin n → K), Nondeg (unitaryInvolution K p f) V ∧ finrank K V = 2 ∧
      V ≠ V₀ ∧ V ≠ V₁ ∧ V ≠ V₂ ∧ Orth (unitaryInvolution K p f) V V₀ ∧
      ¬ Orth (unitaryInvolution K p f) V V₁ ∧ ¬ Orth (unitaryInvolution K p f) V V₂ := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨v₁, hv₁, hv₁0⟩ := exists_aniso_of_plane_su hσ h₁ d₁
  obtain ⟨r, hr, hr0⟩ := exists_aniso_of_plane_su hσ h₂ d₂
  have hvr : herm (unitaryInvolution K p f) v₁ r = 0 := o12 v₁ hv₁ r hr
  have hrv : herm (unitaryInvolution K p f) r v₁ = 0 := (o12.symm hσ) r hr v₁ hv₁
  have hv₁ne : v₁ ≠ 0 := fun h => hv₁0 (by rw [h]; simp)
  have hrne : r ≠ 0 := fun h => hr0 (by rw [h]; simp)
  have hdisj : Disjoint (K ∙ v₁) (K ∙ r) :=
    (disjoint_span_perp hv₁0).mono_right
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (mem_perp_span_singleton.mpr hrv))
  have hv₁V : v₁ ∈ K ∙ v₁ ⊔ K ∙ r := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v₁)
  have hrV : r ∈ K ∙ v₁ ⊔ K ∙ r := Submodule.mem_sup_right (Submodule.mem_span_singleton_self r)
  refine ⟨K ∙ v₁ ⊔ K ∙ r, Nondeg.sup_of_orth hσ (nondeg_span_singleton hv₁0)
    (nondeg_span_singleton hr0) (orth_span_singleton_iff.mpr hvr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finrank_sup_of_disjoint hdisj, finrank_span_singleton hv₁ne, finrank_span_singleton hrne]
  · intro h
    exact hv₁0 (o01 v₁ (h ▸ hv₁V) v₁ hv₁)
  · intro h
    exact hr0 (o12 r (h ▸ hrV) r hr)
  · intro h
    exact hv₁0 (o12 v₁ hv₁ v₁ (h ▸ hv₁V))
  · intro u hu w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [herm_add_left, herm_smul_left, herm_smul_left, (o02.symm hσ) r hr w hw,
      (o01.symm hσ) v₁ hv₁ w hw, mul_zero, mul_zero, add_zero]
  · intro horth'
    exact hv₁0 (horth' v₁ hv₁V v₁ hv₁)
  · intro horth'
    exact hr0 (horth' r hrV r hr)

theorem eq_of_orth_orth_four (hK : Nat.card K = (p ^ f) ^ 2)
    {V₀ V₁ V₂ : Submodule K (Fin 4 → K)} (h₀ : Nondeg (unitaryInvolution K p f) V₀)
    (d₀ : finrank K V₀ = 2) (d₁ : finrank K V₁ = 2) (d₂ : finrank K V₂ = 2)
    (o01 : Orth (unitaryInvolution K p f) V₀ V₁) (o02 : Orth (unitaryInvolution K p f) V₀ V₂) :
    V₁ = V₂ := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hperpdim : finrank K (perp (unitaryInvolution K p f) V₀) = 2 := by
    have := finrank_add_finrank_herm_perp hσ h₀
    omega
  have e1 : V₁ = perp (unitaryInvolution K p f) V₀ :=
    Submodule.eq_of_le_of_finrank_eq (fun v hv s hs => (o01.symm hσ) v hv s hs) (by omega)
  have e2 : V₂ = perp (unitaryInvolution K p f) V₀ :=
    Submodule.eq_of_le_of_finrank_eq (fun v hv s hs => (o02.symm hσ) v hv s hs) (by omega)
  rw [e1, e2]

end Geometry

section Model

variable {p : ℕ} [Fact p.Prime]

theorem linkedIn_modelFund_psu {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU n p e) {R R₁ R₂ : Subgroup (modelUniv .PSU n p e Fact.out).K}
    (hR : R ∈ ModelFund p .PSU n e) (hR₁ : R₁ ∈ ModelFund p .PSU n e)
    (hR₂ : R₂ ∈ ModelFund p .PSU n e) (c₁ : Commutes R R₁) (c₂ : Commutes R R₂)
    (c₃ : Commutes R₁ R₂) : LinkedIn (ModelFund p .PSU n e) R R₁ R₂ := by
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSU n e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSU from trivial) hq hadm hS
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
  set S : Subgroup (modelUniv .PSU n p e Fact.out).K :=
    (planeGroupU (GaloisField p (2 * e)) p e V).map φ.symm.toMonoidHom with hS
  have hSφ : S.map φ.toMonoidHom = planeGroupU (GaloisField p (2 * e)) p e V := by
    rw [hS, Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by ext y; simp
    rw [this, Subgroup.map_id]
  have hSF : S ∈ ModelFund p .PSU n e :=
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

theorem eq_of_commutes_commutes_psu_small {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU n p e) (hn4 : n ≤ 4)
    {R R₁ R₂ : Subgroup (modelUniv .PSU n p e Fact.out).K} (hR : R ∈ ModelFund p .PSU n e)
    (hR₁ : R₁ ∈ ModelFund p .PSU n e) (hR₂ : R₂ ∈ ModelFund p .PSU n e) (c₁ : Commutes R R₁)
    (c₂ : Commutes R R₂) : R₁ = R₂ := by
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  have hnab := fun {S} (hS : S ∈ ModelFund p .PSU n e) =>
    not_commutes_self_modelFund hp2 (show IsFundTag .PSU from trivial) hq hadm hS
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

end Model

end CFSG.ClassicalInvolution.RouteD
