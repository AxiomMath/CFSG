module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

section Config

variable {K : Type*} [Group K]

@[expose] def NoTE6Config (Fund : Set (Subgroup K)) : Prop :=
  ∀ R₀ ∈ Fund, ∀ R₁, UniversalPartner Fund R₀ R₁ → ThirdMember Fund R₀ R₁ → False

theorem NoTE6Config.of_pairSeparated {Fund : Set (Subgroup K)} (h : PairSeparated Fund) :
    NoTE6Config Fund :=
  fun _ h0 _ hP _ => false_of_pairSeparated h h0 hP

theorem NoTE6Config.of_noPartner {Fund : Set (Subgroup K)} (h : NoPartner Fund) :
    NoTE6Config Fund :=
  fun _ h0 _ hP _ => false_of_noPartner h h0 hP

theorem NoTE6Config.of_noThreeCommuting {Fund : Set (Subgroup K)} (h : NoThreeCommuting Fund) :
    NoTE6Config Fund :=
  fun _ h0 _ hP hT => false_of_noThreeCommuting h h0 hP hT

theorem NoTE6Config.of_equiv {K' : Type*} [Group K'] (e : K ≃* K') {Fund : Set (Subgroup K)}
    {Fund' : Set (Subgroup K')} (h : ∀ R : Subgroup K, R ∈ Fund ↔ R.map e.toMonoidHom ∈ Fund')
    (hN : NoTE6Config Fund') : NoTE6Config Fund := by
  intro R₀ h0 R₁ hP hT
  have hinj := Subgroup.map_injective (f := e.toMonoidHom) e.injective
  have back : ∀ S' : Subgroup K', (S'.map e.symm.toMonoidHom).map e.toMonoidHom = S' := by
    intro S'
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K' := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  refine hN (R₀.map e.toMonoidHom) ((h _).mp h0) (R₁.map e.toMonoidHom)
    ⟨(h _).mp hP.1, fun heq => hP.2.1 (hinj heq), (commutes_map_equiv e).mpr hP.2.2.1,
      fun S' hS' hc => ?_⟩ ?_
  · obtain ⟨S, rfl⟩ : ∃ S : Subgroup K, S.map e.toMonoidHom = S' :=
      ⟨S'.map e.symm.toMonoidHom, back S'⟩
    rcases hP.2.2.2 S ((h S).mpr hS') ((commutes_map_equiv e).mp hc) with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr ((commutes_map_equiv e).mpr h1)
  · obtain ⟨S, hS, h0', h1', hc⟩ := hT
    exact ⟨S.map e.toMonoidHom, (h S).mp hS, fun heq => h0' (hinj heq),
      fun heq => h1' (hinj heq), (commutes_map_equiv e).mpr hc⟩

end Config

section Linear

variable {F : Type} [Field F] {n : ℕ}

theorem pairSeparated_longRootSet (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn5 : 5 ≤ n) :
    PairSeparated (longRootSet (K := F) hn) := by
  rintro R₀ ⟨i₀, h₀⟩ R₁ ⟨i₁, h₁⟩ hne hc
  obtain ⟨S, hS, -, hS1, hcS, hncS⟩ := exists_separating h2 hn5 h₀ h₁ (Ne.symm hne) hc
  exact ⟨S, hS, hcS, hS1, hncS⟩

theorem noPartner_longRootSet (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n) (hn4 : n < 4) :
    NoPartner (longRootSet (K := F) hn) := by
  rintro R₀ ⟨i₀, h₀⟩ S ⟨i, h⟩ hne hc
  have := four_le_of_commutes h2 hn3 h h₀ hne hc
  omega

theorem noThreeCommuting_longRootSet_four (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 4} :
    NoThreeCommuting (longRootSet (K := F) hn) := by
  rintro A ⟨i₀, h₀⟩ B ⟨i₁, h₁⟩ C ⟨i₂, h₂'⟩ h01 h02 h12 c01 c02 c12
  exact false_of_commutes_three_four h2 h₀ h₁ h₂' h01 h02 h12 c01 c02 c12

theorem noTE6Config_longRootSet (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} :
    NoTE6Config (longRootSet (K := F) hn) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    intro R₀ h0 R₁ hP _
    exact hP.2.1 ((longRootSet_two_subset hn hP.1).trans (longRootSet_two_subset hn h0).symm)
  · rcases Nat.lt_or_ge n 4 with h' | h'
    · exact NoTE6Config.of_noPartner (noPartner_longRootSet h2 h h')
    · rcases Nat.lt_or_ge n 5 with h'' | h''
      · obtain rfl : n = 4 := by omega
        exact NoTE6Config.of_noThreeCommuting (noThreeCommuting_longRootSet_four h2)
      · exact NoTE6Config.of_pairSeparated (pairSeparated_longRootSet h2 h'')

end Linear

section Symplectic

variable {F : Type} [Field F] {n : ℕ}

open CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem pairSeparated_planeGroupSet (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) :
    PairSeparated (planeGroupSet F n) := by
  rintro R₀ ⟨P₀, hP₀, rfl⟩ R₁ ⟨P₁, hP₁, rfl⟩ hne hc
  have hne' : P₀ ≠ P₁ := fun e => hne (by rw [e])
  have horth := (commutes_planeGroup_iff h2 hP₀ hP₁ hne').mp hc
  obtain ⟨S, hS, -, hS1, hcS, hncS⟩ := exists_separating_psp h2 hn hP₀ hP₁ horth
  exact ⟨S, hS, hcS, hS1, hncS⟩

theorem noThreeCommuting_planeGroupSet_two (h2 : (2 : F) ≠ 0) :
    NoThreeCommuting (planeGroupSet F 2) := by
  rintro A ⟨P₀, hP₀, rfl⟩ B ⟨P₁, hP₁, rfl⟩ C ⟨P₂, hP₂, rfl⟩ h01 h02 h12 c01 c02 c12
  exact false_of_orth_three_two hP₀ hP₁ hP₂
    ((commutes_planeGroup_iff h2 hP₀ hP₁ (fun e => h01 (by rw [e]))).mp c01)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ (fun e => h02 (by rw [e]))).mp c02)
    ((commutes_planeGroup_iff h2 hP₁ hP₂ (fun e => h12 (by rw [e]))).mp c12)

theorem noTE6Config_planeGroupSet (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n) :
    NoTE6Config (planeGroupSet F n) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact NoTE6Config.of_noThreeCommuting (noThreeCommuting_planeGroupSet_two h2)
  · exact NoTE6Config.of_pairSeparated (pairSeparated_planeGroupSet h2 h)

end Symplectic

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem pairSeparated_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) (hn5 : 5 ≤ n) : PairSeparated (longRootSetU (K := K) (p := p) (f := f) hn) := by
  intro R₀ hR₀ R₁ hR₁ hne hc
  obtain ⟨V₀, n₀, d₀, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hR₀
  obtain ⟨V₁, n₁, d₁, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hR₁
  have hne' : V₀ ≠ V₁ := fun e => hne (by rw [e])
  have horth := (commutes_planeGroupU_iff hK hp hn hn3 n₀ d₀ n₁ d₁ hne').mp hc
  obtain ⟨V, nV, dV, hV0, hV1, hVo, hVn⟩ := exists_separating_su hK hn5 n₀ d₀ n₁ d₁ horth
  refine ⟨planeGroupU K p f V, planeGroupU_mem hK hp hn nV dV,
    (commutes_planeGroupU_iff hK hp hn hn3 nV dV n₀ d₀ hV0).mpr hVo,
    fun e => hV1 (planeGroupU_injective hK hp hn nV dV n₁ d₁ e), fun hcc => hVn ?_⟩
  exact (commutes_planeGroupU_iff hK hp hn hn3 nV dV n₁ d₁ hV1).mp hcc

theorem noPartner_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) (hn4 : n < 4) : NoPartner (longRootSetU (K := K) (p := p) (f := f) hn) := by
  intro R₀ hR₀ S hS hne hc
  obtain ⟨V₀, n₀, d₀, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hR₀
  obtain ⟨V₁, n₁, d₁, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hS
  have hne' : V₁ ≠ V₀ := fun e => hne (by rw [e])
  have horth := (commutes_planeGroupU_iff hK hp hn hn3 n₁ d₁ n₀ d₀ hne').mp hc
  have hsum := finrank_sup_of_disjoint (disjoint_of_orth n₀ horth)
  have hle := Submodule.finrank_le (V₁ ⊔ V₀)
  rw [Module.finrank_fin_fun] at hle
  omega

theorem noThreeCommuting_longRootSetU_four (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ 4} : NoThreeCommuting (longRootSetU (K := K) (p := p) (f := f) hn) := by
  intro A hA B hB C hC h01 h02 h12 c01 c02 c12
  obtain ⟨V₀, n₀, d₀, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hA
  obtain ⟨V₁, n₁, d₁, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hB
  obtain ⟨V₂, n₂, d₂, rfl⟩ := (mem_longRootSetU_iff_plane hK hp hn).mp hC
  exact false_of_orth_three_four n₁ n₂ d₀ d₁ d₂
    ((commutes_planeGroupU_iff hK hp hn (by norm_num) n₀ d₀ n₁ d₁
      (fun e => h01 (by rw [e]))).mp c01)
    ((commutes_planeGroupU_iff hK hp hn (by norm_num) n₀ d₀ n₂ d₂
      (fun e => h02 (by rw [e]))).mp c02)
    ((commutes_planeGroupU_iff hK hp hn (by norm_num) n₁ d₁ n₂ d₂
      (fun e => h12 (by rw [e]))).mp c12)

theorem noTE6Config_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) : NoTE6Config (longRootSetU (K := K) (p := p) (f := f) hn) := by
  rcases Nat.lt_or_ge n 4 with h' | h'
  · exact NoTE6Config.of_noPartner (noPartner_longRootSetU hK hp hn3 h')
  · rcases Nat.lt_or_ge n 5 with h'' | h''
    · obtain rfl : n = 4 := by omega
      exact NoTE6Config.of_noThreeCommuting (noThreeCommuting_longRootSetU_four hK hp)
    · exact NoTE6Config.of_pairSeparated (pairSeparated_longRootSetU hK hp hn3 h'')

end Unitary

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem noTE6Config_psl_model (hp2 : p ≠ 2) {n : ℕ} (hadm : StatedLieAdmissible .PSL n p f) :
    NoTE6Config (fundamentalSubgroups .PSL (modelUniv .PSL n p f Fact.out).D) := by
  have hn2 : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hF := noTE6Config_longRootSet (F := GaloisField p f) (n := m + 1)
    (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) (hn := by omega)
  rw [← fundamentalSubgroups_psl_eq (p := p) (f := f) (by omega : 1 ≤ m)] at hF
  exact hF

theorem noTE6Config_psp_model (hp2 : p ≠ 2) {n : ℕ} (hadm : StatedLieAdmissible .PSp n p f) :
    NoTE6Config (fundamentalSubgroups .PSp (modelUniv .PSp n p f Fact.out).D) := by
  rw [fundamentalSubgroups_psp_eq hadm]
  exact noTE6Config_planeGroupSet
    (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hadm.2.2.1

theorem noTE6Config_psu_model (hp2 : p ≠ 2) {n : ℕ} (hadm : StatedLieAdmissible .PSU n p f) :
    NoTE6Config (fundamentalSubgroups .PSU (modelUniv .PSU n p f Fact.out).D) := by
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  exact NoTE6Config.of_equiv e he
    (noTE6Config_longRootSetU (CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1)
      hp2 hadm.2.2.1)

end Model

end CFSG.ClassicalInvolution.RouteD.NonClassical
