module

public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Symplectic
open scoped Matrix

section Criteria

variable {K : Type} [Group K]

theorem cartanC_entries {m : ℕ} {a b c : Fin m} (ha : a.val + 3 = m) (hb : b.val + 2 = m)
    (hc : c.val + 1 = m) :
    cartanC m a a = 2 ∧ cartanC m b b = 2 ∧ cartanC m c c = 2 ∧ cartanC m a b = -1 ∧
      cartanC m b a = -1 ∧ cartanC m b c = -2 ∧ cartanC m c b = -1 ∧ cartanC m a c = 0 ∧
      cartanC m c a = 0 := by
  have hab : a ≠ b := fun h => by rw [h] at ha; omega
  have hac : a ≠ c := fun h => by rw [h] at ha; omega
  have hbc : b ≠ c := fun h => by rw [h] at hb; omega
  simp [cartanC, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  omega

theorem criterion_C (D : UniversalRootDatum K) (hcart : D.cartan = cartanC D.rank)
    (hdiv : D.divisible = ∅) {a b c : Fin D.rank} (ha : a.val + 3 = D.rank)
    (hb : b.val + 2 = D.rank) (hc : c.val + 1 = D.rank) :
    ModelFacts.IsLongestRoot D (Pi.single c 1) ∧ ∀ i : Fin D.rank,
    (Pi.single c 1 : Fin D.rank → ℤ) = Pi.single i 1 ∨
      form D.isFiniteType (toRat (Pi.single c 1)) (toRat (Pi.single i 1)) = 0 ∨
      ∃ ε, ModelFacts.IsLongestRoot D ε ∧
        form D.isFiniteType (toRat (Pi.single c 1)) (toRat ε) = 0 ∧
        form D.isFiniteType (toRat ε) (toRat (Pi.single i 1)) = 0 := by
  obtain ⟨haa, hbb, hcc, hab, hba, hbc, hcb, hac, hca⟩ := cartanC_entries ha hb hc
  have hlong : ModelFacts.IsLongestRoot D (Pi.single c 1) := by
    unfold ModelFacts.IsLongestRoot
    rw [hdiv]
    exact ModelFacts.isLongest_single_cartanC (by omega) hcart D.isFiniteType hc
  refine ⟨hlong, fun i => ?_⟩
  by_cases hic : i = c
  · exact Or.inl (by rw [hic])
  by_cases hib : i = b
  · subst hib
    set S := fun j => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hS
    have eAbc : D.cartan i c = -2 := by rw [hcart]; exact hbc
    have eAab : D.cartan a i = -1 := by rw [hcart]; exact hab
    have eAac : D.cartan a c = 0 := by rw [hcart]; exact hac
    have hε : weylAction D.isFiniteType (S a * S i) (Pi.single c 1) =
        Pi.single c 1 + (2 : ℤ) • Pi.single i 1 + (2 : ℤ) • Pi.single a 1 := by
      rw [weylAction_mul_apply, hS, weylAction_simple, weylAction_simple,
        reflection_apply_coroot D.cartan i, coroot_single, eAbc,
        reflection_apply_coroot D.cartan a]
      simp only [map_sub, map_zsmul, coroot_single, eAac, eAab, smul_eq_mul]
      module
    refine Or.inr (Or.inr ⟨weylAction D.isFiniteType (S a * S i) (Pi.single c 1),
      ModelFacts.IsLongest.map_weylAction hlong _, ?_, ?_⟩)
    · rw [form_comm]
      refine form_toRat_single_eq_zero D c _ ?_
      rw [hε]
      simp only [map_add, map_zsmul, coroot_single, smul_eq_mul]
      have e1 : D.cartan c a = 0 := by rw [hcart]; exact hca
      have e2 : D.cartan c i = -1 := by rw [hcart]; exact hcb
      have e3 : D.cartan c c = 2 := by rw [hcart]; exact hcc
      rw [e1, e2, e3]
      norm_num
    · refine form_toRat_single_eq_zero D i _ ?_
      rw [hε]
      simp only [map_add, map_zsmul, coroot_single, smul_eq_mul]
      have e1 : D.cartan i a = -1 := by rw [hcart]; exact hba
      have e3 : D.cartan i i = 2 := by rw [hcart]; exact hbb
      rw [e1, e3, eAbc]
      norm_num
  · refine Or.inr (Or.inl (form_single_eq_zero_of_cartan D ?_))
    rw [hcart]
    simp only [cartanC, Matrix.of_apply]
    have : i.val + 1 ≠ D.rank := fun h => hic (Fin.ext (by omega))
    have hi : i.val ≤ D.rank - 3 := by
      have : i.val ≠ b.val := fun h => hib (Fin.ext h)
      omega
    split_ifs <;> first | rfl | (exfalso; omega)

theorem criterion_BC (D : UniversalRootDatum K) (hcart : D.cartan = (cartanC D.rank)ᵀ)
    (hdiv : D.divisible = {j : Fin D.rank | j.val + 1 = D.rank}) {a b c : Fin D.rank}
    (ha : a.val + 3 = D.rank) (hb : b.val + 2 = D.rank) (hc : c.val + 1 = D.rank) :
    ModelFacts.IsLongestRoot D (2 • Pi.single c 1) ∧ ∀ i : Fin D.rank,
    (2 • Pi.single c 1 : Fin D.rank → ℤ) = Pi.single i 1 ∨
      form D.isFiniteType (toRat (2 • Pi.single c 1)) (toRat (Pi.single i 1)) = 0 ∨
      ∃ ε, ModelFacts.IsLongestRoot D ε ∧
        form D.isFiniteType (toRat (2 • Pi.single c 1)) (toRat ε) = 0 ∧
        form D.isFiniteType (toRat ε) (toRat (Pi.single i 1)) = 0 := by
  obtain ⟨haa, hbb, hcc, hab, hba, hbc, hcb, hac, hca⟩ := cartanC_entries ha hb hc
  have eT : ∀ i j, D.cartan i j = cartanC D.rank j i := fun i j => by rw [hcart]; rfl
  have hlong : ModelFacts.IsLongestRoot D (2 • Pi.single c 1) := by
    unfold ModelFacts.IsLongestRoot
    rw [hdiv]
    exact ModelFacts.isLongest_two_nsmul_single_BC (by omega) hcart D.isFiniteType hc
  refine ⟨hlong, fun i => Or.inr ?_⟩
  have hab' : a ≠ b := fun h => by rw [h] at ha; omega
  have hac' : a ≠ c := fun h => by rw [h] at ha; omega
  have hbc' : b ≠ c := fun h => by rw [h] at hb; omega
  by_cases hex : i = c ∨ i = b
  · set S := fun j => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hS
    have eAbc : D.cartan b c = -1 := by rw [eT]; exact hcb
    have eAab : D.cartan a b = -1 := by rw [eT]; exact hba
    have eAac : D.cartan a c = 0 := by rw [eT]; exact hca
    have hε : weylAction D.isFiniteType (S a * S b) (2 • Pi.single c 1) =
        2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1 := by
      rw [weylAction_mul_apply, hS, weylAction_simple, weylAction_simple,
        reflection_apply_coroot D.cartan b, map_nsmul, coroot_single, eAbc,
        reflection_apply_coroot D.cartan a]
      simp only [map_nsmul, map_sub, map_zsmul, coroot_single, eAac, eAab, smul_eq_mul]
      module
    have hcc' : D.cartan c c = 2 := by rw [eT]; exact hcc
    have hcb' : D.cartan c b = -2 := by rw [eT]; exact hbc
    have hca' : D.cartan c a = 0 := by rw [eT]; exact hac
    have hbb' : D.cartan b b = 2 := by rw [eT]; exact hbb
    have hba' : D.cartan b a = -1 := by rw [eT]; exact hab
    have hcorc : coroot D.cartan c (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
        (2 : ℤ) • Pi.single a 1) = 0 := by
      simp only [map_nsmul, map_add, map_zsmul, coroot_single, smul_eq_mul, hcc', hcb', hca']
      norm_num
    have hcorb : coroot D.cartan b (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 +
        (2 : ℤ) • Pi.single a 1) = 0 := by
      simp only [map_nsmul, map_add, map_zsmul, coroot_single, smul_eq_mul, eAbc, hbb', hba']
      norm_num
    refine Or.inr ⟨weylAction D.isFiniteType (S a * S b) (2 • Pi.single c 1),
      ModelFacts.IsLongest.map_weylAction hlong _, ?_, ?_⟩
    · rw [hε]
      have hform : form D.isFiniteType (toRat (Pi.single c 1))
          (toRat (2 • Pi.single c 1 + (2 : ℤ) • Pi.single b 1 + (2 : ℤ) • Pi.single a 1)) = 0 := by
        rw [form_comm]
        exact form_toRat_single_eq_zero D c _ hcorc
      simp only [map_nsmul, LinearMap.smul_apply, hform, smul_zero]
    · rw [hε]
      rcases hex with rfl | rfl
      · exact form_toRat_single_eq_zero D _ _ hcorc
      · exact form_toRat_single_eq_zero D _ _ hcorb
  · refine Or.inl ?_
    have hic : i ≠ c := fun h => hex (Or.inl h)
    have hib : i ≠ b := fun h => hex (Or.inr h)
    have h0 : D.cartan c i = 0 := by
      rw [eT]
      simp only [cartanC, Matrix.of_apply]
      have : i.val + 1 ≠ D.rank := fun h => hic (Fin.ext (by omega))
      have hi : i.val ≤ D.rank - 3 := by
        have : i.val ≠ b.val := fun h => hib (Fin.ext h)
        omega
      split_ifs <;> first | rfl | (exfalso; omega)
    have := form_single_eq_zero_of_cartan D h0
    simp only [map_nsmul, LinearMap.smul_apply, this, smul_zero]

end Criteria

section Models

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_psp {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSp n p e)
    (hn : 3 ≤ n) : CommFamilyConnected (ModelFund p .PSp n e) := by
  refine commFamilyConnected_modelFund_of_criterion hp2 trivial hadm (by decide) (by decide) ?_
  have key := criterion_C (modelUniv .PSp n p e Fact.out).D rfl rfl
    (a := ⟨n - 3, by show n - 3 < n; omega⟩) (b := ⟨n - 2, by show n - 2 < n; omega⟩)
    (c := ⟨n - 1, by show n - 1 < n; omega⟩) (by show n - 3 + 3 = n; omega)
    (by show n - 2 + 2 = n; omega) (by show n - 1 + 1 = n; omega)
  exact ⟨_, key.1, key.2⟩

theorem commFamilyConnected_psu_even {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p e) (he : Even n) (hn : 6 ≤ n) :
    CommFamilyConnected (ModelFund p .PSU n e) := by
  refine commFamilyConnected_modelFund_of_criterion hp2 trivial hadm (by decide) (by decide) ?_
  have hf : 1 ≤ e := hadm.2.1
  have h : modelUniv .PSU n p e Fact.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
        Unitary.rootDatum (card_galoisField_two_mul p e hf) n⟩ :=
    ModelFacts.modelUniv_PSU hf
  generalize modelUniv .PSU n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hc, hd⟩ := ModelFacts.unitary_even he
  have key := criterion_C (Unitary.rootDatum (card_galoisField_two_mul p e hf) n) hc hd
    (a := ⟨n / 2 - 3, by show n / 2 - 3 < n / 2; omega⟩)
    (b := ⟨n / 2 - 2, by show n / 2 - 2 < n / 2; omega⟩)
    (c := ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩) (by show n / 2 - 3 + 3 = n / 2; omega)
    (by show n / 2 - 2 + 2 = n / 2; omega) (by show n / 2 - 1 + 1 = n / 2; omega)
  exact ⟨_, key.1, key.2⟩

theorem commFamilyConnected_psu_odd {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p e) (ho : ¬ Even n) (hn : 7 ≤ n) :
    CommFamilyConnected (ModelFund p .PSU n e) := by
  refine commFamilyConnected_modelFund_of_criterion hp2 trivial hadm (by decide) (by decide) ?_
  have hf : 1 ≤ e := hadm.2.1
  have h : modelUniv .PSU n p e Fact.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
        Unitary.rootDatum (card_galoisField_two_mul p e hf) n⟩ :=
    ModelFacts.modelUniv_PSU hf
  generalize modelUniv .PSU n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hc, hd⟩ := ModelFacts.unitary_odd ho
  have key := criterion_BC (Unitary.rootDatum (card_galoisField_two_mul p e hf) n) hc hd
    (a := ⟨n / 2 - 3, by show n / 2 - 3 < n / 2; omega⟩)
    (b := ⟨n / 2 - 2, by show n / 2 - 2 < n / 2; omega⟩)
    (c := ⟨n / 2 - 1, by show n / 2 - 1 < n / 2; omega⟩) (by show n / 2 - 3 + 3 = n / 2; omega)
    (by show n / 2 - 2 + 2 = n / 2; omega) (by show n / 2 - 1 + 1 = n / 2; omega)
  exact ⟨_, key.1, key.2⟩

end Models

end CFSG.ClassicalInvolution.RouteD
