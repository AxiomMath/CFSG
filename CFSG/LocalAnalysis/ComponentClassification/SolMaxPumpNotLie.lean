module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpAltComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpOrders

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixedSubgroup_conj_eq {X : Type*} [Group X] (t : X) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set X) := by
  ext x
  rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_centralizer_singleton_iff,
    MulAut.conj_apply]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [h]
      _ = x := by group

theorem card_of_mulEquiv_alt {X : Type*} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : Nat.card X = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem not_lieModel_of_mulEquiv_alt
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m) (e : X ≃* alternatingGroup (Fin m)) {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) : ¬ LieModel X t n p f := by
  intro hX
  have hcard := card_of_mulEquiv_alt (by omega) e
  rcases (show m = 7 ∨ m = 9 ∨ 11 ≤ m by obtain ⟨r, rfl⟩ := hm; omega) with rfl | rfl | hm11
  · exact lieModel_card_ne_alt_seven hO hadm hX (by rw [hcard]; decide)
  · exact lieModel_card_ne_alt_nine hO hadm hX (by rw [hcard]; decide)
  obtain ⟨k, hk, hk4, h4⟩ : ∃ k : ℕ, (k = 7 ∨ k = 9) ∧ k + 4 ≤ m ∧ 4 ∣ m - k := by
    obtain ⟨r, rfl⟩ := hm
    rcases Nat.even_or_odd r with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact ⟨9, Or.inr rfl, by omega, ⟨s - 2, by omega⟩⟩
    · exact ⟨7, Or.inl rfl, by omega, ⟨s - 1, by omega⟩⟩
  obtain ⟨u, hu, B, hB, ⟨eB⟩⟩ :=
    exists_component_of_mulEquiv_alt e (by rcases hk with rfl | rfl <;> norm_num) hk4 h4
  have hBcard : Nat.card B = k.factorial / 2 :=
    card_of_mulEquiv_alt (by rcases hk with rfl | rfl <;> norm_num) eB
  by_cases hp2 : p = 2
  ·
    subst hp2
    exact involutionCentralizersComponentFree_of_evenLieType ⟨t, n, f, hadm, hX⟩ u hu B hB
  have hZX : center X = ⊥ := by
    have : IsSimpleGroup (alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    have : IsSimpleGroup X := e.isSimpleGroup
    obtain ⟨a, b, hab⟩ := alt_nonabelian_of_card (Ω := Fin m) (by rw [Nat.card_fin]; omega)
    exact center_eq_bot_of_simple ⟨e.symm a, e.symm b, fun h =>
      hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  have hα : orderOf (MulAut.conj u) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
    · intro h
      apply hu1
      have hc : u ∈ center X := by
        rw [mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut X => φ g) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * u = u * g * u⁻¹ * u := by rw [h1]
          _ = u * g := by group
      rwa [hZX, mem_bot] at hc
  have hfix := fixedSubgroup_conj_eq u
  let eF : ↥(fixedSubgroup (MulAut.conj u)) ≃* ↥(centralizer ({u} : Set X)) :=
    MulEquiv.subgroupCongr hfix
  have hB' : IsComponent (B.map eF.symm.toMonoidHom) := isComponent_map_mulEquiv eF.symm hB
  let eB' : ↥(B.map eF.symm.toMonoidHom) ≃* alternatingGroup (Fin k) :=
    (B.equivMapOfInjective eF.symm.toMonoidHom eF.symm.injective).symm.trans eB
  have hB'card : Nat.card ↥(B.map eF.symm.toMonoidHom) = k.factorial / 2 :=
    card_of_mulEquiv_alt (by rcases hk with rfl | rfl <;> norm_num) eB'
  have hsimp : IsSimpleGroup ↥(B.map eF.symm.toMonoidHom) := by
    have : IsSimpleGroup (alternatingGroup (Fin k)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; rcases hk with rfl | rfl <;> norm_num)
    exact eB'.isSimpleGroup
  have hZB : center ↥(B.map eF.symm.toMonoidHom) = ⊥ := by
    obtain ⟨a, b, hab⟩ := alt_nonabelian_of_card (Ω := Fin k)
      (by rw [Nat.card_fin]; rcases hk with rfl | rfl <;> norm_num)
    exact center_eq_bot_of_simple ⟨eB'.symm a, eB'.symm b, fun h =>
      hab (eB'.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hQcard : Nat.card (↥(B.map eF.symm.toMonoidHom) ⧸ center ↥(B.map eF.symm.toMonoidHom)) =
      k.factorial / 2 := by
    rw [← hB'card, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZB).trans
      QuotientGroup.quotientBot).toEquiv]
  rcases hGLS X t n p f hadm.1 hp2 hadm hX (MulAut.conj u) hα _ hB' with
    ⟨t', n', f', hadm', hm'⟩ | ⟨-, -, -, h8⟩
  · rcases hk with rfl | rfl
    · exact lieModel_card_ne_alt_seven hO hadm' hm' (by rw [hQcard]; decide)
    · exact lieModel_card_ne_alt_nine hO hadm' hm' (by rw [hQcard]; decide)
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    rw [hB'card] at h504
    rcases hk with rfl | rfl <;> revert h504 <;> decide

end CFSG.ComponentClassification.SolMax
