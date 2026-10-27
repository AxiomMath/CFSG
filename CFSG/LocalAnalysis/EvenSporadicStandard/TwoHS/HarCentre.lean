module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarSylowE

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

theorem card_map_mul_card_inf_ker {G N : Type*} [Group G] [Group N] [Finite G] (f : G →* N)
    (K : Subgroup G) :
    Nat.card (K.map f) * Nat.card ↥(K ⊓ f.ker) = Nat.card K := by
  have h := Subgroup.card_ker_mul_card_range (f.comp K.subtype)
  have hr : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card (f.comp K.subtype).ker = Nat.card ↥(K ⊓ f.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, (Subgroup.mem_inf.1 y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hr, hk] at h
  rw [mul_comm]
  exact h

section Elements

variable
  {E : Type} [Group E]

theorem CoverMaps.ker_pi_eq (M : CoverMaps E) : M.π.ker = center E := by
  ext x
  rw [MonoidHom.mem_ker]
  exact M.π_ker x

theorem CoverMaps.tE_ne_one (M : CoverMaps E) : M.tE ≠ 1 :=
  fun h => M.rho_tE_ne (by rw [h, map_one])

theorem CoverMaps.mem_center_iff (M : CoverMaps E) (hZ : Nat.card (center E) = 2) {x : E} :
    x ∈ center E ↔ x = 1 ∨ x = M.tE := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center E))).1 hZ
      have h1 : (⟨x, hx⟩ : ↥(center E)) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
      have h2 : (⟨M.tE, M.tE_mem_center⟩ : ↥(center E)) = y :=
        hy _ (fun h => M.tE_ne_one (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact M.tE_mem_center

end Elements

section Words

variable
  {E : Type} [Group E]

theorem CoverMaps.uE_length (M : CoverMaps E) : M.uE.length = 3 := by
  have h := congrArg List.length M.uE_rho
  simpa [harU_length] using h

theorem CoverMaps.wordVal_uE_mem (M : CoverMaps E) {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    wordVal M.uE w ∈ M.T0 := by
  unfold wordVal
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h1, h2⟩ := hw l hl
  have hlen := M.uE_length
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact Subgroup.subset_closure (List.getElem_mem _)

theorem CoverMaps.cgens_comm (M : CoverMaps E) {x : E} (hx : x ∈ M.cgens) :
    ∃ a ∈ M.T0, ∃ b ∈ M.T0, x = ⁅a, b⁆ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  have hl := harCPairs_letters p hp
  exact ⟨_, M.wordVal_uE_mem hl.1, _, M.wordVal_uE_mem hl.2, rfl⟩

theorem CoverMaps.T0'_le_commutator (M : CoverMaps E) : M.T0' ≤ ⁅M.T0, M.T0⁆ := by
  rw [CoverMaps.T0', Subgroup.closure_le]
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := M.cgens_comm hx
  exact Subgroup.commutator_mem_commutator ha hb

end Words

section Sylow

variable
  {E : Type} [Group E]
  (M : CoverModel E)

theorem CoverModel.tE_sq : M.tE ^ 2 = 1 := by
  apply M.ρ_inj
  rw [map_pow, map_one, pow_two]
  exact (harC_sq M.rep_tE).1

theorem CoverModel.z1E_sq : M.z1E ^ 2 = 1 := by
  apply M.ρ_inj
  rw [map_pow, map_one]
  have h := harZ1_order M.rep_z1E
  have h2 := pow_orderOf_eq_one (M.ρ M.z1E)
  rwa [h] at h2

theorem CoverModel.z1E_ne_tE : M.z1E ≠ M.tE :=
  fun h => (harZ_distinct M.rep_tE M.rep_z1E).1 (congrArg M.ρ h)

theorem CoverModel.z1E_ne_one : M.z1E ≠ 1 :=
  fun h => (harZ_distinct M.rep_tE M.rep_z1E).2.2.1 (by rw [h, map_one])

theorem CoverModel.tE_mul_z1E_ne_z1E : M.tE * M.z1E ≠ M.z1E :=
  fun h => (harZ_distinct M.rep_tE M.rep_z1E).2.1 (by rw [← map_mul, h])

theorem CoverModel.tE_mul_z1E_ne_tE : M.tE * M.z1E ≠ M.tE :=
  fun h => (harZ_distinct M.rep_tE M.rep_z1E).2.2.2.1 (by rw [← map_mul, h])

theorem CoverModel.tE_mul_z1E_ne_one : M.tE * M.z1E ≠ 1 :=
  fun h => (harZ_distinct M.rep_tE M.rep_z1E).2.2.2.2 (by rw [← map_mul, h, map_one])

theorem CoverModel.tE_mem_T0 : M.tE ∈ M.T0 := by
  rw [← Subgroup.mem_map_iff_mem M.ρ_inj, M.map_T0]
  exact harC_mem_harT0 M.rep_tE

theorem CoverModel.z1E_mem_T0 : M.z1E ∈ M.T0 := by
  rw [← Subgroup.mem_map_iff_mem M.ρ_inj, M.map_T0]
  exact harZ1_mem_harT0 M.rep_z1E

theorem CoverModel.z1E_comm : ∀ y ∈ M.T0, M.z1E * y = y * M.z1E := by
  have hcl : M.T0 ≤ centralizer ({M.z1E} : Set E) := by
    rw [CoverMaps.T0, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hx' : M.ρ x ∈ M.uE.map M.ρ := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [M.uE_rho] at hx'
    obtain ⟨g, hg, hgx⟩ := List.mem_map.1 hx'
    apply M.ρ_inj
    rw [map_mul, map_mul, ← hgx]
    exact (harZ1_comm M.rep_z1E g hg).symm
  intro y hy
  exact (mem_centralizer_singleton_iff.1 (hcl hy)).symm

theorem CoverModel.map_centre :
    (M.T0 ⊓ centralizer (M.T0 : Set E)).map M.ρ =
      harT0 ⊓ centralizer (harT0 : Set (Equiv.Perm (Fin 11200))) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨x, ⟨hxT, hxc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← M.map_T0]
      exact Subgroup.mem_map_of_mem _ hxT
    · intro h hh
      rw [← M.map_T0] at hh
      obtain ⟨y', hy', rfl⟩ := hh
      rw [← map_mul, ← map_mul, hxc y' hy']
  · rintro ⟨hyT, hyc⟩
    rw [← M.map_T0] at hyT
    obtain ⟨x, hxT, rfl⟩ := hyT
    refine ⟨x, ⟨hxT, fun y' hy' => ?_⟩, rfl⟩
    apply M.ρ_inj
    rw [map_mul, map_mul]
    exact hyc (M.ρ y') (by rw [← M.map_T0]; exact Subgroup.mem_map_of_mem _ hy')

theorem CoverModel.card_centre : Nat.card ↥(M.T0 ⊓ centralizer (M.T0 : Set E)) = 4 := by
  rw [← Subgroup.card_map_of_injective M.ρ_inj, M.map_centre]
  exact harT0_centre_card

theorem CoverModel.centre_T0 {x : E} (hx : x ∈ M.T0) (hc : ∀ y ∈ M.T0, x * y = y * x) :
    x = 1 ∨ x = M.tE ∨ x = M.z1E ∨ x = M.tE * M.z1E := by
  classical
  set Z := M.T0 ⊓ centralizer (M.T0 : Set E) with hZ
  have hcard : Nat.card Z = 4 := M.card_centre
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hmem : ∀ a, a ∈ M.T0 → (∀ y ∈ M.T0, a * y = y * a) → a ∈ (Z : Set E) := by
    intro a ha hac
    refine Subgroup.mem_inf.2 ⟨ha, mem_centralizer_iff.2 fun h hh => ?_⟩
    exact (hac h hh).symm
  have hcentral : ∀ a, a ∈ center E → a ∈ M.T0 → a ∈ (Z : Set E) := by
    intro a ha haT
    exact hmem a haT fun y _ => ((Subgroup.mem_center_iff.1 ha) y).symm
  have hzt : M.tE ∈ (Z : Set E) := hcentral _ M.tE_mem_center M.tE_mem_T0
  have hz1 : M.z1E ∈ (Z : Set E) := hmem _ M.z1E_mem_T0 (fun y hy => M.z1E_comm y hy)
  have hz2 : M.tE * M.z1E ∈ (Z : Set E) := by
    refine hmem _ (mul_mem M.tE_mem_T0 M.z1E_mem_T0) fun y hy => ?_
    rw [mul_assoc, M.z1E_comm y hy, ← mul_assoc, ← mul_assoc,
      ((Subgroup.mem_center_iff.1 M.tE_mem_center) y)]
  let A : Finset E := {1, M.tE, M.z1E, M.tE * M.z1E}
  have hAcard : A.card = 4 := by
    have h1 : (1 : E) ∉ ({M.tE, M.z1E, M.tE * M.z1E} : Finset E) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(M.tE_ne_one).symm, M.z1E_ne_one.symm, M.tE_mul_z1E_ne_one.symm⟩
    have h2 : M.tE ∉ ({M.z1E, M.tE * M.z1E} : Finset E) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨M.z1E_ne_tE.symm, M.tE_mul_z1E_ne_tE.symm⟩
    have h3 : M.z1E ∉ ({M.tE * M.z1E} : Finset E) := by
      simp only [Finset.mem_singleton]
      exact M.tE_mul_z1E_ne_z1E.symm
    simp only [A]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hsub : (A : Set E) ⊆ (Z : Set E) := by
    intro a ha
    simp only [A, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_mem Z
    · exact hzt
    · exact hz1
    · exact hz2
  have hZc : (Z : Set E).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hAc : (A : Set E).ncard = 4 := by
    rw [Set.ncard_coe_finset, hAcard]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hxZ : x ∈ (Z : Set E) := hmem x hx hc
  rw [← heq] at hxZ
  simp only [A, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hxZ
  tauto

theorem factorization_two_card_E : (88704000 : ℕ).factorization 2 = 10 := by
  have h : (88704000 : ℕ) = 2 ^ 10 * 86625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem CoverModel.eq_of_le_isPGroup [Finite E] (hcard : Nat.card E = 88704000) {Q : Subgroup E}
    (hQ : IsPGroup 2 Q) (hle : M.T0 ≤ Q) : Q = M.T0 :=
  (Sylow.ofCard (p := 2) M.T0
    (by rw [M.card_T0, hcard, factorization_two_card_E]; norm_num)).is_maximal' hQ hle

theorem CoverModel.isPGroup_T0 : IsPGroup 2 M.T0 :=
  IsPGroup.of_card (n := 10) (by rw [M.card_T0]; norm_num)

theorem CoverMaps.ker_le_of_tE_mem (M : CoverMaps E) (hZ : Nat.card (center E) = 2)
    {K : Subgroup E} (ht : M.tE ∈ K) : M.π.ker ≤ K := by
  intro x hx
  rw [M.ker_pi_eq] at hx
  rcases (M.mem_center_iff hZ).1 hx with rfl | rfl
  · exact one_mem K
  · exact ht

theorem CoverMaps.card_ker_pi (M : CoverMaps E) (hZ : Nat.card (center E) = 2) :
    Nat.card M.π.ker = 2 := by
  rw [M.ker_pi_eq]
  exact hZ

theorem CoverMaps.card_map_pi [Finite E] (M : CoverMaps E) (hZ : Nat.card (center E) = 2)
    {K : Subgroup E} (ht : M.tE ∈ K) : Nat.card (K.map M.π) * 2 = Nat.card K := by
  have h := card_map_mul_card_inf_ker M.π K
  rw [inf_eq_right.2 (M.ker_le_of_tE_mem hZ ht), M.card_ker_pi hZ] at h
  exact h

theorem CoverModel.card_map_pi_T0 [Finite E] (hZ : Nat.card (center E) = 2) :
    Nat.card (M.T0.map M.π) = 512 := by
  have h := M.card_map_pi hZ M.tE_mem_T0
  rw [M.card_T0] at h
  omega

theorem CoverModel.card_map_pi_T0' [Finite E] (hZ : Nat.card (center E) = 2) :
    Nat.card (M.T0'.map M.π) = 64 := by
  have h := M.card_map_pi hZ M.tE_mem_T0'
  rw [M.card_T0'] at h
  omega

end Sylow

end CFSG.EvenSporadicStandard.TwoHS
