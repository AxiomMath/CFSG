module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.DegreeTwelveSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.ThreeCentralizerSymmetricLocal
public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem card_orderOf_eq_one (A : Type*) [Group A] :
    Nat.card {x : A // orderOf x = 1} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, orderOf_one⟩⟩⟩
  rw [orderOf_eq_one_iff.mp x.2, orderOf_eq_one_iff.mp y.2]

theorem card_orderOf_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) (d : ℕ) :
    Nat.card {x : A // orderOf x = d} = Nat.card {y : B // orderOf y = d} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show orderOf x = d ↔ orderOf (e x) = d
    rw [MulEquiv.orderOf_eq])

theorem degree_twelve_character_thirteen_point_action_core {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 5616) (t : G) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (a : G) (haC : a ∈ Subgroup.centralizer ({t} : Set G)) (ha : orderOf a = 3)
    (hCa : Nat.card (Subgroup.centralizer ({a} : Set G)) = 54)
    (P : Subgroup G) (hPa : P ≤ Subgroup.centralizer ({a} : Set G)) (hP : Nat.card P = 27)
    (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 12)
    (hgap : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ → ∃ d : ℕ, 12 < d ∧ ψ 1 = d)
    (hfaith : ∀ g, χ g = 12 → g = 1)
    (h2 : ∀ g, orderOf g = 2 → χ g = 4)
    (h3 : ∀ g, orderOf g = 3 → χ g = 0 ∨ χ g = 3)
    (h489 : ∀ g, orderOf g = 4 ∨ orderOf g = 8 ∨ orderOf g = 9 → χ g = 0)
    (h6 : ∀ g, orderOf g = 6 → χ g = 1) :
    ∃ M : Subgroup G, Nonempty (M ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      Nat.card (M ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 12 ∧
      (M ⊔ Subgroup.centralizer ({t} : Set G)).index = 13 ∧
      (∀ g : G, (∀ x : G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G)), g • x = x) → g = 1) ∧
      MulAction.IsMultiplyPretransitive G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) 2 ∧
      fixedPointCount G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) = 1 + χ := by
  obtain ⟨φ⟩ := hC
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  have hχ' := hχ
  obtain ⟨V, _, _, _, ρ, hρirr, hρχ⟩ := hχ'
  have hcls : ∀ g h : G, χ (h * g * h⁻¹) = χ g := fun g h => by
    rw [← hρχ]
    exact Representation.char_conj ρ g h
  obtain ⟨-, b, l, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMiso, hM36, hMC, -, hT12, hM2, hM3,
    hM6, hT2, hT3, hT6⟩ := three_centralizer_produces_two_S3_local_subgroups t ht ⟨φ⟩ a haC ha
      hCa P hPa hP hexp
  set M := Subgroup.closure ({a, l, t, b} : Set G) with hMdef
  set T := Subgroup.closure ({a, b, t} : Set G) with hTdef
  have haM : a ∈ M := Subgroup.subset_closure (by simp)
  have hTM : T ≤ M := by rw [← hMC]; exact inf_le_left
  have hTC : T ≤ C := by rw [← hMC]; exact inf_le_right
  have hMorders : ∀ x : M, orderOf x ∈ ({1, 2, 3, 6} : Finset ℕ) :=
    orderOf_mem_of_card_sum _ (by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton, card_orderOf_eq_one, hM2, hM3, hM6,
        hM36]; norm_num)
  have hTorders : ∀ x : T, orderOf x ∈ ({1, 2, 3, 6} : Finset ℕ) :=
    orderOf_mem_of_card_sum _ (by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton, card_orderOf_eq_one, hT2, hT3, hT6,
        hT12]; norm_num)
  have hprof := GL2_three_element_profile_and_derived_subgroup
  dsimp only at hprof
  obtain ⟨hH48, -, -, -, -, -, -, -, -, hH2, hH3, hH4, hH6, hH8, hHorders, hHconj, -⟩ := hprof
  have hCcount : ∀ d, Nat.card {x : C // orderOf x = d} =
      Nat.card {g : GL (Fin 2) (ZMod 3) // orderOf g = d} := card_orderOf_congr φ
  have hCorders : ∀ x : C, orderOf x ∈ ({1, 2, 3, 4, 6, 8} : Finset ℕ) := fun x => by
    rw [← MulEquiv.orderOf_eq φ]
    exact hHorders (φ x)
  have hC48 : Nat.card C = 48 := by rw [Nat.card_congr φ.toEquiv, hH48]
  have hone_val : ∀ {A : Subgroup G} (x : A), orderOf x = 1 → χ x = 12 := by
    intro A x hx
    rw [orderOf_eq_one_iff.mp hx]
    simpa using hχ1
  have hfinM := finrank_invariants_subgroup ρ M
  have hfinC := finrank_invariants_subgroup ρ C
  have hfinT := finrank_invariants_subgroup ρ T
  rw [hρχ] at hfinM hfinC hfinT
  set n := (Finset.univ.filter fun x : M => orderOf x = 3 ∧ χ x = 3).card with hn
  have hsplitM : ∑ x : M, χ x = 84 + 3 * n := by
    have hsplit : ∑ x : M, χ x = ∑ x : M, (if orderOf x = 3 then 0 else χ x) +
        ∑ x : M, (if orderOf x = 3 then χ x else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    have hA : ∑ x : M, (if orderOf x = 3 then 0 else χ x) = 84 := by
      rw [sum_eq_sum_orders _ _ hMorders (fun d => if d = 3 then 0 else if d = 1 then 12
        else if d = 2 then 4 else 1)]
      · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton, card_orderOf_eq_one, hM2, hM3,
          hM6]
        norm_num
      · intro x
        have hx := hMorders x
        have hx' : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx
        · simp [hx, hone_val x hx]
        · simp [hx, h2 _ (hx'.trans hx)]
        · simp [hx]
        · simp [hx, h6 _ (hx'.trans hx)]
    have hB : ∑ x : M, (if orderOf x = 3 then χ x else 0) = 3 * n := by
      rw [hn, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : orderOf x = 3
      · have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
        rcases h3 _ hx' with h0 | h3'
        · simp [hx, h0]
        · simp [hx, h3']
      · simp [hx]
    rw [hsplit, hA, hB]
  have hsub3 : (Finset.univ.filter fun x : M => orderOf x = 3 ∧ χ x = 3) ⊆
      Finset.univ.filter fun x : M => orderOf x = 3 := fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩
  have hcard3 : (Finset.univ.filter fun x : M => orderOf x = 3).card = 8 := by
    rw [← hM3, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hn8 : n ≤ 8 := by
    rw [hn, ← hcard3]
    exact Finset.card_le_card hsub3
  have hMdim : Module.finrank ℂ (Representation.invariants (ρ.comp M.subtype)) = 3 ∧ n = 8 := by
    rw [hsplitM, hM36] at hfinM
    have hnat : (Module.finrank ℂ (Representation.invariants (ρ.comp M.subtype)) : ℂ) * 36 =
        84 + 3 * n := by
      rw [← hfinM]
      field_simp
      push_cast
      ring
    have hnat' : Module.finrank ℂ (Representation.invariants (ρ.comp M.subtype)) * 36 =
        84 + 3 * n := by exact_mod_cast hnat
    omega
  have hM3all : ∀ x : M, orderOf x = 3 → χ x = 3 := by
    intro x hx
    by_contra hne
    have hlt : n < (Finset.univ.filter fun x : M => orderOf x = 3).card := by
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub3, fun heq => ?_⟩)
      have : x ∈ Finset.univ.filter fun x : M => orderOf x = 3 ∧ χ x = 3 := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      exact hne (Finset.mem_filter.mp this).2.2
    rw [hcard3, hMdim.2] at hlt
    exact lt_irrefl _ hlt
  have hχa : χ a = 3 := hM3all ⟨a, haM⟩ (by rw [Subgroup.orderOf_mk]; exact ha)
  have hC3 : ∀ x : C, orderOf x = 3 → χ x = 3 := by
    intro x hx
    have hxφ : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    have haφ : orderOf (φ ⟨a, haC⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact ha
    obtain ⟨c, hc⟩ := isConj_iff.mp (hHconj _ _ haφ hxφ)
    have h : x = φ.symm c * ⟨a, haC⟩ * (φ.symm c)⁻¹ := by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hc]
    have hxc : (x : G) = ((φ.symm c : C) : G) * a * ((φ.symm c : C) : G)⁻¹ := by
      rw [h]
      rfl
    rw [hxc, hcls, hχa]
  have hsumC : ∑ x : C, χ x = 96 := by
    rw [sum_eq_sum_orders _ _ hCorders (fun d => if d = 1 then 12 else if d = 2 then 4
      else if d = 3 then 3 else if d = 6 then 1 else 0)]
    · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton, card_orderOf_eq_one, hCcount 2,
        hCcount 3, hCcount 4, hCcount 6, hCcount 8, hH2, hH3, hH4, hH6, hH8]
      norm_num
    · intro x
      have hx := hCorders x
      have hx' : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx | hx | hx
      · simp [hx, hone_val x hx]
      · simp [hx, h2 _ (hx'.trans hx)]
      · simp [hx, hC3 x hx]
      · simp [hx, h489 _ (Or.inl (hx'.trans hx))]
      · simp [hx, h6 _ (hx'.trans hx)]
      · simp [hx, h489 _ (Or.inr (Or.inl (hx'.trans hx)))]
  have hsumT : ∑ x : T, χ x = 48 := by
    rw [sum_eq_sum_orders _ _ hTorders (fun d => if d = 1 then 12 else if d = 2 then 4
      else if d = 3 then 3 else 1)]
    · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton, card_orderOf_eq_one, hT2, hT3, hT6]
      norm_num
    · intro x
      have hx := hTorders x
      have hx' : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx
      · simp [hx, hone_val x hx]
      · simp [hx, h2 _ (hx'.trans hx)]
      · have h3M : orderOf (⟨x, hTM x.2⟩ : M) = 3 := by
          rw [Subgroup.orderOf_mk]
          exact hx'.trans hx
        have := hM3all ⟨x, hTM x.2⟩ h3M
        simp [hx, this]
      · simp [hx, h6 _ (hx'.trans hx)]
  have hCdim : Module.finrank ℂ (Representation.invariants (ρ.comp C.subtype)) = 2 := by
    rw [hsumC, hC48] at hfinC
    have h : (Module.finrank ℂ (Representation.invariants (ρ.comp C.subtype)) : ℂ) = 2 := by
      rw [← hfinC]
      norm_num
    exact_mod_cast h
  have hTdim : Module.finrank ℂ (Representation.invariants (ρ.comp T.subtype)) = 4 := by
    rw [hsumT, hT12] at hfinT
    have h : (Module.finrank ℂ (Representation.invariants (ρ.comp T.subtype)) : ℂ) = 4 := by
      rw [← hfinT]
      norm_num
    exact_mod_cast h
  set J := M ⊔ C with hJdef
  have hJpos : 0 < Module.finrank ℂ (Representation.invariants (ρ.comp J.subtype)) := by
    have hle : Representation.invariants (ρ.comp M.subtype) ⊓
        Representation.invariants (ρ.comp C.subtype) ≤
        Representation.invariants (ρ.comp J.subtype) := invariants_inf_le_sup ρ M C
    have hsup : Representation.invariants (ρ.comp M.subtype) ⊔
        Representation.invariants (ρ.comp C.subtype) ≤
        Representation.invariants (ρ.comp T.subtype) :=
      sup_le (invariants_le_of_le ρ hTM) (invariants_le_of_le ρ hTC)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (Representation.invariants (ρ.comp M.subtype))
      (Representation.invariants (ρ.comp C.subtype))
    have h1 := Submodule.finrank_mono hsup
    have h2' := Submodule.finrank_mono hle
    rw [hMdim.1, hCdim] at hdim
    rw [hTdim] at h1
    omega
  have hJne : J ≠ ⊤ := by
    intro hJtop
    have hle : Representation.invariants (ρ.comp J.subtype) ≤
        Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) :=
      invariants_le_of_le ρ (le_of_eq hJtop.symm)
    have hχne : ρ.character ≠ 1 := by
      rw [hρχ]
      intro h
      have := congrFun h 1
      rw [hχ1, Pi.one_apply] at this
      norm_num at this
    have h0 := finrank_invariants_top_eq_zero ρ (hρχ ▸ hχ) hχne
    have := Submodule.finrank_mono hle
    omega
  have hMJ : M ≤ J := le_sup_left
  have hCJ : C ≤ J := le_sup_right
  have h36 : 36 ∣ Nat.card J := hM36 ▸ Subgroup.card_dvd_of_le hMJ
  have h48 : 48 ∣ Nat.card J := hC48 ▸ Subgroup.card_dvd_of_le hCJ
  have hidx := J.card_mul_index
  rw [hG] at hidx
  have h144 : 144 ∣ Nat.card J := by
    have h := Nat.lcm_dvd h36 h48
    rwa [show Nat.lcm 36 48 = 144 by norm_num] at h
  obtain ⟨k, hk⟩ := h144
  have hk39 : k * J.index = 39 := by
    have h : 144 * (k * J.index) = 144 * 39 := by
      rw [← mul_assoc, ← hk, hidx]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hidx1 : J.index ≠ 1 := fun h => hJne (Subgroup.index_eq_one.mp h)
  have hrel : C.relIndex J * 48 = Nat.card J := by
    have h := Subgroup.relIndex_mul_card C J
    rwa [inf_eq_left.mpr hCJ, hC48] at h
  have hrel3 : C.relIndex J ≠ 3 := relIndex_ne_three_of_GL2_centralizer t ht ⟨φ⟩ J hCJ
  let data : FiniteComplexRepresentation.{0, 0} G :=
    { vector := G ⧸ J → ℂ, representation := permutationRepresentation G (G ⧸ J) }
  have hdatachar : data.character = fixedPointCount G (G ⧸ J) :=
    funext permutationRepresentation_character
  have horbits : Nat.card (MulAction.orbitRel.Quotient G (G ⧸ J)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨Quotient.mk _ (Classical.arbitrary _)⟩⟩
    obtain ⟨i, rfl⟩ := Quotient.exists_rep x
    obtain ⟨j, rfl⟩ := Quotient.exists_rep y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G j i
    exact Quotient.sound ⟨g, hg⟩
  have hone : characterPairing data.character 1 = 1 := by
    rw [hdatachar]
    have h := blocksInnerProduct_fixedPointCount_one (W := G) (I := G ⧸ J)
    rw [horbits, Nat.cast_one] at h
    rw [← h]
    simp [characterPairing, CFSG.BlocksInnerProduct]
  obtain ⟨hdeg13, hdecomp⟩ := permutation_constituents_of_degree_gap data χ hgap hχ1 hone
  have hdimdata : Module.finrank ℂ data.vector = J.index := by
    change Module.finrank ℂ (G ⧸ J → ℂ) = J.index
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, Subgroup.index]
  have hdata1 : data.character 1 = J.index := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdimdata]
  have hidx13 : J.index = 13 := by
    have hne1 : data.character 1 ≠ 1 := by
      rw [hdata1]
      exact_mod_cast hidx1
    have h13 := hdeg13 hne1
    rw [hdimdata] at h13
    have hdvd : J.index ∣ 39 := ⟨k, by rw [← hk39]; ring⟩
    have hmem : J.index ∈ Nat.divisors 39 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 39 = {1, 3, 13, 39} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · omega
    · omega
    · exact h
    · exfalso
      have hJ144 : Nat.card J = 144 := by
        rw [h] at hidx
        omega
      exact hrel3 (by omega)
  have hπ : fixedPointCount G (G ⧸ J) = 1 + χ := by
    rw [← hdatachar]
    exact hdecomp (by rw [hdimdata, hidx13])
  refine ⟨M, hMiso, by rw [hMC, hT12], hidx13, fun g hg => ?_, ?_, hπ⟩
  ·
    apply hfaith
    have hfix : fixedPointCount G (G ⧸ J) g = 13 := by
      rw [fixedPointCount]
      have : MulAction.fixedBy (G ⧸ J) g = Set.univ := Set.eq_univ_of_forall fun x => hg x
      rw [this, Nat.card_univ, ← Subgroup.index, hidx13]
      norm_num
    have h := congrFun hπ g
    rw [hfix, Pi.add_apply, Pi.one_apply] at h
    linear_combination -h
  ·
    have hcard : 2 ≤ Nat.card (G ⧸ J) := by
      rw [← Subgroup.index, hidx13]
      norm_num
    obtain ⟨-, -, -, h2t⟩ := permutation_character_orbit_count G (G ⧸ J)
    rw [h2t inferInstance hcard, hπ]
    simpa using hχ

end CFSG.Semidihedral.GL2Recognition
