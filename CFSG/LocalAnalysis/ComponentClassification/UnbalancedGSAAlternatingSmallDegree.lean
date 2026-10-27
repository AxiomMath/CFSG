module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASmallReeExclusion
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

namespace AlternatingModel

theorem swap_mul_swap_mem_alternatingGroup {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hcd]
  decide

theorem exists_elementaryAbelian_eight {n : ℕ} (h : 8 ≤ n) :
    ∃ E : Subgroup (alternatingGroup (Fin n)), IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x : alternatingGroup (Fin 8) :=
    ⟨swap 0 1 * swap 2 3, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩
  let y : alternatingGroup (Fin 8) :=
    ⟨swap 0 2 * swap 1 3, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩
  let t : alternatingGroup (Fin 8) :=
    ⟨swap 4 5 * swap 6 7, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩
  have hx : x * x = 1 := Subtype.ext (by decide)
  have hy : y * y = 1 := Subtype.ext (by decide)
  have ht : t * t = 1 := Subtype.ext (by decide)
  have hx1 : x ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hy1 : y ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have ht1 : t ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hyx : y ≠ x := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hord : ∀ g : alternatingGroup (Fin 8), g * g = 1 → g ≠ 1 → orderOf g = 2 :=
    fun g hg hg1 => orderOf_eq_prime (by rw [sq, hg]) hg1
  let S : Subgroup (alternatingGroup (Fin 8)) :=
    (MulAction.stabilizer (Perm (Fin 8)) (4 : Fin 8)).comap (alternatingGroup (Fin 8)).subtype
  have hxS : x ∈ S := by
    change (swap 0 1 * swap 2 3 : Perm (Fin 8)) • (4 : Fin 8) = 4
    decide
  have hyS : y ∈ S := by
    change (swap 0 2 * swap 1 3 : Perm (Fin 8)) • (4 : Fin 8) = 4
    decide
  have htS : t ∉ S := by
    change ¬ (swap 4 5 * swap 6 7 : Perm (Fin 8)) • (4 : Fin 8) = 4
    decide
  have hinf : Subgroup.zpowers t ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have hgS : g ∈ S := sup_le (Subgroup.zpowers_le.mpr hxS) (Subgroup.zpowers_le.mpr hyS) hg.2
    rcases SmallReeExclusion.eq_one_or_eq_of_mem_zpowers ht hg.1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hgS htS
  have hyz : y ∉ Subgroup.zpowers x := by
    intro hmem
    rcases SmallReeExclusion.eq_one_or_eq_of_mem_zpowers hx hmem with h | h
    · exact hy1 h
    · exact hyx h
  obtain ⟨hE, hEcard⟩ := SmallReeExclusion.triple_isElementaryAbelian_card (hord t ht ht1)
    (hord x hx hx1) (hord y hy hy1) (Subtype.ext (by decide)) (Subtype.ext (by decide))
    (Subtype.ext (by decide)) hyz hinf
  let f : Fin 8 ≃ {i : Fin n // i.val < 8} :=
    { toFun := fun i => ⟨Fin.castLE h i, i.2⟩
      invFun := fun j => ⟨j.1.val, j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let φ : alternatingGroup (Fin 8) →* alternatingGroup (Fin n) :=
    ((extendDomainHom f).comp (alternatingGroup (Fin 8)).subtype).codRestrict _ fun σ => by
      rw [mem_alternatingGroup, MonoidHom.comp_apply, extendDomainHom_apply, sign_extendDomain]
      exact σ.2
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (extendDomainHom_injective f (congrArg Subtype.val hab))
  have := hE
  exact ⟨_, IsElementaryAbelian.map φ, by rw [Subgroup.card_map_of_injective hφ, hEcard]⟩

end AlternatingModel

open AlternatingModel

theorem dihedral_sylow_alternating_model_small_degree {T : Type} [Group T] {n : ℕ} (hn : 5 ≤ n)
    (hT : Nonempty (T ≃* alternatingGroup (Fin n))) {s : ℕ} (hs : 2 ≤ s) (P : Sylow 2 T)
    (hP : Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))) :
    (n = 5 ∨ n = 6 ∨ n = 7) ∧ (n = 5 → StatedClassicalModel T .PSL 2 5 1) ∧
      (n = 6 → StatedClassicalModel T .PSL 2 3 2) ∧
      ((n = 7 ∧ Nonempty (T ≃* alternatingGroup (Fin 7))) ∨
        ∃ ℓ e : ℕ, ℓ.Prime ∧ Odd ℓ ∧ 1 ≤ e ∧ StatedClassicalModel T .PSL 2 ℓ e) := by
  obtain ⟨eT⟩ := hT
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, -⟩ := SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, hP⟩
  have hn7 : n ≤ 7 := by
    by_contra h8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨E, hE, hEcard⟩ := exists_elementaryAbelian_eight (n := n) (by omega)
    have := hE
    have hle := RankOneCenter.le_pRank_of_subgroup
      (IsElementaryAbelian.map (p := 2) (A := E) eT.symm.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective eT.symm.injective, hEcard])
    omega
  have h5 : n = 5 → StatedClassicalModel T .PSL 2 5 1 := by
    rintro rfl
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨e5⟩ := (LinearGroups.five_field_linear_two_alternating_five_model
      (GaloisField 5 1) (by rw [GaloisField.card 5 1 one_ne_zero, pow_one])).1
    exact statedClassicalModel_psl_two_of_mulEquiv T 5 1 (by norm_num) (eT.trans e5.symm)
  have h6 : n = 6 → StatedClassicalModel T .PSL 2 3 2 := by
    rintro rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    obtain ⟨e6⟩ :=
      LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        (GaloisField 3 2)
        (by rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 two_ne_zero]; norm_num)
    exact statedClassicalModel_psl_two_of_mulEquiv T 3 2 (by norm_num) (eT.trans e6.symm)
  refine ⟨by omega, h5, h6, ?_⟩
  rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
  · exact Or.inr ⟨5, 1, Nat.prime_five, by decide, le_rfl, h5 rfl⟩
  · exact Or.inr ⟨3, 2, Nat.prime_three, by decide, by norm_num, h6 rfl⟩
  · exact Or.inl ⟨rfl, ⟨eT⟩⟩

end CFSG.ComponentClassification.UnbalancedGS
