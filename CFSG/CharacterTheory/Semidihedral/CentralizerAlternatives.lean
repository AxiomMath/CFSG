module

public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Semidihedral.CentralizerAlternatives

noncomputable section

universe u v

instance generalizedFitting_characteristic (G : Type u) [Group G] :
    (CFSG.generalizedFitting G).Characteristic := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.characteristic G

instance generalizedFitting_normal (G : Type u) [Group G] :
    (CFSG.generalizedFitting G).Normal := inferInstance

@[expose] def normalizerLift {G : Type u} [Group G]
    (L : Subgroup G) [L.Normal] : G →* Subgroup.normalizer (L : Set G) where
  toFun g := ⟨g, by rw [L.normalizer_eq_top]; trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem conjNormal_eq_normalizerMonoidHom {G : Type u} [Group G]
    (L : Subgroup G) [L.Normal] :
    MulAut.conjNormal (H := L) = L.normalizerMonoidHom.comp (normalizerLift L) := by
  ext g x
  rfl

theorem conjNormal_ker {G : Type u} [Group G]
    (L : Subgroup G) [L.Normal] :
    (MulAut.conjNormal (H := L)).ker = Subgroup.centralizer (L : Set G) := by
  rw [conjNormal_eq_normalizerMonoidHom]
  ext g
  change normalizerLift L g ∈ L.normalizerMonoidHom.ker ↔ _
  rw [L.normalizerMonoidHom_ker]
  rfl

theorem inner_le_conjNormal_range {G : Type u} [Group G]
    (L : Subgroup G) [L.Normal] :
    (MulAut.conj : L →* MulAut L).range ≤ (MulAut.conjNormal (H := L)).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x : G), MulAut.conjNormal_val⟩

@[expose] def actualConjugation (G : Type u) [Group G] :
    G →* MulAut (CFSG.generalizedFitting G) := MulAut.conjNormal

theorem actualConjugation_ker (G : Type u) [Group G] :
    (actualConjugation G).ker =
      Subgroup.centralizer (CFSG.generalizedFitting G : Set G) :=
  conjNormal_ker _

theorem actualConjugation_injective {G : Type u} [Group G]
    (hC : Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥) :
    Function.Injective (actualConjugation G) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [actualConjugation_ker, hC]

theorem inner_le_actualConjugation_range (G : Type u) [Group G] :
    (MulAut.conj : CFSG.generalizedFitting G →* MulAut (CFSG.generalizedFitting G)).range ≤
      (actualConjugation G).range := inner_le_conjNormal_range _

theorem perfect_le_index_two {G : Type u} [Group G] [Finite G]
    (L J : Subgroup G) [J.Normal] [Group.IsPerfect L] (hJ : J.index = 2) : L ≤ J := by
  have hcard : Nat.card (G ⧸ J) = 2 := hJ
  let : IsCyclic (G ⧸ J) := isCyclic_of_prime_card hcard
  let q : L →* G ⧸ J := (QuotientGroup.mk' J).comp L.subtype
  have hker : q.ker = ⊤ := by
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top (G := L)]
    exact Abelianization.commutator_subset_ker q
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact MonoidHom.mem_ker.mp (show (⟨x, hx⟩ : L) ∈ q.ker by rw [hker]; trivial)

theorem sylow_card_dvd_of_le {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (L J : Subgroup G) (hLJ : L ≤ J)
    (U : Sylow p L) (T : Sylow p J) : Nat.card U ∣ Nat.card T := by
  let f : L →* J := Subgroup.inclusion hLJ
  let V : Subgroup J := (U : Subgroup L).map f
  have hV : IsPGroup p V := U.isPGroup'.map f
  obtain ⟨W, hVW⟩ := hV.exists_le_sylow
  have hUV : Nat.card U = Nat.card V :=
    Nat.card_congr ((U : Subgroup L).equivMapOfInjective f
      (Subgroup.inclusion_injective hLJ)).toEquiv
  have hWT : Nat.card W = Nat.card T := Nat.card_congr (Sylow.equiv W T).toEquiv
  rw [hUV, ← hWT]
  exact Subgroup.card_dvd_of_le hVW

theorem card_of_dihedral_equiv {H : Type u} [Group H]
    (k : ℕ) (hk : 1 ≤ k) (e : H ≃* DihedralGroup (2 ^ (k - 1))) :
    Nat.card H = 2 ^ k := by
  calc
    Nat.card H = 2 * 2 ^ (k - 1) :=
      (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    _ = 2 ^ (k - 1 + 1) := by rw [pow_succ]; omega
    _ = 2 ^ k := by rw [Nat.sub_add_cancel hk]

theorem factorization_two_pow_mul_three (k : ℕ) :
    (2 ^ k * 3).factorization 2 = k := by
  rw [Nat.factorization_mul_apply_of_coprime
      ((by decide : Nat.Coprime 2 3).pow_left k),
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3), Nat.add_zero]

theorem sylow_two_card_of_card {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (k : ℕ) (hcard : Nat.card G = 2 ^ k * 3) :
    Nat.card S = 2 ^ k := by
  rw [S.card_eq_multiplicity, hcard, factorization_two_pow_mul_three]

theorem alternatingFour_card : Nat.card (alternatingGroup (Fin 4)) = 12 :=
  alternatingGroup.card_of_card_eq_four (by simp)

theorem alternatingFour_sylow_two_card (S : Sylow 2 (alternatingGroup (Fin 4))) :
    Nat.card S = 4 := by
  exact sylow_two_card_of_card S 2 (by rw [alternatingFour_card]; norm_num)

theorem symmetricFour_card : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]

theorem symmetricFour_sylow_two_card (S : Sylow 2 (Equiv.Perm (Fin 4))) :
    Nat.card S = 8 := by
  exact sylow_two_card_of_card S 3 (by rw [symmetricFour_card]; norm_num)

theorem not_twoGroup_of_residual {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (J : Subgroup G) (T : Sylow 2 J)
    (eT : T ≃* DihedralGroup (2 ^ (n - 3)))
    (htrivial : ∀ (P : Type u) [Group P] [Finite P],
      IsPGroup 2 P → ∀ f : J →* P, f = 1) : ¬ IsPGroup 2 G := by
  intro hG
  have hJ : IsPGroup 2 J := hG.of_injective J.subtype J.subtype_injective
  have hid := htrivial J hJ (MonoidHom.id J)
  have hall : ∀ x : J, x = 1 := fun x => DFunLike.congr_fun hid x
  let : Subsingleton J := ⟨fun x y => (hall x).trans (hall y).symm⟩
  have hTcard : Nat.card T = 2 ^ (n - 2) :=
    card_of_dihedral_equiv (n - 2) (by omega)
      (by rw [show n - 2 - 1 = n - 3 by omega]; exact eT)
  have hTtrivial : Nat.card T = 1 := by simp
  have hfour : 4 ≤ 2 ^ (n - 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n - 2)
  omega

theorem not_alternatingFour_of_supplied {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (eS : S ≃* DihedralGroup (2 ^ (n - 2))) :
    ¬ Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  rintro ⟨e⟩
  have hGcard : Nat.card G = 12 := (Nat.card_congr e.toEquiv).trans alternatingFour_card
  have hScard : Nat.card S = 4 :=
    sylow_two_card_of_card S 2 (by rw [hGcard]; norm_num)
  have hSdihedral : Nat.card S = 2 ^ (n - 1) :=
    card_of_dihedral_equiv (n - 1) (by omega)
      (by rw [show n - 1 - 1 = n - 2 by omega]; exact eS)
  have height : 8 ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n - 1)
  omega

theorem n_eq_four_of_symmetricFour {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (eS : S ≃* DihedralGroup (2 ^ (n - 2))) (e : G ≃* Equiv.Perm (Fin 4)) : n = 4 := by
  have hGcard : Nat.card G = 24 := (Nat.card_congr e.toEquiv).trans symmetricFour_card
  have hScard : Nat.card S = 2 ^ 3 :=
    sylow_two_card_of_card S 3 (by rw [hGcard]; norm_num)
  have hSdihedral : Nat.card S = 2 ^ (n - 1) :=
    card_of_dihedral_equiv (n - 1) (by omega)
      (by rw [show n - 1 - 1 = n - 2 by omega]; exact eS)
  have hexp := Nat.pow_right_injective (by decide : 2 ≤ 2) (hSdihedral.symm.trans hScard)
  omega

theorem image_index_two_eq_alternating {G : Type u} [Group G]
    (J : Subgroup G) (hJ : J.index = 2) (e : G ≃* Equiv.Perm (Fin 4)) :
    J.map e.toMonoidHom = alternatingGroup (Fin 4) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  exact (J.index_map_of_bijective e.bijective).trans hJ

theorem dihedral_parameter_le {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (L J : Subgroup G) (hLJ : L ≤ J)
    (T : Sylow 2 J) (eT : T ≃* DihedralGroup (2 ^ (n - 3)))
    (U : Sylow 2 L) (m : ℕ) (hm : 2 ≤ m)
    (eU : U ≃* DihedralGroup (2 ^ (m - 1))) : m ≤ n - 2 := by
  have hdvd := sylow_card_dvd_of_le L J hLJ U T
  have hUcard := card_of_dihedral_equiv m (by omega) eU
  have hTcard : Nat.card T = 2 ^ (n - 2) :=
    card_of_dihedral_equiv (n - 2) (by omega)
      (by rw [show n - 2 - 1 = n - 3 by omega]; exact eT)
  rw [hUcard, hTcard] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hdvd

theorem generic_structural_alternatives
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (n - 2)))
    (J : Subgroup G) [J.Normal] (hJ : J.index = 2)
    (T : Sylow 2 J) (eT : T ≃* DihedralGroup (2 ^ (n - 3)))
    (htrivial : ∀ (P : Type u) [Group P] [Finite P],
      IsPGroup 2 P → ∀ f : J →* P, f = 1) :
    (n = 4 ∧ ∃ φ : G ≃* Equiv.Perm (Fin 4),
      J.map φ.toMonoidHom = alternatingGroup (Fin 4)) ∨
    (IsSimpleGroup (CFSG.generalizedFitting G) ∧
      (∃ x y : CFSG.generalizedFitting G, x * y ≠ y * x) ∧
      CFSG.generalizedFitting G ≤ J ∧
      Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ ∧
      (∀ U : Sylow 2 (CFSG.generalizedFitting G),
        ∃ m : ℕ, 2 ≤ m ∧ m ≤ n - 2 ∧ Nonempty (U ≃* DihedralGroup (2 ^ (m - 1)))) ∧
      Function.Injective (actualConjugation G) ∧
      (MulAut.conj : CFSG.generalizedFitting G →* MulAut (CFSG.generalizedFitting G)).range ≤
        (actualConjugation G).range) := by
  rcases CoreFreeDihedral.corefree_dihedral_generalized_fitting_alternatives
      hcore S (n - 1) (by omega)
      (by rw [show n - 1 - 1 = n - 2 by omega]; exact eS) with h2 | hA | hS | hL
  · exact (not_twoGroup_of_residual n hn J T eT htrivial h2).elim
  · exact (not_alternatingFour_of_supplied n hn S eS hA).elim
  · obtain ⟨φ⟩ := hS
    exact Or.inl ⟨n_eq_four_of_symmetricFour n hn S eS φ,
      φ, image_index_two_eq_alternating J hJ φ⟩
  · obtain ⟨hsimple, hnonabelian, hC, hSylow⟩ := hL
    let : IsSimpleGroup (CFSG.generalizedFitting G) := hsimple
    let : Group.IsPerfect (CFSG.generalizedFitting G) :=
      CoreFreeDihedral.isPerfect_of_simple_nonabelian hnonabelian
    have hLJ := perfect_le_index_two (CFSG.generalizedFitting G) J hJ
    refine Or.inr ⟨hsimple, hnonabelian, hLJ, hC, ?_,
      actualConjugation_injective hC, inner_le_actualConjugation_range G⟩
    intro U
    obtain ⟨m, hm, ⟨eU⟩⟩ := hSylow U
    exact ⟨m, hm, dihedral_parameter_le n hn _ J hLJ T eT U m hm eU, ⟨eU⟩⟩

end

end CFSG.Semidihedral.CentralizerAlternatives
