module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeTwoRho
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeTwoEdge
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeDFive
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

section Frame

variable {E} {ω : K} (hω : IsTraceNormOne E ω) {H : Type} [Group H]
  {t : Equiv.Perm (Fin 4) →* H} {κ : normOmega E 3 →* H}

private theorem two_nodes_cases (J : Finset (Fin 5)) (hJ : J.card ≤ 2) :
    (∀ k ∈ J, (k : ℕ) < 2) ∨ (∀ k ∈ J, 2 ≤ (k : ℕ)) ∨
      ∃ k l : Fin 5, (k : ℕ) < 2 ∧ 2 ≤ (l : ℕ) ∧ J = {k, l} := by
  by_cases h1 : ∀ k ∈ J, (k : ℕ) < 2
  · exact Or.inl h1
  by_cases h2 : ∀ k ∈ J, 2 ≤ (k : ℕ)
  · exact Or.inr (Or.inl h2)
  push Not at h1 h2
  obtain ⟨l, hlJ, hl⟩ := h1
  obtain ⟨k, hkJ, hk⟩ := h2
  refine Or.inr (Or.inr ⟨k, l, by omega, by omega, ?_⟩)
  have hkl : k ≠ l := fun h => by rw [h] at hk; omega
  have hsub : ({k, l} : Finset (Fin 5)) ⊆ J := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hkJ, hlJ]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hkl]; exact hJ)).symm

private theorem cartanD_five_eq_zero_of_cross {k l : Fin 5} (hk : (k : ℕ) < 2)
    (hl : 2 ≤ (l : ℕ)) (hkl : ¬((k : ℕ) = 1 ∧ (l : ℕ) = 2)) : cartanD 5 k l = 0 := by
  have hne : k ≠ l := by rintro rfl; omega
  simp only [cartanD, Matrix.of_apply, if_neg hne]
  rw [if_neg (by omega)]

private theorem singleton_ne_univ_four (i : Fin 4) : ({i} : Finset (Fin 4)) ≠ Finset.univ :=
  (Finset.card_lt_iff_ne_univ _).mp (by simp)

private theorem qTwoRho_apply_eq_of_le_eqLocus {Ψ : normOmega E 4 →* H} {T : Finset (Fin 4)}
    (hT : T ≠ Finset.univ) {B : Subgroup (normOmega E 4)} (hBT : B ≤ normBlock E 4 T)
    (h : B ≤ (MonoidHom.eqLocus (Ψ.comp (normBlock E 4 T).subtype)
      (deletionPhiThree E t κ T hT)).map (normBlock E 4 T).subtype)
    {x : normOmega E 4} (hx : x ∈ B) :
    Ψ x = deletionPhiThree E t κ T hT ⟨x, hBT hx⟩ := by
  obtain ⟨z, hz, hzx⟩ := h hx
  have hz' : z = ⟨x, hBT hx⟩ := Subtype.ext hzx
  subst hz'
  exact hz

private theorem qTwoRho_eqLocus_pair_two_three
    (Ψ : normOmega E 4 →* H)
    (hΨ : ∀ (k : Fin 5) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
      Ψ ((qTwoLambda E hω).symm x) = qTwoRho E hω t κ k x) :
    normBlock E 4 ({2, 3} : Finset (Fin 4)) ≤
      (MonoidHom.eqLocus (Ψ.comp (normBlock E 4 ({2, 3} : Finset (Fin 4))).subtype)
        (deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3))).map
        (normBlock E 4 ({2, 3} : Finset (Fin 4))).subtype := by
  refine (normBlock_two_three_le_map_levi E hω).trans ?_
  simp only [levi, Subgroup.map_iSup]
  refine iSup₂_le fun j hj => ?_
  rintro _ ⟨y, hy, rfl⟩
  have hj2 : 2 ≤ (j : ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> norm_num
  exact ⟨⟨_, map_rankOne_le_normBlock_two_three E hω hj2 (Subgroup.mem_map_of_mem _ hy)⟩,
    (hΨ j ⟨y, hy⟩).trans (qTwoRho_of_two_le E hω hj2 ⟨y, hy⟩), rfl⟩

private theorem qTwoRho_eqLocus_map_conj
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (Ψ : normOmega E 4 →* H)
    (hΨ : ∀ (k : Fin 5) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
      Ψ ((qTwoLambda E hω).symm x) = qTwoRho E hω t κ k x) :
    ((rankOne (plusRootGroup 5 F (by norm_num)) 1).map
        (qTwoLambda E hω).symm.toMonoidHom).map (MulAut.conj (qTwoW0 E hω)).toMonoidHom ≤
      (MonoidHom.eqLocus (Ψ.comp (normBlock E 4 ({0, 1, 2} : Finset (Fin 4))).subtype)
        (deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) (by decide))).map
        (normBlock E 4 ({0, 1, 2} : Finset (Fin 4))).subtype := by
  have h012 : ({0, 1, 2} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hsub01 : ({0, 1} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have hsub2 : ({2} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have h23 := qTwoRho_eqLocus_pair_two_three (hω := hω) Ψ hΨ
  have h23eq : ∀ (x : normOmega E 4) (hx : x ∈ normBlock E 4 ({2, 3} : Finset (Fin 4))),
      Ψ x = deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3) ⟨x, hx⟩ :=
    fun x hx => qTwoRho_apply_eq_of_le_eqLocus (pair_ne_univ_four 2 3) le_rfl h23 hx
  have hw2 : qTwoW0 E hω ∈ normBlock E 4 ({2} : Finset (Fin 4)) := qTwoW0_mem_normBlock E hω
  have hw012 : qTwoW0 E hω ∈ normBlock E 4 ({0, 1, 2} : Finset (Fin 4)) :=
    normBlock_mono E 4 hsub2 hw2
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hz
  have hmem01 : (qTwoLambda E hω).symm y ∈ normBlock E 4 ({0, 1} : Finset (Fin 4)) :=
    map_rankOne_le_normBlock_zero_one E hω (by norm_num) (Subgroup.mem_map_of_mem _ hy)
  have hz012 : (qTwoLambda E hω).symm y ∈ normBlock E 4 ({0, 1, 2} : Finset (Fin 4)) :=
    normBlock_mono E 4 hsub01 hmem01
  have hmemconj : ((MulAut.conj (qTwoW0 E hω)).toMonoidHom ((qTwoLambda E hω).symm y) :
      normOmega E 4) ∈ normBlock E 4 ({0, 1, 2} : Finset (Fin 4)) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      mul_mem (mul_mem hw012 hz012) (inv_mem hw012)
  let v : normBlock E 4 ({0, 1, 2} : Finset (Fin 4)) :=
    ⟨(MulAut.conj (qTwoW0 E hω)).toMonoidHom ((qTwoLambda E hω).symm y), hmemconj⟩
  refine ⟨v, ?_, rfl⟩
  change Ψ v.1 = deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012 v
  have hwv : Ψ (qTwoW0 E hω) =
      deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012 ⟨_, hw012⟩ := by
    have hw23 : qTwoW0 E hω ∈ normBlock E 4 ({2, 3} : Finset (Fin 4)) :=
      normBlock_mono E 4 (by decide) hw2
    have h1 : deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)
        ⟨qTwoW0 E hω, hw23⟩ =
        deletionPhiThree E t κ ({2} : Finset (Fin 4)) (singleton_ne_univ_four 2)
          ⟨qTwoW0 E hω, hw2⟩ :=
      deletionPhiThree_of_subset hT1 hC (singleton_ne_univ_four 2) (pair_ne_univ_four 2 3)
        (by decide) hw2
    have h2 : deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012
        ⟨qTwoW0 E hω, hw012⟩ =
        deletionPhiThree E t κ ({2} : Finset (Fin 4)) (singleton_ne_univ_four 2)
          ⟨qTwoW0 E hω, hw2⟩ :=
      deletionPhiThree_of_subset hT1 hC (singleton_ne_univ_four 2) h012 hsub2 hw2
    exact (h23eq _ hw23).trans (h1.trans h2.symm)
  have hzv : Ψ ((qTwoLambda E hω).symm y) =
      deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012 ⟨_, hz012⟩ :=
    (hΨ 1 ⟨y, hy⟩).trans ((qTwoRho_of_lt_two E hω (by norm_num) ⟨y, hy⟩).trans
      (deletionPhiThree_of_subset hT1 hC (pair_ne_univ_four 0 1) h012 hsub01 hmem01).symm)
  have hconj : v = ⟨qTwoW0 E hω, hw012⟩ * ⟨(qTwoLambda E hω).symm y, hz012⟩ *
      ⟨qTwoW0 E hω, hw012⟩⁻¹ :=
    Subtype.ext rfl
  show Ψ (qTwoW0 E hω * (qTwoLambda E hω).symm y * (qTwoW0 E hω)⁻¹) =
    deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012
      (⟨qTwoW0 E hω, hw012⟩ * ⟨(qTwoLambda E hω).symm y, hz012⟩ *
        ⟨qTwoW0 E hω, hw012⟩⁻¹)
  simp only [map_mul, map_inv, hwv, hzv]

private theorem qTwoRho_eqLocus_pair_zero_one
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (Ψ : normOmega E 4 →* H)
    (hΨ : ∀ (k : Fin 5) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
      Ψ ((qTwoLambda E hω).symm x) = qTwoRho E hω t κ k x) :
    normBlock E 4 ({0, 1} : Finset (Fin 4)) ≤
      (MonoidHom.eqLocus (Ψ.comp (normBlock E 4 ({0, 1, 2} : Finset (Fin 4))).subtype)
        (deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) (by decide))).map
        (normBlock E 4 ({0, 1, 2} : Finset (Fin 4))).subtype := by
  have h012 : ({0, 1, 2} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hsub01 : ({0, 1} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4)) := by decide
  refine (normBlock_zero_one_le_map_levi E hω).trans
    (sup_le ?_ (qTwoRho_eqLocus_map_conj hω hT1 hC Ψ hΨ))
  · simp only [levi, Subgroup.map_iSup]
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hj2 : (j : ℕ) < 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> norm_num
    have hmem01 : (qTwoLambda E hω).symm y ∈ normBlock E 4 ({0, 1} : Finset (Fin 4)) :=
      map_rankOne_le_normBlock_zero_one E hω hj2 (Subgroup.mem_map_of_mem _ hy)
    exact ⟨⟨_, normBlock_mono E 4 hsub01 hmem01⟩, (hΨ j ⟨y, hy⟩).trans
      ((qTwoRho_of_lt_two E hω hj2 ⟨y, hy⟩).trans
        (deletionPhiThree_of_subset hT1 hC (pair_ne_univ_four 0 1) h012 hsub01 hmem01).symm),
      rfl⟩
private theorem qTwoRho_eq_singleton
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (Ψ : normOmega E 4 →* H)
    (hΨ : ∀ (k : Fin 5) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
      Ψ ((qTwoLambda E hω).symm x) = qTwoRho E hω t κ k x)
    (i : Fin 4) {x : normOmega E 4}
    (hx : x ∈ normBlock E 4 ({i} : Finset (Fin 4))) :
    Ψ x = deletionPhiThree E t κ ({i} : Finset (Fin 4)) (singleton_ne_univ_four i) ⟨x, hx⟩ := by
  have h012 : ({0, 1, 2} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hsub01 : ({0, 1} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have hcases : ({i} : Finset (Fin 4)) ⊆ ({0, 1} : Finset (Fin 4)) ∨
      ({i} : Finset (Fin 4)) ⊆ ({2, 3} : Finset (Fin 4)) := by
    fin_cases i <;> simp
  rcases hcases with hsub | hsub
  · have hx' : x ∈ normBlock E 4 ({0, 1} : Finset (Fin 4)) := normBlock_mono E 4 hsub hx
    have heq : Ψ x = deletionPhiThree E t κ ({0, 1, 2} : Finset (Fin 4)) h012
        ⟨x, normBlock_mono E 4 (by decide) hx'⟩ :=
      qTwoRho_apply_eq_of_le_eqLocus (B := normBlock E 4 ({0, 1} : Finset (Fin 4)))
        h012 (normBlock_mono E 4 hsub01) (qTwoRho_eqLocus_pair_zero_one hω hT1 hC Ψ hΨ) hx'
    exact heq.trans (deletionPhiThree_of_subset hT1 hC (singleton_ne_univ_four i) h012
      (hsub.trans hsub01) hx)
  · have hx' : x ∈ normBlock E 4 ({2, 3} : Finset (Fin 4)) := normBlock_mono E 4 hsub hx
    have heq : Ψ x = deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)
        ⟨x, hx'⟩ :=
      qTwoRho_apply_eq_of_le_eqLocus (B := normBlock E 4 ({2, 3} : Finset (Fin 4)))
        (pair_ne_univ_four 2 3) le_rfl (qTwoRho_eqLocus_pair_two_three hω Ψ hΨ) hx'
    exact heq.trans (deletionPhiThree_of_subset hT1 hC (singleton_ne_univ_four i)
      (pair_ne_univ_four 2 3) hsub hx)

theorem qTwoRho_extends
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹))
    (J : Finset (Fin 5)) (hJ : J.card ≤ 2) :
    ∃ ψ : levi (plusRootGroup 5 F (by norm_num)) J →* H,
      ∀ k (hk : k ∈ J) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
        ψ (Subgroup.inclusion (rankOne_le_levi _ hk) x) = qTwoRho E hω t κ k x := by
  rcases two_nodes_cases J hJ with hlt | hge | ⟨k, l, hk, hl, hJe⟩
  · have hle : levi (plusRootGroup 5 F (by norm_num)) J ≤
        (normBlock E 4 ({0, 1} : Finset (Fin 4))).comap (qTwoLambda E hω).symm.toMonoidHom :=
      iSup₂_le fun j hj => Subgroup.map_le_iff_le_comap.mp
        (map_rankOne_le_normBlock_zero_one E hω (hlt j hj))
    refine ⟨(deletionPhiThree E t κ ({0, 1} : Finset (Fin 4)) (pair_ne_univ_four 0 1)).comp
      (((qTwoLambda E hω).symm.toMonoidHom.comp
        (levi (plusRootGroup 5 F (by norm_num)) J).subtype).codRestrict _ fun x => hle x.2), ?_⟩
    intro j hj x
    exact (qTwoRho_of_lt_two E hω (hlt j hj) x).symm
  · have hle : levi (plusRootGroup 5 F (by norm_num)) J ≤
        (normBlock E 4 ({2, 3} : Finset (Fin 4))).comap (qTwoLambda E hω).symm.toMonoidHom :=
      iSup₂_le fun j hj => Subgroup.map_le_iff_le_comap.mp
        (map_rankOne_le_normBlock_two_three E hω (hge j hj))
    refine ⟨(deletionPhiThree E t κ ({2, 3} : Finset (Fin 4)) (pair_ne_univ_four 2 3)).comp
      (((qTwoLambda E hω).symm.toMonoidHom.comp
        (levi (plusRootGroup 5 F (by norm_num)) J).subtype).codRestrict _ fun x => hle x.2), ?_⟩
    intro j hj x
    exact (qTwoRho_of_two_le E hω (hge j hj) x).symm
  · by_cases h12 : (k : ℕ) = 1 ∧ (l : ℕ) = 2
    · obtain ⟨hk1, hl2⟩ := h12
      have hk1' : k = 1 := Fin.ext hk1
      have hl2' : l = 2 := Fin.ext hl2
      subst hk1'
      subst hl2'
      rw [hJe]
      exact exists_levi_hom_one_two E hω hT1 hC hR2
    · rw [hJe]
      exact exists_levi_hom_pair_spinTen (ρ := qTwoRho E hω t κ)
        (cartanD_five_eq_zero_of_cross hk hl h12)
        fun a b => commute_qTwoRho_cross E hω hT1 hC hk hl h12 a b

theorem eq_deletionPhiThree_of_qTwoRho
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (Ψ : normOmega E 4 →* H)
    (hΨ : ∀ (k : Fin 5) (x : rankOne (plusRootGroup 5 F (by norm_num)) k),
      Ψ ((qTwoLambda E hω).symm x) = qTwoRho E hω t κ k x)
    {S : Finset (Fin 4)} (hS : S ≠ Finset.univ) {x : normOmega E 4}
    (hx : x ∈ normBlock E 4 S) :
    Ψ x = deletionPhiThree E t κ S hS ⟨x, hx⟩ := by
  have hmain : normBlock E 4 S ≤
      (MonoidHom.eqLocus (Ψ.comp (normBlock E 4 S).subtype)
        (deletionPhiThree E t κ S hS)).map (normBlock E 4 S).subtype := by
    by_cases hS2 : 2 ≤ S.card
    · have hgen : normBlock E 4 S ≤ ⨆ i ∈ S, normBlock E 4 ({i} : Finset (Fin 4)) := by
        rw [normBlock_eq_iSup_pairs E 4 S hS2]
        refine iSup_le fun P => ?_
        obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp P.2.2
        have haS : a ∈ S := P.2.1 (by rw [hP]; simp)
        have hbS : b ∈ S := P.2.1 (by rw [hP]; simp)
        rw [hP, ← normBlock_singleton_sup_singleton E a b]
        exact sup_le
          (le_iSup₂ (f := fun i (_ : i ∈ S) => normBlock E 4 ({i} : Finset (Fin 4))) a haS)
          (le_iSup₂ (f := fun i (_ : i ∈ S) => normBlock E 4 ({i} : Finset (Fin 4))) b hbS)
      refine hgen.trans (iSup_le fun i => iSup_le fun hi => ?_)
      intro y hy
      refine ⟨⟨y, normBlock_mono E 4 (Finset.singleton_subset_iff.mpr hi) hy⟩, ?_, rfl⟩
      exact (qTwoRho_eq_singleton hω hT1 hC Ψ hΨ i hy).trans
        (deletionPhiThree_of_subset hT1 hC (singleton_ne_univ_four i) hS
          (Finset.singleton_subset_iff.mpr hi) hy).symm
    · have hcard : S.card ≤ 1 := by omega
      obtain ⟨i, hi⟩ : ∃ i : Fin 4, S ⊆ ({i} : Finset (Fin 4)) := by
        rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
        · exact ⟨0, by simp⟩
        · refine ⟨i, fun j hj => Finset.mem_singleton.mpr ?_⟩
          by_contra hne
          have hsub : ({i, j} : Finset (Fin 4)) ⊆ S := by
            intro z hz
            rw [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            exacts [hi, hj]
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair (Ne.symm hne)] at hc
          omega
      intro y hy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      exact (qTwoRho_eq_singleton hω hT1 hC Ψ hΨ i (normBlock_mono E 4 hi hy)).trans
        (deletionPhiThree_of_subset hT1 hC hS (singleton_ne_univ_four i) hi hy)
  exact qTwoRho_apply_eq_of_le_eqLocus (B := normBlock E 4 S) hS le_rfl hmain hx

end Frame

theorem exists_hom_normOmegaCast_normPerm_three_of_card_two (hF : Nat.card F = 2)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (3 + 1)) →* H) (κ : normOmega E 3 →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹)) :
    ∃ Ψ : normOmega E (3 + 1) →* H, (∀ a, Ψ (normOmegaCast E (Nat.le_succ 3) a) = κ a) ∧
      ∀ σ, Ψ (normPerm E (by norm_num : 3 ≤ 3 + 1) σ) = t σ := by
  obtain ⟨ω, hω⟩ := exists_isTraceNormOne E hF
  obtain ⟨Ψ, hΨ⟩ := exists_hom_spinTen_of_rankOne (qTwoLambda E hω).symm (qTwoRho E hω t κ)
    (qTwoRho_extends hω hT1 hC hR2)
  refine ⟨Ψ, ?_, ?_⟩
  · intro a
    have hS : (Finset.univ.erase (Fin.last 3) : Finset (Fin 4)) ≠ Finset.univ := by
      intro h
      exact Finset.notMem_erase _ _ (h ▸ Finset.mem_univ (Fin.last 3))
    have hmem : normOmegaCast E (Nat.le_succ 3) a ∈
        normBlock E 4 (Finset.univ.erase (Fin.last 3)) := by
      rw [← range_normOmegaCast_succ E 3]
      exact ⟨a, rfl⟩
    rw [eq_deletionPhiThree_of_qTwoRho hω hT1 hC Ψ hΨ hS hmem]
    exact deletionPhiThree_normOmegaCast hT1 hC hS (Finset.notMem_erase _ _) a hmem
  · intro σ
    have hcomp : Ψ.comp (normPerm E (by norm_num : 3 ≤ 3 + 1)) = t := by
      refine MonoidHom.eq_of_eqOn_dense (Equiv.Perm.closure_isSwap (α := Fin (3 + 1))) ?_
      intro τ hτ
      obtain ⟨i, j, hij, rfl⟩ := hτ
      have hS : ({i, j} : Finset (Fin 4)) ≠ Finset.univ := pair_ne_univ_four i j
      have hmem : normPerm E (by norm_num) (Equiv.swap i j) ∈
          normBlock E 4 ({i, j} : Finset (Fin 4)) :=
        normPerm_swap_mem_normBlock E (by norm_num) i j
      rw [MonoidHom.comp_apply, eq_deletionPhiThree_of_qTwoRho hω hT1 hC Ψ hΨ hS hmem]
      exact deletionPhiThree_normPerm_swap hT1 hC i j
    exact DFunLike.congr_fun hcomp σ

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
