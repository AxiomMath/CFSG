module

public import CFSG.LargeExtraspecial.S45QSix
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Equiv Equiv.Perm Subgroup Module
open CFSG.ComponentClassification.PresentationLocal

@[expose] def fourIdx : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun i := if i = 0 then Sum.inl 0 else if i = 1 then Sum.inl 1 else if i = 2 then Sum.inr 1
    else Sum.inr 0
  invFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 1
    | Sum.inr 1 => 2
    | Sum.inr 0 => 3
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def glFourEquiv : GL (Fin 4) (ZMod 2) ≃* GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).toMulEquiv

theorem glFourEquiv_apply (g : GL (Fin 4) (ZMod 2)) :
    ((glFourEquiv g : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix _ _ (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  rfl

theorem reindex_antidiagGram :
    Matrix.reindex fourIdx fourIdx antidiagGram = Matrix.J (Fin 2) (ZMod 2) := by
  ext a c
  rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;> decide

theorem map_sympFour :
    sympFour.map glFourEquiv.toMonoidHom = TauCeti.GLSymplectic (Fin 2) (ZMod 2) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_sympFour_iff, TauCeti.GLSymplectic.mem_iff']
  set M := ((glFourEquiv.symm g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hg : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx M := by
    rw [← glFourEquiv_apply, MulEquiv.apply_symm_apply]
  have e : ∀ X : Matrix (Fin 4) (Fin 4) (ZMod 2), Matrix.reindex fourIdx fourIdx X =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx X := fun X =>
    (congrFun (Matrix.coe_reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx) X).symm
  rw [hg, ← reindex_antidiagGram, Matrix.transpose_reindex, e, e, e, ← map_mul, ← map_mul]
  exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).injective.eq_iff.symm

@[expose] noncomputable def spFourEquivPerm :
    TauCeti.GLSymplectic (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 6) :=
  ((glFourEquiv.subgroupMap sympFour).trans (MulEquiv.subgroupCongr map_sympFour)).symm.trans
    (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩)

section Transport

variable {G : Type*} [Group G] {S : Subgroup G} (Φ : S ≃* Perm (Fin 6))

@[expose] def img (H : Subgroup G) : Subgroup (Perm (Fin 6)) :=
  (H.subgroupOf S).map Φ.toMonoidHom

@[expose] noncomputable def imgEquiv {H : Subgroup G} (hH : H ≤ S) : H ≃* img Φ H :=
  (subgroupOfEquivOfLe hH).symm.trans (Φ.subgroupMap (H.subgroupOf S))

theorem card_img {H : Subgroup G} (hH : H ≤ S) : Nat.card (img Φ H) = Nat.card H :=
  (Nat.card_congr (imgEquiv Φ hH).toEquiv).symm

theorem img_mono {H K : Subgroup G} (h : H ≤ K) : img Φ H ≤ img Φ K :=
  map_mono fun _ hx => h hx

theorem coe_symm_mem_of_mem_img {H : Subgroup G} {σ : Perm (Fin 6)} (hσ : σ ∈ img Φ H) :
    ((Φ.symm σ : S) : G) ∈ H := by
  obtain ⟨h, hh, rfl⟩ := hσ
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact hh

theorem commutator_subgroupOf_self : ⁅S, S⁆.subgroupOf S = commutator S := by
  rw [← map_subtype_commutator]
  exact comap_map_eq_self_of_injective S.subtype_injective _

theorem img_commutator : img Φ ⁅S, S⁆ = alternatingGroup (Fin 6) := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  rw [img, commutator_subgroupOf_self, commutator_def, map_commutator,
    map_top_of_surjective _ Φ.surjective, ← commutator_def,
    alternatingGroup.commutator_perm_eq h5]

omit Φ in
theorem card_self_of_equiv (Φ : S ≃* Perm (Fin 6)) : Nat.card S = 720 := by
  rw [Nat.card_congr Φ.toEquiv, card_perm_six]

end Transport

section Four

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem nonempty_isometryGroup_equiv_perm (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) :
    Nonempty (TauCeti.BilinForm.isometryGroup β ≃* Perm (Fin 6)) := by
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis β hβ hnd
  obtain rfl : m = 2 := by omega
  exact ⟨(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b β
    hb).trans spFourEquivPerm⟩

theorem finite_linearEquiv : Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

theorem commutator_isometryGroup_four (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) :
    (⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆.subgroupOf
        (TauCeti.BilinForm.isometryGroup β)).Normal ∧
      IsSimpleGroup (⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ :
        Subgroup (V ≃ₗ[ZMod 2] V)) ∧
      ⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆.relIndex
        (TauCeti.BilinForm.isometryGroup β) = 2 ∧
      S5.NonabelianSylowTwo
        ⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ := by
  set Sp := TauCeti.BilinForm.isometryGroup β
  obtain ⟨Φ⟩ := nonempty_isometryGroup_equiv_perm hβ hnd h4
  have hle : ⁅Sp, Sp⁆ ≤ Sp := commutator_le_self Sp
  have himg := img_commutator Φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [commutator_subgroupOf_self]
    infer_instance
  · have := isSimpleGroup_alternatingGroup_six
    exact ((imgEquiv Φ hle).trans (MulEquiv.subgroupCongr himg)).isSimpleGroup
  · have hm := (⁅Sp, Sp⁆.subgroupOf Sp).card_mul_index
    change _ * ⁅Sp, Sp⁆.relIndex Sp = _ at hm
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, ← card_img Φ hle, himg,
      card_alternatingGroup_six, card_self_of_equiv Φ] at hm
    omega
  · have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
    obtain ⟨hx, hy, hxx, hyy, hxy, hne⟩ := dihedral_pair_mem
    rw [← himg] at hx hy
    refine nonabelianSylowTwo_of_mem (coe_symm_mem_of_mem_img Φ hx)
      (coe_symm_mem_of_mem_img Φ hy) ?_ ?_ (k := 2) ?_ ?_
    · rw [← Subgroup.coe_mul, ← map_mul, hxx, map_one, Subgroup.coe_one]
    · rw [← Subgroup.coe_mul, ← map_mul, hyy, map_one, Subgroup.coe_one]
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, hxy, map_one,
        Subgroup.coe_one]
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, Ne,
        Subtype.ext_iff.symm.not, Φ.symm.injective.eq_iff]
      exact hne

theorem exists_simple_normal_of_fifteen_dvd (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) (h15 : 15 ∣ Nat.card X) :
    ∃ M₀ ≤ X, (M₀.subgroupOf X).Normal ∧ IsSimpleGroup M₀ ∧ M₀.relIndex X ≤ 2 := by
  set Sp := TauCeti.BilinForm.isometryGroup β
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  obtain ⟨Φ⟩ := nonempty_isometryGroup_equiv_perm hβ hnd h4
  have hNle : ⁅Sp, Sp⁆ ≤ Sp := commutator_le_self Sp
  obtain ⟨hNn, -, hNi, -⟩ := commutator_isometryGroup_four hβ hnd h4
  have hrel : (X ⊓ ⁅Sp, Sp⁆).relIndex X ≤ 2 := by
    rw [inf_comm, inf_relIndex_right]
    exact (relIndex_le_of_le_right hX (by rw [hNi]; norm_num)).trans hNi.le
  refine ⟨X ⊓ ⁅Sp, Sp⁆, inf_le_left, ⟨fun n hn x => ?_⟩, ?_, hrel⟩
  · rw [mem_subgroupOf] at hn ⊢
    refine ⟨(x * n * x⁻¹).2, ?_⟩
    have := hNn.conj_mem ⟨n, hNle hn.2⟩ (mem_subgroupOf.mpr hn.2) ⟨x, hX x.2⟩
    rw [mem_subgroupOf] at this
    simpa using this
  · have hMle : X ⊓ ⁅Sp, Sp⁆ ≤ Sp := inf_le_left.trans hX
    have hKA : img Φ (X ⊓ ⁅Sp, Sp⁆) ≤ alternatingGroup (Fin 6) :=
      img_commutator Φ ▸ img_mono Φ inf_le_right
    have h15' : 15 ∣ Nat.card ↥(X ⊓ ⁅Sp, Sp⁆) := by
      have hm := ((X ⊓ ⁅Sp, Sp⁆).subgroupOf X).card_mul_index
      change _ * (X ⊓ ⁅Sp, Sp⁆).relIndex X = _ at hm
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hm
      have hpos : 0 < Nat.card X := Nat.card_pos
      have h12 : (X ⊓ ⁅Sp, Sp⁆).relIndex X = 1 ∨ (X ⊓ ⁅Sp, Sp⁆).relIndex X = 2 := by
        have h0 : (X ⊓ ⁅Sp, Sp⁆).relIndex X ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hm
          omega
        omega
      rw [← hm] at h15
      rcases h12 with h1 | h2
      · rwa [h1, mul_one] at h15
      · rw [h2] at h15
        exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h15
    rw [← card_img Φ hMle] at h15'
    have := (simple_of_le_alternatingGroup hKA h15').1
    exact (imgEquiv Φ hMle).isSimpleGroup

omit [FiniteDimensional (ZMod 2) V] in
theorem polarBilin_isAlt (Q : QuadraticForm (ZMod 2) V) : Q.polarBilin.IsAlt := fun x => by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
    CharTwo.add_self_eq_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem orthogonalGroup_le_isometryGroup (Q : QuadraticForm (ZMod 2) V) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤ TauCeti.BilinForm.isometryGroup Q.polarBilin :=
  fun _ hg => TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]

theorem omegaGroup_simple_or_solvable_four {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) :
    IsSimpleGroup (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) ∨
      Group.IsSolvable (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) := by
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  set Ω := CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ
  by_cases h60 : Nat.card Ω < 60
  · exact Or.inr (CFSG.GroupTheory.groups_order_below_sixty_solvable h60)
  left
  obtain ⟨Φ⟩ := nonempty_isometryGroup_equiv_perm (polarBilin_isAlt Q) hQ h4
  have hOS := orthogonalGroup_le_isometryGroup Q
  have hΩO : Ω ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ
  have hΩS := hΩO.trans hOS
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hcard : 2 * Nat.card Ω = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    have hm := (Ω.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).card_mul_index
    change _ * Ω.relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) = _ at hm
    rw [CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup,
      Nat.card_congr (subgroupOfEquivOfLe hΩO).toEquiv] at hm
    omega
  rw [← card_img Φ hΩS, ← card_img Φ hOS] at hcard
  rw [← card_img Φ hΩS] at h60
  have := simple_of_two_mul_card_eq (img_mono Φ hΩO) hcard (by omega)
  exact (imgEquiv Φ hΩS).isSimpleGroup

end Four

end CFSG.LargeExtraspecial.S45Q
