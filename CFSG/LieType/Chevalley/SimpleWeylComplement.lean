module

public import CFSG.LieType.Chevalley.SimpleRootComplement
public import CFSG.LieType.Chevalley.WeylRootTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag}

variable (τ) (R : Type*) [CommRing R] in
@[expose] def posComplement
    (i : Fin τ.rank) : Subgroup (Module.End R (RootModule τ R))ˣ :=
  rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1}

theorem weylElt_eq_torusElt_mul_weylElt_one
    {R : Type*} [CommRing R] (i : Fin τ.rank)
    (t : Rˣ) : weylElt τ R i t = torusElt τ R i t * weylElt τ R i 1 := by
  rw [torusElt, mul_assoc, ← weylElt_inv, inv_mul_cancel, mul_one]

theorem map_conj_torusElt_rootSubgroup
    {R : Type*} [CommRing R] (i : Fin τ.rank) (t : Rˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ R α).map (MulAut.conj (torusElt τ R i t)).toMonoidHom = rootSubgroup τ R α := by
  set u : Rˣ := t ^ (∑ j, τ.cartan i j * α j)
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      root_torus_conjugation i hα t c]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨pinnedX τ R α ((u⁻¹ : Rˣ) * c), Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, root_torus_conjugation i hα t]
    congr 1
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem map_conj_weylElt_rootSubgroup'
    (R : Type) [CommRing R] (i : Fin τ.rank) (t : Rˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ R α).map (MulAut.conj (weylElt τ R i t)).toMonoidHom =
      rootSubgroup τ R (reflect τ i α) := by
  rw [weylElt_eq_torusElt_mul_weylElt_one, map_conj_mul, map_conj_weylElt_rootSubgroup R i hα,
    map_conj_torusElt_rootSubgroup i t (IsRoot.reflect i hα)]

theorem map_conj_weylElt_rootSpan
    (R : Type) [CommRing R] (i : Fin τ.rank) (t : Rˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ R S).map (MulAut.conj (weylElt τ R i t)).toMonoidHom =
      rootSpan τ R (reflect τ i '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun α => iSup_congr fun hα => map_conj_weylElt_rootSubgroup' R i t (hS α hα)

theorem simple_Weyl_positive_complement
    (τ : Tag) (R : Type) [CommRing R] (i : Fin τ.rank)
    (t : Rˣ) :
    (posComplement τ R i).map (MulAut.conj (weylElt τ R i t)).toMonoidHom = posComplement τ R i ∧
    (rootSubgroup τ R (Pi.single i 1)).map (MulAut.conj (weylElt τ R i t)).toMonoidHom =
      rootSubgroup τ R (-Pi.single i 1) ∧
    ((posUnipotent τ R).map (MulAut.conj (weylElt τ R i t)).toMonoidHom :
        Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (rootSubgroup τ R (-Pi.single i 1)) * SetLike.coe (posComplement τ R i) ∧
    ((posUnipotent τ R).map (MulAut.conj (weylElt τ R i t)).toMonoidHom :
        Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (posComplement τ R i) * SetLike.coe (rootSubgroup τ R (-Pi.single i 1)) ∧
    ((posComplement τ R i).subgroupOf
      ((posUnipotent τ R).map (MulAut.conj (weylElt τ R i t)).toMonoidHom)).Normal ∧
    rootSubgroup τ R (-Pi.single i 1) ⊓ posComplement τ R i = ⊥ ∧
    (∀ a ∈ rootSubgroup τ R (-Pi.single i 1), ∀ a' ∈ rootSubgroup τ R (-Pi.single i 1),
      ∀ b ∈ posComplement τ R i, ∀ b' ∈ posComplement τ R i,
        a * b = a' * b' → a = a' ∧ b = b') ∧
    ∀ a ∈ rootSubgroup τ R (-Pi.single i 1), ∀ a' ∈ rootSubgroup τ R (-Pi.single i 1),
      ∀ b ∈ posComplement τ R i, ∀ b' ∈ posComplement τ R i,
        b * a = b' * a' → a = a' ∧ b = b' := by
  obtain ⟨-, hnorm, -, -, -, -, -⟩ := simple_positive_root_complement τ R i
  have hS : (posComplement τ R i).map (MulAut.conj (weylElt τ R i t)).toMonoidHom =
      posComplement τ R i := by
    simp only [posComplement]
    rw [map_conj_weylElt_rootSpan R i t fun γ hγ => hγ.1]
    congr 1
    exact (bijOn_reflect i).image_eq
  set n := weylElt τ R i t
  set Ustar := posComplement τ R i
  set U := rootSubgroup τ R (Pi.single i 1)
  set V := rootSubgroup τ R (-Pi.single i 1)
  have hU : U.map (MulAut.conj n).toMonoidHom = V := by
    rw [map_conj_weylElt_rootSubgroup' R i t (isRoot_single τ i), reflect_single_self]
  have hplus : (posUnipotent τ R).map (MulAut.conj n).toMonoidHom = V ⊔ Ustar := by
    rw [← rootSubgroup_single_sup_rootSpan_complement R i, Subgroup.map_sup, hU]
    exact congrArg (V ⊔ ·) hS
  have hUplus : posUnipotent τ R ≤ Subgroup.normalizer (Ustar : Set (Module.End R
      (RootModule τ R))ˣ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (iSup₂_le fun γ hγ =>
      le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl)).1 hnorm
  have hn : n ∈ Subgroup.normalizer (Ustar : Set (Module.End R (RootModule τ R))ˣ) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h := congrArg SetLike.coe hS
    rw [Subgroup.coe_map] at h
    exact h
  have hVN : V ≤ Subgroup.normalizer (Ustar : Set (Module.End R (RootModule τ R))ˣ) := by
    rw [← hU]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hUplus ((le_iSup₂_of_le (Pi.single i 1)
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ le_rfl : U ≤ posUnipotent τ R) hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn hx') (inv_mem hn)
  have hsupN : V ⊔ Ustar ≤ Subgroup.normalizer (Ustar : Set (Module.End R (RootModule τ R))ˣ) :=
    sup_le hVN Subgroup.le_normalizer
  have hinf : V ⊓ Ustar = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgV, hgU⟩ := Subgroup.mem_inf.1 hg
    have h1 : g ∈ posUnipotent τ R ⊓ negUnipotent τ R := Subgroup.mem_inf.2
      ⟨(iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl : Ustar ≤ _) hgU,
        (le_iSup₂_of_le (-Pi.single i 1)
          ⟨isRoot_neg_single τ i, by rw [height_neg, height_single]; omega⟩ le_rfl :
            V ≤ negUnipotent τ R) hgV⟩
    rwa [posUnipotent_inf_negUnipotent] at h1
  refine ⟨hS, hU, ?_, ?_, ?_, hinf, fun a ha a' ha' b hb b' hb' h => ?_,
    fun a ha a' ha' b hb b' hb' h => ?_⟩
  · rw [hplus, Subgroup.coe_mul_of_left_le_normalizer_right V Ustar hVN]
  · rw [hplus, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left Ustar V hVN]
  · rw [hplus]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hsupN
  · have hm : a'⁻¹ * a = b' * b⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h1 : a'⁻¹ * a ∈ V ⊓ Ustar :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, hm ▸ mul_mem hb' (inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_left_cancel h⟩
  · have hm : a * a'⁻¹ = b⁻¹ * b' := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
    have h1 : a * a'⁻¹ ∈ V ⊓ Ustar :=
      Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem ha'), hm ▸ mul_mem (inv_mem hb) hb'⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_right_cancel h⟩

end CFSG.LieType.Chevalley
