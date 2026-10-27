module

public import CFSG.LargeExtraspecial.S12Gen
public import CFSG.LargeExtraspecial.S12I4MData
public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12I4M

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.LargeExtraspecial.OrthoF2 CFSG.Fischer.Classification.LocalU4
  CFSG.Fischer.Classification.Unitary
open CFSG.LargeExtraspecial (Setting IsTypeA)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {χ : PG 4 →* S.O}

@[expose] noncomputable def line (χ : PG 4 →* S.O) (i : Fin 45) : Submodule (ZMod 2) S.Qt :=
  commSpace (χ (pt i) : S.Qt ≃ₗ[ZMod 2] S.Qt)

theorem coe_mul_self (χ : PG 4 →* S.O) (k : Fin 45) :
    (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt) * (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
  rw [← Subgroup.coe_mul, ← map_mul, pt_mul_self, map_one]
  rfl

theorem apply_mem_line_tauI (χ : PG 4 →* S.O) {k i : Fin 45} {v : S.Qt}
    (hv : v ∈ line χ i) : (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ line χ (tauI k i) := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  set E := (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hEE : ∀ x, E (E x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, coe_mul_self χ k]
    rfl
  have e : (χ (pt (tauI k i)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = E * (χ (pt i) : _) * E := by
    rw [← pt_mul_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  have key := sub_mem_commSpace (E * (χ (pt i) : S.Qt ≃ₗ[ZMod 2] S.Qt) * E) (E w)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hEE] at key
  unfold line
  rw [e, map_sub]
  exact key

theorem line_tauI_le (χ : PG 4 →* S.O) (k i : Fin 45) :
    line χ (tauI k i) ≤ line χ k ⊔ line χ i := by
  intro v hv
  set E := (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hEE : E (E v) = v := by
    rw [← LinearEquiv.mul_apply, coe_mul_self χ k]
    rfl
  have h1 : E v ∈ line χ i := by
    have := apply_mem_line_tauI χ (k := k) hv
    rwa [tauI_tauI] at this
  have h2 : E (E v) - E v ∈ line χ k := sub_mem_commSpace E (E v)
  rw [hEE] at h2
  have e : v = (v - E v) + E v := by abel
  rw [e]
  exact Submodule.add_mem_sup h2 h1

theorem line_inf_ne_bot_tauI (χ : PG 4 →* S.O) (k : Fin 45) {i j : Fin 45}
    (h : line χ i ⊓ line χ j ≠ ⊥) : line χ (tauI k i) ⊓ line χ (tauI k j) ≠ ⊥ := by
  obtain ⟨v, ⟨hvi, hvj⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine Submodule.ne_bot_iff _ |>.mpr ⟨_, ⟨apply_mem_line_tauI χ hvi,
    apply_mem_line_tauI χ hvj⟩, fun h0 => hv0 ?_⟩
  exact (χ (pt k) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp h0

@[expose] noncomputable def genSpan (χ : PG 4 →* S.O) : Submodule (ZMod 2) S.Qt :=
  line χ 15 ⊔ line χ 0 ⊔ line χ 16 ⊔ line χ 1 ⊔ line χ 6

theorem line_le_genSpan (χ : PG 4 →* S.O) (i : Fin 45) : line χ i ≤ genSpan χ := by
  refine gen_all (fun i => line χ i ≤ genSpan χ) ?_ ?_ ?_ ?_ ?_ ?_ i
  · exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right
  · intro a b ha hb
    exact (line_tauI_le χ a b).trans (sup_le ha hb)

theorem finrank_sup_le_of_inf_ne_bot {U ℓ : Submodule (ZMod 2) S.Qt}
    (hℓ : finrank (ZMod 2) ℓ = 2) (h : U ⊓ ℓ ≠ ⊥) :
    finrank (ZMod 2) (U ⊔ ℓ : Submodule (ZMod 2) S.Qt) ≤ finrank (ZMod 2) U + 1 := by
  have e := Submodule.finrank_sup_add_finrank_inf_eq U ℓ
  have hpos : 0 < finrank (ZMod 2) (U ⊓ ℓ : Submodule (ZMod 2) S.Qt) :=
    Nat.pos_of_ne_zero fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  omega

section Ebar

variable (hχE : ∀ q ∈ DG 4, χ q ∈ S.Ebar12 g)
include hχE

theorem isTypeA_pt (i : Fin 45) : IsTypeA S.q (χ (pt i) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 :=
  Setting.isTypeA_of_mem_Ebar12 (hχE _ (pt_mem_DG i))

theorem finrank_line (i : Fin 45) : finrank (ZMod 2) (line χ i) = 2 :=
  (isTypeA_pt hχE i).2.2.2.1

theorem finrank_genSpan_le (h1 : line χ 15 ⊓ line χ 0 ≠ ⊥) (h2 : line χ 15 ⊓ line χ 16 ≠ ⊥)
    (h3 : line χ 15 ⊓ line χ 1 ≠ ⊥) (h4 : line χ 16 ⊓ line χ 6 ≠ ⊥) :
    finrank (ZMod 2) (genSpan χ) ≤ 6 := by
  have f := finrank_line hχE
  have e1 := finrank_sup_le_of_inf_ne_bot (f 0) h1
  have e2 := finrank_sup_le_of_inf_ne_bot (U := line χ 15 ⊔ line χ 0) (f 16)
    (fun h => h2 (eq_bot_iff.mpr ((inf_le_inf_right _ le_sup_left).trans h.le)))
  have e3 := finrank_sup_le_of_inf_ne_bot (U := line χ 15 ⊔ line χ 0 ⊔ line χ 16) (f 1)
    (fun h => h3 (eq_bot_iff.mpr ((inf_le_inf_right _ (le_sup_left.trans le_sup_left)).trans
      h.le)))
  have e4 := finrank_sup_le_of_inf_ne_bot (U := line χ 15 ⊔ line χ 0 ⊔ line χ 16 ⊔ line χ 1)
    (f 6) (fun h => h4 (eq_bot_iff.mpr ((inf_le_inf_right _ (le_sup_right.trans
      le_sup_left)).trans h.le)))
  rw [f 15] at e1
  unfold genSpan
  omega

variable (hEχ : ∀ τ ∈ S.Ebar12 g, ∃ q ∈ DG 4, χ q = τ)
include hEχ

omit hχE in
theorem commSub12_le_genSpan : S.commSub12 (S.Xbar12 g) ≤ genSpan χ := by
  refine (Setting.commSub12_closure_le _).trans (Setting.commSubSet12_le fun τ hτ => ?_)
  obtain ⟨q, hq, rfl⟩ := hEχ τ hτ
  obtain ⟨i, rfl⟩ := exists_pt_eq hq
  exact line_le_genSpan χ i

theorem line_inf_eq_bot (hred : ¬ S.IsReducible12) (hw : S.width = 4) {i j : Fin 45}
    (hij : cm i j) (hne : i ≠ j) : line χ i ⊓ line χ j = ⊥ := by
  by_contra h
  have hR : ∀ k a b, line χ a ⊓ line χ b ≠ ⊥ → line χ (tauI k a) ⊓ line χ (tauI k b) ≠ ⊥ :=
    fun k a b => line_inf_ne_bot_tauI χ k
  have h0 := (pair_iff _ hR hij hne).mp h
  have hall : ∀ a b, cm a b → a ≠ b → line χ a ⊓ line χ b ≠ ⊥ := fun a b hab hne' =>
    (pair_iff _ hR hab hne').mpr h0
  obtain ⟨c1, c2, c3, c4⟩ := cm_tree
  have hdim := finrank_genSpan_le hχE (hall _ _ c1 (by decide)) (hall _ _ c2 (by decide))
    (hall _ _ c3 (by decide)) (hall _ _ c4 (by decide))
  apply hred
  have hX : χ (pt 15) ∈ S.Xbar12 g := Setting.subset_Xbar12 (hχE _ (pt_mem_DG 15))
  refine S.s12_isReducible12_of_finrank_lt Setting.Mbar_le_normalizer_Xbar12 hX ?_ ?_
  · intro h1
    exact (isTypeA_pt hχE 15).2.1 (by rw [h1]; rfl)
  · have := Submodule.finrank_mono (commSub12_le_genSpan hEχ)
    rw [S.finrank_Qt_eq_two_mul_width, hw]
    omega

theorem polar_eq_zero_of_commute (hred : ¬ S.IsReducible12) (hw : S.width = 4) {q q' : PG 4}
    (hq : q ∈ DG 4) (hq' : q' ∈ DG 4) (hne : q ≠ q') (hc : q * q' = q' * q) :
    commSpace (χ q : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (χ q' : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∧
      ∀ x ∈ commSpace (χ q : S.Qt ≃ₗ[ZMod 2] S.Qt),
        ∀ y ∈ commSpace (χ q' : S.Qt ≃ₗ[ZMod 2] S.Qt), polar S.q x y = 0 := by
  obtain ⟨i, rfl⟩ := exists_pt_eq hq
  obtain ⟨j, rfl⟩ := exists_pt_eq hq'
  have hij : cm i j := (pt_commute_iff i j).mp hc
  have hd := line_inf_eq_bot hχE hEχ hred hw hij fun h => hne (by rw [h])
  refine ⟨hd, orthogonal_of_commute_of_inf_eq_bot S.q_nondegenerate
    (mem_orthogonalGroup_of_isTypeA (isTypeA_pt hχE i)) ?_ hd⟩
  rw [← Subgroup.coe_mul, ← map_mul, hc, map_mul, Subgroup.coe_mul]

end Ebar

end CFSG.LargeExtraspecial.S12I4M
