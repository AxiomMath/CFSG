module

public import CFSG.ClassicalInvolution.Balance.PassTwoBProperty

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
open scoped commutatorElement

section TwoFactor

variable {X : Type} [Group X] [Finite X]

theorem twoComponent_le_or_le_of_le_sup {A B : Subgroup X} (hAsub : IsSubnormal A ⊤)
    (hBsub : IsSubnormal B ⊤) (hcomm : ⁅A, B⁆ = ⊥) {t : X}
    (hAinv : A.map (MulAut.conj t).toMonoidHom = A)
    (hBinv : B.map (MulAut.conj t).toMonoidHom = B) {C : Subgroup X}
    (hC : C = Subgroup.centralizer ({t} : Set X)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) (hle : Lc.map C.subtype ≤ A ⊔ B) :
    Lc.map C.subtype ≤ A ∨ Lc.map C.subtype ≤ B := by
  classical
  have hfixed : FixedCommutingProduct.fixedSubgroup (MulAut.conj t) = C := by
    rw [hC]
    exact fixedSubgroup_conj_eq_centralizer t
  have : Group.IsPerfect Lc := ⟨TwoComponents.perfect hLc⟩
  have : Group.IsPerfect (Lc.map C.subtype) := Group.IsPerfect.map C.subtype
  have hderived := FixedCommutingProduct.derived_fixed A B hcomm (MulAut.conj t) hAinv hBinv
  rw [hfixed] at hderived
  have hle'' : Lc.map C.subtype ≤ (A ⊔ B) ⊓ C := le_inf hle (Subgroup.map_subtype_le Lc)
  have hprod : Lc.map C.subtype ≤ (A ⊓ C) ⊔ (B ⊓ C) :=
    calc Lc.map C.subtype = ⁅Lc.map C.subtype, Lc.map C.subtype⁆ :=
          Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(A ⊔ B) ⊓ C, (A ⊔ B) ⊓ C⁆ := Subgroup.commutator_mono hle'' hle''
      _ ≤ (A ⊓ C) ⊔ (B ⊓ C) := hderived
  have hlocal : Lc ≤ A.subgroupOf C ⊔ B.subgroupOf C := by
    have hmap : Lc.map C.subtype ≤ (A.subgroupOf C ⊔ B.subgroupOf C).map C.subtype := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      exact hprod
    have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
    rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
  have hAlocal : IsSubnormal (A.subgroupOf C) ⊤ := Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hAsub Subgroup.IsSubnormal.top).subgroupOf)
  have hBlocal : IsSubnormal (B.subgroupOf C) ⊤ := Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hBsub Subgroup.IsSubnormal.top).subgroupOf)
  have hpairJoin : sSup ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)) =
      A.subgroupOf C ⊔ B.subgroupOf C := by simp
  have hpairSub : ∀ s ∈ ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)),
      IsSubnormal s ⊤ := by
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact hAlocal
    · rw [Set.mem_singleton_iff.mp hs]
      exact hBlocal
  obtain ⟨cont, hcont, hcontle⟩ := TwoComponentJoins.exists_le_of_le_sSup Lc hLc
    ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)) hpairSub (by rwa [hpairJoin])
  rcases Set.mem_insert_iff.mp hcont with rfl | hcont
  · left
    calc Lc.map C.subtype ≤ (A.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
      _ = A ⊓ C := Subgroup.subgroupOf_map_subtype A C
      _ ≤ A := inf_le_left
  · right
    rw [Set.mem_singleton_iff.mp hcont] at hcontle
    calc Lc.map C.subtype ≤ (B.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
      _ = B ⊓ C := Subgroup.subgroupOf_map_subtype B C
      _ ≤ B := inf_le_left

end TwoFactor

section Centralizes

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isComponentOf_conj_map {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) (t : X) :
    IsComponentOf (Q.map (MulAut.conj t).toMonoidHom) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj t) Q).mpr hQ

omit [Finite X] in
theorem conj_comp_conj_eq_id {t : X} (ht2 : t * t = 1) :
    (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id X := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hti,
    MonoidHom.id_apply]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht2]; simp

omit [Finite X] in
theorem map_conj_map_conj_of_mul_self_eq_one {t : X} (ht2 : t * t = 1) (K : Subgroup X) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
  rw [Subgroup.map_map, conj_comp_conj_eq_id ht2, Subgroup.map_id]

theorem map_conj_eq_of_centralizes {Q L : Subgroup X} (hQ : IsComponentOf Q ⊤) (hLQ : L ≤ Q)
    (hperf : ⁅L, L⁆ = L) (hne : L ≠ ⊥) {t : X} (htL : ∀ l ∈ L, t * l = l * t) :
    Q.map (MulAut.conj t).toMonoidHom = Q := by
  have hL' : L ≤ Q.map (MulAut.conj t).toMonoidHom := fun l hl =>
    ⟨l, hLQ hl, by simp [MulAut.conj_apply, htL l hl]⟩
  exact eq_of_isComponentOf_of_perfect_le (isComponentOf_conj_map hQ t) hQ hperf hne hL' hLQ

omit [Finite X] in
theorem layer_eq_sup_sSup {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) :
    Layer.subgroup X = Q ⊔ sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} := by
  have hset : {R : Subgroup X | IsComponentOf R ⊤} =
      insert Q {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} := by
    ext R
    by_cases hRQ : R = Q
    · subst hRQ
      simp [hQ]
    · simp [hRQ]
  rw [Layer.subgroup, hset, sSup_insert]

theorem otherComponents_data {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) {t : X} (ht2 : t * t = 1)
    (hQinv : Q.map (MulAut.conj t).toMonoidHom = Q) :
    (sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}).map (MulAut.conj t).toMonoidHom =
        sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} ∧
      ⁅Q, sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}⁆ = ⊥ ∧
      IsSubnormal (sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}) ⊤ := by
  set S' : Set (Subgroup X) := {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} with hS'
  have hS'comp : ∀ b ∈ S', IsComponentOf b ⊤ := fun b hb => hb.1
  refine ⟨?_, ?_, ?_⟩
  · have hS'inv : ∀ R ∈ S', R.map (MulAut.conj t).toMonoidHom ∈ S' := by
      rintro R ⟨hR, hRQ⟩
      refine ⟨isComponentOf_conj_map hR t, fun h => hRQ ?_⟩
      have := congrArg (fun K => K.map (MulAut.conj t).toMonoidHom) h
      simp only [map_conj_map_conj_of_mul_self_eq_one ht2, hQinv] at this
      exact this
    have hle1 : (sSup S').map (MulAut.conj t).toMonoidHom ≤ sSup S' := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun R hR => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (hS'inv R hR)
    refine le_antisymm hle1 ?_
    have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hle1
    rwa [map_conj_map_conj_of_mul_self_eq_one ht2] at this
  · rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    refine sSup_le fun b hb => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne b Q (hS'comp b hb) hQ hb.2)
  · have hTE : sSup S' ≤ Layer.subgroup X :=
      sSup_le fun b hb => Layer.component_le (hS'comp b hb)
    have hTnormal : ((sSup S').subgroupOf (Layer.subgroup X)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTE]
      intro g hg
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_sSup_of_isComponentOf hS'comp hg)
    have : (Layer.subgroup X).Normal := Layer.normal X
    exact IsSubnormal.step hTE hTnormal
      (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤))

theorem isQuasisimple_or_commutator_eq_bot_of_centralizes (hLB : L2PrimeBalance)
    (hO : componentClassificationOddCore X = ⊥) {Q : Subgroup X} (hQ : IsComponentOf Q ⊤)
    {L : Subgroup X} (hLQ : L ≤ Q) (hperf : ⁅L, L⁆ = L) (hne : L ≠ ⊥) {t : X} (ht2 : t * t = 1)
    (htL : ∀ l ∈ L, t * l = l * t)
    (hQB : ∀ M₁ : Subgroup ↥(Q ⊓ Subgroup.centralizer ({t} : Set X)),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁)
    {W : Subgroup X} (hW : W = Subgroup.centralizer ({t} : Set X)) (M : Subgroup ↥W)
    (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M ∨ ⁅M.map W.subtype, L⁆ = ⊥ := by
  have hlayer : M.map W.subtype ≤ Layer.subgroup X :=
    twoComponent_le_layer_of_l2PrimeBalance hLB hO ht2 hW hM
  have hQinv := map_conj_eq_of_centralizes hQ hLQ hperf hne htL
  obtain ⟨hBinv, hcomm, hBsub⟩ := otherComponents_data hQ ht2 hQinv
  rw [layer_eq_sup_sSup hQ] at hlayer
  rcases twoComponent_le_or_le_of_le_sup hQ.2.1 hBsub hcomm hQinv hBinv hW hM hlayer with h | h
  · exact Or.inl (isQuasisimple_of_map_le_component hQB hW hM h)
  · right
    refine le_bot_iff.mp ((Subgroup.commutator_mono h hLQ).trans ?_)
    rw [Subgroup.commutator_comm]
    exact hcomm.le

end Centralizes

end CFSG.ClassicalInvolution.Balance
