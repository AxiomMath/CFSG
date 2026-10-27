module

public import CFSG.GH74.Uniqueness.Section12Center
public import TauCeti.GroupTheory.Perm.FinThree.Basic
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GroupTheory.CentralExtensionS3

open Subgroup

theorem ker_inf_commutator_eq_bot_of_zgroup
    {E H : Type} [Group E] [Finite E] [Group H] [Finite H] [IsZGroup H]
    (pi : E →* H) (hker : pi.ker ≤ center E) : pi.ker ⊓ commutator E = ⊥ := by
  refine CFSG.Walter.W67.inf_commutator_eq_bot hker ?_
  intro q hq _
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP⟩ := CFSG.GH74.Uniqueness.exists_sylow_isMulCommutative_of_ker_le_center
    pi hker (fun Q => IsZGroup.isZGroup q hq Q)
  exact ⟨inferInstance, P, hP⟩

theorem card_commutator_eq_three_of_central_extension
    {E : Type} [Group E] [Finite E] (pi : E →* Equiv.Perm (Fin 3))
    (hpi : Function.Surjective pi) (hker : pi.ker ≤ center E) :
    Nat.card (commutator E) = 3 := by
  letI : IsZGroup (Equiv.Perm (Fin 3)) := IsZGroup.of_squarefree (by
    have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    rw [hcard]
    change Squarefree (2 * 3)
    exact (Nat.squarefree_mul (by decide)).mpr
      ⟨(Nat.prime_iff.mp Nat.prime_two).squarefree,
        (Nat.prime_iff.mp Nat.prime_three).squarefree⟩)
  have hcap := ker_inf_commutator_eq_bot_of_zgroup pi hker
  let f := pi.comp (commutator E).subtype
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (by
    apply le_bot_iff.mp
    intro x hx
    have hmem : (x : E) ∈ pi.ker ⊓ commutator E := ⟨hx, x.2⟩
    rw [hcap] at hmem
    exact Subtype.ext (mem_bot.mp hmem))
  have hrange : f.range = commutator (Equiv.Perm (Fin 3)) := by
    change (pi.comp (commutator E).subtype).range = commutator (Equiv.Perm (Fin 3))
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_commutator_eq,
      MonoidHom.range_eq_top.mpr hpi]
    rfl
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange,
    TauCeti.commutator_perm_fin_three_eq_alternatingGroup,
    nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem exists_fixed_lift_of_cube_of_square
    {E H : Type} [Group E] [Group H] (pi : E →* H) (hpi : Function.Surjective pi)
    (hker : pi.ker ≤ center E) (alpha : MulAut E) (ha3 : alpha ^ 3 = 1)
    (hfix : ∀ x, pi (alpha x) = pi x) {y : H} (hy2 : y ^ 2 = 1) :
    ∃ x : E, pi x = y ∧ alpha x = x := by
  obtain ⟨a, rfl⟩ := hpi y
  have hcycle : alpha (alpha (alpha a)) = a := by
    have h := congrArg (fun f : MulAut E => f a) ha3
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using h
  let z := alpha a * a⁻¹
  have hz : z ∈ center E := hker (by
    change pi (alpha a * a⁻¹) = 1
    rw [map_mul, map_inv, hfix, mul_inv_cancel])
  have hac : Commute a (alpha a) := by
    have h := (mem_center_iff.mp hz) a
    change a * (alpha a * a⁻¹) = (alpha a * a⁻¹) * a at h
    have h' := congrArg (fun v => v * a) h
    change a * alpha a = alpha a * a
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'
  have hbc : Commute (alpha a) (alpha (alpha a)) := hac.map alpha.toMonoidHom
  let x := a * alpha a * alpha (alpha a)
  refine ⟨x, ?_, ?_⟩
  · change pi (a * alpha a * alpha (alpha a)) = pi a
    rw [map_mul, map_mul, hfix, hfix, hfix]
    calc pi a * pi a * pi a = (pi a) ^ 2 * pi a := by rw [pow_two]
      _ = pi a := by rw [hy2, one_mul]
  · change alpha (a * alpha a * alpha (alpha a)) = a * alpha a * alpha (alpha a)
    rw [map_mul, map_mul, hcycle]
    calc alpha a * alpha (alpha a) * a = alpha a * (alpha (alpha a) * a) := mul_assoc _ _ _
      _ = alpha a * (a * alpha (alpha a)) := by
        have hca : Commute (alpha (alpha a)) a := by
          have h := hbc.map alpha.toMonoidHom
          change Commute (alpha (alpha a)) (alpha (alpha (alpha a))) at h
          rw [hcycle] at h
          exact h
        rw [hca.eq]
      _ = (alpha a * a) * alpha (alpha a) := (mul_assoc _ _ _).symm
      _ = a * alpha a * alpha (alpha a) := by rw [hac.eq]

theorem fixedSubgroup_surjective_of_central_extension_s3
    {E : Type} [Group E] (pi : E →* Equiv.Perm (Fin 3))
    (hpi : Function.Surjective pi) (hker : pi.ker ≤ center E)
    (alpha : MulAut E) (ha3 : alpha ^ 3 = 1) (hfix : ∀ x, pi (alpha x) = pi x) :
    (MonoidHom.eqLocus alpha.toMonoidHom (MonoidHom.id E)).map pi = ⊤ := by
  rw [← Equiv.Perm.closure_isSwap]
  apply le_antisymm (le_top.trans (Equiv.Perm.closure_isSwap.symm.le))
  rw [Subgroup.closure_le]
  intro y hy
  have hy2 : y ^ 2 = 1 := by
    obtain ⟨u, v, _, rfl⟩ := hy
    simp only [pow_two, Equiv.swap_mul_self]
  obtain ⟨x, hx, hax⟩ := exists_fixed_lift_of_cube_of_square pi hpi hker alpha ha3 hfix hy2
  exact Subgroup.mem_map.mpr ⟨x, hax, hx⟩

theorem commutator_not_le_center_of_central_extension
    {E : Type} [Group E] [Finite E] (pi : E →* Equiv.Perm (Fin 3))
    (hpi : Function.Surjective pi) (hker : pi.ker ≤ center E) :
    ¬ commutator E ≤ center E := by
  intro hc
  have hcard := card_commutator_eq_three_of_central_extension pi hpi hker
  have hcenter : center (Equiv.Perm (Fin 3)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h := mem_center_iff.mp hx
    have he : x = 1 := by
      have key : ∀ z : Equiv.Perm (Fin 3), (∀ t, t * z = z * t) → z = 1 := by
        decide +kernel
      exact key x h
    exact mem_bot.mpr he
  have hmap : (commutator E).map pi = ⊥ := le_bot_iff.mp (by
    calc (commutator E).map pi ≤ (center E).map pi := Subgroup.map_mono hc
      _ ≤ center (Equiv.Perm (Fin 3)) := Subgroup.map_center_le_center hpi
      _ = ⊥ := hcenter)
  have hle : commutator E ≤ pi.ker := (Subgroup.map_eq_bot_iff _).mp hmap
  letI : IsZGroup (Equiv.Perm (Fin 3)) := IsZGroup.of_squarefree (by
    have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    rw [hcard]
    change Squarefree (2 * 3)
    exact (Nat.squarefree_mul (by decide)).mpr
      ⟨(Nat.prime_iff.mp Nat.prime_two).squarefree,
        (Nat.prime_iff.mp Nat.prime_three).squarefree⟩)
  have hcap := ker_inf_commutator_eq_bot_of_zgroup pi hker
  have hbot : commutator E = ⊥ := le_bot_iff.mp (by
    simpa only [hcap] using (le_inf hle le_rfl : commutator E ≤ pi.ker ⊓ commutator E))
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem fixed_subgroup_card_commutator_and_not_central
    {E : Type} [Group E] [Finite E] (pi : E →* Equiv.Perm (Fin 3))
    (hpi : Function.Surjective pi) (hker : pi.ker ≤ center E)
    (alpha : MulAut E) (ha3 : alpha ^ 3 = 1) (hfix : ∀ x, pi (alpha x) = pi x) :
    let C := MonoidHom.eqLocus alpha.toMonoidHom (MonoidHom.id E);
    Nat.card (commutator C) = 3 ∧ ¬ commutator C ≤ center C := by
  dsimp only
  let C := MonoidHom.eqLocus alpha.toMonoidHom (MonoidHom.id E)
  let f := pi.comp C.subtype
  have hmap := fixedSubgroup_surjective_of_central_extension_s3 pi hpi hker alpha ha3 hfix
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hfc : f.ker ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hker hx) y)
  exact ⟨card_commutator_eq_three_of_central_extension f hf hfc,
    commutator_not_le_center_of_central_extension f hf hfc⟩

end CFSG.GroupTheory.CentralExtensionS3
