module

public import Mathlib
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42PermAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndexInputs
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.Open.StatedDefs
public import Certificates.Certificate450100
public import Certificates.Certificate2012

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex

open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem mem_bl {g : Equiv.Perm (Fin 45)} :
    g ∈ bl ↔ g ∈ QP45.originalSubgroup ∧ g * z0 = z0 * g := by
  simp [bl, elemsTab_eq, mem_elemsT QP45 QP45_ok]

theorem bl_nodup : bl.Nodup := by
  rw [bl, elemsTab_eq]
  exact (nodup_elemsT QP45 QP45_ok).filter _

theorem mem_pl {g : Equiv.Perm (Fin 45)} : g ∈ pl ↔ g ∈ bl ∧ g ∈ pcl := by
  simp [pl]

theorem pl_nodup : pl.Nodup := bl_nodup.filter _

theorem bl_card : bl.length = 648 :=
  Certificates.certificate450100.1

theorem pl_card : pl.length = 27 :=
  Certificates.certificate450100.2.1

theorem pl_mul : ∀ x ∈ pl, ∀ y ∈ pl, x * y ∈ pl := by
  have h := Certificates.certificate450100.2.2.1
  simpa [plMulCheck, List.all_eq_true] using h

theorem pl_exp : ∀ x ∈ pl, x ^ 3 = 1 := by
  have h := Certificates.certificate450100.2.2.2.1
  simpa [plExpCheck, List.all_eq_true] using h

theorem bl_norm : ∀ x ∈ bl, ∀ p ∈ pl, x * p * x⁻¹ ∈ pl := by
  have h := Certificates.certificate450100.2.2.2.2.1
  simpa [blNormCheck, List.all_eq_true] using h

theorem z0_data :
    z0 ≠ 1 ∧ (∃ x ∈ pl, ∃ y ∈ pl, z0 = x * y * x⁻¹ * y⁻¹) ∧
      ∀ a ∈ pl, a ≠ 1 → a ≠ z0 → a⁻¹ ≠ z0 → ∃ R : List (Equiv.Perm (Fin 45)), R.length ≤ 6 ∧
        ∀ x ∈ bl, (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹) → ∃ r ∈ R, x * r⁻¹ ∈ pl := by
  have h := Certificates.certificate450100.2.2.2.2.2
  simp only [zDataCheck, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hz1, hc⟩, hall⟩ := h
  refine ⟨hz1, ?_, fun a ha ha1 haz haz' => ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hc
    exact ⟨x, hx, y, hy, hxy⟩
  · have hca := hall a ha
    simp only [ha1, haz, haz', decide_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
      false_or] at hca
    simp only [cosetCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true] at hca
    refine ⟨cosetReps (conjSet a), hca.1, fun x hx hxa => ?_⟩
    obtain ⟨r, hr, hxr⟩ := hca.2 x (by
      simp only [conjSet, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨hx, hxa⟩)
    exact ⟨r, hr, hxr⟩

@[expose] def bSub : Subgroup (Equiv.Perm (Fin 45)) :=
  QP45.originalSubgroup ⊓ Subgroup.centralizer {z0}

theorem mem_bSub {g : Equiv.Perm (Fin 45)} :
    g ∈ bSub ↔ g ∈ QP45.originalSubgroup ∧ g * z0 = z0 * g := by
  simp [bSub, Subgroup.mem_centralizer_iff, eq_comm]

@[expose] def pSub : Subgroup (Equiv.Perm (Fin 45)) where
  carrier := {g | g ∈ pl}
  mul_mem' {a b} ha hb := pl_mul a ha b hb
  one_mem' := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ pl := List.exists_mem_of_length_pos (by rw [pl_card]; norm_num)
    have h := pl_mul x hx (x * x) (pl_mul x hx x hx)
    have h3 := pl_exp x hx
    rwa [← pow_three, h3] at h
  inv_mem' {a} ha := by
    have h3 := pl_exp a ha
    have : a⁻¹ = a * a := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_three]
      exact h3
    show a⁻¹ ∈ pl
    rw [this]
    exact pl_mul a ha a ha

theorem mem_pSub {g : Equiv.Perm (Fin 45)} :
    g ∈ pSub ↔ g ∈ pl := Iff.rfl

theorem card_subgroup_eq_length {S : Type*} [Group S] {E : Subgroup S} {El : List S}
    (hEl : ∀ x, x ∈ E ↔ x ∈ El) (hnd : El.Nodup) : Nat.card E = El.length := by
  classical
  have hset : (E : Set S) = ↑El.toFinset := by
    ext x
    simp [hEl x]
  have : Nat.card E = (E : Set S).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem card_bSub :
    Nat.card bSub = 648 := by
  rw [card_subgroup_eq_length (fun x => mem_bSub.trans mem_bl.symm) bl_nodup, bl_card]

theorem card_pSub :
    Nat.card pSub = 27 := by
  rw [card_subgroup_eq_length (fun x => mem_pSub) pl_nodup, pl_card]

theorem pSub_le_bSub :
    pSub ≤ bSub := fun _ hg => mem_bSub.2 (mem_bl.1 (mem_pl.1 (mem_pSub.1 hg)).1)

instance : Finite bSub :=
  Nat.finite_of_card_ne_zero (by rw [card_bSub]; norm_num)

theorem bSub_le : bSub ≤ QP45.originalSubgroup := fun _ hg => (mem_bSub.1 hg).1

theorem exists_z_small_index :
    ∃ z : Equiv.Perm (Fin 45), z ∈ pSub ∧ z ≠ 1 ∧
      ∀ K : Subgroup (Equiv.Perm (Fin 45)), K ≤ bSub → 24 < Nat.card K → z ∈ K := by
  obtain ⟨hz1, ⟨x0, hx0, y0, hy0, hzc⟩, hN⟩ := z0_data
  have hnormP : ∀ x ∈ bSub, ∀ p ∈ pSub, x * p * x⁻¹ ∈ pSub := fun x hx p hp =>
    mem_pSub.2 (bl_norm x (mem_bl.2 (mem_bSub.1 hx)) p (mem_pSub.1 hp))
  have hzP : z0 ∈ pSub := by
    have hx0' : x0 ∈ pSub := mem_pSub.2 hx0
    have hy0' : y0 ∈ pSub := mem_pSub.2 hy0
    rw [hzc]
    exact mul_mem (mul_mem (mul_mem hx0' hy0') (inv_mem hx0')) (inv_mem hy0')
  refine ⟨z0, hzP, hz1, fun K hKB hK => ?_⟩
  by_contra hzK
  have hmain := card_le_24_of_not_mem bSub pSub pSub_le_bSub hnormP card_pSub card_bSub
    (fun p hp => pl_exp p (mem_pSub.1 hp)) (z := z0) ⟨x0, mem_pSub.2 hx0, y0, mem_pSub.2 hy0, hzc⟩
    ?_ K hKB hzK
  · omega
  · intro a haP ha1 haz haz'
    obtain ⟨R, hRlen, hRmem⟩ := hN a haP ha1 haz haz'
    refine ⟨R.toFinset, (List.toFinset_card_le R).trans hRlen, fun x hx hxa => ?_⟩
    obtain ⟨r, hr, hxr⟩ := hRmem x (mem_bl.2 (mem_bSub.1 hx)) hxa
    exact ⟨r, List.mem_toFinset.2 hr, hxr⟩

theorem exists_z_action :
    ∃ z : ↥QP45.originalSubgroup, z ≠ 1 ∧
      ∀ (Ψ : Type) [Finite Ψ], Nat.card Ψ ≤ 26 →
        ∀ β : ↥QP45.originalSubgroup →* Equiv.Perm Ψ, β z = 1 := by
  obtain ⟨z, hzP, hz1, hz⟩ := exists_z_small_index
  have hzG : z ∈ QP45.originalSubgroup := (mem_bl.1 (mem_pl.1 (mem_pSub.1 hzP)).1).1
  refine ⟨⟨z, hzG⟩, fun h => hz1 (congrArg Subtype.val h), ?_⟩
  intro Ψ _ hΨ β
  by_contra hβ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, β ⟨z, hzG⟩ ψ ≠ ψ := by
    by_contra h
    push Not at h
    exact hβ (Equiv.ext h)
  set B' : Subgroup ↥QP45.originalSubgroup := bSub.subgroupOf QP45.originalSubgroup with hB'
  let _ : MulAction B' Ψ := MulAction.compHom Ψ (β.comp B'.subtype)
  have hB'card : Nat.card B' = 648 := by
    rw [← card_bSub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe bSub_le).toEquiv
  set Kb : Subgroup B' := MulAction.stabilizer B' ψ with hKb
  have h1 := Subgroup.card_mul_index Kb
  have h2 : Kb.index = (MulAction.orbit B' ψ).ncard := MulAction.index_stabilizer B' ψ
  have h3 : (MulAction.orbit B' ψ).ncard ≤ Nat.card Ψ := Set.ncard_le_card _
  set K : Subgroup (Equiv.Perm (Fin 45)) :=
    (Kb.map B'.subtype).map QP45.originalSubgroup.subtype with hK
  have hKcard : Nat.card K = Nat.card Kb := by
    rw [hK, Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective Subtype.val_injective]
  have hKB : K ≤ bSub := by
    rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.1 b.2
  have hzK : z ∉ K := by
    rintro ⟨_, ⟨b, hb, rfl⟩, hbz⟩
    have hbz' : (b : ↥QP45.originalSubgroup) = ⟨z, hzG⟩ := Subtype.ext hbz
    have : β ⟨z, hzG⟩ ψ = ψ := by
      rw [← hbz']
      exact hb
    exact hψ this
  have hbig : 24 < Nat.card K := by
    rw [hKcard]
    by_contra hle
    push Not at hle
    have hidx : Kb.index ≤ 26 := by omega
    have := Nat.mul_le_mul hle hidx
    omega
  exact hzK (hz K hKB hbig)

theorem action_eq_one_of_simple_u42
    {G : Type*} [Group G] [IsSimpleGroup G] (e : G ≃* ↥QP45.originalSubgroup) {Ψ : Type}
    [Finite Ψ] (hΨ : Nat.card Ψ ≤ 26) (α : G →* Equiv.Perm Ψ) : α = 1 := by
  obtain ⟨z, hz1, hz⟩ := exists_z_action
  have h := hz Ψ hΨ (α.comp e.symm.toMonoidHom)
  have hmem : e.symm z ∈ α.ker := by
    rw [MonoidHom.mem_ker]
    exact h
  have hne : e.symm z ≠ 1 := fun h1 => hz1 (by simpa using congrArg e h1)
  have hker : α.ker = ⊤ := by
    rcases (inferInstance : α.ker.Normal).eq_bot_or_eq_top with h0 | h0
    · rw [h0, Subgroup.mem_bot] at hmem
      exact absurd hmem hne
    · exact h0
  refine MonoidHom.ext fun g => ?_
  have : g ∈ α.ker := hker ▸ Subgroup.mem_top g
  rw [MonoidHom.one_apply]
  exact MonoidHom.mem_ker.1 this

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex

theorem nonempty_mulEquiv_qp45_of_statedClassicalModel
    {U : Type} [Group U] (hU : CFSG.Open.StatedClassicalModel U .PSU 4 2 1) :
    Nonempty (U ≃* QP45.originalSubgroup) :=
  equiv_of_lieModel (Or.inl ⟨by decide,
    CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hU⟩)

theorem hom_eq_one_of_statedClassicalModel_psu42
    {U : Type} [Group U]
    (hU : CFSG.Open.StatedClassicalModel U .PSU 4 2 1) {n : ℕ} (hn : n ≤ 26)
    (φ : U →* Equiv.Perm (Fin n)) : φ = 1 := by
  haveI : IsSimpleGroup U := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity U 4 2 1 hU).2
  obtain ⟨e⟩ := nonempty_mulEquiv_qp45_of_statedClassicalModel hU
  exact action_eq_one_of_simple_u42 e (by simpa using hn) φ

theorem perm_inn_of_statedClassicalModel
    {A : Type} [Group A] {U : Type} [Group U]
    (hU : CFSG.Open.StatedClassicalModel U .PSU 4 2 1) (e : A ≃* MulAut U) {n : ℕ} (hn : n ≤ 26)
    (φ : A →* Equiv.Perm (Fin n)) (u : U) : φ (e.symm (MulAut.conj u)) = 1 := by
  have h := hom_eq_one_of_statedClassicalModel_psu42 hU hn
    (φ.comp ((e.symm : MulAut U →* A).comp MulAut.conj))
  exact DFunLike.congr_fun h u

theorem inn_le_ker_perm
    {A : Type} [Group A] {U : Type} [Group U] (hU : CFSG.Open.StatedClassicalModel U .PSU 4 2 1)
    (e : A ≃* MulAut U) {n : ℕ} (hn : n ≤ 26) (φ : A →* Equiv.Perm (Fin n)) :
    Subgroup.map (e.symm : MulAut U →* A) (MulAut.conj : U →* MulAut U).range ≤ φ.ker := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact perm_inn_of_statedClassicalModel hU e hn φ u

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
