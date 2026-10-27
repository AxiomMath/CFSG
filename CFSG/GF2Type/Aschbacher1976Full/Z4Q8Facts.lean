module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_two {z x : G} (hz : orderOf z = 2) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : z ^ k = z ^ (k % 2) := by
    have h := zpow_mod_orderOf z k
    rw [hz] at h
    exact_mod_cast h.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem card_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) : Nat.card (Fz z) = 16 := by
  obtain ⟨Z, A, -, -, hZ4, -, -, hA8, -, hAc, hsup, hinf⟩ := unpack hZ hz
  have key := natCard_inf_mul_natCard_sup Z A hAc
  rw [hinf, hsup, Nat.card_zpowers, hz, hZ4, hA8] at key
  omega

theorem sq_mem_zpowers_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {x : G}
    (hx : x ∈ Fz z) : x ^ 2 ∈ Subgroup.zpowers z := by
  obtain ⟨Z, A, -, hZc, hZ4, hzZ, hA, hA8, hzA, hAc, hsup, -⟩ := unpack hZ hz
  have hxF : x ∈ Z ⊔ A := by rw [hsup]; exact hx
  obtain ⟨c, hc, a, ha, rfl⟩ := (mem_sup_iff' hAc).mp hxF
  have hc4 : c ^ 4 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨c, hc⟩ : ↥Z)))
    rw [hZ4] at h
    simpa using h
  have hcc : c * c ∈ Subgroup.zpowers z := by
    have h2 : (c * c) ^ 2 = 1 := by
      calc (c * c) ^ 2 = c ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := hc4
    rcases involution_eq_one_or_eq hZc hz hzZ (Z.mul_mem hc hc) h2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  have haa : a * a ∈ Subgroup.zpowers z := by
    have := sq_mem_zpowers_of_extraspecial hA hA8 hzA hz (fun b hb => (hAc z hzZ b hb)) ha
    simpa [sq] using this
  have e : (c * a) ^ 2 = (c * c) * (a * a) := by
    rw [sq]
    calc c * a * (c * a) = c * (a * c) * a := by group
      _ = c * (c * a) * a := by rw [hAc c hc a ha]
      _ = (c * c) * (a * a) := by group
  rw [e]
  exact Subgroup.mul_mem _ hcc haa

theorem comm_mem_zpowers_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {x y : G}
    (hx : x ∈ Fz z) (hy : y ∈ Fz z) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨Z, A, -, hZc, -, hzZ, hA, hA8, hzA, hAc, hsup, -⟩ := unpack hZ hz
  have hxF : x ∈ Z ⊔ A := by rw [hsup]; exact hx
  have hyF : y ∈ Z ⊔ A := by rw [hsup]; exact hy
  obtain ⟨c, hc, a, ha, rfl⟩ := (mem_sup_iff' hAc).mp hxF
  obtain ⟨c', hc', a', ha', rfl⟩ := (mem_sup_iff' hAc).mp hyF
  have e1 : c * a * (c' * a') = (c * c') * (a * a') := by
    calc c * a * (c' * a') = c * (a * c') * a' := by group
      _ = c * (c' * a) * a' := by rw [hAc c' hc' a ha]
      _ = (c * c') * (a * a') := by group
  have e2 : c' * a' * (c * a) = (c * c') * (a' * a) := by
    calc c' * a' * (c * a) = c' * (a' * c) * a := by group
      _ = c' * (c * a') * a := by rw [← hAc c hc a' ha']
      _ = (c' * c) * (a' * a) := by group
      _ = (c * c') * (a' * a) := by rw [comm_of_mem_cyclic hZc hc' hc]
  have hd : a * a' * a⁻¹ * a'⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')
  have hcc : (c * c') * (a * a' * a⁻¹ * a'⁻¹) = (a * a' * a⁻¹ * a'⁻¹) * (c * c') :=
    hAc (c * c') (Z.mul_mem hc hc') _ hd
  have key : c * a * (c' * a') * (c * a)⁻¹ * (c' * a')⁻¹ =
      (c * c') * (a * a' * a⁻¹ * a'⁻¹) * (c * c')⁻¹ := by
    calc c * a * (c' * a') * (c * a)⁻¹ * (c' * a')⁻¹
        = (c * a * (c' * a')) * (c' * a' * (c * a))⁻¹ := by group
      _ = ((c * c') * (a * a')) * ((c * c') * (a' * a))⁻¹ := by rw [e1, e2]
      _ = (c * c') * (a * a' * a⁻¹ * a'⁻¹) * (c * c')⁻¹ := by group
  rw [key, hcc]
  have h3 : (a * a' * a⁻¹ * a'⁻¹) * (c * c') * (c * c')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by group
  rw [h3]
  exact comm_mem_zpowers_of_extraspecial hA hA8 hzA hz (fun b hb => hAc z hzZ b hb) ha ha'

theorem commutator_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    ⁅Fz z, Fz z⁆ = Subgroup.zpowers z := by
  obtain ⟨Z, A, -, -, -, hzZ, hA, hA8, hzA, hAc, hsup, -⟩ := unpack hZ hz
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact comm_mem_zpowers_Fz hZ hz hx hy
  · have hzmem : z ∈ ⁅Fz z, Fz z⁆ := by
      obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_extraspecial hA hA8
      have h1 : ⁅a, b⁆ ∈ Subgroup.zpowers z := by
        rw [commutatorElement_def]
        exact comm_mem_zpowers_of_extraspecial hA hA8 hzA hz (fun c hc => hAc z hzZ c hc) ha hb
      have h2 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
      have h3 : ⁅a, b⁆ = z := (mem_zpowers_two hz h1).resolve_left h2
      have haF : a ∈ Fz z := by rw [← hsup]; exact Subgroup.mem_sup_right ha
      have hbF : b ∈ Fz z := by rw [← hsup]; exact Subgroup.mem_sup_right hb
      have hmem := Subgroup.commutator_mem_commutator haF hbF
      rw [h3] at hmem
      exact hmem
    exact Subgroup.zpowers_le.mpr hzmem

theorem mem_center_Fz_iff {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {x : ↥(Fz z)} :
    x ∈ Subgroup.center ↥(Fz z) ↔ (x : G) ∈ Zc z := by
  obtain ⟨Z, A, hZeq, -⟩ := unpack hZ hz
  constructor
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem z_mem_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) : z ∈ Zc z := by
  obtain ⟨Z, A, hZeq, -, -, hzZ, -⟩ := unpack hZ hz
  rw [hZeq]
  exact hzZ

theorem zpowers_le_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    Subgroup.zpowers z ≤ Zc z :=
  Subgroup.zpowers_le.mpr (z_mem_Zc hZ hz)

theorem isCyclic_center_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    IsCyclic ↥(Subgroup.center ↥(Fz z)) := by
  obtain ⟨Z, A, hZeq, hZc, -⟩ := unpack hZ hz
  have hcyc : IsCyclic ↥(Subgroup.map (Fz z).subtype (Subgroup.center ↥(Fz z))) := by
    show IsCyclic ↥(Zc z)
    rw [hZeq]
    exact hZc
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ (Fz z).subtype
    Subtype.val_injective)).mpr hcyc

theorem isElementaryAbelian_quot_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    IsElementaryAbelian 2 (↥(Fz z) ⧸ Subgroup.center ↥(Fz z)) := by
  have hmem : ∀ x y : ↥(Fz z), (x * y)⁻¹ * (y * x) ∈ Subgroup.center ↥(Fz z) := by
    intro x y
    rw [mem_center_Fz_iff hZ hz]
    have h := comm_mem_zpowers_Fz hZ hz (Subgroup.inv_mem _ y.2) (Subgroup.inv_mem _ x.2)
    have e : (((x * y)⁻¹ * (y * x) : ↥(Fz z)) : G) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e]
    exact zpowers_le_Zc hZ hz h
  have hc : ∀ a b : ↥(Fz z) ⧸ Subgroup.center ↥(Fz z), a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact QuotientGroup.eq.mpr (hmem x y)
  have hsq : ∀ a : ↥(Fz z) ⧸ Subgroup.center ↥(Fz z), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_Fz_iff hZ hz]
      have h := sq_mem_zpowers_Fz hZ hz x.2
      rw [SubgroupClass.coe_pow]
      exact zpowers_le_Zc hZ hz h
  have htop := CFSG.IsElementaryAbelian.two_of_forall_mul_self (E := (⊤ : Subgroup (↥(Fz z) ⧸ Subgroup.center ↥(Fz z))))
    (fun a _ b _ => hc a b) (fun a _ => by rw [← pow_two]; exact hsq a)
  exact CFSG.IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv htop

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
