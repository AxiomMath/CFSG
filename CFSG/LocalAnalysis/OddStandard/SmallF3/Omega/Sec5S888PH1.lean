module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH0

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H}

private lemma sec5s888ph1_pow4_map {i : Fin 4} {e : ↥(K i) ≃* SL23} (u : ↥(K i)) :
    (e u) ^ 4 = 1 ↔ (u : H) ^ 4 = 1 := by
  have hmap : e (u ^ 4) = (e u) ^ 4 := map_pow e u 4
  constructor
  · intro h
    have hsub : u ^ 4 = 1 := e.injective (by rw [hmap, map_one]; exact h)
    simpa using congrArg (fun x : ↥(K i) => (x : H)) hsub
  · intro h
    have hsub : u ^ 4 = 1 := by
      apply Subtype.ext
      simpa using h
    rw [← hmap, hsub, map_one]

private lemma sec5s888ph1_map_subgroupOf (hq : Sec5B517Quad K z) (i : Fin 4)
    (e : ↥(K i) ≃* SL23) :
    ((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)).map (e : ↥(K i) →* SL23) = sl23Q8 := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_sl23Q8]
    exact (sec5s888ph1_pow4_map a).2
      (Sec5B517Q8.pow_four hq (Subgroup.mem_subgroupOf.mp ha).1)
  · intro hx
    rw [mem_sl23Q8] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact Subgroup.mem_subgroupOf.mpr
      ⟨Sec5B517Q8.mem_of_mem hq (e.symm x).2
        ((sec5s888ph1_pow4_map (e.symm x)).1 (by rw [e.apply_symm_apply]; exact hx)),
      (e.symm x).2⟩

theorem mem_inf_K_iff (hq : Sec5B517Quad K z) (i : Fin 4) {u : H} :
    u ∈ Sec5B517Q8 hq ⊓ K i ↔ u ∈ K i ∧ u ^ 4 = 1 := by
  constructor
  · intro h
    exact ⟨h.2, Sec5B517Q8.pow_four hq h.1⟩
  · rintro ⟨hu, h4⟩
    exact ⟨Sec5B517Q8.mem_of_mem hq hu h4, hu⟩

theorem z_mem_Q8 (hq : Sec5B517Quad K z) : z ∈ Sec5B517Q8 hq := by
  refine Sec5B517Q8.mem_of_mem hq (hq.z_mem 0) ?_
  have h : z ^ 2 = 1 := by rw [pow_two]; exact hq.z_sq
  calc z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [h, one_pow]

theorem z_mem_inf_K (hq : Sec5B517Quad K z) (i : Fin 4) : z ∈ Sec5B517Q8 hq ⊓ K i :=
  ⟨z_mem_Q8 hq, hq.z_mem i⟩

theorem card_inf_K (hq : Sec5B517Quad K z) (i : Fin 4) :
    Nat.card ↥(Sec5B517Q8 hq ⊓ K i) = 8 := by
  obtain ⟨e⟩ := hq.iso i
  have h1 : Nat.card ↥((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)) =
      Nat.card ↥(Sec5B517Q8 hq ⊓ K i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h2 : Nat.card ↥(((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)).map
        (e : ↥(K i) →* SL23)) =
      Nat.card ↥((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)) :=
    Subgroup.card_map_of_injective (f := (e : ↥(K i) →* SL23)) e.injective
  calc Nat.card ↥(Sec5B517Q8 hq ⊓ K i)
      = Nat.card ↥((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)) := h1.symm
    _ = Nat.card ↥(((Sec5B517Q8 hq ⊓ K i).subgroupOf (K i)).map
          (e : ↥(K i) →* SL23)) := h2.symm
    _ = Nat.card ↥sl23Q8 := by rw [sec5s888ph1_map_subgroupOf hq i e]
    _ = 8 := by rw [← sl23_pCore_eq_Q8]; exact sl23_card_pCore

theorem planeW_le (hq : Sec5B517Quad K z) (α : H →* X) (i : Fin 4) :
    planeW hq α i ≤ planeV hq α :=
  Subgroup.map_mono inf_le_left

theorem card_planeW [Finite H] {α : H →* X} (hS : PlaneSetup z K α) (i : Fin 4) :
    Nat.card ↥(planeW hS.quad α i) = 4 := by
  let A : Subgroup H := Sec5B517Q8 hS.quad ⊓ K i
  have hkerle : α.ker ≤ A := by
    rw [hS.ker]
    exact Subgroup.zpowers_le.mpr (z_mem_inf_K hS.quad i)
  let f : ↥A →* X := α.comp A.subtype
  have hker_eq : f.ker = (α.ker).subgroupOf A := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hrange_eq : f.range = A.map α := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hcardker : Nat.card ↥f.ker = 2 := by
    have hsub : Nat.card ↥((α.ker).subgroupOf A) = Nat.card ↥(α.ker) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
    rw [hker_eq, hsub, hS.ker, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hS.quad.z_sq) hS.quad.z_ne
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hcardker, card_inf_K hS.quad i] at hmul
  rw [hrange_eq] at hmul
  change Nat.card ↥(A.map α) = 4
  omega

end CFSG.OddStandard.SmallF3.Omega
