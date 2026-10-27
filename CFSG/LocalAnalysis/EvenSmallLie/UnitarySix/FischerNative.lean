module

public import CFSG.Fischer.Polar.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModel
public import Certificates.Certificate3145

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Certificates

theorem tvP_val (p q : Fin 693) :
    (tvP p q).val = ap tvTabs[p.val]! q.val := by
  rw [rep_tvP p q.val q.2, idx_of_lt _ q.2]
  rfl

theorem swapOK_eq : swapOK = true :=
  Certificates.certificate3145.1

theorem tvP_swap
    {p q : Fin 693} (hpq : ¬ perp p q) : tvP p q = tvP q
    p := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 swapOK_eq p.val (List.mem_range.2 p.2))
    q.val (List.mem_range.2 q.2)
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd (tvP_apply_eq_self_iff.1 (Fin.ext (by rw [tvP_val, h]))) hpq
  · exact Fin.ext (by rw [tvP_val, tvP_val, h])

theorem fixOK_eq : fixOK = true :=
  Certificates.certificate3145.2

theorem mem_fixA_of_maps {m : Fin 693}
    (h : ∀ q ∈ finSet 693 fixA, tvP m q ∈ finSet 693 fixA) : m ∈ finSet 693 fixA := by
  have hm := List.all_eq_true.1 fixOK_eq m.val (List.mem_range.2 m.2)
  rw [Bool.or_eq_true, List.any_eq_true] at hm
  rcases hm with hm | ⟨q, hq, hq'⟩
  · exact List.contains_iff_mem.1 hm
  · have hq693 : q < 693 := by
      have : ∀ x ∈ fixA, x < 693 := by decide
      exact this q hq
    have h1 : (tvP m ⟨q, hq693⟩).val ∈ fixA := h ⟨q, hq693⟩ hq
    rw [tvP_val] at h1
    rw [Bool.not_eq_true', List.contains_iff_mem.2 h1] at hq'
    exact absurd hq' (by decide)

theorem mem_uA_of_mem_normalizer
    {m : Fin 693}
    (hm : tvP m ∈ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693)))) : tvP m ∈ uA := by
  have hU := smul_fixed_j3 hm
  rw [fixed_j3] at hU
  have hmU : m ∈ finSet 693 fixA := by
    refine mem_fixA_of_maps fun q hq => ?_
    rw [← hU]
    exact ⟨q, hq, rfl⟩
  have hc : tvP m ∈ T46 ⊓ Subgroup.centralizer (uA : Set (Equiv.Perm (Fin 693))) := by
    refine ⟨tvP_mem m, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have e := (isPolarAut_of_mem (uA_le_T46 ha)).mul_tvP_mul_inv m
    rw [uA_fix a ha m hmU] at e
    calc a * tvP m = a * tvP m * a⁻¹ * a := by group
      _ = tvP m * a := by rw [e]
  rwa [centralizer_uA] at hc

end CFSG.EvenSmallLie.UnitarySix.Fischer
