module

public import CFSG.LargeExtraspecial.Asc611IStepE4
public import CFSG.LargeExtraspecial.Asc611Model
public import CFSG.LargeExtraspecial.Asc611IStepD

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

namespace Asc611I

variable {m : ℕ}

theorem exists_frame2 {e : SUid frob m} (he : e * e = 1)
    (he1 : (QuotientGroup.mk e : PG m) ≠ 1) (heD : (QuotientGroup.mk e : PG m) ∉ DG m) :
    ∃ q y : Fin m → K, Frame2 e q y := by
  by_cases hall : ∀ a, herm frob a (invN e a) = 0
  · exfalso
    apply he1
    rw [show e = 1 from ext_smul _ fun b => by
      rw [smul_eq_invN_add, invN_eq_zero_of_diag he hall, zero_add, one_smul],
      QuotientGroup.mk_one]
  push Not at hall
  obtain ⟨q₀, hq₀⟩ := hall
  have hq₁ := (herm_invN_self he q₀).resolve_left hq₀
  by_cases hrank : ∀ y, herm frob q₀ (invN e y) = 0 → herm frob y (invN e y) = 0
  · obtain ⟨hp0, hpp, heq⟩ := eq_tvU_of_rank_one he hq₁ hrank
    exact absurd (by rw [heq]; exact tq_mem_DG hp0 hpp) heD
  push Not at hrank
  obtain ⟨y₀, hqy, hy₀⟩ := hrank
  have hy₁ := (herm_invN_self he y₀).resolve_left hy₀
  obtain ⟨p, x, q, y, -, -, hNq, hNy, -, -, hqq, hyy, -, hpq, -, hxq, hxy, hqy'⟩ :=
    exists_frame he hq₁ hy₁ hqy
  refine ⟨q, y, ⟨?_, ?_, ?_, hqq, hyy, hqy'⟩⟩
  · rw [hNq, herm_conj frob frob_frob p q, hpq, map_one]
  · rw [hNy, herm_conj frob frob_frob x y, hxy, map_one]
  · rw [hNy, herm_conj frob frob_frob x q, hxq, map_zero]

theorem eq_one_or_eq_of_mem {e : SUid frob m} {U : Subgroup (PG m)} (S : Setup e U)
    (hEU : (QuotientGroup.mk e : PG m) ∈ U)
    (hUC : U ≤ centralizer ({(QuotientGroup.mk e : PG m)} : Set (PG m))) {q y : Fin m → K}
    (F : Frame2 e q y) {u : PG m} (hu : u ∈ U) : u = 1 ∨ u = QuotientGroup.mk e := by
  have he := S.invol
  obtain ⟨k, rfl, hke, r, hkr⟩ := exists_lift S.three_le he S.isPGroup hUC hu
  have hkN := invN_smul_eq S.three_le he S.isPGroup S.normal hu hke hkr F.hq F.hy F.hqy
  have hker : ∀ v, invN e v = 0 → k • v = v := fun v hv => smul_eq_of_ker S hu hke hkN F hv
  have hperp : ∀ x b, invN e b = 0 → herm frob (k • x + x) b = 0 := fun x b hb =>
    smul_add_perp_all S hu hke hkN F x hb
  have hHc : ∀ x z : Fin m → K, herm frob z (invN e x) = frob (herm frob x (invN e z)) :=
    fun x z => herm_invN_swap he x z
  have hBs : IsSesq (fun x z : Fin m → K => herm frob x (k • z + z)) :=
    { add_left := fun x x' z => herm_add_left frob x x' _
      add_right := fun x z z' => by
        rw [smul_add, show k • z + k • z' + (z + z') = (k • z + z) + (k • z' + z') by abel,
          herm_add_right]
      smul_left := fun c x z => herm_smul_left frob c x _
      smul_right := fun c x z => by
        rw [smul_comm k c z, ← smul_add, herm_smul_right] }
  have hS0 : ∀ a, herm frob a (invN e a) = 0 → herm frob a (k • a + a) = 0 := by
    intro a ha
    by_cases hNa : invN e a = 0
    · rw [hker a hNa, vec_add_self, herm_zero_right]
    · obtain ⟨z, c, hiso⟩ := exists_isotropic_shift he hNa
      have hw0 : invN e (c • invN e z) = 0 := by rw [invN_smul, invN_invN he, smul_zero]
      have hkw : k • (c • invN e z) = c • invN e z := by rw [smul_comm, smul_invN hke hkN]
      have h1 := herm_self_shift_eq_zero S hEU hu hke hkN hker hperp hiso
        (isoN_add_ker he ha hw0)
      have hw : herm frob (c • invN e z) (k • a + a) = 0 := by
        rw [herm_smul_left, herm_invN_left he, invN_add, hkN, vec_add_self, herm_zero_right,
          mul_zero]
      rw [smul_add, hkw, show k • a + c • invN e z + (a + c • invN e z) = k • a + a by
        rw [add_add_add_comm, vec_add_self, add_zero], herm_add_left, hw, add_zero] at h1
      exact h1
  have hZ := eq_smul_of_isotropic (isSesq_H e) hHc hBs hS0 F.hq F.hy F.hqy
  set μ := herm frob q (k • q + q) with hμ
  have hk' : ∀ z, k • z = z + μ • invN e z := by
    intro z
    have h : k • z + z = μ • invN e z := by
      rw [← sub_eq_zero]
      refine eq_zero_of_herm frob fun x => ?_
      rw [herm_conj frob frob_frob, sub_eq_add_neg, herm_add_right, herm_neg_right,
        herm_smul_right]
      rw [hZ x z, add_neg_cancel, map_zero]
    rw [← h, add_comm (k • z), ← add_assoc, vec_add_self, zero_add]
  have hNqq : herm frob (invN e q) q = 1 := by rw [herm_invN_left he, F.hq]
  have hμ2 : μ + frob μ = 0 := by
    have h1 : herm frob (k • q) (k • q) = herm frob q q := herm_smul_smul frob k q q
    rw [hk', herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_right,
      herm_smul_left, herm_smul_right, F.hq, hNqq, herm_invN_invN he] at h1
    linear_combination h1
  rcases (add_frob_eq_zero_iff μ).1 hμ2 with h0 | h1
  · left
    rw [show k = 1 from ext_smul _ fun z => by rw [hk', h0, zero_smul, add_zero, one_smul],
      QuotientGroup.mk_one]
  · right
    rw [show k = e from ext_smul _ fun z => by rw [hk', h1, one_smul, smul_eq_invN_add e z,
      add_comm]]

end Asc611I

namespace S14

theorem unitaryInnerCentStmt : UnitaryInnerCentStmt := by
  intro m hm e he he1 heD U hU heU hUC hUN hUD
  have S : Asc611I.Setup e U := ⟨by omega, he, hU, hUN, hUD⟩
  obtain ⟨q, y, F⟩ := Asc611I.exists_frame2 he he1 heD
  have hsub : (U : Set (PG m)) ⊆ {1, QuotientGroup.mk e} := fun u hu => by
    rcases Asc611I.eq_one_or_eq_of_mem S heU hUC F hu with h | h
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]; exact Set.mem_insert_of_mem _ rfl
  calc Nat.card U = (U : Set (PG m)).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, QuotientGroup.mk e} : Set (PG m)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 2 := Set.ncard_pair (fun h => he1 h.symm)

end S14

end CFSG.LargeExtraspecial
