module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.KGroups.Checks3
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Certificate2022
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34RankInputs
public import Certificates.Certificate2011

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.PSL3Four

local notation "P42" => Equiv.Perm (Fin 42)

namespace L34

theorem QS_valid : QS.check = true ∧ QS.orderCertificate = 20160 :=
  Certificates.certificate2011.1

theorem QE_valid : QE.check = true ∧ QE.orderCertificate = 16 :=
  Certificates.certificate2011.2.1

theorem QS_ok : ValidSchreier QS := QS_valid.1

theorem QE_ok : ValidSchreier QE := QE_valid.1

theorem class_ok : classCheck (elemsT QS) g₂ conjugators = true :=
  Certificates.certificate2011.2.2.1

theorem sq_ok : sqOneCheck (elemsT QE) = true :=
  Certificates.certificate2011.2.2.2.1

theorem indep_ok : indepCheck g₂ g₃ c₁ = true :=
  Certificates.certificate2011.2.2.2.2

theorem QS_eq : QS.originalSubgroup = S := by
  rw [QS, certificate_originalSubgroup]
  unfold S
  congr 1
  ext g
  simp [tab_eq]

theorem c₁_mem_S : c₁ ∈ S :=
  mul_mem (mul_mem (mul_mem g₂_mem_S (mul_mem (mul_mem g₁_mem_S g₂_mem_S) (inv_mem g₁_mem_S)))
    (inv_mem g₂_mem_S)) (inv_mem (mul_mem (mul_mem g₁_mem_S g₂_mem_S) (inv_mem g₁_mem_S)))

theorem c₂_mem_S : c₂ ∈ S :=
  mul_mem (mul_mem (mul_mem g₃_mem_S (mul_mem (mul_mem g₁_mem_S g₂_mem_S) (inv_mem g₁_mem_S)))
    (inv_mem g₃_mem_S)) (inv_mem (mul_mem (mul_mem g₁_mem_S g₂_mem_S) (inv_mem g₁_mem_S)))

theorem QE_eq : QE.originalSubgroup = closure {g₂, g₃, c₁, c₂} := by
  rw [QE, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem QE_le : QE.originalSubgroup ≤ S := by
  rw [QE_eq, closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · exact g₂_mem_S
  · exact g₃_mem_S
  · exact c₁_mem_S
  · exact c₂_mem_S

theorem g₂_mem_E : g₂ ∈ QE.originalSubgroup := by
  rw [QE_eq]
  exact subset_closure (by simp)

theorem g₃_mem_E : g₃ ∈ QE.originalSubgroup := by
  rw [QE_eq]
  exact subset_closure (by simp)

theorem c₁_mem_E : c₁ ∈ QE.originalSubgroup := by
  rw [QE_eq]
  exact subset_closure (by simp)

theorem card_E : Nat.card QE.originalSubgroup = 16 := by
  rw [card_group QE QE_ok, QE_valid.2]

theorem conjugators_mem : ∀ c ∈ conjugators, c ∈ S := by
  intro c hc
  simp only [conjugators, List.mem_map] at hc
  obtain ⟨w, -, rfl⟩ := hc
  rw [tab_eq]
  refine evalCodes_mem_of_gens _ S (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [tab_eq]; exact g₁_mem_S
  · rw [tab_eq]; exact g₂_mem_S
  · rw [tab_eq]; exact g₃_mem_S

theorem one_class {x : P42} (hx : x ∈ S) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ S, g * g₂ * g⁻¹ = x := by
  have h := List.all_eq_true.1 class_ok x ((mem_elemsT QS QS_ok x).2 (QS_eq ▸ hx))
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with (h | h) | ⟨c, hc, hcx⟩
  · exact absurd hx2 h
  · exact absurd h hx1
  · exact ⟨c, conjugators_mem c hc, hcx⟩

theorem sq_E : ∀ x ∈ QE.originalSubgroup, x ^ 2 = 1 := sqOneCheck_sound QE QE_ok sq_ok

theorem conj_E : ∀ x ∈ QE.originalSubgroup, x ≠ 1 → ∃ g ∈ S, g * g₂ * g⁻¹ = x :=
  fun x hx hx1 => one_class (QE_le hx) (by rw [← pow_two]; exact sq_E x hx) hx1

end L34

open L34

theorem cfL34CoverRank : CFL34CoverRank := by
  intro Y _ _ hperf hZ hL l hl
  obtain ⟨ψ⟩ := nonempty_equiv_psl34_of_lieModel hL
  let π : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = center Y := QuotientGroup.ker_mk' _
  have hZc : ∀ z ∈ center Y, ∀ g : Y, g * z = z * g := fun z hz g => mem_center_iff.1 hz g
  have hZ2 : ∀ z ∈ center Y, z ^ 2 = 1 := fun z hz => sq_eq_one_of_card_two _ hZ z hz
  have hl1 : π l * π l = 1 := by
    rw [← map_mul, ← pow_two]
    exact (QuotientGroup.eq_one_iff _).2 hl
  obtain ⟨e, he⟩ : ∃ e : Y ⧸ center Y ≃* S,
      ((e (π l) : S) : P42) ∈ QE.originalSubgroup := by
    by_cases h1 : π l = 1
    · exact ⟨ψ, by rw [h1, map_one]; exact one_mem _⟩
    · have hx2 : ((ψ (π l) : S) : P42) * ((ψ (π l) : S) : P42) = 1 := by
        rw [← coe_mul, ← map_mul, hl1, map_one, coe_one]
      have hx1 : ((ψ (π l) : S) : P42) ≠ 1 := by
        intro h
        apply h1
        apply ψ.injective
        rw [map_one]
        exact Subtype.ext h
      obtain ⟨g, hgS, hg⟩ := one_class (ψ (π l)).2 hx2 hx1
      refine ⟨ψ.trans (MulAut.conj (⟨g, hgS⟩ : S)⁻¹), ?_⟩
      have h2 : (((ψ.trans (MulAut.conj (⟨g, hgS⟩ : S)⁻¹)) (π l) : S) : P42) = g₂ := by
        rw [MulEquiv.trans_apply, MulAut.conj_apply]
        simp only [coe_mul, coe_inv, inv_inv]
        rw [← hg]
        group
      rw [h2]
      exact g₂_mem_E
  obtain ⟨i1, i2, i3, i12, i13, i23, i123⟩ := indepCheck_sound indep_ok
  have key := preimage_elementary_model π hπ (center Y) hker hZc hZ2 S e QE.originalSubgroup
    QE_le sq_E g₂ conj_E g₂ g₃ c₁ g₂_mem_E g₃_mem_E c₁_mem_E i1 i2 i3 i12 i13 i23 i123
  have hlmem : l ∈ ((QE.originalSubgroup.subgroupOf S).comap e.toMonoidHom).comap π := he
  refine ⟨((QE.originalSubgroup.subgroupOf S).comap e.toMonoidHom).comap π, ?_, ?_, ?_⟩
  · intro a ha
    rw [mem_centralizer_singleton_iff]
    exact (key a ha).2 l hlmem
  · intro a ha
    exact (key a ha).1
  · rw [card_comap_of_surjective π hπ, hker, hZ, comap_equiv_eq_map_symm',
      card_map_of_injective e.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe QE_le).toEquiv, card_E]

end CFSG.ComponentClassification.CatFactsSmall
