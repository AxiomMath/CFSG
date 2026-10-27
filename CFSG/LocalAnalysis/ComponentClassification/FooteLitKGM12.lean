module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGA5
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.Sporadic.Schreier

theorem card_centralizer_dvd_of_M12
    {G : Type} [Group G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .M12) (t : G) (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set G)) ∣ 960 := by
  have hG' : Nonempty (G ≃* ↥Blueprint.NativeSporadic.M12) := hG
  obtain ⟨e⟩ := hG'
  set u : Equiv.Perm (Fin 12) := (e t : Equiv.Perm (Fin 12)) with hudef
  have huM : u ∈ Blueprint.NativeSporadic.M12 := (e t).2
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  have hc : Nat.card ↥(centralizer ({t} : Set G)) =
      Nat.card ↥(Blueprint.NativeSporadic.M12 ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 12)))) := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_centralizer_equiv e t,
      ← Subgroup.card_map_of_injective (f := Blueprint.NativeSporadic.M12.subtype)
        Blueprint.NativeSporadic.M12.subtype_injective,
      map_centralizer_subtype]
    rfl
  obtain ⟨hrecs, -, hcover⟩ := OddStandard.m12_innerRecordsValid
  obtain ⟨r, hr, c, hcM, huc⟩ := hcover u huM hu2
  have hcard := (hrecs r hr).2.2.2.1
  rw [hc, huc, ← map_conj_inf_centralizer_of_mem _ hcM,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  change Nat.card ↥(centralizerIn _ r.representative) ∣ 960
  rw [hcard]
  simp only [OddStandard.m12Records, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨5, rfl⟩
  · exact ⟨4, rfl⟩

theorem pRank_le_three_of_M12
    {G : Type} [Group G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .M12) : CFSG.pRank 2 G ≤ 3 := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have h8 := GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three hG A
    (GH74.GLS.C3.Layer1.P14.elemAb2_of_isElementaryAbelian hA)
  rw [hcard] at h8
  by_contra h
  have : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem footeKnownSmall_M12
    (G : Type) [Group G] [Finite G] (hG : Blueprint.NativeSporadic.IsSporadic G .M12) :
    FooteKnownSmall G :=
  footeKnownSmall_of_alt5 (c := 960)
    (fun t ht => by
      have h := OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_of_isSporadic
        .M12 (Or.inr (Or.inl rfl)) hG t ht
      rwa [(CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm] at h)
    (card_centralizer_dvd_of_M12 hG)
    (eq_of_isSmallOrder_dvd (q₁ := 16) (by norm_num) (by norm_num) (by decide) (by norm_num)
      (by norm_num))
    (pRank_le_three_of_M12 hG)

end CFSG.ComponentClassification.FooteLit.KG
