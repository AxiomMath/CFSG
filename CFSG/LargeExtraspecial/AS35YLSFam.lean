module

public import CFSG.LargeExtraspecial.S12InspFamJ2
public import CFSG.LargeExtraspecial.S12InspFamSmall
public import CFSG.LargeExtraspecial.DWInsMain
public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.J2Cover (P nativeEquivP)

namespace AS35YL

theorem false_of_J2_YL
    {X : Type} [Group X] (h : NativeSporadic.IsSporadic X .J2) {E : Set X} {d₀ : X}
    (hd₀ : d₀ ∈ E) (hd1 : d₀ ≠ 1) (hdd : d₀ * d₀ = 1)
    (hconj : ∀ c : X, ∀ x ∈ E, c * x * c⁻¹ ∈ E)
    (hord : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ≤ 4) : False := by
  obtain ⟨e⟩ := h
  have e' : X ≃* NativeSporadic.J2 := e
  set ψ : X ≃* P := e'.trans nativeEquivP with hψ
  have hd2 : orderOf ((ψ d₀ : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hdd) hd1
  obtain ⟨w, hw, h5⟩ := S12InspJ2.exists_conj_orderOf_five (ψ d₀).2 hd2
  set k : X := ψ.symm ⟨w, hw⟩ with hk
  have h4 := hord d₀ hd₀ _ (hconj k d₀ hd₀)
  have h5' : orderOf (d₀ * (k * d₀ * k⁻¹)) = 5 := by
    rw [← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe]
    simpa [hk] using h5
  omega

theorem false_of_alt6_YL {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 6)) {E : Set X}
    {d₀ : X} (hd₀ : d₀ ∈ E) (hd1 : d₀ ≠ 1) (hdd : d₀ * d₀ = 1)
    (hconj : ∀ c : X, ∀ x ∈ E, c * x * c⁻¹ ∈ E)
    (hord : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ≤ 4) : False := by
  set a : Equiv.Perm (Fin 6) := (φ d₀ : Equiv.Perm (Fin 6)) with ha
  have ha1 : a ≠ 1 := fun h => hd1 (φ.injective (Subtype.ext (by rw [← ha, h, map_one]; rfl)))
  have haa : a * a = 1 := by
    rw [ha, ← Subgroup.coe_mul, ← map_mul, hdd, map_one]
    rfl
  obtain ⟨c, hcs, h5, h51⟩ := S12Insp5.alt6_exists_conj_orderOf_five a
    (Equiv.Perm.mem_alternatingGroup.mp (φ d₀).2) haa ha1
  set c' : X := φ.symm ⟨c, Equiv.Perm.mem_alternatingGroup.mpr hcs⟩ with hc'
  have h4 := hord d₀ hd₀ _ (hconj c' d₀ hd₀)
  have h5' : orderOf (d₀ * (c' * d₀ * c'⁻¹)) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← MulEquiv.orderOf_eq φ, ← Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ ?_
    · simpa [hc', ha] using h5
    · simpa [hc', ha] using h51
  omega

end AS35YL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_mem_EhatAsc_YL (hst : S.Asc512Standing)
    [h : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc)] :
    ∃ d ∈ S.EhatAsc, d ≠ 1 ∧ d * d = 1 := by
  obtain ⟨t₀, ht₀⟩ := @AS35YL.nonempty_of_nontrivial_YL _ _ S.DbarAsc h
  have hT : t₀ ∈ S.LbarAsc := subset_closure ht₀
  exact ⟨_, mk_mem_EhatAsc_YL (d := ⟨t₀, hT⟩) ht₀, AS35YL.mk_ne_one_YL hst.conj (d := ⟨t₀, hT⟩) ht₀,
    AS35YL.mul_self_of_mem_image_YL (D := S.DbarAsc) (fun _ hd => mul_self_of_mem_DbarAsc_YL hd)
      ⟨⟨t₀, hT⟩, ht₀, rfl⟩⟩

end Setting

namespace S14

theorem asc512InspField_of (hF : DW.DW2FieldInput) : Asc512InspFor Asc512FieldFam := by
  intro G _ _ S hS hst h
  obtain ⟨hnd, τ, n, f, hf, hτ, hX⟩ := h
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  exact (hF _ τ n f hf hτ hX _ (Setting.isTransClass34_EhatAsc_YL hS hst)).elim

theorem asc512InspJ2 :
    Asc512InspFor Asc512J2Fam := by
  intro G _ _ S hS hst h
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := by
    obtain ⟨e⟩ := h
    have e' : S.LbarAsc ⧸ center S.LbarAsc ≃* NativeSporadic.J2 := e
    have : Nontrivial NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.2.1
    exact e'.toEquiv.nontrivial
  obtain ⟨d₀, hd₀, hd1, hdd⟩ := Setting.exists_mem_EhatAsc_YL hst
  exact (AS35YL.false_of_J2_YL h hd₀ hd1 hdd (fun _ _ hx => Setting.conj_mem_EhatAsc_YL hx)
    (fun _ hx _ hy => Setting.orderOf_mul_EhatAsc_le_YL hS hx hy)).elim

theorem asc512InspAlt6 : Asc512InspFor Asc512Alt6Fam := by
  intro G _ _ S hS hst h
  obtain ⟨φ⟩ := h
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact φ.toEquiv.nontrivial
  obtain ⟨d₀, hd₀, hd1, hdd⟩ := Setting.exists_mem_EhatAsc_YL hst
  exact (AS35YL.false_of_alt6_YL φ hd₀ hd1 hdd (fun _ _ hx => Setting.conj_mem_EhatAsc_YL hx)
    (fun _ hx _ hy => Setting.orderOf_mul_EhatAsc_le_YL hS hx hy)).elim

theorem asc512InspNondeg_of_families (hF : Asc512InspFor Asc512FieldFam)
    (hL : Asc512InspFor Asc512PSLFam) (hSp : Asc512InspFor Asc512PSpFam)
    (hO : Asc512InspFor Asc512POmegaFam) (hE : Asc512InspFor Asc512ExcFam)
    (hU : Asc512InspFor Asc512U33Fam) (hA : Asc512InspFor Asc512Alt6Fam)
    (hJ : Asc512InspFor Asc512J2Fam) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) =>
      InspNondeg X D ∧ CFSG.Timmesfeld.Outcome X := by
  intro G _ _ S hS hst h
  obtain ⟨hnd, hout⟩ := h
  rcases hout with ⟨m, f, hm, hf, h⟩ | ⟨m, f, hm, hf, h⟩ | ⟨m, f, hm, hf, h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, τ, hτ, h⟩ | h | h | h
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact hL G S hS hst ⟨hnd, m, hm, h⟩
    · exact hF G S hS hst ⟨hnd, .PSL, m, f, hf2, Or.inl ⟨rfl, hm⟩, h⟩
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact hSp G S hS hst ⟨hnd, m, hm, h⟩
    · exact hF G S hS hst ⟨hnd, .PSp, m, f, hf2, Or.inr (Or.inl ⟨rfl, hm⟩), h⟩
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact hO G S hS hst ⟨hnd, m, hm, h⟩
    · rcases h with h | h
      · exact hF G S hS hst ⟨hnd, .POmegaPlus, m, f, hf2,
          Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hm⟩)), h⟩
      · exact hF G S hS hst ⟨hnd, .POmegaMinus, m, f, hf2,
          Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hm⟩)), h⟩
  · exact hF G S hS hst ⟨hnd, .G2, 0, f, hf, Or.inr (Or.inr (Or.inr ⟨rfl, by decide⟩)), h⟩
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact hE G S hS hst ⟨hnd, τ, hτ, h⟩
    · refine hF G S hS hst ⟨hnd, τ, 0, f, hf2, Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)), h⟩
      revert hτ
      cases τ <;> decide
  · exact hU G S hS hst ⟨hnd, h⟩
  · exact hA G S hS hst h
  · exact hJ G S hS hst h

end S14

end CFSG.LargeExtraspecial
