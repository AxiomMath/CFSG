module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Clauses2

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.clause1 :
    S.relIndex T = 2 ∧ T ≤ Subgroup.normalizer (S : Set G) ∧
      T ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  ⟨dat.index_two, le_normalizer_of_relIndex_two h.S_le_T dat.index_two,
    fun _ hx => dat.x_normalizer_R h hx⟩

theorem Lin2Data.clause2 : pCoreOf 2 L = blockU L ∧ blockU L = pCoreOf 2 H :=
  ⟨dat.pCore_eq, (dat.Q_eq_U h).symm⟩

theorem Lin2Data.centralizer_U_le_U {z : G} (hz : z ∈ thompsonJ S)
    (hc : ∀ u ∈ blockU L, z * u = u * z) : z ∈ blockU L := by
  have : z ∈ thompsonJ S ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨hz, Subgroup.mem_centralizer_iff.2 fun u hu => (hc u hu).symm⟩
  rw [← dat.Q_cent, dat.Q_eq_U h] at this
  exact this

theorem Lin2Data.U_inf_conjU_eq_center {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    blockU L ⊓ conjR (blockU L) x = centerOf (thompsonJ S) := by
  have hEU := (isElemAbelian_conjR_iff (blockU L) x).2 (dat.U_elem h)
  have hUR := dat.U_le_R h
  have hUxR := dat.conjU_le_R h hx
  have hsup := dat.R_eq_U_sup h hx hxS
  apply le_antisymm
  · rintro z ⟨hzU, hzU'⟩
    refine ⟨hUR hzU, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    rw [hsup, sup_comm] at hr
    obtain ⟨u', hu', u, hu, rfl⟩ := (mem_sup_iff_of_le_normalizer
      (dat.U_le_normalizer_conjU h hx)).1 hr
    have h1 : z * u = u * z := IsElemAbelian.comm (dat.U_elem h) hzU hu
    have h2 : z * u' = u' * z := IsElemAbelian.comm hEU hzU' hu'
    calc u' * u * z = u' * (u * z) := by group
      _ = u' * (z * u) := by rw [h1]
      _ = (u' * z) * u := by group
      _ = (z * u') * u := by rw [h2]
      _ = z * (u' * u) := by group
  · rintro z ⟨hzR, hzc⟩
    have hc := Subgroup.mem_centralizer_iff.1 hzc
    have hzU : z ∈ blockU L :=
      dat.centralizer_U_le_U h hzR fun u hu => (hc u (hUR hu)).symm
    refine ⟨hzU, mem_conjR.2 ?_⟩
    have hxR := dat.x_normalizer_R h hx
    have hxz : x * z * x⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 hxR z).1 hzR
    refine dat.centralizer_U_le_U h hxz fun u hu => ?_
    have hu' : x⁻¹ * u * x ∈ conjR (blockU L) x := by
      rw [mem_conjR]
      have : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
      rw [this]
      exact hu
    have := hc _ (hUxR hu')
    calc x * z * x⁻¹ * u = x * (z * (x⁻¹ * u * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * u * x) * z) * x⁻¹ := by rw [← hc _ (hUxR hu')]
      _ = u * (x * z * x⁻¹) := by group

theorem Lin2Data.isMaxElemAbelian_S_iff {x : G} (hx : x ∈ T) (hxS : x ∉ S) (A : Subgroup G) :
    IsMaxElemAbelian S A ↔ A = blockU L ∨ A = conjR (blockU L) x := by
  rw [dat.A_eq x hx hxS A, dat.Q_eq_U h]

theorem Lin2Data.isMaxElemAbelian_T_iff {x : G} (hx : x ∈ T) (hxS : x ∉ S) (A : Subgroup G) :
    IsMaxElemAbelian T A ↔ A = blockU L ∨ A = conjR (blockU L) x := by
  have hJ : thompsonJ T = thompsonJ S := dat.jT.symm
  have hAS : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → IsMaxElemAbelian S A' := by
    intro A' hA'
    have hA'J : A' ≤ thompsonJ T := le_iSup₂ (f := fun (A'' : Subgroup G) (_ : IsMaxElemAbelian T A'') => A'')
      A' hA'
    have hA'S : A' ≤ S := hA'J.trans (hJ ▸ thompsonJ_le_self S)
    exact ⟨hA'S, hA'.2.1, fun B hB hBe => hA'.2.2 B (hB.trans h.S_le_T) hBe⟩
  constructor
  · intro hA
    exact (dat.isMaxElemAbelian_S_iff h hx hxS A).1 (hAS A hA)
  · intro hA
    have hAS' : IsMaxElemAbelian S A := (dat.isMaxElemAbelian_S_iff h hx hxS A).2 hA
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀S := hAS A₀ hA₀
    refine ⟨hAS'.1.trans h.S_le_T, hAS'.2.1, fun B hB hBe => ?_⟩
    exact (hA₀.2.2 B hB hBe).trans (hAS'.2.2 A₀ hA₀S.1 hA₀.2.1)

theorem Lin2Data.clause3 :
    thompsonJ S = baum S ∧ IsSylowTwoOf (thompsonJ S) L ∧ ∀ x ∈ T, x ∉ S →
      thompsonJ S = blockU L ⊔ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x = centerOf (thompsonJ S) ∧
      (∀ A : Subgroup G, IsMaxElemAbelian S A ↔ A = blockU L ∨ A = conjR (blockU L) x) ∧
      (∀ A : Subgroup G, IsMaxElemAbelian T A ↔ A = blockU L ∨ A = conjR (blockU L) x) := by
  refine ⟨dat.baum_eq.symm, ?_, fun x hx hxS => ⟨dat.R_eq_U_sup h hx hxS,
    dat.U_inf_conjU_eq_center h hx hxS, dat.isMaxElemAbelian_S_iff h hx hxS,
    dat.isMaxElemAbelian_T_iff h hx hxS⟩⟩
  rw [dat.R_eq_P h]
  exact isSylowTwoOf_S_inf_L h.cs

end Clauses2

end CFSG.QuasithinUnique.Lin2
