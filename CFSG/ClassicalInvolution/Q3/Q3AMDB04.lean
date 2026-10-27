module

public import CFSG.ClassicalInvolution.Q3.Q3CHS2Tri
public import CFSG.ClassicalInvolution.Q3.Q3AMDB01
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Elementary

variable {G : Type} [Group G]

theorem isMulCommutative_closure_pair {a b : G} (h : a * b = b * a) :
    IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
  Subgroup.isMulCommutative_closure (by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [Commute.refl _, h, h.symm, Commute.refl _])

end Elementary

section Closed


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.conj_mem_of_le_sylow [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') (hD : PspNbhdDouble Ω K z)
    (hres : PspNoA2At Ω K z) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPz : P ≤ Subgroup.centralizer ({z} : Set G)) (htP : t ∈ P) (hztP : z * t ∈ P) {h : G}
    (hh : h * z * h⁻¹ ∈ P) : h * z * h⁻¹ = z ∨ h * z * h⁻¹ = t ∨ h * z * h⁻¹ = z * t := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  by_cases hbz : h * z * h⁻¹ = z
  · exact Or.inl hbz
  have hM : conjSub h K ∈ Ω := hΩ.conjInvariant h K hstd.stand.mem
  have hMu : IsUniqueInvolution (conjSub h K) (h * z * h⁻¹) := hstd.hz.conj h
  have hcomm : (h * z * h⁻¹) * z = z * (h * z * h⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPz hh)
  have hMn : conjSub h K ∈ omegaNbr Ω K := hres _ hM _ hMu hbz hcomm
  rcases hset.nbr_involution_eq hD hMn hMu hP2 htP hztP hh with e | e
  exacts [Or.inr (Or.inl e), Or.inr (Or.inr e)]

theorem PspSetting.stronglyClosed_of_le_sylow [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') (hD : PspNbhdDouble Ω K z)
    (hres : PspNoA2At Ω K z) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPz : P ≤ Subgroup.centralizer ({z} : Set G)) (htP : t ∈ P) (hztP : z * t ∈ P) :
    ∀ a ∈ Subgroup.closure ({z, t} : Set G), ∀ g : G, g⁻¹ * a * g ∈ P →
      g⁻¹ * a * g ∈ Subgroup.closure ({z, t} : Set G) := by
  have hstd := hset.bad.std
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hzt := hset.mul_comm_zt
  have hzE : z ∈ Subgroup.closure ({z, t} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert z _)
  have htE : t ∈ Subgroup.closure ({z, t} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  have hconj : ∀ h : G, h * z * h⁻¹ ∈ P → h * z * h⁻¹ ∈ Subgroup.closure ({z, t} : Set G) := by
    intro h hh
    rcases hset.conj_mem_of_le_sylow hD hres hP2 hPz htP hztP hh with e | e | e <;> rw [e]
    · exact hzE
    · exact htE
    · exact Subgroup.mul_mem _ hzE htE
  have hconj' : ∀ {M : Subgroup G} {m : G}, M ∈ Ω → IsUniqueInvolution M m → ∀ g : G,
      g⁻¹ * m * g ∈ P → g⁻¹ * m * g ∈ Subgroup.closure ({z, t} : Set G) := by
    intro M m hM hm g hg
    obtain ⟨c, rfl⟩ := hset.exists_conj_of_uniq hM hm
    have e : g⁻¹ * (c * z * c⁻¹) * g = (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ := by group
    rw [e] at hg ⊢
    exact hconj _ hg
  intro a ha g hg
  rcases Q3CH.mem_closure_pair hz2 ht2 hzt ha with rfl | rfl | rfl | rfl
  · rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · exact hconj' hstd.stand.mem hstd.hz g hg
  · exact hconj' hstd.hJ.1 hstd.ht g hg
  · exact hconj' hset.nbrK.1 hset.uniq_mul g hg

end Closed

end CFSG.ClassicalInvolution.Q3.Q3AM
