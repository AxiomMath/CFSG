module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64F
public import CFSG.ClassicalInvolution.Asc77.AscL62Cyc

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  unfold conjSub at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

omit [Finite G] in
theorem inf_centralizer_zj : K ⊓ Subgroup.centralizer ({z * j} : Set G) =
    K ⊓ Subgroup.centralizer ({j} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have hxz := c.z_comm hx
    calc x * j = z * (x * (z * j)) := by
          calc x * j = (z * z) * x * j := by rw [c.hz.sq, one_mul]
            _ = z * (z * x) * j := by group
            _ = z * (x * z) * j := by rw [hxz]
            _ = z * (x * (z * j)) := by group
      _ = z * ((z * j) * x) := by rw [h]
      _ = (z * z) * j * x := by group
      _ = j * x := by rw [c.hz.sq, one_mul]
  · rintro ⟨hx, h⟩
    exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_mul
      (Subgroup.mem_centralizer_singleton_iff.mpr (c.z_comm hx))
      (Subgroup.mem_centralizer_singleton_iff.mpr h))⟩

theorem UV_isPGroup : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) :=
  c.U_isPGroup.to_sup_of_normal_right' c.symm.U_isPGroup (AscL62.le_normalizer_of_commutes c.hUV)

omit [Finite G] in
theorem conjSub_V_le {r : G} (hr : r ∈ R) :
    conjSub r (Subgroup.zpowers v) ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have h1 : conjSub r (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := mem_normalizer_iff_conjSub_eq.mp (c.hRN hr)
  rw [← h1]
  exact conjSub_mono le_sup_right

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
