module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.GH74.GLS.Stage2.Local.P27
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

variable {G : Type} [Group G] [Finite G]

noncomputable def JbarConjEquiv (x g : G) :
    (↥(Jx (g * x * g⁻¹)) ⧸ pPrimeCore 2 ↥(Jx (g * x * g⁻¹))) ≃* (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) :=
  let e₀ : ↥(Jx (g * x * g⁻¹)) ≃* ↥(Jx x) :=
    (MulEquiv.subgroupCongr (Jx_conj x g)).trans ((MulAut.conj g).subgroupMap (Jx x)).symm
  QuotientGroup.congr (pPrimeCore 2 ↥(Jx (g * x * g⁻¹))) (pPrimeCore 2 ↥(Jx x)) e₀
    (pPrimeCore_map_iso 2 e₀)

theorem fullCL4_conj {x : G} {q : ℕ} (g : G) (h : FullCL4 x q) : FullCL4 (g * x * g⁻¹) q := by
  rcases h with ⟨F, i1, i2, hF, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · exact Or.inl ⟨F, i1, i2, hF, ⟨(JbarConjEquiv x g).trans e⟩⟩
  · exact Or.inr ⟨hq, ⟨(JbarConjEquiv x g).trans e⟩⟩

omit [Finite G] in
theorem hasNormal2Compl_cmap {Y : Subgroup G} (g : G) (h : HasNormal2Compl Y) :
    HasNormal2Compl (cmap g Y) := by
  obtain ⟨N, hNY, hNn, hNodd, a, ha⟩ := h
  refine ⟨cmap g N, Subgroup.map_mono hNY, ?_, ?_, a, ?_⟩
  · refine ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (g⁻¹ * (n : G) * g) ∈ N := mem_cmap.1 hn
    have hy' : (g⁻¹ * (y : G) * g) ∈ Y := mem_cmap.1 y.2
    have := hNn.conj_mem (⟨g⁻¹ * (n : G) * g, hNY hn'⟩ : ↥Y) (Subgroup.mem_subgroupOf.2 hn') ⟨_, hy'⟩
    have h2 := Subgroup.mem_subgroupOf.1 this
    rw [mem_cmap]
    have e : g⁻¹ * ((y : G) * (n : G) * (y : G)⁻¹) * g =
        (g⁻¹ * (y : G) * g) * (g⁻¹ * (n : G) * g) * (g⁻¹ * (y : G) * g)⁻¹ := by group
    rw [show ((y * n * y⁻¹ : ↥(cmap g Y)) : G) = (y : G) * (n : G) * (y : G)⁻¹ from rfl, e]
    exact h2
  · have h1 : Nat.card ↥(cmap g N) = Nat.card ↥N :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [h1]
    exact hNodd
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) N Y
      (MulAut.conj g).injective
    exact this.trans ha

theorem cmap_CxK_le (x g : G) :
    cmap g (CxK x (Jx x)) ≤ CxK (g * x * g⁻¹) (Jx (g * x * g⁻¹)) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hy1 ⊢
    have := hy1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · have h3 := cmap_mem_centralizerSection hy2 g
    rw [← pPrimeCoreOf_cmap, ← Jx_conj] at h3
    simpa [MulAut.conj_apply] using h3

theorem hasNormal2Compl_CxK_conj {x : G} (g : G) (h : HasNormal2Compl (CxK x (Jx x))) :
    HasNormal2Compl (CxK (g * x * g⁻¹) (Jx (g * x * g⁻¹))) := by
  have h1 := cmap_CxK_le x g
  have h2 := cmap_CxK_le (g * x * g⁻¹) g⁻¹
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e] at h2
  have h3 : CxK (g * x * g⁻¹) (Jx (g * x * g⁻¹)) = cmap g (CxK x (Jx x)) := by
    apply le_antisymm
    · intro y hy
      have := h2 (show g⁻¹ * y * g⁻¹⁻¹ ∈ cmap g⁻¹ (CxK (g * x * g⁻¹) (Jx (g * x * g⁻¹))) from ⟨y, hy, rfl⟩)
      rw [mem_cmap]
      simpa using this
    · exact h1
  rw [h3]
  exact hasNormal2Compl_cmap g h

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
