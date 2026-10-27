module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem pump_location_in [Finite X] {Y : Subgroup X} {x : X} (hxY : x ∈ Y)
    (hx : orderOf x = 2) {T : Subgroup X} (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ M.map (MulAut.conj x).toMonoidHom) ⊓
        centralizer ({x} : Set X))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  have hTE : T' ≤ pLayer ↥Y 2 :=
    FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx' hT'C hT'pc
  obtain ⟨M₀, hM₀pc, hTM₀, hTM₀pc⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location hx' hT'C hT'pc hTE
  set M := M₀.map Y.subtype with hMdef
  have hMY : M ≤ Y := map_subtype_le _
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ Mx := by
    rw [Subgroup.map_sup, hconj]
  have hMxY : Mx ≤ Y := by
    rw [← hconj]
    exact map_subtype_le _
  refine ⟨M, hMY, by rw [hMsub]; exact hM₀pc, ?_, ?_⟩
  · rw [← hsup]
    intro y hy
    exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩
  · have hle : (M ⊔ Mx) ⊓ centralizer ({x} : Set X) ≤ Y :=
      inf_le_left.trans (sup_le hMY hMxY)
    have heq : (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) =
        ((M ⊔ Mx) ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
      rw [centralizer_mk_eq hxY, ← hsup]
      ext y
      simp only [mem_inf, mem_subgroupOf]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨⟨y, h1, rfl⟩, h2⟩
      · rintro ⟨⟨z, hz, hzy⟩, h2⟩
        have hzy' : z = y := Subtype.ext hzy
        exact ⟨hzy' ▸ hz, h2, y.2⟩
    rw [heq] at hTM₀pc
    rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2 Nat.prime_two]
    exact hTM₀pc

end CFSG.ComponentClassification.SolMax
