module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplStep2D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplGlue

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma s8_map_centralizer_of_map_eq {Q : Type} [Group Q] (e : Q ≃* Q)
    {A B : Subgroup Q} (h : A.map e.toMonoidHom = B) :
    (Subgroup.centralizer (A : Set Q)).map e.toMonoidHom
      = Subgroup.centralizer (B : Set Q) := by
  rw [← h]
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy b hb
    rcases Subgroup.mem_map.mp hb with ⟨a, ha, rfl⟩
    have hcomm : a * e.symm y = e.symm y * a := hy a ha
    calc e a * y = e a * e (e.symm y) := by rw [MulEquiv.apply_symm_apply]
      _ = e (a * e.symm y) := by rw [map_mul]
      _ = e (e.symm y * a) := by rw [hcomm]
      _ = e (e.symm y) * e a := by rw [map_mul]
      _ = y * e a := by rw [MulEquiv.apply_symm_apply]
  · intro hy a ha
    apply e.injective
    show e (a * e.symm y) = e (e.symm y * a)
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)

private lemma s8_map_H_of_map_eq {Q : Type} [Group Q] (e : Q ≃* Q)
    {A B : Subgroup Q} (h : A.map e.toMonoidHom = B) :
    (s8H A).map e.toMonoidHom = s8H B := by
  unfold s8H
  rw [Subgroup.map_commutator, s8_map_centralizer_of_map_eq e h]

theorem s8_glue_data {Γ : Type} [Group Γ] [Finite Γ] {G0 V1 V2 : Subgroup Γ}
    {φ1 φ2 : (Fin 5 → ZMod 2) → ↥G0} {α β : ↥G0 →* S8A5}
    (h : S8Data (V1.subgroupOf G0) (V2.subgroupOf G0) φ1 φ2 α β)
    (hV1 : V1 ≤ G0) (hV2 : V2 ≤ G0) (hG0 : G0.index = 2) {t : Γ} (ht : t ∉ G0)
    (hv : V1.map (MulAut.conj t).toMonoidHom = V2) :
    ∃ K : Subgroup Γ, K ⊓ (V1 ⊔ V2) = ⊥ ∧ K ⊔ (V1 ⊔ V2) = ⊤ := by
  haveI : G0.Normal := Subgroup.normal_of_index_eq_two hG0
  haveI : Finite ↥G0 := Subtype.finite
  let V1' : Subgroup ↥G0 := V1.subgroupOf G0
  let V2' : Subgroup ↥G0 := V2.subgroupOf G0
  let c : MulAut ↥G0 := MulAut.conjNormal t
  have hV1'map : V1'.map G0.subtype = V1 := Subgroup.map_subgroupOf_eq_of_le hV1
  have hV2'map : V2'.map G0.subtype = V2 := Subgroup.map_subgroupOf_eq_of_le hV2
  have hc : (MulAut.conj t).toMonoidHom.comp G0.subtype = G0.subtype.comp c.toMonoidHom := by
    ext x
    simp [c, MulAut.conjNormal_apply, MulAut.conj_apply]
  have htransport : ∀ A : Subgroup ↥G0,
      (A.map G0.subtype).map (MulAut.conj t).toMonoidHom
        = (A.map c.toMonoidHom).map G0.subtype := by
    intro A
    rw [Subgroup.map_map, Subgroup.map_map, hc]
  have hB1 : V1'.map c.toMonoidHom = V2' := by
    refine Subgroup.map_injective G0.subtype_injective ?_
    rw [← htransport V1', hV1'map, hv, ← hV2'map]
  let s : ↥G0 := ⟨t * t, Subgroup.mul_self_mem_of_index_two hG0 t⟩
  have hcc : ∀ x : ↥G0, c.toMonoidHom (c.toMonoidHom x) = s * x * s⁻¹ := by
    intro x
    apply Subtype.ext
    show t * (t * (x : Γ) * t⁻¹) * t⁻¹ = (t * t) * (x : Γ) * (t * t)⁻¹
    group
  have hB2 : V2'.map c.toMonoidHom = V1' := by
    apply le_antisymm
    · rintro y hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      have hz' : z ∈ V1'.map c.toMonoidHom := by rw [hB1]; exact hz
      rcases Subgroup.mem_map.mp hz' with ⟨w, hw, rfl⟩
      rw [hcc w]
      exact h.normal1.conj_mem w hw s
    · intro y hy
      have hw : s⁻¹ * y * s ∈ V1' := by
        simpa using h.normal1.conj_mem y hy s⁻¹
      have hw' : c.toMonoidHom (s⁻¹ * y * s) ∈ V2' := by
        rw [← hB1]
        exact Subgroup.mem_map_of_mem c.toMonoidHom hw
      refine Subgroup.mem_map.mpr ⟨c.toMonoidHom (s⁻¹ * y * s), hw', ?_⟩
      rw [hcc (s⁻¹ * y * s)]
      group
  have hH1c : (s8H V1').map c.toMonoidHom = s8H V2' := s8_map_H_of_map_eq c hB1
  have hH2c : (s8H V2').map c.toMonoidHom = s8H V1' := s8_map_H_of_map_eq c hB2
  obtain ⟨C, _, hC, hCs⟩ := h.H_compl
  let H1 : Subgroup Γ := (s8H V2').map G0.subtype
  let H2 : Subgroup Γ := (s8H V1').map G0.subtype
  let C1 : Subgroup Γ := C.map G0.subtype
  have h12 : H1.map (MulAut.conj t).toMonoidHom ≤ H2 := by
    apply le_of_eq
    show ((s8H V2').map G0.subtype).map (MulAut.conj t).toMonoidHom
      = (s8H V1').map G0.subtype
    rw [htransport (s8H V2'), hH2c]
  have h21 : H2.map (MulAut.conj t).toMonoidHom ≤ H1 := by
    apply le_of_eq
    show ((s8H V1').map G0.subtype).map (MulAut.conj t).toMonoidHom
      = (s8H V2').map G0.subtype
    rw [htransport (s8H V1'), hH1c]
  have hsup : H1 ⊔ H2 = G0 := by
    show (s8H V2').map G0.subtype ⊔ (s8H V1').map G0.subtype = G0
    rw [← Subgroup.map_sup, h.H_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hdisj : H1 ⊓ H2 = ⊥ := by
    show (s8H V2').map G0.subtype ⊓ (s8H V1').map G0.subtype = ⊥
    rw [← Subgroup.map_inf _ _ G0.subtype G0.subtype_injective, h.H_disj, Subgroup.map_bot]
  have hcomm : ∀ x ∈ H1, ∀ y ∈ H2, x * y = y * x := by
    intro x hx y hy
    rcases Subgroup.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
    show G0.subtype x' * G0.subtype y' = G0.subtype y' * G0.subtype x'
    rw [← map_mul, ← map_mul, h.H_comm x' hx' y' hy']
  have hV1H : V1 ≤ H1 := by
    rw [← hV1'map]
    exact Subgroup.map_mono h.V1_le_H
  have hV2H : V2 ≤ H2 := by
    rw [← hV2'map]
    exact Subgroup.map_mono h.swap.V1_le_H
  have hVc : ∀ x ∈ V1, ∀ y ∈ V2, x * y = y * x := by
    intro x hx y hy
    have hx' : (⟨x, hV1 hx⟩ : ↥G0) ∈ V1' := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have hy' : (⟨y, hV2 hy⟩ : ↥G0) ∈ V2' := by
      rw [Subgroup.mem_subgroupOf]; exact hy
    exact congrArg Subtype.val (h.comm ⟨x, hV1 hx⟩ hx' ⟨y, hV2 hy⟩ hy')
  have hC' : C1 ⊓ V1 = ⊥ := by
    change C.map G0.subtype ⊓ V1 = ⊥
    rw [← hV1'map, ← Subgroup.map_inf C V1' G0.subtype G0.subtype_injective, inf_comm, hC,
      Subgroup.map_bot]
  have hCs' : C1 ⊔ V1 = H1 := by
    change C.map G0.subtype ⊔ V1 = (s8H V2').map G0.subtype
    rw [← hV1'map, ← Subgroup.map_sup, sup_comm, hCs]
  exact s8_glue hG0 ht hsup hdisj hcomm h12 h21 hV1H hV2H hVc hv hC' hCs'

end CFSG.OddStandard.SmallF3.Omega
