module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Defs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {A : Subgroup X}

private lemma mem_map_conj_inv {A : Subgroup X} {g₀ x : X} :
    x ∈ A.map (MulAut.conj g₀⁻¹).toMonoidHom ↔ g₀ * x * g₀⁻¹ ∈ A := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change g₀ * (MulAut.conj g₀⁻¹) a * g₀⁻¹ ∈ A
    have h : g₀ * (MulAut.conj g₀⁻¹) a * g₀⁻¹ = a := by
      rw [MulAut.conj_apply, inv_inv]
      group
    rwa [h]
  · rintro hx
    refine ⟨g₀ * x * g₀⁻¹, hx, ?_⟩
    change (MulAut.conj g₀⁻¹) (g₀ * x * g₀⁻¹) = x
    rw [MulAut.conj_apply, inv_inv]
    group

private lemma conj_eq_self_of_mem_map_conj_inv {A : Subgroup X} (hA : IsElemAbelian 2 A)
    {g₀ a' b : X} (ha' : a' ∈ A.map (MulAut.conj g₀⁻¹).toMonoidHom)
    (hbA : g₀ * b * g₀⁻¹ ∈ A) : a' * b * a'⁻¹ = b := by
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp ha'
  have hcomm : c * (g₀ * b * g₀⁻¹) = (g₀ * b * g₀⁻¹) * c :=
    hA.comm hc hbA
  have hca' : a' = g₀⁻¹ * c * g₀ := by
    rw [← hca]
    change (MulAut.conj g₀⁻¹) c = g₀⁻¹ * c * g₀
    rw [MulAut.conj_apply, inv_inv]
  rw [hca']
  have hstep : (g₀⁻¹ * c * g₀) * b * (g₀⁻¹ * c * g₀)⁻¹ =
      g₀⁻¹ * (c * (g₀ * b * g₀⁻¹) * c⁻¹) * g₀ := by group
  rw [hstep, hcomm]
  group

private lemma sylow_conj_mem {N : Subgroup X} {P Q : Sylow 2 ↥N} {n : ↥N}
    (hn : n • Q = P) {A' : Subgroup X} (hA'N : A' ≤ N) (hAQ : A'.subgroupOf N ≤ Q)
    {a' : X} (ha' : a' ∈ A') :
    (n : X) * a' * (n : X)⁻¹ ∈ (P : Subgroup ↥N).map N.subtype := by
  have haN : (⟨a', hA'N ha'⟩ : ↥N) ∈ Q := hAQ ha'
  have hPQ : MulAut.conj n • (Q : Subgroup ↥N) = (P : Subgroup ↥N) := by
    rw [← Sylow.coe_subgroup_smul, hn]
  have hmem : (MulAut.conj n) (⟨a', hA'N ha'⟩ : ↥N) ∈ (P : Subgroup ↥N) := by
    have h4 := Subgroup.smul_mem_pointwise_smul (⟨a', hA'N ha'⟩ : ↥N)
      (MulAut.conj n) (Q : Subgroup ↥N) haN
    rwa [hPQ] at h4
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj n) (⟨a', hA'N ha'⟩ : ↥N), hmem, ?_⟩
  simp [MulAut.conj_apply]

theorem GoldHyp.normal_of_mem (h : GoldHyp T A) {x a : X} (hx : x ∈ (T : Subgroup X))
    (ha : a ∈ A) : x * a * x⁻¹ ∈ A := by
  exact h.weak x (fun a ha => T.mul_mem (T.mul_mem hx (h.le ha)) (T.inv_mem hx)) a ha

theorem goldschmidt_9_3_two (h : GoldHyp T A) {B : Subgroup X}
    (hBA : ∃ g : X, ∀ b ∈ B, g * b * g⁻¹ ∈ A) :
    ∃ g : X, (∀ b ∈ B, g * b * g⁻¹ ∈ A) ∧
      ∀ n ∈ (T : Subgroup X) ⊓ normalizer (B : Set X), g * n * g⁻¹ ∈ (T : Subgroup X) := by
  classical
  obtain ⟨g₀, hg₀⟩ := hBA
  let N : Subgroup X := normalizer (B : Set X)
  let NTB : Subgroup X := (T : Subgroup X) ⊓ N
  let A' : Subgroup X := A.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hApg : IsPGroup 2 A := fun x => ⟨1, by
    apply Subtype.ext
    simpa using h.elemAb.2 x.1 x.2⟩
  have hA'pg : IsPGroup 2 A' := hApg.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hNTBpg : IsPGroup 2 NTB :=
    T.isPGroup'.to_le (show NTB ≤ (T : Subgroup X) from inf_le_left)
  have hA'N : A' ≤ N := by
    intro a' ha'
    rw [mem_set_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [conj_eq_self_of_mem_map_conj_inv h.elemAb
        (show a' ∈ A.map (MulAut.conj g₀⁻¹).toMonoidHom from ha') (hg₀ b hb)]
      exact hb
    · intro hb
      have hb' : a' * b * a'⁻¹ ∈ B := hb
      have h1 : a'⁻¹ * (a' * b * a'⁻¹) * a' = a' * b * a'⁻¹ := by
        simpa using conj_eq_self_of_mem_map_conj_inv h.elemAb
          (show a'⁻¹ ∈ A.map (MulAut.conj g₀⁻¹).toMonoidHom from A'.inv_mem ha')
          (hg₀ _ hb')
      have h2 : a'⁻¹ * (a' * b * a'⁻¹) * a' = b := by group
      rw [h2] at h1
      rw [h1]
      exact hb
  haveI : Finite (Sylow 2 X) := T.finite_of_finiteIndex
  obtain ⟨T1', hT1'⟩ := (hNTBpg.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨T2', hT2'⟩ := (hA'pg.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥N) T2' T1'
  let T1 : Subgroup X := (T1' : Subgroup ↥N).map N.subtype
  have hT1pg : IsPGroup 2 T1 := T1'.isPGroup'.map N.subtype
  have hNTB_le_T1 : NTB ≤ T1 := by
    calc NTB = (NTB.subgroupOf N).map N.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
      _ ≤ (T1' : Subgroup ↥N).map N.subtype := Subgroup.map_mono hT1'
  obtain ⟨T', hT1leT'⟩ := hT1pg.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (X) T' T
  have hconjT1 : ∀ y ∈ T1, u * y * u⁻¹ ∈ (T : Subgroup X) := by
    intro y hy
    have hmem : MulAut.conj u • y ∈ MulAut.conj u • T1 :=
      Subgroup.smul_mem_pointwise_smul y (MulAut.conj u) T1 hy
    have hle : MulAut.conj u • T1 ≤ MulAut.conj u • (T' : Subgroup X) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hT1leT'
    have hT'eq : MulAut.conj u • (T' : Subgroup X) = (T : Subgroup X) := by
      rw [← Sylow.coe_subgroup_smul, hu]
    have hh := hle hmem
    rw [hT'eq] at hh
    simpa only [MulAut.smul_def, MulAut.conj_apply] using hh
  let g : X := u * (n : X) * g₀⁻¹
  have hA'conj : ∀ a' ∈ A', (n : X) * a' * (n : X)⁻¹ ∈ T1 := by
    intro a' ha'
    exact sylow_conj_mem hn hA'N hT2' ha'
  have hpres : ∀ a ∈ A, g * a * g⁻¹ ∈ (T : Subgroup X) := by
    intro a ha
    have ha' : g₀⁻¹ * a * g₀ ∈ A' := by
      rw [mem_map_conj_inv]
      have hh : g₀ * (g₀⁻¹ * a * g₀) * g₀⁻¹ = a := by group
      rwa [hh]
    have h1 : (n : X) * (g₀⁻¹ * a * g₀) * (n : X)⁻¹ ∈ T1 := hA'conj _ ha'
    have h2 : u * ((n : X) * (g₀⁻¹ * a * g₀) * (n : X)⁻¹) * u⁻¹ ∈ (T : Subgroup X) :=
      hconjT1 _ h1
    convert h2 using 1
    dsimp only [g]
    group
  have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := h.weak g hpres
  have hBconj : ∀ b ∈ B, u * b * u⁻¹ ∈ A := by
    intro b hb
    have hnN : (n : X) ∈ N := n.2
    have hx : (n : X)⁻¹ * b * (n : X) ∈ B :=
      ((mem_set_normalizer_iff''.mp hnN) b).mp hb
    have hxA : g₀ * ((n : X)⁻¹ * b * (n : X)) * g₀⁻¹ ∈ A := hg₀ _ hx
    have hgxA : g * (g₀ * ((n : X)⁻¹ * b * (n : X)) * g₀⁻¹) * g⁻¹ ∈ A := hgA _ hxA
    convert hgxA using 1
    dsimp only [g]
    group
  refine ⟨u, hBconj, ?_⟩
  intro m hm
  exact hconjT1 m (hNTB_le_T1 hm)

end CFSG.EvenSporadicStandard.HNRecog.Harada
