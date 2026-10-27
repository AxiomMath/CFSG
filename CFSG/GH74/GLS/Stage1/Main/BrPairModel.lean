module

public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.GH74.GLS.Stage1.Main.Out

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section ModelComps

variable {Gs : Type} [Group Gs]

theorem Ez_conj_mem {z' y e : Gs} (hy : y ∈ centralizer ({z'} : Set Gs)) (he : e ∈ IVK.Ez z') :
    y * e * y⁻¹ ∈ IVK.Ez z' := by
  obtain ⟨l, hl, rfl⟩ := he
  have hc : (layer ↥(centralizer ({z'} : Set Gs))).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hn : (layer ↥(centralizer ({z'} : Set Gs))).Normal := inferInstance
  refine ⟨⟨y, hy⟩ * l * ⟨y, hy⟩⁻¹, hn.conj_mem l hl ⟨y, hy⟩, ?_⟩
  rfl

theorem quasi_of_hasSL2 {E : Subgroup Gs} {q : ℕ} (h5 : 5 ≤ q) (h : HasSL2Model ↥E (fun r => r = q)) :
    IsQuasisimple ↥E := by
  obtain ⟨F, iF, fF, hq, ⟨e⟩⟩ := h
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have hc : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hq]; omega
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hc
    exact ⟨t, ht⟩
  have e' : ↥E ≃* Matrix.SpecialLinearGroup (Fin 2) F := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  exact (isQuasisimple_congr e').2 (CFSG.RankThree.Classical.isQuasisimple_SL2 h4)


theorem model_swap_data {q : ℕ} {z' t' : Gs} {S' E₁ E₂ : Subgroup Gs} (h5 : 5 ≤ q)
    (hz'o : orderOf z' = 2) (hz'S' : ∀ s ∈ S', s * z' = z' * s) (hEz : IVK.Ez z' = E₁ ⊔ E₂)
    (hE₂ : E₂ = E₁.map (MulAut.conj t').toMonoidHom) (hsl2 : HasSL2Model ↥E₁ (fun r => r = q))
    (hinter : E₁ ⊓ E₂ = zpowers z') (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) (ht'S : t' ∈ S')
    (ht'o : orderOf t' = 2) :
    ∃ ht : t' ∈ IVK.Ez z' ⊔ S',
      IsComponent (E₁.subgroupOf (IVK.Ez z' ⊔ S')) ∧ IsComponent (E₂.subgroupOf (IVK.Ez z' ⊔ S')) ∧
      E₁.subgroupOf (IVK.Ez z' ⊔ S') ≠ E₂.subgroupOf (IVK.Ez z' ⊔ S') ∧
      (E₁.subgroupOf (IVK.Ez z' ⊔ S')).map (MulAut.conj (⟨t', ht⟩ : ↥(IVK.Ez z' ⊔ S'))).toMonoidHom =
        E₂.subgroupOf (IVK.Ez z' ⊔ S') ∧
      (E₂.subgroupOf (IVK.Ez z' ⊔ S')).map (MulAut.conj (⟨t', ht⟩ : ↥(IVK.Ez z' ⊔ S'))).toMonoidHom =
        E₁.subgroupOf (IVK.Ez z' ⊔ S') := by
  set Y : Subgroup Gs := IVK.Ez z' ⊔ S' with hY
  have hsq : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [ht'o, pow_two] at this
  have hE₁E : E₁ ≤ IVK.Ez z' := by rw [hEz]; exact le_sup_left
  have hE₂E : E₂ ≤ IVK.Ez z' := by rw [hEz]; exact le_sup_right
  have hE₁Y : E₁ ≤ Y := hE₁E.trans le_sup_left
  have hE₂Y : E₂ ≤ Y := hE₂E.trans le_sup_left
  have ht'Y : t' ∈ Y := Subgroup.mem_sup_right ht'S
  have hEC : IVK.Ez z' ≤ centralizer ({z'} : Set Gs) := Subgroup.map_subtype_le _
  have hSC : S' ≤ centralizer ({z'} : Set Gs) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hz'S' s hs)
  have hYC : Y ≤ centralizer ({z'} : Set Gs) := sup_le hEC hSC
  have hq₁ : IsQuasisimple ↥E₁ := quasi_of_hasSL2 h5 hsl2
  have hq₂ : IsQuasisimple ↥E₂ := by
    rw [hE₂]
    exact (isQuasisimple_congr (E₁.equivMapOfInjective _ (MulAut.conj t').injective)).1 hq₁
  have hq₁' : IsQuasisimple ↥(E₁.subgroupOf Y) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hE₁Y)).2 hq₁
  have hq₂' : IsQuasisimple ↥(E₂.subgroupOf Y) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hE₂Y)).2 hq₂
  have hcomm' : ∀ a ∈ E₁.subgroupOf Y, ∀ b ∈ E₂.subgroupOf Y, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hcomm a ha b hb)
  have hNY : (E₁.subgroupOf Y ⊔ E₂.subgroupOf Y).Normal := by
    rw [← Subgroup.subgroupOf_sup hE₁Y hE₂Y, ← hEz]
    constructor
    intro n hn g
    exact Ez_conj_mem (hYC g.2) hn
  have hcomm'' : ∀ b ∈ E₂.subgroupOf Y, ∀ a ∈ E₁.subgroupOf Y, b * a = a * b := fun b hb a ha =>
    (hcomm' a ha b hb).symm
  have hNY' : (E₂.subgroupOf Y ⊔ E₁.subgroupOf Y).Normal := by rw [sup_comm]; exact hNY
  have hc₁ : IsComponent (E₁.subgroupOf Y) := ⟨hq₁', isSubnormal_of_comm_normal hcomm' hNY⟩
  have hc₂ : IsComponent (E₂.subgroupOf Y) := ⟨hq₂', isSubnormal_of_comm_normal hcomm'' hNY'⟩
  refine ⟨ht'Y, hc₁, hc₂, ?_, ?_, ?_⟩
  · intro hEq
    have h1 : E₁ ⊓ Y = E₂ ⊓ Y := Subgroup.subgroupOf_inj.mp hEq
    rw [inf_eq_left.2 hE₁Y, inf_eq_left.2 hE₂Y] at h1
    rw [← h1, inf_idem] at hinter
    obtain ⟨F, iF, fF, hqF, ⟨e⟩⟩ := hsl2
    have h2 := Nat.card_congr e.toEquiv
    have hcard : Nat.card ↥E₁ = 2 := by
      rw [hinter, Nat.card_zpowers, hz'o]
    rw [hcard, CFSG.GH74.GLS.Stage1.Main.card_statedSL_two', hqF] at h2
    have h25 : 25 ≤ q ^ 2 := by nlinarith
    have h24 : 24 ≤ q ^ 2 - 1 := by omega
    have : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h24
    omega
  · ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      show t' * (n : Gs) * t'⁻¹ ∈ E₂
      rw [hE₂]
      exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
    · intro hx
      have hx' : (x : Gs) ∈ E₁.map (MulAut.conj t').toMonoidHom := by rw [← hE₂]; exact hx
      obtain ⟨e, he, hex⟩ := hx'
      refine ⟨⟨e, hE₁Y he⟩, he, ?_⟩
      apply Subtype.ext
      show t' * e * t'⁻¹ = x
      simpa [MulAut.conj_apply] using hex
  · ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨e, he, hen⟩ : (n : Gs) ∈ E₁.map (MulAut.conj t').toMonoidHom := by rw [← hE₂]; exact hn
      show t' * (n : Gs) * t'⁻¹ ∈ E₁
      have hen' : t' * e * t'⁻¹ = (n : Gs) := by simpa [MulAut.conj_apply] using hen
      rw [← hen']
      have : t' * (t' * e * t'⁻¹) * t'⁻¹ = e := by
        calc t' * (t' * e * t'⁻¹) * t'⁻¹ = (t' * t') * e * (t'⁻¹ * t'⁻¹) := by group
          _ = e := by rw [hsq, ← mul_inv_rev, hsq]; group
      rw [this]; exact he
    · intro hx
      have hxE : (x : Gs) ∈ E₁ := hx
      have hmem : t' * (x : Gs) * t'⁻¹ ∈ E₂ := by
        rw [hE₂]; exact ⟨x, hxE, by simp [MulAut.conj_apply]⟩
      have hmemY : t' * (x : Gs) * t'⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem ht'Y x.2) (Y.inv_mem ht'Y)
      refine ⟨⟨t' * (x : Gs) * t'⁻¹, hmemY⟩, hmem, ?_⟩
      apply Subtype.ext
      show t' * (t' * (x : Gs) * t'⁻¹) * t'⁻¹ = x
      calc t' * (t' * (x : Gs) * t'⁻¹) * t'⁻¹ = (t' * t') * (x : Gs) * (t'⁻¹ * t'⁻¹) := by group
        _ = x := by rw [hsq, ← mul_inv_rev, hsq]; group

end ModelComps

end CFSG.GH74.GLS.Stage1.Main
