module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructTwo
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.LocalCores

theorem exists_perm_hom_of_equiv_alt {A : Type*} [Group A] {Γ Y : Subgroup A}
    (e : Y ≃* alternatingGroup (Fin 5)) (hYΓ : Y ≤ Γ)
    (hYn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∃ π : Γ →* Equiv.Perm (Fin 5),
      (∀ (y : A) (hy : y ∈ Y),
        π ⟨y, hYΓ hy⟩ = ((e ⟨y, hy⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) ∧
      ∀ g : Γ, π g = 1 → ∀ y ∈ Y, (g : A) * y = y * g := by
  classical
  have hN : (Y.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hYn g g.2 n hn⟩
  let eN : (Y.subgroupOf Γ) ≃* alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hYΓ).trans e
  have bij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  let c : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) := MulEquiv.ofBijective _ bij
  let π : Γ →* Equiv.Perm (Fin 5) :=
    c.symm.toMonoidHom.comp
      ((MulAut.congr eN).toMonoidHom.comp (MulAut.conjNormal (H := Y.subgroupOf Γ)))
  have key : ∀ γ : Γ, c (π γ) =
      MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) := fun γ => by
    simp [π]
  refine ⟨π, ?_, ?_⟩
  · intro y hy
    set γ : Γ := ⟨y, hYΓ hy⟩ with hγ
    set n : Y.subgroupOf Γ := ⟨γ, hy⟩ with hn
    have h1 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) =
        c ((eN n : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      refine MulEquiv.ext fun a => ?_
      have h3 : MulAut.conjNormal (H := Y.subgroupOf Γ) γ (eN.symm a) = n * eN.symm a * n⁻¹ :=
        Subtype.ext (MulAut.conjNormal_apply γ _)
      have h5 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) a =
          eN (n * eN.symm a * n⁻¹) := by
        show eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ (eN.symm a)) = _
        rw [h3]
      rw [h5, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      refine Subtype.ext ?_
      show _ = ((MulAut.conjNormal ((eN n : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) a :
        alternatingGroup (Fin 5)).1
      rw [MulAut.conjNormal_apply]
      rfl
    have h2 : π γ = ((eN n : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
      apply c.injective
      rw [key, ← h1]
    rw [h2]
    rfl
  · intro γ hγ y hy
    have h1 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) = 1 := by
      rw [← key, hγ, map_one]
    have h2 : MulAut.conjNormal (H := Y.subgroupOf Γ) γ = 1 := by
      have := (MulAut.congr eN).injective (h1.trans (map_one (MulAut.congr eN)).symm)
      exact this
    have h3 := congrArg (fun φ : MulAut (Y.subgroupOf Γ) =>
      ((φ ⟨⟨y, hYΓ hy⟩, hy⟩ : Y.subgroupOf Γ) : Γ)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    exact mul_inv_eq_iff_eq_mul.mp h4

theorem exists_sign_hom_of_equiv_alt {A : Type*} [Group A] {Γ Y : Subgroup A}
    (e : Y ≃* alternatingGroup (Fin 5)) (hYΓ : Y ≤ Γ)
    (hYn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∃ χ : Γ →* ℤˣ, ∀ g : Γ, χ g = 1 →
      ∃ y ∈ Y, ∀ x ∈ Y, (y⁻¹ * (g : A)) * x = x * (y⁻¹ * (g : A)) := by
  obtain ⟨π, hπ1, hπ2⟩ := exists_perm_hom_of_equiv_alt e hYΓ hYn
  refine ⟨Equiv.Perm.sign.comp π, fun g hg => ?_⟩
  have hgA : π g ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hg
  let a : alternatingGroup (Fin 5) := ⟨π g, hgA⟩
  have hyY : ((e.symm a : Y) : A) ∈ Y := (e.symm a).2
  have hπy : π ⟨((e.symm a : Y) : A), hYΓ hyY⟩ = π g := by
    rw [hπ1 _ hyY]
    simp [a]
  refine ⟨((e.symm a : Y) : A), hyY, fun x hx => ?_⟩
  have h1 : π (⟨((e.symm a : Y) : A), hYΓ hyY⟩⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hπy, inv_mul_cancel]
  exact hπ2 _ h1 x hx

theorem TwoComp.mem_layer_of_inner {N : Type} [Group N] {S₁ S₂ : Subgroup N}
    (hT : TwoComp N S₁ S₂) {g : N}
    (h₁ : ∃ y ∈ S₁, ∀ x ∈ S₁, (y⁻¹ * g) * x = x * (y⁻¹ * g))
    (h₂ : ∃ y ∈ S₂, ∀ x ∈ S₂, (y⁻¹ * g) * x = x * (y⁻¹ * g)) : g ∈ layer N := by
  obtain ⟨y₁, hy₁, hc₁⟩ := h₁
  obtain ⟨y₂, hy₂, hc₂⟩ := h₂
  have hy₁' : y₁⁻¹ ∈ S₁ := S₁.inv_mem hy₁
  have hy₂' : y₂⁻¹ ∈ S₂ := S₂.inv_mem hy₂
  obtain ⟨z, hz⟩ : ∃ z : N, z = y₂⁻¹ * (y₁⁻¹ * g) := ⟨_, rfl⟩
  have hz' : z = y₁⁻¹ * (y₂⁻¹ * g) := by
    rw [hz, ← mul_assoc, ← mul_assoc, ← hT.comm _ hy₁' _ hy₂']
  have hzS₁ : ∀ x ∈ S₁, x * z = z * x := by
    intro x hx
    calc x * z = (x * y₂⁻¹) * (y₁⁻¹ * g) := by simp only [hz, mul_assoc]
      _ = (y₂⁻¹ * x) * (y₁⁻¹ * g) := by rw [hT.comm x hx _ hy₂']
      _ = y₂⁻¹ * (x * (y₁⁻¹ * g)) := mul_assoc _ _ _
      _ = y₂⁻¹ * ((y₁⁻¹ * g) * x) := by rw [hc₁ x hx]
      _ = z * x := by simp only [hz, mul_assoc]
  have hzS₂ : ∀ x ∈ S₂, x * z = z * x := by
    intro x hx
    calc x * z = (x * y₁⁻¹) * (y₂⁻¹ * g) := by simp only [hz', mul_assoc]
      _ = (y₁⁻¹ * x) * (y₂⁻¹ * g) := by rw [(hT.comm _ hy₁' x hx).symm]
      _ = y₁⁻¹ * (x * (y₂⁻¹ * g)) := mul_assoc _ _ _
      _ = y₁⁻¹ * ((y₂⁻¹ * g) * x) := by rw [hc₂ x hx]
      _ = z * x := by simp only [hz', mul_assoc]
  have hz1 : z = 1 := by
    have hzc : z ∈ centralizer ((layer N : Subgroup N) : Set N) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, ← hT.sup_eq] at hh
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hT.comm h).1 hh
      calc a * b * z = a * (b * z) := mul_assoc _ _ _
        _ = a * (z * b) := by rw [hzS₂ b hb]
        _ = (a * z) * b := (mul_assoc _ _ _).symm
        _ = (z * a) * b := by rw [hzS₁ a ha]
        _ = z * (a * b) := mul_assoc _ _ _
    rw [hT.cent_bot, mem_bot] at hzc
    exact hzc
  have hg : g = y₁ * y₂ := by
    calc g = y₁ * (y₂ * (y₂⁻¹ * (y₁⁻¹ * g))) := by group
      _ = y₁ * y₂ := by rw [← hz, hz1, mul_one]
  rw [hg, ← hT.sup_eq]
  exact mul_mem_sup hy₁ hy₂

open scoped commutatorElement in
theorem derivedSeries_two_le_layer_of_twoComp {N : Type} [Group N] [Finite N]
    {S₁ S₂ : Subgroup N} (hT : TwoComp N S₁ S₂) (h₁ : Nat.card S₁ = 60)
    (h₂ : Nat.card S₂ = 60) : derivedSeries N 2 ≤ layer N := by
  have hS₁ := hT.simple₁
  have hS₂ := hT.simple₂
  obtain ⟨e₁⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h₁
  obtain ⟨e₂⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h₂
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Subgroup N, Γ = normalizer (S₁ : Set N) := ⟨_, rfl⟩
  have hΓ₁ : ∀ g ∈ Γ, ∀ y ∈ S₁, g * y * g⁻¹ ∈ S₁ := fun g hg y hy => by
    rw [hΓ] at hg
    exact (mem_normalizer_iff.1 hg y).1 hy
  have hΓ₂ : ∀ g ∈ Γ, ∀ y ∈ S₂, g * y * g⁻¹ ∈ S₂ := by
    intro g hg y hy
    rw [hΓ, mem_normalizer_iff_map_eq] at hg
    rcases hT.normalizes_or_swaps g with ⟨_, h2⟩ | ⟨h1, _⟩
    · have : g * y * g⁻¹ ∈ S₂.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
      rwa [h2] at this
    · exact absurd (hg.symm.trans h1) hT.ne
  have hS₁Γ : S₁ ≤ Γ := by
    rw [hΓ]
    exact le_normalizer
  have hS₂Γ : S₂ ≤ Γ := by
    intro x hx
    rw [hΓ, mem_normalizer_iff]
    intro h
    have hx' : x⁻¹ ∈ S₂ := S₂.inv_mem hx
    constructor
    · intro hh
      have h2 : x * h * x⁻¹ = h := by
        calc x * h * x⁻¹ = (h * x) * x⁻¹ := by rw [hT.comm h hh x hx]
          _ = h := by group
      rwa [h2]
    · intro hh
      have h3 : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ := (hT.comm _ hh _ hx').symm
      have h4 : h = x * h * x⁻¹ := by
        calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
          _ = ((x * h * x⁻¹) * x⁻¹) * x := by rw [h3]
          _ = x * h * x⁻¹ := by group
      rwa [← h4] at hh
  have hmapmul : ∀ (a b : N) (T : Subgroup N), T.map (MulAut.conj (a * b)).toMonoidHom =
      (T.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b T
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hPmul : ∀ a b : N, a * b ∈ Γ ↔ (a ∈ Γ ↔ b ∈ Γ) := by
    intro a b
    simp only [hΓ, mem_normalizer_iff_map_eq, hmapmul]
    rcases hT.normalizes_or_swaps a with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
    rcases hT.normalizes_or_swaps b with ⟨hb1, -⟩ | ⟨hb1, -⟩ <;>
    simp only [ha1, ha2, hb1, iff_self, true_iff, iff_true]
  have hcomm : ∀ a b : N, ⁅a, b⁆ ∈ Γ := by
    intro a b
    have h1 := hPmul (a * b * a⁻¹) b⁻¹
    have h2 := hPmul (a * b) a⁻¹
    have h3 := hPmul a b
    have h4 : a⁻¹ ∈ Γ ↔ a ∈ Γ := inv_mem_iff
    have h5 : b⁻¹ ∈ Γ ↔ b ∈ Γ := inv_mem_iff
    rw [commutatorElement_def]
    tauto
  obtain ⟨χ₁, hχ₁⟩ := exists_sign_hom_of_equiv_alt (Γ := Γ) e₁ hS₁Γ hΓ₁
  obtain ⟨χ₂, hχ₂⟩ := exists_sign_hom_of_equiv_alt (Γ := Γ) e₂ hS₂Γ hΓ₂
  have hker : ∀ (χ : Γ →* ℤˣ) (a b : Γ), χ ⁅a, b⁆ = 1 := fun χ a b => by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  have hD : derivedSeries N 2 = ⁅⁅(⊤ : Subgroup N), ⊤⁆, ⁅(⊤ : Subgroup N), ⊤⁆⁆ := rfl
  have hDΓ : ⁅(⊤ : Subgroup N), ⊤⁆ ≤ Γ := commutator_le.2 fun x _ y _ => hcomm x y
  rw [hD]
  refine commutator_le.2 fun a ha b hb => ?_
  have haΓ : a ∈ Γ := hDΓ ha
  have hbΓ : b ∈ Γ := hDΓ hb
  have hgcoe : ((⁅(⟨a, haΓ⟩ : Γ), ⟨b, hbΓ⟩⁆ : Γ) : N) = ⁅a, b⁆ := rfl
  obtain ⟨y₁, hy₁, hc₁⟩ := hχ₁ _ (hker χ₁ ⟨a, haΓ⟩ ⟨b, hbΓ⟩)
  obtain ⟨y₂, hy₂, hc₂⟩ := hχ₂ _ (hker χ₂ ⟨a, haΓ⟩ ⟨b, hbΓ⟩)
  rw [hgcoe] at hc₁ hc₂
  exact hT.mem_layer_of_inner ⟨y₁, hy₁, hc₁⟩ ⟨y₂, hy₂, hc₂⟩

end CFSG.OddStandard.Seitz77
