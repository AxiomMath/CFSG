module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAltRank
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Equiv Equiv.Perm

theorem exists_elemAbelian_perm_six : ∃ E : Subgroup (Perm (Fin 6)),
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ 8 ≤ Nat.card E := by
  classical
  set s₀ : Perm (Fin 6) := swap 0 1
  set s₁ : Perm (Fin 6) := swap 2 3
  set s₂ : Perm (Fin 6) := swap 4 5
  set T := closure ({s₀, s₁, s₂} : Set (Perm (Fin 6)))
  have hT := elemAbelian_closure (S := ({s₀, s₁, s₂} : Set (Perm (Fin 6)))) (by
      intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> decide)
    (by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl <;> exact swap_mul_self _ _)
  set H₁ := (⊥ : Subgroup (Perm (Fin 6))) ⊔ zpowers s₀
  set H₂ := H₁ ⊔ zpowers s₁
  set H₃ := H₂ ⊔ zpowers s₂
  have hstab : ∀ (z : Fin 6) (g : Perm (Fin 6)), g z = z →
      zpowers g ≤ MulAction.stabilizer (Perm (Fin 6)) z :=
    fun z g hg => (zpowers_le).mpr hg
  have h1 : 2 * Nat.card (⊥ : Subgroup (Perm (Fin 6))) ≤ Nat.card H₁ :=
    two_mul_card_le_sup (z := 0) (fun h hh => by rw [(mem_bot.mp hh)]; rfl) (by decide)
  have h2 : 2 * Nat.card H₁ ≤ Nat.card H₂ :=
    two_mul_card_le_sup (z := 2) (fun h hh => (sup_le bot_le (hstab 2 s₀ (by decide))) hh)
      (by decide)
  have h3 : 2 * Nat.card H₂ ≤ Nat.card H₃ :=
    two_mul_card_le_sup (z := 4)
      (fun h hh => (sup_le (sup_le bot_le (hstab 4 s₀ (by decide))) (hstab 4 s₁ (by decide))) hh)
      (by decide)
  rw [card_bot] at h1
  have hH₃T : H₃ ≤ T :=
    sup_le (sup_le (sup_le bot_le ((zpowers_le).mpr (subset_closure (by simp))))
      ((zpowers_le).mpr (subset_closure (by simp)))) ((zpowers_le).mpr (subset_closure (by simp)))
  exact ⟨H₃, fun x hx y hy => hT.1 x (hH₃T hx) y (hH₃T hy), fun x hx => hT.2 x (hH₃T hx),
    by omega⟩

theorem elemAbelian_comap {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {E : Subgroup H} (hE : E ≤ f.range)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card (E.comap f) = Nat.card E ∧ (∀ x ∈ E.comap f, ∀ y ∈ E.comap f, x * y = y * x) ∧
      ∀ x ∈ E.comap f, x * x = 1 := by
  refine ⟨?_, fun x hx y hy => hf (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy),
    fun x hx => hf (by rw [map_mul, map_one]; exact hsq _ hx)⟩
  conv_rhs => rw [← map_comap_eq_self hE]
  rw [card_map_of_injective hf]

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem not_sectionalTwoRankLE_of_perm_six (hnab : ∃ a b : Y, a * b ≠ b * a) {τ : MulAut Y}
    {P : Type} [Group P] {ρ : MulAut Y →* MulAut P} (hρ : Function.Injective ρ)
    {N : Subgroup (MulAut P)} (hN : Nonempty (↥N ≃* Perm (Fin 6)))
    (hNle : N ≤ (generalizedFitting (MulAut Y) ⊓ centralizer {τ}).map ρ) :
    ¬ GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2 := by
  classical
  obtain ⟨eN⟩ := hN
  obtain ⟨E₀, hE₀c, hE₀s, hE₀8⟩ := exists_elemAbelian_perm_six
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  set E₁ : Subgroup (MulAut P) := (E₀.map eN.symm.toMonoidHom).map N.subtype with hE₁
  have hE₁N : E₁ ≤ N := map_subtype_le _
  have hE₁c : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, ← Subgroup.coe_mul, ← map_mul,
      hE₀c u hu v hv]
  have hE₁s : ∀ x ∈ E₁, x * x = 1 := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, ← Subgroup.coe_mul, ← map_mul,
      hE₀s u hu, map_one, Subgroup.coe_one]
  have hE₁card : Nat.card E₁ = Nat.card E₀ := by
    rw [hE₁, card_map_of_injective N.subtype_injective,
      card_map_of_injective eN.symm.injective]
  have hE₁ρ : E₁ ≤ ρ.range := hE₁N.trans (hNle.trans (map_le_range _ _))
  obtain ⟨hE₂card, hE₂c, hE₂s⟩ := elemAbelian_comap hρ hE₁ρ hE₁c hE₁s
  have hE₂G : E₁.comap ρ ≤ generalizedFitting (MulAut Y) ⊓ centralizer {τ} := by
    intro g hg
    obtain ⟨g', hg'G, hg'⟩ := hNle (hE₁N hg)
    rwa [hρ hg'] at hg'G
  have hE₂W : E₁.comap ρ ≤ (MulAut.conj : Y →* MulAut Y).range :=
    (hE₂G.trans inf_le_left).trans hF.le
  obtain ⟨hE₃card, hE₃c, hE₃s⟩ :=
    elemAbelian_comap (conj_injective_of_center hZ) hE₂W hE₂c hE₂s
  refine not_sectionalTwoRankLE_of_le (E := (E₁.comap ρ).comap MulAut.conj) ?_ hE₃c
    (fun x hx => by rw [pow_two]; exact hE₃s x hx) ?_
  · intro y hy
    exact (conj_mem_centralizer_iff hZ τ y).mp (hE₂G hy).2
  · rw [hE₃card, hE₂card, hE₁card]
    omega

end CFSG.ComponentClassification.HarrisLit.Hin
