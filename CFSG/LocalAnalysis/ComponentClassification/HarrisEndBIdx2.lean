module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdxDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup
open scoped commutatorElement

section Sig

variable {G : Type*} [Group G]

@[expose] def sigProd (z : G) (a : Fin 4 → G) (p : (Fin 4 → Bool) × Bool) : G :=
  (if p.1 0 then a 0 else 1) * (if p.1 1 then a 1 else 1) * (if p.1 2 then a 2 else 1) *
    (if p.1 3 then a 3 else 1) * (if p.2 then z else 1)

@[expose] def SigRel (z : G) (sq : Fin 4 → Bool) (cm : Fin 4 → Fin 4 → Bool) (a : Fin 4 → G) :
    Prop :=
  (∀ k, a k ^ 2 = if sq k then z else 1) ∧ (∀ k l, ⁅a k, a l⁆ = if cm k l then z else 1) ∧
    Function.Injective (sigProd z a)

theorem sigProd_map {G' : Type*} [Group G'] (f : G →* G') (z : G) (a : Fin 4 → G) (p) :
    f (sigProd z a p) = sigProd (f z) (fun k => f (a k)) p := by
  simp only [sigProd, map_mul, apply_ite f, map_one]

theorem SigRel.map {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Injective f) {z : G}
    {sq cm} {a : Fin 4 → G} (h : SigRel z sq cm a) : SigRel (f z) sq cm (fun k => f (a k)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun k => ?_, fun k l => ?_, fun p q hpq => h3 (hf ?_)⟩
  · rw [← map_pow, h1 k, apply_ite f, map_one]
  · rw [← map_commutatorElement, h2 k l, apply_ite f, map_one]
  · rw [sigProd_map, sigProd_map]
    exact hpq

theorem sigProd_mem {K : Subgroup G} {z : G} (hz : z ∈ K) {a : Fin 4 → G} (ha : ∀ k, a k ∈ K)
    (p) : sigProd z a p ∈ K := by
  simp only [sigProd]
  refine mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_ <;> split_ifs <;>
    first | exact one_mem _ | exact ha _ | exact hz

theorem closure_eq_of_sigRel [Finite G] {K : Subgroup G} (hK : Nat.card K = 32) {z : G}
    {sq cm} {a : Fin 4 → G} (ha : ∀ k, a k ∈ K) (h : SigRel z sq cm a)
    (hzc : z ∈ closure (Set.range a)) : closure (Set.range a) = K := by
  have hle : closure (Set.range a) ≤ K := by
    rw [closure_le]
    rintro _ ⟨k, rfl⟩
    exact ha k
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hK]
  have hinj : Function.Injective (fun p : (Fin 4 → Bool) × Bool =>
      (⟨sigProd z a p, sigProd_mem hzc (fun k => subset_closure ⟨k, rfl⟩) p⟩ :
        ↥(closure (Set.range a)))) :=
    fun p q hpq => h.2.2 (congrArg Subtype.val hpq)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at this

end Sig

section Count

theorem mem_quads {L₀ L₁ L₂ L₃ : List ℕ} {a : ℕ × ℕ × ℕ × ℕ} :
    a ∈ quads L₀ L₁ L₂ L₃ ↔ a.1 ∈ L₀ ∧ a.2.1 ∈ L₁ ∧ a.2.2.1 ∈ L₂ ∧ a.2.2.2 ∈ L₃ := by
  obtain ⟨a₀, a₁, a₂, a₃⟩ := a
  simp only [quads, List.mem_product]

theorem nodup_quads {L₀ L₁ L₂ L₃ : List ℕ} (h₀ : L₀.Nodup) (h₁ : L₁.Nodup) (h₂ : L₂.Nodup)
    (h₃ : L₃.Nodup) : (quads L₀ L₁ L₂ L₃).Nodup :=
  h₀.product (h₁.product (h₂.product h₃))

end Count

end CFSG.ComponentClassification.HarrisLit.EndB
