module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section TypeFree

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_into_self {H : Subgroup G} [Finite H] {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hcard : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem mem_normalizer_of_le_closure_involutions {H : Subgroup G} [Finite H] {g : G}
    (hgen : H ≤ closure {x : G | x ∈ H ∧ x * x = 1})
    (hg : ∀ y ∈ H, y * y = 1 → g * y * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  refine mem_normalizer_of_conj_into_self fun x hx => ?_
  have h1 : (closure {x : G | x ∈ H ∧ x * x = 1}).map (MulAut.conj g).toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, ⟨hyH, hyy⟩, rfl⟩
    exact hg y hyH hyy
  exact h1 ⟨x, hgen hx, rfl⟩

theorem mem_or_exists_conj_of_mul_self_eq_one {S₀ : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htS₀ : t ∈ normalizer (S₀ : Set G))
    (hThom : ∀ x ∈ S₀, x * t * (x * t) = 1 → ∃ z ∈ S₀, x * t = z * t * z⁻¹)
    {y : G} (hy : y ∈ S₀ ⊔ zpowers t) (hyy : y * y = 1) :
    y ∈ S₀ ∨ ∃ z ∈ S₀, y = z * t * z⁻¹ := by
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htS₀ hy with h | h
  · exact Or.inl h
  · have h1 : y * t * t = y := by rw [mul_assoc, ht2, mul_one]
    obtain ⟨z, hzS, hz⟩ := hThom _ h (by rw [h1]; exact hyy)
    rw [h1] at hz
    exact Or.inr ⟨z, hzS, hz⟩

end TypeFree

@[expose] def LFiveFieldSylowGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      S₀ ≤ closure {x : G | x ∈ S₀ ∧ x * x = 1}

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_normalizer_of_mem_normalizer_sup_zpowers
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} (hS₀N : S₀ ≤ seitzTilde W₁ Kc) (htS₀ : t ∈ normalizer (S₀ : Set G))
    (hThom : ∀ x ∈ S₀, x * t * (x * t) = 1 → ∃ z ∈ S₀, x * t = z * t * z⁻¹)
    (hgen : S₀ ≤ closure {x : G | x ∈ S₀ ∧ x * x = 1}) {g : G}
    (hg : g ∈ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G)) :
    g ∈ normalizer (S₀ : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hconj := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  refine mem_normalizer_of_le_closure_involutions hgen fun y hyS hyy => ?_
  have hy1 : g * y * g⁻¹ ∈ S₀ ⊔ zpowers t := (mem_normalizer_iff.1 hg y).1 (mem_sup_left hyS)
  have hy2 : g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  rcases mem_or_exists_conj_of_mul_self_eq_one ht2 htS₀ hThom hy1 hy2 with h | ⟨z, hzS, hz⟩
  · exact h
  · exfalso
    apply hconj (z⁻¹ * g)
    have h1 : (z⁻¹ * g)⁻¹ * t * (z⁻¹ * g) = y := by
      calc (z⁻¹ * g)⁻¹ * t * (z⁻¹ * g) = g⁻¹ * (z * t * z⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hz]
        _ = y := by group
    rw [h1]
    exact hS₀N hyS

theorem lFiveFieldSylowNormalInput_of_gen
    (hB : LFiveThompsonFieldInput) (hΩ : LFiveFieldSylowGenInput) :
    LFiveFieldSylowNormalInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀ g
    _ hgN _
  obtain ⟨-, hS₀N, -, htS₀, -⟩ := id hS₀
  exact mem_normalizer_of_mem_normalizer_sup_zpowers hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN
    hfield hS₀N htS₀
    (hB G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀)
    (hΩ G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀) hgN

end Setting

end CFSG.SeitzReduction.LinearPilot
