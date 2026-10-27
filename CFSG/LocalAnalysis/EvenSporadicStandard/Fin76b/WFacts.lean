module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

structure WFacts {G : Type*} [Group G] (L : Subgroup G) (t : G) (E : Subgroup G) : Prop where
  card_cent : Nat.card ↥(L ⊓ centralizer ({t} : Set G)) = 1920
  card_E : Nat.card ↥E = 32
  E_le : E ≤ L
  normal : ∀ w ∈ L, w * t = t * w → ∀ e ∈ E, w * e * w⁻¹ ∈ E
  cent : ∀ l ∈ L, (∀ e ∈ E, l * e = e * l) → l = 1 ∨ l = t
  beta : ∃ β ∈ L, β * t = t * β ∧ orderOf β = 3 ∧
    Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8 ∧
    ∃ d₁ ∈ E ⊓ centralizer ({β} : Set G), ∃ d₂ ∈ E ⊓ centralizer ({β} : Set G),
      d₁ * d₂ ≠ d₂ * d₁

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}

theorem wFacts_of_model (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) {X : Type*}
    [Group X] [Finite X] (φ : X ≃* L) {T Ex : Subgroup X} {tx : X} (hM : PinModel X T Ex tx)
    (hR : RootFactsClass X) : WFacts L t E := by
  obtain ⟨ι, hι, hιL, hrange, hTι, hιt⟩ := h.exists_embedding hM φ
  have hEι : E = Ex.map ι := hE.eq_map_of_pinModel h hM ι hι hrange hTι hιt
  have htx2 : orderOf tx = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hM.t_sq) hM.t_ne
  have hsq : ∃ g : X, g * g = tx := by
    have hne : {x | x ∈ T ∧ x * x = tx}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have := hM.roots_ge
      rw [hempty, Set.ncard_empty] at this
      omega
    obtain ⟨x, -, hx⟩ := hne
    exact ⟨x, hx⟩
  have hRf := hR tx htx2 hsq
  have hroots : {x : X | x * x = tx} = {x | x ∈ T ∧ x * x = tx} := by
    have hsub : {x | x ∈ T ∧ x * x = tx} ⊆ {x : X | x * x = tx} := fun x hx => hx.2
    exact (Set.eq_of_subset_of_ncard_le hsub (le_trans hRf.roots_le hM.roots_ge)
      (Set.toFinite _)).symm
  have hEx : rootGroup X tx = Ex := by
    rw [rootGroup, hroots, ← hM.E_eq]
  have hcentι : L ⊓ centralizer ({t} : Set G) = (centralizer ({tx} : Set X)).map ι := by
    ext g
    constructor
    · rintro ⟨hgL, hg⟩
      obtain ⟨x, rfl⟩ := hrange g hgL
      refine ⟨x, mem_centralizer_singleton_iff.2 (hι ?_), rfl⟩
      rw [map_mul, map_mul, hιt]
      exact mem_centralizer_singleton_iff.1 hg
    · rintro ⟨x, hx, rfl⟩
      refine ⟨hιL x, mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hιt, ← map_mul, ← map_mul]
      exact congrArg ι (mem_centralizer_singleton_iff.1 hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcentι, Subgroup.card_map_of_injective hι]
    exact hRf.card_cent
  · rw [hEι, Subgroup.card_map_of_injective hι, ← hEx]
    exact hRf.card_E
  · exact (hE.le).trans h.T₀_le
  · intro w hwL hwt e he
    obtain ⟨x, rfl⟩ := hrange w hwL
    rw [hEι] at he ⊢
    obtain ⟨f, hf, rfl⟩ := he
    have hxt : x * tx = tx * x := hι (by rw [map_mul, map_mul, hιt]; exact hwt)
    refine ⟨x * f * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [← hEx] at hf ⊢
    have hconj : ∀ y, y * y = tx → x * y * x⁻¹ * (x * y * x⁻¹) = tx := by
      intro y hy
      calc x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
        _ = x * tx * x⁻¹ := by rw [hy]
        _ = tx := by rw [hxt]; group
    have : (rootGroup X tx).map (MulAut.conj x).toMonoidHom ≤ rootGroup X tx := by
      rw [rootGroup, MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact subset_closure (by simpa [MulAut.conj_apply] using hconj y hy)
    simpa [MulAut.conj_apply] using this ⟨f, hf, rfl⟩
  · intro l hlL hl
    obtain ⟨y, rfl⟩ := hrange l hlL
    have hy := hRf.cent_E y (fun r hr => by
      have hrE : ι r ∈ E := by
        rw [hEι, ← hEx]
        exact ⟨r, subset_closure hr, rfl⟩
      have := hl _ hrE
      rw [← map_mul, ← map_mul] at this
      exact hι this)
    rcases hy with hy | hy
    · left; rw [hy, map_one]
    · right; rw [hy, hιt]
  · obtain ⟨β, hβt, hβ3, hcard, d₁, hd₁, d₂, hd₂, hne⟩ := hRf.beta
    have hE' : E = (rootGroup X tx).map ι := by rw [hEι, hEx]
    have himg : E ⊓ centralizer ({ι β} : Set G) =
        (rootGroup X tx ⊓ centralizer ({β} : Set X)).map ι := by
      ext g
      constructor
      · rintro ⟨hgE, hg⟩
        rw [hE'] at hgE
        obtain ⟨f, hf, rfl⟩ := hgE
        refine ⟨f, ⟨hf, mem_centralizer_singleton_iff.2 (hι ?_)⟩, rfl⟩
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.1 hg
      · rintro ⟨f, ⟨hf, hfc⟩, rfl⟩
        refine ⟨by rw [hE']; exact ⟨f, hf, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ι (mem_centralizer_singleton_iff.1 hfc)
    refine ⟨ι β, hιL β, ?_, ?_, ?_, ι d₁, ?_, ι d₂, ?_, ?_⟩
    · rw [← hιt, ← map_mul, ← map_mul, hβt]
    · rw [← hβ3]; exact orderOf_injective ι hι β
    · rw [himg, Subgroup.card_map_of_injective hι]; exact hcard
    · rw [himg]; exact ⟨d₁, hd₁, rfl⟩
    · rw [himg]; exact ⟨d₂, hd₂, rfl⟩
    · intro hc
      apply hne
      apply hι
      rw [map_mul, map_mul]
      exact hc

end CFSG.EvenSporadicStandard.Fin76b
