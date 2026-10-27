module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltCoord
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem ncard_of_invariant_perm (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (Perm (Fin (2 * p)))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) (P : Set (Perm (Fin (2 * p))))
    (hP : P ⊆ (E : Set (Perm (Fin (2 * p)))) \ {1})
    (hinv : ∀ g : Perm (Fin (2 * p)), Perm.sign g = 1 →
      g ∈ Subgroup.normalizer (E : Set (Perm (Fin (2 * p)))) → ∀ t ∈ P, g * t * g⁻¹ ∈ P) :
    P.ncard = 0 ∨ P.ncard = p ^ 2 - 1 ∨ P.ncard = 2 * (p - 1) ∨ P.ncard = (p - 1) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hE hcard
  obtain ⟨c, hc⟩ := exists_alt_coord (hE.2 a₁ ha₁) (hE.2 a₂ ha₂) hO₁ hO₂ hd hm₁ hm₂
  let Φ : Perm (ZMod p × Fin 2) ≃* Perm (Fin (2 * p)) := c.permCongrHom
  have hΦ : ∀ (σ : Perm (ZMod p × Fin 2)) (w : ZMod p × Fin 2), Φ σ (c w) = c (σ w) := by
    intro σ w
    simp [Φ, Equiv.permCongrHom, Equiv.permCongr_apply]
  have hA1 : Φ (altTr 1 0) = a₁ := by
    refine Equiv.ext fun x => ?_
    obtain ⟨⟨k, s⟩, rfl⟩ := c.surjective x
    rw [hΦ]
    fin_cases s
    · simp [altTr_apply, (hc k).1]
    · simp [altTr_apply, (hc k).2.1]
  have hA2 : Φ (altTr 0 1) = a₂ := by
    refine Equiv.ext fun x => ?_
    obtain ⟨⟨k, s⟩, rfl⟩ := c.surjective x
    rw [hΦ]
    fin_cases s
    · simp [altTr_apply, (hc k).2.2.1]
    · simp [altTr_apply, (hc k).2.2.2]
  have htr : ∀ i j : ZMod p, Φ (altTr i j) = a₁ ^ i.val * a₂ ^ j.val := by
    intro i j
    have h1 : altTr i j = (altTr 1 0) ^ i.val * (altTr 0 1) ^ j.val := by
      rw [altTr_pow, altTr_pow, altTr_mul]
      simp
    rw [h1, map_mul, map_pow, map_pow, hA1, hA2]
  have htrE : ∀ i j : ZMod p, Φ (altTr i j) ∈ E := fun i j => by
    rw [htr]
    exact mul_mem (pow_mem ha₁ _) (pow_mem ha₂ _)
  have hmem : ∀ x : Perm (ZMod p × Fin 2),
      Φ x ∈ E ↔ x ∈ (altEtr : Subgroup (Perm (ZMod p × Fin 2))) := by
    intro x
    constructor
    · intro hx
      let ψ : ZMod p × ZMod p → E := fun y => ⟨Φ (altTr y.1 y.2), htrE y.1 y.2⟩
      have hψinj : Function.Injective ψ := by
        intro y z h
        obtain ⟨h1, h2⟩ := altTr_injective (Φ.injective (congrArg Subtype.val h))
        exact Prod.ext h1 h2
      have hψbij : Function.Bijective ψ := hψinj.bijective_of_nat_card_le (by
        rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
      obtain ⟨y, hy⟩ := hψbij.2 ⟨Φ x, hx⟩
      exact ⟨y.1, y.2, (Φ.injective (congrArg Subtype.val hy)).symm⟩
    · rintro ⟨i, j, rfl⟩
      exact htrE i j
  let P' : Set (Perm (ZMod p × Fin 2)) := Φ ⁻¹' P
  have hncard : P.ncard = P'.ncard := by
    have h1 : (Φ '' P').ncard = P'.ncard := Set.ncard_image_of_injective _ Φ.injective
    rwa [Set.image_preimage_eq P Φ.surjective] at h1
  have hP' : P' ⊆ ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
      Set (Perm (ZMod p × Fin 2))) \ {1} := by
    intro y hy
    refine ⟨(hmem y).1 (hP hy).1, fun h => (hP hy).2 ?_⟩
    have h1 : y = 1 := h
    show Φ y = 1
    rw [h1, map_one]
  have hinv' : ∀ g : Perm (ZMod p × Fin 2), Perm.sign g = 1 →
      g ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
        Set (Perm (ZMod p × Fin 2))) → ∀ t ∈ P', g * t * g⁻¹ ∈ P' := by
    intro g hsg hg t ht
    have h1 : Φ g ∈ Subgroup.normalizer (E : Set (Perm (Fin (2 * p)))) := by
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      obtain ⟨y, rfl⟩ := Φ.surjective x
      have hy : y ∈ (altEtr : Subgroup (Perm (ZMod p × Fin 2))) := (hmem y).1 hx
      have h2 : g * y * g⁻¹ ∈ (altEtr : Subgroup (Perm (ZMod p × Fin 2))) :=
        (Subgroup.mem_normalizer_iff.1 hg y).1 hy
      show Φ g * Φ y * (Φ g)⁻¹ ∈ E
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (hmem _).2 h2
    have h2 : Perm.sign (Φ g) = 1 := (Perm.sign_permCongr c g).trans hsg
    have h3 := hinv (Φ g) h2 h1 (Φ t) ht
    show Φ (g * t * g⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact h3
  rw [hncard]
  exact ncard_altEtr_of_invariant hp2 P' hP' hinv'

theorem orbits_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) (T : Sylow p K)
    (O : Set K) (hO : O ⊆ (T : Set K) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = p ^ 2 - 1 ∨ O.ncard = 2 * (p - 1) ∨ O.ncard = (p - 1) ^ 2 := by
  obtain ⟨e⟩ := hK
  set ι := altPermEmbed e with hι'
  have hι : Function.Injective ι := altPermEmbed_injective e
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  set E : Subgroup (Perm (Fin (2 * p))) := (T : Subgroup K).map ι with hE
  rw [← Set.ncard_image_of_injective O hι]
  refine ncard_of_invariant_perm hp hp2 hEab hEcard (ι '' O) ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨htT, ht1⟩ := hO ht
    refine ⟨⟨t, htT, rfl⟩, fun h => ht1 ?_⟩
    have h1 : ι t = ι 1 := by rw [map_one]; exact h
    exact hι h1
  · rintro g hsg hgN _ ⟨t, ht, rfl⟩
    let n : K := e.symm ⟨g, Perm.mem_alternatingGroup.2 hsg⟩
    have hιn : ι n = g := by simp [n, ι, altPermEmbed]
    have hnN : n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      have h1 : ι x ∈ E := ⟨x, hx, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hgN (ι x)).1 h1
      rw [← hιn] at h2
      obtain ⟨x', hx', hx'e⟩ := h2
      have h3 : x' = n * x * n⁻¹ := hι (by rw [hx'e]; simp)
      rw [← h3]
      exact hx'
    refine ⟨n * t * n⁻¹, hinv n hnN t ht, ?_⟩
    rw [map_mul, map_mul, map_inv, hιn]

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
