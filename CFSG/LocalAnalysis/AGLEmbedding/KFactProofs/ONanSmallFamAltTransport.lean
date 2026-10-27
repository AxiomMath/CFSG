module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltCoord
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {p : ℕ}

theorem exists_altModel [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup (Perm (Fin (2 * p)))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    ∃ Φ : Perm (ZMod p × Fin 2) ≃* Perm (Fin (2 * p)),
      (∀ x, Perm.sign (Φ x) = Perm.sign x) ∧
      ∀ x, Φ x ∈ E ↔ x ∈ (altEtr : Subgroup (Perm (ZMod p × Fin 2))) := by
  have hp : p.Prime := Fact.out
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
  exact ⟨Φ, fun x => Perm.sign_permCongr c x, hmem⟩

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
