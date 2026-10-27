module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (piReindex map_pi_piReindex IsWBlock)
open scoped commutatorElement

section Reindex

variable {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

theorem piReindex_apply (e : ι ≃ Fin (Nat.card ι)) (x : ∀ j, G j) (i : Fin (Nat.card ι)) :
    piReindex (G := G) e x i = x (e.symm i) :=
  Equiv.piCongrLeft'_apply G e x i

theorem piReindex_mulSingle (e : ι ≃ Fin (Nat.card ι)) (i : Fin (Nat.card ι)) (x : G (e.symm i)) :
    piReindex (G := G) e (Pi.mulSingle (e.symm i) x) =
      Pi.mulSingle (M := fun i => G (e.symm i)) i x := by
  funext k
  rw [piReindex_apply]
  by_cases hk : k = i
  · subst hk
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne (e.symm.injective.ne hk), Pi.mulSingle_eq_of_ne hk]

theorem mem_map_mulSingle_of_piReindex (e : ι ≃ Fin (Nat.card ι)) {i : Fin (Nat.card ι)}
    {E : Subgroup (G (e.symm i))} {y : ∀ j, G j}
    (h : piReindex (G := G) e y ∈ E.map (MonoidHom.mulSingle (fun i => G (e.symm i)) i)) :
    y ∈ E.map (MonoidHom.mulSingle G (e.symm i)) := by
  obtain ⟨z, hz, hzy⟩ := h
  refine ⟨z, hz, (piReindex (G := G) e).injective ?_⟩
  rw [MonoidHom.mulSingle_apply, piReindex_mulSingle, ← hzy, MonoidHom.mulSingle_apply]

variable {Q : Type} [Group Q] (e : ι ≃ Fin (Nat.card ι)) (S : ∀ j, Subgroup (G j))
  (β : Q →* ∀ j, G j)

theorem ker_piReindex_comp : ((piReindex (G := G) e).toMonoidHom.comp β).ker = β.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem range_piReindex_comp :
    ((piReindex (G := G) e).toMonoidHom.comp β).range =
      β.range.map (piReindex (G := G) e).toMonoidHom :=
  MonoidHom.range_comp _ _

theorem pi_le_range_piReindex (hS : Subgroup.pi Set.univ S ≤ β.range) :
    Subgroup.pi Set.univ (fun i => S (e.symm i)) ≤
      ((piReindex (G := G) e).toMonoidHom.comp β).range := by
  rw [range_piReindex_comp, ← map_pi_piReindex e S]
  exact Subgroup.map_mono hS

theorem commutator_le_pi_piReindex (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S) :
    ⁅((piReindex (G := G) e).toMonoidHom.comp β).range,
      ((piReindex (G := G) e).toMonoidHom.comp β).range⁆ ≤
      Subgroup.pi Set.univ (fun i => S (e.symm i)) := by
  rw [range_piReindex_comp, ← Subgroup.map_commutator, ← map_pi_piReindex e S]
  exact Subgroup.map_mono hc

theorem relIndex_pi_piReindex :
    (Subgroup.pi Set.univ (fun i => S (e.symm i))).relIndex
      ((piReindex (G := G) e).toMonoidHom.comp β).range =
      (Subgroup.pi Set.univ S).relIndex β.range := by
  rw [range_piReindex_comp, ← map_pi_piReindex e S,
    Subgroup.relIndex_map_map_of_injective _ _ (piReindex (G := G) e).injective]

end Reindex

variable {Y : Type} [Group Y] [Finite Y]

theorem actsInnerlyW_of_levi_data_index {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L) (hZL : Odd (Nat.card (Subgroup.center ↥L)))
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (hρo : Odd (Nat.card ρ.ker)) (Q : Subgroup K)
    (hQ : Q = coverSub ρ P) {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex β.range))
    (hW : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    (hblock : ∀ j, S j ≠ ⊥ → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : ι) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hZW : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ x : ↥Q, ρ (x : K) = 1 →
      β x ∈ (S j).map (MonoidHom.mulSingle G j) → β x = 1)
    (φ : MulAut ↥Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (hgN : ∀ j, ∀ s ∈ S j, g j * s * (g j)⁻¹ ∈ S j)
    {a : Y} (ha : a ∈ Subgroup.normalizer (P : Set Y))
    (hcompat : ∀ x : ↥Q,
      (MulAut.conjNormal a : MulAut ↥L) (ρ (x : K)) * (ρ ((φ x : ↥Q) : K))⁻¹ ∈
        Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ wPre P, a ^ (p ^ m) * w = w * a ^ (p ^ m))
    (hrk : Open.pRank p (wPre P) ≤ 1) :
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P := by
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let π := (piReindex (G := G) e).toMonoidHom
  refine ParabCensus.actsInnerlyW_of_levi_dataP hp2 hPL hZL ρ hρ hker hρo Q hQ
    (G := fun i => G (e.symm i)) (fun i => S (e.symm i)) (fun i => H (e.symm i)) (π.comp β)
    (ker_piReindex_comp e β ▸ h2) (pi_le_range_piReindex e S β hS)
    (commutator_le_pi_piReindex e S β hc) (relIndex_pi_piReindex e S β ▸ hodd)
    (fun i => hW _) (fun i hi => hblock _ hi)
    (fun i E hES hE hcard x hρx hx => hZ _ E hES hE hcard x hρx
      (mem_map_mulSingle_of_piReindex e hx))
    (fun i hq x hρx hx => by
      change π (β x) = 1
      rw [hZW _ hq x hρx (mem_map_mulSingle_of_piReindex e hx), map_one])
    φ (π g) (fun i => by rw [show π g i = g (e.symm i) from piReindex_apply e g i]; exact hg _)
    (fun x => by rw [MonoidHom.comp_apply, hφ, map_mul, map_mul, map_inv]; rfl)
    (fun i s hs => by
      rw [show π g i = g (e.symm i) from piReindex_apply e g i]
      exact hgN _ s hs)
    ha hcompat hpow hrk

theorem leviInnAtW_of_levi_data_index {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L) (hZL : Odd (Nat.card (Subgroup.center ↥L)))
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (hρo : Odd (Nat.card ρ.ker)) (Q : Subgroup K)
    (hQ : Q = coverSub ρ P) {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex β.range))
    (hW : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    (hH : ∀ (x : ↥Q) (j : ι), β x j ∈ H j)
    (hblock : ∀ j, S j ≠ ⊥ → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : ι) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hZW : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ x : ↥Q, ρ (x : K) = 1 →
      β x ∈ (S j).map (MonoidHom.mulSingle G j) → β x = 1)
    (hrk : Open.pRank p (wPre P) ≤ 1) : LeviInnAtPW p P := by
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  let π := (piReindex (G := G) e).toMonoidHom
  exact leviInnAtW_of_levi_dataP hp2 hPL hZL ρ hρ hker hρo Q hQ
    (G := fun i => G (e.symm i)) (fun i => S (e.symm i)) (fun i => H (e.symm i)) (π.comp β)
    (ker_piReindex_comp e β ▸ h2) (pi_le_range_piReindex e S β hS)
    (commutator_le_pi_piReindex e S β hc) (relIndex_pi_piReindex e S β ▸ hodd)
    (fun i => hW _)
    (fun x i => by rw [MonoidHom.comp_apply, show π (β x) i = β x (e.symm i) from
      piReindex_apply e _ i]; exact hH x _)
    (fun i hi => hblock _ hi)
    (fun i E hES hE hcard x hρx hx => hZ _ E hES hE hcard x hρx
      (mem_map_mulSingle_of_piReindex e hx))
    (fun i hq x hρx hx => by
      change π (β x) = 1
      rw [hZW _ hq x hρx (mem_map_mulSingle_of_piReindex e hx), map_one])
    hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
