module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Tools
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

open CFSG.SectionRank

@[expose] def sixInv : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 3 4

theorem sixInv_sign : Equiv.Perm.sign sixInv = 1 := by decide +kernel

theorem sixInv_conj_012 : sixInv * six012 * sixInv⁻¹ = six012⁻¹ := by decide +kernel

theorem sixInv_conj_345 : sixInv * six345 * sixInv⁻¹ = six345⁻¹ := by decide +kernel

@[expose] def altInv {n : ℕ} (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  altEmbed hn ⟨sixInv, sixInv_sign⟩

theorem altInv_conj_A {n : ℕ} (hn : 6 ≤ n) :
    altInv hn * altCycA hn * (altInv hn)⁻¹ = (altCycA hn)⁻¹ := by
  have h : (⟨sixInv, sixInv_sign⟩ : alternatingGroup (Fin 6)) * ⟨six012, six012_sign⟩ *
      (⟨sixInv, sixInv_sign⟩ : alternatingGroup (Fin 6))⁻¹ =
      (⟨six012, six012_sign⟩ : alternatingGroup (Fin 6))⁻¹ :=
    Subtype.ext sixInv_conj_012
  unfold altInv altCycA
  rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]

theorem altInv_conj_B {n : ℕ} (hn : 6 ≤ n) :
    altInv hn * altCycB hn * (altInv hn)⁻¹ = (altCycB hn)⁻¹ := by
  have h : (⟨sixInv, sixInv_sign⟩ : alternatingGroup (Fin 6)) * ⟨six345, six345_sign⟩ *
      (⟨sixInv, sixInv_sign⟩ : alternatingGroup (Fin 6))⁻¹ =
      (⟨six345, six345_sign⟩ : alternatingGroup (Fin 6))⁻¹ :=
    Subtype.ext sixInv_conj_345
  unfold altInv altCycB
  rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]

theorem not_forall_commute_alt {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hc : Nat.card (Subgroup.center L) = 3) {n : ℕ} (hn : 6 ≤ n) (hn8 : n ≤ 8)
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin n)) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_sylowThreeAlt hn hn8
  have hA : altCycA hn ∈ sylowThreeAlt hn := by
    rw [← closure_altCyc hn]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : altCycB hn ∈ sylowThreeAlt hn := by
    rw [← closure_altCyc hn]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hE := isElemAbelian_sylowThreeAlt hn
  exact not_forall_commute_of_cover hq hc e (hE.2 _ hA) (hE.2 _ hB)
    ⟨altInv hn, altInv_conj_A hn⟩ ⟨altInv hn, altInv_conj_B hn⟩ Q
    (hQ.trans (closure_altCyc hn).symm) S

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
