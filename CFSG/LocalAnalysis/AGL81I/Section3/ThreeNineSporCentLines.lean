module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import Certificates.Certificate1322010
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Lines

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open CFSG.AGLEmbedding.CoreD2 (gs_rep rep_map_words mem_of_central card_closure_pair_of_pow
  wordVal_mem_of)
open Certificates.FusD2Perm (powT wordT)

section Group

variable {K : Type*} [Group K] {p : ℕ}

theorem eq_top_of_cent_gens {A : Subgroup K} {Γ : Set K} (hΓ : Subgroup.closure Γ = ⊤)
    (h : ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g) (Y : Subgroup K)
    (hY : ∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) : Y = ⊤ := by
  rw [eq_top_iff, ← hΓ, Subgroup.closure_le]
  intro g hg
  obtain ⟨y, hyA, hy1, hgy⟩ := h g hg
  exact hY y hyA hy1 (Subgroup.mem_centralizer_singleton_iff.2 hgy)

theorem eq_top_of_mulEquiv_cent {L : Type*} [Group L] [Finite L] {e : ℕ} (hp : p.Prime)
    (φ : K ≃* L) {E : Subgroup L} (hE : Nat.card E = p ^ e)
    (hfac : (Nat.card L).factorization p = e)
    (h : ∀ B : Subgroup L, B ≤ E → IsElemAbelian p B → Nat.card B = p ^ 2 →
      ∀ Y : Subgroup L, (∀ y ∈ B, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) → Y = ⊤)
    (A : Subgroup K) (hA : IsElemAbelian p A) (hc : Nat.card A = p ^ 2) (Y : Subgroup K)
    (hY : ∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) : Y = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hφc : Nat.card (A.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
  obtain ⟨T, hT⟩ := (IsPGroup.of_card hφc).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L T (Sylow.ofCard E (by rw [hE, hfac]))
  set ψ : K ≃* L := φ.trans (MulAut.conj g)
  have hψE : A.map ψ.toMonoidHom ≤ E := by
    have hgT : ((g • T : Sylow p L) : Subgroup L) =
        (T : Subgroup L).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hg, Sylow.coe_ofCard] at hgT
    rw [hgT]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.2 ⟨φ x, hT (Subgroup.mem_map_of_mem _ hx), rfl⟩
  have h1 := h _ hψE (CFSG.SectionRank.isElemAbelian_map hA _)
    (by rw [Subgroup.card_map_of_injective ψ.injective, hc]) (Y.map ψ.toMonoidHom) ?_
  · apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [h1, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective]
  · rintro _ ⟨y, hyA, rfl⟩ hy1 c hc
    refine Subgroup.mem_map.2 ⟨ψ.symm c, hY y hyA (fun h1 => hy1 (by simp [h1])) ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    apply ψ.injective
    simpa using hc

end Group

theorem centralizers_eq_top_Co3
    (K : Type*) [Group K] [Finite K]
    (hK : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Co3)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) (Y : Subgroup K)
    (hY : ∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) : Y = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨E, hEc, hE⟩ := Certificates.certificate1322010
  refine eq_top_of_mulEquiv_cent Nat.prime_five
    (e₁.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv) hEc ?_
    (fun B hBE hBe hBc => (hE B hBE hBe hBc).elim fun _ hΓ => eq_top_of_cent_gens hΓ.1 hΓ.2)
    A hA hc Y hY
  rw [← Nat.card_congr CFSG.Sporadic.Schreier.Co3.co3PermEquiv.toEquiv,
    CFSG.Sporadic.Co3.card_Co3]
  exact factorization_eq_of_pow_dvd Nat.prime_five (by norm_num) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_co3
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    {d : ℕ} (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Co3) : False := by
  obtain ⟨e⟩ := hs
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e
  have hcK : Nat.card ↥K = 495766656000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co3.card_Co3
  refine h.false_of_centralizers_eq_top
    (SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)) ?_
    (SporCent.centralizers_eq_top_Co3 ↥K ⟨e⟩)
  rw [Nat.card_congr (equivalence e).toEquiv,
    show Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
      CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
  norm_num

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
