module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2J2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co3
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Presentation.Co2Exact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 Certificates.CoreD2Perm
open CFSG.AGLEmbedding.CoreD2 (gs_rep rep_map_words mem_of_central card_closure_pair_of_pow
  wordVal_mem_of mem_normalizer_zpowers_of_mul_eq)
open Certificates.FusD2Perm (powT wordT)

section Group

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem glbCore_one_eq_top_of_gens (hp : p.Prime) {A : Subgroup K} {Γ : Set K}
    (hΓ : Subgroup.closure Γ = ⊤)
    (h : ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ y ^ p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g) :
    GLBCore p 1 A = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_top_iff, ← hΓ, Subgroup.closure_le]
  intro g hg
  obtain ⟨y, hyA, hy1, hyp, α, hgy⟩ := h g hg
  refine CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 (Subgroup.zpowers_le.2 hyA) ?_
    (mem_normalizer_zpowers_of_mul_eq hgy)
  exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl
    (CFSG.AGLEmbedding.CoreD2.isElemAbelian_zpowers hyp)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1, pow_one])

theorem glbCore_one_eq_top_of_mulEquiv {L : Type*} [Group L] [Finite L] {e : ℕ} (hp : p.Prime)
    (φ : K ≃* L) {E : Subgroup L} (hE : Nat.card E = p ^ e)
    (hfac : (Nat.card L).factorization p = e)
    (h : ∀ B : Subgroup L, B ≤ E → IsElemAbelian p B → Nat.card B = p ^ 2 → GLBCore p 1 B = ⊤)
    (A : Subgroup K) (hA : IsElemAbelian p A) (hc : Nat.card A = p ^ 2) : GLBCore p 1 A = ⊤ := by
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
    (by rw [Subgroup.card_map_of_injective ψ.injective, hc])
  rw [CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_equiv] at h1
  apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rw [h1, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective]

end Group

private theorem factorization_eq {p n e : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ^ e ∣ n)
    (h2 : ¬ p ^ (e + 1) ∣ n) : n.factorization p = e := by
  have h3 := (hp.pow_dvd_iff_le_factorization hn).1 h1
  have h4 : ¬ e + 1 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem glbCore_one_eq_top_J2
    (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J2).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 2) : GLBCore 3 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  obtain ⟨E, hEc, hE⟩ := CFSG.AGLEmbedding.j2_normalizer_gens
  refine glbCore_one_eq_top_of_mulEquiv Nat.prime_three
    ((e₁.trans e₂.symm).trans CFSG.Sporadic.Schreier.j2PermEquiv) hEc ?_
    (fun B hBE hBe hBc => by
      obtain ⟨Γ, hΓ, hn⟩ := hE B hBE hBe hBc
      exact CFSG.AGLEmbedding.CoreD2.glbCore_one_eq_top_of_normalizer_gens Nat.prime_three hBe
        hΓ hn)
    A hA hc
  rw [← Nat.card_congr CFSG.Sporadic.Schreier.j2PermEquiv.toEquiv, CFSG.Sporadic.J2.card_J2]
  exact factorization_eq Nat.prime_three (by norm_num) (by norm_num) (by norm_num)

theorem glbCore_one_eq_top_Co2
    (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) : GLBCore 5 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  obtain ⟨E, hEc, hE⟩ := CFSG.AGLEmbedding.co2_normalizer_gens
  refine glbCore_one_eq_top_of_mulEquiv Nat.prime_five
    ((e₁.trans e₂.symm).trans CFSG.Sporadic.Co2Cert.co2PermEquiv) hEc ?_
    (fun B hBE hBe hBc => by
      obtain ⟨Γ, hΓ, hn⟩ := hE B hBE hBe hBc
      exact CFSG.AGLEmbedding.CoreD2.glbCore_one_eq_top_of_normalizer_gens Nat.prime_five hBe
        hΓ hn)
    A hA hc
  rw [← Nat.card_congr CFSG.Sporadic.Co2Cert.co2PermEquiv.toEquiv, CFSG.Sporadic.Co2.card_Co2]
  exact factorization_eq Nat.prime_five (by norm_num) (by norm_num) (by norm_num)

theorem glbCore_one_eq_top_Co3
    (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) : GLBCore 5 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  obtain ⟨E, hEc, hE⟩ := CFSG.AGLEmbedding.co3_normalizer_gens
  refine glbCore_one_eq_top_of_mulEquiv Nat.prime_five
    ((e₁.trans e₂.symm).trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv) hEc ?_
    (fun B hBE hBe hBc => by
      obtain ⟨Γ, hΓ, hn⟩ := hE B hBE hBe hBc
      exact CFSG.AGLEmbedding.CoreD2.glbCore_one_eq_top_of_normalizer_gens Nat.prime_five hBe
        hΓ hn)
    A hA hc
  rw [← Nat.card_congr CFSG.Sporadic.Schreier.Co3.co3PermEquiv.toEquiv,
    CFSG.Sporadic.Co3.card_Co3]
  exact factorization_eq Nat.prime_five (by norm_num) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
