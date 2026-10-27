module

import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_card_eq_prime_of_pRank_le_one {p : ℕ} [Fact p.Prime] {Q A B : Subgroup G}
    (hQ : IsPGroup p Q) (hr : CFSG.Open.pRank p Q ≤ 1) (hAQ : A ≤ Q) (hBQ : B ≤ Q)
    (hA : Nat.card A = p) (hB : Nat.card B = p) : A = B := by
  have hp : p.Prime := Fact.out
  obtain ⟨C, hCQ, hCp, hCc⟩ : ∃ C : Subgroup G, C ≤ Q ∧ Nat.card C = p ∧
      ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c := by
    have : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact hp.one_lt.trans_le (hA ▸ Subgroup.card_le_of_le hAQ)
    have hZ : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
    have hdvd : p ∣ Nat.card (Subgroup.center Q) :=
      ((hQ.to_subgroup (Subgroup.center Q)).card_eq_or_dvd).resolve_left
        (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨zpowers ((z : Q) : G), ?_, ?_, ?_⟩
    · rw [zpowers_le]
      exact (z : Q).2
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    · intro c hc q hq
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      have h1 : Commute ((z : Q) : G) q :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩).symm
      exact (h1.zpow_left k).eq
  have key : ∀ X : Subgroup G, X ≤ Q → Nat.card X = p → X = C := by
    intro X hXQ hXp
    by_contra hXC
    have hdisj : X ⊓ C = ⊥ := by
      have hdvd : Nat.card ↥(X ⊓ C) ∣ p := hXp ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have h2 : X ⊓ C = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hXp])
        exact hXC (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h2) (by rw [hXp, hCp]))
    have hcomm : ∀ (x : X) (c : C), Commute (X.subtype x) (C.subtype c) := fun x c =>
      (hCc c c.2 x (hXQ x.2)).symm
    have hf : Function.Injective (X.subtype.noncommCoprod C.subtype hcomm) :=
      (MonoidHom.noncommCoprod_injective _ _ _).mpr
        ⟨X.subtype_injective, C.subtype_injective, by simpa [disjoint_iff] using hdisj⟩
    have hXcyc : IsCyclic X := isCyclic_of_prime_card hXp
    have hCcyc : IsCyclic C := isCyclic_of_prime_card hCp
    have h2 := CFSG.SectionRank.le_pRank_of_injective (p := p) hp.one_lt (A := ↥X × ↥C) (k := 2)
      (fun a b => Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2))
      (fun a => Prod.ext (by simpa [hXp] using pow_card_eq_one' (x := a.1))
        (by simpa [hCp] using pow_card_eq_one' (x := a.2)))
      (by rw [Nat.card_prod, hXp, hCp, sq]) (X.subtype.noncommCoprod C.subtype hcomm) hf
      (H := Q) (by
        rintro _ ⟨⟨x, c⟩, rfl⟩
        exact Q.mul_mem (hXQ x.2) (hCQ c.2))
    omega
  rw [key A hAQ hA, key B hBQ hB]

theorem exists_mem_map_conj_eq_of_card_eq_prime {p : ℕ} [Fact p.Prime] {H A B : Subgroup G}
    (hr : CFSG.Open.pRank p H ≤ 1) (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : Nat.card A = p) (hB : Nat.card B = p) :
    ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B := by
  have hp : p.Prime := Fact.out
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p H
  obtain ⟨g₁, hg₁, hAS⟩ := exists_conj_mem_of_isSylowOf hS
    (IsPGroup.of_card (n := 1) (by rwa [pow_one])) hAH
  obtain ⟨g₂, hg₂, hBS⟩ := exists_conj_mem_of_isSylowOf hS
    (IsPGroup.of_card (n := 1) (by rwa [pow_one])) hBH
  have heq := eq_of_card_eq_prime_of_pRank_le_one hS.isPGroup
    ((pRank_mono p hp.one_lt hS.le).trans hr)
    (A := A.map (MulAut.conj g₁).toMonoidHom) (B := B.map (MulAut.conj g₂).toMonoidHom)
    (by rintro _ ⟨a, ha, rfl⟩; exact hAS a ha) (by rintro _ ⟨b, hb, rfl⟩; exact hBS b hb)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g₁).injective, hA])
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g₂).injective, hB])
  refine ⟨g₂⁻¹ * g₁, H.mul_mem (H.inv_mem hg₂) hg₁, ?_⟩
  rw [← conjugate_map_mul A g₂⁻¹ g₁, heq, conjugate_map_mul B g₂⁻¹ g₂, inv_mul_cancel]
  ext x
  simp

end CFSG.LocalAnalysis.RankThreeUC
