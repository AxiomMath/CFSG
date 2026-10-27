module

public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Dihedral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

@[expose] def Section3SzInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, Sec3 T T₁ → ∀ a : ℕ, 1 ≤ a →
      ¬ ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
        Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* Sz a)

@[expose] def Section3DihedralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, Sec3 T T₁ → ∀ n : ℕ, Odd n → 3 ≤ n →
      (∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
        Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n)) → n = 3

theorem sl2_mulEquiv_dihedral_three_of_card_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hFcard : Nat.card F = 2) : Nonempty (DihedralGroup 3 ≃* SL(2, F)) := by
  have hone : (1 : F) * 1 = 1 := mul_one 1
  have ha : (utriElt (1 : F)) * utriElt 1 = 1 := utriElt_mul_self 1
  have hb : (ltriElt (1 : F)) * ltriElt 1 = 1 := ltriElt_mul_self 1
  have ha1 : utriElt (1 : F) ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : SL(2, F) => g 0 1) h
    simp only [utriElt_apply_01, one_apply_01] at h01
    exact one_ne_zero h01
  have hord : orderOf (utriElt (1 : F) * ltriElt 1) = 3 := orderOf_utriElt_mul_ltriElt hone
  have hcard : Nat.card SL(2, F) = 6 := by
    rw [card_sl2, hFcard]
    norm_num
  refine dihedral_mulEquiv_of_involutions (a := utriElt (1 : F)) (b := ltriElt 1) (n := 3)
    ⟨1, by norm_num⟩ ha ha1 hb hord ?_
  set H : Subgroup SL(2, F) := Subgroup.closure ({utriElt (1 : F), ltriElt 1} : Set SL(2, F))
  have haH : utriElt (1 : F) ∈ H := Subgroup.subset_closure (by simp)
  have hbH : ltriElt (1 : F) ∈ H := Subgroup.subset_closure (by simp)
  have hdvd : Nat.card H ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have h2 : 2 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H haH
    have ho : orderOf (utriElt (1 : F)) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using ha) ha1
    simpa [ho] using this
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (H.mul_mem haH hbH)
    simpa [hord] using this
  have h6 : Nat.card H = 6 := by
    have h6' : 6 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    exact Nat.dvd_antisymm hdvd h6'
  exact Subgroup.eq_top_of_card_eq H (h6.trans hcard.symm)

theorem psl2_two_mulEquiv_dihedral_three :
    Nonempty (DihedralGroup 3 ≃* PSL(2, GaloisField 2 1)) := by
  obtain ⟨e⟩ := sl2_mulEquiv_dihedral_three_of_card_two (F := GaloisField 2 1)
    (by rw [GaloisField.card 2 1 one_ne_zero, pow_one])
  exact ⟨e.trans pslMulEquivSL.symm⟩

theorem section3IsoInput_of_parts (h214 : Lemma214) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) : Section3IsoInput := by
  intro G _ _ _ hnab T T₁ hS
  obtain ⟨x, -, hx⟩ := hS.conj
  have hT : IsWC T := hS.cfg.wc
  have hne : conjSubgroup x T ≠ T := by
    intro h
    have hinf : T ⊓ T₁ = ⊥ := hS.cfg.inf
    rw [hx, h, inf_idem] at hinf
    apply hS.cfg.ne
    exact eq_bot_iff.2 fun y hy => by
      have hyT : y ∈ T := hy.1
      rwa [hinf] at hyT
  have hL : normIn T (conjSubgroup x T) ≠ ⊥ := hx ▸ hS.cfg.ne
  obtain ⟨-, hN, hcases⟩ := h214 G T hT x hne hL
  subst hx
  rcases hcases with ⟨f, hf, hiso⟩ | ⟨a, ha, hiso⟩ | ⟨n, hn, hn3, hiso⟩
  · exact ⟨hN, f, by omega, hiso⟩
  · exact absurd ⟨hN, hiso⟩ (hSz G hnab T _ hS a ha)
  · have h3 : n = 3 := hD G hnab T _ hS n hn hn3 ⟨hN, hiso⟩
    subst h3
    obtain ⟨e⟩ := hiso
    obtain ⟨e'⟩ := psl2_two_mulEquiv_dihedral_three
    exact ⟨hN, 1, one_ne_zero, ⟨e.trans e'⟩⟩

end CFSG.CGT.Timmesfeld75
