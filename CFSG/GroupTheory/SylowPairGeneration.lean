module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_ne_le_normalizer_of_not_modEq {p : ℕ} [Fact p.Prime] {A : Subgroup X}
    (hA : (Nat.card A).Prime) (U : Sylow p X)
    (hAU : A ≤ normalizer ((U : Subgroup X) : Set X))
    (hcount : ¬ Nat.card (Sylow p X) ≡ 1 [MOD Nat.card A]) :
    ∃ P : Sylow p X, P ≠ U ∧ A ≤ normalizer ((P : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.card A).Prime := ⟨hA⟩
  have hAp : IsPGroup (Nat.card A) A := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hcong := hAp.card_modEq_card_fixedPoints (Sylow p X)
  have hUfix : U ∈ MulAction.fixedPoints A (Sylow p X) := fun a =>
    (Subgroup.smul_def a U).trans (Sylow.smul_eq_iff_mem_normalizer.2 (hAU a.2))
  by_contra hno
  have hsub : MulAction.fixedPoints A (Sylow p X) = {U} := by
    ext P
    refine ⟨fun hP => ?_, fun hP => (Set.mem_singleton_iff.1 hP) ▸ hUfix⟩
    by_contra hPU
    exact hno ⟨P, hPU, fun a ha =>
      Sylow.smul_eq_iff_mem_normalizer.1 ((Subgroup.smul_def ⟨a, ha⟩ P).symm.trans (hP ⟨a, ha⟩))⟩
  rw [hsub] at hcong
  simp only [Nat.card_unique] at hcong
  exact hcount hcong

theorem sup_normalizer_eq_top_of_sylow_pair {p : ℕ} [Fact p.Prime] {A : Subgroup X}
    (hA : (Nat.card A).Prime) (U : Sylow p X)
    (hAU : A ≤ normalizer ((U : Subgroup X) : Set X))
    (hcount : ¬ Nat.card (Sylow p X) ≡ 1 [MOD Nat.card A])
    (hgen : ∀ P Q : Sylow p X, P ≠ Q → (P : Subgroup X) ⊔ (Q : Subgroup X) = ⊤)
    (hrank : CFSG.Open.pRank (Nat.card A) (⊤ : Subgroup X) ≤ 1) :
    (U : Subgroup X) ⊔ normalizer (A : Set X) = ⊤ := by
  classical
  have : Fact (Nat.card A).Prime := ⟨hA⟩
  obtain ⟨U', hU'U, hAU'⟩ := exists_sylow_ne_le_normalizer_of_not_modEq hA U hAU hcount
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X U U'
  set N : Subgroup X := normalizer ((U' : Subgroup X) : Set X) with hN
  have hAp : IsPGroup (Nat.card A) A := IsPGroup.of_card (n := 1) (by rw [pow_one])
  set A' : Subgroup X := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'N : A' ≤ N := by
    rintro _ ⟨a, ha, rfl⟩
    refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
    rw [← hg]
    change (g * a * g⁻¹) • (g • U) = g • U
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, Sylow.smul_eq_iff_mem_normalizer.2 (hAU ha)]
  obtain ⟨R, hR⟩ := (hAp.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨R', hR'⟩ :=
    ((hAp.map (MulAut.conj g).toMonoidHom).comap_subtype (K := N)).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (↥N) R' R
  set Rx : Subgroup X := (R : Subgroup ↥N).map N.subtype with hRx
  have hARx : A ≤ Rx := fun a ha => ⟨⟨a, hAU' ha⟩, hR (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  set B : Subgroup X := A'.map (MulAut.conj (b : X)).toMonoidHom with hB
  have hBRx : B ≤ Rx := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hy : (⟨g * a * g⁻¹, hA'N ⟨a, ha, rfl⟩⟩ : ↥N) ∈ (R' : Subgroup ↥N) :=
      hR' (Subgroup.mem_subgroupOf.2 ⟨a, ha, rfl⟩)
    have hy' := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj b) _ hy
    rw [← Sylow.coe_subgroup_smul, hb] at hy'
    exact ⟨_, hy', rfl⟩
  have hcardB : Nat.card B = Nat.card A := by
    rw [hB, Subgroup.card_map_of_injective (f := (MulAut.conj (b : X)).toMonoidHom)
      (MulAut.conj (b : X)).injective, hA',
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  have hBA : B = A := CFSG.LocalAnalysis.RankThreeUC.eq_of_card_eq_prime_of_pRank_le_one
    (R.isPGroup'.map N.subtype)
    ((CFSG.SectionRank.pRank_mono hA.one_lt le_top).trans hrank) hBRx hARx hcardB rfl
  have hhA : (b : X) * g ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Eq.trans ?_ hBA
    rw [hB, hA', Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hhU : ((b : X) * g) • U = U' := by
    rw [mul_smul, hg]
    exact Sylow.smul_eq_iff_mem_normalizer.2 b.2
  refine eq_top_iff.2 ?_
  rw [← hgen U U' (Ne.symm hU'U)]
  refine sup_le le_sup_left ?_
  rw [← hhU]
  intro x hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  change (b : X) * g * u * ((b : X) * g)⁻¹ ∈ _
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hhA) (Subgroup.mem_sup_left hu))
    (inv_mem (Subgroup.mem_sup_right hhA))

omit [Finite X] in
theorem commutator_ne_bot_of_sup_normalizer_eq_top [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) {A U : Subgroup X} (hA : (Nat.card A).Prime)
    (hsup : U ⊔ normalizer (A : Set X) = ⊤) : ⁅U, A⁆ ≠ ⊥ := by
  intro hUA
  have hUN : U ≤ normalizer (A : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hUA).trans
      (Subgroup.centralizer_le_normalizer _)
  have htop : normalizer (A : Set X) = ⊤ := by
    rw [← hsup, sup_eq_right.2 hUN]
  rcases (Subgroup.normalizer_eq_top_iff.1 htop).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.card_bot] at hA
    exact Nat.not_prime_one hA
  · obtain ⟨a, b, hab⟩ := hX
    have : Fact (Nat.card A).Prime := ⟨hA⟩
    have hcard : Nat.card X = Nat.card A := by rw [h, Subgroup.card_top]
    have : IsCyclic X := isCyclic_of_prime_card hcard
    exact hab (IsCyclic.commGroup.mul_comm a b)

end CFSG.GroupTheory
