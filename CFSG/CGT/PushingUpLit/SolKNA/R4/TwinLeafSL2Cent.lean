module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y]

theorem normal_two_le_center_of_sl2 {A X : Subgroup Y} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : ↥A ≃* SL(2, F)) (hXA : X ≤ A)
    (hXn : (X.subgroupOf A).Normal) (hX2 : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1) :
    ∀ x ∈ X, ∀ a ∈ A, x * a = a * x := by
  classical
  have hW : ((X.subgroupOf A).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hXn e.toMonoidHom e.surjective
  rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.sl2_normal h4 ((X.subgroupOf A).map e.toMonoidHom) with
    hc | htop
  · intro x hx a ha
    have hmem : e ⟨x, hXA hx⟩ ∈ (X.subgroupOf A).map e.toMonoidHom :=
      ⟨⟨x, hXA hx⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
    have h1 := Subgroup.mem_center_iff.1 (hc hmem) (e ⟨a, ha⟩)
    have h2 : e (⟨a, ha⟩ * ⟨x, hXA hx⟩) = e (⟨x, hXA hx⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]; exact h1
    have h3 := e.injective h2
    exact (congrArg Subtype.val h3).symm
  · exfalso
    have hF1 : Nat.card F ≠ 1 := by omega
    obtain ⟨p, hp, hpF⟩ := Nat.exists_prime_and_dvd hF1
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpF)
    have hpS : p ∣ Nat.card SL(2, F) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
      exact hpF.mul_right _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpS
    have hgW : g ∈ (X.subgroupOf A).map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x', hx', rfl⟩ := hgW
    have hxX : ((x' : ↥A) : Y) ∈ X := hx'
    obtain ⟨k, hk⟩ := hX2 _ hxX
    have h1 : x' ^ 2 ^ k = 1 := Subtype.ext hk
    have h2 : (e.toMonoidHom x') ^ 2 ^ k = 1 := by rw [← map_pow, h1, map_one]
    have h3 : p ∣ 2 ^ k := hg ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))

theorem commute_of_normal_odd_two {C A D O : Subgroup Y} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : ↥A ≃* SL(2, F))
    (hAC : A ≤ C) (hDC : D ≤ C) (hAn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    (hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hOn : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    (hOodd : Odd (Nat.card O)) (hDO : ∀ g ∈ D, ∃ k : ℕ, g ^ 2 ^ k ∈ O) :
    ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := by
  classical
  have hOA : O ⊓ A = ⊥ := by
    refine noOddNormal_of_equiv_sl2 hodd h4 e _ inf_le_right ⟨fun n hn g => ?_⟩
      (hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnO, hnA⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨hOn g (hAC g.2) n hnO,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnA) (Subgroup.inv_mem _ g.2)⟩
  have hXn : ((D ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnD, hnA⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨hDn g (hAC g.2) n hnD,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnA) (Subgroup.inv_mem _ g.2)⟩
  have hX2 : ∀ x ∈ D ⊓ A, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hDO x (Subgroup.mem_inf.1 hx).1
    refine ⟨k, ?_⟩
    have : x ^ 2 ^ k ∈ O ⊓ A := Subgroup.mem_inf.2 ⟨hk, A.pow_mem (Subgroup.mem_inf.1 hx).2 _⟩
    rw [hOA] at this
    exact Subgroup.mem_bot.1 this
  have hXc := normal_two_le_center_of_sl2 hodd h4 e inf_le_right hXn hX2
  have hAD : ⁅A, D⁆ ≤ Subgroup.centralizer (A : Set Y) := by
    refine Subgroup.commutator_le.2 fun a ha d hd => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hmem : ⁅a, d⁆ ∈ D ⊓ A := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (hDn a (hAC ha) d hd) (Subgroup.inv_mem _ hd)
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine Subgroup.mul_mem _ ha ?_
        rw [← mul_assoc]
        exact hAn d (hDC hd) a⁻¹ (Subgroup.inv_mem _ ha)
    exact (hXc _ hmem b hb).symm
  have h1 : ⁅⁅A, D⁆, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAD
  have h2 : ⁅⁅D, A⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm D A]; exact h1
  have h3 : ⁅⁅A, A⁆, D⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hperf : ⁅A, A⁆ = A := by
    have : Group.IsPerfect SL(2, F) := sl2_isPerfect h4
    have hA : Group.IsPerfect ↥A := by
      refine ⟨?_⟩
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) this.commutator_eq_top
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.symm.surjective] at h
      rw [commutator_def]
      exact h
    exact Subgroup.isPerfect_iff.1 hA
  rw [hperf] at h3
  intro d hd a ha
  have : ⁅a, d⁆ ∈ (⊥ : Subgroup Y) := by
    rw [← h3]; exact Subgroup.commutator_mem_commutator ha hd
  exact (commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 this)).symm

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
