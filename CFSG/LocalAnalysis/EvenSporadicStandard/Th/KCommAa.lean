module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommT

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

set_option linter.unusedSectionVars false

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

open CFSG.LocalAnalysis.ComponentInitial in
theorem ThCyc.Aa_le_kCommutator {k : G} (hkL : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) :
    Aa ≤ kCommutator (Csub A Aa t) k := by
  classical
  have hkAa : ∀ x ∈ Aa, k * x * k⁻¹ ∈ Aa := W2.conj_mem_of_mem_L W hkL hkA
  have hkn : k ∈ normalizer (Aa : Set G) :=
    mem_normalizer_iff.2 fun x => ⟨fun hx => hkAa x hx, fun hx => by
      have := conj_inv_mem_of_conj_mem hkAa hx
      simpa [mul_assoc] using this⟩
  have hnorm : Subgroup.Normalizes (zpowers k) Aa := ⟨zpowers_le.2 hkn⟩
  have hcard : Nat.card Aa = 2 ^ 8 := W2.Aa_card
  have hsolv : Group.IsSolvable ↥Aa := by
    have h2 : IsPGroup 2 ↥Aa := IsPGroup.of_card hcard
    have : Group.IsNilpotent ↥Aa := h2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥Aa) (Nat.card ↥(zpowers k)) := by
    rw [hcard, Nat.card_zpowers]
    exact Nat.Coprime.pow_left 8 (Nat.coprime_two_left.2 hodd)
  obtain ⟨-, -, hfac, -⟩ :=
    CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization hsolv hcop
  intro x hx
  obtain ⟨d, hd, f, hf, hxdf⟩ := hfac ⟨x, hx⟩
  have hfk : k * (f : G) * k⁻¹ = (f : G) := by
    have h := hf ⟨k, mem_zpowers k⟩
    have h' := congrArg Subtype.val h
    simpa using h'
  have hf1 : (f : G) = 1 := W2.eq_one_of_fixed W hfix f.2 hfk
  have hxd : x = (d : G) := by
    have := congrArg Subtype.val hxdf
    simpa [hf1] using this
  have hmap : (d : G) ∈ (actionCommutator ↥(zpowers k) (⊤ : Subgroup ↥Aa)).map Aa.subtype :=
    ⟨d, hd, rfl⟩
  rw [map_actionCommutator_subtype (zpowers k) Aa ⊤] at hmap
  rw [hxd]
  refine (closure_le _).2 ?_ hmap
  rintro _ ⟨d', hd', a, ha, rfl⟩
  obtain ⟨d'', -, rfl⟩ := hd'
  exact subset_closure ⟨d'', H.Aa_le_inf_centralizer_Aa W W2 d''.2, a, ha, rfl⟩

theorem ThCyc.kCommutator_inf_Aa_sup {k : G} (hk : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) :
    kCommutator (Csub A Aa t) k ⊓ (Aa ⊔ zpowers t) = Aa := by
  have hAaD := H.Aa_le_kCommutator W W2 hk hkA hodd hfix
  have ht := H.t_not_mem_kCommutator W W2 hk hkA hodd
  refine le_antisymm (fun x hx => ?_) (le_inf hAaD le_sup_left)
  obtain ⟨hxD, hxA1⟩ := hx
  have hCl : zpowers t ≤ centralizer (Aa : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => (H.comm_of_mem_L (W.B_le (W2.Aa_le hy))).symm
  obtain ⟨a, ha, e, he, rfl⟩ := exists_mul_of_mem_sup hCl hxA1
  have hea : e ∈ kCommutator (Csub A Aa t) k := by
    have := (kCommutator (Csub A Aa t) k).mul_mem ((kCommutator (Csub A Aa t) k).inv_mem
      (hAaD ha)) hxD
    simpa using this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  rcases zpow_eq_one_or_self H.sq_t j with h | h
  · rw [h, mul_one]
    exact ha
  · rw [h] at hea
    exact absurd hea ht

theorem ThCyc.exists_theta_eq_kCommutator {k : G} (hk : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) {a : G} (ha : a ∈ A) :
    ∃ d ∈ kCommutator (Csub A Aa t) k, theta t d = a := by
  obtain ⟨hDC, -, -, -, hfac⟩ := H.kCommutator_factorization W W2 (C := Csub A Aa t) rfl hk hkA
    hodd hfix
  obtain ⟨c, hc, hca⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 ha
  obtain ⟨d, hd, e, he, rfl⟩ := hfac c hc
  refine ⟨d, hd, ?_⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  have hdBp : d ∈ Bp A t := (hDC hd).1
  have hteBp : t ^ j ∈ Bp A t :=
    (zpowers_le.2 (H.t_mem_inf_centralizer_Aa W W2).1) (Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩)
  rw [H.theta_mul W hdBp hteBp] at hca
  have h1 : theta t (t ^ j) = 1 := by
    simp only [theta]
    group
  rw [h1, mul_one] at hca
  exact hca

end

end CFSG.EvenSporadicStandard.ThStd
