module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section OddParts

omit [Field K] [Finite K] [CharP K 2] in
theorem ordCompl_two_pow_mul (k x : ℕ) : ordCompl[2] (2 ^ k * x) = ordCompl[2] x :=
  Nat.ordCompl_self_pow_mul x k Nat.prime_two

omit [Field K] [Finite K] [CharP K 2] in
theorem ordCompl_two_of_odd {x : ℕ} (hx : ¬ 2 ∣ x) : ordCompl[2] x = x :=
  (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x Nat.prime_two).2 (Or.inr hx)

theorem exists_card_eq_two_pow : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩

theorem not_two_dvd_card_pow_sub_one {j : ℕ} (hj : 1 ≤ j) : ¬ 2 ∣ Nat.card K ^ (2 * j) - 1 := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow (K := K)
  rw [hK, ← pow_mul]
  have hpos : 1 ≤ 2 ^ (f * (2 * j)) := Nat.one_le_two_pow
  have heven : 2 ∣ 2 ^ (f * (2 * j)) := dvd_pow_self 2 (by positivity)
  omega

theorem not_two_dvd_prod (m : ℕ) :
    ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1) := by
  rw [(Nat.prime_iff.1 Nat.prime_two).dvd_finsetProd_iff]
  rintro ⟨j, hj, h⟩
  exact not_two_dvd_card_pow_sub_one (Finset.mem_Icc.1 hj).1 h

theorem ordCompl_card_statedSp (m : ℕ) :
    ordCompl[2] (Nat.card (StatedSp m K)) = ∏ j ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * j) - 1) := by
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow (K := K)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  conv_lhs => rw [hK, ← pow_mul]
  rw [ordCompl_two_pow_mul, ← hK, ordCompl_two_of_odd (not_two_dvd_prod m)]

theorem ordCompl_card_mul_of_isPGroup {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (x : ℕ) : ordCompl[2] (Nat.card Q * x) = ordCompl[2] x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  rw [hk, ordCompl_two_pow_mul]

end OddParts

section Cores

variable (n : ℕ)

theorem perfectCore_centralizer_spRep_b1_eq (hK : 4 ≤ Nat.card K) :
    perfectCore (centralizer ({spRep (K := K) n .b1} : Set (StatedSp (n + 3) K))) =
      transvRadical K 1 ⊔ complSp K 1 := by
  rw [spRep_b1_eq_siegDiag, CFSG.Quasithin.perfectCore_eq_self_of_perfect
    (commutator_centralizer_siegDiag (K := K) (m := n + 2) hK (p := 1) (by omega)),
    centralizer_siegDiag_eq_sup]

theorem ordCompl_card_perfectCore_b1 (hK : 4 ≤ Nat.card K) :
    ordCompl[2] (Nat.card (perfectCore (centralizer ({spRep (K := K) n .b1} :
      Set (StatedSp (n + 3) K))))) = ∏ j ∈ Finset.Icc 1 (n + 2), (Nat.card K ^ (2 * j) - 1) := by
  rw [perfectCore_centralizer_spRep_b1_eq n hK,
    GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      complSp_le_normalizer_transvRadical disjoint_transvRadical_complSp,
    ordCompl_card_mul_of_isPGroup isPGroup_transvRadical,
    ← Nat.card_congr (complSpEquiv (K := K) (1 : Fin (n + 3))).toEquiv, ordCompl_card_statedSp]

theorem ordCompl_card_perfectCore_c2 (hK : 4 ≤ Nat.card K) :
    ordCompl[2] (Nat.card (perfectCore (centralizer ({spRep (K := K) n .c2} :
      Set (StatedSp (n + 3) K))))) = ∏ j ∈ Finset.Icc 1 (n + 1), (Nat.card K ^ (2 * j) - 1) := by
  have h12 := one_ne_two_fin (n := n)
  have hML : spCompl12 K n ≤ (leviHom h12 (1 : K) one_ne_zero).range :=
    spCompl12_le_range_leviHom one_ne_zero
  rw [spRep_c2_eq, perfectCore_centralizer_c2 hK,
    GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (hML.trans (range_leviHom_le_normalizer_wRadical h12 one_ne_zero))
      ((disjoint_wRadical_range_leviHom h12 one_ne_zero).mono_right hML),
    ordCompl_card_mul_of_isPGroup (isPGroup_wRadical h12),
    ← Nat.card_congr (spCompl12Equiv K n).toEquiv, ordCompl_card_statedSp]


omit [Finite K] [CharP K 2] in
theorem shortBlock_mem_suppGroup (A : SL(2, K)) :
    shortBlock K (one_ne_two_fin (n := n)) A ∈
      suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t} := by
  have hoff : ∀ x : Fin (n + 3), (OffPQ 1 2 (Sum.inl x) ↔ x ≠ 1 ∧ x ≠ 2) ∧
      (OffPQ 1 2 (Sum.inr x) ↔ x ≠ 1 ∧ x ≠ 2) := fun x => by
    simp [OffPQ, mem_coords]
  have hB : ∀ (B : Matrix (Fin 2) (Fin 2) K) (x y : Fin (n + 3)),
      ((x ≠ 1 ∧ x ≠ 2) ∨ (y ≠ 1 ∧ y ≠ 2)) →
      CFSG.LieType.Steinberg.Sp.blockMat (1 : Fin (n + 3)) 2 B x y =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y := by
    intro B x y hxy
    simp only [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply]
    rcases hxy with ⟨hx1, hx2⟩ | ⟨hy1, hy2⟩
    · simp [hx1, hx2]
    · by_cases hx1 : x = 1
      · subst hx1
        simp [hy1, hy2, Ne.symm hy1]
      by_cases hx2 : x = 2
      · subst hx2
        simp [hy1, hy2, Ne.symm hy2]
      · simp [hx1, hx2]
  intro r t hrt
  simp only [Set.mem_ofPred_eq, not_not, not_and_or] at hrt
  rw [mat_shortBlock]
  rcases r with x | x <;> rcases t with y | y
  · rw [fromBlocks_apply₁₁]
    have h := hB (A : Matrix (Fin 2) (Fin 2) K) x y (by
      rcases hrt with h | h
      · exact Or.inl ((hoff x).1.1 h)
      · exact Or.inr ((hoff y).1.1 h))
    rw [h]
    simp [Matrix.one_apply]
  · rfl
  · rfl
  · rw [fromBlocks_apply₂₂, Matrix.transpose_apply]
    have h := hB ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) y x (by
      rcases hrt with h | h
      · exact Or.inr ((hoff x).2.1 h)
      · exact Or.inl ((hoff y).2.1 h))
    rw [h]
    simp [Matrix.one_apply, eq_comm]

omit [Finite K] [CharP K 2] in
theorem compl_setOf_not_offPQ :
    ({t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t})ᶜ = {t | OffPQ 1 2 t} := by
  ext t
  simp

omit [Finite K] [CharP K 2] in
theorem card_a2Levi :
    Nat.card (a2Levi K n) = Nat.card (StatedSp 1 K) * Nat.card (StatedSp (n + 1) K) := by
  have h12 := one_ne_two_fin (n := n)
  have hR : (shortBlock K h12).range ≤ suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t} :=
    by rintro _ ⟨A, rfl⟩; exact shortBlock_mem_suppGroup n A
  have hS : spCompl12 K n ≤ suppGroup ({t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t})ᶜ := by
    rw [compl_setOf_not_offPQ, ← spCompl12_eq_suppGroup]
  have hnorm :
      spCompl12 K n ≤ normalizer ((shortBlock K h12).range : Set (StatedSp (n + 3) K)) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := (commute_suppGroup_compl (hR hx) (hS hm)).eq
      have e : m * x * m⁻¹ = x := by rw [← hc, mul_inv_cancel_right]
      rw [e]
      exact hx
    · intro hx
      have hc := (commute_suppGroup_compl (hR hx) (hS hm)).eq
      have e : x = m * x * m⁻¹ := by
        calc x = m⁻¹ * (m * x * m⁻¹ * m) := by group
          _ = m⁻¹ * (m * (m * x * m⁻¹)) := by rw [hc]
          _ = m * x * m⁻¹ := by group
      rw [e]
      exact hx
  have hdisj : Disjoint (shortBlock K h12).range (spCompl12 K n) :=
    (disjoint_suppGroup_compl _).mono hR hS
  rw [a2Levi, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    ← Nat.card_congr (spCompl12Equiv K n).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (shortBlock_injective (K := K) h12)).toEquiv,
    Nat.card_congr (longBlockEquivOne K).toEquiv]

theorem ordCompl_card_perfectCore_a2 (hK : 4 ≤ Nat.card K) :
    ordCompl[2] (Nat.card (perfectCore (centralizer ({spRep (K := K) n .a2} :
      Set (StatedSp (n + 3) K))))) =
      (Nat.card K ^ 2 - 1) * ∏ j ∈ Finset.Icc 1 (n + 1), (Nat.card K ^ (2 * j) - 1) := by
  have h12 := one_ne_two_fin (n := n)
  have hML : a2Levi K n ≤ (leviHom h12 0 (one_ne_zero (α := K))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  have h1 := ordCompl_card_statedSp (K := K) 1
  simp only [Finset.Icc_self, Finset.prod_singleton, mul_one] at h1
  rw [spRep_a2_eq, (perfectCore_centralizer_a2 hK).1]
  change ordCompl[2] (Nat.card ↥(wRadical K (1 : Fin (n + 3)) 2 ⊔ a2Levi K n)) = _
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (hML.trans (range_leviHom_le_normalizer_wRadical h12 one_ne_zero))
      ((disjoint_wRadical_range_leviHom h12 one_ne_zero).mono_right hML),
    ordCompl_card_mul_of_isPGroup (isPGroup_wRadical h12), card_a2Levi, Nat.ordCompl_mul, h1,
    ordCompl_card_statedSp]

omit [Finite K] [CharP K 2] in
theorem prod_Icc_succ (m : ℕ) (g : ℕ → ℕ) :
    ∏ j ∈ Finset.Icc 1 (m + 1), g j = (∏ j ∈ Finset.Icc 1 m, g j) * g (m + 1) := by
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem ordCompl_card_perfectCore_injective (hK : 4 ≤ Nat.card K) {κ κ' : SpTwoCentral}
    (h : ordCompl[2] (Nat.card (perfectCore (centralizer ({spRep (K := K) n κ} :
      Set (StatedSp (n + 3) K))))) = ordCompl[2] (Nat.card (perfectCore (centralizer
        ({spRep (K := K) n κ'} : Set (StatedSp (n + 3) K)))))) : κ = κ' := by
  set q := Nat.card K with hq
  set P := ∏ j ∈ Finset.Icc 1 (n + 1), (q ^ (2 * j) - 1) with hP
  have hP1 : 1 ≤ P := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := not_two_dvd_prod (K := K) (n + 1)
    rw [← hq, ← hP, h0] at this
    exact this (dvd_zero 2)
  have hq2 : 3 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  have hqb : q ^ 2 - 1 < q ^ (2 * (n + 2)) - 1 := by
    have h1 : q ^ 2 < q ^ (2 * (n + 2)) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have eb1 : ordCompl[2] (Nat.card (perfectCore (centralizer ({spRep (K := K) n .b1} :
      Set (StatedSp (n + 3) K))))) = P * (q ^ (2 * (n + 2)) - 1) := by
    rw [ordCompl_card_perfectCore_b1 n hK, prod_Icc_succ]
  have ea2 := ordCompl_card_perfectCore_a2 n hK
  have ec2 := ordCompl_card_perfectCore_c2 n hK
  rw [← hq, ← hP] at ea2 ec2
  have hne1 : P * (q ^ (2 * (n + 2)) - 1) ≠ (q ^ 2 - 1) * P := by
    rw [mul_comm]
    intro h'
    have := Nat.eq_of_mul_eq_mul_right hP1 h'
    omega
  have hne2 : P * (q ^ (2 * (n + 2)) - 1) ≠ P := by
    intro h'
    have h'' : P * (q ^ (2 * (n + 2)) - 1) = P * 1 := by rw [mul_one]; exact h'
    have := Nat.eq_of_mul_eq_mul_left hP1 h''
    omega
  have hne3 : (q ^ 2 - 1) * P ≠ P := by
    intro h'
    have h'' : (q ^ 2 - 1) * P = 1 * P := by rw [one_mul]; exact h'
    have := Nat.eq_of_mul_eq_mul_right hP1 h''
    omega
  cases κ <;> cases κ' <;>
    first
    | rfl
    | (exfalso; simp only [eb1, ea2, ec2] at h;
        first | exact hne1 h | exact hne1 h.symm | exact hne2 h | exact hne2 h.symm |
          exact hne3 h | exact hne3 h.symm)

theorem card_perfectCore_centralizer_spRep_injective (hK : 4 ≤ Nat.card K)
    {κ κ' : SpTwoCentral}
    (h : Nat.card (perfectCore (centralizer ({spRep (K := K) n κ} :
      Set (StatedSp (n + 3) K)))) = Nat.card (perfectCore (centralizer
        ({spRep (K := K) n κ'} : Set (StatedSp (n + 3) K))))) : κ = κ' :=
  ordCompl_card_perfectCore_injective n hK (by rw [h])

omit [Field K] [Finite K] [CharP K 2] in
theorem map_centralizer_singleton_mulEquiv {X Y : Type*} [Group X] [Group Y] (f : X ≃* Y) (z : X) :
    (centralizer ({z} : Set X)).map f.toMonoidHom = centralizer ({f z} : Set Y) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg f h
    simpa using this
  · intro h
    apply f.injective
    simpa using h

omit [CharP K 2] in
theorem card_perfectCore_centralizer_eq_of_conj {X : Type*} [Group X] [Finite X]
    (e : X ≃* StatedSp (n + 3) K) {z c : X} {κ : SpTwoCentral}
    (hc : c * z * c⁻¹ = e.symm (spRep n κ)) :
    Nat.card (perfectCore (centralizer ({z} : Set X))) =
      Nat.card (perfectCore (centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K)))) := by
  set f : X ≃* StatedSp (n + 3) K := (MulAut.conj c).trans e with hf
  have hfz : f z = spRep n κ := by
    simp only [hf, MulEquiv.trans_apply, MulAut.conj_apply, hc, MulEquiv.apply_symm_apply]
  rw [← hfz, ← map_centralizer_singleton_mulEquiv f z, ← CFSG.Quasithin.map_perfectCore,
    Subgroup.card_map_of_injective f.injective]

theorem eq_of_card_perfectCore_centralizer_eq (hK : 4 ≤ Nat.card K) {X X' : Type*} [Group X]
    [Group X'] [Finite X] [Finite X'] (e : X ≃* StatedSp (n + 3) K)
    (e' : X' ≃* StatedSp (n + 3) K) {z c : X} {z' c' : X'} {κ κ' : SpTwoCentral}
    (hc : c * z * c⁻¹ = e.symm (spRep n κ)) (hc' : c' * z' * c'⁻¹ = e'.symm (spRep n κ'))
    (hcard : Nat.card (perfectCore (centralizer ({z} : Set X))) =
      Nat.card (perfectCore (centralizer ({z'} : Set X')))) : κ = κ' :=
  card_perfectCore_centralizer_spRep_injective n hK (by
    rw [← card_perfectCore_centralizer_eq_of_conj n e hc,
      ← card_perfectCore_centralizer_eq_of_conj n e' hc', hcard])
end Cores

end CFSG.SeitzReduction.SymplecticPilot
