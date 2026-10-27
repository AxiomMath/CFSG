module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossLin
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin (StatedGU)
open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open scoped Matrix
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU det_pow_card_add_one_of_mem_statedGU statedSU_le_statedGU)

namespace PSUThree

variable {L : Type} [Field L] [Finite L] {ℓ f n : ℕ}

theorem two_le (hL : Nat.card L = (ℓ ^ f) ^ 2) : 2 ≤ ℓ ^ f := by
  have h1 : 1 < Nat.card L := Finite.one_lt_card
  rw [hL] at h1
  by_contra h
  have h2 : ℓ ^ f ≤ 1 := by omega
  have h3 : (ℓ ^ f) ^ 2 ≤ 1 := by
    calc (ℓ ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := by norm_num
  omega

theorem mem_statedSU_iff (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (A : GL (Fin n) L) :
    A ∈ StatedSU n (ℓ ^ f) L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) L).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) L) = 1 :=
  Set.ext_iff.1 (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).1 A

theorem exp_pos {q : ℕ} (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    1 ≤ padicValInt 3 ((-(q : ℤ)) ^ orderOf (-(q : ZMod 3)) - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne0 : (-(q : ZMod 3)) ≠ 0 :=
    neg_ne_zero.2 (fun h => hq3 ((ZMod.natCast_eq_zero_iff q 3).1 h))
  have hepos : 0 < orderOf (-(q : ZMod 3)) := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, ZMod.pow_card_sub_one_eq_one hne0⟩
  have hdvd : ((3 : ℕ) : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod 3)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx : (-(q : ZMod 3)) ^ orderOf (-(q : ZMod 3)) = 1 := pow_orderOf_eq_one _
    push_cast
    exact sub_eq_zero.2 hx
  have hne : (-(q : ℤ)) ^ orderOf (-(q : ZMod 3)) - 1 ≠ 0 := by
    intro h
    have h1 : (-(q : ℤ)) ^ orderOf (-(q : ZMod 3)) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have h3 : q = 1 := (Nat.pow_eq_one.1 h2).resolve_right (by omega)
    omega
  rcases (padicValInt_dvd_iff (p := 3) 1 ((-(q : ℤ)) ^ orderOf (-(q : ZMod 3)) - 1)).1
      (by rw [pow_one]; exact hdvd) with h | h
  · exact absurd h hne
  · exact h

@[expose] noncomputable def detGU (n q : ℕ) (L : Type) [Field L] : ↥(StatedGU n q L) →* Lˣ :=
  Matrix.GeneralLinearGroup.det.comp (StatedGU n q L).subtype

theorem detGU_val {q : ℕ} (g : ↥(StatedGU n q L)) :
    ((detGU n q L g : Lˣ) : L) = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det := rfl

theorem subgroupOf_eq_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    (StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L) = (detGU n (ℓ ^ f) L).ker := by
  haveI := Fintype.ofFinite L
  obtain ⟨f', hq, h⟩ := exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    exact Units.ext (by rw [detGU_val]; exact ((mem_statedSU_iff hℓ hL hn _).1 hg).1)
  · intro hg
    exact mem_statedSU_of_mem_statedGU h hq g.2 (by rw [← detGU_val, hg]; rfl)

theorem not_three_dvd_index (hL : Nat.card L = (ℓ ^ f) ^ 2) (h1 : ¬ 3 ∣ ℓ ^ f + 1) :
    ¬ 3 ∣ (detGU n (ℓ ^ f) L).ker.index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite L
  obtain ⟨f', hq, h⟩ := exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)
  intro hdvd
  rw [Subgroup.index_ker] at hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (detGU n (ℓ ^ f) L).range) 3 hdvd
  obtain ⟨g, hg⟩ := y.2
  have hpow : (y : Lˣ) ^ (ℓ ^ f + 1) = 1 := by
    rw [← hg]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, detGU_val, Units.val_one]
    exact det_pow_card_add_one_of_mem_statedGU h hq g.2
  have h2 : orderOf (y : Lˣ) ∣ ℓ ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hy] at h2
  exact h1 h2

noncomputable def equivKer (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    ↥(StatedSU n (ℓ ^ f) L) ≃* ↥(detGU n (ℓ ^ f) L).ker :=
  (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU).symm.trans
    (MulEquiv.subgroupCongr (subgroupOf_eq_ker hℓ hL hn))

theorem threeLocal_of_not_dvd (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hq3 : ¬ 3 ∣ ℓ ^ f) (hn : 1 ≤ n) (h1 : ¬ 3 ∣ ℓ ^ f + 1) :
    ThreeLocal (StatedProj (StatedSU n (ℓ ^ f) L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  have hGU : ThreeLocal ↥(StatedGU n (ℓ ^ f) L) :=
    threeLocal_of_sigma (exp_pos (two_le hL) hq3) (fun P => sylow_GU (by decide) L hLc hq3 hn P)
  have hSU : ThreeLocal ↥(StatedSU n (ℓ ^ f) L) :=
    ThreeLocal.of_mulEquiv (equivKer hℓ hL hn)
      (ThreeLocal.of_normal_coprime_index _ (not_three_dvd_index hL h1) hGU)
  refine ThreeLocal.of_surjective_coprime_ker (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hSU
  rw [QuotientGroup.ker_mk', (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).2.2]
  exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))

theorem diagGL_mem {L : Type} [Field L] {n q : ℕ} (hq : q ≠ 0) (u : Fin n → Lˣ)
    (hu : ∀ i, (u i) ^ (q + 1) = 1) (hprod : ∏ i, u i = 1) :
    diagGL n u ∈ StatedSU n q L := by
  have hdet : ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    rw [det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
  have hunit : (((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [coe_diagGL, Matrix.diagonal_map (f := fun x : L => x ^ q) (zero_pow hq),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg Units.val (hu i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_succ]
    exact this
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hunit⟩

theorem permGL_mem {L : Type} [Field L] {n q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm (Fin n))
    (hσ : Equiv.Perm.sign σ = 1) : permGL n σ ∈ StatedSU n q L := by
  have hdet : ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    rw [det_permGL, hσ]; simp
  have hmap : ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q) =
      ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [coe_permGL]
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp [hq]
  have hunit : (((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hmap, coe_permGL, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one]
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hunit⟩

end PSUThree

theorem dichLieCross_PSU (hLie : LieOrderFormulasInput) : DichLieCrossAt .PSU := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  have hadm' := hadm
  obtain ⟨hℓ, -, hn3, -⟩ := hadm'
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by omega)
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq2 := PSUThree.two_le hL
  have hq0 : ℓ ^ f ≠ 0 := by omega
  by_cases h1 : 3 ∣ ℓ ^ f + 1
  swap
  · exact DichThreeLieAt.of_mulEquiv e
      (dichThreeLieAt_of_threeLocal (PSUThree.threeLocal_of_not_dvd hℓ hL hq3 (by omega) h1))
  have hdvd : ∀ d, d ∣ ℓ ^ f + 1 → d ∣ Nat.card L - 1 := by
    intro d hd
    rw [hL, show (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f) ^ 2 - 1 ^ 2 by norm_num, Nat.pow_two_sub_pow_two]
    exact hd.mul_right _
  have hdiag : ∀ {ζ : Lˣ} {d : ℕ}, orderOf ζ = d → d ∣ ℓ ^ f + 1 → ∀ (m : ℕ) (u : Fin m → Lˣ),
      (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 → diagGL m u ∈ StatedSU m (ℓ ^ f) L := by
    intro ζ d hζ hd m u hu hprod
    refine PSUThree.diagGL_mem hq0 u (fun i => ?_) hprod
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_mem_zpowers (hu i)).trans (hζ ▸ hd)
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_of_dvd_card_sub_one (hdvd 3 h1)
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | hn5
  · by_cases h9 : 9 ∣ ℓ ^ f + 1
    · obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd_card_sub_one (hdvd 9 h9)
      exact DichThreeLieAt.of_mulEquiv e (ProjLin.dichThreeLieAt_three hζ _ (hdiag hζ h9 3)
        (PSUThree.permGL_mem hq0 _ (by rw [sign_finRotate]; decide)))
    ·
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hN : Nat.card K * Nat.gcd 3 (ℓ ^ f + 1) =
          CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (ℓ ^ f) :=
        (hLie K .PSU 3 ℓ f hadm hmodel).2.1
      have hfac := OuterArith.psu_three_factorization hq2 h1 hN
      have hq1 : ℓ ^ f + 1 ≠ 0 := by omega
      have hv : padicValNat 3 (ℓ ^ f + 1) ≤ 1 := by
        by_contra hc
        push Not at hc
        exact h9 (by simpa using (padicValNat_dvd_iff_le hq1).2 hc)
      exact dichThreeLieAt_of_factorization_le_two (by omega)
  · refine DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_cycleWitness
      (ProjLin.cycleWitness_four hω _ (fun g hg => ?_) (hdiag hω h1 4)
        (PSUThree.permGL_mem hq0 _ ProjLin.sign_cyc4)))
    exact ((PSUThree.mem_statedSU_iff hℓ hL (by norm_num) g).1 hg).1
  · have hnp : 6 ≤ n ∨ ¬ 3 ∣ n := by omega
    obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag Nat.prime_three hn5 hnp hω
      (StatedSU n (ℓ ^ f) L) (fun u hu _ hprod => hdiag hω h1 n u hu hprod)
    exact DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_elemAbelian hE hEcard)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
