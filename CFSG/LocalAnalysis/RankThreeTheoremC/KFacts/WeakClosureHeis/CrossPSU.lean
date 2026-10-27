module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossTorus
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Open
open CFSG.Quasithin (StatedGU)
open scoped Matrix
open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU det_pow_card_add_one_of_mem_statedGU statedSU_le_statedGU)

section PSUCross

variable {L : Type} [Field L] [Finite L] {ℓ f n p : ℕ}

private theorem psuField (hL : Nat.card L = (ℓ ^ f) ^ 2) :
    ∃ f', ℓ ^ f = ringChar L ^ f' ∧ UnitaryFieldData (ringChar L) f' L := by
  haveI := Fintype.ofFinite L
  exact exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)

private theorem mem_statedSU_iff' (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (A : GL (Fin n) L) :
    A ∈ StatedSU n (ℓ ^ f) L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) L).map (· ^ ℓ ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) L) = 1 :=
  Set.ext_iff.1 (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).1 A

private theorem psu_exp_pos (hp : p.Prime) {q : ℕ} (hq2 : 2 ≤ q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne0 : (-(q : ZMod p)) ≠ 0 :=
    neg_ne_zero.2 (fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h))
  have hepos : 0 < orderOf (-(q : ZMod p)) := by
    rw [orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne0⟩
  have hdvd : (p : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx : (-(q : ZMod p)) ^ orderOf (-(q : ZMod p)) = 1 := pow_orderOf_eq_one _
    push_cast
    exact sub_eq_zero.2 hx
  have hne : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 ≠ 0 := by
    intro h
    have h1 : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have h3 : q = 1 := (Nat.pow_eq_one.1 h2).resolve_right (by omega)
    omega
  rcases (padicValInt_dvd_iff 1 ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)).1
      (by simpa using hdvd) with h | h
  · exact absurd h hne
  · exact h

private theorem psu_two_le (hL : Nat.card L = (ℓ ^ f) ^ 2) : 2 ≤ ℓ ^ f := by
  have h1 : 1 < Nat.card L := Finite.one_lt_card
  rw [hL] at h1
  by_contra h
  have h2 : ℓ ^ f ≤ 1 := by omega
  have h3 : (ℓ ^ f) ^ 2 ≤ 1 := by
    calc (ℓ ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := by norm_num
  omega

private theorem psu_dich_GU (hp : p.Prime) (h5 : 5 ≤ p) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) : SylowDichotomyAt ↥(StatedGU n (ℓ ^ f) L) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  exact SylowDichotomyAt.of_sylow_sigmaModel hp h5 (psu_exp_pos hp (psu_two_le hL) hpq)
    (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)

private noncomputable def psuDet (n q : ℕ) (L : Type) [Field L] : ↥(StatedGU n q L) →* Lˣ :=
  Matrix.GeneralLinearGroup.det.comp (StatedGU n q L).subtype

private theorem psuDet_val {q : ℕ} (g : ↥(StatedGU n q L)) :
    ((psuDet n q L g : Lˣ) : L) = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det := rfl

private theorem psu_subgroupOf_eq_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hn : 1 ≤ n) :
    (StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L) = (psuDet n (ℓ ^ f) L).ker := by
  obtain ⟨f', hq, h⟩ := psuField hL
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    exact Units.ext (by rw [psuDet_val]; exact ((mem_statedSU_iff' hℓ hL hn _).1 hg).1)
  · intro hg
    exact mem_statedSU_of_mem_statedGU h hq g.2 (by rw [← psuDet_val, hg]; rfl)

private theorem psu_not_dvd_index (hp : p.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) : ¬ p ∣ (psuDet n (ℓ ^ f) L).ker.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f', hq, h⟩ := psuField hL
  intro hdvd
  rw [Subgroup.index_ker] at hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (psuDet n (ℓ ^ f) L).range) p hdvd
  obtain ⟨g, hg⟩ := y.2
  have hpow : (y : Lˣ) ^ (ℓ ^ f + 1) = 1 := by
    rw [← hg]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, psuDet_val, Units.val_one]
    exact det_pow_card_add_one_of_mem_statedGU h hq g.2
  have h1 : orderOf (y : Lˣ) ∣ ℓ ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hy] at h1
  exact hpq1 h1

private noncomputable def psuEquivKer (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hn : 1 ≤ n) : ↥(StatedSU n (ℓ ^ f) L) ≃* ↥(psuDet n (ℓ ^ f) L).ker :=
  (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU).symm.trans
    (MulEquiv.subgroupCongr (psu_subgroupOf_eq_ker hℓ hL hn))

private noncomputable def psuProj (n q : ℕ) (L : Type) [Field L] :
    ↥(StatedSU n q L) →* StatedProj (StatedSU n q L) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))

private theorem psuProj_surjective (n q : ℕ) :
    Function.Surjective (psuProj n q L) := QuotientGroup.mk'_surjective _

private theorem psuProj_ker (n q : ℕ) :
    (psuProj n q L).ker = (StatedScalars (Fin n) L).subgroupOf (StatedSU n q L) :=
  QuotientGroup.ker_mk' _

private theorem psu_not_dvd_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) : ¬ p ∣ Nat.card (psuProj n (ℓ ^ f) L).ker := by
  rw [psuProj_ker, (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).2.2]
  exact fun h => hpq1 (h.trans (Nat.gcd_dvd_right _ _))

private theorem psu_dich_SU_of_not_dvd (hp : p.Prime) (h5 : 5 ≤ p) (hℓ : ℓ.Prime)
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) (hpq1 : ¬ p ∣ ℓ ^ f + 1) :
    SylowDichotomyAt ↥(StatedSU n (ℓ ^ f) L) p :=
  SylowDichotomyAt.of_mulEquiv hp (psuEquivKer hℓ hL hn)
    (SylowDichotomyAt.of_normal_coprime_index hp _ (psu_not_dvd_index hp hL hpq1)
      (psu_dich_GU hp h5 hL hpq hn))

private theorem psu_dich_PSU_of_not_dvd (hp : p.Prime) (h5 : 5 ≤ p) (hℓ : ℓ.Prime)
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) (hpq1 : ¬ p ∣ ℓ ^ f + 1) :
    SylowDichotomyAt (StatedProj (StatedSU n (ℓ ^ f) L)) p :=
  SylowDichotomyAt.of_surjective_coprime_ker hp (psuProj n (ℓ ^ f) L)
    (psuProj_surjective _ _) (psu_not_dvd_ker hℓ hL hn hpq1)
    (psu_dich_SU_of_not_dvd hp h5 hℓ hL hpq hn hpq1)

private theorem psu_exists_zeta (hp : p.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq1 : p ∣ ℓ ^ f + 1) : ∃ ζ : Lˣ, orderOf ζ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine exists_prime_orderOf_dvd_card' p ?_
  rw [Nat.card_units, hL]
  refine hpq1.trans ⟨ℓ ^ f - 1, ?_⟩
  have h2 := psu_two_le hL
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by omega⟩
  rw [hm]
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel]
  ring

private theorem psu_zeta_pow (hpq1 : p ∣ ℓ ^ f + 1) {ζ : Lˣ} (hζ : orderOf ζ = p) :
    ∀ x ∈ Subgroup.zpowers ζ, x ^ (ℓ ^ f + 1) = 1 := fun x hx => by
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact (orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]; exact hpq1)

private theorem diagGL_mem_statedSU {q : ℕ} (hq : q ≠ 0) (u : Fin n → Lˣ)
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

private theorem permGL_mem_statedSU {q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm (Fin n))
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

private theorem psu_dich_PSU_of_dvd (hp : p.Prime) (h5 : 5 ≤ p) (hL : Nat.card L = (ℓ ^ f) ^ 2)
    (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n) (hpq1 : p ∣ ℓ ^ f + 1) :
    SylowDichotomyAt (StatedProj (StatedSU n (ℓ ^ f) L)) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := by have := psu_two_le hL; omega
  by_cases hnp5 : n < 5
  ·
    have hnp : n < p := by omega
    have he : orderOf (-((ℓ ^ f : ℕ) : ZMod p)) = 1 := by
      have h0 : (((ℓ ^ f + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq1
      have h1 : ((ℓ ^ f : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_add, Nat.cast_one] at h0
        exact eq_neg_of_add_eq_zero_left h0
      have h2 : -((ℓ ^ f : ℕ) : ZMod p) = 1 := neg_eq_iff_eq_neg.2 h1
      rw [h2, orderOf_one]
    haveI := Fintype.ofFinite L
    have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
    have hGU : ∀ P : Sylow p ↥(StatedGU n (ℓ ^ f) L),
        IsMulCommutative (P : Subgroup ↥(StatedGU n (ℓ ^ f) L)) :=
      sylow_isMulCommutative_of_sigmaModel_of_lt hp
        (e := orderOf (-((ℓ ^ f : ℕ) : ZMod p))) (by rw [he, Nat.div_one]; exact hnp)
        (fun P => sylow_GU (hp.odd_of_ne_two (by omega)) L hLc hpq hn P)
    have hSub := sylow_comm_of_subgroup
      ((StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L)) hGU
    have hSU := sylow_comm_of_surjective
      (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (statedSU_le_statedGU (L := L) (q := ℓ ^ f) (n := n))).surjective
      hSub
    exact SylowDichotomyAt.of_sylow_comm
      (sylow_comm_of_surjective (psuProj n (ℓ ^ f) L) (psuProj_surjective _ _) hSU)
  · push Not at hnp5
    obtain ⟨ζ, hζ⟩ := psu_exists_zeta hp hL hpq1
    have hzp := psu_zeta_pow hpq1 hζ
    have hdiag : ∀ u : Fin n → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 →
        diagGL n u ∈ StatedSU n (ℓ ^ f) L := fun u hu hprod =>
      diagGL_mem_statedSU hq0 u (fun i => hzp _ (hu i)) hprod
    by_cases hnp : 6 ≤ n ∨ ¬ p ∣ n
    · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_four_projDiag hp hnp5 hnp hζ
        (StatedSU n (ℓ ^ f) L) (fun u hu _ hprod => hdiag u hu hprod)
      exact SylowDichotomyAt.of_elemAbelian hp hE hEc le_rfl
    · push Not at hnp
      obtain ⟨hn6, hpn⟩ := hnp
      have hn5 : n = 5 := by omega
      subst hn5
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
      subst hp5
      have hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ StatedSU 5 (ℓ ^ f) L := by
        apply hdiag
        · intro i
          fin_cases i
          · exact Subgroup.mem_zpowers ζ
          · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
          · exact Subgroup.one_mem _
          · exact Subgroup.one_mem _
          · exact Subgroup.one_mem _
        · simp [Fin.prod_univ_five]
      have hc : permGL 5 (finRotate 5) ∈ StatedSU 5 (ℓ ^ f) L :=
        permGL_mem_statedSU hq0 _ (by rw [sign_finRotate]; decide)
      obtain ⟨U, hU, hUd⟩ := exists_not_cyclic_derived_projFive hζ (StatedSU 5 (ℓ ^ f) L) hd hc
      exact SylowDichotomyAt.of_not_cyclic_derived hU hUd

end PSUCross

theorem sdLieCross_PSU : SDLieCrossAt .PSU := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨hℓ, hf, hn3, -⟩ := hadm
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by omega)
  have hpq : ¬ p ∣ ℓ ^ f :=
    fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  refine SylowDichotomyAt.of_mulEquiv hp e ?_
  by_cases hpq1 : p ∣ ℓ ^ f + 1
  · exact psu_dich_PSU_of_dvd hp h5 hL hpq (by omega) hpq1
  · exact psu_dich_PSU_of_not_dvd hp h5 hℓ hL hpq (by omega) hpq1

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
