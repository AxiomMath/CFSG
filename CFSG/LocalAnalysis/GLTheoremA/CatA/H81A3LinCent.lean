module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinBlock
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G] [Finite G]

private theorem ne_bot_of_glaPComponent {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) :
    L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ :=
    by rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem dvd_card_quotient_center_of_not_commute {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) (hxp : x ^ p = 1) (hxy : x * y ≠ y * x) :
    p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk (⟨x, hx⟩ : L) with hc
  have hcp : c ^ p = 1 := by
    rw [hc, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : L) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, QuotientGroup.mk_one]
  have hc1 : c ≠ 1 := by
    intro h1
    rw [hc, QuotientGroup.eq_one_iff] at h1
    apply hxy
    have := Subgroup.mem_center_iff.1 h1 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  rw [← orderOf_eq_prime hcp hc1]
  exact orderOf_dvd_natCard c

theorem eq_of_glaPComponent_of_commutator_le {p : ℕ} {X J K : Subgroup G} (hJX : J ≤ X)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hXJ : ⁅X, X⁆ ≤ J) (hK : GLAPComponent p X K) :
    K = J := by
  have hKX : K ≤ X := hK.1
  have hperf : ⁅K, K⁆ = K := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hK
  have hKJ : K ≤ J := by
    rw [← hperf]
    exact (Subgroup.commutator_mono hKX hKX).trans hXJ
  have hsnJ : IsSubnormal K J := by
    have := CFSG.ClassicalInvolution.isSubnormal_inf hK.2.1 J
    rwa [inf_eq_left.2 hKJ, inf_eq_right.2 hJX] at this
  by_contra hne
  obtain ⟨M, hKM, hMJ, hMne, hMn, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_exists_normal hsnJ hne
  have hMtop : M.subgroupOf J ≠ ⊤ := by
    intro htop
    apply hMne
    refine le_antisymm hMJ fun x hx => ?_
    have : (⟨x, hx⟩ : J) ∈ M.subgroupOf J := htop ▸ Subgroup.mem_top _
    exact this
  have hMc := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq hMn hMtop
  have hKcomm : ⁅K, K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hb' : (⟨b, hKJ hb⟩ : J) ∈ M.subgroupOf J := hKM hb
    have := Subgroup.mem_center_iff.1 (hMc hb') ⟨a, hKJ ha⟩
    simpa using this
  exact ne_bot_of_glaPComponent hK (hperf ▸ hKcomm)

end Abstract

variable {F : Type} [Field F] {p : ℕ} {μ : F}

@[expose] def yd (μ : F) : Fin 4 → F := ![(μ ^ 3)⁻¹, μ, μ, μ]

@[expose] def zd (μ : F) : Fin 4 → F := ![μ, μ⁻¹, 1, 1]

@[expose] def td (μ : F) : Fin 4 → F := ![1, μ, μ⁻¹, 1]

@[expose] def t2d (μ : F) : Fin 4 → F := ![1, 1, μ, μ⁻¹]

theorem prod_yd (hμ : μ ≠ 0) : ∏ i, yd μ i = 1 := by
  rw [Fin.prod_univ_four]
  show (μ ^ 3)⁻¹ * μ * μ * μ = 1
  rw [mul_assoc, mul_assoc, ← pow_two, ← pow_succ', inv_mul_cancel₀ (pow_ne_zero 3 hμ)]

theorem prod_zd (hμ : μ ≠ 0) : ∏ i, zd μ i = 1 := by
  rw [Fin.prod_univ_four]
  simp [zd, hμ]

theorem prod_td (hμ : μ ≠ 0) : ∏ i, td μ i = 1 := by
  rw [Fin.prod_univ_four]
  simp [td, hμ]

theorem prod_t2d (hμ : μ ≠ 0) : ∏ i, t2d μ i = 1 := by
  rw [Fin.prod_univ_four]
  simp [t2d, hμ]

@[expose] noncomputable def ySL (hμ : μ ≠ 0) : SpecialLinearGroup (Fin 4) F :=
  diagSL (yd μ) (prod_yd hμ)

@[expose] noncomputable def zSL (hμ : μ ≠ 0) : SpecialLinearGroup (Fin 4) F :=
  diagSL (zd μ) (prod_zd hμ)

abbrev blockI : Finset (Fin 4) := {2, 3}

section Root

variable (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
include hp hp2 hμ

theorem ne_zero_of_root : μ ≠ 0 := hμ.ne_zero hp.ne_zero

theorem pow_two_ne_one : μ ^ 2 ≠ 1 := by
  intro h
  have := (hμ.pow_eq_one_iff_dvd 2).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem pow_four_ne_one : μ ^ 4 ≠ 1 := by
  intro h
  have h4 := (hμ.pow_eq_one_iff_dvd 4).1 h
  have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num at h4 ⊢; exact h4)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem ne_one_of_root : μ ≠ 1 := hμ.ne_one hp.one_lt

theorem yd_zero_ne (j : Fin 4) (hj : j ≠ 0) : yd μ 0 ≠ yd μ j := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hj' : yd μ j = μ := by
    fin_cases j
    · exact absurd rfl hj
    all_goals rfl
  rw [hj']
  intro h
  apply pow_four_ne_one hp hp2 hμ
  have h1 : (μ ^ 3)⁻¹ = μ := h
  calc μ ^ 4 = μ * μ ^ 3 := by ring
    _ = (μ ^ 3)⁻¹ * μ ^ 3 := by rw [h1]
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hμ0)

theorem yd_const (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) : yd μ i = yd μ j := by
  have key : ∀ k : Fin 4, k ≠ 0 → yd μ k = μ := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    all_goals rfl
  rw [key i hi, key j hj]

theorem diagSL_pow_eq_one {d : Fin 4 → F} {hd : ∏ i, d i = 1} (hdp : ∀ i, d i ^ p = 1) :
    diagSL d hd ^ p = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL, diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, one_apply_eq, Pi.pow_apply, hdp]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem yd_pow (i : Fin 4) : yd μ i ^ p = 1 := by
  have h3 : ((μ ^ 3)⁻¹) ^ p = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm 3 p, pow_mul, hμ.pow_eq_one, one_pow, inv_one]
  fin_cases i
  · exact h3
  all_goals exact hμ.pow_eq_one

theorem zd_pow (i : Fin 4) : zd μ i ^ p = 1 := by
  fin_cases i <;> simp [zd, hμ.pow_eq_one]

theorem ySL_pow : ySL (ne_zero_of_root hp hp2 hμ) ^ p = 1 :=
  diagSL_pow_eq_one hp hp2 hμ (yd_pow hp hp2 hμ)

theorem zSL_pow : zSL (ne_zero_of_root hp hp2 hμ) ^ p = 1 :=
  diagSL_pow_eq_one hp hp2 hμ (zd_pow hp hp2 hμ)

end Root

theorem diagSL_mul_transvection_apply {d : Fin 4 → F} (hd : ∏ i, d i = 1) {a b : Fin 4}
    (hab : a ≠ b) (c : F) (k l : Fin 4) :
    ((diagSL d hd * Matrix.SpecialLinearGroup.transvection hab c :
        SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) k l =
      d k * (1 + Matrix.single a b c : Matrix (Fin 4) (Fin 4) F) k l ∧
    ((Matrix.SpecialLinearGroup.transvection hab c * diagSL d hd :
        SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) k l =
      (1 + Matrix.single a b c : Matrix (Fin 4) (Fin 4) F) k l * d l := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
    Matrix.SpecialLinearGroup.transvection_coe, diagonal_mul, mul_diagonal]
  exact ⟨rfl, rfl⟩

theorem proj_diagSL_mul_transvection_ne {d : Fin 4 → F} (hd : ∏ i, d i = 1) {a b : Fin 4}
    (hab : a ≠ b) (hd_ab : d a ≠ d b) :
    proj 4 F (diagSL d hd) * proj 4 F (Matrix.SpecialLinearGroup.transvection hab 1) ≠
      proj 4 F (Matrix.SpecialLinearGroup.transvection hab 1) * proj 4 F (diagSL d hd) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  have hmem : (Matrix.SpecialLinearGroup.transvection hab 1 * diagSL d hd)⁻¹ *
      (diagSL d hd * Matrix.SpecialLinearGroup.transvection hab 1) ∈ scalars 4 F := by
    have h' : (QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection hab 1 * diagSL d hd) :
        projectiveSL 4 F) = QuotientGroup.mk (diagSL d hd *
          Matrix.SpecialLinearGroup.transvection hab 1) := h.symm
    exact (QuotientGroup.eq).1 h'
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hmem
  set u := Matrix.SpecialLinearGroup.transvection hab (1 : F)
  set x := diagSL d hd
  have heq : x * u = (u * x) * ((u * x)⁻¹ * (x * u)) := by group
  have hent : ∀ k l, ((x * u : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) k l =
      ((u * x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) k l * (c : F) := by
    intro k l
    conv_lhs => rw [heq]
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, mul_diagonal]
  have h1 := hent a a
  have h2 := hent a b
  rw [(diagSL_mul_transvection_apply hd hab 1 a a).1,
    (diagSL_mul_transvection_apply hd hab 1 a a).2] at h1
  rw [(diagSL_mul_transvection_apply hd hab 1 a b).1,
    (diagSL_mul_transvection_apply hd hab 1 a b).2] at h2
  have e1 : (1 + Matrix.single a b (1 : F) : Matrix (Fin 4) (Fin 4) F) a a = 1 := by
    rw [Matrix.add_apply, one_apply_eq, Matrix.single_apply, if_neg (fun h => hab h.2.symm),
      add_zero]
  have e2 : (1 + Matrix.single a b (1 : F) : Matrix (Fin 4) (Fin 4) F) a b = 1 := by
    rw [Matrix.add_apply, one_apply_ne hab, Matrix.single_apply, if_pos ⟨rfl, rfl⟩, zero_add]
  rw [e1, mul_one, one_mul] at h1
  rw [e2, mul_one, one_mul] at h2
  have hda : d a ≠ 0 := by
    intro h0
    have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h0
    rw [hd] at this
    exact one_ne_zero this
  have hc1 : (c : F) = 1 := by
    have h3 : d a * (c : F) = d a * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel₀ hda h3
  rw [hc1, mul_one] at h2
  exact hd_ab h2

section Cent

variable [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
include hp hp2 hμ

omit [Finite F] in
theorem proj_noTorsion : ∀ z ∈ (proj 4 F).ker, z ^ p = 1 → z = 1 := fun z hz hzp => by
  rw [ker_proj] at hz
  exact eq_one_of_mem_scalars_of_pow_eq_one hp hp2 hz hzp

omit hp hp2 hμ [Finite F] in
theorem ker_proj_le_center : (proj 4 F).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) F) := by
  rw [ker_proj]
  exact scalars_le_center 4 F

theorem centralizer_proj_ySL :
    Subgroup.centralizer ({proj 4 F (ySL (ne_zero_of_root hp hp2 hμ))} : Set (projectiveSL 4 F)) =
      (cent (yd μ) (prod_yd (ne_zero_of_root hp hp2 hμ))).map (proj 4 F) :=
  CFSG.StandardType.TableBUE.centralizer_map_eq_of_noTorsion (proj 4 F) (proj_surjective 4 F)
    ker_proj_le_center (proj_noTorsion hp hp2 hμ) (ySL_pow hp hp2 hμ)

theorem centralizer_proj_zSL :
    Subgroup.centralizer ({proj 4 F (zSL (ne_zero_of_root hp hp2 hμ))} : Set (projectiveSL 4 F)) =
      (cent (zd μ) (prod_zd (ne_zero_of_root hp hp2 hμ))).map (proj 4 F) :=
  CFSG.StandardType.TableBUE.centralizer_map_eq_of_noTorsion (proj 4 F) (proj_surjective 4 F)
    ker_proj_le_center (proj_noTorsion hp hp2 hμ) (zSL_pow hp hp2 hμ)

end Cent

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
