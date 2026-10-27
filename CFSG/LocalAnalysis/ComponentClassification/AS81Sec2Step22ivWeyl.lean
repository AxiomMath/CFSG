module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag Matrix CFSG.LieType.Chevalley

namespace Sec2Weyl

variable {k : Type} [Field k]

@[expose] def weylSL2 : SL2 k :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem coe_weylSL2 : ((weylSL2 : SL2 k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] :=
  rfl

theorem torusSL2_inv {t : k} (ht : t ≠ 0) : (torusSL2 ht)⁻¹ = torusSL2 (inv_ne_zero ht) := by
  rw [inv_eq_iff_mul_eq_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_torusSL2, coe_torusSL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

theorem weylSL2_mul_torusSL2 {t : k} (ht : t ≠ 0) :
    weylSL2 * torusSL2 ht = torusSL2 (inv_ne_zero ht) * weylSL2 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weylSL2,
    coe_torusSL2, coe_torusSL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem torusSL2_pow_three {t : k} (ht : t ≠ 0) (h3 : t ^ 3 = 1) : torusSL2 ht ^ 3 = 1 := by
  have h3' : t⁻¹ ^ 3 = 1 := by rw [inv_pow, h3, inv_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_torusSL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h3, h3', pow_succ, Fin.sum_univ_two]

theorem leviOne_torus_mul_unipU {t : k} (ht : t ≠ 0) (a b c : k) :
    leviOne k (torusSL2 ht) * unipU k a b c =
      unipU k (a * t⁻¹) (t * b * t) (c * t) * leviOne k (torusSL2 ht) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_leviOne, coe_unipU,
    coe_unipU, coe_torusSL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem leviTwo_torus_mul_unipU {t : k} (ht : t ≠ 0) (a b c : k) :
    leviTwo k (torusSL2 ht) * unipU k a b c =
      unipU k (t * a * t) (b * t⁻¹) (t * c) * leviTwo k (torusSL2 ht) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_leviTwo, coe_unipU,
    coe_unipU, coe_torusSL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem proj_conj_eq {g : SpecialLinearGroup (Fin 3) k} {a b c a' b' c' : k}
    (h : g * unipU k a b c = unipU k a' b' c' * g) :
    proj 3 k g * proj 3 k (unipU k a b c) * (proj 3 k g)⁻¹ = proj 3 k (unipU k a' b' c') := by
  rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 h]

theorem leviOne_torus_conj_mem_zero {t : k} (ht : t ≠ 0) {x : projectiveSL 3 k}
    (hx : x ∈ projRad k 0) :
    proj 3 k (leviOne k (torusSL2 ht)) * x * (proj 3 k (leviOne k (torusSL2 ht)))⁻¹ ∈
      projRad k 0 := by
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  rw [proj_conj_eq (leviOne_torus_mul_unipU ht a 0 c), mul_zero, zero_mul]
  exact mem_projRad_zero.2 ⟨_, _, rfl⟩

theorem leviOne_torus_conj_mem_one {t : k} (ht : t ≠ 0) {x : projectiveSL 3 k}
    (hx : x ∈ projRad k 1) :
    proj 3 k (leviOne k (torusSL2 ht)) * x * (proj 3 k (leviOne k (torusSL2 ht)))⁻¹ ∈
      projRad k 1 := by
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
  rw [proj_conj_eq (leviOne_torus_mul_unipU ht 0 b c), zero_mul]
  exact mem_projRad_one.2 ⟨_, _, rfl⟩

theorem leviTwo_torus_conj_mem_zero {t : k} (ht : t ≠ 0) {x : projectiveSL 3 k}
    (hx : x ∈ projRad k 0) :
    proj 3 k (leviTwo k (torusSL2 ht)) * x * (proj 3 k (leviTwo k (torusSL2 ht)))⁻¹ ∈
      projRad k 0 := by
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  rw [proj_conj_eq (leviTwo_torus_mul_unipU ht a 0 c), zero_mul]
  exact mem_projRad_zero.2 ⟨_, _, rfl⟩

theorem leviTwo_torus_conj_mem_one {t : k} (ht : t ≠ 0) {x : projectiveSL 3 k}
    (hx : x ∈ projRad k 1) :
    proj 3 k (leviTwo k (torusSL2 ht)) * x * (proj 3 k (leviTwo k (torusSL2 ht)))⁻¹ ∈
      projRad k 1 := by
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
  rw [proj_conj_eq (leviTwo_torus_mul_unipU ht 0 b c), mul_zero, zero_mul]
  exact mem_projRad_one.2 ⟨_, _, rfl⟩

theorem levi_torus_conj_mem (i j : Fin 2) {t : k} (ht : t ≠ 0) {x : projectiveSL 3 k}
    (hx : x ∈ projRad k j) :
    proj 3 k (levi k i (torusSL2 ht)) * x * (proj 3 k (levi k i (torusSL2 ht)))⁻¹ ∈
      projRad k j := by
  fin_cases i <;> fin_cases j
  · exact leviOne_torus_conj_mem_zero ht hx
  · exact leviOne_torus_conj_mem_one ht hx
  · exact leviTwo_torus_conj_mem_zero ht hx
  · exact leviTwo_torus_conj_mem_one ht hx

theorem levi_torus_mem_normalizer (i j : Fin 2) {t : k} (ht : t ≠ 0) :
    proj 3 k (levi k i (torusSL2 ht)) ∈ normalizer (projRad k j : Set (projectiveSL 3 k)) := by
  refine mem_normalizer_of_conj_mem (fun x hx => levi_torus_conj_mem i j ht hx) fun x hx => ?_
  have h := levi_torus_conj_mem i j (inv_ne_zero ht) hx
  rwa [← torusSL2_inv ht, map_inv, map_inv, inv_inv] at h

theorem levi_weyl_conj_torus (i : Fin 2) {t : k} (ht : t ≠ 0) :
    proj 3 k (levi k i weylSL2) * proj 3 k (levi k i (torusSL2 ht)) *
        (proj 3 k (levi k i weylSL2))⁻¹ = proj 3 k (levi k i (torusSL2 (inv_ne_zero ht))) := by
  rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
    weylSL2_mul_torusSL2 ht, mul_inv_cancel_right]

theorem levi_weyl_mem_normalizer (i : Fin 2) :
    proj 3 k (levi k i weylSL2) ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
  fin_cases i
  · exact leviOne_mem_normalizer _
  · exact leviTwo_mem_normalizer _

theorem levi_weyl_conj_projCenterW (i : Fin 2) {x : projectiveSL 3 k} (hx : x ∈ projCenterW k)
    (hmem : proj 3 k (levi k i weylSL2) * x * (proj 3 k (levi k i weylSL2))⁻¹ ∈
      projCenterW k) : x = 1 := by
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hx
  fin_cases i
  · change proj 3 k (leviOne k weylSL2) * _ * (proj 3 k (leviOne k weylSL2))⁻¹ ∈ _ at hmem
    rw [proj_conj_eq (leviOne_mul_unipU weylSL2 0 c)] at hmem
    obtain ⟨c', hc'⟩ := mem_projCenterW.1 hmem
    obtain ⟨h0, -, -⟩ := unipU_eq_of_proj_eq hc'
    simp only [coe_weylSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h0
    have hc : c = 0 := by linear_combination -h0
    rw [hc, unipU_zero, map_one]
  · change proj 3 k (leviTwo k weylSL2) * _ * (proj 3 k (leviTwo k weylSL2))⁻¹ ∈ _ at hmem
    rw [proj_conj_eq (leviTwo_mul_unipU weylSL2 0 c)] at hmem
    obtain ⟨c', hc'⟩ := mem_projCenterW.1 hmem
    obtain ⟨-, h1, -⟩ := unipU_eq_of_proj_eq hc'
    simp only [coe_weylSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h1
    have hc : c = 0 := by linear_combination h1
    rw [hc, unipU_zero, map_one]

end Sec2Weyl

section Component

open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

theorem exists_torus_weyl_of_card_sixteen {A H K T : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥A) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) (hTsyl : IsSylowOf 2 T A) (hHT : H ≤ T) (hKT : K ≤ T)
    (hH : IsElemAbelian 2 H) (hK : IsElemAbelian 2 K) (hH16 : Nat.card H = 16)
    (hK16 : Nat.card K = 16) :
    ∃ y ∈ A, ∃ a ∈ A, y ∈ normalizer (H : Set G) ∧ y ∈ normalizer (K : Set G) ∧
      (∀ w ∈ centerIn T, y * w * y⁻¹ = w → w = 1) ∧ y * y * y ∈ (center ↥A).map A.subtype ∧
      a ∈ normalizer (H : Set G) ∧ a * y * a⁻¹ ∈ normalizer (K : Set G) ∧
      ∀ w ∈ centerIn T, a * w * a⁻¹ ∈ centerIn T → w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  obtain ⟨φ, hφs, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hrad : ∀ X : Subgroup G, X ≤ T → IsElemAbelian 2 X → Nat.card X = 16 →
      IsPGroup 2 (X.subgroupOf A) ∧ ∃ i : Fin 2, (X.subgroupOf A).map φ = projRad c.k i := by
    intro X hXT hX hX16
    have hX₀T : X.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hXT (mem_subgroupOf.mp hx))
    have hX₀ : IsPGroup 2 (X.subgroupOf A) := hT₀2.to_le hX₀T
    refine ⟨hX₀, ?_⟩
    have hX₀2 : ∀ x ∈ (X.subgroupOf A).map φ, x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by
        simpa using hX.2 _ (mem_subgroupOf.mp hx)), map_one]
    have hX₀16 : Nat.card ((X.subgroupOf A).map φ) = 16 := by
      rw [card_map_of_isPGroup φ hkerodd hX₀, ← hX16]
      exact Nat.card_congr (subgroupOfEquivOfLe (hXT.trans hTA)).toEquiv
    have hX₀U : (X.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hX₀T
    rcases eq_projRad_of_le_projUnip c.card_k hX₀U hX₀2 hX₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨hH₀, i, hi⟩ := hrad H hHT hH hH16
  obtain ⟨hK₀, j, hj⟩ := hrad K hKT hK hK16
  have hsubodd : Odd (Nat.card A.subtype.ker) := by
    rw [ker_subtype, card_bot]
    exact odd_one
  have hW : (centerIn (T₀ : Subgroup ↥A)).map A.subtype = centerIn T := by
    rw [map_centerIn_eq A.subtype hsubodd hT₀2, hT₀]
  have hW₀ : (centerIn T).subgroupOf A = centerIn (T₀ : Subgroup ↥A) := by
    rw [← hW]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hW₀2 : IsPGroup 2 ((centerIn T).subgroupOf A) := hW₀ ▸ hT₀2.to_le inf_le_left
  have hWA : centerIn T ≤ A := (inf_le_left : centerIn T ≤ T).trans hTA
  have hWφ : ((centerIn T).subgroupOf A).map φ = projCenterW c.k := by
    rw [hW₀, map_centerIn_eq φ hkerodd hT₀2, hφT, ← center_projUnip]
    ext x
    constructor
    · rintro ⟨hxU, hxC⟩
      refine ⟨⟨x, hxU⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hxC y y.2
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : projectiveSL 3 c.k) ∈ centralizer ((projUnip c.k : Subgroup _) : Set _)
      rw [mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card c.card_k
  obtain ⟨n, hn⟩ := hφs (proj 3 c.k (levi c.k i (torusSL2 ht0)))
  obtain ⟨m, hm⟩ := hφs (proj 3 c.k (levi c.k i Sec2Weyl.weylSL2))
  have hHA : H ≤ A := hHT.trans hTA
  have hKA : K ≤ A := hKT.trans hTA
  have hnH : n ∈ normalizer ((H.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hH₀
      (hi ▸ hn ▸ Sec2Weyl.levi_torus_mem_normalizer i i ht0)
  have hnK : n ∈ normalizer ((K.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hK₀
      (hj ▸ hn ▸ Sec2Weyl.levi_torus_mem_normalizer i j ht0)
  have hmH : m ∈ normalizer ((H.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hH₀ (hi ▸ hm ▸ Sec2Weyl.levi_weyl_mem_normalizer i)
  have hmnK : m * n * m⁻¹ ∈ normalizer ((K.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
    refine mem_normalizer_of_map φ hkerZ hkerodd hK₀ ?_
    rw [map_mul, map_mul, map_inv, hm, hn, Sec2Weyl.levi_weyl_conj_torus i ht0, hj]
    exact Sec2Weyl.levi_torus_mem_normalizer i j (inv_ne_zero ht0)
  refine ⟨n, n.2, m, m.2, mem_normalizer_of_mem_normalizer_subgroupOf hHA hnH,
    mem_normalizer_of_mem_normalizer_subgroupOf hKA hnK, fun w hw hfix => ?_, ?_,
    mem_normalizer_of_mem_normalizer_subgroupOf hHA hmH,
    mem_normalizer_of_mem_normalizer_subgroupOf hKA hmnK, fun w hw hmem => ?_⟩
  ·
    set w₀ : ↥A := ⟨w, hWA hw⟩
    have hw₀ : w₀ ∈ (centerIn T).subgroupOf A := hw
    have hfix₀ : n * w₀ * n⁻¹ = w₀ := Subtype.ext hfix
    have hφw₀ : φ w₀ ∈ projCenterW c.k := by rw [← hWφ]; exact ⟨w₀, hw₀, rfl⟩
    have hφw : φ w₀ = 1 := by
      obtain ⟨c', hc'⟩ := mem_projCenterW.1 hφw₀
      have h1 := congrArg φ hfix₀
      rw [map_mul, map_mul, map_inv, hn, ← hc', levi_torus_conj] at h1
      obtain ⟨-, -, hc⟩ := unipU_eq_of_proj_eq h1
      have hc0 : c' = 0 := by
        have h2 : (t - 1) * c' = 0 := by linear_combination hc
        exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ht1)
      rw [← hc', hc0, unipU_zero, map_one]
    have := eq_of_map_eq_of_isPGroup φ hkerodd hW₀2 hw₀ (one_mem _) (by rw [hφw, map_one])
    exact congrArg Subtype.val this
  ·
    have h3 : φ (n * n * n) = 1 := by
      rw [map_mul, map_mul, hn, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← pow_three',
        Sec2Weyl.torusSL2_pow_three ht0 (pow_three_eq_one_of_card c.card_k ht0), map_one,
        map_one]
    have hmem : n * n * n ∈ center ↥A := by rw [← hφk]; exact h3
    exact ⟨n * n * n, hmem, rfl⟩
  ·
    set w₀ : ↥A := ⟨w, hWA hw⟩
    have hw₀ : w₀ ∈ (centerIn T).subgroupOf A := hw
    have hmw₀ : m * w₀ * m⁻¹ ∈ (centerIn T).subgroupOf A := hmem
    have hφw₀ : φ w₀ ∈ projCenterW c.k := by rw [← hWφ]; exact ⟨w₀, hw₀, rfl⟩
    have hφw : φ w₀ = 1 := by
      refine Sec2Weyl.levi_weyl_conj_projCenterW i hφw₀ ?_
      rw [← hm, ← map_inv, ← map_mul, ← map_mul, ← hWφ]
      exact ⟨_, hmw₀, rfl⟩
    have := eq_of_map_eq_of_isPGroup φ hkerodd hW₀2 hw₀ (one_mem _) (by rw [hφw, map_one])
    exact congrArg Subtype.val this

end Component

section Frame

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

theorem exists_torus_weyl_frame (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ y ∈ A, ∃ a ∈ A, y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      y ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) ∧
      (∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1) ∧ y * y * y ∈ (center ↥A).map A.subtype ∧
      a ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      a * y * a⁻¹ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) ∧
      ∀ w ∈ E ⊓ F ⊓ A, a * w * a⁻¹ ∈ E ⊓ F ⊓ A → w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨-, hDA, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hF16 : Nat.card (F ⊓ A : Subgroup G) = 16 := card_inf_left hF.symm hodd
  obtain ⟨y, hyA, a, haA, hyH, hyK, hyfix, hy3, haH, hayK, hafix⟩ :=
    exists_torus_weyl_of_card_sixteen hF.base.hyp.standard.1 hL hodd hDA
      (inf_le_inf_right A le_sup_left) (inf_le_inf_right A le_sup_right)
      (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
      (AS76b.IsElemAbelian.mono hF.elemF inf_le_left) (card_inf_left hF hodd) hF16
  have hW := centerIn_inf_eq hF
  exact ⟨y, hyA, a, haA, hyH, hyK, fun w hw => hyfix w (hW ▸ hw), hy3, haH, hayK,
    fun w hw hmem => hafix w (hW ▸ hw) (hW ▸ hmem)⟩

end Frame

end CFSG.ComponentClassification.AS81
