module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBlocksGen
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSL4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub

theorem orth8_orthogonal_zero_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {m : ℕ} (hm : m = 0)
    {y : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm F b c)))}
    (hy : y ^ p = 1) : y = 1 := by
  haveI : Finite (((Fin m ⊕ Fin m → F) × (Fin 2 → F)) ≃ₗ[F]
      ((Fin m ⊕ Fin m → F) × (Fin 2 → F))) := finite_orthLinearEquiv
  subst hm
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hy1
  have hord : orderOf y = p := orderOf_eq_prime hy hy1
  have hdvd : p ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadTail 0 (minusTailForm F b c))) := hord ▸ orderOf_dvd_natCard y
  rw [orthMinus_card_orthogonalGroup_tail_zero hirr] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | h2
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    omega
  · exact hpq (h2.trans (orthMinus_add_one_dvd_sq_sub_one _))

theorem orth8_mem_orthogonalGroup_zero_of_mem_commutator {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F}
    {x : ((Fin 0 ⊕ Fin 0 → F) × (Fin 2 → F)) ≃ₗ[F] ((Fin 0 ⊕ Fin 0 → F) × (Fin 2 → F))}
    (hx : x ∈ orthResDer F b c 0) :
    x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm F b c)) := by
  have hle : orthResDer F b c 0 ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm F b c)) := by
    refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact hle hx

theorem orth8_orthResDer_zero_mul_comm {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (x y : ↥(orthResDer F b c 0)) : x * y = y * x := by
  set e := orthMinusCommutatorCongr (minusTailZeroIsometry (b := b) (c := c))
  refine e.injective ?_
  rw [map_mul, map_mul]
  exact Subtype.ext (commute_of_mem_commutator_minusTailForm hirr (e x).2 (e y).2)

theorem orth8_orthResDer_eq_zero_facts {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {m : ℕ} (hm : m = 0) :
    (∀ x ∈ orthResDer F b c m, ∀ x' ∈ orthResDer F b c m, x * x' = x' * x) ∧
      ∀ x ∈ orthResDer F b c m, x ^ p = 1 → x = 1 := by
  subst hm
  refine ⟨fun x hx x' hx' => ?_, fun x hx hxp => ?_⟩
  · exact congrArg Subtype.val (orth8_orthResDer_zero_mul_comm hirr ⟨x, hx⟩ ⟨x', hx'⟩)
  · have hxO := orth8_mem_orthogonalGroup_zero_of_mem_commutator hx
    have hy : (⟨x, hxO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadTail 0 (minusTailForm F b c)))) = 1 := by
      apply orth8_orthogonal_zero_eq_one hirr hp hp5 hpq rfl
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hxp
    exact congrArg Subtype.val hy

theorem orth8_perfect_slRange {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) (k : ℕ) :
    ⁅slRange F k, slRange F k⁆ = slRange F k :=
  fong_commutator_self_eq_of_top _
    (fong_commutator_top_of_mulEquiv (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) k)
      (fong_commutator_specialLinear h4 k))

theorem orth8_levi_sl3 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : CFSG.Open.pRank p
      (⊤ : Subgroup ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) ≤ 1)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    (ht : d (Fin.last s) = 3)
    {z : ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))} (hz : orderOf z = p)
    (hzP : z ∈ orthParab 3 (minusTailForm F b c) d) :
    LeviSurj p (orthParab 3 (minusTailForm F b c) d) z
      (Matrix.SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  haveI : Finite (((Fin 3 ⊕ Fin 3 → F) × (Fin 2 → F)) ≃ₗ[F]
      ((Fin 3 ⊕ Fin 3 → F) × (Fin 2 → F))) := finite_orthLinearEquiv
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))) := inferInstance
  have hp2 : p ≠ 2 := by omega
  have hnd : ¬ p ∣ Nat.card F - 1 := fong_not_dvd_card_sub_one hpq
  have h0 : 3 - d (Fin.last s) = 0 := by omega
  have hβ : IsPGroup 2 (orthLeviHom b c hd).ker := isPGroup_ker_orthLeviHom hd
  have hS : Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) ≤ (orthLeviHom b c hd).range :=
    pi_orthLeviBlock_le_range hd (le_refl 3)
      (commutator_orthogonalGroup_quadTail_minus (le_refl 3) hirr)
  have hcomm : ⁅(orthLeviHom b c hd).range, (orthLeviHom b c hd).range⁆ ≤
      Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) :=
    commutator_range_orthLeviHom_le hd
  have hperf : ∀ j, ⁅orthLeviBlock F 3 d b c j, orthLeviBlock F 3 d b c j⁆ =
      orthLeviBlock F 3 d b c j ∨
      ((∀ x ∈ orthLeviBlock F 3 d b c j, ∀ x' ∈ orthLeviBlock F 3 d b c j, x * x' = x' * x) ∧
        ∀ x ∈ orthLeviBlock F 3 d b c j, x ^ p = 1 → x = 1) := by
    rintro (l | u)
    · exact Or.inl (orth8_perfect_slRange h4 (d l.succ - d l.castSucc))
    · exact Or.inr (orth8_orthResDer_eq_zero_facts hirr hp hp5 hpq h0)
  have hpR : ∀ x ∈ (orthLeviHom b c hd).range, x ^ p = 1 →
      x ∈ Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) := by
    rintro x ⟨g, rfl⟩ hx
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    rcases j with l | u
    · have hxa : orthLeviHom b c hd g (Sum.inl l) ^ p = 1 := by
        have h := congrFun hx (Sum.inl l)
        rw [Pi.pow_apply, Pi.one_apply] at h
        exact h
      change orthLeviHom b c hd g (Sum.inl l) ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) F →*
          Matrix.GeneralLinearGroup (Fin (d l.succ - d l.castSucc)) F).range
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.det_eq_one_of_pow_eq_one hp hnd hxa
    · have hxa : orthResHom (minusTailForm F b c) hd g ^ p = 1 := by
        have h := congrFun hx (Sum.inr u)
        rw [Pi.pow_apply, Pi.one_apply] at h
        exact h
      have hy : (⟨orthResHom (minusTailForm F b c) hd g, orthResHom_mem_orthogonalGroup hd g⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup
            (quadTail (3 - d (Fin.last s)) (minusTailForm F b c)))) = 1 := by
        apply orth8_orthogonal_zero_eq_one hirr hp hp5 hpq h0
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hxa
      have hres : orthResHom (minusTailForm F b c) hd g = 1 := congrArg Subtype.val hy
      change orthResHom (minusTailForm F b c) hd g ∈ orthResDer F b c (3 - d (Fin.last s))
      rw [hres]
      exact Subgroup.one_mem _
  have hblk : ∀ j, (∃ u ∈ orthLeviBlock F 3 d b c j, orderOf u = p) →
      CFSG.Open.IsQuasisimple ↥(orthLeviBlock F 3 d b c j) ∧
        ¬ p ∣ Nat.card (Subgroup.center ↥(orthLeviBlock F 3 d b c j)) := by
    rintro (l | w) ⟨v, hv, hord⟩
    · have hv1 : v ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one v
      have hv2 : v ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hord
        omega
      obtain ⟨hq, hz', -, -⟩ := orthMinus_gl_block_data hF hp hp5 hpq hv1 hv2
      exact ⟨hq, hz'⟩
    · exfalso
      have hv1 : v ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one v
      have hv0 : v = 1 := (orth8_orthResDer_eq_zero_facts hirr hp hp5 hpq h0).2 v hv hv1
      rw [hv0, orderOf_one] at hord
      omega
  obtain ⟨j₀, ⟨u, hu, hord⟩, hL⟩ :=
    leviSurj_of_blocks_gen (ι := Fin s ⊕ Unit) (G := orthLeviGroup F 3 d) hp hp2 hzP hz hrk
      (orthLeviHom b c hd) hβ (orthLeviBlock F 3 d b c) hS hcomm hperf hpR hblk
  rcases j₀ with l | w
  · have hv1 : u ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
    have hv2 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    have hk3 : 3 ≤ d l.succ - d l.castSucc :=
      orthMinus_three_le_of_pow_eq_one hF hp hp5 hpq hv1 hv2
    have hmono : d l.succ ≤ d (Fin.last s) := hd.mono.monotone (Fin.le_last _)
    have hk : d l.succ - d l.castSucc = 3 := by omega
    obtain ⟨e⟩ := fong_nonempty_quotient_iso_three (F := F) (d l.succ - d l.castSucc) hk
      (orthLeviBlock F 3 d b c (Sum.inl l)) rfl
    exact LeviSurj.of_mulEquiv hL e
  · exfalso
    have hv1 : u ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
    have hu0 : u = 1 := (orth8_orthResDer_eq_zero_facts hirr hp hp5 hpq h0).2 u hu hv1
    rw [hu0, orderOf_one] at hord
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
