module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBlocksGen
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSL4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub
  (orthMinus_three_le_of_pow_eq_one orthMinus_res_block_data
    orthMinus_mem_orthResDer_of_pow_eq_one det_eq_one_of_pow_eq_one slRange)
open scoped commutatorElement

theorem orth8res_commutator_self_eq_of_simple {G : Type*} [Group G] (H : Subgroup G)
    (hs : IsSimpleGroup ↥H) (hna : ∃ x y : ↥H, x * y ≠ y * x) : ⁅H, H⁆ = H := by
  apply fong_commutator_self_eq_of_top H
  rcases hs.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    apply hxy
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem orth8res_le_orthogonalGroup {F : Type} [Field F] {b c : F} (m : ℕ) :
    orthResDer F b c m ≤ TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm F b c)) :=
  Subgroup.commutator_le_of_le le_rfl le_rfl

theorem orth8_levi_res {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : CFSG.Open.pRank p
      (⊤ : Subgroup ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) ≤ 1)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {s : ℕ} (hs : 1 ≤ s) {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (ht : d (Fin.last s) ≤ 2)
    {z : ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))} (hz : orderOf z = p)
    (hzP : z ∈ orthParab 3 (minusTailForm F b c) d) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ LeviSurj p (orthParab 3 (minusTailForm F b c) d) z
      (↥(orthResDer F b c m) ⧸ Subgroup.center ↥(orthResDer F b c m)) := by
  have hpF : ¬ p ∣ Nat.card F - 1 := fun h => hpq (h.trans (Nat.sub_one_dvd_pow_sub_one _ 2))
  have hp2 : p ≠ 2 := by omega
  have hdle : ∀ i : Fin (s + 1), d i ≤ 2 := fun i => (hd.mono.monotone (Fin.le_last i)).trans ht
  have hlast1 : 1 ≤ d (Fin.last s) := by
    have h0 : (0 : Fin (s + 1)) < Fin.last s := by
      simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last]
      omega
    have h := hd.mono h0
    rw [hd.zero] at h
    omega
  have hm1 : 1 ≤ 3 - d (Fin.last s) := by omega
  have hk_le : ∀ l : Fin s, d l.succ - d l.castSucc ≤ 2 := fun l =>
    (Nat.sub_le _ _).trans (hdle l.succ)
  have hnoinl : ∀ l : Fin s, ∀ u : orthLeviGroup F 3 d (Sum.inl l), orderOf u ≠ p := by
    intro l u hord
    have hu' : u ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hord
      exact hp.one_lt.ne hord
    have h3 := orthMinus_three_le_of_pow_eq_one (k := d l.succ - d l.castSucc) hF hp hp5 hpq hu' hu1
    have := hk_le l
    omega
  have hβ : IsPGroup 2 (orthLeviHom b c hd).ker := isPGroup_ker_orthLeviHom hd
  have hS : Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) ≤ (orthLeviHom b c hd).range :=
    pi_orthLeviBlock_le_range hd (le_refl 3)
      (commutator_orthogonalGroup_quadTail_minus (le_refl 3) hirr)
  have hcomm : ⁅(orthLeviHom b c hd).range, (orthLeviHom b c hd).range⁆ ≤
      Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) :=
    commutator_range_orthLeviHom_le hd
  have hperf : ∀ j, ⁅orthLeviBlock F 3 d b c j, orthLeviBlock F 3 d b c j⁆ =
      orthLeviBlock F 3 d b c j ∨
      ((∀ a ∈ orthLeviBlock F 3 d b c j, ∀ a' ∈ orthLeviBlock F 3 d b c j, a * a' = a' * a) ∧
        ∀ x ∈ orthLeviBlock F 3 d b c j, x ^ p = 1 → x = 1) := by
    rintro (l | v)
    · exact Or.inl (fong_commutator_self_eq_of_top (orthLeviBlock F 3 d b c (Sum.inl l))
        (fong_commutator_top_of_mulEquiv
          (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) (d l.succ - d l.castSucc))
          (fong_commutator_specialLinear h4 (d l.succ - d l.castSucc))))
    · obtain ⟨hs, hna, -⟩ := orthResDer_facts hF hm1 hirr
      exact Or.inl (orth8res_commutator_self_eq_of_simple
        (orthResDer F b c (3 - d (Fin.last s))) hs hna)
  have hpR : ∀ x ∈ (orthLeviHom b c hd).range, x ^ p = 1 →
      x ∈ Subgroup.pi Set.univ (orthLeviBlock F 3 d b c) := by
    rintro x ⟨g, rfl⟩ hxp
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    rcases j with l | v
    · have hxl : orthLeviHom b c hd g (Sum.inl l) ^ p = 1 := by
        have h := congrFun hxp (Sum.inl l)
        rwa [Pi.pow_apply, Pi.one_apply] at h
      show orthLeviHom b c hd g (Sum.inl l) ∈ slRange F (d l.succ - d l.castSucc)
      rw [slRange, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact det_eq_one_of_pow_eq_one (k := d l.succ - d l.castSucc) hp hpF hxl
    · have h2 := congrFun hxp (Sum.inr v)
      rw [Pi.pow_apply, Pi.one_apply] at h2
      have hx' : (⟨orthResHom (minusTailForm F b c) hd g, orthResHom_mem_orthogonalGroup hd g⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup
            (quadTail (3 - d (Fin.last s)) (minusTailForm F b c)))) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact h2
      exact orthMinus_mem_orthResDer_of_pow_eq_one hF hm1 hirr hp hp2 hx'
  have hblk : ∀ j, (∃ u ∈ orthLeviBlock F 3 d b c j, orderOf u = p) →
      CFSG.Open.IsQuasisimple ↥(orthLeviBlock F 3 d b c j) ∧
        ¬ p ∣ Nat.card (Subgroup.center ↥(orthLeviBlock F 3 d b c j)) := by
    rintro (l | v) ⟨u, hu, hord⟩
    · exact (hnoinl l u hord).elim
    · have hu' : u ∈ orthResDer F b c (3 - d (Fin.last s)) := hu
      have hup : u ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
      have hu1 : u ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        exact hp.one_lt.ne hord
      let x : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (quadTail (3 - d (Fin.last s)) (minusTailForm F b c))) :=
        ⟨u, orth8res_le_orthogonalGroup (3 - d (Fin.last s)) hu'⟩
      have hx : x ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hup
      have hx1 : x ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
      obtain ⟨hq, hc, -, -⟩ :=
        orthMinus_res_block_data (m := 3 - d (Fin.last s)) hF hirr hp hp5 hpq hx hx1
      exact ⟨hq, hc⟩
  haveI : Finite (((Fin 3 ⊕ Fin 3 → F) × (Fin 2 → F)) ≃ₗ[F]
      ((Fin 3 ⊕ Fin 3 → F) × (Fin 2 → F))) := finite_orthLinearEquiv
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))) := Subtype.finite
  obtain ⟨j₀, hu, hL⟩ := leviSurj_of_blocks_gen hp hp2 hzP hz hrk (orthLeviHom b c hd) hβ
    (orthLeviBlock F 3 d b c) hS hcomm hperf hpR hblk
  rcases j₀ with l | v
  · obtain ⟨u, -, hord⟩ := hu
    exact (hnoinl l u hord).elim
  · exact ⟨3 - d (Fin.last s), by omega, hL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
