module

public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem coe_eq_mul_closure_of_quotient {C N : Subgroup G} (hCN : C ≤ N)
    [(C.subgroupOf N).Normal] (s : Set G) (hs : s ⊆ N)
    (hgen : Subgroup.closure ((QuotientGroup.mk' (C.subgroupOf N)) '' {x : N | (x : G) ∈ s}) =
      ⊤) :
    (N : Set G) = (C : Set G) * (Subgroup.closure s : Set G) := by
  apply Set.Subset.antisymm
  · intro g hg
    have hmem : (QuotientGroup.mk' (C.subgroupOf N)) ⟨g, hg⟩ ∈
        (Subgroup.closure {x : N | (x : G) ∈ s}).map (QuotientGroup.mk' (C.subgroupOf N)) := by
      rw [MonoidHom.map_closure, hgen]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwg⟩ := hmem
    have hc : w⁻¹ * ⟨g, hg⟩ ∈ C.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' (C.subgroupOf N) w)⁻¹ *
        QuotientGroup.mk' (C.subgroupOf N) ⟨g, hg⟩ = 1
      rw [hwg, inv_mul_cancel]
    have hwG : (w : G) ∈ Subgroup.closure s := by
      have h := Subgroup.mem_map_of_mem N.subtype hw
      rw [MonoidHom.map_closure] at h
      refine (Subgroup.closure_mono ?_) h
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hcG : (w : G)⁻¹ * g ∈ C := hc
    have hconj : (w : G) * ((w : G)⁻¹ * g) * (w : G)⁻¹ ∈ C := by
      have := (inferInstance : (C.subgroupOf N).Normal).conj_mem _ hc w
      exact this
    refine ⟨(w : G) * ((w : G)⁻¹ * g) * (w : G)⁻¹, hconj, w, hwG, by group⟩
  · rintro _ ⟨c, hc, w, hw, rfl⟩
    refine N.mul_mem (hCN hc) ?_
    have : Subgroup.closure s ≤ N := (Subgroup.closure_le N).mpr hs
    exact this hw

theorem exists_base_three_cycle {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    ∃ Y ∈ Subgroup.normalizer (modelBase S e : Set G),
      Y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * Y =
          wreathModelHom S e (Original.x2 (2 ^ n)) ∧
      Y⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) * Y =
          wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) ∧
      Y⁻¹ * wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) * Y =
          wreathModelHom S e (Original.x (2 ^ n)) := by
  set φ := wreathModelHom S e
  set J := φ (Original.x (2 ^ n))
  set J₁ := φ (Original.x2 (2 ^ n))
  set J₂ := φ (Original.t (2 ^ n) ^ (2 ^ n / 2))
  set T := φ (Original.z (2 ^ n))
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨g₁, hg₁N, hg₁⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hbase
    J J₁ (modelHom_x_mem_modelBase S e) (modelHom_x2_mem_modelBase S e)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.1)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.2.1)
  set Y₀ := g₁⁻¹
  have hY₀N : Y₀ ∈ Subgroup.normalizer (modelBase S e : Set G) :=
    (Subgroup.normalizer _).inv_mem hg₁N
  have hY₀J : Y₀⁻¹ * J * Y₀ = J₁ := by simpa [Y₀] using hg₁
  have hJJ₁ : J * J₁ = J₂ := modelHom_x_mul_x2 S e (by omega)
  have hJ₁J₂ : J₁ * J₂ = J := modelHom_x2_mul_t_half S e
  have hJ₁J : J₁ * J = J₂ := by
    rw [← hJJ₁]
    exact modelBase_commute S e _ _ (modelHom_x2_mem_modelBase S e) (modelHom_x_mem_modelBase S e)
  set u := Y₀⁻¹ * J₁ * Y₀
  have huB : u ∈ modelBase S e :=
    (Subgroup.mem_normalizer_iff''.mp hY₀N J₁).mp (modelHom_x2_mem_modelBase S e)
  have hu2 : orderOf u = 2 := by
    rw [show u = (MulAut.conj Y₀⁻¹) J₁ by simp [u], MulEquiv.orderOf_eq,
      orderOf_injective _ (wreathModelHom_injective S e)]
    exact hstr.involution_orders.2.1
  have huJ₁ : u ≠ J₁ := by
    intro h
    apply modelHom_x_ne_x2 S e (by omega)
    have h' : Y₀⁻¹ * J * Y₀ = Y₀⁻¹ * J₁ * Y₀ := hY₀J.trans h.symm
    exact mul_left_cancel (mul_right_cancel h')
  rcases modelBase_involution_cases S e (by omega) huB hu2 with hu | hu | hu
  ·
    refine ⟨T * Y₀, (Subgroup.normalizer _).mul_mem
      (sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)) hY₀N, ?_, ?_, ?_⟩
    · have hTJ : T⁻¹ * J * T = J := modelHom_x_central S e hn (wreathModelHom_mem S e _)
      calc
        (T * Y₀)⁻¹ * J * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J * T) * Y₀ := by group
        _ = J₁ := by rw [hTJ, hY₀J]
    · calc
        (T * Y₀)⁻¹ * J₁ * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J₁ * T) * Y₀ := by group
        _ = Y₀⁻¹ * (J * J₁) * Y₀ := by rw [modelHom_swap_conj_x2 S e, hJJ₁]
        _ = (Y₀⁻¹ * J * Y₀) * (Y₀⁻¹ * J₁ * Y₀) := by group
        _ = J₂ := by rw [hY₀J, show Y₀⁻¹ * J₁ * Y₀ = J from hu, hJ₁J]
    · calc
        (T * Y₀)⁻¹ * J₂ * (T * Y₀) = Y₀⁻¹ * (T⁻¹ * J₂ * T) * Y₀ := by group
        _ = J := by rw [modelHom_swap_conj_t_half S e]; exact hu
  · exact absurd hu huJ₁
  · refine ⟨Y₀, hY₀N, hY₀J, hu, ?_⟩
    calc
      Y₀⁻¹ * J₂ * Y₀ = (Y₀⁻¹ * J * Y₀) * (Y₀⁻¹ * J₁ * Y₀) := by rw [← hJJ₁]; group
      _ = J := by rw [hY₀J, show Y₀⁻¹ * J₁ * Y₀ = J₂ from hu, hJ₁J₂]

omit [Finite G] in
theorem swap_not_mem_centralizer_modelBase {n : ℕ} (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.z (2 ^ n)) ∉
      Subgroup.centralizer (modelBase S e : Set G) := by
  intro h
  have hc := Subgroup.mem_centralizer_iff.mp h _ (modelHom_x2_mem_modelBase S e)
  have h' : (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n)) = wreathModelHom S e (Original.x2 (2 ^ n)) := by
    rw [mul_assoc, hc]
    group
  rw [modelHom_swap_conj_x2] at h'
  exact modelHom_x2_ne_t_half S e hn h'.symm

omit [Finite G] in
theorem relIndex_eq_card_quotient (C N : Subgroup G) :
    C.relIndex N = Nat.card (N ⧸ C.subgroupOf N) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

theorem normalizer_base_eq_of_three_cycle {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (Y : G) (hYN : Y ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hY1 : Y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * Y =
      wreathModelHom S e (Original.x2 (2 ^ n)))
    (hY2 : Y⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) * Y =
      wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)))
    (hY3 : Y⁻¹ * wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) * Y =
      wreathModelHom S e (Original.x (2 ^ n))) :
    (Subgroup.normalizer (modelBase S e : Set G) : Set G) =
      (Subgroup.centralizer (modelBase S e : Set G) : Set G) *
        (Subgroup.closure {wreathModelHom S e (Original.z (2 ^ n)), Y} : Set G) := by
  set N := Subgroup.normalizer (modelBase S e : Set G)
  set C := Subgroup.centralizer (modelBase S e : Set G)
  set J := wreathModelHom S e (Original.x (2 ^ n))
  set T := wreathModelHom S e (Original.z (2 ^ n))
  have hTN : T ∈ N := sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)
  have hs : ({T, Y} : Set G) ⊆ N := by
    rintro _ (rfl | rfl)
    · exact hTN
    · exact hYN
  apply coe_eq_mul_closure_of_quotient (Subgroup.centralizer_le_normalizer _) _ hs
  set π := QuotientGroup.mk' (C.subgroupOf N)
  set H := Subgroup.closure (π '' {x : N | (x : G) ∈ ({T, Y} : Set G)})
  obtain ⟨esix⟩ := hbase
  have hQ : Nat.card (N ⧸ C.subgroupOf N) = 6 := by
    rw [Nat.card_congr esix.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hTH : π ⟨T, hTN⟩ ∈ H := Subgroup.subset_closure ⟨⟨T, hTN⟩, by simp, rfl⟩
  have hYH : π ⟨Y, hYN⟩ ∈ H := Subgroup.subset_closure ⟨⟨Y, hYN⟩, by simp, rfl⟩
  have hπ (x : N) : π x = 1 ↔ (x : G) ∈ C := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hT2 : orderOf (π ⟨T, hTN⟩) = 2 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [← map_pow, hπ]
      have hz : Original.z (2 ^ n) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (Original.z (2 ^ n))
        rwa [Original.orderOf_z] at h
      have : (T : G) ^ 2 = 1 := by rw [← map_pow, hz, map_one]
      change (T : G) ^ 2 ∈ C
      rw [this]
      exact C.one_mem
    · rw [Ne, hπ]
      exact swap_not_mem_centralizer_modelBase (by omega) S e
  have hY3k : ∀ q : ℕ, (Y ^ (3 * q))⁻¹ * J * Y ^ (3 * q) = J := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [show 3 * (q + 1) = 3 * q + 3 by ring, pow_add]
        calc
          (Y ^ (3 * q) * Y ^ 3)⁻¹ * J * (Y ^ (3 * q) * Y ^ 3) =
              Y⁻¹ * (Y⁻¹ * (Y⁻¹ * ((Y ^ (3 * q))⁻¹ * J * Y ^ (3 * q)) * Y) * Y) * Y := by
            simp only [pow_succ, pow_zero, one_mul]
            group
          _ = J := by rw [ih, hY1, hY2, hY3]
  have hY3dvd : 3 ∣ orderOf (π ⟨Y, hYN⟩) := by
    set k := orderOf (π ⟨Y, hYN⟩)
    have hk : π ⟨Y, hYN⟩ ^ k = 1 := pow_orderOf_eq_one _
    rw [← map_pow, hπ, Subgroup.coe_pow] at hk
    have hfix : (Y ^ k)⁻¹ * J * Y ^ k = J := by
      have h := Subgroup.mem_centralizer_iff.mp hk J (modelHom_x_mem_modelBase S e)
      change J * Y ^ k = Y ^ k * J at h
      rw [mul_assoc, h]
      group
    obtain ⟨q, r, hr, hkqr⟩ : ∃ q r, r < 3 ∧ k = 3 * q + r :=
      ⟨k / 3, k % 3, Nat.mod_lt _ (by decide), (Nat.div_add_mod k 3).symm⟩
    rw [hkqr, pow_add] at hfix
    have hred : (Y ^ r)⁻¹ * J * Y ^ r = J := by
      have h : (Y ^ (3 * q) * Y ^ r)⁻¹ * J * (Y ^ (3 * q) * Y ^ r) =
          (Y ^ r)⁻¹ * ((Y ^ (3 * q))⁻¹ * J * Y ^ (3 * q)) * Y ^ r := by group
      rw [h, hY3k] at hfix
      exact hfix
    interval_cases r
    · rw [hkqr, add_zero]
      exact Dvd.intro q rfl
    · rw [pow_one, hY1] at hred
      exact absurd hred.symm (modelHom_x_ne_x2 S e (by omega))
    · rw [pow_two, show (Y * Y)⁻¹ * J * (Y * Y) = Y⁻¹ * (Y⁻¹ * J * Y) * Y by group, hY1,
        hY2] at hred
      exact absurd hred.symm (modelHom_x_ne_t_half S e (by omega))
  have h2 : 2 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hTH
    rwa [hT2] at h
  have h3 : 3 ∣ Nat.card H := hY3dvd.trans (Subgroup.orderOf_dvd_natCard H hYH)
  have h6 : 6 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
  have hle : Nat.card H ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card H
    rwa [hQ] at h
  apply Subgroup.eq_top_of_card_eq
  rw [hQ]
  exact Nat.dvd_antisymm hle h6

theorem normalizer_base_eq_of_order_two {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    (Subgroup.normalizer (modelBase S e : Set G) : Set G) =
      (Subgroup.centralizer (modelBase S e : Set G) : Set G) *
        (Subgroup.closure {wreathModelHom S e (Original.z (2 ^ n))} : Set G) := by
  set N := Subgroup.normalizer (modelBase S e : Set G)
  set C := Subgroup.centralizer (modelBase S e : Set G)
  set T := wreathModelHom S e (Original.z (2 ^ n))
  have hTN : T ∈ N := sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)
  have hs : ({T} : Set G) ⊆ N := by
    rintro _ rfl
    exact hTN
  apply coe_eq_mul_closure_of_quotient (Subgroup.centralizer_le_normalizer _) _ hs
  set π := QuotientGroup.mk' (C.subgroupOf N)
  set H := Subgroup.closure (π '' {x : N | (x : G) ∈ ({T} : Set G)})
  have hTH : π ⟨T, hTN⟩ ∈ H := Subgroup.subset_closure ⟨⟨T, hTN⟩, by simp, rfl⟩
  have hT1 : π ⟨T, hTN⟩ ≠ 1 := by
    rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact swap_not_mem_centralizer_modelBase (by omega) S e
  have hH : H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hTH
    exact hT1 hTH
  have hle : Nat.card H ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card H
    rwa [hcard] at h
  have hne1 : Nat.card H ≠ 1 := fun h => hH (Subgroup.eq_bot_of_card_eq H h)
  apply Subgroup.eq_top_of_card_eq
  rw [hcard]
  rcases (Nat.dvd_prime Nat.prime_two).mp hle with h | h
  · exact absurd h hne1
  · exact h

end CFSG.Wreathed.BrauerWong
