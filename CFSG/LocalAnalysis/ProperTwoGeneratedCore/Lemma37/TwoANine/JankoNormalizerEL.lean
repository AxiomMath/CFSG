module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerEPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreeD
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFInvolution

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup CFSG.DisconnectedInvolutionGraph.Helpers

namespace JankoNormalizerE

open Janko

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))

theorem map_closure_Q :
    (closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} : Set J)).map (proj e) =
      closure {ybar, tbar * ℓbar} := by
  rw [MonoidHom.map_closure, Set.image_pair, JankoPTwoThree.proj_someLift_ℓbar_sq, map_mul,
    proj_someLift, proj_someLift]

theorem proj_mem_of_mem_Q {x : J}
    (hx : x ∈ closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} : Set J)) :
    proj e x ∈ closure ({ybar, tbar * ℓbar} : Set (alternatingGroup (Fin 9))) := by
  rw [← map_closure_Q e]
  exact mem_map_of_mem _ hx

include hJ

theorem zbar_mem_Q :
    zbar J ∈ closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} : Set J) := by
  rw [← hJ.sq_eq_zbar_of_cycleType_two_two e (x := someLift e ℓbar ^ 2)
    (by rw [JankoPTwoThree.proj_someLift_ℓbar_sq]; exact JankoF.cycleType_ybar)]
  exact pow_mem (subset_closure (by simp)) 2

theorem eq_zbar_of_mem_Q {x : J}
    (hx : x ∈ closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} : Set J))
    (h2 : orderOf x = 2) : x = zbar J := by
  have hx2 : x ^ 2 = 1 := by
    rw [← h2]
    exact pow_orderOf_eq_one x
  by_cases h1 : proj e x = 1
  · rcases hJ.mem_center_iff.mp ((proj_eq_one_iff e).mp h1) with h | h
    · rw [h, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  · have hsq := hJ.sq_eq_zbar_of_cycleType_two_two e
      (JankoNormalizerE.cycleType_of_mem_closure_ybar_qbar (proj_mem_of_mem_Q e hx) h1)
    exact absurd (hsq.symm.trans hx2) hJ.zbar_ne_one

theorem card_closure_Q :
    Nat.card (closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} : Set J)) = 8 := by
  rw [JankoPTwoThree.card_eq_two_mul_card_map hJ e (zbar_mem_Q hJ e), map_closure_Q,
    card_closure_ybar_qbar]

end JankoNormalizerE

namespace JankoNormalizerE

open Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

theorem t_notMem_F : t e ∉ F e := by
  rw [t, F, JankoF.coe_mem_map_comap_iff, proj_someLift]
  exact JankoNormalizerE.tbar_notMem_Fbar

theorem zpowers_ℓ_le_F : zpowers (ℓ e) ≤ F e :=
  zpowers_le.mpr (ℓ_mem_F e)

theorem t_notMem_zpowers_ℓ : t e ∉ zpowers (ℓ e) := fun h => t_notMem_F e (zpowers_ℓ_le_F e h)

theorem closure_ℓ_t : closure ({ℓ e, t e} : Set G) = zpowers (ℓ e) ⊔ zpowers (t e) := by
  rw [Set.insert_eq, Subgroup.closure_union, zpowers_eq_closure, zpowers_eq_closure]

theorem ℓ_mem_L : ℓ e ∈ closure ({ℓ e, t e} : Set G) :=
  subset_closure (by simp)

theorem t_mem_L : t e ∈ closure ({ℓ e, t e} : Set G) :=
  subset_closure (by simp)

theorem Q_eq_map : closure ({ℓ e ^ 2, t e * ℓ e} : Set G) =
    (closure ({someLift e ℓbar ^ 2, someLift e tbar * someLift e ℓbar} :
      Set (centralizer ({z} : Set G)))).map (centralizer ({z} : Set G)).subtype := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

include hH

theorem t_inv : (t e)⁻¹ = t e := by
  have h := pow_orderOf_eq_one (t e)
  rw [orderOf_t hH e, sq] at h
  exact inv_eq_of_mul_eq_one_left h

theorem t_mem_normalizer_zpowers_ℓ : t e ∈ normalizer (zpowers (ℓ e) : Set G) :=
  JankoPTwoThree.mem_normalizer_zpowers (by rw [t_mul_ℓ hH e]; exact pow_mem (mem_zpowers _) 3)
    (by rw [t_inv hH e, t_mul_ℓ hH e]; exact pow_mem (mem_zpowers _) 3)

theorem s₁_ne_one : s₁ e ≠ 1 := fun h => by
  have h3 := orderOf_s₁ hH e
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem t_notMem_centralizer_P₁ : t e ∉ centralizer (zpowers (s₁ e) : Set G) := by
  rw [centralizer_zpowers_s₁, mem_centralizer_singleton_iff]
  intro h
  have h1 := t_mul_s₁ hH e
  rw [h, mul_inv_cancel_right] at h1
  have h2 : s₁ e ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_s₁ hH e] at h3
  exact absurd h3 (by norm_num)

theorem L_le_normalizer_P₁ :
    closure ({ℓ e, t e} : Set G) ≤ normalizer (zpowers (s₁ e) : Set G) := by
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact centralizer_le_normalizer _ (F_le_centralizer hH e (ℓ_mem_F e))
  · exact JankoPTwoThree.mem_normalizer_zpowers_of_conj_eq_inv (t_mul_s₁ hH e)

theorem card_Q : Nat.card (closure ({ℓ e ^ 2, t e * ℓ e} : Set G)) = 8 := by
  rw [Q_eq_map, card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
    JankoNormalizerE.card_closure_Q hH e]

include hz

theorem ℓ_sq_mul_tℓ_ne : ℓ e ^ 2 * (t e * ℓ e) ≠ t e * ℓ e * ℓ e ^ 2 := by
  intro h
  have h1 : t e * ℓ e * ℓ e ^ 2 * (t e * ℓ e)⁻¹ = ℓ e ^ 2 := mul_inv_eq_of_eq_mul h.symm
  have h2 : t e * ℓ e * ℓ e ^ 2 * (t e * ℓ e)⁻¹ = (t e * ℓ e * (t e)⁻¹) ^ 2 := by
    rw [conj_pow]
    group
  rw [h2, t_mul_ℓ hH e, ← pow_mul, show (3 * 2 : ℕ) = 4 + 2 from rfl, pow_add] at h1
  have h4 := mul_eq_right.mp h1
  rw [ℓ_pow_four hz hH e] at h4
  rw [h4, orderOf_one] at hz
  exact absurd hz (by norm_num)

end JankoNormalizerE

namespace Janko

open JankoNormalizerE

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

include hz hH

theorem card_L : Nat.card (closure ({ℓ e, t e} : Set G)) = 16 := by
  have h2 : Nat.card (zpowers (t e)) = 2 := by rw [Nat.card_zpowers, orderOf_t hH e]
  have : Finite (zpowers (t e)) := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hdisj : Disjoint (zpowers (ℓ e)) (zpowers (t e)) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (zpowers (ℓ e) ⊓ zpowers (t e) : Subgroup G) ∣ 2 :=
      h2 ▸ card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : zpowers (ℓ e) ⊓ zpowers (t e) = zpowers (t e) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, h2])
      exact t_notMem_zpowers_ℓ e ((inf_eq_right.mp heq) (mem_zpowers _))
  rw [closure_ℓ_t, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (zpowers_le.mpr (t_mem_normalizer_zpowers_ℓ hH e)) hdisj, Nat.card_zpowers, h2,
    orderOf_ℓ hz hH e]

theorem L_inf_centralizer :
    closure ({ℓ e, t e} : Set G) ⊓ centralizer (zpowers (s₁ e) : Set G) = zpowers (ℓ e) := by
  have hL := card_L hz hH e
  have : Finite (closure ({ℓ e, t e} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have hle : zpowers (ℓ e) ≤
      closure ({ℓ e, t e} : Set G) ⊓ centralizer (zpowers (s₁ e) : Set G) :=
    le_inf (zpowers_le.mpr (ℓ_mem_L e)) ((zpowers_ℓ_le_F e).trans (F_le_centralizer hH e))
  have h8 : Nat.card (zpowers (ℓ e)) = 8 := by rw [Nat.card_zpowers, orderOf_ℓ hz hH e]
  have : Finite (closure ({ℓ e, t e} : Set G) ⊓ centralizer (zpowers (s₁ e) : Set G) :
      Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : closure ({ℓ e, t e} :
      Set G) ⊓ centralizer (zpowers (s₁ e) : Set G) ≤ _))
  have hd1 := card_dvd_of_le hle
  have hd2 := card_dvd_of_le (inf_le_left : closure ({ℓ e, t e} : Set G) ⊓
    centralizer (zpowers (s₁ e) : Set G) ≤ _)
  rw [h8] at hd1
  rw [hL] at hd2
  have hne : Nat.card (closure ({ℓ e, t e} : Set G) ⊓
      centralizer (zpowers (s₁ e) : Set G) : Subgroup G) ≠ 16 := by
    intro h16
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : closure ({ℓ e, t e} : Set G) ⊓
      centralizer (zpowers (s₁ e) : Set G) ≤ _) (by rw [h16, hL])
    exact t_notMem_centralizer_P₁ hH e ((inf_eq_left.mp heq) (t_mem_L e))
  have hpos := Nat.pos_of_dvd_of_pos hd2 (by norm_num)
  have hle16 := Nat.le_of_dvd (by norm_num) hd2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem mul_s₁_of_not_mem : ∀ x ∈ closure ({ℓ e, t e} : Set G), x ∉ zpowers (ℓ e) →
    x * s₁ e * x⁻¹ = (s₁ e)⁻¹ := by
  intro x hx hxL
  have hmem : x * s₁ e * x⁻¹ ∈ zpowers (s₁ e) :=
    (mem_normalizer_iff.mp (L_le_normalizer_P₁ hH e hx) _).mp (mem_zpowers _)
  rcases JankoPTwoThree.eq_or_eq_inv_of_mem_zpowers (orderOf_s₁ hH e) hmem
    (JankoPTwoThree.conj_ne_one (s₁_ne_one hH e)) with h | h
  · refine absurd ?_ hxL
    rw [← L_inf_centralizer hz hH e]
    refine mem_inf.mpr ⟨hx, ?_⟩
    rw [centralizer_zpowers_s₁, mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp h
  · exact h

theorem eq_z_of_mem_Q : ∀ x ∈ closure ({ℓ e ^ 2, t e * ℓ e} : Set G), orderOf x = 2 → x = z := by
  rw [Q_eq_map]
  rintro _ ⟨x, hx, rfl⟩ h2
  rw [coe_subtype, Subgroup.orderOf_coe] at h2
  rw [coe_subtype, JankoNormalizerE.eq_zbar_of_mem_Q hH e hx h2]
  exact JankoPTwoThree.coe_zbar_eq hz hH

theorem Q_quaternion : Nonempty (closure ({ℓ e ^ 2, t e * ℓ e} : Set G) ≃* QuaternionGroup 2) := by
  have h8 := card_Q hH e
  have : Finite (closure ({ℓ e ^ 2, t e * ℓ e} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hp : IsPGroup 2 (closure ({ℓ e ^ 2, t e * ℓ e} : Set G)) :=
    IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hrank : NoCommutingDistinctInvolutions (closure ({ℓ e ^ 2, t e * ℓ e} : Set G)) := by
    intro a b _
    have ha := eq_z_of_mem_Q hz hH e _ (a : closure ({ℓ e ^ 2, t e * ℓ e} : Set G)).2
      (by rw [Subgroup.orderOf_coe]; exact a.2)
    have hb := eq_z_of_mem_Q hz hH e _ (b : closure ({ℓ e ^ 2, t e * ℓ e} : Set G)).2
      (by rw [Subgroup.orderOf_coe]; exact b.2)
    exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
  have hnonab : ∃ a b : closure ({ℓ e ^ 2, t e * ℓ e} : Set G), a * b ≠ b * a :=
    ⟨⟨ℓ e ^ 2, subset_closure (by simp)⟩, ⟨t e * ℓ e, subset_closure (by simp)⟩,
      fun h => ℓ_sq_mul_tℓ_ne hz hH e (congrArg Subtype.val h)⟩
  obtain ⟨n, -, ⟨φ⟩⟩ := rank_one_two_nonabelian_quaternion hp hrank hnonab
  have hcard : 4 * 2 ^ n = 8 := by
    rw [← h8, ← Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hn : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hn
  exact ⟨φ.symm⟩

theorem eq_of_le_L : ∀ B : Subgroup G, B ≤ closure ({ℓ e, t e} : Set G) → Nat.card B = 8 →
    t e ∉ B → B = zpowers (ℓ e) ∨ B = closure ({ℓ e ^ 2, t e * ℓ e} : Set G) := by
  intro B hBL hB8 htB
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB8]; norm_num)
  have hidx : (B.subgroupOf (closure ({ℓ e, t e} : Set G))).index = 2 := by
    have h := (B.subgroupOf (closure ({ℓ e, t e} : Set G))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv, hB8, card_L hz hH e] at h
    omega
  have hℓ2 : ℓ e ^ 2 ∈ B := mem_subgroupOf.mp (sq_mem_of_index_two hidx ⟨ℓ e, ℓ_mem_L e⟩)
  by_cases hℓB : ℓ e ∈ B
  · left
    exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hℓB)
      (by rw [hB8, Nat.card_zpowers, orderOf_ℓ hz hH e])).symm
  · right
    have htℓ : t e * ℓ e ∈ B := mem_subgroupOf.mp ((mul_mem_iff_of_index_two hidx
      (a := ⟨t e, t_mem_L e⟩) (b := ⟨ℓ e, ℓ_mem_L e⟩)).mpr
        (iff_of_false (fun h => htB (mem_subgroupOf.mp h)) (fun h => hℓB (mem_subgroupOf.mp h))))
    have hQB : closure ({ℓ e ^ 2, t e * ℓ e} : Set G) ≤ B := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      exacts [hℓ2, htℓ]
    exact (Subgroup.eq_of_le_of_card_ge hQB (by rw [hB8, card_Q hH e])).symm

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
