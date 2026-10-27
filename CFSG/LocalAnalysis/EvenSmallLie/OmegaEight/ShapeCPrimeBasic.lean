module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_eq_two {K T : Subgroup G} (h : K.relIndex T = 2) :
    ⁅T, T⁆ ≤ K := by
  have h' : (K.subgroupOf T).index = 2 := h
  rw [commutator_le]
  intro x hx y hy
  set x' : T := ⟨x, hx⟩
  set y' : T := ⟨y, hy⟩
  have key : x' * y' * x'⁻¹ * y'⁻¹ ∈ K.subgroupOf T := by
    rw [mul_assoc (x' * y'), mul_mem_iff_of_index_two h', mul_mem_iff_of_index_two h',
      mul_mem_iff_of_index_two h', inv_mem_iff, inv_mem_iff]
  rw [mem_subgroupOf] at key
  simpa [commutatorElement_def] using key

theorem normal_subgroupOf_of_relIndex_eq_two {K T : Subgroup G} (h : K.relIndex T = 2) :
    (K.subgroupOf T).Normal :=
  Subgroup.normal_of_index_eq_two h

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem U_le_L : U ≤ L := hS.rad.U_le_L

theorem c_conj_mem_U {u : G} (hu : u ∈ U) : c * u * c⁻¹ ∈ U := hS.data.c_normalizes_U u hu

theorem c_inv_conj_mem_U {u : G} (hu : u ∈ U) : c⁻¹ * u * c⁻¹⁻¹ ∈ U := by
  have h : c⁻¹ = c * c * c := by rw [hS.shape.c_inv, hS.shape.sq, hS.shape.c_comm]
  have h3 := hS.c_conj_mem_U (hS.c_conj_mem_U (hS.c_conj_mem_U hu))
  rw [h]
  convert h3 using 1
  group

theorem c_mem_normalizer_U : c ∈ normalizer (U : Set G) := by
  refine mem_normalizer_iff.2 fun n => ⟨fun h => hS.c_conj_mem_U h, fun h => ?_⟩
  have := hS.c_inv_conj_mem_U h
  simpa [mul_assoc] using this

theorem zpowers_c_le : zpowers c ≤ normalizer (U : Set G) := zpowers_le.2 hS.c_mem_normalizer_U

theorem mem_zpowers_c {z : G} : z ∈ zpowers c ↔ z = 1 ∨ z = c ∨ z = t ∨ z = c * t := by
  constructor
  · rintro ⟨k, rfl⟩
    have h4 : c ^ (4 : ℕ) = 1 := hS.shape.c_pow_four
    change c ^ k = 1 ∨ c ^ k = c ∨ c ^ k = t ∨ c ^ k = c * t
    rw [zpow_eq_zpow_emod' k h4]
    have hlt : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
    have hge : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
    have hcases : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨ k % ((4 : ℕ) : ℤ) = 2 ∨
        k % ((4 : ℕ) : ℤ) = 3 := by omega
    rcases hcases with h | h | h | h <;> rw [h]
    · exact Or.inl (zpow_zero c)
    · exact Or.inr (Or.inl (zpow_one c))
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, hS.shape.sq]
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, pow_succ, pow_two, hS.shape.sq,
        hS.shape.c_comm]
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers c
    · rw [← hS.shape.sq]; exact mul_mem (mem_zpowers c) (mem_zpowers c)
    · rw [← hS.shape.sq]
      exact mul_mem (mem_zpowers c) (mul_mem (mem_zpowers c) (mem_zpowers c))

theorem mem_TH_iff {x : G} : x ∈ U ⊔ zpowers c ↔
    ∃ u ∈ U, x = u ∨ x = u * c ∨ x = u * t ∨ x = u * (c * t) := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left U (zpowers c) hS.zpowers_c_le]
  constructor
  · rintro ⟨u, hu, z, hz, rfl⟩
    rcases hS.mem_zpowers_c.1 hz with rfl | rfl | rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr (Or.inl rfl)⟩
    · exact ⟨u, hu, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨u, hu, Or.inr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨u, hu, h | h | h | h⟩ <;> rw [h]
    · exact ⟨u, hu, 1, one_mem _, mul_one u⟩
    · exact ⟨u, hu, c, hS.mem_zpowers_c.2 (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨u, hu, t, hS.mem_zpowers_c.2 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨u, hu, c * t, hS.mem_zpowers_c.2 (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

omit hS in
theorem c_mem_TH : c ∈ U ⊔ zpowers c := mem_sup_right (mem_zpowers c)

theorem t_mem_TH : t ∈ U ⊔ zpowers c := hS.shape.sq ▸ mul_mem c_mem_TH c_mem_TH

theorem K_le_TH : U ⊔ zpowers t ≤ U ⊔ zpowers c := sup_le le_sup_left (zpowers_le.2 hS.t_mem_TH)

theorem TH_le_centralizer : U ⊔ zpowers c ≤ centralizer ({t} : Set G) :=
  sup_le (hS.U_le_L.trans hS.shape.le_centralizer) (zpowers_le.2 hS.shape.c_mem_centralizer)

theorem isPGroup_zpowers_c : IsPGroup 2 (zpowers c) := by
  rintro ⟨z, hz⟩
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨k, rfl⟩ := hz
  change (c ^ k) ^ (2 ^ 2) = 1
  rw [show (2 ^ 2 : ℕ) = 4 by rfl, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, zpow_natCast, hS.shape.c_pow_four, _root_.one_zpow]

theorem isPGroup_TH : IsPGroup 2 (U ⊔ zpowers c : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' hS.rad.U_pgroup hS.isPGroup_zpowers_c hS.zpowers_c_le

theorem K_le_sup : U ⊔ zpowers t ≤ L ⊔ zpowers t := sup_le_sup_right hS.U_le_L _

theorem mul_c_not_mem {x : G} (hx : x ∈ L ⊔ zpowers t) : x * c ∉ L ⊔ zpowers t := fun h =>
  hS.shape.c_not_mem (by simpa using mul_mem (inv_mem hx) h)

theorem mul_c_t_not_mem {x : G} (hx : x ∈ L ⊔ zpowers t) : x * (c * t) ∉ L ⊔ zpowers t := by
  intro h
  apply hS.shape.c_not_mem
  have ht : t ∈ L ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have := mul_mem (mul_mem (inv_mem hx) h) (inv_mem ht)
  simpa [mul_assoc] using this

theorem mem_K_of_mem_TH {x : G} (hx : x ∈ U ⊔ zpowers c) (hxL : x ∈ L ⊔ zpowers t) :
    x ∈ U ⊔ zpowers t := by
  obtain ⟨u, hu, rfl | rfl | rfl | rfl⟩ := hS.mem_TH_iff.1 hx
  · exact mem_sup_left hu
  · exact absurd hxL (hS.mul_c_not_mem (hS.K_le_sup (mem_sup_left hu)))
  · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))
  · exact absurd hxL (hS.mul_c_t_not_mem (hS.K_le_sup (mem_sup_left hu)))

theorem mem_K_of_mul_self {x : G} (hx : x ∈ U ⊔ zpowers c) (hx2 : x * x = 1) :
    x ∈ U ⊔ zpowers t :=
  hS.mem_K_of_mem_TH hx (hS.shape.involution_mem x (hS.TH_le_centralizer hx) hx2)

theorem mul_self_mem_U {x : G} (hx : x ∈ U ⊔ zpowers t) : x * x ∈ U :=
  hS.shape.mul_self_mem hS.U_le_L hx

theorem c_not_mem_K : c ∉ U ⊔ zpowers t := fun h => hS.shape.c_not_mem (hS.K_le_sup h)

theorem relIndex_K_TH : (U ⊔ zpowers t).relIndex (U ⊔ zpowers c) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨c, c_mem_TH, fun b hb => ?_⟩
  have hU : ∀ u ∈ U, u ∈ L ⊔ zpowers t := fun u hu => hS.K_le_sup (mem_sup_left hu)
  have hUt : ∀ u ∈ U, u * t ∈ L ⊔ zpowers t := fun u hu =>
    mul_mem (hU u hu) (mem_sup_right (mem_zpowers t))
  have hnK : ∀ y, y ∉ L ⊔ zpowers t → y ∉ U ⊔ zpowers t := fun y hy h => hy (hS.K_le_sup h)
  obtain ⟨u, hu, h | rfl | rfl | rfl⟩ := hS.mem_TH_iff.1 hb
  · rw [h]
    exact Or.inr ⟨mem_sup_left hu, hnK _ (hS.mul_c_not_mem (hU u hu))⟩
  · refine Or.inl ⟨?_, hnK _ (hS.mul_c_not_mem (hU u hu))⟩
    rw [mul_assoc, hS.shape.sq]
    exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))
  · exact Or.inr ⟨mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t)),
      hnK _ (hS.mul_c_not_mem (hUt u hu))⟩
  · refine Or.inl ⟨?_, hnK _ (hS.mul_c_t_not_mem (hU u hu))⟩
    have : u * (c * t) * c = u := by
      rw [mul_assoc, mul_assoc, ← hS.shape.c_comm, ← mul_assoc c c, hS.shape.sq, hS.shape.mul_self,
        mul_one]
    rw [this]
    exact mem_sup_left hu

theorem Q_le_L : Q ≤ L := hS.rad.Q_le_L

theorem Q_le_TH : Q ≤ U ⊔ zpowers c := hS.rad.Q_le_U.trans le_sup_left

theorem commute_ψ (v : V6) : ψ v * t = t * ψ v :=
  hS.shape.commute_of_mem (hS.rad.Q_le_L (hS.rad.ψ_mem v))

theorem mem_E_iff {x : G} : x ∈ Q ⊔ zpowers t ↔ ∃ v, x = ψ v ∨ x = t * ψ v := by
  rw [hS.shape.mem_sup_iff hS.Q_le_L]
  constructor
  · rintro ⟨q, hq, h | h⟩ <;> obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    · exact ⟨v, Or.inl h⟩
    · exact ⟨v, Or.inr (h.trans (hS.commute_ψ v))⟩
  · rintro ⟨v, h | h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inl h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inr (h.trans (hS.commute_ψ v).symm)⟩

omit hS in
theorem t_mem_E : t ∈ Q ⊔ zpowers t := mem_sup_right (mem_zpowers t)

theorem ψ_mem_E (v : V6) : ψ v ∈ Q ⊔ zpowers t := mem_sup_left (hS.rad.ψ_mem v)

theorem E_comm {x y : G} (hx : x ∈ Q ⊔ zpowers t) (hy : y ∈ Q ⊔ zpowers t) : x * y = y * x := by
  have hψψ : ∀ v w, Commute (ψ v) (ψ w) := fun v w =>
    hS.rad.Q_comm (hS.rad.ψ_mem v) (hS.rad.ψ_mem w)
  have hψt : ∀ v, Commute (ψ v) t := fun v => hS.commute_ψ v
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hx <;> obtain ⟨w, rfl | rfl⟩ := hS.mem_E_iff.1 hy
  · exact (hψψ v w).eq
  · exact ((hψt v).mul_right (hψψ v w)).eq
  · exact ((hψt w).symm.mul_left (hψψ v w)).eq
  · exact (((Commute.refl t).mul_right (hψt w).symm).mul_left
      ((hψt v).mul_right (hψψ v w))).eq

theorem E_mul_self {x : G} (hx : x ∈ Q ⊔ zpowers t) : x * x = 1 := by
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hx
  · exact hS.rad.ψ_mul_self v
  · calc t * ψ v * (t * ψ v) = t * (ψ v * t) * ψ v := by group
      _ = t * (t * ψ v) * ψ v := by rw [hS.commute_ψ v]
      _ = (t * t) * (ψ v * ψ v) := by group
      _ = 1 := by rw [hS.shape.mul_self, hS.rad.ψ_mul_self, one_mul]

theorem card_E [Finite G] : Nat.card (Q ⊔ zpowers t : Subgroup G) = 128 := by
  have h2 : Q.relIndex (Q ⊔ zpowers t) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨t, t_mem_E, fun b hb => ?_⟩
    have htQ : ∀ x ∈ Q, x * t ∉ Q := fun x hx h =>
      hS.shape.not_mem (hS.Q_le_L (by simpa using Q.mul_mem (Q.inv_mem hx) h))
    obtain ⟨u, hu, h | rfl⟩ := (hS.shape.mem_sup_iff hS.Q_le_L).1 hb
    · rw [h]
      exact Or.inr ⟨hu, htQ u hu⟩
    · rw [mul_assoc, hS.shape.mul_self, mul_one]
      exact Or.inl ⟨hu, htQ u hu⟩
  rw [← Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ zpowers t), h2,
    inf_of_le_left le_sup_left, hS.rad.card_Q]

theorem centralizer_E_le : centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ Q ⊔ zpowers t :=
  fun _ hx => hS.data.centralizer_Q ⟨centralizer_le (Set.singleton_subset_iff.2 t_mem_E) hx,
    centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx⟩

theorem E_le_TH : Q ⊔ zpowers t ≤ U ⊔ zpowers c := sup_le hS.Q_le_TH (zpowers_le.2 hS.t_mem_TH)

theorem c_conj_mem_Q {x : G} (hx : x ∈ Q) : c * x * c⁻¹ ∈ Q := by
  obtain ⟨v, rfl⟩ := hS.rad.mem_ψ x hx
  rw [hS.data.c_act]
  exact hS.rad.ψ_mem _

theorem c_mem_normalizer_Q : c ∈ normalizer (Q : Set G) := by
  refine mem_normalizer_iff.2 fun n => ⟨fun h => hS.c_conj_mem_Q h, fun h => ?_⟩
  have e : c * (c * (c * (c * n * c⁻¹) * c⁻¹) * c⁻¹) * c⁻¹ =
      (c * c * (c * c)) * n * (c * c * (c * c))⁻¹ := by group
  rw [hS.shape.c_mul_c_mul_c_mul_c, one_mul, inv_one, mul_one] at e
  rw [← e]
  exact hS.c_conj_mem_Q (hS.c_conj_mem_Q (hS.c_conj_mem_Q h))

theorem lin_c (v : V6) : lin ψ c v = toMat 6 6 (reflRows ε v₀) *ᵥ v := by
  rw [hS.rad.lin_eq_iff hS.c_mem_normalizer_Q, hS.data.c_act]

omit hS in
theorem mem_normalizer_E_of {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgt : g * t = t * g) :
    g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_sup hgQ (mem_normalizer_zpowers hgt)

theorem c_mem_normalizer_E : c ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_E_of hS.c_mem_normalizer_Q hS.shape.c_comm

theorem P_le_normalizer_E : P ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_E_of (hS.rad.P_le_normalizer hx)
    (hS.shape.commute_of_mem (hS.rad.P_le_L hx))

theorem TH_le_normalizer_E : U ⊔ zpowers c ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (hS.rad.U_le_P.trans hS.P_le_normalizer_E) (zpowers_le.2 hS.c_mem_normalizer_E)

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
