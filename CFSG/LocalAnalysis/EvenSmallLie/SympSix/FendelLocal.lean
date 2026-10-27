module

public import Mathlib.GroupTheory.Sylow
import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup

theorem isPGroup_zpowers_iff {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (n : X) :
    IsPGroup p (zpowers n) ↔ ∃ k, orderOf n = p ^ k := by
  rw [IsPGroup.iff_card, Nat.card_zpowers]

theorem fendel_mem_sylow_of_normalizer {X : Type*} [Group X] {p : ℕ} (P : Sylow p X) {n : X}
    (hn : n ∈ normalizer (P : Set X)) (hp : IsPGroup p (zpowers n)) : n ∈ P := by
  have h := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' hp (zpowers_le.2 hn))
    le_sup_left
  have hm : n ∈ (P : Subgroup X) ⊔ zpowers n := mem_sup_right (mem_zpowers n)
  rw [h] at hm
  exact hm

theorem not_dvd_index_of_normalizer {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup X} (hQ : IsPGroup p Q)
    (h : ∀ n ∈ normalizer (Q : Set X), (∃ k, orderOf n = p ^ k) → n ∈ Q) : ¬ p ∣ Q.index := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  suffices hPQ : (P : Subgroup X) ≤ Q by
    rw [le_antisymm hQP hPQ]
    exact P.not_dvd_index
  by_contra hne
  have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ Q.subgroupOf P := htop ▸ mem_top _
    exact mem_subgroupOf.1 this
  obtain ⟨n, hnN, hnQ⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  apply hnQ
  rw [mem_subgroupOf]
  refine h n ?_ ?_
  · rw [mem_normalizer_iff] at hnN ⊢
    intro x
    constructor
    · intro hx
      exact mem_subgroupOf.1 ((hnN ⟨x, hQP hx⟩).1 (mem_subgroupOf.2 hx))
    · intro hx
      have hxP : x ∈ (P : Subgroup X) := by
        have h1 : (n : X) * x * (n : X)⁻¹ ∈ (P : Subgroup X) := hQP hx
        have h2 := (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem
          ((P : Subgroup X).inv_mem n.2) h1) n.2
        simpa [mul_assoc] using h2
      exact mem_subgroupOf.1 ((hnN ⟨x, hxP⟩).2 (mem_subgroupOf.2 hx))
  · obtain ⟨k, hk⟩ := (isPGroup_zpowers_iff n).1 (P.isPGroup'.to_subgroup (zpowers n))
    exact ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩

theorem exists_conj_sylow_iff {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p X) :
    ∃ g : X, ∀ y : X, y ∈ (Q : Subgroup X) ↔ g⁻¹ * y * g ∈ (P : Subgroup X) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨g, fun y => ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem fendel_mul_self_eq_one {X : Type*} [Group X] {x : X} (h : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem fendel_ne_one {X : Type*} [Group X] {x : X} (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  omega

theorem fendel_orderOf_conj {X : Type*} [Group X] (g x : X) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) x
  simpa using h

theorem fendel_orderOf_conj' {X : Type*} [Group X] (g x : X) :
    orderOf (g⁻¹ * x * g) = orderOf x := by
  simpa using fendel_orderOf_conj g⁻¹ x

structure FendelLocalData (C0 : Type*) [Group C0] (z a t0 : C0) : Prop where
  z_central : ∀ x : C0, x * z = z * x
  orderOf_z : orderOf z = 2
  orderOf_a : orderOf a = 2
  orderOf_t0 : orderOf t0 = 2
  t0_ne_z : t0 ≠ z
  noncomm : ¬ ∀ x y : C0, x * y = y * x
  involutions : ∀ y : C0, orderOf y = 2 → y = z ∨ IsConj a y ∨ IsConj t0 y
  sylow : ∃ T : Subgroup C0, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ z ∈ T ∧
    ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = z
  conj_t0 : IsConj t0 (z * t0)
  sq_z : ∃ k : C0, k * t0 = t0 * k ∧ k * k = z
  not_sq_t0 : ∀ k : C0, k * t0 = t0 * k → k * k ≠ t0
  sylow_t0 : ∃ R : Subgroup C0, R ≤ centralizer {t0} ∧ IsPGroup 2 R ∧
    ¬ 2 ∣ (R.subgroupOf (centralizer {t0})).index ∧ z ∈ R ∧ t0 ∈ R ∧
    ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = z ∨ x = t0 ∨ x = z * t0

section Theta

variable {C0 : Type*} [Group C0] {G : Type*} [Group G] {s : G}
  (θ : C0 ≃* centralizer ({s} : Set G))

@[expose] def fendelHom : C0 →* G := (centralizer ({s} : Set G)).subtype.comp θ.toMonoidHom

theorem fendelHom_apply (x : C0) : fendelHom θ x = (θ x : G) := rfl

theorem fendelHom_injective : Function.Injective (fendelHom θ) := fun _ _ h =>
  θ.injective (Subtype.ext h)

theorem fendel_comm_s (x : C0) : (θ x : G) * s = s * θ x :=
  mem_centralizer_singleton_iff.1 (θ x).2

theorem fendel_exists_eq {g : G} (hg : g * s = s * g) : ∃ x : C0, (θ x : G) = g :=
  ⟨θ.symm ⟨g, mem_centralizer_singleton_iff.2 hg⟩, by simp⟩

theorem fendel_mul (x y : C0) : (θ (x * y) : G) = θ x * θ y := by simp

theorem fendel_inv (x : C0) : (θ x⁻¹ : G) = (θ x : G)⁻¹ := by simp

theorem fendel_inj {x y : C0} (h : (θ x : G) = θ y) : x = y :=
  fendelHom_injective θ h

theorem fendel_orderOf (x : C0) : orderOf (θ x : G) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem fendel_comm_iff (x y : C0) : (θ x : G) * θ y = θ y * θ x ↔ x * y = y * x := by
  rw [← fendel_mul, ← fendel_mul]
  exact ⟨fun h => fendel_inj θ h, fun h => by rw [h]⟩

theorem fendel_conj (c x : C0) :
    (θ (c * x * c⁻¹) : G) = (θ c : G) * (θ x : G) * (θ c : G)⁻¹ := by simp

theorem fendel_isConj {x y : C0} (h : IsConj x y) : IsConj (θ x : G) (θ y) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨θ c, by rw [← fendel_conj, hc]⟩

theorem fendel_mem_map {R : Subgroup C0} {x : C0} :
    (θ x : G) ∈ R.map (fendelHom θ) ↔ x ∈ R :=
  (mem_map_iff_mem (fendelHom_injective θ)).trans Iff.rfl

end Theta

section Local

variable {C0 : Type*} [Group C0] {z a t0 : C0} {G : Type} [Group G] {s : G}
  (θ : C0 ≃* centralizer ({s} : Set G))

theorem fendel_s_sq (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) : s * s = 1 := by
  rw [← hθ, ← fendel_mul, fendel_mul_self_eq_one hD.orderOf_z]
  simp

theorem fendel_s_ne_one (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) : s ≠ 1 := by
  intro h
  exact fendel_ne_one hD.orderOf_z (θ.injective (Subtype.ext ((hθ.trans h).trans (by simp))))

theorem fendel_orderOf_s (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    orderOf s = 2 := by
  rw [← hθ, fendel_orderOf, hD.orderOf_z]

theorem fendel_t1_ne_s (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    (θ t0 : G) ≠ s := fun h => hD.t0_ne_z (fendel_inj θ (h.trans hθ.symm))

theorem fendel_t1_sq (hD : FendelLocalData C0 z a t0) : (θ t0 : G) * θ t0 = 1 := by
  rw [← fendel_mul, fendel_mul_self_eq_one hD.orderOf_t0]
  simp

theorem fendel_orderOf_t1 (hD : FendelLocalData C0 z a t0) : orderOf (θ t0 : G) = 2 := by
  rw [fendel_orderOf, hD.orderOf_t0]

theorem fendel_not_conj_mul (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) {h : G}
    (hh : h * θ t0 = θ t0 * h) : h * s * h⁻¹ ≠ s * θ t0 := by
  intro hhs
  obtain ⟨c, hc⟩ := isConj_iff.1 hD.conj_t0
  obtain ⟨k, hkt, hkz⟩ := hD.sq_z
  have hs2 := fendel_s_sq θ hD hθ
  have ht2 := fendel_t1_sq θ hD
  set t1 : G := (θ t0 : G) with ht1
  set v : G := (θ c : G) with hv
  have hvs : v * s = s * v := fendel_comm_s θ c
  have hvt : v * t1 * v⁻¹ = s * t1 := by
    rw [ht1, hv, ← fendel_conj, hc, fendel_mul, hθ]
  set u : G := v⁻¹ * h with hu
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hus : u * s * u⁻¹ = t1 := by
    calc u * s * u⁻¹ = v⁻¹ * (h * s * h⁻¹) * v := by rw [hu]; group
      _ = v⁻¹ * (s * t1) * v := by rw [hhs]
      _ = t1 := by rw [← hvt]; group
  have hvt' : v⁻¹ * t1 * v = s * t1 := by
    have e1 : s * (v⁻¹ * t1 * v) = t1 := by
      calc s * (v⁻¹ * t1 * v) = v⁻¹ * (s * t1) * v := by
            rw [show s * (v⁻¹ * t1 * v) = (s * v⁻¹) * t1 * v by group,
              show s * v⁻¹ = v⁻¹ * s by
                rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hvs, ← mul_assoc, inv_mul_cancel,
                  one_mul]]
            group
        _ = t1 := by rw [← hvt]; group
    calc v⁻¹ * t1 * v = s⁻¹ * (s * (v⁻¹ * t1 * v)) := by group
      _ = s * t1 := by rw [e1, hsinv]
  have hut : u * t1 * u⁻¹ = s * t1 := by
    calc u * t1 * u⁻¹ = v⁻¹ * (h * t1 * h⁻¹) * v := by rw [hu]; group
      _ = v⁻¹ * t1 * v := by rw [hh, mul_inv_cancel_right]
      _ = s * t1 := hvt'
  set φ := MulAut.conj u with hφ
  have hφs : φ s = t1 := by rw [hφ, MulAut.conj_apply, hus]
  have hφt : φ t1 = s * t1 := by rw [hφ, MulAut.conj_apply, hut]
  set w : G := φ (θ k) with hw
  have hks : (θ k : G) * s = s * θ k := fendel_comm_s θ k
  have hkt' : (θ k : G) * t1 = t1 * θ k := (fendel_comm_iff θ k t0).2 hkt
  have hw2 : w * w = t1 := by
    rw [hw, ← map_mul, ← fendel_mul, hkz, hθ, hφs]
  have hwt : w * t1 = t1 * w := by
    rw [hw, ← hφs, ← map_mul, ← map_mul, hks]
  have hwst : w * (s * t1) = (s * t1) * w := by
    rw [hw, ← hφt, ← map_mul, ← map_mul, hkt']
  have hws : w * s = s * w := by
    have e : s = (s * t1) * t1 := by rw [mul_assoc, ht2, mul_one]
    calc w * s = w * (s * t1) * t1 := by rw [mul_assoc, ← e]
      _ = (s * t1) * w * t1 := by rw [hwst]
      _ = (s * t1) * t1 * w := by rw [mul_assoc, hwt, ← mul_assoc]
      _ = s * w := by rw [← e]
  obtain ⟨k', hk'⟩ := fendel_exists_eq θ hws
  have h1 : k' * t0 = t0 * k' := (fendel_comm_iff θ k' t0).1 (by rw [hk']; exact hwt)
  have h2 : k' * k' = t0 := fendel_inj θ (by rw [fendel_mul, hk']; exact hw2)
  exact hD.not_sq_t0 k' h1 h2

theorem fendel_sylow_aux [Finite C0] [Finite G] (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) {T : Subgroup C0} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hzT : z ∈ T) (hTc : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = z) :
    ¬ 2 ∣ (T.map (fendelHom θ)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_dvd_index_of_normalizer (hT.map _) fun n hn hnp => ?_
  rw [mem_normalizer_iff] at hn
  have hsT : s ∈ T.map (fendelHom θ) := by
    have h := (fendel_mem_map θ).2 hzT
    rwa [hθ] at h
  have hnsT := (hn s).1 hsT
  obtain ⟨x, hxT, hx⟩ := mem_map.1 hnsT
  rw [fendelHom_apply] at hx
  have hxc : ∀ y ∈ T, x * y = y * x := by
    intro y hy
    have hy' : (θ y : G) ∈ T.map (fendelHom θ) := (fendel_mem_map θ).2 hy
    have hny : n⁻¹ * θ y * n ∈ T.map (fendelHom θ) := (hn _).2 (by group; exact hy')
    obtain ⟨y', hy'T, hyy⟩ := mem_map.1 hny
    rw [fendelHom_apply] at hyy
    have hcs : (θ y' : G) * s = s * θ y' := fendel_comm_s θ y'
    rw [hyy] at hcs
    rw [← fendel_comm_iff θ, hx]
    calc n * s * n⁻¹ * θ y = n * (s * (n⁻¹ * θ y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * θ y * n) * s) * n⁻¹ := by rw [hcs]
      _ = θ y * (n * s * n⁻¹) := by group
  have hns : n * s * n⁻¹ = s := by
    rcases hTc x hxT hxc with rfl | rfl
    · exfalso
      apply fendel_s_ne_one θ hD hθ
      have : n * s * n⁻¹ = 1 := by rw [← hx]; simp
      rw [mul_inv_eq_one] at this
      exact mul_eq_left.1 this
    · rw [← hx, hθ]
  obtain ⟨m, hm⟩ := fendel_exists_eq θ (show n * s = s * n by
    rw [← mul_inv_eq_iff_eq_mul, hns])
  have hmN : m ∈ normalizer (T : Set C0) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← fendel_mem_map θ (R := T), ← fendel_mem_map θ (R := T), fendel_conj, hm, hn]
  have hmp : IsPGroup 2 (zpowers m) := by
    rw [isPGroup_zpowers_iff, ← fendel_orderOf θ, hm]
    exact hnp
  have hmT := fendel_mem_sylow_of_normalizer (hT.toSylow hTi) (by exact hmN) hmp
  rw [← hm]
  exact (fendel_mem_map θ).2 (by rwa [IsPGroup.mem_toSylow] at hmT)

end Local

theorem fendel_card_centralizer_conj {X : Type*} [Group X] (c x : X) :
    Nat.card (centralizer ({c * x * c⁻¹} : Set X)) = Nat.card (centralizer ({x} : Set X)) := by
  refine Nat.card_congr ⟨fun y => ⟨c⁻¹ * y * c, ?_⟩, fun y => ⟨c * y * c⁻¹, ?_⟩, ?_, ?_⟩
  · have h := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * ↑y * c * x = c⁻¹ * (↑y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * ↑y) * c := by rw [h]
      _ = x * (c⁻¹ * ↑y * c) := by group
  · have h := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc c * ↑y * c⁻¹ * (c * x * c⁻¹) = c * (↑y * x) * c⁻¹ := by group
      _ = c * (x * ↑y) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * (c * ↑y * c⁻¹) := by group
  · intro y
    apply Subtype.ext
    simp only
    group
  · intro y
    apply Subtype.ext
    simp only
    group

section Main

variable {C0 : Type*} [Group C0] [Finite C0] {z a t0 : C0} {G : Type} [Group G] [Finite G]
  {s : G} (θ : C0 ≃* centralizer ({s} : Set G))

theorem fendel_sylow (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    ∃ T : Subgroup C0, z ∈ T ∧ (∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = z) ∧
      ∃ S : Sylow 2 G, (S : Subgroup G) = T.map (fendelHom θ) := by
  obtain ⟨T, hT, hTi, hzT, hTc⟩ := hD.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨T, hzT, hTc, (hT.map _).toSylow (fendel_sylow_aux θ hD hθ hT hTi hzT hTc),
    IsPGroup.toSylow_coe _ _⟩

omit [Finite C0] in
theorem fendel_not_isolated (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) {T : Subgroup C0} (hzT : z ∈ T) (S : Sylow 2 G)
    (hS : (S : Subgroup G) = T.map (fendelHom θ)) :
    ∃ g : G, g⁻¹ * s * g ∈ (S : Subgroup G) ∧ g⁻¹ * s * g ≠ s := by
  by_contra hcon
  push Not at hcon
  have hsS : s ∈ (S : Subgroup G) := by
    rw [hS]
    have h := (fendel_mem_map θ).2 hzT
    rwa [hθ] at h
  set z' : (S : Subgroup G) := ⟨s, hsS⟩ with hz'
  have hzZ : z' ∈ center (S : Subgroup G) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : G) ∈ T.map (fendelHom θ) := hS ▸ g.2
    obtain ⟨x, -, hx⟩ := mem_map.1 hg
    rw [fendelHom_apply] at hx
    show (g : G) * s = s * g
    rw [← hx]
    exact fendel_comm_s θ x
  have hzo : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact fendel_orderOf_s θ hD hθ
  obtain ⟨hfac, -⟩ := CFSG.Milestones.glauberman_zStar_central_sylow_involution S z' hzZ hzo hcon
  have hcore : CFSG.oddCore G = ⊥ := by
    rcases hG.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      have hne : CFSG.oddCore G ≠ ⊥ := by rw [h]; exact top_ne_bot
      obtain ⟨N, ⟨hN, hNodd⟩, hNb⟩ :
          ∃ N ∈ {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}, N ≠ ⊥ := by
        by_contra hall
        push Not at hall
        exact hne (sSup_eq_bot.2 hall)
      rcases hG.eq_bot_or_eq_top_of_normal N with h' | h'
      · exact hNb h'
      · rw [h', Subgroup.card_top] at hNodd
        have h2 : 2 ∣ Nat.card G := fendel_orderOf_s θ hD hθ ▸ orderOf_dvd_natCard s
        exact Nat.not_even_iff_odd.2 hNodd (even_iff_two_dvd.2 h2)
  have hcen : ∀ g : G, g * s = s * g := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
    rw [hcore, mem_bot] at hk
    rw [hk, mul_one]
    exact mem_centralizer_singleton_iff.1 hc
  have hZ : center G = ⊤ := by
    rcases hG.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exfalso
      have hsZ : s ∈ center G := mem_center_iff.2 hcen
      rw [h, mem_bot] at hsZ
      exact fendel_s_ne_one θ hD hθ hsZ
    · exact h
  apply hD.noncomm
  intro x y
  have hx : (θ x : G) ∈ center G := hZ ▸ mem_top _
  exact (fendel_comm_iff θ x y).1 (mem_center_iff.1 hx (θ y)).symm

theorem fendel_sylow_H_aux (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s)
    {R : Subgroup C0} (hRt : R ≤ centralizer {t0}) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (centralizer {t0})).index) (hzR : z ∈ R)
    (hRc : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = z ∨ x = t0 ∨ x = z * t0) :
    R.map (fendelHom θ) ≤ centralizer {(θ t0 : G)} ∧
      IsPGroup 2 ((R.map (fendelHom θ)).subgroupOf (centralizer {(θ t0 : G)})) ∧
      ¬ 2 ∣ ((R.map (fendelHom θ)).subgroupOf (centralizer {(θ t0 : G)})).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({(θ t0 : G)} : Set G) with hH
  set RG := R.map (fendelHom θ) with hRG
  have hRH : RG ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [fendelHom_apply, hH, mem_centralizer_singleton_iff, fendel_comm_iff]
    exact mem_centralizer_singleton_iff.1 (hRt hx)
  have hRGp : IsPGroup 2 (RG.subgroupOf H) := (hR.map _).of_equiv (subgroupOfEquivOfLe hRH).symm
  refine ⟨hRH, hRGp, not_dvd_index_of_normalizer hRGp fun n hn hnp => ?_⟩
  rw [mem_normalizer_iff] at hn
  have hnG : ∀ y : G, y ∈ RG → (n : G) * y * (n : G)⁻¹ ∈ RG := by
    intro y hy
    have h1 := (hn ⟨y, hRH hy⟩).1 (mem_subgroupOf.2 hy)
    exact mem_subgroupOf.1 h1
  have hnG' : ∀ y : G, y ∈ RG → (n : G)⁻¹ * y * (n : G) ∈ RG := by
    intro y hy
    have hy' : (n : G)⁻¹ * y * (n : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem n.2) (hRH hy)) n.2
    have h1 := (hn ⟨_, hy'⟩).2 (mem_subgroupOf.2 (by
      show (n : G) * ((n : G)⁻¹ * y * (n : G)) * (n : G)⁻¹ ∈ RG
      group
      exact hy))
    exact mem_subgroupOf.1 h1
  have hsR : s ∈ RG := by
    have h := (fendel_mem_map θ).2 hzR
    rwa [hθ] at h
  obtain ⟨x, hxR, hx⟩ := mem_map.1 (hnG s hsR)
  rw [fendelHom_apply] at hx
  have hxc : ∀ y ∈ R, x * y = y * x := by
    intro y hy
    obtain ⟨y', -, hyy⟩ := mem_map.1 (hnG' _ ((fendel_mem_map θ).2 hy))
    rw [fendelHom_apply] at hyy
    have hcs : (θ y' : G) * s = s * θ y' := fendel_comm_s θ y'
    rw [hyy] at hcs
    rw [← fendel_comm_iff θ, hx]
    calc (n : G) * s * (n : G)⁻¹ * θ y = n * (s * ((n : G)⁻¹ * θ y * n)) * (n : G)⁻¹ := by group
      _ = n * (((n : G)⁻¹ * θ y * n) * s) * (n : G)⁻¹ := by rw [hcs]
      _ = θ y * ((n : G) * s * (n : G)⁻¹) := by group
  have hnt : (n : G) * θ t0 * (n : G)⁻¹ = θ t0 := by
    rw [mem_centralizer_singleton_iff.1 n.2, mul_inv_cancel_right]
  have hns : (n : G) * s * (n : G)⁻¹ = s := by
    rcases hRc x hxR hxc with rfl | rfl | rfl | rfl
    · exfalso
      apply fendel_s_ne_one θ hD hθ
      have : (n : G) * s * (n : G)⁻¹ = 1 := by rw [← hx]; simp
      rw [mul_inv_eq_one] at this
      exact mul_eq_left.1 this
    · rw [← hx, hθ]
    · exfalso
      apply fendel_t1_ne_s θ hD hθ
      have h1 : (n : G) * s * (n : G)⁻¹ = (n : G) * θ x * (n : G)⁻¹ := by rw [← hx, hnt]
      simpa using h1.symm
    · exfalso
      exact fendel_not_conj_mul θ hD hθ (mem_centralizer_singleton_iff.1 n.2)
        (by rw [← hx, fendel_mul, hθ])
  obtain ⟨m, hm⟩ := fendel_exists_eq θ (show (n : G) * s = s * n by
    rw [← mul_inv_eq_iff_eq_mul, hns])
  have hmt : m * t0 = t0 * m := by
    rw [← fendel_comm_iff θ, hm]
    exact mem_centralizer_singleton_iff.1 n.2
  set K := centralizer ({t0} : Set C0) with hK
  have hmK : m ∈ K := mem_centralizer_singleton_iff.2 hmt
  have hRKp : IsPGroup 2 (R.subgroupOf K) := hR.of_equiv (subgroupOfEquivOfLe hRt).symm
  have hmN : (⟨m, hmK⟩ : K) ∈ normalizer ((hRKp.toSylow hRi : Subgroup K) : Set K) := by
    show (⟨m, hmK⟩ : K) ∈ normalizer ((R.subgroupOf K : Subgroup K) : Set K)
    rw [mem_normalizer_iff]
    intro y
    rw [mem_subgroupOf, mem_subgroupOf]
    show (y : C0) ∈ R ↔ m * y * m⁻¹ ∈ R
    have hyH : (θ y : G) ∈ H := by
      rw [hH, mem_centralizer_singleton_iff, fendel_comm_iff]
      exact mem_centralizer_singleton_iff.1 y.2
    have h1 := hn ⟨θ y, hyH⟩
    rw [mem_subgroupOf, mem_subgroupOf] at h1
    rw [← fendel_mem_map θ (R := R), ← fendel_mem_map θ (R := R), fendel_conj, hm]
    exact h1
  have hmp : IsPGroup 2 (zpowers (⟨m, hmK⟩ : K)) := by
    rw [isPGroup_zpowers_iff, ← Subgroup.orderOf_coe]
    show ∃ k, orderOf m = 2 ^ k
    rw [← fendel_orderOf θ, hm, Subgroup.orderOf_coe]
    exact hnp
  have hmR := fendel_mem_sylow_of_normalizer (hRKp.toSylow hRi) hmN hmp
  rw [IsPGroup.mem_toSylow, mem_subgroupOf] at hmR
  rw [mem_subgroupOf, ← hm]
  exact (fendel_mem_map θ).2 hmR

theorem fendel_sylow_H (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    ∃ R : Subgroup C0, R ≤ centralizer {t0} ∧ IsPGroup 2 R ∧
      ¬ 2 ∣ (R.subgroupOf (centralizer {t0})).index ∧ z ∈ R ∧ t0 ∈ R ∧
      (∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1 ∨ x = z ∨ x = t0 ∨ x = z * t0) ∧
      R.map (fendelHom θ) ≤ centralizer {(θ t0 : G)} ∧
      ∃ P : Sylow 2 (centralizer ({(θ t0 : G)} : Set G)),
        (P : Subgroup _) = (R.map (fendelHom θ)).subgroupOf (centralizer {(θ t0 : G)}) := by
  obtain ⟨R, hRt, hR, hRi, hzR, ht0R, hRc⟩ := hD.sylow_t0
  obtain ⟨hRH, hp, hi⟩ := fendel_sylow_H_aux θ hD hθ hRt hR hRi hzR hRc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨R, hRt, hR, hRi, hzR, ht0R, hRc, hRH, hp.toSylow hi, IsPGroup.toSylow_coe _ _⟩

theorem fendel_not_isConj_t1 (hD : FendelLocalData C0 z a t0) (hθ : (θ z : G) = s) :
    ¬ IsConj s (θ t0 : G) := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTi, -, hTc⟩ := hD.sylow
  obtain ⟨R, hRt, hR, hRi, hzR, ht0R, hRc, hRH, P, hP⟩ := fendel_sylow_H θ hD hθ
  obtain ⟨c, hcs⟩ := isConj_iff.1 hc
  have hcardH : Nat.card (centralizer ({(θ t0 : G)} : Set G)) = Nat.card C0 := by
    rw [← hcs, fendel_card_centralizer_conj, Nat.card_congr θ.toEquiv]
  have hcardR : Nat.card R = 2 ^ (Nat.card C0).factorization 2 := by
    have h1 := P.card_eq_multiplicity
    rw [hP, hcardH, Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,
      card_map_of_injective (fendelHom_injective θ)] at h1
    exact h1
  let RS : Sylow 2 C0 := Sylow.ofCard R hcardR
  obtain ⟨g, hg⟩ := exists_conj_sylow_iff (hT.toSylow hTi) RS
  have hgt : g⁻¹ * t0 * g ∈ T := by
    have h1 := (hg t0).1 (by rw [Sylow.coe_ofCard]; exact ht0R)
    rwa [IsPGroup.toSylow_coe] at h1
  have hgc : ∀ y ∈ T, g⁻¹ * t0 * g * y = y * (g⁻¹ * t0 * g) := by
    intro y hy
    have hy' : g * y * g⁻¹ ∈ R := by
      have h1 := (hg (g * y * g⁻¹)).2 (by rw [IsPGroup.toSylow_coe]; group; exact hy)
      rwa [Sylow.coe_ofCard] at h1
    have h2 := mem_centralizer_singleton_iff.1 (hRt hy')
    calc g⁻¹ * t0 * g * y = g⁻¹ * (t0 * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * t0) * g := by rw [h2]
      _ = y * (g⁻¹ * t0 * g) := by group
  rcases hTc _ hgt hgc with h | h
  · apply fendel_ne_one hD.orderOf_t0
    calc t0 = g * (g⁻¹ * t0 * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · apply hD.t0_ne_z
    calc t0 = g * (g⁻¹ * t0 * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [h]
      _ = z := by rw [hD.z_central g, mul_inv_cancel_right]

theorem fendel_isConj_a (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) : IsConj s (θ a : G) := by
  obtain ⟨T, hzT, -, S, hS⟩ := fendel_sylow θ hD hθ
  obtain ⟨g, hgS, hgs⟩ := fendel_not_isolated θ hG hD hθ hzT S hS
  rw [hS] at hgS
  obtain ⟨y, -, hy⟩ := mem_map.1 hgS
  rw [fendelHom_apply] at hy
  have hsy : IsConj s (θ y : G) := by
    rw [hy]
    exact isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩
  have hyo : orderOf y = 2 := by
    rw [← fendel_orderOf θ, hy, fendel_orderOf_conj', fendel_orderOf_s θ hD hθ]
  rcases hD.involutions y hyo with rfl | h | h
  · exact absurd (hy.symm.trans hθ) hgs
  · exact hsy.trans (isConj_comm.1 (fendel_isConj θ h))
  · exact absurd (hsy.trans (isConj_comm.1 (fendel_isConj θ h)))
      (fendel_not_isConj_t1 θ hD hθ)

theorem fendel_fusion (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) (x : C0) (hx : orderOf x = 2) :
    IsConj s (θ x : G) ↔ x = z ∨ IsConj a x := by
  constructor
  · intro h
    rcases hD.involutions x hx with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (h.trans (isConj_comm.1 (fendel_isConj θ h'))) (fendel_not_isConj_t1 θ hD hθ)
  · rintro (rfl | h)
    · rw [hθ]
    · exact (fendel_isConj_a θ hG hD hθ).trans (fendel_isConj θ h)

theorem fendel_two_classes (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) (w : G) (hw : orderOf w = 2) :
    IsConj s w ∨ IsConj (θ t0 : G) w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, -, S, hS⟩ := fendel_sylow θ hD hθ
  obtain ⟨P, hwP⟩ := ((isPGroup_zpowers_iff w).2 ⟨1, by rw [hw, pow_one]⟩).exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_sylow_iff S P
  have hgw : g⁻¹ * w * g ∈ T.map (fendelHom θ) := by
    rw [← hS]
    exact (hg w).1 (hwP (mem_zpowers w))
  obtain ⟨y, -, hy⟩ := mem_map.1 hgw
  rw [fendelHom_apply] at hy
  have hwy : IsConj (θ y : G) w := by
    rw [hy]
    exact isConj_iff.2 ⟨g, by group⟩
  have hyo : orderOf y = 2 := by
    rw [← fendel_orderOf θ, hy, fendel_orderOf_conj', hw]
  rcases hD.involutions y hyo with rfl | h | h
  · exact Or.inl (by rw [← hθ]; exact hwy)
  · exact Or.inl (((fendel_fusion θ hG hD hθ y hyo).2 (Or.inr h)).trans hwy)
  · exact Or.inr ((fendel_isConj θ h).trans hwy)

theorem fendel_conj_in_H (hG : IsSimpleGroup G) (hD : FendelLocalData C0 z a t0)
    (hθ : (θ z : G) = s) {x : G} (hxt : x * θ t0 = θ t0 * x) (hx : IsConj s x) :
    ∃ h : G, h * θ t0 = θ t0 * h ∧ h * s * h⁻¹ = x := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  set t1 : G := (θ t0 : G) with ht1
  have hts : g⁻¹ * t1 * g * s = s * (g⁻¹ * t1 * g) := by
    have e : s = g⁻¹ * x * g := by rw [← hg]; group
    rw [e]
    calc g⁻¹ * t1 * g * (g⁻¹ * x * g) = g⁻¹ * (t1 * x) * g := by group
      _ = g⁻¹ * (x * t1) * g := by rw [hxt]
      _ = g⁻¹ * x * g * (g⁻¹ * t1 * g) := by group
  obtain ⟨y, hy⟩ := fendel_exists_eq θ hts
  have hyo : orderOf y = 2 := by
    rw [← fendel_orderOf θ, hy, fendel_orderOf_conj', fendel_orderOf_t1 θ hD]
  have hyt : IsConj t1 (θ y : G) := by
    rw [hy]
    exact isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩
  have hy' : ¬ (y = z ∨ IsConj a y) := by
    intro h
    exact fendel_not_isConj_t1 θ hD hθ
      (((fendel_fusion θ hG hD hθ y hyo).2 h).trans (isConj_comm.1 hyt))
  rcases hD.involutions y hyo with h | h | h
  · exact absurd (Or.inl h) hy'
  · exact absurd (Or.inr h) hy'
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine ⟨g * θ c, ?_, ?_⟩
    · have e : (θ c : G) * t1 * (θ c : G)⁻¹ = g⁻¹ * t1 * g := by
        rw [ht1, ← fendel_conj, hc, hy]
      calc g * θ c * t1 = g * ((θ c : G) * t1 * (θ c : G)⁻¹) * θ c := by group
        _ = g * (g⁻¹ * t1 * g) * θ c := by rw [e]
        _ = t1 * (g * θ c) := by group
    · calc g * θ c * s * (g * θ c)⁻¹ = g * ((θ c : G) * s * (θ c : G)⁻¹) * g⁻¹ := by group
        _ = g * s * g⁻¹ := by rw [fendel_comm_s θ c, mul_inv_cancel_right]
        _ = x := hg

end Main

end CFSG.EvenSmallLie.SympSix
