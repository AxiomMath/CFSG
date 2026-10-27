module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQbar

public section

open Subgroup

namespace CFSG.ComponentClassification.RankTwoAltFive

section Points

variable {G : Type*} [Group G]

@[expose] def points (Q : Subgroup G) (z : G) : Set (Subgroup G) :=
  {U | U ≤ Q ∧ z ∈ U ∧ Nat.card U = 4 ∧ ∀ u ∈ U, u * u = 1}

@[expose] def ptOf (z u : G) : Subgroup G := zpowers z ⊔ zpowers u

variable {z u : G}

theorem mem_ptOf (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {y : G} :
    y ∈ ptOf z u ↔ y = 1 ∨ y = z ∨ y = u ∨ y = z * u := by
  have hN : zpowers z ≤ normalizer ((zpowers u : Subgroup G) : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact ((Commute.zpow_right (show Commute z u from hzu) k)).eq.symm))
  constructor
  · intro hy
    have hy' : y ∈ ((zpowers z ⊔ zpowers u : Subgroup G) : Set G) := hy
    rw [coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    have hab' : a * b = y := hab
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_of_sq hu2 hb with rfl | rfl
    · left; rw [← hab', one_mul]
    · right; right; left; rw [← hab', one_mul]
    · right; left; rw [← hab', mul_one]
    · right; right; right; exact hab'.symm
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem mul_not_mem_zpowers (hu : u ∉ zpowers z) : z * u ∉ zpowers z := fun h => hu (by
  have := mul_mem (inv_mem (mem_zpowers z)) h
  rwa [inv_mul_cancel_left] at this)

theorem card_ptOf (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu2 : u * u = 1)
    (hzu : z * u = u * z) (hu : u ∉ zpowers z) : Nat.card (ptOf z u) = 4 := by
  classical
  have hu1 : u ≠ 1 := fun h => hu (h ▸ one_mem _)
  have hzu1 : z * u ≠ 1 := fun h => mul_not_mem_zpowers hu (h ▸ one_mem _)
  have hzu' : z ≠ u := fun h => hu (h ▸ mem_zpowers z)
  have hzzu : z ≠ z * u := fun h => mul_not_mem_zpowers hu (h ▸ mem_zpowers z)
  have huzu : u ≠ z * u := fun h => hz1 (by
    calc z = (z * u) * u⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel])
  have hset : ((ptOf z u : Subgroup G) : Set G) = {1, z, u, z * u} := by
    ext y
    simp only [SetLike.mem_coe, mem_ptOf hz2 hu2 hzu, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [show Nat.card (ptOf z u) = ((ptOf z u : Subgroup G) : Set G).ncard from
    Nat.card_coe_set_eq _, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair huzu]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzu', hzzu⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hz1, Ne.symm hu1, Ne.symm hzu1⟩

theorem ptOf_mem_points {Q : Subgroup G} (hzQ : z ∈ Q) (huQ : u ∈ Q) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hu : u ∉ zpowers z) :
    ptOf z u ∈ points Q z := by
  refine ⟨sup_le (zpowers_le.mpr hzQ) (zpowers_le.mpr huQ), mem_sup_left (mem_zpowers z),
    card_ptOf hz2 hz1 hu2 hzu hu, fun y hy => ?_⟩
  rcases (mem_ptOf hz2 hu2 hzu).mp hy with h | h | h | h <;> rw [h]
  · exact mul_one 1
  · exact hz2
  · exact hu2
  · rw [show z * u * (z * u) = z * (u * z) * u by group, ← hzu,
      show z * (z * u) * u = z * z * (u * u) by group, hz2, hu2, mul_one]

theorem eq_ptOf_of_mem_points {Q U : Subgroup G} (hU : U ∈ points Q z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (huU : u ∈ U) (hu : u ∉ zpowers z) : U = ptOf z u := by
  obtain ⟨-, hzU, hU4, hU2⟩ := hU
  have hu2 := hU2 u huU
  have hzu : z * u = u * z := by
    have h1 := mul_eq_one_iff_eq_inv.mp (hU2 _ (mul_mem hzU huU))
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right hz2] at h1
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hU4]; norm_num)
  exact (eq_of_le_of_card_ge (show ptOf z u ≤ U from sup_le (zpowers_le.mpr hzU)
    (zpowers_le.mpr huU)) (le_of_eq (by rw [hU4, card_ptOf hz2 hz1 hu2 hzu hu]))).symm

theorem card_points [Finite G] {Q : Subgroup G} (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ q ∈ Q, z * q = q * z) :
    Nat.card {y : Q // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} = 2 * Nat.card (points Q z) := by
  classical
  have : Fintype (points Q z) := Fintype.ofFinite _
  set f : {y : Q // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} → points Q z := fun y =>
    ⟨ptOf z y, ptOf_mem_points hzQ y.1.2 hz2 hz1 y.2.1 (hzc _ y.1.2) y.2.2⟩ with hf
  have hfib : ∀ U : points Q z, Nat.card {y // f y = U} = 2 := by
    intro U
    obtain ⟨hUQ, hzU, hU4, hU2⟩ := U.2
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ (U : Subgroup G), u ∉ zpowers z := by
      by_contra hno
      push Not at hno
      have h1 := card_le_of_le (show (U : Subgroup G) ≤ zpowers z from hno)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [hU4, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hz2) hz1] at h1
      omega
    have hzuU : z * u ∈ (U : Subgroup G) := mul_mem hzU huU
    have hzu' := mul_not_mem_zpowers hu
    have hne : u ≠ z * u := fun h => hz1 (by
      calc z = z * u * u⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel])
    set g : Bool → {y // f y = U} := fun b => if b then
      ⟨⟨⟨u, hUQ huU⟩, hU2 u huU, hu⟩, Subtype.ext (eq_ptOf_of_mem_points U.2 hz2 hz1 huU hu).symm⟩
      else ⟨⟨⟨z * u, hUQ hzuU⟩, hU2 _ hzuU, hzu'⟩,
        Subtype.ext (eq_ptOf_of_mem_points U.2 hz2 hz1 hzuU hzu').symm⟩ with hg
    have hbij : Function.Bijective g := by
      refine ⟨fun a b hab => ?_, fun y => ?_⟩
      · have h1 := congrArg (fun y : {y // f y = U} => ((y.1.1 : Q) : G)) hab
        cases a <;> cases b <;> simp only [hg, Bool.false_eq_true, ite_false, ite_true] at h1
        · rfl
        · exact absurd h1.symm hne
        · exact absurd h1 hne
        · rfl
      · obtain ⟨y₀, hy₀⟩ := y
        have hy : ptOf z ((y₀.1 : Q) : G) = (U : Subgroup G) := congrArg Subtype.val hy₀
        have hyU : ((y₀.1 : Q) : G) ∈ (U : Subgroup G) := by
          rw [← hy]
          exact mem_sup_right (mem_zpowers _)
        rw [eq_ptOf_of_mem_points U.2 hz2 hz1 huU hu,
          mem_ptOf hz2 (hU2 u huU) (hzc u (hUQ huU))] at hyU
        rcases hyU with h1 | h1 | h1 | h1
        · exact (y₀.2.2 (by rw [h1]; exact one_mem _)).elim
        · exact (y₀.2.2 (by rw [h1]; exact mem_zpowers z)).elim
        · exact ⟨true, Subtype.ext (Subtype.ext (Subtype.ext h1.symm))⟩
        · exact ⟨false, Subtype.ext (Subtype.ext (Subtype.ext h1.symm))⟩
    rw [← Nat.card_eq_of_bijective g hbij, Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    Finset.sum_congr rfl fun U _ => hfib U, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := points Q z), mul_comm]

end Points

section Action

variable {G : Type*} [Group G] {Q H : Subgroup G} {z : G}

theorem map_conj_mul (a b : G) (U : Subgroup G) :
    U.map (MulAut.conj (a * b)).toMonoidHom =
      (U.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  ext y
  simp only [mem_map_equiv, MulAut.conj_symm_apply]
  rw [show (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b by group]

theorem map_conj_one (U : Subgroup G) : U.map (MulAut.conj (1 : G)).toMonoidHom = U := by
  ext y
  simp only [mem_map_equiv, MulAut.conj_symm_apply, inv_one, one_mul, mul_one]

theorem map_conj_mem_points {h : G} (hhQ : h ∈ normalizer (Q : Set G))
    (hhz : h ∈ centralizer ({z} : Set G)) {U : Subgroup G} (hU : U ∈ points Q z) :
    U.map (MulAut.conj h).toMonoidHom ∈ points Q z := by
  obtain ⟨hUQ, hzU, hU4, hU2⟩ := hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.mp hhQ u).mp (hUQ hu)
  · rw [mem_map_equiv, MulAut.conj_symm_apply, mul_assoc,
      ← mem_centralizer_singleton_iff.mp hhz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzU
  · rw [card_map_of_injective (MulEquiv.injective _), hU4]
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show h * u * h⁻¹ * (h * u * h⁻¹) = h * (u * u) * h⁻¹ by group, hU2 u hu, mul_one,
      mul_inv_cancel]

@[expose] def ptAction (hHQ : H ≤ normalizer (Q : Set G)) (hHz : H ≤ centralizer ({z} : Set G)) :
    ↥H →* Equiv.Perm (points Q z) where
  toFun h :=
    { toFun := fun U => ⟨U.1.map (MulAut.conj (h : G)).toMonoidHom,
        map_conj_mem_points (hHQ h.2) (hHz h.2) U.2⟩
      invFun := fun U => ⟨U.1.map (MulAut.conj (h : G)⁻¹).toMonoidHom,
        map_conj_mem_points (inv_mem (hHQ h.2)) (inv_mem (hHz h.2)) U.2⟩
      left_inv := fun U => Subtype.ext (by
        dsimp only
        rw [← map_conj_mul, inv_mul_cancel, map_conj_one])
      right_inv := fun U => Subtype.ext (by
        dsimp only
        rw [← map_conj_mul, mul_inv_cancel, map_conj_one]) }
  map_one' := Equiv.ext fun U => by
    rw [Equiv.Perm.one_apply]
    exact Subtype.ext (map_conj_one U.1)
  map_mul' a b := Equiv.ext fun U => by
    rw [Equiv.Perm.mul_apply]
    exact Subtype.ext (map_conj_mul (a : G) (b : G) U.1)

theorem ptAction_apply (hHQ : H ≤ normalizer (Q : Set G)) (hHz : H ≤ centralizer ({z} : Set G))
    (h : H) (U : points Q z) :
    ((ptAction hHQ hHz h U : points Q z) : Subgroup G) =
      (U : Subgroup G).map (MulAut.conj (h : G)).toMonoidHom :=
  rfl

theorem ptAction_eq_one (hHQ : H ≤ normalizer (Q : Set G)) (hHz : H ≤ centralizer ({z} : Set G))
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {h : H} (hh : (h : G) ∈ Q) :
    ptAction hHQ hHz h = 1 := by
  refine Equiv.ext fun U => Subtype.ext ?_
  rw [ptAction_apply, Equiv.Perm.one_apply]
  obtain ⟨hUQ, hzU, -, -⟩ := U.2
  have hzU' : zpowers z ≤ (U : Subgroup G) := zpowers_le.mpr hzU
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro hy
    have hc := hzU' (hcomm _ hh _ (hUQ hy))
    have := mul_mem hc hy
    rwa [show (h : G) * ((h : G)⁻¹ * y * h) * (h : G)⁻¹ * ((h : G)⁻¹ * y * h)⁻¹ *
      ((h : G)⁻¹ * y * h) = y by group] at this
  · intro hy
    have hc := hzU' (hcomm _ (inv_mem hh) _ (hUQ hy))
    have := mul_mem hc hy
    rwa [inv_inv, show (h : G)⁻¹ * y * h * y⁻¹ * y = (h : G)⁻¹ * y * h by group] at this

variable (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ q ∈ Q, z * q = q * z)
include hzQ hz2 hz1 hzc

theorem conj_eq_or_of_ptAction_eq_one (hHQ : H ≤ normalizer (Q : Set G))
    (hHz : H ≤ centralizer ({z} : Set G)) {h : H} (hh : ptAction hHQ hHz h = 1) {u : G}
    (huQ : u ∈ Q) (hu2 : u * u = 1) (hu : u ∉ zpowers z) :
    (h : G) * u * (h : G)⁻¹ = u ∨ (h : G) * u * (h : G)⁻¹ = z * u := by
  have h1 := congrArg Subtype.val
    (Equiv.ext_iff.mp hh ⟨ptOf z u, ptOf_mem_points hzQ huQ hz2 hz1 hu2 (hzc u huQ) hu⟩)
  simp only [ptAction_apply, Equiv.Perm.one_apply] at h1
  have h2 : (h : G) * u * (h : G)⁻¹ ∈ ptOf z u := by
    rw [← h1]
    exact ⟨u, mem_sup_right (mem_zpowers u), rfl⟩
  have hhz : (h : G) * z = z * h := mem_centralizer_singleton_iff.mp (hHz h.2)
  rcases (mem_ptOf hz2 hu2 (hzc u huQ)).mp h2 with h3 | h3 | h3 | h3
  · refine absurd ?_ hu
    rw [show u = (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) * h by group, h3]
    simp
  · refine absurd ?_ hu
    rw [show u = (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) * h by group, h3, mul_assoc,
      ← hhz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact mem_zpowers z
  · exact Or.inl h3
  · exact Or.inr h3

theorem commute_of_ptAction_eq_one (hHQ : H ≤ normalizer (Q : Set G))
    (hHz : H ≤ centralizer ({z} : Set G)) {h : H} (hh : ptAction hHQ hHz h = 1)
    (hodd : Odd (orderOf (h : G))) {u : G} (huQ : u ∈ Q) (hu2 : u * u = 1)
    (hu : u ∉ zpowers z) : (h : G) * u = u * h := by
  set g : G := (h : G) with hgdef
  have hgz : g * z = z * g := mem_centralizer_singleton_iff.mp (hHz h.2)
  have hsq : Commute (g * g) u := by
    rcases conj_eq_or_of_ptAction_eq_one hzQ hz2 hz1 hzc hHQ hHz hh huQ hu2 hu with h1 | h1
    · have hc : Commute g u := by
        show g * u = u * g
        calc g * u = g * u * g⁻¹ * g := by group
          _ = u * g := by rw [h1]
      exact hc.mul_left hc
    · show g * g * u = u * (g * g)
      calc g * g * u = g * (g * u * g⁻¹) * g⁻¹ * (g * g) := by group
        _ = g * z * u * g⁻¹ * (g * g) := by rw [h1]; group
        _ = z * (g * u * g⁻¹) * (g * g) := by rw [hgz]; group
        _ = u * (g * g) := by rw [h1, ← mul_assoc z z u, hz2, one_mul]
  obtain ⟨k, hk⟩ := hodd
  have hg : (g * g) ^ (k + 1) = g := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have key := (hsq.pow_left (k + 1)).eq
  rwa [hg] at key

end Action

section Perm5

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eq_alternatingGroup_of_card (hα : Nat.card α = 5) {K : Subgroup (Equiv.Perm α)}
    (hK : Nat.card K = 60) : K = alternatingGroup α := by
  have hidx : K.index = 2 := by
    have h1 := K.card_mul_index
    rw [hK, Nat.card_perm, hα, show (5 : ℕ).factorial = 120 from rfl] at h1
    omega
  have hle : alternatingGroup α ≤ K := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      rw [← (show σ.IsThreeCycle from hσ).orderOf, pow_orderOf_eq_one]
    have hσ4 : (σ ^ 2) ^ 2 = σ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rw [SetLike.mem_coe, ← hσ4]
    exact sq_mem_of_index_two hidx _
  have : Nontrivial α :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hα]; norm_num)
  have hcard : Nat.card (alternatingGroup α) = 60 := by
    rw [nat_card_alternatingGroup, hα]
    rfl
  exact (eq_of_le_of_card_ge hle (le_of_eq (by rw [hK, hcard]))).symm

omit [Fintype α] [DecidableEq α] in
theorem five_dvd_card_of_transitive (hα : Nat.card α = 5) {K : Subgroup (Equiv.Perm α)} (a : α)
    (htr : ∀ b : α, ∃ σ ∈ K, σ a = b) : 5 ∣ Nat.card K := by
  have horb : MulAction.orbit K a = Set.univ := by
    ext b
    simp only [Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, rfl⟩ := htr b
    exact ⟨⟨σ, hσ⟩, rfl⟩
  have h1 := MulAction.index_stabilizer K a
  rw [horb, Set.ncard_univ, hα] at h1
  rw [← h1]
  exact index_dvd_card _

variable {H : Type*} [Group H] (ρ : H →* Equiv.Perm α) (hα : Nat.card α = 5)
  (hρ : ρ.range = alternatingGroup α)
include hα hρ

theorem nonempty_quot_mulEquiv {N : Subgroup H} [N.Normal] (hN : ρ.ker = N) :
    Nonempty (H ⧸ N ≃* alternatingGroup (Fin 5)) := by
  have e1 : H ⧸ N ≃* H ⧸ ρ.ker := QuotientGroup.quotientMulEquivOfEq hN.symm
  have e2 : alternatingGroup α ≃* alternatingGroup (Fin 5) :=
    Equiv.altCongrHom (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hα]))
  exact ⟨e1.trans ((QuotientGroup.quotientKerEquivRange ρ).trans
    ((MulEquiv.subgroupCongr hρ).trans e2))⟩

theorem pCore_eq_ker [Finite H] (hN2 : IsPGroup 2 ρ.ker) : CFSG.Open.pCore 2 H = ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.pCore_eq_iSup]
  refine le_antisymm (iSup_le fun M => iSup_le fun hM => iSup_le fun hM2 => ?_)
    (le_iSup_of_le ρ.ker (le_iSup_of_le inferInstance (le_iSup_of_le hN2 le_rfl)))
  set ψ : H →* alternatingGroup α := (MulEquiv.subgroupCongr hρ).toMonoidHom.comp ρ.rangeRestrict
    with hψ
  have hψs : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hρ).surjective.comp ρ.rangeRestrict_surjective
  have : Nontrivial α :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hα]; norm_num)
  have : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup (by rw [hα])
  have : (M.map ψ).Normal := hM.map ψ hψs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map ψ) with h1 | h1
  · intro m hm
    have h2 : ψ m = 1 := by
      rw [← mem_bot, ← h1]
      exact mem_map_of_mem ψ hm
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val h2
  · exfalso
    obtain ⟨n, hn⟩ := (hM2.map ψ).exists_card_eq
    rw [h1, card_top, nat_card_alternatingGroup, hα] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; decide
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

end Perm5

end CFSG.ComponentClassification.RankTwoAltFive
