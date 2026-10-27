module

public import CFSG.Sporadic.SuzOddCore.CompQuot
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.SuzCS

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

theorem mem_normalizer_of_comm {G : Type*} [Group G] {H : Subgroup G} {a : G}
    (h : ∀ x ∈ H, x * a = a * x) : a ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx
    rw [inv_mul_cancel_right] at h1
    rw [mul_left_cancel h1]
    exact hx

theorem map_eq_of_component {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (D : Subgroup K) (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    {B : Subgroup E} (hB : IsComponent B) : B.map ρ = D := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := by rw [← Subgroup.map_commutator, hBB]
  have hle : B.map ρ ≤ D := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (CFSG.Sporadic.SuzOddCore.commutator_le_of_index_two hDi)
  have hsubD : ((B.map ρ).subgroupOf D).IsSubnormal := (hsub.map hρ).subgroupOf
  rcases hsubD.eq_bot_or_top_of_isSimpleGroup hDs with h | h
  · exfalso
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : (⟨ρ b, hle ⟨b, hb, rfl⟩⟩ : D) ∈ (B.map ρ).subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · apply le_antisymm hle
    intro d hd
    have : (⟨d, hd⟩ : D) ∈ (B.map ρ).subgroupOf D := h ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at this

theorem isComponent_subgroupOf_of_le {W : Type*} [Group W] {J E Y : Subgroup W} (hJE : J ≤ E)
    (hEY : E ≤ Y) (hJ : IsComponent (J.subgroupOf Y)) : IsComponent (J.subgroupOf E) := by
  have h1 : J.subgroupOf Y ≤ E.subgroupOf Y := fun x hx => hJE hx
  have h2 := component_overgroup hJ h1
  have h3 := isComponent_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hEY) h2
  have h4 : ((J.subgroupOf Y).subgroupOf (E.subgroupOf Y)).map
      (Subgroup.subgroupOfEquivOfLe hEY).toMonoidHom = J.subgroupOf E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨⟨x, hEY x.2⟩, x.2⟩, hx, ?_⟩
      rfl
  rwa [h4] at h3

theorem normal_of_component {X : Type*} [Group X] [Finite X] {K : Subgroup X} (hK : IsComponent K)
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card (K ⧸ center K)) (hpX : ¬ p ^ 2 ∣ Nat.card X) :
    K.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K = Nat.card (K ⧸ center K) * Nat.card (center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hKX : Nat.card K ∣ Nat.card X := Subgroup.card_subgroup_dvd_card K
  have hZ : ¬ p ∣ Nat.card (center K) := by
    intro h
    apply hpX
    refine (?_ : p ^ 2 ∣ Nat.card K).trans hKX
    rw [hcard, pow_two]
    exact Nat.mul_dvd_mul hpK h
  have hpKc : p ∣ Nat.card K := by
    rw [hcard]
    exact hpK.mul_right _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpKc
  set a : X := (g : X) with ha
  have hao : orderOf a = p := by rw [ha, Subgroup.orderOf_coe, hg]
  have key : ∀ x : X, K.map (MulAut.conj x).toMonoidHom = K := by
    intro x
    have hKx : IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
      isComponent_map_mulEquiv (MulAut.conj x) hK
    rcases distinct_components_commute hK hKx with h | h
    · exact h.symm
    · exfalso
      have hc : ∀ k ∈ K, ∀ y ∈ K.map (MulAut.conj x).toMonoidHom, k * y = y * k := by
        intro k hk y hy
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk
        exact (Subgroup.mem_centralizer_iff.mp this y hy).symm
      set b : X := x * a * x⁻¹ with hb
      have hbK : b ∈ K.map (MulAut.conj x).toMonoidHom := ⟨a, g.2, rfl⟩
      have hbo : orderOf b = p := by
        rw [hb, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hao]
      by_cases hbK' : b ∈ K
      ·
        have hcen : (⟨b, hbK'⟩ : K) ∈ center K := by
          rw [Subgroup.mem_center_iff]
          intro k
          apply Subtype.ext
          exact hc k k.2 b hbK
        apply hZ
        have h1 : orderOf (⟨⟨b, hbK'⟩, hcen⟩ : center K) = p := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hbo]
        rw [← h1]
        exact orderOf_dvd_natCard _
      ·
        have hab : a * b = b * a := hc a g.2 b hbK
        have hPa : IsPGroup p (zpowers a) := by
          rw [IsPGroup.iff_card, Nat.card_zpowers, hao]
          exact ⟨1, (pow_one p).symm⟩
        have hPb : IsPGroup p (zpowers b) := by
          rw [IsPGroup.iff_card, Nat.card_zpowers, hbo]
          exact ⟨1, (pow_one p).symm⟩
        have hnorm : zpowers a ≤ normalizer (zpowers b : Set X) := by
          rw [zpowers_le]
          apply mem_normalizer_of_comm
          rintro _ ⟨k, rfl⟩
          exact ((Commute.zpow_left (show Commute b a from hab.symm) k)).eq
        have hP := IsPGroup.to_sup_of_normal_right' hPa hPb hnorm
        obtain ⟨k, hk⟩ := hP.exists_card_eq
        have hlt : zpowers a < zpowers a ⊔ zpowers b := by
          refine lt_of_le_of_ne le_sup_left fun h => hbK' ?_
          have hb' : b ∈ zpowers a := by
            rw [h]
            exact mem_sup_right (mem_zpowers b)
          exact (zpowers_le.mpr g.2) hb'
        have hcardlt := Subgroup.card_lt_of_lt hlt
        rw [Nat.card_zpowers, hao, hk] at hcardlt
        have hk2 : 2 ≤ k :=
          (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rwa [pow_one])
        apply hpX
        refine (pow_dvd_pow p hk2).trans ?_
        rw [← hk]
        exact Subgroup.card_subgroup_dvd_card _
  constructor
  intro k hk x
  have := key x
  rw [← this]
  exact ⟨k, hk, rfl⟩

theorem card_dvd_of_normal {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [MulAction.IsPreprimitive G Ω] (N : Subgroup G) [N.Normal] {g : G} (hg : g ∈ N) {x : Ω}
    (hx : g • x ≠ x) : Nat.card Ω ∣ Nat.card N := by
  have hfix : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro h
    have hxf : x ∈ MulAction.fixedPoints N Ω := h ▸ Set.mem_univ x
    exact hx (hxf ⟨g, hg⟩)
  have := MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
  have horb : MulAction.orbit N x = Set.univ := MulAction.orbit_eq_univ N x
  have h := MulAction.index_stabilizer (G := N) (x := x)
  rw [horb, Set.ncard_univ] at h
  rw [← h]
  exact Subgroup.index_dvd_card _

theorem le_of_perfect_of_index_two {W : Type*} [Group W] {M T H : Subgroup W}
    (hidx : (M.subgroupOf T).index = 2) (hHT : H ≤ T) (hH : ⁅H, H⁆ = H) : H ≤ M := by
  rw [← hH, Subgroup.commutator_le]
  intro x hx y hy
  have h := CFSG.Sporadic.SuzOddCore.commutator_le_of_index_two hidx
  have hm : ⁅(⟨x, hHT hx⟩ : T), (⟨y, hHT hy⟩ : T)⁆ ∈ M.subgroupOf T :=
    h (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
  rw [Subgroup.mem_subgroupOf] at hm
  simpa [commutatorElement_def] using hm

theorem eq_of_mem_of_card_eq_four {G : Type*} [Group G] {K : Subgroup G} (hK : Nat.card K = 4)
    {a b c d : G} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {x : G} (hx : x ∈ K) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hxa, hxb, hxc, hxd⟩ := h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let _ := Fintype.ofFinite K
  let s : Finset K := {⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨x, hx⟩}
  have hs : s.card = 5 := by
    simp only [s]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair]
    · exact fun h => hxd (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hcd (congrArg Subtype.val h), fun h => hxc (congrArg Subtype.val h).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hbc (congrArg Subtype.val h), fun h => hbd (congrArg Subtype.val h),
        fun h => hxb (congrArg Subtype.val h).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hab (congrArg Subtype.val h), fun h => hac (congrArg Subtype.val h),
        fun h => had (congrArg Subtype.val h), fun h => hxa (congrArg Subtype.val h).symm⟩
  have h1 := s.card_le_univ
  rw [hs, Fintype.card_eq_nat_card, hK] at h1
  omega

end CFSG.ComponentClassification.CatFactsL4U4.SuzCS
