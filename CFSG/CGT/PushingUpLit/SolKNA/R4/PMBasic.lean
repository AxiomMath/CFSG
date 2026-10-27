module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

section PM

variable {G : Type*} [Group G]

@[expose] def ActsPM (C : Subgroup G) (g : G) : Prop :=
  (∀ x ∈ C, g * x * g⁻¹ = x) ∨ (∀ x ∈ C, g * x * g⁻¹ = x⁻¹)

theorem actsPM_one (C : Subgroup G) : ActsPM C 1 := by
  refine Or.inl fun x _ => ?_
  simp

private theorem ActsPM.mem {C : Subgroup G} {g : G} (hg : ActsPM C g) {x : G} (hx : x ∈ C) :
    g * x * g⁻¹ ∈ C := by
  rcases hg with hg | hg
  · rw [hg x hx]; exact hx
  · rw [hg x hx]; exact C.inv_mem hx

theorem ActsPM.mul {C : Subgroup G} {g h : G} (hg : ActsPM C g) (hh : ActsPM C h) :
    ActsPM C (g * h) := by
  have e1 : ∀ x : G, g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := fun x => by group
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · refine Or.inl fun x hx => ?_
    rw [e1, hh x hx, hg x hx]
  · refine Or.inr fun x hx => ?_
    rw [e1, hh x hx, hg x⁻¹ (C.inv_mem hx)]
  · refine Or.inr fun x hx => ?_
    rw [e1, hh x hx, hg x hx]
  · refine Or.inl fun x hx => ?_
    rw [e1, hh x hx, hg x⁻¹ (C.inv_mem hx), inv_inv]

theorem ActsPM.inv {C : Subgroup G} {g : G} (hg : ActsPM C g) : ActsPM C g⁻¹ := by
  rcases hg with hg | hg
  · refine Or.inl fun x hx => ?_
    have hc : g * x = x * g := mul_inv_eq_iff_eq_mul.mp (hg x hx)
    rw [inv_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  · refine Or.inr fun x hx => ?_
    have h1 : g * x⁻¹ * g⁻¹ = x := by rw [hg x⁻¹ (C.inv_mem hx), inv_inv]
    have hc : g * x⁻¹ = x * g := mul_inv_eq_iff_eq_mul.mp h1
    rw [inv_inv, mul_assoc, ← hc, inv_mul_cancel_left]

@[expose] def pmSubgroup (C : Subgroup G) : Subgroup G where
  carrier := {g | ActsPM C g}
  one_mem' := actsPM_one C
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' := fun hg => hg.inv

theorem mem_pmSubgroup {C : Subgroup G} {g : G} : g ∈ pmSubgroup C ↔ ActsPM C g :=
  Iff.rfl

theorem centralizer_le_pmSubgroup (C : Subgroup G) :
    Subgroup.centralizer (C : Set G) ≤ pmSubgroup C := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [mem_pmSubgroup]
  refine Or.inl fun x hx => ?_
  rw [← hg x hx]
  exact mul_inv_cancel_right x g

theorem pmSubgroup_le_normalizer (C : Subgroup G) :
    pmSubgroup C ≤ Subgroup.normalizer (C : Set G) := by
  intro g hg
  rw [mem_pmSubgroup] at hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ActsPM.mem hg hy, fun hy => ?_⟩
  have h1 := ActsPM.mem (ActsPM.inv hg) hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1

private theorem exists_pow_conj_of_isCyclic {C : Subgroup G} (hC : IsCyclic ↥C) {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) : ∃ k : ℤ, ∀ x ∈ C, g * x * g⁻¹ = x ^ k := by
  obtain ⟨c, hc⟩ := (IsCyclic.exists_generator : ∃ c : ↥C, ∀ x : ↥C, x ∈ Subgroup.zpowers c)
  have hgc : g * (c : G) * g⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hg (c : G)).mp c.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨g * (c : G) * g⁻¹, hgc⟩)
  have hk' : (c : G) ^ k = g * (c : G) * g⁻¹ := by
    simpa using congrArg Subtype.val hk
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨x, hx⟩)
  have hxm : x = (c : G) ^ m := by
    simpa using (congrArg Subtype.val hm).symm
  rw [hxm, ← conj_zpow, ← hk', ← zpow_mul, ← zpow_mul, mul_comm]

theorem commutator_mem_centralizer_of_isCyclic {C : Subgroup G} (hC : IsCyclic ↥C) {g h : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (hh : h ∈ Subgroup.normalizer (C : Set G)) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.centralizer (C : Set G) := by
  obtain ⟨k, hk⟩ := exists_pow_conj_of_isCyclic hC hg
  have hmem : ∀ {u : G}, u ∈ Subgroup.normalizer (C : Set G) → ∀ x ∈ C, u * x * u⁻¹ ∈ C :=
    fun hu x hx => (Subgroup.mem_normalizer_iff.mp hu x).mp hx
  have comm : ∀ x ∈ C, g * (h * x * h⁻¹) * g⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by
    intro x hx
    rw [hk _ (hmem hh x hx), hk x hx, conj_zpow]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : g⁻¹ * (h⁻¹ * x * h) * g ∈ C := by
    have h2 : h⁻¹ * x * h⁻¹⁻¹ ∈ C := hmem (inv_mem hh) x hx
    rw [inv_inv] at h2
    have h1 : g⁻¹ * (h⁻¹ * x * h) * g⁻¹⁻¹ ∈ C := hmem (inv_mem hg) (h⁻¹ * x * h) h2
    rw [inv_inv] at h1
    exact h1
  have hgy : g * (g⁻¹ * (h⁻¹ * x * h) * g) * g⁻¹ = h⁻¹ * x * h := by group
  have h3 : g * (h * (g⁻¹ * (h⁻¹ * x * h) * g) * h⁻¹) * g⁻¹ = x := by
    rw [comm _ hy, hgy]
    group
  have hzx : g * h * g⁻¹ * h⁻¹ * x * (g * h * g⁻¹ * h⁻¹)⁻¹ = x := by
    rw [show g * h * g⁻¹ * h⁻¹ * x * (g * h * g⁻¹ * h⁻¹)⁻¹
        = g * (h * (g⁻¹ * (h⁻¹ * x * h) * g) * h⁻¹) * g⁻¹ by group]
    exact h3
  exact (mul_inv_eq_iff_eq_mul.mp hzx).symm

theorem commutator_mem_pmSubgroup {C : Subgroup G} (hC : IsCyclic ↥C) {g h : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (hh : h ∈ Subgroup.normalizer (C : Set G)) :
    g * h * g⁻¹ * h⁻¹ ∈ pmSubgroup C :=
  centralizer_le_pmSubgroup C (commutator_mem_centralizer_of_isCyclic hC hg hh)

end PM

section Quat

variable {G : Type*} [Group G]

private theorem eq_zpowers_a_one_of_isCyclic {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    (L : Subgroup (QuaternionGroup n)) [IsCyclic L] (hL : Nat.card L = 2 * n) :
    L = Subgroup.zpowers (QuaternionGroup.a 1) := by
  obtain ⟨g, hg⟩ := (IsCyclic.exists_generator : ∃ g : L, ∀ x : L, x ∈ Subgroup.zpowers g)
  have htop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hord : orderOf (g : QuaternionGroup n) = 2 * n := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, htop, Subgroup.card_top, hL]
  have hcase : ∀ q : QuaternionGroup n, orderOf q = 2 * n → ∃ k, q = QuaternionGroup.a k := by
    intro q hq
    cases q with
    | a k => exact ⟨k, rfl⟩
    | xa k =>
      exfalso
      rw [QuaternionGroup.orderOf_xa] at hq
      omega
  obtain ⟨k, hk⟩ := hcase _ hord
  have hak : (QuaternionGroup.a k : QuaternionGroup n) ∈
      Subgroup.zpowers (QuaternionGroup.a 1) := by
    rw [show (QuaternionGroup.a k : QuaternionGroup n) = QuaternionGroup.a 1 ^ k.val by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hle : L ≤ Subgroup.zpowers (QuaternionGroup.a 1) := by
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hxm : x = (g : QuaternionGroup n) ^ m := by
      simpa using (congrArg Subtype.val hm).symm
    rw [hxm, hk]
    exact Subgroup.zpow_mem _ hak m
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one, hL]

private theorem mem_zpowers_a_one {n : ℕ} [NeZero n] {q : QuaternionGroup n}
    (hq : q ∈ Subgroup.zpowers (QuaternionGroup.a 1)) :
    ∃ k : ZMod (2 * n), q = QuaternionGroup.a k := by
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hq)
  exact ⟨(m : ZMod (2 * n)), by rw [← hm, QuaternionGroup.a_one_pow]⟩

private theorem map_eq_zpowers_a_one {n : ℕ} [NeZero n] (hn : 4 ≤ n) {T : Type*} [Group T]
    (e : T ≃* QuaternionGroup n) (K : Subgroup T) [IsCyclic K] (hK : Nat.card K = 2 * n) :
    K.map e.toMonoidHom = Subgroup.zpowers (QuaternionGroup.a 1) := by
  have hiso := Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  haveI : IsCyclic (K.map e.toMonoidHom) := (MulEquiv.isCyclic hiso).mp inferInstance
  refine eq_zpowers_a_one_of_isCyclic hn (K.map e.toMonoidHom) ?_
  rw [← Nat.card_congr hiso.toEquiv]
  exact hK

private theorem card_quat {T : Type*} [Group T] {n : ℕ} [NeZero n]
    (e : T ≃* QuaternionGroup n) : Nat.card T = 4 * n := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem four_le_two_pow {r : ℕ} (hr : 4 ≤ r) : 4 ≤ 2 ^ (r - 2) := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem card_of_relIndex_two {S₀ C : Subgroup G} {n : ℕ} (hC : C ≤ S₀)
    (hCi : C.relIndex S₀ = 2) (hS : Nat.card S₀ = 4 * n) : Nat.card C = 2 * n := by
  have h := Subgroup.relIndex_mul_card C S₀
  rw [inf_eq_left.mpr hC, hCi, hS] at h
  omega

private theorem natCast_add_self (n : ℕ) : (n : ZMod (2 * n)) + (n : ZMod (2 * n)) = 0 := by
  rw [← Nat.cast_add, ← two_mul]
  exact ZMod.natCast_self _

private theorem a_conj_a {n : ℕ} (j k : ZMod (2 * n)) :
    QuaternionGroup.a j * QuaternionGroup.a k * (QuaternionGroup.a j)⁻¹ =
      QuaternionGroup.a k := by
  rw [show (QuaternionGroup.a j : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-j) from rfl,
    QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a]
  congr 1
  ring

private theorem xa_conj_a {n : ℕ} (j k : ZMod (2 * n)) :
    QuaternionGroup.xa j * QuaternionGroup.a k * (QuaternionGroup.xa j)⁻¹ =
      (QuaternionGroup.a k : QuaternionGroup n)⁻¹ := by
  rw [show (QuaternionGroup.xa j : QuaternionGroup n)⁻¹ =
      QuaternionGroup.xa ((n : ZMod (2 * n)) + j) from rfl,
    show (QuaternionGroup.a k : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-k) from rfl,
    QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
  congr 1
  rw [show (n : ZMod (2 * n)) + ((n : ZMod (2 * n)) + j) - (j + k) =
      ((n : ZMod (2 * n)) + (n : ZMod (2 * n))) - k by ring, natCast_add_self, zero_sub]

theorem eq_of_isCyclic_of_relIndex_eq_two {r : ℕ} (hr : 4 ≤ r) {S₀ : Subgroup G}
    (e : ↥S₀ ≃* QuaternionGroup (2 ^ (r - 2))) {C D : Subgroup G} (hC : C ≤ S₀)
    (hCc : IsCyclic ↥C) (hCi : C.relIndex S₀ = 2) (hD : D ≤ S₀) (hDc : IsCyclic ↥D)
    (hDi : D.relIndex S₀ = 2) : C = D := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hn := four_le_two_pow hr
  have hS := card_quat e
  have hKC : Nat.card ↥(C.subgroupOf S₀) = 2 * 2 ^ (r - 2) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv).trans
      (card_of_relIndex_two hC hCi hS)
  have hKD : Nat.card ↥(D.subgroupOf S₀) = 2 * 2 ^ (r - 2) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv).trans
      (card_of_relIndex_two hD hDi hS)
  haveI : IsCyclic ↥(C.subgroupOf S₀) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hC)).mpr hCc
  haveI : IsCyclic ↥(D.subgroupOf S₀) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hD)).mpr hDc
  have hmC := map_eq_zpowers_a_one hn e (C.subgroupOf S₀) hKC
  have hmD := map_eq_zpowers_a_one hn e (D.subgroupOf S₀) hKD
  have hKey : C.subgroupOf S₀ = D.subgroupOf S₀ :=
    Subgroup.map_injective (f := e.toMonoidHom) e.injective (hmC.trans hmD.symm)
  calc C = (C.subgroupOf S₀).map S₀.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC]
    _ = (D.subgroupOf S₀).map S₀.subtype := by rw [hKey]
    _ = D := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD]

theorem le_normalizer_of_isCyclic_of_relIndex_eq_two {r : ℕ} (hr : 4 ≤ r) {S₀ : Subgroup G}
    (e : ↥S₀ ≃* QuaternionGroup (2 ^ (r - 2))) {C : Subgroup G} (hC : C ≤ S₀)
    (hCc : IsCyclic ↥C) (hCi : C.relIndex S₀ = 2) :
    Subgroup.normalizer (S₀ : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  intro g hg
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hgS : ∀ x ∈ S₀, g * x * g⁻¹ ∈ S₀ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hC'S : C.map (MulAut.conj g).toMonoidHom ≤ S₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgS x (hC hx)
  have hiso := Subgroup.equivMapOfInjective C (MulAut.conj g).toMonoidHom hinj
  have hC'c : IsCyclic ↥(C.map (MulAut.conj g).toMonoidHom) :=
    (MulEquiv.isCyclic hiso).mp hCc
  have hS := card_quat e
  have hKc := card_of_relIndex_two hC hCi hS
  have hC'card : Nat.card ↥(C.map (MulAut.conj g).toMonoidHom) = 2 * 2 ^ (r - 2) := by
    rw [← Nat.card_congr hiso.toEquiv, hKc]
  have hC'i : (C.map (MulAut.conj g).toMonoidHom).relIndex S₀ = 2 := by
    have h := Subgroup.relIndex_mul_card (C.map (MulAut.conj g).toMonoidHom) S₀
    rw [inf_eq_left.mpr hC'S, hC'card, hS] at h
    have hpos : 0 < 2 * 2 ^ (r - 2) := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h]; ring)
  have hCC : C.map (MulAut.conj g).toMonoidHom = C :=
    eq_of_isCyclic_of_relIndex_eq_two hr e hC'S hC'c hC'i hC hCc hCi
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : g * y * g⁻¹ ∈ C.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rwa [hCC] at h1
  · intro hy
    have h1 : g * y * g⁻¹ ∈ C.map (MulAut.conj g).toMonoidHom := by
      rwa [hCC]
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp h1
    have h2 : g * x * g⁻¹ = g * y * g⁻¹ := hxy
    have h3 : x = y := by simpa using h2
    rw [← h3]
    exact hx

theorem le_pmSubgroup_of_quat {r : ℕ} (hr : 4 ≤ r) {S₀ : Subgroup G}
    (e : ↥S₀ ≃* QuaternionGroup (2 ^ (r - 2))) {C : Subgroup G} (hC : C ≤ S₀)
    (hCc : IsCyclic ↥C) (hCi : C.relIndex S₀ = 2) : S₀ ≤ pmSubgroup C := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hn := four_le_two_pow hr
  have hS := card_quat e
  have hKC : Nat.card ↥(C.subgroupOf S₀) = 2 * 2 ^ (r - 2) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv).trans
      (card_of_relIndex_two hC hCi hS)
  haveI : IsCyclic ↥(C.subgroupOf S₀) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hC)).mpr hCc
  have hmC := map_eq_zpowers_a_one hn e (C.subgroupOf S₀) hKC
  have hcoset : ∀ x : G, ∀ hx : x ∈ C, ∃ k : ZMod (2 * 2 ^ (r - 2)),
      e ⟨x, hC hx⟩ = QuaternionGroup.a k := by
    intro x hx
    apply mem_zpowers_a_one
    rw [← hmC]
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (show (⟨x, hC hx⟩ : ↥S₀) ∈ C.subgroupOf S₀ from hx)
  intro g hg
  rw [mem_pmSubgroup]
  rcases hq : e ⟨g, hg⟩ with j | j
  · refine Or.inl fun x hx => ?_
    obtain ⟨k, hk⟩ := hcoset x hx
    have key : e (⟨g, hg⟩ * ⟨x, hC hx⟩ * (⟨g, hg⟩ : ↥S₀)⁻¹) = e ⟨x, hC hx⟩ := by
      rw [map_mul, map_mul, map_inv, hq, hk, a_conj_a]
    have h2 := congrArg Subtype.val (e.injective key)
    simpa using h2
  · refine Or.inr fun x hx => ?_
    obtain ⟨k, hk⟩ := hcoset x hx
    have key : e (⟨g, hg⟩ * ⟨x, hC hx⟩ * (⟨g, hg⟩ : ↥S₀)⁻¹) = e (⟨x, hC hx⟩ : ↥S₀)⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hq, hk, xa_conj_a]
    have h2 := congrArg Subtype.val (e.injective key)
    simpa using h2

end Quat

end CFSG.CGT.PushingUpLit.SolKNA.R4
