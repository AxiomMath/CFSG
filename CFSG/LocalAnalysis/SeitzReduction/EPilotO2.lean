module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

section Abelian

variable {A : Type*} [Group A] {L : Subgroup A} [L.Normal]

theorem exists_odd_pow_mem_of_mem_closure_odd (hcomm : ∀ a b : A, a * b * a⁻¹ * b⁻¹ ∈ L)
    {a : A} (ha : a ∈ closure {x : A | Odd (orderOf x)}) : ∃ n : ℕ, Odd n ∧ a ^ n ∈ L := by
  have hq : ∀ x y : A, Commute (QuotientGroup.mk x : A ⧸ L) (QuotientGroup.mk y) := by
    intro x y
    show (QuotientGroup.mk (x * y) : A ⧸ L) = QuotientGroup.mk (y * x)
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hcomm y⁻¹ x⁻¹
  let S : Subgroup A :=
    { carrier := {a | ∃ n : ℕ, Odd n ∧ a ^ n ∈ L}
      one_mem' := ⟨1, odd_one, by simp⟩
      mul_mem' := by
        rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
        refine ⟨m * n, hm.mul hn, ?_⟩
        have h1 : (QuotientGroup.mk x : A ⧸ L) ^ m = 1 := by
          rw [← QuotientGroup.mk_pow]
          exact (QuotientGroup.eq_one_iff _).2 hx
        have h2 : (QuotientGroup.mk y : A ⧸ L) ^ n = 1 := by
          rw [← QuotientGroup.mk_pow]
          exact (QuotientGroup.eq_one_iff _).2 hy
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
          (hq x y).mul_pow, pow_mul, pow_mul', h1, h2, one_pow, one_pow, one_mul]
      inv_mem' := by
        rintro x ⟨n, hn, hx⟩
        exact ⟨n, hn, by simpa [inv_pow] using L.inv_mem hx⟩ }
  have hsub : closure {x : A | Odd (orderOf x)} ≤ S := by
    rw [closure_le]
    intro x hx
    exact ⟨orderOf x, hx, by simp [pow_orderOf_eq_one]⟩
  exact hsub ha

theorem mem_of_mem_closure_odd_of_sq_eq_one (hcomm : ∀ a b : A, a * b * a⁻¹ * b⁻¹ ∈ L)
    {a : A} (ha2 : a ^ 2 = 1) (ha : a ∈ closure {x : A | Odd (orderOf x)}) : a ∈ L := by
  obtain ⟨n, ⟨k, rfl⟩, hn⟩ := exists_odd_pow_mem_of_mem_closure_odd hcomm ha
  have e : a ^ (2 * k + 1) = a := by rw [pow_succ, pow_mul, ha2, one_pow, one_mul]
  rwa [e] at hn

end Abelian

section LemmaO2

variable {G : Type*} [Group G]

theorem mem_of_mem_closure_odd_of_commutator_mem {A L : Subgroup G}
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ L)
    {x : G} (hx2 : x ^ 2 = 1) (hx : x ∈ closure {y : G | y ∈ A ∧ Odd (orderOf y)}) :
    x ∈ L := by
  have hN : (L.subgroupOf A).Normal := ⟨fun n hn a => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.1 (hAN a.2) n).1 hn⟩
  have hle : closure {y : G | y ∈ A ∧ Odd (orderOf y)} ≤
      (closure {y : A | Odd (orderOf y)}).map A.subtype := by
    rw [closure_le]
    rintro y ⟨hyA, hyo⟩
    exact ⟨⟨y, hyA⟩, subset_closure (by simpa [Subgroup.orderOf_mk] using hyo), rfl⟩
  obtain ⟨a, ha, rfl⟩ := hle hx
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  exact mem_subgroupOf.1 (mem_of_mem_closure_odd_of_sq_eq_one (L := L.subgroupOf A)
    (fun a b => mem_subgroupOf.2 (by simpa using hcomm a a.2 b b.2)) ha2 ha)

theorem mem_centralizer_of_inf_centralizer_eq_zpowers {L : Subgroup G} {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    t ∈ centralizer (L : Set G) :=
  (hKt ▸ mem_zpowers t : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1

theorem not_mem_of_mem_centralizer_of_center_eq_bot {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (hZ : center L = ⊥) (ht1 : t ≠ 1) : t ∉ L := by
  intro htL
  have hZt : (⟨t, htL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 htC l l.2)
  rw [hZ, mem_bot] at hZt
  exact ht1 (congrArg Subtype.val hZt)

theorem commutator_mem_of_mem_centralizer_of_isCyclic_outer {L : Subgroup G} {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hOut : IsCyclic (Outer L))
    {a b : G} (ha : a ∈ centralizer ({t} : Set G)) (hb : b ∈ centralizer ({t} : Set G)) :
    a * b * a⁻¹ * b⁻¹ ∈ L := by
  set A := centralizer ({t} : Set G) with hAdef
  have htC := mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  have hLA : L ≤ A := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have htA : t ∈ A := mem_centralizer_singleton_iff.2 rfl
  have : (L.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hLA).2 hCN
  set π : A →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp (L.normalizerMonoidHom.comp (inclusion hCN)) with hπ
  have hK1 : L.subgroupOf A ≤ π.ker := by
    intro d hd
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨⟨d, mem_subgroupOf.1 hd⟩, ?_⟩
    ext x
    simp [MulAut.conj_apply]
  have hK2 : ∀ d : A, π d = 1 → ∃ l ∈ L, ∃ j : ℤ, (d : G) = l * t ^ j := by
    intro d hd
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hd
    obtain ⟨l, hl⟩ := hd
    have hc : (l : G)⁻¹ * d ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 : (d : G) * x * (d : G)⁻¹ = l * x * (l : G)⁻¹ := by
        have := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : G)) hl
        simpa [MulAut.conj_apply] using this.symm
      calc x * ((l : G)⁻¹ * d) = (l : G)⁻¹ * (l * x * (l : G)⁻¹) * d := by group
        _ = (l : G)⁻¹ * (d * x * (d : G)⁻¹) * d := by rw [h1]
        _ = (l : G)⁻¹ * d * x := by group
    have hct : (l : G)⁻¹ * d ∈ A := A.mul_mem (A.inv_mem (hLA l.2)) d.2
    obtain ⟨j, hj⟩ : (l : G)⁻¹ * d ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hc, hct⟩
    refine ⟨l, l.2, j, ?_⟩
    have hj' : t ^ j = (l : G)⁻¹ * d := hj
    rw [hj']
    group
  set ρ := QuotientGroup.mk' (L.subgroupOf A) with hρ
  set f : A ⧸ L.subgroupOf A →* Outer L := QuotientGroup.lift (L.subgroupOf A) π hK1 with hf
  have hK3 : f.ker ≤ center (A ⧸ L.subgroupOf A) := by
    intro x hx
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf A) x
    have hd : π d = 1 := by
      rw [MonoidHom.mem_ker, hf, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at hx
      exact hx
    obtain ⟨l, hl, j, hdj⟩ := hK2 d hd
    have hdeq : d = ⟨l, hLA hl⟩ * ⟨t, htA⟩ ^ j := Subtype.ext (by simpa using hdj)
    have hρl : ρ ⟨l, hLA hl⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hl)
    rw [mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf A) z
    have hyt : Commute y ⟨t, htA⟩ := Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
    rw [hdeq, map_mul, map_zpow, hρl, one_mul]
    exact ((hyt.map ρ).zpow_right j).eq
  have hcomm : ρ ⟨a, ha⟩ * ρ ⟨b, hb⟩ = ρ ⟨b, hb⟩ * ρ ⟨a, ha⟩ :=
    (f.isMulCommutative_of_isCyclic_of_ker_le_center hK3).is_comm.comm _ _
  have h1 : ρ (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : A)⁻¹ * (⟨b, hb⟩ : A)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_inv_cancel_right,
      mul_inv_cancel]
  have h2 := mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  simpa using h2

theorem not_mem_closure_odd_centralizer {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hZ : center L = ⊥)
    (hOut : IsCyclic (Outer L)) :
    t ∉ closure {x : G | x ∈ centralizer ({t} : Set G) ∧ Odd (orderOf x)} := by
  intro h
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  exact not_mem_of_mem_centralizer_of_center_eq_bot
    (mem_centralizer_of_inf_centralizer_eq_zpowers hKt) hZ ht1
    (mem_of_mem_closure_odd_of_commutator_mem hCN (fun a ha b hb =>
      commutator_mem_of_mem_centralizer_of_isCyclic_outer hKt hCN hOut ha hb) ht2 h)

theorem not_mem_closure_odd_of_conj_mem {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hZ : center L = ⊥)
    (hOut : IsCyclic (Outer L)) (g : G) :
    g⁻¹ * t * g ∉
      closure {x : G | x ∈ L ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Odd (orderOf x)} := by
  intro h
  apply not_mem_closure_odd_centralizer ht hKt hCN hZ hOut
  have hle : closure {x : G | x ∈ L ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Odd (orderOf x)} ≤
      (closure {x : G | x ∈ centralizer ({t} : Set G) ∧ Odd (orderOf x)}).comap
        (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro x ⟨hxLw, hxo⟩
    have hxw := (mem_inf.1 hxLw).2
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hxw ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hxw]
        _ = t * (g * x * g⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hxo
  have h' := hle h
  rw [mem_comap] at h'
  have e : (MulAut.conj g).toMonoidHom (g⁻¹ * t * g) = t := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [e] at h'

theorem not_mem_closure_odd_of_inner {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hZ : center L = ⊥)
    (hOut : IsCyclic (Outer L)) {g w' : G} (hw : g⁻¹ * t * g ∈ L)
    (htw' : t = w' ∨ t = w' * (g⁻¹ * t * g)) :
    w' ∉ closure
      {x : G | x ∈ CFSG.conjugate L g ⊓ centralizer ({w'} : Set G) ∧ Odd (orderOf x)} := by
  intro h
  have htC := mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hw2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have htw : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := mem_centralizer_iff.1 htC _ hw
  have hw'2 : w' ^ 2 = 1 := by
    rcases htw' with h' | h'
    · rw [← h', sq, ht2]
    · have hw' : w' = t * (g⁻¹ * t * g) := by
        calc w' = w' * ((g⁻¹ * t * g) * (g⁻¹ * t * g)) := by rw [hw2, mul_one]
          _ = (w' * (g⁻¹ * t * g)) * (g⁻¹ * t * g) := (mul_assoc _ _ _).symm
          _ = t * (g⁻¹ * t * g) := by rw [← h']
      rw [hw', sq]
      calc t * (g⁻¹ * t * g) * (t * (g⁻¹ * t * g))
          = t * ((g⁻¹ * t * g) * t) * (g⁻¹ * t * g) := by group
        _ = t * t * ((g⁻¹ * t * g) * (g⁻¹ * t * g)) := by rw [htw]; group
        _ = 1 := by rw [ht2, hw2, one_mul]
  have hle : closure
      {x : G | x ∈ CFSG.conjugate L g ⊓ centralizer ({w'} : Set G) ∧ Odd (orderOf x)} ≤
      closure {x : G | x ∈ centralizer ({t} : Set G) ∧ Odd (orderOf x)} := by
    apply Subgroup.closure_mono
    rintro x ⟨hxLw, hxo⟩
    obtain ⟨hxL, hxw'⟩ := mem_inf.1 hxLw
    refine ⟨?_, hxo⟩
    have hxw : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := by
      obtain ⟨l, hl, rfl⟩ := hxL
      have hlt := mem_centralizer_iff.1 htC l hl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * l * g * (g⁻¹ * t * g) = g⁻¹ * (l * t) * g := by group
        _ = g⁻¹ * (t * l) * g := by rw [hlt]
        _ = g⁻¹ * t * g * (g⁻¹ * l * g) := by group
    rw [mem_centralizer_singleton_iff] at hxw' ⊢
    rcases htw' with h' | h'
    · rw [h']
      exact hxw'
    · rw [h']
      calc x * (w' * (g⁻¹ * t * g)) = (x * w') * (g⁻¹ * t * g) := by group
        _ = (w' * x) * (g⁻¹ * t * g) := by rw [hxw']
        _ = w' * (x * (g⁻¹ * t * g)) := by group
        _ = w' * ((g⁻¹ * t * g) * x) := by rw [hxw]
        _ = w' * (g⁻¹ * t * g) * x := by group
  have hw'L : w' ∈ L := mem_of_mem_closure_odd_of_commutator_mem hCN (fun a ha b hb =>
    commutator_mem_of_mem_centralizer_of_isCyclic_outer hKt hCN hOut ha hb) hw'2 (hle h)
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  apply not_mem_of_mem_centralizer_of_center_eq_bot htC hZ ht1
  rcases htw' with h' | h'
  · rw [h']
    exact hw'L
  · rw [h']
    exact mul_mem hw'L hw

end LemmaO2

end CFSG.SeitzReduction.EPilot
