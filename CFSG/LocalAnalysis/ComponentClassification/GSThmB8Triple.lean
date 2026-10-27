module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Eight

theorem exists_conj_fixed_mul {G : Type*} [Group G] {N : Subgroup G} [Finite N]
    (hN : Odd (Nat.card N)) {a g : G} (ha : a * a = 1) (haN : a ∈ normalizer (N : Set G))
    (hg : g⁻¹ * (a * g * a⁻¹) ∈ N) : ∃ n ∈ N, a * (g * n) * a⁻¹ = g * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype N := Fintype.ofFinite N
  have hconj : ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun n hn => (mem_normalizer_iff.mp haN n).mp hn
  set c : G := g⁻¹ * (a * g * a⁻¹) with hc
  let F : N → N := fun n => ⟨c * (a * n * a⁻¹), mul_mem hg (hconj n n.2)⟩
  have hF : Function.Involutive F := by
    intro n
    apply Subtype.ext
    show c * (a * (c * (a * (n : G) * a⁻¹)) * a⁻¹) = n
    have h1 : c * (a * (c * (a * (n : G) * a⁻¹)) * a⁻¹) =
        g⁻¹ * (a * a) * g * (a * a)⁻¹ * ((a * a) * n * (a * a)⁻¹) := by
      rw [hc]
      group
    rw [h1, ha]
    group
  have hσ : Function.Involutive.toPerm F hF ^ 2 ^ 1 = 1 := by
    refine Equiv.ext fun n => ?_
    rw [pow_one, pow_two, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm,
      Equiv.Perm.one_apply]
    exact hF n
  have hodd : ¬ 2 ∣ Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h2 => Nat.not_even_iff_odd.mpr hN (even_iff_two_dvd.mpr h2)
  obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
  have hn' : c * (a * (n : G) * a⁻¹) = n := by
    have := congrArg Subtype.val hn
    rwa [Function.Involutive.coe_toPerm] at this
  refine ⟨n, n.2, ?_⟩
  calc a * (g * n) * a⁻¹ = g * (c * (a * (n : G) * a⁻¹)) := by
        rw [hc]
        group
    _ = g * n := by rw [hn']

theorem eq_sq_pow_of_odd {G : Type*} [Monoid G] {x : G} (hx : Odd (orderOf x)) :
    x = (x * x) ^ ((orderOf x + 1) / 2) := by
  obtain ⟨k, hk⟩ := hx
  have h1 : (orderOf x + 1) / 2 = k + 1 := by omega
  rw [h1, ← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

theorem relIndex_map_le {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    (A B : Subgroup G) : (A.map f).relIndex (B.map f) ≤ A.relIndex B := by
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_le_of_le_left (Subgroup.le_comap_map f A)
    (Subgroup.index_ne_zero_of_finite (H := A.subgroupOf B))

theorem normal_map_subgroupOf {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {A B : Subgroup G} (hAB : A ≤ B) (hA : ∀ x ∈ A, ∀ y ∈ B, y * x * y⁻¹ ∈ A) :
    ((A.map f).subgroupOf (B.map f)).Normal := by
  refine (normal_subgroupOf_iff (map_mono hAB)).mpr fun x y hx hy => ?_
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mem_map_of_mem f (hA u hu v hv)

theorem mem_normalizer_range_conj {K₀ : Type*} [Group K₀] (φ : MulAut K₀) :
    φ ∈ normalizer ((MulAut.conj : K₀ →* MulAut K₀).range : Set (MulAut K₀)) := by
  have key : ∀ (ψ : MulAut K₀) (y : K₀), ψ * MulAut.conj y * ψ⁻¹ = MulAut.conj (ψ y) := by
    intro ψ y
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  rw [mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨φ y, (key φ y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨φ⁻¹ y, ?_⟩
    rw [← key, hy]
    group

theorem trans_mem_range_conj_iff {A B : Type*} [Group A] [Group B] (κ : A ≃* B)
    (α : MulAut A) : κ.symm.trans (α.trans κ) ∈ (MulAut.conj : B →* MulAut B).range ↔
      α ∈ (MulAut.conj : A →* MulAut A).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨κ.symm y, ?_⟩
    ext x
    have h1 := congrArg (fun φ : MulAut B => φ (κ x)) hy
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.conj_apply]
    apply κ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  · rintro ⟨y, hy⟩
    refine ⟨κ y, ?_⟩
    ext x
    rw [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hy, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem le_oddCore_of_odd {G : Type*} [Group G] {C N : Subgroup G} (hNC : N ≤ C)
    (hN : C ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ (pPrimeCore 2 C).map C.subtype := by
  have hn : (N.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hNC).mpr hN
  have hcard : Nat.card (N.subgroupOf C) = Nat.card N := by
    rw [← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype, inf_eq_left.mpr hNC]
  have hle : N.subgroupOf C ≤ pPrimeCore 2 C :=
    le_sSup ⟨hn, Nat.coprime_two_left.mpr (hcard ▸ hodd)⟩
  intro x hx
  exact ⟨⟨x, hNC hx⟩, hle hx, rfl⟩

theorem gsUnbalancingTriple_of_active {G : Type*} [Group G] [Finite G] {w a : G}
    (hw : orderOf w = 2) (ha : orderOf a = 2) (hwa : w * a = a * w) {L : Subgroup G}
    (hLw : L ≤ centralizer ({w} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({w} : Set G)))) {d l : G}
    (hd : d ∈ (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype ⊓
      centralizer ({w} : Set G))
    (hl : l ∈ L) (hdl : l⁻¹ * d⁻¹ * l * d ∉ (pPrimeCore 2 L).map L.subtype) :
    GSUnbalancingTriple w a L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cw : Subgroup G := centralizer ({w} : Set G) with hCw
  set Ca : Subgroup G := centralizer ({a} : Set G) with hCa
  set D : Subgroup G := (pPrimeCore 2 Ca).map Ca.subtype ⊓ Cw with hD
  have haCw : a ∈ Cw := mem_centralizer_singleton_iff.mpr hwa.symm
  set t : ↥Cw := ⟨a, haCw⟩ with ht
  have hDCw : D ≤ Cw := inf_le_right
  have hDCa : D ≤ Ca := inf_le_left.trans (map_subtype_le _)
  set D' : Subgroup ↥Cw := D.subgroupOf Cw with hD'
  set L' : Subgroup ↥Cw := L.subgroupOf Cw with hL'
  have ht2 : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ha
  have hDC : D' ≤ centralizer ({t} : Set ↥Cw) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hDCa hx)
  have hDn : (D'.subgroupOf (centralizer ({t} : Set ↥Cw))).Normal := by
    refine (normal_subgroupOf_iff hDC).mpr fun x k hx hk => ?_
    have hka : (k : G) ∈ Ca :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk))
    exact Subgroup.mem_inf.mpr ⟨conj_mem_map_pPrimeCore hka (Subgroup.mem_inf.mp hx).1,
      (k * x * k⁻¹).2⟩
  have hDodd : Odd (Nat.card D') := by
    have h1 : Nat.card D' = Nat.card D := by
      rw [hD', ← card_map_of_injective Cw.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hDCw]
    have h2 : Nat.card D ∣ Nat.card ((pPrimeCore 2 Ca).map Ca.subtype) :=
      card_dvd_of_le inf_le_left
    rw [card_map_of_injective Ca.subtype_injective] at h2
    rw [h1]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
  have hO : ((pPrimeCore 2 ↥L').map L'.subtype).map Cw.subtype =
      (pPrimeCore 2 ↥L).map L.subtype := by
    let e : ↥L' ≃* ↥L := subgroupOfEquivOfLe hLw
    rw [map_map, ← pPrimeCore_map_iso 2 e, map_map]
    rfl
  have hLD : ¬ ⁅L', D'⁆ ≤ (pPrimeCore 2 ↥L').map L'.subtype := by
    intro hle
    apply hdl
    have hl' : (⟨l, hLw hl⟩ : ↥Cw) ∈ L' := hl
    have hd' : (⟨d, hd.2⟩ : ↥Cw) ∈ D' := hd
    have h1 := hle (commutator_mem_commutator (inv_mem hl') (inv_mem hd'))
    have h2 := mem_map_of_mem Cw.subtype h1
    rw [hO] at h2
    have h3 : Cw.subtype ⁅(⟨l, hLw hl⟩ : ↥Cw)⁻¹, (⟨d, hd.2⟩ : ↥Cw)⁻¹⁆ = l⁻¹ * d⁻¹ * l * d := by
      simp [commutatorElement_def]
    rwa [h3] at h2
  obtain ⟨-, -, hLD', hLt⟩ := odd_fixed_core_active_two_component ht2 hDC hDn hDodd hL hLD
  have hmapL : L'.map Cw.subtype = L := by
    rw [hL', subgroupOf_map_subtype, inf_eq_left.mpr hLw]
  have hmapD : D'.map Cw.subtype = D := by
    rw [hD', subgroupOf_map_subtype, inf_eq_left.mpr hDCw]
  refine gsUnbalancingTriple_iff.mpr ⟨hw, ha, hwa, hLw, hL, ?_, ?_⟩
  · have := congrArg (map Cw.subtype) hLt
    rw [map_commutator, hmapL, MonoidHom.map_zpowers] at this
    exact this
  · have := congrArg (map Cw.subtype) hLD'
    rw [map_commutator, hmapL, hmapD] at this
    exact this

end Eight

end CFSG.ComponentClassification.GSThmB
