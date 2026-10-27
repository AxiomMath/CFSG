module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantSylow

open Subgroup
open scoped Pointwise

theorem conj_mem_inf {G : Type*} [Group G] (a : G) (S X : Subgroup G)
    (haS : a ∈ normalizer (S : Set G)) (haX : a ∈ normalizer (X : Set G)) (n : G)
    (hn : n ∈ S ⊓ normalizer (X : Set G)) : a * n * a⁻¹ ∈ S ⊓ normalizer (X : Set G) := by
  have hnS : n ∈ S := hn.1
  have hnX : n ∈ normalizer (X : Set G) := hn.2
  refine ⟨(Subgroup.mem_normalizer_iff.mp haS n).mp hnS, ?_⟩
  show a * n * a⁻¹ ∈ normalizer (X : Set G)
  rw [Subgroup.mem_normalizer_iff] at hnX haX ⊢
  intro h
  have e : a * n * a⁻¹ * h * (a * n * a⁻¹)⁻¹ = a * (n * (a⁻¹ * h * a) * n⁻¹) * a⁻¹ := by
    simp [mul_assoc, mul_inv_rev]
  rw [e, ← haX (n * (a⁻¹ * h * a) * n⁻¹), ← hnX (a⁻¹ * h * a)]
  have key := haX (a⁻¹ * h * a)
  have hs : a * (a⁻¹ * h * a) * a⁻¹ = h := by simp [mul_assoc]
  rw [hs] at key
  exact key.symm

@[expose] def conjSubEquiv {G : Type*} [Group G] (N : Subgroup G) (a : G)
    (h1 : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (h2 : ∀ n ∈ N, a⁻¹ * n * a ∈ N) : N ≃* N where
  toFun n := ⟨a * n * a⁻¹, h1 n n.2⟩
  invFun n := ⟨a⁻¹ * n * a, h2 n n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])

theorem conjSubEquiv_apply {G : Type*} [Group G] (N : Subgroup G) (a : G)
    (h1 : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (h2 : ∀ n ∈ N, a⁻¹ * n * a ∈ N) (n : N) :
    ((conjSubEquiv N a h1 h2 n : N) : G) = a * n * a⁻¹ := rfl

theorem exists_inv_sylow_inf {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (A S X : Subgroup G) (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S)
    (hAS : A ≤ normalizer (S : Set G)) (hAX : A ≤ normalizer (X : Set G))
    (hXS : X ≤ S) (hX : IsPGroup q X) :
    ∃ R : Subgroup G, R ≤ S ⊓ normalizer (X : Set G) ∧ IsPGroup q R ∧ X ≤ R ∧
      A ≤ normalizer (R : Set G) ∧
      ∀ Y : Subgroup G, Y ≤ S ⊓ normalizer (X : Set G) → IsPGroup q Y → R ≤ Y → Y = R := by
  set N : Subgroup G := S ⊓ normalizer (X : Set G)
  have hNS : N ≤ S := inf_le_left
  have hNX : N ≤ normalizer (X : Set G) := inf_le_right
  have hXN : X ≤ N := le_inf hXS Subgroup.le_normalizer
  have hpN : ¬ p ∣ Nat.card N := fun h => hS (h.trans (Subgroup.card_dvd_of_le hNS))
  have hinv : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn =>
    conj_mem_inf a S X (hAS ha) (hAX ha) n hn
  have hinv' : ∀ a ∈ A, ∀ n ∈ N, a⁻¹ * n * a ∈ N := fun a ha n hn => by
    have := conj_mem_inf a⁻¹ S X (hAS (A.inv_mem ha)) (hAX (A.inv_mem ha)) n hn
    rw [inv_inv] at this
    exact this
  let φ : A →* MulAut N :=
    { toFun := fun a => conjSubEquiv N a (hinv a a.2) (hinv' a a.2)
      map_one' := MulEquiv.ext fun n => Subtype.ext (by
        rw [conjSubEquiv_apply]; simp)
      map_mul' := fun a b => MulEquiv.ext fun n => Subtype.ext (by
        simp [MulAut.mul_apply, conjSubEquiv_apply, mul_assoc, mul_inv_rev]) }
  let act : MulAction A (Sylow q N) := MulAction.compHom (Sylow q N) φ
  have hcard : ¬ p ∣ Nat.card (Sylow q N) := by
    obtain ⟨P0, -⟩ := IsPGroup.exists_le_sylow (P := (⊥ : Subgroup N)) IsPGroup.of_bot
    exact fun h => hpN ((h.trans (Sylow.card_dvd_index P0)).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q N) hcard
  have hP' := MulAction.mem_fixedPoints.mp hP
  have hfwd : ∀ g : A, ∀ m : N, m ∈ (P : Subgroup N) → φ g m ∈ (P : Subgroup N) := by
    intro g m hm
    have hc : (φ g) • (P : Subgroup N) = (P : Subgroup N) :=
      congrArg (fun Q : Sylow q N => (Q : Subgroup N)) (hP' g)
    have hm' : (φ g) • m ∈ (φ g) • (P : Subgroup N) := Subgroup.smul_mem_pointwise_smul _ _ _ hm
    rw [hc] at hm'
    exact hm'
  refine ⟨(P : Subgroup N).map N.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, -, rfl⟩
    exact n.2
  · exact P.isPGroup'.map N.subtype
  ·
    have hXsub : (X.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNX
    have hXq : IsPGroup q (X.subgroupOf N) := hX.comap_subtype
    have hle : X.subgroupOf N ≤ (P : Subgroup N) := IsPGroup.le_sylow_of_normal hXq P
    intro x hx
    have hxN : x ∈ N := hXN hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  ·
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_map.mpr ⟨φ ⟨a, ha⟩ n, hfwd ⟨a, ha⟩ n hn, rfl⟩
    · intro hh
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hh
      refine Subgroup.mem_map.mpr ⟨φ ⟨a⁻¹, A.inv_mem ha⟩ m, hfwd _ m hm, ?_⟩
      have hme' : (m : G) = a * h * a⁻¹ := hme
      show a⁻¹ * (m : G) * a⁻¹⁻¹ = h
      rw [hme']
      simp [mul_assoc]
  ·
    intro Y hY hYq hRY
    have hYsub : IsPGroup q (Y.subgroupOf N) := hYq.comap_subtype
    have hPY : (P : Subgroup N) ≤ Y.subgroupOf N := by
      intro n hn
      exact Subgroup.mem_subgroupOf.mpr (hRY (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩))
    have hYP : Y.subgroupOf N = (P : Subgroup N) := P.is_maximal' hYsub hPY
    calc Y = (Y.subgroupOf N).map N.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY]
      _ = (P : Subgroup N).map N.subtype := by rw [hYP]

theorem ng_growth {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] (P X : Subgroup G)
    (hP : IsPGroup q P) (hXP : X ≤ P) (hne : X ≠ P) :
    ∃ g ∈ P, g ∉ X ∧ g ∈ Subgroup.normalizer (X : Set G) := by
  have : Finite P := inferInstance
  have : Group.IsNilpotent P := hP.isNilpotent
  let H : Subgroup P := X.subgroupOf P
  have hH : H ≠ ⊤ := by
    intro h
    apply hne
    apply le_antisymm hXP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ H := by rw [h]; exact Subgroup.mem_top _
    exact this
  have hnc := (normalizerCondition_iff_only_full_group_self_normalizing (G := P)).mp
    (Group.normalizerCondition_of_isNilpotent) H
  have hlt : H < Subgroup.normalizer H := lt_of_le_of_ne Subgroup.le_normalizer
    (fun h => hH (hnc h.symm))
  obtain ⟨g, hgN, hgH⟩ := IsConcreteLE.exists_of_lt hlt
  have hgX : ∀ h ∈ X, (g : G) * h * (g : G)⁻¹ ∈ X := by
    intro h hh
    have hhP : (⟨h, hXP hh⟩ : P) ∈ H := Subgroup.mem_subgroupOf.mpr hh
    have := (Subgroup.mem_normalizer_iff.mp hgN ⟨h, hXP hh⟩).mp hhP
    exact Subgroup.mem_subgroupOf.mp (by simpa using this)
  have hmap : X.map (MulAut.conj (g : G)).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgX x hx
  have hmapEq : X.map (MulAut.conj (g : G)).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective])
  refine ⟨g.1, g.2, fun hgX' => hgH (Subgroup.mem_subgroupOf.mpr hgX'), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hgX h hh
  · intro hh
    have hmem : (MulAut.conj (g : G)) h ∈ X.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [hmapEq]; exact hh
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hmem
    have hxh : x = h := by
      simpa using hxe
    simpa [hxh] using hx

theorem exists_invariant_sylow_ge {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (A S X : Subgroup G) (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S)
    (hAS : A ≤ normalizer (S : Set G)) (hXS : X ≤ S) (hX : IsPGroup q X)
    (hAX : A ≤ normalizer (X : Set G)) :
    ∃ P : Subgroup G, P ≤ S ∧ IsPGroup q P ∧ ¬ q ∣ (P.subgroupOf S).index ∧ X ≤ P ∧
      A ≤ normalizer (P : Set G) := by
  suffices H : ∀ n : ℕ, ∀ Y : Subgroup G, Nat.card S - Nat.card Y = n → Y ≤ S → IsPGroup q Y →
      A ≤ normalizer (Y : Set G) → ∃ P : Subgroup G, P ≤ S ∧ IsPGroup q P ∧
        ¬ q ∣ (P.subgroupOf S).index ∧ Y ≤ P ∧ A ≤ normalizer (P : Set G) from
    H _ X rfl hXS hX hAX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hn hYS hYq hAY
  obtain ⟨R, hRN, hRq, hYR, hAR, hmax⟩ := exists_inv_sylow_inf A S Y hA hS hAS hAY hYS hYq
  by_cases hRY : R = Y
  ·
    obtain ⟨Q, hQ⟩ := (hYq.comap_subtype : IsPGroup q (Y.subgroupOf S)).exists_le_sylow
    have hYmax : ∀ Z : Subgroup G, Z ≤ S ⊓ normalizer (Y : Set G) → IsPGroup q Z →
        Y ≤ Z → Z = Y := fun Z hZ hZq hYZ => by
      have h1 : R ≤ Z := by rw [hRY]; exact hYZ
      exact (hmax Z hZ hZq h1).trans hRY
    set P : Subgroup G := Q.toSubgroup.map S.subtype
    have hPS : P ≤ S := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hPq : IsPGroup q P := Q.isPGroup'.map S.subtype
    have hYP : Y ≤ P := by
      intro y hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hYS hy⟩, hQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
    have hYeq : Y = P := by
      by_contra hne
      obtain ⟨g, hgP, hgY, hgN⟩ := ng_growth P Y hPq hYP hne
      have hZS : P ⊓ normalizer (Y : Set G) ≤ S ⊓ normalizer (Y : Set G) :=
        fun x hx => ⟨hPS hx.1, hx.2⟩
      have hZq : IsPGroup q ((P ⊓ normalizer (Y : Set G) : Subgroup G)) := IsPGroup.to_le hPq inf_le_left
      have hYZ : Y ≤ P ⊓ normalizer (Y : Set G) := le_inf hYP Subgroup.le_normalizer
      have hZY := hYmax (P ⊓ normalizer (Y : Set G)) hZS hZq hYZ
      have hgZ : g ∈ P ⊓ normalizer (Y : Set G) := ⟨hgP, hgN⟩
      rw [hZY] at hgZ
      exact hgY hgZ
    have hsub : P.subgroupOf S = Q.toSubgroup := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hxy : y = x := Subtype.ext hyx
        rw [← hxy]
        exact hy
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    refine ⟨P, hPS, hPq, ?_, hYP, ?_⟩
    · rw [hsub]
      exact Sylow.not_dvd_index Q
    · rw [← hYeq]
      exact hAY
  ·
    have hYR' : Y < R := lt_of_le_of_ne hYR (fun h => hRY h.symm)
    have hlt : Nat.card Y < Nat.card R := Subgroup.card_lt_of_lt hYR'
    have hRS : R ≤ S := hRN.trans inf_le_left
    have hcardRS : Nat.card R ≤ Nat.card S := Subgroup.card_le_of_le hRS
    obtain ⟨P, hPS, hPq, hPi, hRP, hAP⟩ :=
      ih (Nat.card S - Nat.card R) (by omega) R rfl hRS hRq hAR
    exact ⟨P, hPS, hPq, hPi, hYR.trans hRP, hAP⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantSylow
