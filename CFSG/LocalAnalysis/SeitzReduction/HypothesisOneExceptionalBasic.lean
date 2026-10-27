module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

@[expose] def NoNormalZ4OrZ2xZ4 (G : Type*) [Group G] : Prop :=
  ∀ B : Subgroup G, B.Normal → ¬ (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))

@[expose] def AbelianNormalCardLeTwo (G : Type*) [Group G] : Prop :=
  ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ 2

@[expose] def NoAbelianNormal (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, P.Normal → (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → P = ⊥

theorem NoAbelianNormal.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : NoAbelianNormal G) : NoAbelianNormal H := by
  intro P hP hab
  have h1 := h (P.comap e.toMonoidHom) (hP.comap _) fun a ha b hb => e.injective (by
    rw [map_mul, map_mul]
    exact hab _ ha _ hb)
  rw [← map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective P, h1, Subgroup.map_bot]

theorem NoNormalZ4OrZ2xZ4.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : NoNormalZ4OrZ2xZ4 G) : NoNormalZ4OrZ2xZ4 H := by
  intro B hB hiso
  have eB : B.comap e.toMonoidHom ≃* B := (e.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective B))
  apply h _ (hB.comap _)
  rcases hiso with hi | hi
  · obtain ⟨i⟩ := hi
    exact Or.inl ⟨eB.trans i⟩
  · obtain ⟨i⟩ := hi
    exact Or.inr ⟨eB.trans i⟩

theorem AbelianNormalCardLeTwo.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : AbelianNormalCardLeTwo G) : AbelianNormalCardLeTwo H := by
  intro B hB hab
  have hcard : Nat.card (B.comap e.toMonoidHom) = Nat.card B :=
    Nat.card_congr ((e.subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective B))).toEquiv
  rw [← hcard]
  refine h _ (hB.comap _) fun a ha b hb => e.injective ?_
  rw [map_mul, map_mul]
  exact hab _ ha _ hb

theorem mul_comm_of_mulEquiv {G A : Type*} [Group G] [CommGroup A] {B : Subgroup G}
    (i : B ≃* A) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h : (⟨a, ha⟩ : B) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    i.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

theorem AbelianNormalCardLeTwo.noNormalZ4OrZ2xZ4 {G : Type*} [Group G]
    (h : AbelianNormalCardLeTwo G) : NoNormalZ4OrZ2xZ4 G := by
  intro B hB hiso
  rcases hiso with hi | hi
  · obtain ⟨i⟩ := hi
    have hc := h B hB (mul_comm_of_mulEquiv i)
    rw [Nat.card_congr i.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card] at hc
    omega
  · obtain ⟨i⟩ := hi
    have hc := h B hB (mul_comm_of_mulEquiv i)
    rw [Nat.card_congr i.toEquiv, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_multiplicative, Fintype.card_multiplicative, ZMod.card, ZMod.card] at hc
    omega

theorem hypothesisOne_of_centralizers {Y : Type*} [Group Y]
    (h : ∀ M : Subgroup (MulAut Y), inner Y ≤ M → ∀ x ∈ M, orderOf x = 2 →
      CFSG.oddCore ↥(M ⊓ centralizer ({x} : Set (MulAut Y))) = ⊥ ∧
        NoNormalZ4OrZ2xZ4 ↥(M ⊓ centralizer ({x} : Set (MulAut Y)))) :
    HypothesisOne Y := by
  intro M hM x hxM hx2 B hB hiso
  obtain ⟨hcore, hno⟩ := h M hM x hxM hx2
  have hcore' : CFSG.Assembly.oddCore ↥(M ⊓ centralizer ({x} : Set (MulAut Y))) = ⊥ := hcore
  exact (NoNormalZ4OrZ2xZ4.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcore').trans QuotientGroup.quotientBot).symm hno)
    B hB hiso

theorem hypothesisOne_of_inner_outer {Y : Type*} [Group Y]
    (hcore : ∀ M : Subgroup (MulAut Y), inner Y ≤ M → ∀ x ∈ M, orderOf x = 2 →
      CFSG.oddCore ↥(M ⊓ centralizer ({x} : Set (MulAut Y))) = ⊥)
    (hinner : ∀ M : Subgroup (MulAut Y), inner Y ≤ M → ∀ x ∈ inner Y, orderOf x = 2 →
      NoNormalZ4OrZ2xZ4 ↥(M ⊓ centralizer ({x} : Set (MulAut Y))))
    (houter : ∀ M : Subgroup (MulAut Y), inner Y ≤ M → ∀ x ∈ M, x ∉ inner Y → orderOf x = 2 →
      AbelianNormalCardLeTwo ↥(M ⊓ centralizer ({x} : Set (MulAut Y)))) :
    HypothesisOne Y := by
  refine hypothesisOne_of_centralizers fun M hM x hxM hx2 => ⟨hcore M hM x hxM hx2, ?_⟩
  by_cases hx : x ∈ inner Y
  · exact hinner M hM x hx hx2
  · exact (houter M hM x hxM hx hx2).noNormalZ4OrZ2xZ4

theorem eq_one_or_eq_of_mem_zpowers {A : Type*} [Group A] {η x : A} (hη2 : η ^ 2 = 1)
    (hx : x ∈ zpowers η) : x = 1 ∨ x = η := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hη2' : η ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hη2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, add_zero, zpow_mul, hη2', one_zpow]
  · right
    rw [hk, h, zpow_add, zpow_mul, hη2', one_zpow, one_mul, zpow_one]

theorem eq_bot_of_normal_of_isSimpleGroup {A : Type*} [Group A] {η : A} (hη2 : η ^ 2 = 1)
    {N : Subgroup A} [IsSimpleGroup N] (hNη : N ≤ centralizer ({η} : Set A)) (hηN : η ∉ N)
    (hcent : ∀ c ∈ centralizer ({η} : Set A), (∀ n ∈ N, c * n = n * c) → c ∈ zpowers η) :
    NoAbelianNormal N := by
  intro P hP hPab
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := exists_ne (1 : N)
    have hcomm : ∀ m ∈ N, (n : A) * m = m * n := by
      intro m hm
      have := hPab n (h ▸ mem_top n) ⟨m, hm⟩ (h ▸ mem_top _)
      exact congrArg Subtype.val this
    rcases eq_one_or_eq_of_mem_zpowers hη2 (hcent n (hNη n.2) hcomm) with h1 | h1
    · exact hn (Subtype.ext h1)
    · exact hηN (h1 ▸ n.2)

theorem abelianNormalCardLeTwo_of_normal_of_centralizer {A : Type*} [Group A] {η : A}
    (hη2 : η ^ 2 = 1) {N H : Subgroup A} (hNH : N ≤ H) (hNη : N ≤ centralizer ({η} : Set A))
    (hNnorm : ∀ c ∈ centralizer ({η} : Set A), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hNab : NoAbelianNormal N)
    (hcent : ∀ c ∈ centralizer ({η} : Set A), (∀ n ∈ N, c * n = n * c) → c ∈ zpowers η) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({η} : Set A)) := by
  intro B hB hBab
  have hNS : ∀ n ∈ N, n ∈ H ⊓ centralizer ({η} : Set A) := fun n hn =>
    mem_inf.2 ⟨hNH hn, hNη hn⟩
  have hPn : ((B.map (H ⊓ centralizer ({η} : Set A)).subtype).subgroupOf N).Normal := by
    constructor
    intro p hp n
    rw [mem_subgroupOf] at hp ⊢
    obtain ⟨b, hb, hbp⟩ := hp
    refine ⟨⟨n, hNS n n.2⟩ * b * (⟨n, hNS n n.2⟩ : ↥(H ⊓ centralizer ({η} : Set A)))⁻¹,
      hB.conj_mem b hb _, ?_⟩
    have hbp' : (b : A) = p := hbp
    simp [hbp']
  have hPab : ∀ a ∈ (B.map (H ⊓ centralizer ({η} : Set A)).subtype).subgroupOf N,
      ∀ b ∈ (B.map (H ⊓ centralizer ({η} : Set A)).subtype).subgroupOf N, a * b = b * a := by
    intro a ha b hb
    rw [mem_subgroupOf] at ha hb
    obtain ⟨a', ha', hae⟩ := ha
    obtain ⟨b', hb', hbe⟩ := hb
    apply Subtype.ext
    have := congrArg Subtype.val (hBab a' ha' b' hb')
    simpa [← hae, ← hbe] using this
  have hP1 := hNab _ hPn hPab
  have hBz : B.map (H ⊓ centralizer ({η} : Set A)).subtype ≤ zpowers η := by
    rintro _ ⟨b, hb, rfl⟩
    have hbη : (b : A) ∈ centralizer ({η} : Set A) := (mem_inf.1 b.2).2
    refine hcent _ hbη fun n hn => ?_
    have hcN : (b : A) * n * (b : A)⁻¹ * n⁻¹ ∈ N :=
      N.mul_mem (hNnorm _ hbη n hn) (N.inv_mem hn)
    have hcB : (b : A) * n * (b : A)⁻¹ * n⁻¹ ∈ B.map (H ⊓ centralizer ({η} : Set A)).subtype := by
      refine ⟨b * (⟨n, hNS n hn⟩ * b⁻¹ * (⟨n, hNS n hn⟩ : ↥(H ⊓ centralizer ({η} : Set A)))⁻¹),
        B.mul_mem hb (hB.conj_mem _ (B.inv_mem hb) _), ?_⟩
      simp [mul_assoc]
    have hmem : (⟨_, hcN⟩ : N) ∈ (B.map (H ⊓ centralizer ({η} : Set A)).subtype).subgroupOf N := by
      rw [mem_subgroupOf]
      exact hcB
    rw [hP1, mem_bot] at hmem
    have h1 := congrArg Subtype.val hmem
    simp only [OneMemClass.coe_one] at h1
    calc (b : A) * n = (b : A) * n * (b : A)⁻¹ * n⁻¹ * (n * b) := by group
      _ = n * b := by rw [h1, one_mul]
  have hfin : Finite (zpowers η) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, hη2⟩).finite_zpowers
  have hcard : Nat.card B = Nat.card (B.map (H ⊓ centralizer ({η} : Set A)).subtype) :=
    (card_map_of_injective (H ⊓ centralizer ({η} : Set A)).subtype_injective).symm
  rw [hcard]
  calc Nat.card (B.map (H ⊓ centralizer ({η} : Set A)).subtype) ≤ Nat.card (zpowers η) :=
        card_le_of_le hBz
    _ = orderOf η := Nat.card_zpowers η
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hη2)

theorem abelianNormalCardLeTwo_of_isSimpleGroup {A : Type*} [Group A] {η : A}
    (hη2 : η ^ 2 = 1) {N H : Subgroup A} [IsSimpleGroup N] (hNH : N ≤ H)
    (hNη : N ≤ centralizer ({η} : Set A)) (hηN : η ∉ N)
    (hNnorm : ∀ c ∈ centralizer ({η} : Set A), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hcent : ∀ c ∈ centralizer ({η} : Set A), (∀ n ∈ N, c * n = n * c) → c ∈ zpowers η) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({η} : Set A)) :=
  abelianNormalCardLeTwo_of_normal_of_centralizer hη2 hNH hNη hNnorm
    (eq_bot_of_normal_of_isSimpleGroup hη2 hNη hηN hcent) hcent

theorem inner_le_map_conj_of_le {C : Type*} [Group C] {H : Subgroup (MulAut C)}
    (hH : inner C ≤ H) (ψ : MulAut C) : inner C ≤ H.map (MulAut.conj ψ).toMonoidHom := by
  intro y hy
  refine ⟨ψ⁻¹ * y * ψ, hH ?_, ?_⟩
  · have := (inner_normal C).conj_mem y hy ψ⁻¹
    rwa [inv_inv] at this
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem AbelianNormalCardLeTwo.of_conj {C : Type*} [Group C] {H : Subgroup (MulAut C)}
    {α η ψ : MulAut C} (hψ : ψ * α * ψ⁻¹ = η)
    (h : AbelianNormalCardLeTwo ↥(H.map (MulAut.conj ψ).toMonoidHom ⊓
      centralizer ({η} : Set (MulAut C)))) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({α} : Set (MulAut C))) := by
  have hcentr : H.map (MulAut.conj ψ).toMonoidHom ⊓ centralizer ({η} : Set (MulAut C)) =
      (H ⊓ centralizer ({α} : Set (MulAut C))).map (MulAut.conj ψ).toMonoidHom := by
    ext y
    simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzη⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [← hψ] at hzη
      have : ψ * (z * α) * ψ⁻¹ = ψ * (α * z) * ψ⁻¹ := by
        calc ψ * (z * α) * ψ⁻¹ = ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹) := by group
          _ = ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹) := hzη
          _ = ψ * (α * z) * ψ⁻¹ := by group
      simpa using this
    · rintro ⟨z, ⟨hz, hzα⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [← hψ]
      calc ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (z * α) * ψ⁻¹ := by group
        _ = ψ * (α * z) * ψ⁻¹ := by rw [hzα]
        _ = ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹) := by group
  refine h.of_mulEquiv (((MulAut.conj ψ).subgroupMap _).trans
    (MulEquiv.subgroupCongr hcentr.symm)).symm

end CFSG.SeitzReduction
