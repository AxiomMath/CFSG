module

public import CFSG.LargeExtraspecial.AS35YFBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

namespace Setting

structure AscImage {Y : Type*} [Group Y] (N : Subgroup Y) (τ : Y) : Prop where
  isPGroup : IsPGroup 2 N
  mem : τ ∈ N
  commute : ∀ y ∈ N, y * τ = τ * y
  normal : ∀ c : Y, c * τ = τ * c → ∀ y ∈ N, c * y * c⁻¹ ∈ N

theorem AscImage.map {Y Y' : Type*} [Group Y] [Group Y'] {N : Subgroup Y} {τ : Y}
    (h : AscImage N τ) (ψ : Y ≃* Y') : AscImage (N.map ψ.toMonoidHom) (ψ τ) where
  isPGroup := h.isPGroup.map _
  mem := ⟨τ, h.mem, rfl⟩
  commute := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h.commute y hy]
  normal := by
    rintro c hc _ ⟨y, hy, rfl⟩
    obtain ⟨c', rfl⟩ := ψ.surjective c
    have hc' : c' * τ = τ * c' := ψ.injective (by simpa only [map_mul] using hc)
    exact ⟨c' * y * c'⁻¹, h.normal c' hc' y hy, by simp⟩

theorem asc_mem_of_mk_commute {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {a b : H}
    (h : (QuotientGroup.mk a : H ⧸ N) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a) : a * b * (b * a)⁻¹ ∈ N := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, h, mul_inv_cancel]

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem ascImage_ascPhat (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    AscImage (S.ascPhat g) (QuotientGroup.mk (ascTL htD htM)) where
  isPGroup := ascPhat_isPGroup hP hS htD htM
  mem := mem_ascPhat hP hS htD htM
  commute _ hy := ascPhat_commute hP hS htD htM hy
  normal c hc y hy := by
    obtain ⟨cL, rfl⟩ := QuotientGroup.mk'_surjective (center S.LbarAsc) c
    exact ascPhat_normalized hst hP hS htD htM cL hc hy

theorem asc_Pbar_le_Lbar_of_inner (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hinn : ∀ p : S.Mbar, (p : S.O) ∈ S.PbarAsc g →
      ascAct hst p ∈ inner (S.LbarAsc ⧸ center S.LbarAsc)) :
    S.PbarAsc g ≤ S.LbarAsc := by
  intro p hp
  obtain ⟨y, hy⟩ := hinn ⟨p, asc_Pbar_le_Mbar g hp⟩ hp
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center S.LbarAsc) y
  exact asc_mem_Lbar_of_inner hst hP hS htD htM (p := ⟨p, asc_Pbar_le_Mbar g hp⟩) hp hy.symm

omit hst in
theorem card_subgroupOf_of_le {g : G} (hle : S.PbarAsc g ≤ S.LbarAsc) :
    Nat.card ((S.PbarAsc g).subgroupOf S.LbarAsc) = Nat.card (S.PbarAsc g) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem card_ascPhat_of_le (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (hle : S.PbarAsc g ≤ S.LbarAsc) :
    Nat.card (S.ascPhat g) = 2 ^ (2 * S.width - 3) := by
  rw [card_ascPhat hst hP hS htD htM, card_subgroupOf_of_le hle]
  exact (hP G S hS g htD htM).2.2.1

omit hst in
theorem asc_Pbar_not_comm (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∃ a ∈ S.PbarAsc g, ∃ b ∈ S.PbarAsc g, a * b ≠ b * a := by
  have hPg := hP G S hS g htD htM
  by_contra hall
  push Not at hall
  have hle : S.PbarAsc g ≤ zpowers (S.ρ ⟨_, htM⟩) := by
    intro x hx
    rcases hPg.2.2.2.1 x hx (hall x hx) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hPg.2.2.1] at h1
  have h2 : orderOf (S.ρ ⟨_, htM⟩) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num)
    (by rw [sq]; exact asc_mul_self_of_mem (S.ρ_mem_DbarAsc htD htM))
  have h3 : 2 ^ 3 ≤ 2 ^ (2 * S.width - 3) :=
    Nat.pow_le_pow_right (by norm_num) (by have := hS.three_le_width; omega)
  omega

theorem ascPhat_not_comm_of_le (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (hle : S.PbarAsc g ≤ S.LbarAsc) :
    ∃ a ∈ S.ascPhat g, ∃ b ∈ S.ascPhat g, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := asc_Pbar_not_comm hP hS htD htM
  refine ⟨QuotientGroup.mk ⟨a, hle ha⟩, ⟨⟨a, hle ha⟩, ha, rfl⟩,
    QuotientGroup.mk ⟨b, hle hb⟩, ⟨⟨b, hle hb⟩, hb, rfl⟩, fun h => hab ?_⟩
  have hc : (⟨a, hle ha⟩ * ⟨b, hle hb⟩ * (⟨b, hle hb⟩ * ⟨a, hle ha⟩)⁻¹ : S.LbarAsc) ∈
      center S.LbarAsc := asc_mem_of_mk_commute _ h
  have hP2 := ((hP G S hS g htD htM).2.1.1).comap_of_injective S.LbarAsc.subtype
    S.LbarAsc.subtype_injective
  have hmem : (⟨a, hle ha⟩ * ⟨b, hle hb⟩ * (⟨b, hle hb⟩ * ⟨a, hle ha⟩)⁻¹ : S.LbarAsc) ∈
      (S.PbarAsc g).comap S.LbarAsc.subtype := by
    simp only [mem_comap, coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem ha hb) (inv_mem (mul_mem hb ha))
  have h1 := asc_eq_one_of_two_pow_of_odd (x := ⟨_, hmem⟩) (hP2 ⟨_, hmem⟩)
    (asc_center_odd hst hc)
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  exact mul_inv_eq_one.mp h2

theorem asc_mem_Lbar_of_mem_inner (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {p : S.O}
    (hp : p ∈ S.PbarAsc g)
    (hinn : ascAct hst ⟨p, asc_Pbar_le_Mbar g hp⟩ ∈ inner (S.LbarAsc ⧸ center S.LbarAsc)) :
    p ∈ S.LbarAsc := by
  obtain ⟨y, hy⟩ := hinn
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center S.LbarAsc) y
  exact asc_mem_Lbar_of_inner hst hP hS htD htM (p := ⟨p, asc_Pbar_le_Mbar g hp⟩) hp hy.symm

omit hst in
theorem asc_card_le_two {H : Type*} [Group H] {K : Subgroup H} {a m : ℕ}
    (hK : Nat.card K ∣ 2 ^ a) (hm : Nat.card K ∣ m) (h4 : ¬ 4 ∣ m) : Nat.card K ≤ 2 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hK
  rw [hj] at hm ⊢
  by_contra h
  have hj2 : 2 ≤ j := by
    by_contra h'
    interval_cases j <;> simp_all
  exact h4 ((pow_dvd_pow 2 hj2).trans hm)

omit hst in
theorem asc_card_le_two_mul_of_outer {P X : Type*} [Group P] [Group X] [Finite P]
    (K : Subgroup P) (α : P →* MulAut X) {a : ℕ} (h2 : Nat.card P = 2 ^ a)
    (hK : ∀ p : P, α p ∈ inner X → p ∈ K) (hout : ¬ 4 ∣ Nat.card (Outer X)) :
    Nat.card P ≤ 2 * Nat.card K := by
  set φ : P →* Outer X := (QuotientGroup.mk' (inner X)).comp α with hφ
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card P := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h3 : Nat.card φ.range ≤ 2 :=
    asc_card_le_two ((Subgroup.card_range_dvd φ).trans (dvd_of_eq h2))
      (Subgroup.card_subgroup_dvd_card _) hout
  have h4 : φ.ker ≤ K := by
    intro p hp
    have hp' : φ p = 1 := hp
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hp'
    exact hK p hp'
  have h5 : Nat.card φ.ker ≤ Nat.card K := Subgroup.card_le_of_le h4
  calc Nat.card P = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card K * 2 := Nat.mul_le_mul h5 h3
    _ = 2 * Nat.card K := mul_comm _ _

omit hst in
theorem asc_card_subgroupOf_comm {H : Type*} [Group H] (A B : Subgroup H) :
    Nat.card (A.subgroupOf B) = Nat.card (B.subgroupOf A) :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨((x : B) : H), x.2⟩, (x : B).2⟩
      invFun := fun x => ⟨⟨((x : A) : H), x.2⟩, (x : A).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem asc_card_Pbar_le_two_mul (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hout : ¬ 4 ∣ Nat.card (Outer (S.LbarAsc ⧸ center S.LbarAsc))) :
    Nat.card (S.PbarAsc g) ≤ 2 * Nat.card ((S.PbarAsc g).subgroupOf S.LbarAsc) := by
  rw [asc_card_subgroupOf_comm]
  refine asc_card_le_two_mul_of_outer (S.LbarAsc.subgroupOf (S.PbarAsc g))
    ((ascActHom hst).comp (Subgroup.inclusion (asc_Pbar_le_Mbar g)))
    (hP G S hS g htD htM).2.2.1 (fun p hp => ?_) hout
  exact Subgroup.mem_subgroupOf.mpr (asc_mem_Lbar_of_mem_inner hst hP hS htD htM p.2 hp)

end Setting

end CFSG.LargeExtraspecial
