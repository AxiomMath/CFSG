module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Frame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Central
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Sat

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem pPrimeCore_sl2_three : pPrimeCore 2 SL(2, ZMod 3) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GH74.GLS.IVK.Lifted.pPrimeCore_two_sl2_three (K := ZMod 3)
    (by rw [Nat.card_eq_fintype_card, ZMod.card])

theorem nonempty_quot_equiv_of_equiv_sl2Three {H : Type*} [Group H] (e : H ≃* SL(2, ZMod 3)) :
    Nonempty (H ⧸ pPrimeCore 2 H ≃* SL(2, ZMod 3)) := by
  have hO : pPrimeCore 2 H = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 e
    rw [pPrimeCore_sl2_three] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans e)⟩

theorem inv_mul_mem_pPrimeCore_of_involutions {H : Type*} [Group H] [Finite H]
    (e : H ⧸ pPrimeCore 2 H ≃* SL(2, ZMod 3)) {x y : H} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : x⁻¹ * y ∈ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  have hmem : ∀ z : H, e (QuotientGroup.mk' (pPrimeCore 2 H) z) = 1 → z ∈ pPrimeCore 2 H := by
    intro z hz
    have h1 := (MulEquiv.map_eq_one_iff e).mp hz
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have key : ∀ z : H, orderOf z = 2 → e (QuotientGroup.mk' (pPrimeCore 2 H) z) = -1 := by
    intro z hz
    apply (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd _).mp
    have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow, ← map_pow, hz2, map_one, map_one]
    · have h2 := orderOf_dvd_natCard (⟨z, hmem z h1⟩ : pPrimeCore 2 H)
      rw [Subgroup.orderOf_mk, hz] at h2
      exact (Nat.not_even_iff_odd.mpr GSThmB.OddQuot.odd_card_pPrimeCore)
        (even_iff_two_dvd.mpr h2)
  refine hmem _ ?_
  rw [map_mul, map_mul, map_inv, map_inv, key x hx, key y hy, inv_mul_cancel]

section Central

variable {G Y : Type} [Group G] [Group Y] [Finite G] [Finite Y] {α : G →* Y}

omit [Finite G] [Finite Y] in
theorem map_isSubnormal_of_central (hα : Function.Surjective α) (hk : α.ker ≤ center G) {u : G}
    {J : Subgroup G} (hJC : J ≤ centralizer {u})
    (hJs : (J.subgroupOf (centralizer {u})).IsSubnormal) :
    J.map α ≤ centralizer {α u} ∧ ((J.map α).subgroupOf (centralizer {α u})).IsSubnormal := by
  obtain ⟨hle, hn⟩ := normal_map_centralizer hα hk u
  have hsn : ((J.map α).subgroupOf ((centralizer ({u} : Set G)).map α)).IsSubnormal := by
    have h1 := hJs.map (α.subgroupMap_surjective (centralizer ({u} : Set G)))
    rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap α hJC] at h1
  exact ⟨(map_mono hJC).trans hle,
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans (map_mono hJC) hle hsn hn.isSubnormal⟩

omit [Finite G] [Finite Y] in
theorem ker_subgroupMap_eq_bot (hk : α.ker ≤ center G) {J : Subgroup G}
    (hJZ : J ⊓ center G = ⊥) : (α.subgroupMap J).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : G) ∈ J ⊓ center G := ⟨x.2, hk (by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact MonoidHom.mem_ker.mpr this)⟩
  rw [hJZ, mem_bot] at h1
  exact (mem_bot).mpr (Subtype.ext h1)

omit [Finite G] [Finite Y] in
theorem nonempty_equiv_map_of_inf_center (hk : α.ker ≤ center G) {J : Subgroup G}
    (hJZ : J ⊓ center G = ⊥) : Nonempty (↥J ≃* ↥(J.map α)) :=
  ⟨MulEquiv.ofBijective (α.subgroupMap J)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (ker_subgroupMap_eq_bot hk hJZ),
      α.subgroupMap_surjective J⟩⟩

omit [Finite G] in
theorem isSolvableTwoComponentIn_map_sup (hα : Function.Surjective α) (hk : α.ker ≤ center G)
    {u : G} {J : Subgroup G} (hJC : J ≤ centralizer {u})
    (hJs : (J.subgroupOf (centralizer {u})).IsSubnormal) (hJZ : J ⊓ center G = ⊥)
    (e : ↥J ≃* SL(2, ZMod 3)) :
    IsSolvableTwoComponentIn (J.map α ⊔ (pPrimeCore 2 ↥(centralizer {α u})).map
        (centralizer {α u}).subtype) (centralizer {α u}) ∧
      Nonempty (↥(J.map α ⊔ (pPrimeCore 2 ↥(centralizer {α u})).map
        (centralizer {α u}).subtype) ⧸ pPrimeCore 2 ↥(J.map α ⊔
          (pPrimeCore 2 ↥(centralizer {α u})).map (centralizer {α u}).subtype) ≃*
            SL(2, ZMod 3)) := by
  obtain ⟨hle, hsn⟩ := map_isSubnormal_of_central hα hk hJC hJs
  obtain ⟨eJ⟩ := nonempty_equiv_map_of_inf_center hk hJZ
  obtain ⟨q⟩ := nonempty_quot_equiv_of_equiv_sl2Three (eJ.symm.trans e)
  exact T1.F3.isSolvableTwoComponentIn_sup hle hsn q

end Central

@[expose] def RawF3 (G : Type) [Group G] (t : G) : Prop :=
  ∃ u : G, orderOf u = 2 ∧ u ∉ center G ∧ ∃ J₁ J₂ : Subgroup G,
    J₁ ≤ centralizer {u} ∧ (J₁.subgroupOf (centralizer {u})).IsSubnormal ∧ u ∈ J₁ ∧
    J₁ ⊓ center G = ⊥ ∧ Nonempty (↥J₁ ≃* SL(2, ZMod 3)) ∧
    ((IsTwoComponentIn J₂ (centralizer {u}) ∧ IsQuasisimple ↥J₂ ∧
        ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel (↥J₂ ⧸ center ↥J₂) τ' n' 3 1) ∨
      (J₂ ≤ centralizer {u} ∧ (J₂.subgroupOf (centralizer {u})).IsSubnormal ∧
        J₂ ⊓ center G = ⊥ ∧ Nonempty (↥J₂ ≃* SL(2, ZMod 3)))) ∧
    (t ∈ J₂ ∨ t * u ∈ J₂)

section Concl

variable {G Y : Type} [Group G] [Group Y] [Finite G] [Finite Y] {α : G →* Y}

omit [Finite G] in
theorem RawF3.concl3 (hq : IsQuasisimple G) (hα : Function.Surjective α)
    (hk : α.ker ≤ center G) {t : G} (ht2 : orderOf (α t) = 2) (htZ : t ∈ center G)
    (h : RawF3 G t) : Concl3 Y (α t) := by
  obtain ⟨u, hu2, huZ, J₁, J₂, hJ₁C, hJ₁s, huJ₁, hJ₁Z, ⟨e₁⟩, hJ₂, htJ⟩ := h
  have hαu : α u ≠ 1 := fun h1 => huZ (hk (MonoidHom.mem_ker.mpr h1))
  have hqY : IsQuasisimple Y := isQuasisimple_of_surjective hq hα ⟨⟨α u, 1, hαu⟩⟩
  have hu2' : orderOf (α u) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ← hu2, pow_orderOf_eq_one, map_one]) hαu
  have huZ' : α u ∉ center Y := fun h1 => huZ (mem_center_of_map_mem_center hq hk h1)
  have htZ' : α t ∈ center Y := map_mem_center hα htZ
  have hcomm : α t * α u = α u * α t := (mem_center_iff.mp htZ' (α u)).symm
  have hne : α u ≠ α t := fun h1 => huZ' (h1 ▸ htZ')
  have htu2 : orderOf (α t * α u) = 2 := T1.F3.orderOf_mul_of_commute ht2 hu2' hcomm hne
  have hut2 : orderOf (α u * α t) = 2 := by rw [← hcomm]; exact htu2
  obtain ⟨w, hwJ, hw2, hwu⟩ : ∃ w ∈ J₂.map α, orderOf w = 2 ∧
      orderOf ((α u)⁻¹ * w) = 2 := by
    rcases htJ with h1 | h1
    · refine ⟨α t, mem_map_of_mem α h1, ht2, ?_⟩
      have hinv : (α u)⁻¹ = α u := inv_eq_of_mul_eq_one_right (by
        rw [← sq, ← hu2', pow_orderOf_eq_one])
      rw [hinv]
      exact hut2
    · refine ⟨α t * α u, by rw [← map_mul]; exact mem_map_of_mem α h1, htu2, ?_⟩
      rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      exact ht2
  have hwt : α t ∈ J₂.map α ∨ α t * α u ∈ J₂.map α := by
    rcases htJ with h1 | h1
    · exact .inl (mem_map_of_mem α h1)
    · exact .inr (by rw [← map_mul]; exact mem_map_of_mem α h1)
  obtain ⟨hS₁, ⟨E₁⟩⟩ := isSolvableTwoComponentIn_map_sup hα hk hJ₁C hJ₁s hJ₁Z e₁
  have huS₁ : α u ∈ J₁.map α ⊔ (pPrimeCore 2 ↥(centralizer {α u})).map
      (centralizer {α u}).subtype := mem_sup_left (mem_map_of_mem α huJ₁)
  have huZY : α u ∉ Open.fusionZStar Y := not_mem_fusionZStar hqY hu2' huZ'
  rcases hJ₂ with ⟨hJ₂, hqJ₂, τ', n', hlie⟩ | ⟨hJ₂C, hJ₂s, hJ₂Z, ⟨e₂⟩⟩
  ·
    have hwα : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; exact absurd hw2 (by norm_num)
    obtain ⟨x, hxJ, rfl⟩ := hwJ
    have hq₂ : IsQuasisimple ↥(J₂.map α) := isQuasisimple_map hqJ₂ hxJ hwα
    have h2₂ : 2 ∣ Nat.card ↥(J₂.map α) := by
      have h1 := orderOf_dvd_natCard (⟨α x, mem_map_of_mem α hxJ⟩ : ↥(J₂.map α))
      rwa [Subgroup.orderOf_mk, hw2] at h1
    have hT₂ := isTwoComponentIn_map_of_central hα hk hJ₂ hq₂ h2₂
    have hk₂ : (α.subgroupMap J₂).ker ≤ center ↥J₂ := by
      intro a ha
      have h1 : (a : G) ∈ center G := hk (by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
        exact MonoidHom.mem_ker.mpr this)
      rw [mem_center_iff] at h1 ⊢
      intro g
      exact Subtype.ext (h1 g)
    obtain ⟨z₂⟩ := nonempty_center_quot_equiv hqJ₂ (α.subgroupMap_surjective J₂) hk₂
    have hlie' : Blueprint.LieModel (↥(J₂.map α) ⧸ Open.fusionZStar ↥(J₂.map α)) τ' n' 3 1 :=
      GSThmB.OddQuot.lieModel_of_equiv (z₂.trans (QuotientGroup.quotientMulEquivOfEq
        (fusionZStar_eq_center_of_isQuasisimple hq₂ h2₂).symm)) hlie
    refine ⟨α u, hu2', huZY, _, J₂.map α, hS₁, huS₁, ⟨E₁⟩, .inl ⟨hT₂, τ', n', hlie'⟩,
      fun h1 => ?_, hwt⟩
    have hperf : Group.IsPerfect ↥(J₂.map α) := hT₂.2.2.1
    rw [← h1] at hperf
    exact TBLit.not_isPerfect_sl2Three (Group.IsPerfect.ofSurjective (f := E₁.toMonoidHom.comp
      (QuotientGroup.mk' _)) (E₁.surjective.comp (QuotientGroup.mk'_surjective _)))
  ·
    obtain ⟨hS₂, ⟨E₂⟩⟩ := isSolvableTwoComponentIn_map_sup hα hk hJ₂C hJ₂s hJ₂Z e₂
    refine ⟨α u, hu2', huZY, _, _, hS₁, huS₁, ⟨E₁⟩, .inr ⟨hS₂, ⟨E₂⟩⟩, fun h1 => ?_,
      hwt.imp (fun h1 => mem_sup_left h1) (fun h1 => mem_sup_left h1)⟩
    have hwS : w ∈ J₁.map α ⊔ (pPrimeCore 2 ↥(centralizer {α u})).map
        (centralizer {α u}).subtype := by
      rw [h1]
      exact mem_sup_left hwJ
    have hO := inv_mul_mem_pPrimeCore_of_involutions E₁ (x := ⟨α u, huS₁⟩) (y := ⟨w, hwS⟩)
      (by rw [Subgroup.orderOf_mk]; exact hu2') (by rw [Subgroup.orderOf_mk]; exact hw2)
    have h2 := orderOf_dvd_natCard (⟨_, hO⟩ : pPrimeCore 2 _)
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    change orderOf ((α u)⁻¹ * w) ∣ _ at h2
    rw [hwu] at h2
    exact (Nat.not_even_iff_odd.mpr GSThmB.OddQuot.odd_card_pPrimeCore)
      (even_iff_two_dvd.mpr h2)

end Concl

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
