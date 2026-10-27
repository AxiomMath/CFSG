module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Inputs
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.Literature.FSmithForm

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def Step48NoTim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
    ∀ h : ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z),
      ¬ Tim77Facts ((Q.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (zpowers (zC z)))) h

namespace Sec4Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem sq_mem (hQ : Sec4Q G A R g E F S₁ Q z) {q : G} (hq : q ∈ Q) : q ^ 2 ∈ zpowers z := by
  rw [← hQ.center_Q]
  have h1 := CFSG.RankThree.Literature.FSmith.sq_mem_center hQ.extraspecial ⟨q, hq⟩
  refine mem_centerIn.mpr ⟨Q.pow_mem hq 2, mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)

theorem rightConjugate_eq (hQ : Sec4Q G A R g E F S₁ Q z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hle : rightConjugate Q c ≤ S₁) :
    rightConjugate Q c = Q := by
  refine hQ.unique _ hle ?_ (by rw [rightConjugate_card, hQ.card]) ?_
  · exact CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective Q _ (MulAut.conj c⁻¹).injective) hQ.extraspecial
  · rw [hQ.center_S₁, ← hQ.center_Q]
    have hcz := mem_centralizer_singleton_iff.mp hc
    ext x
    rw [mem_centerIn, mem_centerIn, mem_rightConjugate_iff]
    constructor
    · rintro ⟨hx, hxc⟩
      have hxc' : c * x * c⁻¹ ∈ centralizer (Q : Set G) := by
        rw [mem_centralizer_iff]
        intro q hq
        have := mem_centralizer_iff.mp hxc (c⁻¹ * q * c) (by
          rw [SetLike.mem_coe, mem_rightConjugate_iff]; simpa [mul_assoc] using hq)
        calc q * (c * x * c⁻¹) = c * ((c⁻¹ * q * c) * x) * c⁻¹ := by group
          _ = c * (x * (c⁻¹ * q * c)) * c⁻¹ := by rw [this]
          _ = c * x * c⁻¹ * q := by group
      have hzc : c * x * c⁻¹ ∈ centerIn Q := mem_centerIn.mpr ⟨hx, hxc'⟩
      rw [hQ.center_Q] at hzc
      rcases eq_one_or_eq_of_mem_zpowers hQ.order_z hzc with h | h
      · have : x = 1 := by
          calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
            _ = 1 := by rw [h]; group
        rw [this]
        exact ⟨one_mem _, one_mem _⟩
      · have : x = z := by
          calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
            _ = c⁻¹ * (z * c) := by rw [h, mul_assoc]
            _ = z := by rw [← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact mem_centerIn.mp hQ.z_mem_centerIn_Q
    · rintro ⟨hx, hxc⟩
      have hxz : x ∈ zpowers z := by
        have : x ∈ centerIn Q := mem_centerIn.mpr ⟨hx, hxc⟩
        rwa [hQ.center_Q] at this
      have hcx : c * x * c⁻¹ = x := by
        obtain ⟨k, rfl⟩ := hxz
        have : Commute c (z ^ k) := Commute.zpow_right hcz k
        show c * z ^ k * c⁻¹ = z ^ k
        rw [this.eq, mul_inv_cancel_right]
      refine ⟨by rw [hcx]; exact hx, mem_centralizer_iff.mpr fun q hq => ?_⟩
      rw [SetLike.mem_coe, mem_rightConjugate_iff] at hq
      have := mem_centralizer_iff.mp hxc _ hq
      have hxc' : c⁻¹ * x * c = x := by
        conv_lhs => rw [← hcx]
        group
      calc q * x = q * (c⁻¹ * x * c) := by rw [hxc']
        _ = c⁻¹ * ((c * q * c⁻¹) * x) * c := by group
        _ = c⁻¹ * (x * (c * q * c⁻¹)) * c := by rw [this]
        _ = (c⁻¹ * x * c) * q := by group
        _ = x * q := by rw [hxc']

end Sec4Q

theorem step48_of (hT : Tim77Lemma24) (hno : Step48NoTim) : Step48 := by
  intro G _ _ A R g E F S₁ Q z hQ x hx h hh hS
  by_contra hnQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQC := hQ.Q_le_centralizer
  have hS₁C := hQ.le_centralizer
  let π := QuotientGroup.mk' (zpowers (zC z))
  have hker : π.ker = zpowers (zC z) := QuotientGroup.ker_mk' _
  have hcm : ∀ K : Subgroup ↥(centralizer ({z} : Set G)), zpowers (zC z) ≤ K →
      (K.map π).comap π = K := fun K hK => by
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hK]
  have hzQ : zpowers (zC z) ≤ Q.subgroupOf (centralizer ({z} : Set G)) :=
    zpowers_le.mpr (show zC z ∈ Q.subgroupOf (centralizer ({z} : Set G)) from hQ.z_mem_Q)
  have hzS : zpowers (zC z) ≤ S₁.subgroupOf (centralizer ({z} : Set G)) :=
    hzQ.trans (subgroupOf_mono _ hQ.le)
  have hSyl : IsSylowOf 2 ((S₁.subgroupOf (centralizer ({z} : Set G))).map π) ⊤ := by
    obtain ⟨T, hT'⟩ := hQ.sylow.of_le hS₁C le_top
    have hTS : (T : Subgroup (centralizer ({z} : Set G))) =
        S₁.subgroupOf (centralizer ({z} : Set G)) := by
      rw [← hT']
      exact (comap_map_eq_self_of_injective (centralizer ({z} : Set G)).subtype_injective _).symm
    let P := T.mapSurjective (QuotientGroup.mk'_surjective (zpowers (zC z)))
    have hP : (P : Subgroup (↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z))) =
        (T : Subgroup (centralizer ({z} : Set G))).map π := Sylow.coe_mapSurjective _ _
    refine isSylowOf_of_card le_top ?_
    rw [← hTS, ← hP, Sylow.card_eq_multiplicity, card_top]
  have helem : IsElemAbelian 2 ((Q.subgroupOf (centralizer ({z} : Set G))).map π) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, qa, hqa, rfl⟩ := a
      obtain ⟨_, qb, hqb, rfl⟩ := b
      show π qa * π qb = π qb * π qa
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_zpowers_zC]
      have := hQ.commutator_mem (Q.inv_mem hqb) (Q.inv_mem hqa)
      simpa [mul_assoc] using this
    · rintro _ ⟨q, hq, rfl⟩
      rw [← map_pow, ← MonoidHom.mem_ker, hker, mem_zpowers_zC]
      exact hQ.sq_mem hq
  have hweak : ∀ k : ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z),
      rightConjugate ((Q.subgroupOf (centralizer ({z} : Set G))).map π) k ≤
        (S₁.subgroupOf (centralizer ({z} : Set G))).map π →
      rightConjugate ((Q.subgroupOf (centralizer ({z} : Set G))).map π) k =
        (Q.subgroupOf (centralizer ({z} : Set G))).map π := by
    intro k hk
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (zpowers (zC z)) k
    have hmc : ∀ K : Subgroup ↥(centralizer ({z} : Set G)),
        rightConjugate (K.map π) (π c) = (rightConjugate K c).map π := by
      intro K
      unfold rightConjugate
      rw [map_map, map_map]
      congr 1
    rw [hmc] at hk ⊢
    have hk' : rightConjugate (Q.subgroupOf (centralizer ({z} : Set G))) c ≤
        S₁.subgroupOf (centralizer ({z} : Set G)) := by
      intro y hy
      have := hk ⟨y, hy, rfl⟩
      rwa [← hcm _ hzS]
    have hG : rightConjugate Q (c : G) ≤ S₁ := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have hyC : y ∈ centralizer ({z} : Set G) := by
        have h1 := mul_mem (mul_mem (inv_mem c.2) (hQC hy)) c.2
        simpa [mul_assoc] using h1
      have := hk' (show (⟨y, hyC⟩ : centralizer ({z} : Set G)) ∈
        rightConjugate (Q.subgroupOf (centralizer ({z} : Set G))) c from by
          rw [mem_rightConjugate_iff, mem_subgroupOf]
          exact hy)
      exact this
    have heq := hQ.rightConjugate_eq c.2 hG
    have heq' : rightConjugate (Q.subgroupOf (centralizer ({z} : Set G))) c =
        Q.subgroupOf (centralizer ({z} : Set G)) := by
      ext y
      constructor
      · intro hy
        rw [mem_rightConjugate_iff, mem_subgroupOf] at hy
        have : (y : G) ∈ rightConjugate Q (c : G) := by
          rw [mem_rightConjugate_iff]
          simpa using hy
        rw [heq] at this
        exact this
      · intro hy
        rw [mem_subgroupOf] at hy
        rw [mem_rightConjugate_iff, mem_subgroupOf]
        have : (y : G) ∈ rightConjugate Q (c : G) := by rw [heq]; exact hy
        rw [mem_rightConjugate_iff] at this
        simpa using this
    rw [heq']
  have hns : ∃ v ∈ (Q.subgroupOf (centralizer ({z} : Set G))).map π,
      ∃ k : ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z),
        k⁻¹ * v * k ∈ (S₁.subgroupOf (centralizer ({z} : Set G))).map π ∧
        k⁻¹ * v * k ∉ (Q.subgroupOf (centralizer ({z} : Set G))).map π := by
    refine ⟨π ⟨x, hQC hx⟩, ⟨_, hx, rfl⟩, π ⟨h, hh⟩, ?_, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨_, hS, rfl⟩
    · rw [← map_inv, ← map_mul, ← map_mul]
      intro hmem
      have := (show _ ∈ ((Q.subgroupOf (centralizer ({z} : Set G))).map π).comap π
        from hmem)
      rw [hcm _ hzQ, mem_subgroupOf] at this
      exact hnQ this
  obtain ⟨k, hk⟩ := hT _ _ _ hSyl (map_mono (subgroupOf_mono _ hQ.le)) helem hweak hns
  exact hno G A R g E F S₁ Q z hQ k hk

end CFSG.ComponentClassification.AS81
