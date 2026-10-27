module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseINormal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenQuot

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

@[expose] def x0 : A5 := ⟨swap 0 1 * swap 3 4, by decide⟩

theorem x0_conj_y0 : x0 * y0 * x0⁻¹ = y0⁻¹ := by decide

theorem not_norm_x0_k1 :
    ¬ ∀ q ∈ (1 :: p0inv), x0 * k1 * x0⁻¹ * q * (x0 * k1 * x0⁻¹)⁻¹ ∈ (1 :: p0inv) := by
  decide

theorem p0_mul_self : ∀ k ∈ (1 :: p0inv), k * k = 1 := by decide

theorem eq_of_commute_y0 : ∀ σ : Perm (Fin 5), σ * (y0 : Perm (Fin 5)) = y0 * σ →
    Perm.sign σ = 1 → σ = 1 ∨ σ = y0 ∨ σ = (y0 : Perm (Fin 5)) * y0 := by
  decide +kernel

theorem eq_one_of_pow_three {M : Type*} [Monoid M] {σ : M} {k : ℕ} (h3 : σ ^ 3 = 1)
    (hk : σ ^ 2 ^ k = 1) : σ = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk)
  rwa [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h1

theorem sign_eq_one_of_pow {σ : Perm (Fin 5)} {m : ℕ} (hm : Odd m) (h : σ ^ m = 1) :
    Perm.sign σ = 1 := by
  have h2 : Perm.sign σ ^ m = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1, hm.neg_one_pow] at h2
    exact absurd h2 (by decide)

omit [Finite G] in
theorem mul_self_of_map_P0 {M Q : Subgroup G} (ψ : A5 ≃* M)
    (hψ : P0.map ψ.toMonoidHom = Q.subgroupOf M) {s : G} (hsM : s ∈ M) (hs : s ∈ Q) :
    s * s = 1 := by
  have h : (⟨s, hsM⟩ : M) ∈ Q.subgroupOf M := mem_subgroupOf.mpr hs
  rw [← hψ] at h
  obtain ⟨k, hk, hks⟩ := h
  have hk2 := p0_mul_self k (mem_P0.mp hk)
  have hs' : s = ((ψ k : M) : G) := congrArg Subtype.val hks.symm
  rw [hs', ← Subgroup.coe_mul, ← map_mul, hk2, map_one, Subgroup.coe_one]

namespace CaseIPair

variable {A B R T : Subgroup G}

theorem centralizer_le_normalizer_of_mem (p : CaseIPair A B R T) {s : G}
    (hs : s ∈ centralizer (A : Set G)) (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    centralizer ({s} : Set G) ≤ normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have hP : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; rfl)
  have hle : zpowers s ≤ centralizer (A : Set G) := zpowers_le.mpr hs
  have hne : zpowers s ≠ ⊥ := fun h => hs1 (by
    have h1 := mem_zpowers s
    rw [h] at h1
    exact h1)
  intro g hg
  have hgN : g ∈ normalizer (zpowers s : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hg).symm k)).eq
  rw [← p.normA]
  exact normalizer_two_subgroup_le _ _ p.tightA hP hle hne hgN

theorem inf_centralizer_le (p : CaseIPair A B R T) :
    A ⊓ centralizer (B : Set G) ≤ normalizer (T : Set G) := by
  rintro a ⟨haA, haC⟩
  obtain ⟨eA⟩ := p.isoA
  obtain ⟨y, ⟨hyA, hyN⟩, hyk⟩ := p.symm.exists_mul_mem haC
  have h : y⁻¹ * a ∈ A ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨mul_mem (inv_mem hyA) haA, hyk⟩
  rw [inf_centralizer_eq_bot eA, mem_bot, inv_mul_eq_one] at h
  rwa [← h]

end CaseIPair

structure CaseICoords (A B R T : Subgroup G) where
  pair : CaseIPair A B R T
  ψA : A5 ≃* A
  ψB : A5 ≃* B
  mapA : P0.map ψA.toMonoidHom = T.subgroupOf A
  mapB : P0.map ψB.toMonoidHom = R.subgroupOf B

omit [Finite G] in
theorem CaseIPair.nonempty_coords {A B R T : Subgroup G} (p : CaseIPair A B R T) :
    Nonempty (CaseICoords A B R T) := by
  obtain ⟨eA⟩ := p.isoA
  obtain ⟨eB⟩ := p.isoB
  have hT4 : Nat.card (T.subgroupOf A) = 4 := by
    rw [← p.card_T]
    exact Nat.card_congr (subgroupOfEquivOfLe p.T_le).toEquiv
  have hR4 : Nat.card (R.subgroupOf B) = 4 := by
    rw [← p.card_R]
    exact Nat.card_congr (subgroupOfEquivOfLe p.R_le).toEquiv
  obtain ⟨ψA, hψA⟩ := exists_equiv_map_P0 eA hT4
  obtain ⟨ψB, hψB⟩ := exists_equiv_map_P0 eB hR4
  exact ⟨⟨p, ψA, ψB, hψA, hψB⟩⟩

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

@[expose] def w : G := (c.ψA y0 : G)

@[expose] def x : G := (c.ψA x0 : G)

@[expose] def H : Subgroup G := centralizer ({c.w} : Set G)

omit [Finite G] in
theorem w_mem : c.w ∈ A := (c.ψA y0).2

omit [Finite G] in
theorem x_mem : c.x ∈ A := (c.ψA x0).2

omit [Finite G] in
theorem symm_w : c.ψA.symm ⟨c.w, c.w_mem⟩ = y0 := by
  simp [w]

omit [Finite G] in
theorem w_mem_normalizer : c.w ∈ normalizer (T : Set G) := by
  obtain ⟨hN, -, -, -⟩ := klein_of_map c.ψA
  rw [c.mapA] at hN
  have h := (Subgroup.subgroupOf_normalizer_eq c.pair.T_le).symm ▸ hN
  exact mem_subgroupOf.mp h

theorem w_mem_centralizer : c.w ∈ centralizer (B : Set G) :=
  c.pair.symm.inf_normalizer_le ⟨c.w_mem, c.w_mem_normalizer⟩

theorem B_le_H : B ≤ c.H := fun b hb =>
  mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp c.w_mem_centralizer) b hb)

theorem R_le_H : R ≤ c.H := c.pair.R_le.trans c.B_le_H

omit [Finite G] in
theorem w_pow_three : c.w ^ 3 = 1 := by
  rw [w, ← SubgroupClass.coe_pow, ← map_pow, ← orderOf_y0, pow_orderOf_eq_one, map_one,
    OneMemClass.coe_one]

omit [Finite G] in
theorem x_conj_w : c.x * c.w * c.x⁻¹ = c.w⁻¹ := by
  simp only [x, w]
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
    ← map_mul, x0_conj_y0, map_inv, Subgroup.coe_inv]

theorem x_mem_normalizer : c.x ∈ normalizer (c.H : Set G) := by
  refine RankTwoAlt.mem_normalizer_of_conj_le fun k hk => ?_
  rw [H, mem_centralizer_singleton_iff] at hk ⊢
  have h0 : c.x * c.w⁻¹ * c.x⁻¹ = c.w := by
    rw [show c.x * c.w⁻¹ * c.x⁻¹ = (c.x * c.w * c.x⁻¹)⁻¹ by group, c.x_conj_w, inv_inv]
  have h1 : c.x⁻¹ * c.w * c.x = c.w⁻¹ := by
    calc c.x⁻¹ * c.w * c.x = c.x⁻¹ * (c.x * c.w⁻¹ * c.x⁻¹) * c.x := by rw [h0]
      _ = c.w⁻¹ := by group
  have hk' : k * c.w⁻¹ = c.w⁻¹ * k := (show Commute k c.w from hk).inv_right.eq
  calc c.x * k * c.x⁻¹ * c.w = c.x * (k * (c.x⁻¹ * c.w * c.x)) * c.x⁻¹ := by group
    _ = c.x * (k * c.w⁻¹) * c.x⁻¹ := by rw [h1]
    _ = c.x * (c.w⁻¹ * k) * c.x⁻¹ := by rw [hk']
    _ = (c.x * c.w⁻¹ * c.x⁻¹) * (c.x * k * c.x⁻¹) := by group
    _ = c.w * (c.x * k * c.x⁻¹) := by rw [h0]

omit [Finite G] in
include c in
theorem mul_self_of_mem_R {s : G} (hs : s ∈ R) : s * s = 1 :=
  mul_self_of_map_P0 c.ψB c.mapB (c.pair.R_le hs) hs

omit [Finite G] in
include c in
theorem mul_self_of_mem_T {s : G} (hs : s ∈ T) : s * s = 1 :=
  mul_self_of_map_P0 c.ψA c.mapA (c.pair.T_le hs) hs

omit [Finite G] in
theorem autPerm_w : autPerm c.ψA.symm ⟨c.w, le_normalizer c.w_mem⟩ = (y0 : Perm (Fin 5)) := by
  rw [autPerm_of_mem c.ψA.symm c.w_mem, c.symm_w]

omit [Finite G] in
theorem autPerm_commute {y : G} (hy : y ∈ c.H) (hyN : y ∈ normalizer (A : Set G)) :
    autPerm c.ψA.symm ⟨y, hyN⟩ * (y0 : Perm (Fin 5)) = y0 * autPerm c.ψA.symm ⟨y, hyN⟩ := by
  rw [← c.autPerm_w, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp hy)

theorem exists_mem_of_odd {s : G} (hs : s ∈ R) (hs1 : s ≠ 1) {y : G} (hy : y ∈ c.H)
    (hys : y * s = s * y) (hodd : Odd (orderOf y)) :
    ∃ i : ℕ, (c.w ^ i)⁻¹ * y ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  have hs2 : s * s = 1 := c.mul_self_of_mem_R hs
  have hsK : s ∈ centralizer (A : Set G) := c.pair.sylowR.le hs
  have hyN : y ∈ normalizer (A : Set G) :=
    c.pair.centralizer_le_normalizer_of_mem hsK hs1 hs2 (mem_centralizer_singleton_iff.mpr hys)
  have hwN : c.w ∈ normalizer (A : Set G) := le_normalizer c.w_mem
  have hσw : autPerm c.ψA.symm ⟨c.w, hwN⟩ = (y0 : Perm (Fin 5)) := c.autPerm_w
  set σ := autPerm c.ψA.symm ⟨y, hyN⟩ with hσ
  have hcomm : σ * (y0 : Perm (Fin 5)) = y0 * σ := c.autPerm_commute hy hyN
  have hσm : σ ^ orderOf y = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨y, hyN⟩ : normalizer (A : Set G)) ^ orderOf y = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, σ = (y0 : Perm (Fin 5)) ^ i := by
    rcases eq_of_commute_y0 σ hcomm (sign_eq_one_of_pow hodd hσm) with h | h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, by rw [h, sq]⟩
  refine ⟨i, ?_⟩
  have hkN : (c.w ^ i)⁻¹ * y ∈ normalizer (A : Set G) :=
    mul_mem (inv_mem (pow_mem hwN i)) hyN
  have hkA : (c.w ^ i)⁻¹ * y ∈ centralizer (A : Set G) := by
    apply (autPerm_eq_one_iff c.ψA.symm ⟨_, hkN⟩).mp
    have : (⟨(c.w ^ i)⁻¹ * y, hkN⟩ : normalizer (A : Set G)) =
        (⟨c.w, hwN⟩ ^ i)⁻¹ * ⟨y, hyN⟩ := Subtype.ext (by simp)
    rw [this, map_mul, map_inv, map_pow, hσw, ← hσ, hi, inv_mul_cancel]
  refine ⟨hkA, ?_⟩
  have hwy : Commute (c.w ^ i)⁻¹ y :=
    ((Commute.pow_left (mem_centralizer_singleton_iff.mp hy).symm i).inv_left)
  have hw3 : orderOf (c.w ^ i)⁻¹ ∣ 3 := by
    rw [orderOf_inv]
    exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, c.w_pow_three,
      one_pow])
  have hkodd : Odd (orderOf ((c.w ^ i)⁻¹ * y)) :=
    ((Odd.of_dvd_nat (by decide) hw3).mul hodd).of_dvd_nat hwy.orderOf_mul_dvd_mul_orderOf
  have hws : c.w * s = s * c.w := mem_centralizer_iff.mp hsK c.w c.w_mem
  have hks : (c.w ^ i)⁻¹ * y * s = s * ((c.w ^ i)⁻¹ * y) := by
    have h1 : (c.w ^ i)⁻¹ * s = s * (c.w ^ i)⁻¹ :=
      ((Commute.pow_left (show Commute c.w s from hws) i).inv_left).eq
    rw [mul_assoc, hys, ← mul_assoc, h1, mul_assoc]
  exact mem_centralizer_of_odd_of_commute c.ψB.symm (c.pair.centralizer_le_normalizer hkA)
    hkodd (c.pair.R_le hs) hs2 hs1 hks

theorem mem_centralizer_of_odd {s : G} (hs : s ∈ R) (hs1 : s ≠ 1) {y : G} (hy : y ∈ c.H)
    (hys : y * s = s * y) (hodd : Odd (orderOf y)) : y ∈ centralizer (B : Set G) := by
  obtain ⟨i, hi⟩ := c.exists_mem_of_odd hs hs1 hy hys hodd
  have : y = c.w ^ i * ((c.w ^ i)⁻¹ * y) := by group
  rw [this]
  exact mul_mem (pow_mem c.w_mem_centralizer i) (mem_inf.mp hi).2

@[expose] def O : Subgroup G := (CFSG.pPrimeCore 2 c.H).map c.H.subtype

omit [Finite G] in
theorem O_le_H : c.O ≤ c.H := map_subtype_le _

theorem odd_card_O : Odd (Nat.card c.O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [O, card_map_of_injective c.H.subtype_injective]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card))

theorem O_le_centralizer : c.O ≤ centralizer (B : Set G) := by
  have hRN : R ≤ normalizer (c.O : Set G) :=
    c.R_le_H.trans (CFSG.ABGLocalTools.le_normalizer_map_subtype c.H _)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two R c.O (fun r => Subtype.ext (by
      rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
      exact c.mul_self_of_mem_R r.2)) (by rw [c.pair.card_R]; rfl)
    (fun h => (Nat.not_even_iff_odd.mpr c.odd_card_O) (even_iff_two_dvd.mpr h)) hRN
  rw [hgen]
  refine iSup₂_le fun r hr => ?_
  rintro y ⟨hyO, hyr⟩
  have hodd : Odd (orderOf y) := by
    have h1 : orderOf y ∣ Nat.card c.O := by
      rw [← Subgroup.orderOf_mk y hyO]
      exact orderOf_dvd_natCard _
    exact c.odd_card_O.of_dvd_nat h1
  exact c.mem_centralizer_of_odd r.2 (fun h => hr (Subtype.ext h)) (c.O_le_H hyO)
    (mem_centralizer_singleton_iff.mp hyr) hodd

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
