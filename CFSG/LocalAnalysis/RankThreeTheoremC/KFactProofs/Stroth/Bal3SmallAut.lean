module

public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Subgroup

section SmallThreeGroups

theorem isMulCommutative_of_isPGroup_three_of_card_lt {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) (hc : Nat.card G < 27) : IsMulCommutative G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hG
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · have h1 : Nat.card G = 1 := by simpa using hn
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
      exact ⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩
    · have h3 : Nat.card G = 3 := by simpa using hn
      haveI : IsCyclic G := isCyclic_of_prime_card h3
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
  · have h27 : 27 ≤ 3 ^ n :=
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega

theorem le_card_of_isPGroup_three_of_not_isMulCommutative {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) (hc : ¬ IsMulCommutative G) : 27 ≤ Nat.card G := by
  by_contra h
  exact hc (isMulCommutative_of_isPGroup_three_of_card_lt hG (not_le.1 h))

end SmallThreeGroups

section CentralizerOfNormal

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_inf_centralizer_le_card_center (K : Subgroup Y) :
    Nat.card ↥(K ⊓ centralizer (K : Set Y)) ≤ Nat.card ↥(center K) := by
  have hmem : ∀ x : ↥(K ⊓ centralizer (K : Set Y)), (⟨(x : Y), x.2.1⟩ : ↥K) ∈ center K := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.1 x.2.2) g g.2)
  refine Nat.card_le_card_of_injective
    (fun x => (⟨⟨(x : Y), x.2.1⟩, hmem x⟩ : ↥(center K))) ?_
  intro a b h
  exact Subtype.ext (congrArg (fun w : ↥(center K) => ((w : ↥K) : Y)) h)

theorem inf_centralizer_eq_zpowers_of_card_center_eq_three {K : Subgroup Y} {z : Y}
    (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z) (hzo : orderOf z = 3)
    (hZ : Nat.card (center K) = 3) : K ⊓ centralizer (K : Set Y) = zpowers z := by
  refine (Subgroup.eq_of_le_of_card_ge (H := zpowers z) ?_ ?_).symm
  · rw [zpowers_le]
    exact ⟨hzK, mem_centralizer_iff.2 fun k hk => (hzc k hk).symm⟩
  · rw [Nat.card_zpowers, hzo]
    exact (card_inf_centralizer_le_card_center K).trans hZ.le

theorem ker_conjNormal_eq_centralizer (K : Subgroup Y) [K.Normal] :
    (MulAut.conjNormal : Y →* MulAut ↥K).ker = centralizer (K : Set Y) := by
  ext g
  constructor
  · intro hg
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : Y)) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro hg
    refine MonoidHom.mem_ker.2 (MulEquiv.ext fun k => Subtype.ext ?_)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← (mem_centralizer_iff.1 hg) k k.2, mul_inv_cancel_right]

end CentralizerOfNormal

section SylowMeet

theorem le_card_sylow_inf_of_dvd_card_center {Y : Type} [Group Y] [Finite Y] (R : Sylow 3 Y)
    (K : Subgroup Y) [K.Normal] (hKq : CFSG.Open.IsQuasisimple K)
    (hdvd : 3 ∣ Nat.card (center K)) : 27 ≤ Nat.card ↥((R : Subgroup Y) ⊓ K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : CFSG.ABGLocalTools.IsSylowOf 3 (R : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, R.isPGroup', R.not_dvd_index⟩
  have hRK : CFSG.ABGLocalTools.IsSylowOf 3 ((R : Subgroup Y) ⊓ K) K :=
    hR.inf_of_le_normalizer le_top le_normalizer_of_normal
  obtain ⟨Q, hQ⟩ := hRK.exists_sylow_eq_subgroupOf
  have hnab := (GL83.I_6_10_1_proved K hKq 3 Nat.prime_three (by norm_num) hdvd Q).1
  have h27 := le_card_of_isPGroup_three_of_not_isMulCommutative Q.isPGroup' hnab
  have hcard : Nat.card ↥(Q : Subgroup ↥K) = Nat.card ↥((R : Subgroup Y) ⊓ K) := by
    rw [hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  omega

end SylowMeet

section Main

theorem sylow_eq_mul_of_small_aut {Y : Type} [Group Y] [Finite Y] (R : Sylow 3 Y)
    (K : Subgroup Y) [K.Normal] (hKq : CFSG.Open.IsQuasisimple K) {z : Y} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hzo : orderOf z = 3)
    (hZ : Nat.card (Subgroup.center K) = 3)
    (hS : ∀ B : Subgroup (MulAut K), IsPGroup 3 B → Nat.card B ≤ 9) :
    (∀ u ∈ (R : Subgroup Y), ∃ t ∈ (R : Subgroup Y) ⊓ K,
      ∃ c ∈ (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), t * c = u) ∧
    (∀ x ∈ (R : Subgroup Y) ⊓ K, ∀ y ∈ (R : Subgroup Y) ⊓ K,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, hker⟩ : ∃ Φ : Y →* MulAut ↥K, Φ.ker ≤ centralizer (K : Set Y) :=
    ⟨MulAut.conjNormal, (ker_conjNormal_eq_centralizer K).le⟩
  have hB : IsPGroup 3 ↥((R : Subgroup Y).map Φ) := R.isPGroup'.map Φ
  have hBcard : Nat.card ↥((R : Subgroup Y).map Φ) ≤ 9 := hS _ hB
  have hBcomm : IsMulCommutative ↥((R : Subgroup Y).map Φ) :=
    isMulCommutative_of_isPGroup_three_of_card_lt hB (by omega)
  have hT27 : 27 ≤ Nat.card ↥((R : Subgroup Y) ⊓ K) :=
    le_card_sylow_inf_of_dvd_card_center R K hKq (by rw [hZ])
  have hKC : K ⊓ centralizer (K : Set Y) = zpowers z :=
    inf_centralizer_eq_zpowers_of_card_center_eq_three hzK hzc hzo hZ
  have hkerT : Φ.ker ⊓ ((R : Subgroup Y) ⊓ K) ≤ zpowers z := by
    intro g hg
    rw [← hKC]
    exact ⟨hg.2.2, hker hg.1⟩
  have hkerT_card : Nat.card ↥(Φ.ker ⊓ ((R : Subgroup Y) ⊓ K)) ≤ 3 := by
    have := Subgroup.card_le_of_le hkerT
    rwa [Nat.card_zpowers, hzo] at this
  have hmul := Subgroup.relIndex_mul_card Φ.ker ((R : Subgroup Y) ⊓ K)
  rw [Subgroup.relIndex_ker] at hmul
  have hTcard : 9 ≤ Nat.card ↥(((R : Subgroup Y) ⊓ K).map Φ) := by
    by_contra hlt
    push_neg at hlt
    have : Nat.card ↥(((R : Subgroup Y) ⊓ K).map Φ) *
        Nat.card ↥(Φ.ker ⊓ ((R : Subgroup Y) ⊓ K)) < 27 := by nlinarith
    omega
  have hmap_eq : ((R : Subgroup Y) ⊓ K).map Φ = (R : Subgroup Y).map Φ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono inf_le_left) (by omega)
  refine ⟨fun u hu => ?_, fun x hx y hy => ?_⟩
  ·
    have hΦu : Φ u ∈ ((R : Subgroup Y) ⊓ K).map Φ := by
      rw [hmap_eq]
      exact ⟨u, hu, rfl⟩
    obtain ⟨t, htT, hteq⟩ := hΦu
    have hcR : t⁻¹ * u ∈ (R : Subgroup Y) :=
      (R : Subgroup Y).mul_mem ((R : Subgroup Y).inv_mem htT.1) hu
    refine ⟨t, htT, t⁻¹ * u, ⟨hcR, hker ?_⟩, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hteq, inv_mul_cancel]
  ·
    have hxy : Φ x * Φ y = Φ y * Φ x :=
      congrArg Subtype.val (hBcomm.is_comm.comm ⟨Φ x, ⟨x, hx.1, rfl⟩⟩ ⟨Φ y, ⟨y, hy.1, rfl⟩⟩)
    have hmemker : x * y * x⁻¹ * y⁻¹ ∈ Φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
      group
    have hmemK : x * y * x⁻¹ * y⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hx.2 hy.2) (K.inv_mem hx.2)) (K.inv_mem hy.2)
    rw [← hKC]
    exact ⟨hmemK, hker hmemker⟩

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
