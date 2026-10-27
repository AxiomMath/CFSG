module

public import CFSG.Assembly.E6FourNeighbourCfg
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.Assembly.LargeEvenGLABridge

public section

namespace CFSG.Assembly

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem e6four_step1 (hT3 : E6FourOutInner) (hE1 : E6FourSylowFive) (hE2 : E6FourTwoLocalFive)
    {p : ℕ} {B L J : Subgroup G} {x y : G} (hS : LargeEvenSStar p B x L)
    (hm : 4 ≤ LargeEvenTwoLocalRank p G) (hJB : B ≤ normalizer (J : Set G))
    (hNb : LargeEvenIsNeighborOf p B x L y J)
    (hJ : LargeEvenMarking J fun lab _ _ _ _ _ =>
      LargeEvenHalfSplitE6FourException p lab (center J = ⊥)) :
    p = 5 ∧ LargeEvenTwoLocalRank 5 G = 5 ∧
      ∃ A : Subgroup G, A ≤ J ∧ Nat.card A = 5 ^ 4 ∧
        (∀ b ∈ B, ∃ a ∈ A, a⁻¹ * b ∈ centralizer (J : Set G)) ∧
        ∀ a ∈ A, ∃ b ∈ B, a⁻¹ * b ∈ centralizer (J : Set G) := by
  classical
  obtain ⟨hp5, hZ, hmark, hqs⟩ := e6four_J_facts hJ
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBmax : CFSG.Open.IsElemAbelian 5 B ∧
      Nat.card B = 5 ^ LargeEvenTwoLocalRank 5 G ∧
      ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ normalizer (U : Set G) := hNb.1.1
  obtain ⟨hElem, hcardB, U₀, hU₀ne, hU₀2, hBU₀⟩ := hBmax
  have hyB : y ∈ B := hNb.1.2.1
  have hyNe : y ≠ 1 := hNb.1.2.2.1
  have hJy : J ≤ centralizer ({y} : Set G) := hNb.1.2.2.2.1
  have hyPow : y ^ 5 = 1 := hElem.2 y hyB
  have hCy : y ∈ centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJy hj)

  have hCBJ : B ⊓ centralizer (J : Set G) = zpowers y := by
    refine le_antisymm ?_ ?_
    · intro b hb
      have hbNorm : b ∈ normalizer (J : Set G) :=
        Subgroup.centralizer_le_normalizer _ hb.2
      have hcom : (⁅J, zpowers b⁆ : Subgroup G) = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
          Subgroup.zpowers_le]
        exact hb.2
      exact (hNb.1.2.2.2.2.2 b).mp ⟨hb.1, hbNorm, by rw [hcom]; exact bot_le⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hyB, Subgroup.mem_centralizer_iff.mpr fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.mp (hJy hj)⟩

  let α : B →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom (H := J)).comp (Subgroup.inclusion hJB)
  have hαapply : ∀ (b : B) (j : ↥J),
      ((α b) j : G) = (b : G) * (j : G) * (b : G)⁻¹ := by
    intro b j
    have hαb : α b = Subgroup.normalizerMonoidHom (H := J) ⟨(b : G), hJB b.2⟩ := rfl
    rw [hαb, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hαpow : ∀ b : B, (α b) ^ 5 = 1 := by
    intro b
    have hb5 : b ^ 5 = 1 := Subtype.ext (by simpa using hElem.2 (b : G) b.2)
    calc (α b) ^ 5 = α (b ^ 5) := (map_pow α b 5).symm
      _ = α 1 := by rw [hb5]
      _ = 1 := map_one α
  have hInnerFive : E6FourInnerFive ↥J := (hT3 ↥J hmark hZ).1
  let βfun : B → ↥J := fun b => Classical.choose (hInnerFive (α b) (hαpow b))
  have hβspec : ∀ b : B, MulAut.conj (βfun b) = α b := fun b =>
    Classical.choose_spec (hInnerFive (α b) (hαpow b))
  have hβuniq : ∀ a a' : ↥J, MulAut.conj a = MulAut.conj a' → a = a' := by
    intro a a' h
    have hc : a⁻¹ * a' ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : MulAut.conj (a⁻¹ * a') = 1 := by
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have h2 := congrArg (fun φ : MulAut ↥J => φ g) h1
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * (a⁻¹ * a') =
          ((a⁻¹ * a') * g * (a⁻¹ * a')⁻¹) * (a⁻¹ * a') := by rw [h2]
        _ = (a⁻¹ * a') * g := by group
    have hc1 : a⁻¹ * a' = 1 := by
      have := hc
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    have hca : a' = a := by
      calc a' = a * (a⁻¹ * a') := by group
        _ = a := by rw [hc1, mul_one]
    exact hca.symm
  let β : B →* ↥J :=
    { toFun := βfun
      map_one' := by
        apply hβuniq
        rw [hβspec, map_one, map_one]
      map_mul' := by
        intro b b'
        apply hβuniq
        calc MulAut.conj (βfun (b * b')) = α (b * b') := hβspec (b * b')
          _ = α b * α b' := map_mul α b b'
          _ = MulAut.conj (βfun b) * MulAut.conj (βfun b') := by
              rw [hβspec b, hβspec b']
          _ = MulAut.conj (βfun b * βfun b') :=
              (map_mul MulAut.conj (βfun b) (βfun b')).symm }
  have hβconj : ∀ (b : B) (j : ↥J),
      (b : G) * (j : G) * (b : G)⁻¹ = (β b : G) * (j : G) * (β b : G)⁻¹ := by
    intro b j
    show (b : G) * (j : G) * (b : G)⁻¹ =
      (βfun b : G) * (j : G) * (βfun b : G)⁻¹
    have h := congrArg (fun φ : MulAut ↥J => (((φ j : ↥J) : G))) (hβspec b)
    rw [hαapply b j] at h
    simpa [MulAut.conj_apply] using h.symm
  have hβeq : ∀ b : B, β b = 1 ↔ (b : G) ∈ centralizer (J : Set G) := by
    intro b
    constructor
    · intro hb1
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h := hβconj b ⟨j, hj⟩
      rw [hb1] at h
      have h' : (b : G) * (j : G) * (b : G)⁻¹ = (j : G) := by simpa using h
      calc (j : G) * (b : G) = ((b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by rw [h']
        _ = (b : G) * (j : G) := by group
    · intro hbC
      apply hβuniq
      change MulAut.conj (βfun b) = MulAut.conj 1
      rw [hβspec, map_one]
      ext j
      rw [hαapply, MulAut.one_apply]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hbC) (j : G) j.2
      calc (b : G) * (j : G) * (b : G)⁻¹ = ((j : G) * (b : G)) * (b : G)⁻¹ := by rw [hcomm]
        _ = (j : G) := by group
  let A : Subgroup G := (β.range).map J.subtype
  have hAJ : A ≤ J := Subgroup.map_subtype_le β.range
  have hcardA_range : Nat.card A = Nat.card β.range := Subgroup.card_subtype J β.range
  have hcardAB : Nat.card A * Nat.card β.ker = Nat.card B := by
    rw [hcardA_range, Nat.mul_comm, Subgroup.card_ker_mul_card_range]
  have hker : β.ker = (B ⊓ centralizer (J : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨b.2, (hβeq b).mp h⟩
    · intro h
      exact (hβeq b).mpr h.2
  have hcardKer : Nat.card β.ker = 5 := by
    rw [hker]
    have hcardSub : Nat.card ((B ⊓ centralizer (J : Set G)).subgroupOf B) =
        Nat.card ↥(B ⊓ centralizer (J : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : B ⊓ centralizer (J : Set G) ≤ B)).toEquiv
    rw [hcardSub, hCBJ, Nat.card_zpowers, orderOf_eq_prime hyPow hyNe]
  have hcardA5 : Nat.card A * 5 = 5 ^ LargeEvenTwoLocalRank 5 G := by
    calc Nat.card A * 5 = Nat.card A * Nat.card β.ker := by rw [hcardKer]
      _ = Nat.card B := hcardAB
      _ = 5 ^ LargeEvenTwoLocalRank 5 G := hcardB

  have hinfJ : J ⊓ centralizer (J : Set G) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_eq_bot_of_center le_rfl hZ
  have hyNotJ : y ∉ J := by
    intro hyJ
    have hyInf : y ∈ J ⊓ centralizer (J : Set G) := ⟨hyJ, hCy⟩
    rw [hinfJ] at hyInf
    exact hyNe (Subgroup.mem_bot.mp hyInf)

  have hA5 : IsPGroup 5 A :=
    IsPGroup.of_card_dvd_pow ⟨5, hcardA5.symm⟩
  have hAsub5 : IsPGroup 5 (A.subgroupOf J) := hA5.comap_subtype
  obtain ⟨P, hAP⟩ := hAsub5.exists_le_sylow
  have hPcard : Nat.card P = 5 ^ 4 := hE1 ↥J hmark hZ P
  have hcardSubA : Nat.card (A.subgroupOf J) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv
  have hcardAle : Nat.card A ≤ 5 ^ 4 := by
    have h1 : Nat.card (A.subgroupOf J) ≤ Nat.card P := Subgroup.card_le_of_le hAP
    rwa [hcardSubA, hPcard] at h1
  have hm_le : LargeEvenTwoLocalRank 5 G ≤ 5 := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp
    calc 5 ^ LargeEvenTwoLocalRank 5 G = Nat.card A * 5 := hcardA5.symm
      _ ≤ 5 ^ 4 * 5 := Nat.mul_le_mul_right 5 hcardAle
      _ = 5 ^ 5 := by norm_num

  obtain ⟨E, U, hEelem, hEcard, hUne, hU2, hEU⟩ := hE2 ↥J hmark hZ
  let E' : Subgroup G := E.map J.subtype
  let U' : Subgroup G := U.map J.subtype
  have hE'J : E' ≤ J := Subgroup.map_subtype_le E
  have hU'J : U' ≤ J := Subgroup.map_subtype_le U
  have hE'elem : CFSG.Open.IsElemAbelian 5 E' := hEelem.map J.subtype
  have hE'card : Nat.card E' = 5 ^ 4 := by
    rw [Subgroup.card_subtype J E, hEcard]
  have hU'ne : U' ≠ ⊥ := by
    intro h
    exact hUne ((Subgroup.map_eq_bot_iff_of_injective (f := J.subtype) U
      J.subtype_injective).mp h)
  have hU'2 : IsPGroup 2 U' := hU2.map J.subtype
  have hEU' : E' ≤ normalizer (U' : Set G) := by
    calc E' = E.map J.subtype := rfl
      _ ≤ (normalizer (U : Set ↥J)).map J.subtype := Subgroup.map_mono hEU
      _ ≤ normalizer (U.map J.subtype) := Subgroup.le_normalizer_map J.subtype
  have hcommE'y : ∀ e ∈ E', e * y = y * e := by
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp hCy) e (hE'J he)
  have hyNotE' : y ∉ E' := fun h => hyNotJ (hE'J h)
  obtain ⟨hE'y_elem, hE'y_card⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_sup_zpowers_of_card
      (p := 5) (k := 4) (by norm_num) hE'elem hE'card hyPow hyNotE' hcommE'y
  have hyCU' : y ∈ centralizer (U' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp hCy) u (hU'J hu)
  have hE'y_norm : (E' ⊔ zpowers y) ≤ normalizer (U' : Set G) :=
    sup_le hEU' (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hyCU'))
  have hrank : Nat.card ↥(E' ⊔ zpowers y) ≤ 5 ^ LargeEvenTwoLocalRank 5 G := by
    have h := GL83.PiGen.card_le_pow_twoLocalRank (p := 5) hE'y_elem hU'2 hU'ne hE'y_norm
    simpa [CFSG.Assembly.LargeEven.largeEvenTwoLocalRank_eq_glaTwoLocalRank] using h
  have h5le : 5 ^ 5 ≤ 5 ^ LargeEvenTwoLocalRank 5 G := by
    calc 5 ^ 5 = 5 ^ (4 + 1) := by norm_num
      _ = Nat.card ↥(E' ⊔ zpowers y) := hE'y_card.symm
      _ ≤ 5 ^ LargeEvenTwoLocalRank 5 G := hrank
  have hm_ge : 5 ≤ LargeEvenTwoLocalRank 5 G :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp h5le
  have hm_eq : LargeEvenTwoLocalRank 5 G = 5 := le_antisymm hm_le hm_ge
  have hcardA4 : Nat.card A = 5 ^ 4 := by
    have h1 : Nat.card A * 5 = 5 ^ 4 * 5 := by
      rw [hcardA5, hm_eq]
      norm_num
    exact Nat.mul_right_cancel (by norm_num : 0 < 5) h1

  refine ⟨rfl, hm_eq, A, hAJ, hcardA4, ?_, ?_⟩
  ·
    intro b hb
    let bB : B := ⟨b, hb⟩
    have hmemA : ((β bB : ↥J) : G) ∈ A :=
      Subgroup.mem_map.mpr ⟨β bB, MonoidHom.mem_range.mpr ⟨bB, rfl⟩, rfl⟩
    refine ⟨((β bB : ↥J) : G), hmemA, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h := hβconj bB ⟨j, hj⟩
    have h' : ((β bB : ↥J) : G)⁻¹ * (bB : G) * (j : G) =
        (j : G) * (((β bB : ↥J) : G)⁻¹ * (bB : G)) := by
      calc ((β bB : ↥J) : G)⁻¹ * (bB : G) * (j : G) =
          ((β bB : ↥J) : G)⁻¹ * ((bB : G) * (j : G) * (bB : G)⁻¹) * (bB : G) := by group
        _ = ((β bB : ↥J) : G)⁻¹ *
            (((β bB : ↥J) : G) * (j : G) * ((β bB : ↥J) : G)⁻¹) * (bB : G) := by rw [h]
        _ = (j : G) * (((β bB : ↥J) : G)⁻¹ * (bB : G)) := by group
    exact h'.symm
  ·
    intro a ha
    obtain ⟨aJ, haJ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp haJ
    refine ⟨(b : G), b.2, ?_⟩
    rw [← hb]
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h := hβconj b ⟨j, hj⟩
    have h' : ((β b : ↥J) : G)⁻¹ * (b : G) * (j : G) =
        (j : G) * (((β b : ↥J) : G)⁻¹ * (b : G)) := by
      calc ((β b : ↥J) : G)⁻¹ * (b : G) * (j : G) =
          ((β b : ↥J) : G)⁻¹ * ((b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by group
        _ = ((β b : ↥J) : G)⁻¹ *
            (((β b : ↥J) : G) * (j : G) * ((β b : ↥J) : G)⁻¹) * (b : G) := by rw [h]
        _ = (j : G) * (((β b : ↥J) : G)⁻¹ * (b : G)) := by group
    exact h'.symm

end CFSG.Assembly

end
