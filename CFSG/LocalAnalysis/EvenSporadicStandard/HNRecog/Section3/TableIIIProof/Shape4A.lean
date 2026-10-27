module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

open scoped commutatorElement

private theorem t3_sq_eq_one_of_isConj {a z c : G} (h : IsF5Type a z) (hc : IsConj a c) :
    c ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc
  rw [conj_pow, ← h.orderOf_a, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

private theorem t3_inv_eq_self {x : G} (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hx])

private def t3_commHom {a z : G} (h : IsF5Type a z) (a' c : G) (hcQ : c ∈ Qz z) :
    ↥(Qz z ⊓ Gx a') →* ↥(Subgroup.zpowers z) where
  toFun w := ⟨⁅(w : G), c⁆, commutatorElement_mem_zpowers_of_mem_Qz h w.2.1 hcQ⟩
  map_one' := by
    ext
    simp [commutatorElement_def]
  map_mul' w₁ w₂ := by
    ext
    have hcomm : ∀ w ∈ Qz z, ⁅w, c⁆ = 1 ∨ ⁅w, c⁆ = z := fun w hw =>
      (tableIII_mem_zpowers_iff h).1 (commutatorElement_mem_zpowers_of_mem_Qz h hw hcQ)
    have hzw : (w₁ : G) * z = z * w₁ := (mem_Gx.1 (tableIII_Qz_le z w₁.2.1)).symm
    have key : ⁅(w₁ : G) * w₂, c⁆ = (w₁ : G) * ⁅(w₂ : G), c⁆ * (w₁ : G)⁻¹ * ⁅(w₁ : G), c⁆ := by
      simp only [commutatorElement_def]
      group
    have hconj : (w₁ : G) * ⁅(w₂ : G), c⁆ * (w₁ : G)⁻¹ = ⁅(w₂ : G), c⁆ := by
      rcases hcomm _ w₂.2.1 with h2 | h2
      · rw [h2]
        group
      · rw [h2, hzw]
        group
    change ⁅(w₁ : G) * w₂, c⁆ = ⁅(w₁ : G), c⁆ * ⁅(w₂ : G), c⁆
    rw [key, hconj]
    rcases hcomm _ w₁.2.1 with h1 | h1 <;> rcases hcomm _ w₂.2.1 with h2 | h2 <;> simp [h1, h2]

theorem tableIII_card_inf_Qz_4A (hI : TwoHSInterface) [Finite G] {a z a' c : G}
    (h : IsF5Type a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') (hc : c ∈ tab3Set a z a' 2) :
    Nat.card ↥(Gxyz a' z c ⊓ Qz z) = 2 ^ 7 := by
  obtain ⟨⟨hcQ, hcA, -, -⟩, hsq⟩ := hc
  obtain ⟨ha'2, ha'1, ha'z, -, -, -, -, -⟩ := tableIII_basic hI h ha'Q ha'
  have hc2 := t3_sq_eq_one_of_isConj h hcA
  set f := t3_commHom h a' c hcQ
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rcases (tableIII_mem_zpowers_iff h).1 hy with hy1 | hyz
    · refine ⟨1, Subtype.ext ?_⟩
      simp [hy1]
    · refine ⟨⟨a', ha'Q, self_mem_Gx a'⟩, Subtype.ext ?_⟩
      change ⁅a', c⁆ = y
      rw [hyz, ← hsq, commutatorElement_def, t3_inv_eq_self ha'2, t3_inv_eq_self hc2, pow_two]
      simp only [mul_assoc]
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [Nat.card_zpowers, h.orderOf_z, tableIII_card_Qz_inf_Gx h ha'Q ha'1 ha'z] at hcard
  have hker : f.ker.map (Qz z ⊓ Gx a').subtype = Gxyz a' z c ⊓ Qz z := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf, mem_Gxyz]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : ⁅(w : G), c⁆ = 1 := congrArg Subtype.val hw
      rw [commutatorElement_eq_one_iff_mul_comm] at hw'
      exact ⟨⟨w.2.2, tableIII_Qz_le z w.2.1, mem_Gx.2 hw'.symm⟩, w.2.1⟩
    · rintro ⟨⟨h1, -, h3⟩, hgQ⟩
      refine ⟨⟨g, hgQ, h1⟩, Subtype.ext ?_, rfl⟩
      change ⁅g, c⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (mem_Gx.1 h3).symm
  rw [← hker, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  omega

theorem tableIII_shape_4A [Finite G] {z a' c : G}
    (hcQ : Nat.card ↥(Gxyz a' z c ⊓ Qz z) = 2 ^ 7)
    (hcard : Nat.card ↥(Gxyz a' z c) = 2 ^ 7 * 5) : IsShapeTwoOneSixByFive ↥(Gxyz a' z c) := by
  set X := Gxyz a' z c
  set N := (Qz z).subgroupOf X
  have hXz : X ≤ Gx z := fun g hg => (mem_Gxyz.1 hg).2.1
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact tableIII_conj_mem_Qz (hXz g.2) hn⟩
  have hNcard : Nat.card ↥N = 2 ^ 7 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm, hcQ]
  refine ⟨N, hN, hNcard, ?_⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hcard, hNcard] at h
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
