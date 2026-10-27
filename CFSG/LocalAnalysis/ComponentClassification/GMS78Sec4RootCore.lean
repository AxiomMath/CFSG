module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResU

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L T U₁ : Subgroup G} {f : ℕ}

namespace Sec3

theorem exists_mem_A_le_centralizer (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    ∃ a ∈ gmsA L T, a ≠ 1 ∧ T ≤ centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := h.sylow.isPGroup.isNilpotent
  set H : Subgroup T := (T ⊓ L).subgroupOf T with hH
  have hHn : H.Normal := ⟨fun n hn g => by
    rw [hH, mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (h.mem_normalizer_T₁ g.2) (n : G)).mp hn⟩
  have hH1 : H ≠ ⊥ := by
    intro hb
    have h8 := h.eight_le_card_T₁
    have hle : T ⊓ L ≤ ⊥ := by
      intro a ha
      have haH : (⟨a, (mem_inf.mp ha).1⟩ : T) ∈ H := mem_subgroupOf.mpr ha
      rw [hb, mem_bot] at haH
      exact mem_bot.mpr (congrArg Subtype.val haH)
    rw [le_bot_iff.mp hle, card_bot] at h8
    omega
  obtain ⟨⟨a, haH, haZ⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
  refine ⟨(a : G), by rw [h.gmsA_eq_of_psl2 hf e]; exact mem_subgroupOf.mp haH,
    fun h1 => ha1 (Subtype.ext (Subtype.ext h1)), fun t ht => ?_⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((mem_center_iff.mp haZ) ⟨t, ht⟩))

end Sec3

namespace Sec4Base

theorem false_of_conj_mem_A
    (hE : Sec4Base L T U₁) (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f)) (hS₀ : IsSylowOf 2 (U₁ ⊔ T) ⊤) {x m : G} (hxT : x ∈ T)
    (hxV : x ∉ gmsV L T) (hxx : x * x = 1)
    (hxT₀ : T ⊓ centralizer (L : Set G) ≤ centralizer ({x} : Set G))
    (hm : m * x * m⁻¹ ∈ gmsA L T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  have hAeq : gmsA L T = T ⊓ L := h.gmsA_eq_of_psl2 hf e
  have hAel : IsElemAbelian 2 (gmsA L T) := by
    rw [hAeq]
    exact isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hAcard : Nat.card (gmsA L T) = 2 ^ f := (hX.sylow h).1
  obtain ⟨a, haA, ha1, hTa⟩ := h.exists_mem_A_le_centralizer hf e
  have hS₀a : U₁ ⊔ T ≤ centralizer ({a} : Set G) :=
    sup_le (fun u hu => mem_centralizer_singleton_iff.mpr (hE.comm hu (hE.A_le haA))) hTa
  have hS₀C : IsSylowOf 2 (U₁ ⊔ T) (centralizer ({a} : Set G)) := hS₀.of_le hS₀a le_top
  obtain ⟨y₀, -, -, htrans, -⟩ := hX.exists_torus_conj h
  have hm1 : m * x * m⁻¹ ≠ 1 := fun h1 => hxV (by
    rw [show x = m⁻¹ * (m * x * m⁻¹) * m by group, h1, mul_one, inv_mul_cancel]
    exact one_mem _)
  obtain ⟨j, hj⟩ := htrans _ hm a haA hm1 ha1
  set k := m⁻¹ * y₀ ^ j with hk
  have hka : k⁻¹ * x * k = a := by rw [← hj, hk]; group
  obtain ⟨E₀, hE₀T₀, hE₀el, hE₀4⟩ := h.exists_four_le
  have hE₀p : IsPGroup 2 E₀ := fun z => ⟨1, Subtype.ext (by simpa using hE₀el.2 z z.2)⟩
  have hFa : rightConjugate E₀ k ≤ centralizer ({a} : Set G) := by
    intro z hz
    rw [mem_rightConjugate_iff] at hz
    have hc : k * z * k⁻¹ * x = x * (k * z * k⁻¹) :=
      mem_centralizer_singleton_iff.mp (hxT₀ (hE₀T₀ hz))
    rw [mem_centralizer_singleton_iff, ← hka]
    calc z * (k⁻¹ * x * k) = k⁻¹ * (k * z * k⁻¹ * x) * k := by group
      _ = k⁻¹ * (x * (k * z * k⁻¹)) * k := by rw [hc]
      _ = k⁻¹ * x * k * z := by group
  obtain ⟨c, hc, hcF⟩ := exists_conj_le_of_isSylowOf hS₀C hFa (hE₀p.map _)
  have hca : c * a = a * c := mem_centralizer_singleton_iff.mp hc
  set y := k * c⁻¹ with hy
  have hya : y * a * y⁻¹ = x := by
    calc y * a * y⁻¹ = k * (c⁻¹ * (c * a)) * k⁻¹ := by rw [hca, hy]; group
      _ = x := by rw [inv_mul_cancel_left, ← hka]; group
  have hF''S : rightConjugate E₀ y ≤ U₁ ⊔ T := by
    intro z hz
    rw [mem_rightConjugate_iff] at hz
    have hzF : c⁻¹ * z * c ∈ rightConjugate E₀ k := by
      rw [mem_rightConjugate_iff]
      rwa [show k * (c⁻¹ * z * c) * k⁻¹ = y * z * y⁻¹ by rw [hy]; group]
    have hz' := hcF _ hzF
    rwa [show c * (c⁻¹ * z * c) * c⁻¹ = z by group] at hz'
  have hF''2 : ∀ z ∈ rightConjugate E₀ y, z * z = 1 := by
    intro z hz
    rw [mem_rightConjugate_iff] at hz
    have h1 : y * (z * z) * y⁻¹ = 1 := by
      rw [show y * (z * z) * y⁻¹ = y * z * y⁻¹ * (y * z * y⁻¹) by group, ← sq]
      exact hE₀el.2 _ hz
    calc z * z = y⁻¹ * (y * (z * z) * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have h2 := hE.card_le_two_mul h hf e hF''S hF''2
  rw [rightConjugate_card, hE₀4] at h2
  obtain ⟨w, hwFW, hw1⟩ : ∃ w ∈ rightConjugate E₀ y ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))),
      w ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : rightConjugate E₀ y ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ ⊥ :=
      fun z hz => mem_bot.mpr (hall z hz)
    rw [le_bot_iff.mp hle, card_bot] at h2
    omega
  obtain ⟨hwF, hwW⟩ := mem_inf.mp hwFW
  have hwK : y * w * y⁻¹ ∈ centralizer (L : Set G) :=
    (mem_inf.mp (hE₀T₀ ((mem_rightConjugate_iff _ _ _).mp hwF))).2
  have hAw : gmsA L T ≤ centralizer ({w} : Set G) := by
    intro b hb
    rw [mem_centralizer_singleton_iff]
    obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq hwW
    have hbu : b * u = u * b := hE.comm (hE.A_le hb) hu
    have hbt : b * t = t * b :=
      mem_centralizer_iff.mp (mem_inf.mp ht).2 b (mem_inf.mp (mem_inf.mp hb).1).2
    calc b * (u * t) = u * (b * t) := by rw [← mul_assoc, hbu, mul_assoc]
      _ = u * t * b := by rw [hbt, mul_assoc]
  have hP3 := h.card_le_two_mul_inf_rightConjugate hf e h313 hwK hw1 (hF''2 w hwF) le_rfl hAw
  rw [hAcard] at hP3
  set B := (gmsA L T ⊓ rightConjugate L y).map (MulAut.conj y).toMonoidHom with hB
  have hBcard : Nat.card B = Nat.card (gmsA L T ⊓ rightConjugate L y : Subgroup G) :=
    card_map_of_injective (MulAut.conj y).injective
  have hBL : B ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using (mem_rightConjugate_iff _ _ _).mp (mem_inf.mp hb).2
  have hBx : B ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hba : b * a = a * b :=
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨b, (mem_inf.mp hb).1⟩ ⟨a, haA⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hya]
    calc y * b * y⁻¹ * (y * a * y⁻¹) = y * (b * a) * y⁻¹ := by group
      _ = y * (a * b) * y⁻¹ := by rw [hba]
      _ = y * a * y⁻¹ * (y * b * y⁻¹) := by group
  have hBel : IsElemAbelian 2 B := isElemAbelian_map _ (isElemAbelian_of_le hAel inf_le_left)
  have hBp : IsPGroup 2 B := fun z => ⟨1, Subtype.ext (by simpa using hBel.2 z z.2)⟩
  obtain ⟨P, hP, hBP⟩ := AS76b.exists_isSylowOf_le hBL hBp
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    have h1 : 1 < Nat.card B := by
      have : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨b, hb, fun h1 => hb1 (Subtype.ext h1)⟩
  have hxN : x ∈ normalizer (L : Set G) := h.sylow.le hxT
  have hxP : ∀ z ∈ P, x * z * x⁻¹ ∈ P := by
    have hP' : IsSylowOf 2 (rightConjugate P x⁻¹) L := by
      have := AschbacherTheorem3.isSylowOf_rightConjugate hP x⁻¹
      rwa [(rightConjugate_eq_self_iff L x⁻¹).mpr (inv_mem hxN)] at this
    have hbP' : b ∈ rightConjugate P x⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      have hbx : b * x = x * b := mem_centralizer_singleton_iff.mp (hBx hbB)
      rw [show x⁻¹ * b * x = b by rw [mul_assoc, hbx, inv_mul_cancel_left]]
      exact hBP hbB
    obtain ⟨k₀, hk₀⟩ := hX.borel
    have heq := eq_of_mem_of_mem hZ hP hP' hk₀ (hBP hbB) hbP' hb1
    intro z hz
    have hz' : x * z * x⁻¹ ∈ rightConjugate P x⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      simpa [mul_assoc] using hz
    rwa [← heq] at hz'
  have hxLK : x ∉ L ⊔ centralizer (L : Set G) := fun hLK => hxV ((h.mem_V_iff hf e hxT).mpr hLK)
  have hsq := card_centralizer_sq_le_of_sq_mem hLp hZ (by omega) e hP hxN hxP hxLK
    (by rw [hxx]; exact one_mem _)
  have hPcard : Nat.card P = 2 ^ f := by
    obtain ⟨g₀, -, hg₀⟩ := IsSylowOf.exists_map_conj h.isSylowOf_T₁ hP
    rw [hg₀, card_map_of_injective (MulAut.conj g₀).injective, ← hAeq, hAcard]
  have hBle : Nat.card B ≤ Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_le_of_le (le_inf hBP hBx)
  rw [hPcard] at hsq
  rw [hBcard] at hBle
  have hq8 : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  set Q := 2 ^ f with hQ
  set d := Nat.card (gmsA L T ⊓ rightConjugate L y : Subgroup G) with hd
  set c' := Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) with hc'
  have h4 : Q * Q ≤ 4 * Q := by
    calc Q * Q ≤ (2 * d) * (2 * d) := Nat.mul_le_mul hP3 hP3
      _ = 4 * (d * d) := by ring
      _ ≤ 4 * (c' * c') := Nat.mul_le_mul_left 4 (Nat.mul_le_mul hBle hBle)
      _ ≤ 4 * Q := Nat.mul_le_mul_left 4 (by rw [← sq]; exact hsq)
  have h5 : Q ≤ 4 := Nat.le_of_mul_le_mul_right h4 (by omega : 0 < Q)
  omega

end Sec4Base

theorem gms42ResidualRoot :
    GMS42ResidualRoot := by
  intro G _ _ L T U₁ h hF he hX h313 hE _ _ _ g _ _ _ _ _ _ _ _ _ _ _ _ w _ _ _ _ hww _ _ c _
    x hcx hxT hxV _ hxT₀ hroot
  obtain ⟨e⟩ := he
  have hxx : x * x = 1 := by
    rw [← hcx, show c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ by group, hww, mul_one,
      mul_inv_cancel]
  exact hE.toSec4Base.false_of_conj_mem_A h (by norm_num) e hX h313
    (hE.isSylowOf_top h hF (by norm_num) e hX) hxT hxV hxx hxT₀ hroot

end CFSG.ComponentClassification.GMS78
