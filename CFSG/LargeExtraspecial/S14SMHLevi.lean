module

public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SMH

open Subgroup CFSG.Open

theorem isSimpleGroup_timmesfeldPSU_six : IsSimpleGroup (timmesfeldPSU 6) := by
  have hK : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 2 2) 2 1
    hK 6 (by norm_num) (by decide)
  exact ((timmesfeldPSUEquiv (n := 6) (by norm_num)).trans
    (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv unitaryFieldData_two_one (n := 6)
      (by norm_num))).isSimpleGroup

variable {G : Type} [Group G]

theorem conj_eq_of_pow_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : b * a * b * (b * a)⁻¹ = a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : a * b * (a * b) * (a * b) = 1 := by rw [← h, pow_succ, sq]
  have hbab : b * a * b = a * b * a := by
    calc b * a * b = a⁻¹ * (a * b * (a * b) * (a * b)) * b⁻¹ * a⁻¹ := by group
      _ = a * b * a := by rw [h3, hai, hbi]; group
  calc b * a * b * (b * a)⁻¹ = b * a * b * a * b := by rw [mul_inv_rev, hai, hbi]; group
    _ = a * b * a * a * b := by rw [hbab]
    _ = a := by rw [mul_assoc (a * b) a a, ha, mul_one, mul_assoc, hb, mul_one]

theorem not_mem_QG_of_orderOf_eq_three [Finite G] (S : Setting G) {a b : G}
    (hb : b * b = 1) (hbM : b ∈ S.M) (h3 : orderOf (a * b) = 3) : a ∉ S.QG := by
  intro ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h2 : (a * b) ^ 2 ∈ S.QG := by
    have e : (a * b) ^ 2 = a * (b * a * b⁻¹) := by rw [hbi, sq]; group
    rw [e]
    exact S.QG.mul_mem ha (S.conj_mem_QG hbM ha)
  have h1 : a * b ∈ S.QG := by
    have e : a * b = ((a * b) ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, ← h3, pow_orderOf_eq_one, one_mul]
    rw [e]
    exact S.QG.pow_mem h2 2
  have hd := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one h1)
  rw [h3] at hd
  norm_num at hd

@[expose] noncomputable def toMbarM [Finite G] (S : Setting G) : S.M →* S.Mbar :=
  S.ρ.rangeRestrict

@[expose] noncomputable def toMbar [Finite G] (S : Setting G) {N : Subgroup G} (hNM : N ≤ S.M) :
    N →* S.Mbar :=
  (toMbarM S).comp (Subgroup.inclusion hNM)

theorem toMbar_apply [Finite G] (S : Setting G) {N : Subgroup G} (hNM : N ≤ S.M) (n : N) :
    toMbar S hNM n = toMbarM S ⟨n, hNM n.2⟩ := rfl

theorem levi_of_le_M [Finite G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {N : Subgroup G} (hNM : N ≤ S.M)
    (hN : Nonempty (N ≃* timmesfeldPSU 6)) (hNQ : ¬ N ≤ S.QG) :
    (∀ n ∈ N, n ∈ S.QG → n = 1) ∧ (toMbar S hNM).range = Mbar0 S := by
  obtain ⟨eN⟩ := hN
  have := isSimpleGroup_timmesfeldPSU_six
  have : IsSimpleGroup N := eN.isSimpleGroup
  have : Finite S.Mbar := Bridge.finite_Mbar S
  have hcardN : Nat.card N = 9196830720 := by
    rw [Nat.card_congr eN.toEquiv, card_timmesfeldPSU_six]
  have hker : (toMbar S hNM).ker = ⊥ := by
    rcases (toMbar S hNM).normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      refine hNQ fun n hn => ?_
      have h1 : (⟨n, hn⟩ : N) ∈ (toMbar S hNM).ker := by rw [h]; exact mem_top _
      rw [MonoidHom.mem_ker] at h1
      exact (S.ρ_eq_one_iff ⟨n, hNM hn⟩).mp (congrArg Subtype.val h1)
  have hinj : Function.Injective (toMbar S hNM) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hidx : (Mbar0 S).index ∣ 6 := (card_M_of_U6 S hw hU).1
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  have hle : (toMbar S hNM).range ≤ Mbar0 S := by
    rcases ((QuotientGroup.mk' (Mbar0 S)).comp (toMbar S hNM)).normal_ker.eq_bot_or_eq_top
      with h | h
    · exfalso
      have h1 := Nat.card_le_card_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp h)
      have h2 : (Mbar0 S).index ≤ 6 := Nat.le_of_dvd (by norm_num) hidx
      rw [hcardN, ← Subgroup.index_eq_card] at h1
      omega
    · rintro _ ⟨n, rfl⟩
      have h1 : n ∈ ((QuotientGroup.mk' (Mbar0 S)).comp (toMbar S hNM)).ker := by
        rw [h]
        exact mem_top _
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h1
  refine ⟨fun n hn hnQ => congrArg Subtype.val (hinj (a₁ := ⟨n, hn⟩) (a₂ := 1) (Subtype.ext ?_)),
    Subgroup.eq_of_le_of_card_ge hle ?_⟩
  · rw [map_one, OneMemClass.coe_one]
    exact (S.ρ_eq_one_iff ⟨n, hNM hn⟩).mpr hnQ
  · obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr eN.toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end SMH

end CFSG.LargeExtraspecial.S14
