module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem comap_pPrimeCore_le {T M : Subgroup H} (hTM : T ≤ M) :
    (pPrimeCore 2 M).comap (inclusion hTM) ≤ pPrimeCore 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨inferInstance, ?_⟩
  exact Nat.Coprime.coprime_dvd_right
    (card_comap_dvd_of_injective _ _ (inclusion_injective hTM)) pPrimeCore_coprime_card

theorem mem_fusionZStar_of_le {T M : Subgroup H} (hTM : T ≤ M) {w : T}
    (hw : inclusion hTM w ∈ Open.fusionZStar M) : w ∈ Open.fusionZStar T := by
  rw [Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff] at hw ⊢
  intro g
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 T) g
  have h := hw (QuotientGroup.mk' _ (inclusion hTM t))
  simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h ⊢
  apply comap_pPrimeCore_le hTM
  rw [mem_comap]
  simpa only [map_mul, map_inv] using h

theorem mk_mem_center_ne_one {L : Type*} [Group L] [Finite L] {w : L}
    (hw : w ∈ Open.fusionZStar L) (hw2 : orderOf w = 2) :
    QuotientGroup.mk' (pPrimeCore 2 L) w ∈ center (L ⧸ pPrimeCore 2 L) ∧
      QuotientGroup.mk' (pPrimeCore 2 L) w ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sol78.fusionZStar_eq_comap, mem_comap] at hw
  refine ⟨hw, fun h => ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hdvd := Subgroup.orderOf_dvd_natCard _ h
  rw [hw2] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card hdvd

theorem fusionZStar_map_le {T M : Subgroup H} (hTM : T ≤ M)
    (hZ : Nat.card (center (T ⧸ pPrimeCore 2 T)) = 2) {w : H} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwM : w ∈ (Open.fusionZStar M).map M.subtype) :
    (Open.fusionZStar T).map T.subtype ≤
      (pPrimeCore 2 T).map T.subtype ⊔ (Open.fusionZStar M).map M.subtype := by
  have hw'Z : (⟨w, hwT⟩ : T) ∈ Open.fusionZStar T := by
    refine mem_fusionZStar_of_le hTM ?_
    obtain ⟨m, hm, rfl⟩ := hwM
    have he : inclusion hTM ⟨M.subtype m, hwT⟩ = m := Subtype.ext (by simp)
    rw [he]
    exact hm
  obtain ⟨hc, h1⟩ := mk_mem_center_ne_one hw'Z (by rwa [← Subgroup.orderOf_coe])
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
  rw [Sol78.fusionZStar_eq_comap, mem_comap] at hz
  have key : QuotientGroup.mk' (pPrimeCore 2 T) z = 1 ∨
      QuotientGroup.mk' (pPrimeCore 2 T) z = QuotientGroup.mk' (pPrimeCore 2 T) ⟨w, hwT⟩ := by
    obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : center (T ⧸ pPrimeCore 2 T))).mp hZ
    by_contra! h
    have e1 := hyu ⟨_, hz⟩ fun h' => h.1 (congrArg Subtype.val h')
    have e2 := hyu ⟨_, hc⟩ fun h' => h1 (congrArg Subtype.val h')
    exact h.2 (congrArg Subtype.val (e1.trans e2.symm))
  rcases key with h | h
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact mem_sup_left (mem_map_of_mem _ h)
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    have hz' : T.subtype z = w * T.subtype (z⁻¹ * ⟨w, hwT⟩)⁻¹ := by simp
    rw [hz']
    exact mul_mem (mem_sup_right hwM) (mem_sup_left (mem_map_of_mem _ (inv_mem h)))

theorem isDoubleCoverOfAlt_of_center_ne_bot (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hZ : center Q ≠ ⊥) {k : ℕ} (hk : 5 ≤ k) (e : Q ⧸ center Q ≃* alternatingGroup (Fin k)) :
    GH74.GLS.IsDoubleCoverOfAlt Q k := by
  have : Group.IsPerfect Q := hQ.1
  have hle := Sol78.card_center_le_two hS hO hk e
  have hlt := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
  exact ⟨hQ, by omega, ⟨e⟩⟩

end CFSG.ComponentClassification.GS82PumpInputs
