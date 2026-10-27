module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreMaxStrict

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

open CFSG.RankThree.PartTwo.Sec19 (descPSUHom descPSUHom_injective descPSUHom_suConj
  descPSUHom_suField)

theorem descPSUHom_surjective_u3 {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (hq : 2 < 2 ^ 3) : Function.Surjective (descPSUHom h hq) := by
  intro α
  obtain ⟨B, σ, rfl⟩ := exists_psuConj_mul_psuField (h := h) hq α
  exact ⟨suConj h B * suField h σ, by rw [map_mul, descPSUHom_suConj, descPSUHom_suField]⟩

theorem descPSUHom_conj_u3 {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (hq : 2 < 2 ^ 3)
    (e : unitarySU 2 3 F 3) :
    descPSUHom h hq (MulAut.conj e) = MulAut.conj (unitaryProj h 3 e) := by
  rw [CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.conj_eq_suConj (h := h) e, descPSUHom_suConj]
  exact (conj_mk_eq_psuConj e).symm

theorem maxMod_map_conj {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (hq : 2 < 2 ^ 3)
    (c : MulAut (unitarySU 2 3 F 3)) (A : Subgroup (MulAut (unitaryPSU h 3)))
    (hMax : ∀ e : unitaryPSU h 3, e ^ 3 = 1 → (∀ α ∈ A, α e = e) → MulAut.conj e ∈ A)
    (e : unitarySU 2 3 F 3) (he3 : e ^ 3 = 1)
    (hfix : ∀ α ∈ (A.comap (descPSUHom h hq)).map (MulAut.conj c).toMonoidHom,
      ∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), α e = e * z) :
    MulAut.conj e ∈ (A.comap (descPSUHom h hq)).map (MulAut.conj c).toMonoidHom := by
  have hDsurj := descPSUHom_surjective_u3 h hq
  have he' : (c⁻¹ e) ^ 3 = 1 := by rw [← map_pow, he3, map_one]
  have hx3 : (unitaryProj h 3 (c⁻¹ e)) ^ 3 = 1 := by rw [← map_pow, he', map_one]
  have hfix' : ∀ β ∈ A, β (unitaryProj h 3 (c⁻¹ e)) = unitaryProj h 3 (c⁻¹ e) := by
    intro β hβ
    obtain ⟨β', rfl⟩ := hDsurj β
    obtain ⟨z, hz, hz'⟩ := hfix (c * β' * c⁻¹) ⟨β', hβ, by simp [MulAut.conj_apply]⟩
    have h1 : β' (c⁻¹ e) = c⁻¹ e * c⁻¹ z := by
      have := congrArg (fun x => c⁻¹ x) hz'
      simpa using this
    have hker : unitaryProj h 3 (c⁻¹ z) = 1 := by
      have : c⁻¹ z ∈ (unitaryProj h 3).ker := by
        rw [ker_unitaryProj, ← center_unitarySU_three (h := h) hq]
        exact apply_mem_center c⁻¹ hz
      exact this
    show unitaryProj h 3 (β' (c⁻¹ e)) = _
    rw [h1, map_mul, hker, mul_one]
  have hconj' : MulAut.conj (c⁻¹ e) ∈ A.comap (descPSUHom h hq) := by
    rw [Subgroup.mem_comap, descPSUHom_conj_u3]
    exact hMax _ hx3 hfix'
  refine ⟨MulAut.conj (c⁻¹ e), hconj', ?_⟩
  have h4 := conj_apply_aut c (c⁻¹ e)
  rw [MulAut.apply_inv_self] at h4
  rw [h4]
  simp [MulAut.conj_apply]

theorem three_mul_card_le_of_not_mem {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hK : IsElemAbelian 3 K) (hHK : H ≤ K) {x : G} (hxK : x ∈ K) (hxH : x ∉ H) :
    3 * Nat.card H ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hK.isPGroup
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 (hK.mono hHK).isPGroup
  have hlt : Nat.card H < Nat.card K :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hHK fun heq => hxH (by rw [heq]; exact hxK))
  rw [hj, hk] at hlt ⊢
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  calc 3 * 3 ^ j = 3 ^ (j + 1) := by ring
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hjk

theorem card_inf_range_suConj_le_nine {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (E : Subgroup (MulAut (unitarySU 2 3 F 3))) (hE : IsElemAbelian 3 E) :
    Nat.card ↥(E ⊓ (suConj h).range) ≤ 9 := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  have hK3 : 3 ∣ Nat.card F - 1 := by rw [h.card]; norm_num
  have hle := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range
    (h := h) hK3 ((E ⊓ (suConj h).range).map (descPSUHom h hq))
    (by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨B, rfl⟩ := hd.2
      exact ⟨B, (descPSUHom_suConj h hq B).symm⟩)
    (by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
      rw [← map_mul, ← map_mul, hE.comm hd.1 hd'.1])
    (by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, hE.2 d hd.1, map_one])
  rwa [Subgroup.card_map_of_injective (descPSUHom_injective h hq)] at hle

theorem card_le_three_mul_card_inf_range_suConj {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    {σ : F ≃+* F} (hσ : orderOf σ = 3) (E : Subgroup (MulAut (unitarySU 2 3 F 3)))
    (hE : IsElemAbelian 3 E) (hf : suField h σ ∈ E) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ (suConj h).range) := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  have hm : Function.Surjective (fun p : ↥(E ⊓ (suConj h).range) × Fin 3 =>
      (⟨(p.1 : MulAut (unitarySU 2 3 F 3)) * suField h σ ^ (p.2 : ℕ),
        mul_mem p.1.2.1 (pow_mem hf _)⟩ : E)) := by
    rintro ⟨α, hα⟩
    obtain ⟨B, k, hk, hαB, -, -⟩ :=
      exists_suConj_mul_suField_pow h hq hσ (hE.2 α hα) (hE.comm hα hf)
    have hBE : suConj h B ∈ E := by
      have : suConj h B = α * (suField h σ ^ k)⁻¹ := by rw [hαB, mul_inv_cancel_right]
      rw [this]
      exact mul_mem hα (inv_mem (pow_mem hf k))
    exact ⟨(⟨suConj h B, hBE, B, rfl⟩, ⟨k, hk⟩), Subtype.ext hαB.symm⟩
  have hcard := Nat.card_le_card_of_surjective _ hm
  rwa [Nat.card_prod, Nat.card_fin, mul_comm] at hcard

theorem twentySeven_le_card_of_suField_mem {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    {σ : F ≃+* F} (hσ : orderOf σ = 3) (E : Subgroup (MulAut (unitarySU 2 3 F 3)))
    (hE : IsElemAbelian 3 E) (hf : suField h σ ∈ E) {a₁ a₂ : MulAut (unitarySU 2 3 F 3)}
    (ha₁ : a₁ ∈ E ⊓ (suConj h).range) (ha₁1 : a₁ ≠ 1) (ha₂ : a₂ ∈ E ⊓ (suConj h).range)
    (ha₂ni : a₂ ∉ Subgroup.zpowers a₁) : 27 ≤ Nat.card E := by
  have := h.finite
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hfInn : suField h σ ∉ E ⊓ (suConj h).range :=
    fun hmem => suField_not_mem_range h hσ1 hmem.2
  have h1 : 3 * Nat.card (Subgroup.zpowers a₁) ≤ Nat.card ↥(E ⊓ (suConj h).range) :=
    three_mul_card_le_of_not_mem (hE.mono inf_le_left) (Subgroup.zpowers_le.2 ha₁) ha₂ ha₂ni
  have h2 : 3 * Nat.card ↥(E ⊓ (suConj h).range) ≤ Nat.card E :=
    three_mul_card_le_of_not_mem hE inf_le_left hf hfInn
  have h3 : Nat.card (Subgroup.zpowers a₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE.2 a₁ ha₁.1) ha₁1
  omega

theorem exists_rankThree_of_maxMod
    {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (A : Subgroup (MulAut (unitaryPSU h 3))) (hA : IsElemAbelian 3 A)
    (hφ : ∃ φ ∈ A, φ ∉ (psuConj h).range)
    (hMax : ∀ e : unitaryPSU h 3, e ^ 3 = 1 → (∀ α ∈ A, α e = e) → MulAut.conj e ∈ A) :
    Nat.card A = 27 := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  have hDinj := descPSUHom_injective h hq
  have hDsurj := descPSUHom_surjective_u3 h hq
  have hÃel : IsElemAbelian 3 (A.comap (descPSUHom h hq)) := hA.comap hDinj
  have hÃcard : Nat.card (A.comap (descPSUHom h hq)) = Nat.card A := by
    calc Nat.card (A.comap (descPSUHom h hq))
        = Nat.card ((A.comap (descPSUHom h hq)).map (descPSUHom h hq)) :=
          (Subgroup.card_map_of_injective hDinj).symm
      _ = Nat.card A := by rw [Subgroup.map_comap_eq_self_of_surjective hDsurj A]
  obtain ⟨φ, hφA, hφN⟩ := hφ
  obtain ⟨φ', rfl⟩ := hDsurj φ
  have hφ'N : φ' ∉ (suConj h).range := by
    rintro ⟨B, rfl⟩
    exact hφN ⟨B, (descPSUHom_suConj h hq B).symm⟩
  obtain ⟨σ, hσ, H, hH⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.eq_conj_suField_of_not_mem (h := h) hq
      (hÃel.2 φ' hφA) hφ'N
  have hf₁ := mem_map_conj_inv_of_eq_mul_inv (suConj h H) (Subgroup.mem_comap.2 hφA) hH
  have hA₁ := hÃel.map (MulAut.conj (suConj h H)⁻¹).toMonoidHom
  have hcard : Nat.card ((A.comap (descPSUHom h hq)).map (MulAut.conj (suConj h H)⁻¹).toMonoidHom) =
      Nat.card A := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (suConj h H)⁻¹).injective, hÃcard]
  rcases inn_dichotomy h hσ _ hA₁ hf₁ with
    ⟨⟨a₁, ha₁, ha₁1, a₂, ha₂, ha₂ni⟩, -⟩ | ⟨e, he3, hcen, hconj, -⟩
  · have hle := (card_le_three_mul_card_inf_range_suConj h hσ _ hA₁ hf₁).trans
      (Nat.mul_le_mul_left 3 (card_inf_range_suConj_le_nine h _ hA₁))
    have hge := twentySeven_le_card_of_suField_mem h hσ _ hA₁ hf₁ ha₁ ha₁1 ha₂ ha₂ni
    omega
  · exact absurd (maxMod_map_conj h hq _ A hMax e he3 hcen) hconj

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
