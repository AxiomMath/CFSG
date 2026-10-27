module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.Timmesfeld75.Sec3Conj

public section

namespace CFSG.CGT.T75G

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

section SL2

variable {F : Type*} [Field F]

theorem exists_sl_column (a : Fin 2 → F) (ha : a ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = a := by
  by_cases h : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1
      apply ha
      ext i
      fin_cases i
      · exact h
      · exact h1
    refine ⟨⟨!![0, -(a 1)⁻¹; a 1, 0], by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring⟩, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![a 0, 0; a 1, (a 0)⁻¹], by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring⟩, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl_mulVec_eq {a b : Fin 2 → F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F).mulVec a = b := by
  obtain ⟨A, hA⟩ := exists_sl_column a ha
  obtain ⟨B, hB⟩ := exists_sl_column b hb
  refine ⟨B * A⁻¹, ?_⟩
  have h1 : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec a =
      ![1, 0] := by
    rw [← hA, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hB]

end SL2

section Natural

variable {G : Type} [Group G] {T H : Subgroup G} {m : ℕ}

theorem NaturalSL.exists_conj (hnat : NaturalSL T H 2 m) (hTH : T ≤ H) {x y : G} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hy : y ∈ T) (hy1 : y ≠ 1) : ∃ h ∈ H, h * x * h⁻¹ = y := by
  obtain ⟨hN, e, φ, hc⟩ := hnat
  have hne : ∀ z (hz : z ∈ T), z ≠ 1 → Multiplicative.toAdd (φ ⟨z, hz⟩) ≠ 0 := by
    intro z hz hz1 h0
    have h1 : φ ⟨z, hz⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    have h2 : (⟨z, hz⟩ : ↥T) = 1 := φ.injective (by rw [h1, map_one])
    exact hz1 (congrArg Subtype.val h2)
  obtain ⟨A, hA⟩ := exists_sl_mulVec_eq (hne x hx hx1) (hne y hy hy1)
  obtain ⟨hh, hhe⟩ := e.surjective A
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective hh
  have hmem : (h : G) * x * (h : G)⁻¹ ∈ T := by
    have hxH : (⟨x, hTH hx⟩ : ↥H) ∈ T.subgroupOf H := hx
    have := hN.conj_mem _ hxH h
    exact this
  have key := hc h ⟨x, hx⟩ hmem
  rw [hhe, hA] at key
  have h2 : (⟨(h : G) * x * (h : G)⁻¹, hmem⟩ : ↥T) = ⟨y, hy⟩ := by
    apply φ.injective
    rw [key]
    simp
  exact ⟨h, h.2, congrArg Subtype.val h2⟩

theorem NaturalSL.exists_not_normalizes (hnat : NaturalSL T H 2 m) (hTH : T ≤ H)
    {L : Subgroup G} (hLT : L ≤ T) (hL1 : L ≠ ⊥) (hLne : L ≠ T) :
    ∃ h ∈ H, h ∉ Subgroup.normalizer (L : Set G) := by
  obtain ⟨⟨x, hxL⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨y, hyT, hyL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hLT hLne)
  have hy1 : y ≠ 1 := fun h => hyL (h ▸ L.one_mem)
  obtain ⟨h, hh, hxy⟩ := NaturalSL.exists_conj hnat hTH (hLT hxL) hx1' hyT hy1
  refine ⟨h, hh, fun hN => hyL ?_⟩
  have := (Subgroup.mem_normalizer_iff.1 hN x).1 hxL
  rwa [hxy] at this

end Natural

section TI

variable {G : Type} [Group G] [Finite G] {T L : Subgroup G}

theorem normalizer_le_of_isTI (hTI : IsTI T) (hLT : L ≤ T) (hL1 : L ≠ ⊥) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  intro n hn
  have hLn : conjSubgroup n L = L := mem_normalizer_iff_conjSubgroup_eq.1 hn
  have hle : L ≤ T ⊓ conjSubgroup n T := by
    refine le_inf hLT ?_
    rw [← hLn]
    exact conjSubgroup_mono hLT
  have hTn : T ⊓ conjSubgroup n T = T := by
    rcases hTI n with h | h
    · exact absurd (le_bot_iff.1 (h ▸ hle)) hL1
    · exact h
  have hT_le : T ≤ conjSubgroup n T :=
    calc T = T ⊓ conjSubgroup n T := hTn.symm
      _ ≤ conjSubgroup n T := inf_le_right
  have heq : T = conjSubgroup n T :=
    Subgroup.eq_of_le_of_card_ge hT_le (by rw [card_conjSubgroup])
  exact mem_normalizer_of_conjSubgroup_eq heq.symm

end TI

end CFSG.CGT.T75G
