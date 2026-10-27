module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZStd

public section

namespace CFSG.ComponentClassification.GrSLit.HeZ

open CFSG Subgroup
open scoped commutatorElement

theorem false_of_card_eq_2520 {S : Type} [Group S]
    (hS : IsL34Type S) {H : Subgroup S} (hH : Nat.card H = 2520) : False := by
  have hsimp : IsSimpleGroup S := HeInner.isSimpleGroup_of_l34 hS
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hS
  obtain ⟨hcard, -, hnoalt⟩ := PSL3Four.facts_of_equiv_S.{0, 0} θ
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hidx : H.index = 8 := by
    have h := card_mul_index H
    rw [hH, hcard] at h
    omega
  have : Finite (S ⧸ H) := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  have : Fintype (S ⧸ H) := Fintype.ofFinite _
  have hcardQ : Fintype.card (S ⧸ H) = 8 := by
    rw [← Nat.card_eq_fintype_card, ← index_eq_card, hidx]
  let e : S ⧸ H ≃ Fin 8 := Fintype.equivFinOfCardEq hcardQ
  let φ : S →* Equiv.Perm (Fin 8) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom S (S ⧸ H))
  have hker : (MulAction.toPermHom S (S ⧸ H)).ker = ⊥ := by
    rw [← normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exfalso
      have hHt : H = ⊤ := eq_top_iff.mpr (h ▸ H.normalCore_le)
      rw [hHt, card_top, hcard] at hH
      norm_num at hH
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply (MonoidHom.ker_eq_bot_iff _).mp hker
    exact (Equiv.permCongrHom e).injective hxy
  have hsign : (Equiv.Perm.sign.comp φ).ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Equiv.Perm.sign.comp φ).ker with h | h
    · exfalso
      have hinj' : Function.Injective (Equiv.Perm.sign.comp φ) :=
        (MonoidHom.ker_eq_bot_iff _).mp h
      have h1 := Nat.card_le_card_of_injective _ hinj'
      rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
      norm_num at h1
    · exact h
  have hle : φ.range ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have hx : x ∈ (Equiv.Perm.sign.comp φ).ker := by rw [hsign]; exact mem_top x
    exact hx
  have hcardA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    rw [Nat.card_eq_fintype_card]
    have h8 : Nat.factorial 8 = 40320 := by decide
    omega
  have hcardR : Nat.card φ.range = 20160 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have heq : φ.range = alternatingGroup (Fin 8) :=
    eq_of_le_of_card_ge hle (by rw [hcardA, hcardR])
  exact (hnoalt (Fin 8) (by simp)).false
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr heq))

theorem eq_of_card_ge {X : Type} [Group X] [Finite X]
    {K P : Subgroup X} (hKt : IsL34Type (↥K ⧸ center ↥K)) (hKp : ⁅K, K⁆ = K)
    (hZ : Nat.card (center ↥K) = 4) (hPK : P ≤ K) (hPp : ⁅P, P⁆ = P) (hP : 20160 ≤ Nat.card P) :
    P = K := by
  have hsimp : IsSimpleGroup (↥K ⧸ center ↥K) := HeInner.isSimpleGroup_of_l34 hKt
  have hcardQ : Nat.card (↥K ⧸ center ↥K) = 20160 := GSThmB.card_of_lieModel_L34 hKt
  set π := QuotientGroup.mk' (center ↥K)
  set P' : Subgroup ↥K := P.subgroupOf K
  have hP' : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have himg : (P'.map π) = ⊤ := by
    apply HeZ.eq_top_of_index_le_four (by rw [hcardQ]; norm_num)
    have h1 : Nat.card (P'.map π) * Nat.card ↥(P' ⊓ π.ker) = Nat.card P' := by
      have := card_eq_card_quotient_mul_card_subgroup ((π.comp P'.subtype).ker)
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp P'.subtype)).toEquiv,
        MonoidHom.range_comp, range_subtype] at this
      rw [this]
      congr 1
      have e : ((π.comp P'.subtype).ker).map P'.subtype = P' ⊓ π.ker := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact mem_inf.mpr ⟨y.2, hy⟩
        · intro hx
          exact ⟨⟨x, (mem_inf.mp hx).1⟩, (mem_inf.mp hx).2, rfl⟩
      rw [← e, card_map_of_injective P'.subtype_injective]
    have h2 : Nat.card ↥(P' ⊓ π.ker) ≤ 4 := by
      rw [← hZ, QuotientGroup.ker_mk']
      exact card_le_of_le inf_le_right
    have h3 := card_mul_index (P'.map π)
    rw [hcardQ] at h3
    have h4 : 5040 ≤ Nat.card (P'.map π) := by
      by_contra hlt
      simp only [not_le] at hlt
      have : Nat.card P' ≤ Nat.card (P'.map π) * 4 := by
        rw [← h1]; exact Nat.mul_le_mul_left _ h2
      omega
    by_contra hgt
    simp only [not_le] at hgt
    have : 5040 * 5 ≤ Nat.card (P'.map π) * (P'.map π).index := Nat.mul_le_mul h4 hgt
    omega
  have hsup : P' ⊔ center ↥K = ⊤ := by
    have h := congrArg (Subgroup.comap π) himg
    rw [comap_top, comap_map_eq, QuotientGroup.ker_mk'] at h
    exact h
  have hKP : (⊤ : Subgroup ↥K) ≤ P' := by
    have hc : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      rw [← map_subtype_inj, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hKp]
    rw [← hc, ← hsup]
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨p, hp, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hx
    obtain ⟨q, hq, w, hw, rfl⟩ := mem_sup_of_normal_right.mp hy
    have hzc := mem_center_iff.mp hz
    have hwc := mem_center_iff.mp hw
    have e : ⁅p * z, q * w⁆ = ⁅p, q⁆ := by
      simp only [commutatorElement_def]
      calc p * z * (q * w) * (p * z)⁻¹ * (q * w)⁻¹
          = p * (z * q) * w * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by group
        _ = p * (q * z) * w * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by rw [hzc q]
        _ = p * q * (z * w) * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by group
        _ = p * q * (w * z) * z⁻¹ * p⁻¹ * w⁻¹ * q⁻¹ := by rw [hzc w]
        _ = p * q * (w * p⁻¹) * w⁻¹ * q⁻¹ := by group
        _ = p * q * (p⁻¹ * w) * w⁻¹ * q⁻¹ := by rw [hwc p⁻¹]
        _ = p * q * p⁻¹ * q⁻¹ := by group
    rw [e]
    have hPP : ⁅P', P'⁆ = P' := by
      rw [← map_subtype_inj, map_commutator]
      simp only [P', subgroupOf_map_subtype, inf_of_le_left hPK]
      exact hPp
    rw [← hPP]
    exact commutator_mem_commutator hp hq
  apply le_antisymm hPK
  intro k hk
  have := hKP (mem_top ⟨k, hk⟩)
  exact mem_subgroupOf.mp this

theorem false_of_simple_card_eq_2520 {X : Type} [Group X]
    [Finite X] {K P : Subgroup X} (hKt : IsL34Type (↥K ⧸ center ↥K))
    (hZ : Nat.card (center ↥K) = 4) (hPK : P ≤ K) (hPs : IsSimpleGroup ↥P)
    (hP : Nat.card P = 2520) : False := by
  set π := QuotientGroup.mk' (center ↥K)
  set P' : Subgroup ↥K := P.subgroupOf K
  have hP' : Nat.card P' = 2520 := by
    rw [← hP]; exact Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hinter : P' ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    let N : Subgroup ↥P := (center ↥K).comap (inclusion hPK)
    have hN : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      simp only [N, mem_comap] at hn ⊢
      rw [map_mul, map_mul, map_inv, mem_center_iff.mp hn (inclusion hPK g), mul_inv_cancel_right]
      exact hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxP : (x : X) ∈ P := mem_subgroupOf.mp (mem_inf.mp hx).1
      have hxN : (⟨x, hxP⟩ : ↥P) ∈ N := by
        simp only [N, mem_comap]
        exact (mem_inf.mp hx).2
      rw [h, mem_bot] at hxN
      have h2 : (x : X) = 1 := congrArg (fun y : ↥P => (y : X)) hxN
      exact (mem_bot).mpr (Subtype.ext h2)
    · exfalso
      have hle : N.map (inclusion hPK) ≤ center ↥K := by
        rintro _ ⟨n, hn, rfl⟩
        exact hn
      have h1 := card_le_of_le hle
      rw [card_map_of_injective (inclusion_injective hPK), h, card_top, hP, hZ] at h1
      norm_num at h1
  have hinj : Function.Injective (π.comp P'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have : (x : ↥K) ∈ P' ⊓ π.ker := mem_inf.mpr ⟨x.2, hx⟩
    rw [hinter, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext this)
  apply false_of_card_eq_2520 hKt (H := (π.comp P'.subtype).range)
  rw [← hP']
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG.ComponentClassification.GrSLit.HeZ
