module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax.FiveFL2

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem sup_pPrimeCore_eq_of_oddQuotAction_eq_one {A : Type*} [Group A] [Nontrivial A]
    {M J : Subgroup X} {t : X} (htN : t ∈ normalizer (M : Set X)) (ht2 : t * t = 1)
    (hs1 : TBLit.oddQuotAction M ⟨t, htN⟩ = 1) (hJ : J ≤ M ⊓ centralizer ({t} : Set X))
    (hJc : IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({t} : Set X))))
    (χ : J ⧸ pPrimeCore 2 J ≃* A) [IsSimpleGroup (↥M ⧸ pPrimeCore 2 ↥M)] :
    J ⊔ (pPrimeCore 2 ↥M).map M.subtype = M := by
  classical
  set Y := M ⊓ centralizer ({t} : Set X) with hYdef
  have hYM : Y ≤ M := inf_le_left
  set φ : Y →* M ⧸ pPrimeCore 2 M :=
    (QuotientGroup.mk' (pPrimeCore 2 M)).comp (inclusion hYM) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : TBLit.oddQuotAction M ⟨t, htN⟩ (m : M ⧸ pPrimeCore 2 M) = m := by
      rw [hs1]
      rfl
    rw [TBLit.oddQuotAction_mk] at hq'
    have hc : (m : X)⁻¹ * (t * m * t⁻¹) ∈ coreNOf M := by
      have h2 := QuotientGroup.eq.mp hq'.symm
      exact ⟨_, h2, rfl⟩
    obtain ⟨k, hkO, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf M) ht2
      (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore htN) o).mp ho) hc
    obtain ⟨k', hk', hk'eq⟩ := hkO
    have hkM : k ∈ M := by
      rw [← hk'eq]
      exact k'.2
    have hmkM : (m : X) * k ∈ M := mul_mem m.2 hkM
    refine ⟨⟨(m : X) * k, hmkM, mem_centralizer_singleton_iff.mpr hkc.symm⟩, ?_⟩
    change (((⟨(m : X) * k, hmkM⟩ : M)) : M ⧸ pPrimeCore 2 M) = (m : M ⧸ pPrimeCore 2 M)
    have h1 : (⟨(m : X) * k, hmkM⟩ : M) = m * k' :=
      Subtype.ext (by change (m : X) * k = (m : X) * (k' : X); rw [← hk'eq]; rfl)
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k').mpr hk', mul_one]
  obtain ⟨-, -, hJsn, -, -⟩ := id hJc
  have hsn := hJsn.map hφs
  have hmk : ∀ y : Y, φ y = 1 ↔ (y : X) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    intro y
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨o, ho, hoy⟩
      have : o = inclusion hYM y := Subtype.ext hoy
      rw [← this]
      exact ho
  rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  ·
    exfalso
    have hJO : J ≤ (pPrimeCore 2 ↥M).map M.subtype := by
      intro j hj
      have h1 : φ ⟨j, hJ hj⟩ ∈ (J.subgroupOf Y).map φ := mem_map_of_mem φ (mem_subgroupOf.2 hj)
      rw [h, mem_bot] at h1
      exact (hmk _).1 h1
    have hodd : Odd (Nat.card J) := by
      have h1 : Nat.card J ∣ Nat.card ((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le hJO
      rw [card_map_of_injective M.subtype_injective] at h1
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
    have htop : pPrimeCore 2 J = ⊤ :=
      le_antisymm le_top (le_sSup ⟨normal_top, by
        rw [card_top]
        exact Nat.coprime_two_left.mpr hodd⟩)
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    obtain ⟨x, rfl⟩ := χ.surjective a
    apply ha
    have h1 : x = 1 := by
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
      rw [QuotientGroup.eq_one_iff, htop]
      exact mem_top j
    rw [h1, map_one]
  ·
    apply le_antisymm (sup_le (hJ.trans inf_le_left) (map_subtype_le _))
    intro m hm
    have hmem : ((⟨m, hm⟩ : M) : M ⧸ pPrimeCore 2 M) ∈ (J.subgroupOf Y).map φ := by
      rw [h]
      exact mem_top _
    obtain ⟨y, hy, hym⟩ := mem_map.1 hmem
    have hyJ : (y : X) ∈ J := mem_subgroupOf.1 hy
    have h1 : φ y = ((⟨m, hm⟩ : M) : M ⧸ pPrimeCore 2 M) := hym
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hm' : m = (y : X) * ((inclusion hYM y)⁻¹ * ⟨m, hm⟩ : M) := by
      change m = (y : X) * ((y : X)⁻¹ * m)
      group
    rw [hm']
    exact mul_mem (mem_sup_left hyJ) (mem_sup_right ⟨_, h1, rfl⟩)

end CFSG.ComponentClassification.SolMax.FiveFL2
