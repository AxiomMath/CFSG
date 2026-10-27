module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax.FiveFHe

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] [Finite X]

theorem hasOddA_fixedSubgroup_oddQuotAction {A : Type*} [Group A] {M J : Subgroup X} {t : X}
    (htN : t ∈ normalizer (M : Set X)) (ht2 : t * t = 1)
    (hJ : J ≤ M ⊓ centralizer ({t} : Set X))
    (hJc : IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({t} : Set X))))
    (χ : J ⧸ pPrimeCore 2 J ≃* A) :
    HasOddA (fixedSubgroup (TBLit.oddQuotAction M ⟨t, htN⟩)) A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := M ⊓ centralizer ({t} : Set X) with hYdef
  set s := TBLit.oddQuotAction M ⟨t, htN⟩ with hsdef
  have hYM : Y ≤ M := inf_le_left
  set φ₀ : Y →* M ⧸ pPrimeCore 2 M :=
    (QuotientGroup.mk' (pPrimeCore 2 M)).comp (inclusion hYM) with hφ₀
  have hφ₀F : ∀ y : Y, φ₀ y ∈ fixedSubgroup s := by
    intro y
    change s (φ₀ y) = φ₀ y
    have hyt : t * (y : X) * t⁻¹ = y := by
      have h1 := mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2
      rw [← h1, mul_inv_cancel_right]
    rw [hφ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hsdef, TBLit.oddQuotAction_mk]
    congr 1
    exact Subtype.ext hyt
  set φ : Y →* fixedSubgroup s := φ₀.codRestrict (fixedSubgroup s) hφ₀F with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : s (m : M ⧸ pPrimeCore 2 M) = m := hq
    rw [hsdef, TBLit.oddQuotAction_mk] at hq'
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
    apply Subtype.ext
    change (((⟨(m : X) * k, hmkM⟩ : M)) : M ⧸ pPrimeCore 2 M) = (m : M ⧸ pPrimeCore 2 M)
    have h1 : (⟨(m : X) * k, hmkM⟩ : M) = m * k' :=
      Subtype.ext (by change (m : X) * k = (m : X) * (k' : X); rw [← hk'eq]; rfl)
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k').mpr hk', mul_one]
  set J' := J.subgroupOf Y with hJ'def
  obtain ⟨-, -, hJsn, -, -⟩ := id hJc
  have hJp : ⁅J', J'⁆ = J' :=
    Subgroup.isPerfect_iff.1 (CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJc)
  refine ⟨J'.map φ, hJsn.map hφs, by rw [← map_commutator, hJp], ?_⟩
  let eJ : J' ≃* J := subgroupOfEquivOfLe hJ
  let π : J' →* A :=
    χ.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 J)).comp eJ.toMonoidHom)
  have hπs : Function.Surjective π :=
    χ.surjective.comp ((QuotientGroup.mk'_surjective _).comp eJ.surjective)
  let φ' : J' →* J'.map φ := φ.subgroupMap J'
  have hφ's : Function.Surjective φ' := φ.subgroupMap_surjective J'
  set N₀ : Subgroup J := (coreNOf M).comap J.subtype with hN₀
  have hN₀n : N₀.Normal := ⟨fun n hn g => by
    rw [hN₀, mem_comap] at hn ⊢
    have hgM : (g : X) ∈ M := (hJ g.2).1
    have h1 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hgM)) n).mp hn
    simpa using h1⟩
  have hN₀O : N₀ ≤ pPrimeCore 2 J := by
    apply le_sSup
    refine ⟨hN₀n, Nat.coprime_two_left.mpr ?_⟩
    have h1 : Nat.card N₀ ∣ Nat.card (coreNOf M) := by
      rw [← card_map_of_injective J.subtype_injective]
      exact card_dvd_of_le (map_comap_le _ _)
    exact (odd_coreNOf M).of_dvd_nat h1
  have hker : φ'.ker ≤ π.ker := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj ⊢
    have h1 : φ₀ (j : Y) = 1 := congrArg Subtype.val (congrArg Subtype.val hj)
    rw [hφ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : eJ j ∈ N₀ := by
      rw [hN₀, mem_comap]
      exact ⟨_, h1, rfl⟩
    change χ (QuotientGroup.mk' (pPrimeCore 2 J) (eJ j)) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr (hN₀O h2), map_one]
  let ρ : J'.map φ →* A := (QuotientGroup.lift φ'.ker π hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm.toMonoidHom
  have hρφ : ∀ j : J', ρ (φ' j) = π j := by
    intro j
    change QuotientGroup.lift φ'.ker π hker
      ((QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm (φ' j)) = π j
    have he : (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm (φ' j) =
        (j : J' ⧸ φ'.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]
  refine ⟨ρ, fun a => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := hπs a
    exact ⟨φ' j, hρφ j⟩
  ·
    have hle : ρ.ker ≤ π.ker.map φ' := by
      intro x hx
      obtain ⟨j, rfl⟩ := hφ's x
      rw [MonoidHom.mem_ker, hρφ] at hx
      exact mem_map_of_mem φ' hx
    have hπk : Nat.card π.ker ∣ Nat.card (pPrimeCore 2 J) := by
      rw [← card_map_of_injective (f := eJ.toMonoidHom) eJ.injective]
      refine card_dvd_of_le fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hx
      have h1 : χ (QuotientGroup.mk' (pPrimeCore 2 J) (eJ j)) = 1 := hj
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hodd : Odd (Nat.card (pPrimeCore 2 J)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hodd.of_dvd_nat (((card_dvd_of_le hle).trans (card_map_dvd _ _)).trans hπk)

end CFSG.ComponentClassification.SolMax.FiveFHe
