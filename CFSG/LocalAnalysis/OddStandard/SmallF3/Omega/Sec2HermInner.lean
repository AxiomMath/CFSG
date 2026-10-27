module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermPerf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate) (E : OGroup (hermForm 4) ≃* OGroup Q)
  (hE : ∀ g, E g ∈ omegaGroup hQ ↔ g ∈ omegaGroup (hermForm_nondegenerate 4))

@[expose] noncomputable def suToOmega : Su F9 3 1 4 →* omegaGroup hQ :=
  (E.toMonoidHom.comp suToOrth).codRestrict (omegaGroup hQ)
    fun s => (hE _).mpr (suToOrth_mem_omega s)

theorem coe_suToOmega (s : Su F9 3 1 4) :
    ((suToOmega hQ E hE s : omegaGroup hQ) : OGroup Q) = E (suToOrth s) := rfl

@[expose] noncomputable def suToProj : Su F9 3 1 4 →* omegaProj hQ :=
  (omegaToProj hQ).comp (suToOmega hQ E hE)

theorem suToProj_eq_one_iff (hπ : E (piOrth (hermForm 4)) = piOrth Q) (s : Su F9 3 1 4) :
    suToProj hQ E hE s = 1 ↔ s = 1 ∨ s = hermNegSU := by
  rw [suToProj, MonoidHom.comp_apply, omegaToProj_eq_one_iff, coe_suToOmega]
  constructor
  · rintro (h | h)
    · exact Or.inl (suToOrth_injective (E.injective (by rw [h, map_one, map_one])))
    · refine Or.inr (suToOrth_injective (E.injective ?_))
      rw [h, suToOrth_hermNegSU, hπ]
  · rintro (rfl | rfl)
    · exact Or.inl (by rw [map_one, map_one])
    · exact Or.inr (by rw [suToOrth_hermNegSU, hπ])

theorem suToProj_comm {y : omegaGroup hQ} (hEy : E (omegaOrth 4) = (y : OGroup Q))
    (s : Su F9 3 1 4) :
    suToProj hQ E hE s * omegaToProj hQ y = omegaToProj hQ y * suToProj hQ E hE s := by
  rw [suToProj, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_suToOmega, ← hEy, ← map_mul, ← map_mul,
    suToOrth_comm_omega]

theorem suToProj_hermOmegaSU {y : omegaGroup hQ} (hEy : E (omegaOrth 4) = (y : OGroup Q)) :
    suToProj hQ E hE hermOmegaSU = omegaToProj hQ y := by
  rw [suToProj, MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  rw [coe_suToOmega, suToOrth_hermOmegaSU, hEy]

theorem exists_conj_suToProj {y : omegaGroup hQ} (hEy : E (omegaOrth 4) = (y : OGroup Q))
    (hπ : E (piOrth (hermForm 4)) = piOrth Q) {g : omegaProj hQ}
    (hg : g ∈ Subgroup.centralizer ({omegaToProj hQ y} : Set (omegaProj hQ)))
    (s : Su F9 3 1 4) : ∃ s' : Su F9 3 1 4,
      g * suToProj hQ E hE s * g⁻¹ = suToProj hQ E hE s' := by
  obtain ⟨γ, rfl⟩ := omegaToProj_surjective hQ g
  have hcomm : omegaToProj hQ (y * γ) = omegaToProj hQ (γ * y) := by
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have hconj := omegaToProj_eq_iff hQ hcomm
  simp only [Subgroup.coe_mul] at hconj
  have hEs : E.symm (y : OGroup Q) = omegaOrth 4 := by rw [← hEy, MulEquiv.symm_apply_apply]
  have hEπ : E.symm (piOrth Q) = piOrth (hermForm 4) := by
    rw [← hπ, MulEquiv.symm_apply_apply]
  have hkey : (γ : OGroup Q) * y * (γ : OGroup Q)⁻¹ = y ∨
      (γ : OGroup Q) * y * (γ : OGroup Q)⁻¹ = piOrth Q * y := by
    rcases hconj with h | h
    · exact Or.inl (by rw [h]; group)
    · exact Or.inr (by rw [h]; group)
  have hω : E.symm (γ : OGroup Q) * omegaOrth 4 * (E.symm (γ : OGroup Q))⁻¹ = omegaOrth 4 ∨
      E.symm (γ : OGroup Q) * omegaOrth 4 * (E.symm (γ : OGroup Q))⁻¹ =
        piOrth (hermForm 4) * omegaOrth 4 := by
    have e : E.symm (γ : OGroup Q) * omegaOrth 4 * (E.symm (γ : OGroup Q))⁻¹ =
        E.symm ((γ : OGroup Q) * y * (γ : OGroup Q)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hEs]
    rcases hkey with h | h
    · exact Or.inl (by rw [e, h, hEs])
    · exact Or.inr (by rw [e, h, map_mul, hEπ, hEs])
  obtain ⟨s', hs'⟩ := conj_suToOrth_mem_range hω s
  refine ⟨s', ?_⟩
  rw [suToProj, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_suToOmega, coe_suToOmega, ← hs',
    map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conj_conjTwo_suToProj {y : omegaGroup hQ} (hEy : E (omegaOrth 4) = (y : OGroup Q)) :
    (omegaToProj hQ ⟨E conjTwo, (hE _).mpr conjTwo_mem_omega⟩)⁻¹ * omegaToProj hQ y *
      omegaToProj hQ ⟨E conjTwo, (hE _).mpr conjTwo_mem_omega⟩ =
        suToProj hQ E hE (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4)) * omegaToProj hQ y := by
  have h := conjTwo_mul_omega
  rw [conjTwo_inv] at h
  rw [← map_inv, ← map_mul, ← map_mul, suToProj, MonoidHom.comp_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  change (E conjTwo)⁻¹ * (y : OGroup Q) * E conjTwo =
    E (suToOrth (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4))) * (y : OGroup Q)
  rw [← hEy, ← map_inv, ← map_mul, ← map_mul, ← map_mul, conjTwo_inv, h]

theorem asc82OmegaPlusProjInner_holds : Asc82OmegaPlusProjInner := by
  intro V _ _ _ Q hQ hdim hsign y hy
  obtain ⟨E, hEy, hEΩ⟩ := exists_frame_iso hQ hdim hsign hy
  have hπ := frame_iso_piOrth E hEy hy
  have hker0 : (suToProj hQ E hEΩ).ker = Subgroup.zpowers hermNegSU := by
    ext s
    rw [MonoidHom.mem_ker, suToProj_eq_one_iff hQ E hEΩ hπ, mem_zpowers_hermNegSU]
  have hkerR : (suToProj hQ E hEΩ).rangeRestrict.ker = Subgroup.zpowers hermNegSU := by
    rw [MonoidHom.ker_rangeRestrict, hker0]
  have hsurj := (suToProj hQ E hEΩ).rangeRestrict_surjective
  obtain ⟨hq, h2⟩ := isQuasisimple_isTwoU43_of_cover _ hsurj hkerR
  refine ⟨(suToProj hQ E hEΩ).range, isComponentIn_of_normal ?_ hq ?_,
    ⟨hermOmegaSU, suToProj_hermOmegaSU hQ E hEΩ hEy⟩, h2,
    (suToProj hQ E hEΩ).rangeRestrict (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4)),
    isI4PlusIn_map_cover _ hsurj hkerR,
    omegaToProj hQ ⟨E conjTwo, (hEΩ _).mpr conjTwo_mem_omega⟩, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (suToProj_comm hQ E hEΩ hEy s)
  · constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨s, hs⟩ := hn
    obtain ⟨s', hs'⟩ := exists_conj_suToProj hQ E hEΩ hEy hπ g.2 s
    exact ⟨s', by rw [← hs', hs]; rfl⟩
  · exact conj_conjTwo_suToProj hQ E hEΩ hEy

end CFSG.OddStandard.SmallF3.Omega
