module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigUniq

public section

namespace CFSG.ComponentClassification.Sol78H

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem mem_coreActionKernel_of_sup_le_centralizer {M J : Subgroup X} {t : X}
    (htN : t ∈ normalizer (M : Set X)) (hJt : J ≤ centralizer ({t} : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) : t ∈ coreActionKernel M := by
  set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
  have hsup' : J ⊔ O = M := hsup
  have hOM : O ≤ M := map_subtype_le _
  have hJM : J ≤ M := le_sup_left.trans hsup'.le
  have hON : ∀ g ∈ normalizer (M : Set X), ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (mem_normalizer_iff.mp (SolMax.le_normalizer_pPrimeCore hg) o).mp ho
  let K : Subgroup X :=
    { carrier := {m | m ∈ M ∧ m⁻¹ * t⁻¹ * m * t ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨mul_mem haM hbM, ?_⟩
        have h1 : b⁻¹ * (a⁻¹ * t⁻¹ * a * t) * b ∈ O := by
          have h2 := hON b⁻¹ (inv_mem (le_normalizer hbM)) _ ha
          rwa [inv_inv] at h2
        have h3 : (a * b)⁻¹ * t⁻¹ * (a * b) * t =
            b⁻¹ * (a⁻¹ * t⁻¹ * a * t) * b * (b⁻¹ * t⁻¹ * b * t) := by group
        rw [h3]
        exact mul_mem h1 hb
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨inv_mem haM, ?_⟩
        have h1 := hON a (le_normalizer haM) _ (inv_mem ha)
        have h2 : a⁻¹⁻¹ * t⁻¹ * a⁻¹ * t = a * (a⁻¹ * t⁻¹ * a * t)⁻¹ * a⁻¹ := by group
        rw [h2]
        exact h1 }
  have hMK : M ≤ K := by
    rw [← hsup']
    refine sup_le (fun j hj => ⟨hJM hj, ?_⟩) (fun o ho => ⟨hOM ho, ?_⟩)
    · have hc : j * t = t * j := mem_centralizer_singleton_iff.mp (hJt hj)
      have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
        calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
          _ = 1 := by rw [hc]; group
      rw [h1]
      exact one_mem _
    · have h1 := hON t⁻¹ (inv_mem htN) o ho
      rw [inv_inv] at h1
      have h2 := mul_mem (inv_mem ho) h1
      have h3 : o⁻¹ * (t⁻¹ * o * t) = o⁻¹ * t⁻¹ * o * t := by group
      rw [h3] at h2
      exact h2
  exact mem_coreActionKernel.mpr ⟨htN, fun m hm => (hMK hm).2⟩

variable [Finite X]

theorem isSolomonMember_of_centralizer_le {Y M T : Subgroup X}
    (hMY : FooteLit.IsTwoComponentIn M Y) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ coreActionKernel M) (hTY : T ≤ Y) (hCY : centralizer (T : Set X) ≤ Y) :
    FooteLit.IsSolomonMember M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMY', hMpc⟩ := hMY
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M Y hMY').mp hMpc).2.2
  have hMsub : (M.subgroupOf Y).IsSubnormal := hMpc.choose_spec.2.1
  set C := centralizer (T : Set X) with hC
  set MT := GSLit.fixedLayer M T with hMT
  have hpc : IsPComponent 2 (MT.subgroupOf C) := by
    have h := GSLit.fixedLayer_isPComponent hMY' hMsub hTY hTM hT2 hMq
    rwa [inf_eq_right.mpr hCY] at h
  have hMTle : MT ≤ M ⊓ C := GSLit.fixedLayer_le_inf M T
  have hMTC : MT ≤ C := hMTle.trans inf_le_right
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hTM hT2
  have hkey : FooteLit.oddCoreIn C ⊔ (M ⊓ C) = FooteLit.oddCoreIn C ⊔ MT := by
    refine le_antisymm (sup_le le_sup_left fun x hx => ?_) (sup_le_sup_left hMTle _)
    have hxM : x ∈ MT ⊔ (pPrimeCore 2 ↥M).map M.subtype := by
      rw [hsup]
      exact hx.1
    have hnorm : MT ≤ normalizer (((pPrimeCore 2 ↥M).map M.subtype : Subgroup X) : Set X) :=
      fun y hy => SolMax.le_normalizer_pPrimeCore (le_normalizer (hMTle hy).1)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hnorm] at hxM
    obtain ⟨a, ha, b, hb, rfl⟩ := hxM
    have hbC : b ∈ C := by
      have hb' : b = a⁻¹ * (a * b) := by group
      rw [hb']
      exact mul_mem (inv_mem (hMTC ha)) hx.2
    have hbO : b ∈ FooteLit.oddCoreIn C :=
      Sol76.oddCoreIn_inf_le hCY ⟨FooteLit.oddCoreIn_le_of_isTwoComponentIn ⟨hMY', hMpc⟩ hb, hbC⟩
    exact mul_mem (mem_sup_right ha) (mem_sup_left hbO)
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hMY' hMpc, T, hT, hT2, hTM, ?_⟩
  rw [hkey, Sol78.oddResidualIn_eq_oPrimeResidualOf]
  change GH74.GLS.IsPCompIn 2 C (GH74.GLS.oPrimeResidualOf 2 (GH74.GLS.pPrimeCoreOf 2 C ⊔ MT))
  rw [Sol78.oPrimeResidualOf_core_sup_eq hMTC hpc]
  exact ⟨hMTC, hpc⟩

end CFSG.ComponentClassification.Sol78H

namespace CFSG.ComponentClassification.SolMax.Sig36

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem eq_of_isPComponent_alt_of_member (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {Y L₁ L₂ : Subgroup X} (h₁ : L₁ ≤ Y) (h₂ : L₂ ≤ Y) (hp₁ : IsPComponent 2 (L₁.subgroupOf Y))
    (hp₂ : IsPComponent 2 (L₂.subgroupOf Y)) (hm₁ : FooteLit.IsSolomonMember L₁)
    (hm₂ : FooteLit.IsSolomonMember L₂)
    (e₁ : Nonempty (L₁ ⧸ pPrimeCore 2 L₁ ≃* alternatingGroup (Fin n)))
    (e₂ : Nonempty (L₂ ⧸ pPrimeCore 2 L₂ ≃* alternatingGroup (Fin n))) : L₁ = L₂ :=
  Sol78H.eq_of_isTwoComponentIn_alt_of_member h13 hmax hS S.nonab S.kProper S.unbal S.notU
    S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 ⟨h₁, hp₁⟩ ⟨h₂, hp₂⟩ hm₁ hm₂ e₁ e₂

theorem le_normalizer_of_isPComponent_alt_of_member (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {Y L : Subgroup X} (hLY : L ≤ Y) (hL : IsPComponent 2 (L.subgroupOf Y))
    (hm : FooteLit.IsSolomonMember L)
    (eL : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) :
    Y ≤ normalizer (L : Set X) := by
  intro c hc
  obtain ⟨hle, hc'⟩ := isPComponent_conj hLY hL hc
  have eL' : Nonempty ((L.map (MulAut.conj c).toMonoidHom) ⧸
      pPrimeCore 2 (L.map (MulAut.conj c).toMonoidHom) ≃* alternatingGroup (Fin n)) := by
    obtain ⟨φ⟩ := eL
    exact ⟨(Sol78.coreQuotCongr
      (L.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)).symm.trans φ⟩
  have hm' : FooteLit.IsSolomonMember (L.map (MulAut.conj c).toMonoidHom) :=
    Sol76.isSolomonMember_map (MulAut.conj c) hm
  exact mem_normalizer_iff_map_conj_eq.mpr
    (S.eq_of_isPComponent_alt_of_member h13 hmax hS hle hLY hc' hL hm' hm eL' eL)

end CFSG.ComponentClassification.SolMax.Sig36
