module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem false_of_fourPoint_mem_coreActionKernel_conj (S : Sig36 X t J 9 e E D)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) {M : Subgroup X}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    {f g : X} (hfM : f ∈ M) (hf2 : f * f = 1)
    (hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4)
    (hft : g * f * g⁻¹ * t = t * (g * f * g⁻¹))
    (hfK : g * f * g⁻¹ ∈ UnbalancedLayer.coreActionKernel J) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f' := g * f * g⁻¹ with hf'def
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [show (⟨1, le_normalizer hfM⟩ : ↥(normalizer (M : Set X))) = 1 from rfl, map_one,
      Perm.support_one, Finset.card_empty] at hf4
    omega
  have hf'2 : f' * f' = 1 := by
    rw [hf'def]
    calc g * f * g⁻¹ * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have hf'1 : f' ≠ 1 := fun h => hf1 (by
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [hf'def, mul_assoc] using this)
  have hf'o : orderOf f' = 2 := orderOf_eq_prime (by rw [sq]; exact hf'2) hf'1
  have hu2 : IsPGroup 2 (zpowers f') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf'o, pow_one])
  have hut : f' ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hft
  obtain ⟨-, -, hJuC, ⟨eJu⟩⟩ := S.fixedLayer_facts hu2 hut hfK
  set Ju := GSLit.fixedLayer J (zpowers f') with hJudef
  set Y := centralizer ({f'} : Set X) with hYdef
  have hK := UnbalancedCorr.isKGroupCat_of_ne_top S.kProper
    (centralizer_ne_top_of_ne_one S.nonab hf'1)
  have htY : t ∈ Y := mem_centralizer_singleton_iff.mpr hft.symm
  have hto : orderOf t = 2 := S.pair.1.1
  have hcen : centralizer ((zpowers t ⊔ zpowers f' : Subgroup X) : Set X) =
      Y ⊓ centralizer ({t} : Set X) := by
    ext y
    simp only [mem_inf, mem_centralizer_singleton_iff, hYdef]
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · exact ((mem_centralizer_iff.mp hy) f' (mem_sup_right (mem_zpowers f'))).symm
      · exact ((mem_centralizer_iff.mp hy) t (mem_sup_left (mem_zpowers t))).symm
    · rintro ⟨h1, h2⟩
      rw [mem_centralizer_iff]
      intro z hz
      have hle : zpowers t ⊔ zpowers f' ≤ centralizer ({y} : Set X) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h2.symm))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h1.symm))
      exact (mem_centralizer_singleton_iff.mp (hle hz))
  obtain ⟨hJuY, hJupc⟩ := hJuC
  rw [hcen] at hJuY hJupc
  obtain ⟨L, hLY, hLpc, -, -, htype⟩ :=
    pump_type_in hPump hK htY hto hJuY hJupc (by decide) (by norm_num) eJu
  obtain ⟨m, hm, hm9, ⟨θL⟩⟩ : ∃ m : ℕ, Odd m ∧ 9 ≤ m ∧
      Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* alternatingGroup (Fin m)) := by
    rcases htype with ⟨-, ⟨m, hm, hm9, hL⟩ | ⟨h79, -⟩⟩ | ⟨-, hL⟩
    · exact ⟨m, hm, hm9, hL⟩
    · omega
    · exact ⟨9, by decide, le_rfl, hL⟩
  have hCz : centralizer ((zpowers f' : Subgroup X) : Set X) = Y := centralizer_zpowers_eq' f'
  have hZ : Open.fusionZStar ↥L = pPrimeCore 2 ↥L := by
    have hLY' : L ≤ centralizer ((zpowers f' : Subgroup X) : Set X) := by rw [hCz]; exact hLY
    have hLpc' : IsPComponent 2 (L.subgroupOf (centralizer ((zpowers f' : Subgroup X) : Set X))) :=
      by rw [hCz]; exact hLpc
    exact hN1 X S.nonab S.kProper S.unbal S.notU (zpowers f') m L
      (fun h => hf'1 (zpowers_eq_bot.mp h)) hu2 hm hm9 hLY' hLpc' ⟨θL⟩
  let θL' : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).symm.trans θL
  have hm9' : m ≤ 9 := S.pair.2.2.2.1 f' L m ⟨hf'o, hLY, hLpc, ⟨θL'⟩⟩ hm
  obtain rfl : m = 9 := le_antisymm hm9' hm9
  have hCY : Y.map (MulAut.conj g⁻¹).toMonoidHom = centralizer ({f} : Set X) := by
    ext y
    simp only [hYdef, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hf : f = g⁻¹ * f' * g := by rw [hf'def]; group
      rw [hf]
      calc g⁻¹ * z * g * (g⁻¹ * f' * g) = g⁻¹ * (z * f') * g := by group
        _ = g⁻¹ * (f' * z) * g := by rw [hz]
        _ = g⁻¹ * f' * g * (g⁻¹ * z * g) := by group
    · intro hy
      refine ⟨g * y * g⁻¹, ?_, by group⟩
      rw [hf'def]
      calc g * y * g⁻¹ * (g * f * g⁻¹) = g * (y * f) * g⁻¹ := by group
        _ = g * (f * y) * g⁻¹ := by rw [hy]
        _ = g * f * g⁻¹ * (g * y * g⁻¹) := by group
  have h1 := isPComponent_map_conj hLY hLpc g⁻¹
  rw [hCY] at h1
  have hKle : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({f} : Set X) := by
    rw [← hCY]
    exact map_mono hLY
  exact (hNoA9 f hfM hf2 hf4 _ hKle h1).false
    ((Sol78.coreQuotCongr (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm.trans θL')

end Sig36

end CFSG.ComponentClassification.SolMax
