module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X]

theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  have hmap : ∀ (h : X) {C : Subgroup X}, h⁻¹ ∈ normalizer (C : Set X) →
      C.map (MulAut.conj h).toMonoidHom = C := fun h C hC => by
    have h1 := UnbalancedLayer.conjugate_eq_of_mem_normalizer hC
    rwa [conjugate, inv_inv] at h1
  have hsup : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmap g (inv_mem hA), hmap g (inv_mem hB)]
  have hsup' : (A ⊔ B).map (MulAut.conj g⁻¹).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmap g⁻¹ (by rw [inv_inv]; exact hA),
      hmap g⁻¹ (by rw [inv_inv]; exact hB)]
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ (A ⊔ B).map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ hz
    rwa [hsup] at h1
  · intro hz
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * z * g⁻¹) ∈
        (A ⊔ B).map (MulAut.conj g⁻¹).toMonoidHom := mem_map_of_mem _ hz
    rwa [hsup', MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h1

variable [Finite X]

theorem primeResidual_sup_oddCore_eq {C M : Subgroup X} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) :
    (CatalogueBPrimeJoin.primeResidual 2 ↥(M ⊔ oddCoreIn C)).map (M ⊔ oddCoreIn C).subtype =
      M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := M ⊔ oddCoreIn C with hYdef
  apply le_antisymm
  ·
    refine UnbalancedCorr.le_of_primeResidual_eq_top (V := M) (R := oddCoreIn C)
      (map_subtype_le _)
      (CatalogueBPrimeJoin.primeResidual_map_subtype_primeResidual Y)
      (UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hMC hM) ?_
    rw [oddCoreIn, card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := C)
  ·
    have hMres : CatalogueBPrimeJoin.primeResidual 2 ↥(M.subgroupOf C) = ⊤ :=
      CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 2 _ hM
    have hMY : M ≤ Y := le_sup_left
    let e : ↥(M.subgroupOf C) ≃* ↥M := subgroupOfEquivOfLe hMC
    have hMres' : CatalogueBPrimeJoin.primeResidual 2 ↥M = ⊤ := by
      rw [← CatalogueBPrimeJoin.primeResidual_map_equiv 2 e, hMres,
        Subgroup.map_top_of_surjective _ e.surjective]
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ CatalogueBPrimeJoin.primeResidual 2 ↥M := by
      rw [hMres']
      exact mem_top _
    have h2 := CatalogueBPrimeJoin.primeResidual_map_le 2 (inclusion hMY)
      (mem_map_of_mem (inclusion hMY) h1)
    exact ⟨_, h2, rfl⟩

theorem sylow_fixed_core_of_central {a x : X} {J : Subgroup X}
    (hmax : GSMaximalUnbalancingTriple a x J) (hiso : GSIsoAt a J)
    {S : Subgroup X} (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    {z : X} (hz : orderOf z = 2) (hzS : z ∈ S) (hzJ : z ∈ coreActionKernel J)
    (hzC : ∀ s ∈ S, s * z = z * s) (Xz : Subgroup X)
    (hXz : Xz = (pLayer ↥(J ⊓ centralizer ((zpowers z : Subgroup X) : Set X)) 2).map
        (J ⊓ centralizer ((zpowers z : Subgroup X) : Set X)).subtype ⊔
      (pPrimeCore 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))).map
        (normalizer ((zpowers z : Subgroup X) : Set X)).subtype) :
    S ≤ centralizer ({z} : Set X) ⊓ normalizer (Xz : Set X) ∧
      ∃ R : Sylow 2 ↥(centralizer ({z} : Set X) ⊓ normalizer (Xz : Set X)),
        (R : Subgroup _) = S.subgroupOf (centralizer ({z} : Set X) ⊓ normalizer (Xz : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := hmax.1
  have hxH : x ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) := by
    obtain ⟨-, -, hax, -, -, -, -⟩ := gsUnbalancingTriple_iff.mp hU
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hax.symm,
      mem_normalizer_of_gsUnbalancingTriple hU⟩
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card (by
    obtain ⟨-, hx, -⟩ := gsUnbalancingTriple_iff.mp hU
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨h, hh, hhS⟩ := exists_conjugate_le_of_sylow hSsyl (zpowers_le.mpr hxH) hx2
  set y := h⁻¹ * x * h with hydef
  have hyS : y ∈ S := hhS (by
    rw [mem_conjugate_iff, hydef, show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
    exact mem_zpowers x)
  have hUy : GSUnbalancingTriple a y J :=
    gsUnbalancingTriple_conj hU (mem_inf.mp hh).1 (mem_inf.mp hh).2
  have hza : a * z = z * a := (mem_centralizer_singleton_iff.mp (hSH hzS).1).symm
  obtain ⟨M, hIso, -⟩ := hiso y z (hSH hyS) hUy hz hza (hzC y hyS) hzJ
  obtain ⟨hSle, hSsyl'⟩ := (hmax.2 z M hz (mem_centralizer_singleton_iff.mpr hza.symm)
    hIso.1).2 S hSH hSsyl hzS hzC
  obtain ⟨hC, hMa, hsupM⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hIso
  have hMz : M ≤ centralizer ({z} : Set X) := hC.2.2.2.2.2.1
  have hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({z} : Set X))) := hC.2.2.2.2.2.2.1
  set Cz := centralizer ({z} : Set X) with hCzdef
  have hNz : normalizer ((zpowers z : Subgroup X) : Set X) = Cz :=
    UnbalancedCorr.normalizer_zpowers_eq_centralizer hz
  have hCzz : centralizer ((zpowers z : Subgroup X) : Set X) = Cz :=
    UnbalancedLayer.centralizer_zpowers_eq z
  have hXz' : Xz = UnbalancedGS.gsFixedLayer J z ⊔ oddCoreIn Cz := by
    rw [hXz, hNz, hCzz]
    rfl
  have hOM : (pPrimeCore 2 M).map M.subtype ≤ oddCoreIn Cz := by
    have hsub : (M.subgroupOf Cz).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hMpc
      exact hs
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub
    rw [← pPrimeCore_map_subgroupOf 2 M Cz hMz, h1]
    exact map_mono inf_le_right
  have hTM : UnbalancedGS.gsFixedLayer J z ≤ M := hC.gsFixedLayer_le hMa
  have hXM : Xz = M ⊔ oddCoreIn Cz := by
    rw [hXz']
    apply le_antisymm
    · exact sup_le (hTM.trans le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      rw [← hsupM]
      exact sup_le le_sup_left (hOM.trans le_sup_right)
  have heq : Cz ⊓ normalizer (M : Set X) = Cz ⊓ normalizer (Xz : Set X) := by
    apply le_antisymm
    · rintro g ⟨hgC, hgM⟩
      refine mem_inf.mpr ⟨hgC, ?_⟩
      rw [hXM]
      exact mem_normalizer_sup hgM
        (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Cz (pPrimeCore 2 Cz)
          (le_normalizer hgC))
    · rintro g ⟨hgC, hgX⟩
      refine mem_inf.mpr ⟨hgC, ?_⟩
      have : (CatalogueBPrimeJoin.primeResidual 2 ↥Xz).Characteristic :=
        CatalogueBPrimeJoin.primeResidual_characteristic 2 _
      have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Xz
        (CatalogueBPrimeJoin.primeResidual 2 ↥Xz) hgX
      have h2 : (CatalogueBPrimeJoin.primeResidual 2 ↥Xz).map Xz.subtype = M := by
        have h3 := primeResidual_sup_oddCore_eq hMz hMpc
        rwa [← hXM] at h3
      rwa [h2] at h1
  rw [← heq]
  exact ⟨hSle, hSsyl'⟩

end CFSG.ComponentClassification.GSThmB
