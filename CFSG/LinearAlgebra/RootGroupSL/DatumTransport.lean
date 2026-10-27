module

public import CFSG.LinearAlgebra.RootGroupSL.DatumTransportCongr
public import CFSG.LinearAlgebra.RootGroupSL.DatumLin
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open

variable {k E V V' : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

variable [Module.Finite k V] [Module.Finite k V'] [Module.Finite k E]

private lemma datumElt_proof_irrel (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h1 h2 : ∀ t, π (ι t) = 0) (t : E) :
    datumElt ι π h1 t = datumElt ι π h2 t := by
  apply Subtype.ext
  ext v
  rfl

private lemma datumRoot_proof_irrel (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h1 h2 : ∀ t, π (ι t) = 0) :
    datumRoot ι π h1 = datumRoot ι π h2 := by
  unfold datumRoot
  have hset : Set.range (datumElt ι π h1) = Set.range (datumElt ι π h2) := by
    ext g
    constructor
    · intro hg
      obtain ⟨t, ht⟩ := hg
      exact ⟨t, by rw [← datumElt_proof_irrel ι π h1 h2 t, ht]⟩
    · intro hg
      obtain ⟨t, ht⟩ := hg
      exact ⟨t, by rw [datumElt_proof_irrel ι π h1 h2 t, ht]⟩
  rw [hset]

private lemma datumRoot_congr {ι1 ι2 : E →ₗ[k] V} {π1 π2 : V →ₗ[k] E}
    (h1 : ∀ t, π1 (ι1 t) = 0) (h2 : ∀ t, π2 (ι2 t) = 0)
    (hι : ι1 = ι2) (hπ : π1 = π2) :
    datumRoot ι1 π1 h1 = datumRoot ι2 π2 h2 := by
  subst hι
  subst hπ
  exact datumRoot_proof_irrel _ _ h1 h2

variable {X : Type} [AddCommGroup X] [Module k X] [Module.Finite k X]

private lemma mem_flagW_iff (v : DSpace E X) :
    v ∈ flagW k E X ↔ v.2.1 = 0 ∧ v.2.2 = 0 := by
  simp [flagW, Prod.ext_iff]

private lemma mem_flagK_iff (v : DSpace E X) : v ∈ flagK k E X ↔ v.2.2 = 0 := by
  simp [flagK]

private lemma range_stdIota_eq_flagW :
    LinearMap.range (stdIota k E X) = flagW k E X := by
  ext v
  rw [LinearMap.mem_range, mem_flagW_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨v.1, ?_⟩
    rw [stdIota_apply]
    exact Prod.ext rfl (Prod.ext h1.symm h2.symm)

private lemma datumElt_std_eq_rootElt (h : ∀ t, stdPi k E X (stdIota k E X t) = 0) (t : E) :
    datumElt (stdIota k E X) (stdPi k E X) h t = rootElt k X t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, x, b⟩ := v
  simp [datumElt_apply, rootElt, rootEquiv, shearE, stdIota, stdPi, LinearMap.mulLeft_apply]

theorem datumQ_std : datumQ (stdIota k E X) (stdPi k E X) = QK k E X := by
  ext g
  constructor
  · intro hg
    obtain ⟨h1, h2, h3⟩ := hg
    rw [mem_QK_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rw [mem_flagW_iff] at hv
      have hv' : v = stdIota k E X v.1 := by
        ext <;> simp [stdIota, hv.1, hv.2]
      rw [hv']
      exact h1 v.1
    · intro v hv
      rw [mem_flagK_iff] at hv
      have hπv : stdPi k E X v = 0 := by simpa [stdPi] using hv
      have h := h2 v hπv
      rwa [range_stdIota_eq_flagW] at h
    · intro v
      have h := h3 v
      rw [mem_flagK_iff]
      simpa [stdPi] using h
  · intro hg
    rw [mem_QK_iff] at hg
    obtain ⟨hW, hK, hM⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact hW (stdIota k E X t) (by rw [← range_stdIota_eq_flagW]; exact ⟨t, rfl⟩)
    · intro v hv
      have hvK : v ∈ flagK k E X := by rw [mem_flagK_iff]; simpa [stdPi] using hv
      have h := hK v hvK
      rw [mem_flagW_iff] at h
      rwa [range_stdIota_eq_flagW, mem_flagW_iff]
    · intro v
      have h := hM v
      rw [mem_flagK_iff] at h
      simpa [stdPi] using h

theorem datumRoot_std (h : ∀ t, stdPi k E X (stdIota k E X t) = 0) :
    datumRoot (stdIota k E X) (stdPi k E X) h = rootSL k E X := by
  ext g
  rw [mem_datumRoot_iff, mem_rootSL_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← ht, datumElt_std_eq_rootElt]
    rfl
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    rw [datumElt_std_eq_rootElt]
    exact ht.symm

variable [Finite k] [Finite E] [CharP k 2]

private lemma map_pCoreOf_equiv {G G' : Type*} [Group G] [Group G'] (p : ℕ) (e : G ≃* G')
    (H : Subgroup G) :
    (pCoreOf p H).map e.toMonoidHom = pCoreOf p (H.map e.toMonoidHom) := by
  change ((CFSG.pCore p H).map H.subtype).map e.toMonoidHom =
    (CFSG.pCore p (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype
  let ee := Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
  have hcomp : e.toMonoidHom.comp H.subtype =
      (H.map e.toMonoidHom).subtype.comp ee.toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso p ee]

private lemma map_injective_of_injective {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Function.Injective f) :
    Function.Injective (Subgroup.map f) := by
  intro H K h
  ext x
  constructor
  · intro hx
    have hx' : f x ∈ K.map f := by rw [← h]; exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : x = y := (hf hyx).symm
    rwa [hxy]
  · intro hx
    have hx' : f x ∈ H.map f := by rw [h]; exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : x = y := (hf hyx).symm
    rwa [hxy]

theorem pCoreOf_normalizer_datumRoot (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0)
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hV : 2 * Module.finrank k E < Module.finrank k V) :
    pCoreOf 2 (Subgroup.normalizer (datumRoot ι π h : Set (SpecialLinearGroup k V))) =
      datumQ ι π := by
  obtain ⟨X', hX'AC, hX'Mod, hX'Fin, L, hLι, hLπ⟩ := exists_datumLin ι π h hι hπ
  letI : AddCommGroup X' := hX'AC
  letI : Module k X' := hX'Mod
  letI : Module.Finite k X' := hX'Fin
  have hιL : L.toLinearMap ∘ₗ ι = stdIota k E X' := by
    apply LinearMap.ext
    intro t
    rw [stdIota_apply]
    exact hLι t
  have hπL : π ∘ₗ L.symm.toLinearMap = stdPi k E X' := by
    apply LinearMap.ext
    intro v
    show π (L.symm v) = v.2.2
    have h := (hLπ (L.symm v)).symm
    simpa [LinearEquiv.apply_symm_apply] using h
  have h' : ∀ t, (π ∘ₗ L.symm.toLinearMap) ((L.toLinearMap ∘ₗ ι) t) = 0 := by
    intro t
    show π (L.symm (L (ι t))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact h t
  have hstd : ∀ t, stdPi k E X' (stdIota k E X' t) = 0 := fun t => stdPi_stdIota t
  have hfin : Module.finrank k V = 2 * Module.finrank k E + Module.finrank k X' := by
    rw [L.finrank_eq]
    change Module.finrank k (E × X' × E) = 2 * Module.finrank k E + Module.finrank k X'
    rw [Module.finrank_prod, Module.finrank_prod]
    ring
  have hX'pos : 0 < Module.finrank k X' := by omega
  have hroot : (datumRoot ι π h).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      rootSL k E X' := by
    rw [map_datumRoot_congr L ι π h h', datumRoot_congr h' hstd hιL hπL]
    exact datumRoot_std hstd
  have hQ : (datumQ ι π).map (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      QK k E X' := by
    rw [map_datumQ_congr L ι π, hιL, hπL]
    exact datumQ_std
  have hnorm : (Subgroup.normalizer (datumRoot ι π h : Set (SpecialLinearGroup k V))).map
        (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom =
      Subgroup.normalizer (rootSL k E X' : Set (SpecialLinearGroup k (DSpace E X'))) := by
    rw [Subgroup.map_equiv_normalizer_eq, hroot]
  have hp : (pCoreOf 2 (Subgroup.normalizer
        (datumRoot ι π h : Set (SpecialLinearGroup k V)))).map
        (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom = QK k E X' := by
    rw [map_pCoreOf_equiv, hnorm]
    exact pCoreOf_normalizer_rootSL hX'pos
  apply map_injective_of_injective
    (f := (SpecialLinearGroup.congr_linearEquiv L).toMonoidHom)
    (SpecialLinearGroup.congr_linearEquiv L).injective
  rw [hp, hQ]

end CFSG.LinearAlgebra.RootGroupSL
