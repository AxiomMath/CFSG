
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.Quasithin.Background.C1GNC128
public import CFSG.Quasithin.Background.C2Aux
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L238

variable {G : Type} [Group G]

theorem IsAltType.map_equiv {L : Subgroup G} {m : ℕ} (hL : IsAltType L m) (f : G ≃* G) :
    IsAltType (L.map f.toMonoidHom) m := by
  obtain ⟨α, hαs, hαker, β, hβs, hβker, hβeq⟩ := hL
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  have hφ : ∀ x : L, ((φ x : (L.map f.toMonoidHom : Subgroup G)) : G) = f x := fun x => rfl
  have hφsymm : ∀ y : (L.map f.toMonoidHom : Subgroup G), ((φ.symm y : L) : G) = f.symm y := by
    intro y
    apply f.injective
    rw [MulEquiv.apply_symm_apply, ← hφ, MulEquiv.apply_symm_apply]
  have hUmem : ∀ u : G, u ∈ blockU (L.map f.toMonoidHom) ↔ f.symm u ∈ blockU L := by
    intro u
    rw [Lin2.blockU_map_equiv, Subgroup.mem_map_equiv]
  have hZmem : ∀ u : G, u ∈ blockZ (L.map f.toMonoidHom) ↔ f.symm u ∈ blockZ L := by
    intro u
    rw [Lin2.blockZ_map_equiv, Subgroup.mem_map_equiv]
  let ψ : blockU (L.map f.toMonoidHom) →* blockU L :=
    MonoidHom.codRestrict (f.symm.toMonoidHom.comp (blockU (L.map f.toMonoidHom)).subtype)
      (blockU L) fun u => (hUmem u).1 u.2
  have hψ : ∀ u, ((ψ u : blockU L) : G) = f.symm (u : G) := fun u => rfl
  refine ⟨α.comp φ.symm.toMonoidHom, hαs.comp φ.symm.surjective, ?_, β.comp ψ, ?_, ?_, ?_⟩
  · ext ℓ'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαker,
      ← CFSG.pCore_map_iso 2 φ, Subgroup.mem_map_equiv]
    rfl
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    have hfu : f (u : G) ∈ blockU (L.map f.toMonoidHom) :=
      (hUmem _).2 (by rw [MulEquiv.symm_apply_apply]; exact u.2)
    refine ⟨⟨f u, hfu⟩, ?_⟩
    have h1 : ψ ⟨f u, hfu⟩ = u := Subtype.ext (by rw [hψ]; exact MulEquiv.symm_apply_apply f _)
    rw [MonoidHom.comp_apply, h1, hu]
  · ext u'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβker]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψ]
    exact (hZmem _).symm
  · intro ℓ' u' v' h i
    have h' : ((ψ v' : blockU L) : G) = ((φ.symm ℓ' : L) : G) * ((ψ u' : blockU L) : G) *
        ((φ.symm ℓ' : L) : G)⁻¹ := by
      rw [hψ, hψ, hφsymm, h, map_mul, map_mul, InvMemClass.coe_inv, map_inv]
    exact hβeq (φ.symm ℓ') (ψ u') (ψ v') h' i

theorem isChiBlock_conj {X L : Subgroup G} (hL : IsChiBlock X L) {s : G} (hs : s ∈ X) :
    IsChiBlock X (L.map (MulAut.conj s).toMonoidHom) := by
  obtain ⟨hb, htype⟩ := hL
  refine ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem hb hs, ?_⟩
  rcases htype with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj s)⟩
  · exact Or.inr ⟨m, hm, hm3, IsAltType.map_equiv halt (MulAut.conj s)⟩

theorem mem_chiBlocksOutside_conj {X T M L : Subgroup G} (hTX : T ≤ X) (hTM : T ≤ M)
    (hL : L ∈ C1GN.chiBlocksOutside X T M) {s : G} (hs : s ∈ T) :
    L.map (MulAut.conj s).toMonoidHom ∈ C1GN.chiBlocksOutside X T M := by
  obtain ⟨hchi, hJ, hLM⟩ := hL
  refine ⟨isChiBlock_conj hchi (hTX hs), ?_, ?_⟩
  · have hJs : (thompsonJ T).map (MulAut.conj s).toMonoidHom = thompsonJ T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (GammaExtra.normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer hs))
    calc ⁅L.map (MulAut.conj s).toMonoidHom, thompsonJ T⁆
        = ⁅L.map (MulAut.conj s).toMonoidHom, (thompsonJ T).map (MulAut.conj s).toMonoidHom⁆ := by
          rw [hJs]
      _ = (⁅L, thompsonJ T⁆).map (MulAut.conj s).toMonoidHom :=
          (Subgroup.map_commutator _ _ _).symm
      _ = L.map (MulAut.conj s).toMonoidHom := by rw [hJ]
  · intro hle
    apply hLM
    intro x hx
    have h1 : s * x * s⁻¹ ∈ M := hle ⟨x, hx, rfl⟩
    have hsM : s ∈ M := hTM hs
    have h2 := M.mul_mem (M.mul_mem (M.inv_mem hsM) h1) hsM
    simpa [mul_assoc] using h2

end L238

end CFSG.QuasithinUnique
