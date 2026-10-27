module

public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem map_gLAPPrimeCore_le (p : ℕ) {H : Type*} [Group H] (σ : H ≃* H) :
    (GLAPPrimeCore p H).map σ.toMonoidHom ≤ GLAPPrimeCore p H := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map σ.toMonoidHom σ.surjective, ?_⟩
  have h : Nat.card (N.map σ.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective σ.injective
  rw [h]
  exact hN.2

theorem map_gLAPPrimeCore (p : ℕ) {H : Type*} [Group H] (σ : H ≃* H) :
    (GLAPPrimeCore p H).map σ.toMonoidHom = GLAPPrimeCore p H := by
  refine le_antisymm (map_gLAPPrimeCore_le p σ) ?_
  have h := Subgroup.map_mono (f := σ.toMonoidHom) (map_gLAPPrimeCore_le p σ.symm)
  rw [Subgroup.map_map] at h
  have hid : σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id H := by
    ext x; simp
  rwa [hid, Subgroup.map_id] at h

variable {G : Type*} [Group G]

@[expose] noncomputable def barAut (p : ℕ) (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ GLAPPrimeCore p ↥L) :=
  quotAutHom (GLAPPrimeCore p ↥L) L.normalizerMonoidHom
    (fun γ => map_gLAPPrimeCore p (L.normalizerMonoidHom γ))

theorem barAut_mk (p : ℕ) (L : Subgroup G) (γ : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    barAut p L γ (QuotientGroup.mk x) =
      QuotientGroup.mk (L.normalizerMonoidHom γ x) :=
  quotAutHom_mk _ _ _ γ x

end CFSG.HardMathSupport.Solomon.LocalBalance
