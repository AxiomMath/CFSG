module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RCenter
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (transportAut fixSubTransportEquiv
  transportAut_mul_self)

namespace L34R

theorem not_isL34Type_M12
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M12) (P : Subgroup S) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  intro hL
  have h1 := CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  have h2 : Nat.card (NativeSporadic.Carrier .M12) = 95040 := Sporadic.Mathieu.card_M12
  rw [CatLeaf.card_of_isL34Type hL, Nat.card_congr e.toEquiv, h2] at h1
  norm_num at h1

theorem not_isL34Type_J2
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* NativeSporadic.Carrier .J2)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  intro hL
  set θ : S ≃* ↥J2Cover.P := (e : S ≃* NativeSporadic.J2).trans J2Cover.nativeEquivP
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have h2 := transportAut_mul_self θ hσ2
  have h1 : transportAut θ σ ≠ 1 := by
    intro h1
    apply h.ne_one
    ext x
    have := congrArg (fun φ : MulAut ↥J2Cover.P => θ.symm (φ (θ x))) h1
    simpa [transportAut] using this
  have hcard := QuasithinUnique.Id2519.Tab.j2_fixSub_card (transportAut θ σ) h2 h1
  have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
    ext x
    exact Iff.rfl
  have hc : Nat.card (fixedSubgroup σ) =
      Nat.card (Sporadic.Schreier.fixSub (transportAut θ σ)) := by
    rw [hfix]
    exact Nat.card_congr (fixSubTransportEquiv θ σ).toEquiv
  have hdvd : 20160 ∣ Nat.card (fixedSubgroup σ) := by
    rw [← CatLeaf.card_of_isL34Type hL]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.2.1)
  rw [hc] at hdvd
  rcases hcard with h | h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem hs_card_centralizer
    {T : Type} [Group T] (e : T ≃* NativeSporadic.HS) {t : T} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set T)) = 7680 ∨ Nat.card (centralizer ({t} : Set T)) = 2880 := by
  set θ : T ≃* ↥Sporadic.Schreier.hsP := e.trans Sporadic.Schreier.hsPermEquiv
  set ι : T →* Equiv.Perm (Fin 3850) := Sporadic.Schreier.hsP.subtype.comp θ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp θ.injective
  have hrange : ι.range = Sporadic.Schreier.hsP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr θ.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hτP : ι t ∈ Sporadic.Schreier.hsP := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hcard : Nat.card (centralizer ({t} : Set T)) =
      Nat.card ↥(Sporadic.Schreier.hsP ⊓
        centralizer ({ι t} : Set (Equiv.Perm (Fin 3850)))) := by
    rw [← Subgroup.card_map_of_injective hι,
      Sporadic.SmallOddCore.map_centralizer_eq_inf hι, hrange, Set.image_singleton]
  obtain ⟨-, -, h1, h2, hconj⟩ := Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, hgr⟩ := hconj (ι t) hτP hτ
  have hmap : (Sporadic.Schreier.hsP ⊓
      centralizer ({r} : Set (Equiv.Perm (Fin 3850)))).map (MulAut.conj g).toMonoidHom =
      Sporadic.Schreier.hsP ⊓ centralizer ({g * r * g⁻¹} : Set (Equiv.Perm (Fin 3850))) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, Sporadic.SmallOddCore.map_conj_self hg,
      Sporadic.SmallOddCore.map_conj_centralizer, Set.image_singleton]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hcard, hgr, ← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rcases hr with rfl | rfl
  · exact Or.inl h1
  · exact Or.inr h2

theorem false_of_hs
    {Q : Type} [Group Q] [Finite Q] (hZ : Nat.card (center Q) ≤ 2)
    (e : Q ⧸ center Q ≃* NativeSporadic.Carrier .HS) {P : Subgroup Q}
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) (hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar P)) :
    False := by
  obtain ⟨w, hw2, hw⟩ := exists_involution_dvd_card_centralizer hZ htype hrank
  rcases hs_card_centralizer e hw2 with h | h <;> rw [h] at hw <;> norm_num at hw

end L34R

end CFSG.ComponentClassification.GrSLit
