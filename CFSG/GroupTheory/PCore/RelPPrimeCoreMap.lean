module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open

theorem relPPrimeCore_map_le_of_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) (p : ℕ) :
    (relPPrimeCore p H).map f ≤ relPPrimeCore p (H.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply sSup_le
  rintro N ⟨hNH, hN, hcop⟩
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨Subgroup.map_mono hNH, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNH)]
    rintro _ _ ⟨n, hn, rfl⟩ ⟨k, hk, rfl⟩
    have hnorm := (Subgroup.normal_subgroupOf_iff hNH).mp hN n k hn hk
    exact ⟨k * n * k⁻¹, hnorm, by simp⟩
  · rw [Subgroup.card_map_of_injective hf]
    exact hcop

theorem relPPrimeCore_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (H : Subgroup A) (p : ℕ) :
    relPPrimeCore p (H.map e.toMonoidHom) = (relPPrimeCore p H).map e.toMonoidHom := by
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
    ext x
    simp
  have hmap : ∀ X : Subgroup B, (X.map e.symm.toMonoidHom).map e.toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  apply le_antisymm
  · have h := relPPrimeCore_map_le_of_injective e.symm.toMonoidHom e.symm.injective
      (H.map e.toMonoidHom) p
    have hH : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
      rw [Subgroup.map_map]
      have hcomp' : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
        ext x
        simp
      rw [hcomp', Subgroup.map_id]
    rw [hH] at h
    calc relPPrimeCore p (H.map e.toMonoidHom)
        = ((relPPrimeCore p (H.map e.toMonoidHom)).map e.symm.toMonoidHom).map
            e.toMonoidHom := (hmap _).symm
      _ ≤ (relPPrimeCore p H).map e.toMonoidHom := Subgroup.map_mono h
  · exact relPPrimeCore_map_le_of_injective e.toMonoidHom e.injective H p

end CFSG.Open
