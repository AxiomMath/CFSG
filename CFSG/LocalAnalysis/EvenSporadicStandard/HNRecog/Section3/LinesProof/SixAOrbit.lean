module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixABasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixAShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.A8SixOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem lines_sixA_orbit (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hF3 : Fusion3Facts a z)
    (hPic : A8Pictures a z) (hT5 : TableVFacts a z) (h6A : SixAFacts a z) {x : G}
    (hx : x ∈ orb6A a a)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a ((a * x) ^ 3)))) :
    HasSixOrbit φ (derivedOf (Gxy a x)) := by
  obtain ⟨hb, hle, -, hK⟩ := lines_sixA_setup h hF3 hT5 hx
  obtain ⟨t, ht, s, hs, -, hs2, hts, hsB⟩ := lines_sixA_t h hnc hF3 hPic hT5 h6A hx
  obtain ⟨ha2, hb2, hab_comm, -, -, -⟩ := lines_pair h (IsConj.refl a) hb
  have hab2 : (a * (a * x) ^ 3) * (a * (a * x) ^ 3) = 1 := by
    have h1 : (a * (a * x) ^ 3) * (a * (a * x) ^ 3) =
        (a * a) * ((a * x) ^ 3 * (a * x) ^ 3) := by
      calc (a * (a * x) ^ 3) * (a * (a * x) ^ 3)
          = a * ((a * x) ^ 3 * a) * (a * x) ^ 3 := by group
        _ = a * (a * (a * x) ^ 3) * (a * x) ^ 3 := by rw [← hab_comm]
        _ = (a * a) * ((a * x) ^ 3 * (a * x) ^ 3) := by group
    rw [h1, ← pow_two, ha2, ← pow_two, hb2, one_mul]
  let ψ : alternatingGroup (Fin 8) →* G :=
    (derivedOf (Gxy a ((a * x) ^ 3))).subtype.comp φ.toMonoidHom
  have hψ_apply : ∀ g, ψ g = (φ g : G) := fun g => rfl
  have hψ_inj : Function.Injective ψ := fun u v huv => φ.injective (Subtype.ext huv)
  have hψrange : ψ.range = derivedOf (Gxy a ((a * x) ^ 3)) := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact (φ g).2
    · intro y hy
      refine ⟨φ.symm ⟨y, hy⟩, ?_⟩
      show (φ (φ.symm ⟨y, hy⟩) : G) = y
      rw [MulEquiv.apply_symm_apply]
  have hK'H : derivedOf (Gxy a x) ≤ derivedOf (Gxy a ((a * x) ^ 3)) := derivedOf_mono hle
  have hmap : ((derivedOf (Gxy a x)).comap ψ).map ψ = derivedOf (Gxy a x) := by
    rw [Subgroup.map_comap_eq, hψrange, inf_eq_right.mpr hK'H]
  have hS : Nonempty (↥((derivedOf (Gxy a x)).comap ψ) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := lines_isShapeA5_derivedOf hK
    exact ⟨(Subgroup.equivMapOfInjective ((derivedOf (Gxy a x)).comap ψ) ψ hψ_inj).trans
      ((MulEquiv.subgroupCongr hmap).trans e)⟩
  let σ : alternatingGroup (Fin 8) := φ.symm ⟨s, hs⟩
  have hσ : (σ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} :=
    lines_cycleType_of_isConj_z h hnc (IsConj.refl a) hb hPic φ hs hs2 hsB
  have hψσ : ψ σ = s := by
    change ((φ (φ.symm ⟨s, hs⟩) : ↥(derivedOf (Gxy a ((a * x) ^ 3)))) : G) = s
    rw [MulEquiv.apply_symm_apply]
  have hs_eq : s = (a * (a * x) ^ 3) * t := by
    rw [hts, ← mul_assoc, hab2, one_mul]
  have hn : ∀ g ∈ (derivedOf (Gxy a x)).comap ψ,
      σ * g * σ⁻¹ ∈ (derivedOf (Gxy a x)).comap ψ := by
    intro g hg
    rw [Subgroup.mem_comap] at hg
    change ψ (σ * g * σ⁻¹) ∈ derivedOf (Gxy a x)
    have hv : t * ψ g * t⁻¹ ∈ derivedOf (Gxy a x) :=
      conj_mem_derivedOf (H := Gxy a x) ht hg
    have hvH : t * ψ g * t⁻¹ ∈ Gxy a ((a * x) ^ 3) :=
      hle (derivedOf_le (Gxy a x) hv)
    have hva : a * (t * ψ g * t⁻¹) = (t * ψ g * t⁻¹) * a :=
      mem_Gx.mp (mem_Gxy.mp hvH).1
    have hvb : (a * x) ^ 3 * (t * ψ g * t⁻¹) =
        (t * ψ g * t⁻¹) * (a * x) ^ 3 :=
      mem_Gx.mp (mem_Gxy.mp hvH).2
    have hva' : Commute a (t * ψ g * t⁻¹) := hva
    have hvb' : Commute ((a * x) ^ 3) (t * ψ g * t⁻¹) := hvb
    have habv : (a * (a * x) ^ 3) * (t * ψ g * t⁻¹) =
        (t * ψ g * t⁻¹) * (a * (a * x) ^ 3) := hva'.mul_left hvb'
    have hs_conj : s * ψ g * s⁻¹ = t * ψ g * t⁻¹ := by
      rw [hs_eq]
      calc ((a * (a * x) ^ 3) * t) * ψ g * ((a * (a * x) ^ 3) * t)⁻¹
          = (a * (a * x) ^ 3) * (t * ψ g * t⁻¹) * (a * (a * x) ^ 3)⁻¹ := by group
        _ = (t * ψ g * t⁻¹) * (a * (a * x) ^ 3) * (a * (a * x) ^ 3)⁻¹ := by rw [habv]
        _ = t * ψ g * t⁻¹ := by group
    simpa only [map_mul, map_inv, hψσ, hs_conj] using hv
  obtain ⟨i, hi⟩ := linesA8_six_orbit ((derivedOf (Gxy a x)).comap ψ) hS σ hσ hn
  change ∃ k : Fin 8, Set.ncard {j : Fin 8 | ∃ g : alternatingGroup (Fin 8),
    (φ g : G) ∈ derivedOf (Gxy a x) ∧ (g : Equiv.Perm (Fin 8)) k = j} = 6
  exact ⟨i, by simpa [Subgroup.mem_comap, hψ_apply] using hi⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
