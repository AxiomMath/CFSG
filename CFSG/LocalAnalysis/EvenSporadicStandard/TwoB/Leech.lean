module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CentPair

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G]

theorem gmsLeechCentralizer_of_shape {z : G} (hz : orderOf z = 2)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))))
    (hcard : Nat.card (CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 2 ^ 25)
    (hcen : centralizer ((CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :
        Subgroup ↥(centralizer ({z} : Set G))) : Set ↥(centralizer ({z} : Set G))) ≤
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)))
    (e : ↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G)) ≃*
      Carrier .Co1) : CFSG.Monster.GMS.GMSLeechCentralizer z := by
  let e' : ↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G)) ≃* Co1 := e
  refine ⟨hz, hext, hcard, ⟨(MonoidHom.ofClass e').comp (QuotientGroup.mk' _), ?_, ?_⟩, hcen⟩
  · intro y
    obtain ⟨x, rfl⟩ := e'.surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨c, rfl⟩
  · ext c
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

section Co2

theorem centPair_le_centralizer_t (z t : G) : centPair z t ≤ centralizer ({t} : Set G) := by
  intro g hg
  rw [mem_centralizer_iff] at hg
  exact mem_centralizer_singleton_iff.2 (hg t (mem_sup_right (mem_zpowers t))).symm

noncomputable def centralizerEquivCentPair {L : Subgroup G} {t z : G} (hz : z ∈ L)
    (hCt : centralizer ({t} : Set G) = L) :
    centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L) ≃* ↥(centPair z t) :=
  MulEquiv.ofBijective
    ({ toFun := fun y => ⟨(y : L), by
        have hzy : z ∈ centralizer ({((y : L) : G)} : Set G) :=
          mem_centralizer_singleton_iff.2 (congrArg Subtype.val
            (mem_centralizer_singleton_iff.1 y.2).symm)
        have hty : t ∈ centralizer ({((y : L) : G)} : Set G) := by
          have hyL : ((y : L) : G) ∈ centralizer ({t} : Set G) := hCt ▸ (y : L).2
          exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hyL).symm
        have hle : zpowers z ⊔ zpowers t ≤ centralizer ({((y : L) : G)} : Set G) :=
          sup_le (zpowers_le.2 hzy) (zpowers_le.2 hty)
        rw [mem_centralizer_iff]
        intro h hh
        exact mem_centralizer_singleton_iff.1 (hle hh)⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl } :
      centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L) →* ↥(centPair z t))
    ⟨fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h', fun k => by
      have hkL : (k : G) ∈ L := hCt ▸ centPair_le_centralizer_t z t k.2
      have hkz : (k : G) ∈ centralizer ({z} : Set G) := centPair_le_centZ z t k.2
      refine ⟨⟨⟨k, hkL⟩, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hkz)⟩

theorem exists_co2_le_quotient [Finite G] {L : Subgroup G} {t z : G} (hc : CentralPair G L t z)
    (h55 : Conclusion55 G L t z) :
    ∃ S : Subgroup (↥(centZ z) ⧸ CFSG.pCore 2 ↥(centZ z)), Nonempty (S ≃* Carrier .Co2) := by
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  let ι : ↥(centPair z t) →* ↥(centZ z) := Subgroup.inclusion hKC
  let ψ : ↥(centPair z t) →* ↥(centZ z) ⧸ CFSG.pCore 2 ↥(centZ z) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(centZ z))).comp ι
  have hker : ψ.ker = CFSG.pCore 2 ↥(centPair z t) := by
    apply le_antisymm
    · refine le_sSup ⟨?_, ?_⟩
      · have : ψ.ker = (CFSG.pCore 2 ↥(centZ z)).comap ι := by
          ext k
          simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
        rw [this]
        exact Subgroup.Normal.comap inferInstance ι
      · have : ψ.ker = (CFSG.pCore 2 ↥(centZ z)).comap ι := by
          ext k
          simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
        rw [this]
        exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(centZ z))).comap_of_injective ι
          (Subgroup.inclusion_injective hKC)
    · intro k hk
      have h1 : (k : G) ∈ O2In (centPair z t) := ⟨k, hk, rfl⟩
      obtain ⟨c, hc, hck⟩ := h55.o2K_le h1
      rw [MonoidHom.mem_ker]
      have : ι k = c := Subtype.ext hck.symm
      show QuotientGroup.mk' (CFSG.pCore 2 ↥(centZ z)) (ι k) = 1
      rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
  have hCt := h55.centralizer_eq
  let α := centralizerEquivCentPair hc.hz hCt
  have hα : (CFSG.pCore 2 ↥(centralizer ({(⟨z, hc.hz⟩ : ↥L)} : Set ↥L))).map α.toMonoidHom =
      CFSG.pCore 2 ↥(centPair z t) := CFSG.pCore_map_iso 2 α
  obtain ⟨f⟩ := hc.loc.co2
  let q2 := QuotientGroup.congr (CFSG.pCore 2 ↥(centralizer ({(⟨z, hc.hz⟩ : ↥L)} : Set ↥L)))
    (CFSG.pCore 2 ↥(centPair z t)) α hα
  exact ⟨ψ.range, ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (q2.symm.trans f))⟩⟩

end Co2

end CFSG.EvenSporadicStandard.TwoB
