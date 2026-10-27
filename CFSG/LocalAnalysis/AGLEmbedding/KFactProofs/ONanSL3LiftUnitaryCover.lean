module

public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_mulEquiv_unitarySU_three
    {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3)
    (hz : Subgroup.center K ≠ ⊥) : Nonempty (unitarySU p f F 3 ≃* K) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  let β : unitarySU p f F 3 →* unitaryPSU h 3 := unitaryProj h 3
  let η : K →* unitaryPSU h 3 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hβ : Function.Surjective β := unitaryProj_surjective h 3
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : ∀ z, η z = 1 ↔ z ∈ Subgroup.center K := fun z => by
    change e (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hcen : η.ker ≤ Subgroup.center K := fun z hz => (hηker z).1 hz
  have hsec := SUOdd.statedSU_odd_exists_section_of_central h.card_eq_sq h.one_le
    (n := 3) (by norm_num) (by decide) (fun hh => by simp only [Prod.mk.injEq] at hh; omega)
    (pullbackFst_surjective (β := β) hη) (ker_pullbackFst_le_center (β := β) hcen)
  obtain ⟨α, hα, hαsurj⟩ := SL3Lift.exists_surjective_lift hK hβ hcen hsec
  obtain ⟨⟨z, hzc⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have hz1 : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  obtain ⟨s, hs⟩ := hαsurj z
  have hβker : β.ker = unitaryScalars h 3 := ker_unitaryProj h 3
  have hsker : s ∈ β.ker := by
    rw [MonoidHom.mem_ker, ← hα, hs]
    exact (hηker z).2 hzc
  have hαker : α.ker ≤ unitaryScalars h 3 := fun t ht => by
    rw [← hβker, MonoidHom.mem_ker, ← hα, MonoidHom.mem_ker.1 ht, map_one]
  have hcard : Nat.card (unitaryScalars h 3) ∣ 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact SL3Lift.ker_eq_bot_of_card_dvd_prime Nat.prime_three α hαker hcard
      ⟨s, hβker ▸ hsker, by rw [hs]; exact hz1⟩
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαsurj⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
