module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3MCA
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRow
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3MC

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12


theorem center_eq_bot_of_datum {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hd : TightDatum R S t) (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hO2 : ¬ TightInO2 t) (hY : CFSG.Open.IsQuasisimple Y)
    (he : Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) :
    Subgroup.center Y = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := he
  let e : Y ⧸ Subgroup.center Y ≃* ↥NativeSporadic.M12 := e₀
  by_contra hne
  have hQ : CFSG.IsQuasisimple Y := by
    have : Group.IsPerfect Y := ⟨hY.1⟩
    refine ⟨inferInstance, hY.2, e.symm m12a, e.symm m12b, fun h => m12_gens_not_comm ?_⟩
    simpa using congrArg e h
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (NativeSporadic.Carrier .M12)) = 2 := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M12.trans rfl
  have hdvd := E3S3M.natCard_center_dvd hQ e₀
  rw [hM] at hdvd
  have hZ2 : Nat.card ↥(Subgroup.center Y) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
    · exact h
  obtain ⟨⟨c, hcZ⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hc : orderOf c = 2 := by
    have hd2 : orderOf c ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard _ hcZ
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1'
    · exact h
  have hZc : Subgroup.center Y = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZ) ?_
    rw [hZ2, Nat.card_zpowers, hc]
  have htc : t ∉ Subgroup.zpowers c := fun h => hO2
    ⟨Subgroup.center Y, inferInstance, IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one]),
      hZc ▸ h⟩
  set π : Y →* ↥NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
    with hπdef
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = Subgroup.zpowers c := by
    rw [← hZc]
    ext x
    simp [hπdef]
  have hLq : CFSG.Assembly.IsQuasisimple Y := hY
  obtain ⟨-, -, h0⟩ := m12_double_cover_involution_lift_orders hLq hc hZc π hπs hπk
  have ht2 : t ^ 2 = 1 := by rw [← hd.order, pow_orderOf_eq_one]
  have hπt1 : π t ≠ 1 := fun h => htc (hπk ▸ MonoidHom.mem_ker.mpr h)
  have hπt2 : orderOf (π t) = 2 := orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) hπt1
  have hfix4 : fixedCount (π t) = 4 := by
    rcases fixedCount_of_orderOf_eq_two (π t) hπt2 with h | h
    · exact h
    · exfalso
      have h1 := (h0 t hπt2 h).1
      rw [ht2] at h1
      exact hc1' h1.symm
  obtain ⟨r, hr, g, hg, htg⟩ := m12_involution_cover.1 ((π t : ↥NativeSporadic.M12) :
    Equiv.Perm (Fin 12)) (by rw [inv_one, one_mul]; exact (π t).2)
    (by rw [Subgroup.orderOf_coe, hπt2])
  set G : ↥NativeSporadic.M12 := ⟨g, hg⟩ with hG
  have hr1 : r = m12Rep1 := by
    rcases List.mem_pair.1 hr with h | h
    · exact h
    · exfalso
      have hrM := (m12_reps_mem r hr).1
      have hpt : π t = G * ⟨r, hrM⟩ * G⁻¹ := Subtype.ext htg
      rw [hpt, fixedCount_conj] at hfix4
      have h2 : fix12 r = 0 := by
        rw [h]
        exact fix12_rep2
      have h3 : fixedCount ⟨r, hrM⟩ = 0 := h2
      omega
  set π' : Y →* ↥NativeSporadic.M12 := (MulAut.conj G⁻¹).toMonoidHom.comp π with hπ'def
  have hπ's : Function.Surjective π' := (MulAut.conj G⁻¹).surjective.comp hπs
  have hπ'k : π'.ker = Subgroup.zpowers c := by
    rw [← hπk]
    ext x
    simp [hπ'def, MonoidHom.mem_ker]
  obtain ⟨-, h4', h0'⟩ := m12_double_cover_involution_lift_orders hLq hc hZc π' hπ's hπ'k
  have hπ't : ((π' t : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12Rep1 := by
    show g⁻¹ * ((π t : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * g⁻¹⁻¹ = m12Rep1
    rw [htg, hr1]
    group
  exact false_of_rep1 hd hq hc hcZ π' hπ's hπ'k h4' (fun v hv hf => (h0' v hv hf).1) htc hπ't

end CFSG.ClassicalInvolution.Q3.TL4.E3S3MC
