module

public import CFSG.Quasithin.Background.F6Basic
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.GroupTheory

theorem twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded {G : Type*} [Group G] [Finite G]
    {M H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hHM : H ≤ M)
    (hpdvd : p ∣ Nat.card H) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) :
    ∀ g : G, g ∉ M → ¬ CFSG.Quasithin.twoResidual H ≤ CFSG.Quasithin.conjSubgroup M g := by
  have : Fact p.Prime := ⟨hp⟩
  intro g hg hle
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hpdvd
  have hxH : (y : G) ∈ H := y.2
  have hxord : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hyord]
  have hxodd : Odd (orderOf (y : G)) := by
    rw [hxord]
    exact hp.odd_of_ne_two hp2
  have hxres : (y : G) ∈ CFSG.Quasithin.twoResidual H :=
    CFSG.Quasithin.F6.mem_twoResidual_of_odd hxH hxodd
  have hxX : (y : G) ∈ M ⊓ CFSG.Quasithin.conjSubgroup M g :=
    Subgroup.mem_inf.2 ⟨hHM hxH, hle hxres⟩
  have hdvd : p ∣ Nat.card ↥(M ⊓ CFSG.Quasithin.conjSubgroup M g) := by
    have h := Subgroup.orderOf_dvd_natCard (M ⊓ CFSG.Quasithin.conjSubgroup M g) hxX
    rwa [hxord] at h
  have hg' : g⁻¹ ∉ M := fun hh => hg (by simpa using M.inv_mem hh)
  exact hsp.2.2 g⁻¹ hg' (by simpa [CFSG.Quasithin.conjSubgroup] using hdvd)

end CFSG.GroupTheory
