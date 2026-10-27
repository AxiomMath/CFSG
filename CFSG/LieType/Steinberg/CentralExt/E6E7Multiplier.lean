module

public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Chevalley.AdjointCenter

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

namespace CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

theorem hopfMultiplier_of_isogeny {G A : Type} [Group G] [Group A] [Group.IsPerfect G]
    (θ : G →* A) (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.center G)
    (hZ : Subgroup.center A = ⊥)
    (hsplit : ∀ {E : Type} [Group E] (π : E →* G), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : G →* E, ∀ g, π (σ g) = g) :
    commutator (A ⧸ Subgroup.center A) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (A ⧸ Subgroup.center A) ≃*
        Subgroup.center G) := by
  set q : G →* A ⧸ Subgroup.center A := (QuotientGroup.mk' (Subgroup.center A)).comp θ
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hθ
  have hqker : q.ker = Subgroup.center G := by
    rw [← hker]
    ext g
    simp only [q, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot]
  have : Group.IsPerfect (A ⧸ Subgroup.center A) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ⟨?_⟩⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (A ⧸ Subgroup.center A) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hqker.le
      fun π hπ hcen => hsplit π hπ hcen)
  exact (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans (MulEquiv.subgroupCongr hqker))

theorem center_le_ker_of_surjective {G A : Type} [Group G] [Group A] {θ : G →* A}
    (hθ : Function.Surjective θ) (hZ : Subgroup.center A = ⊥) :
    Subgroup.center G ≤ θ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzA : θ z ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun a => by
    obtain ⟨g, rfl⟩ := hθ a
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
  rw [hZ, Subgroup.mem_bot] at hzA
  exact hzA

section E6

variable {K : Type} [Field K] [Finite K]

theorem e6_hopfMultiplier (hK : 5 ≤ Nat.card K) :
    commutator (AdjointQuotient .E6 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  have hker : (e6Isogeny K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) :=
    le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e6 K) (e6Isogeny_ne_one K))
      (center_le_ker_of_surjective (e6Isogeny_surjective K) center_adjointGroup_eq_bot)
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e6Isogeny K) (e6Isogeny_surjective K) hker
    center_adjointGroup_eq_bot fun π hπ hcen => e6_exists_section_of_central hK hπ hcen
  obtain ⟨hcard, hcyc⟩ := card_center_e6 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E6

section E7

variable {K : Type} [Field K] [Finite K]

theorem e7_hopfMultiplier (hK : 5 ≤ Nat.card K) :
    commutator (AdjointQuotient .E7 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  have hker : (e7Isogeny K).ker = Subgroup.center ↥(e7Data_valid.minGroup K) :=
    le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e7 K) (exists_e7Isogeny_ne_one K))
      (center_le_ker_of_surjective (e7Isogeny_surjective K) center_adjointGroup_eq_bot)
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e7Isogeny K) (e7Isogeny_surjective K) hker
    center_adjointGroup_eq_bot fun π hπ hcen => e7_exists_section_of_central hK hπ hcen
  obtain ⟨hcard, hcyc⟩ := card_center_e7 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E7

end CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
