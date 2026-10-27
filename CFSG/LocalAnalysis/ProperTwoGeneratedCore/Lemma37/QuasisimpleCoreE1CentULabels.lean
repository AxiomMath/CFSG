module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUPhiU

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv CFSG.Sporadic.Th.Max3

theorem cycleType_permNine {σ : Perm (Fin 4)} {τ : Perm (Fin 5)} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) {k : ℕ} (hk : σ.support.card + τ.support.card = 2 * k) :
    (permNine (σ, τ)).cycleType = Multiset.replicate k 2 := by
  have h1 : permNine (σ, τ) * permNine (σ, τ) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hσ, hτ, Prod.mk_one_one, map_one]
  rw [cycleType_eq_replicate h1, card_support_permNine, hk]
  congr 1
  omega

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem rho5_of_mem_of_mul_self {l : QuasiQuotient u} (hl : l ∈ L)
    (hll : l * l = quasiCentral u) :
    d.rho5 l * d.rho5 l = 1 ∧ d.rho5 l ≠ 1 ∧ Perm.sign (d.rho5 l) = 1 := by
  refine ⟨?_, fun h1 => ?_, d.sign_rho5_of_mem_sup (Subgroup.mem_sup_left hl)⟩
  · rw [← map_mul, hll, d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer]
  · rcases d.eq_of_mem_of_mem_centralizer hl (d.mem_centralizer_of_rho5_eq_one h1) with rfl | rfl
    · rw [mul_one] at hll
      exact d.quasiCentral_ne_one hll.symm
    · rw [d.quasiCentral_mul_self] at hll
      exact d.quasiCentral_ne_one hll.symm

theorem ne_of_mul_self_eq {k : QuasiQuotient u} (hkk : k * k = quasiCentral u) :
    k ≠ 1 ∧ k ≠ quasiCentral u := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, mul_one] at hkk
    exact d.quasiCentral_ne_one hkk.symm
  · rw [h, d.quasiCentral_mul_self] at hkk
    exact d.quasiCentral_ne_one hkk.symm

theorem exists_toCentralizer_eq (s : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
    {g : J} (hg : (g : J ⧸ Subgroup.center J) = s) :
    ∃ hgX : g ∈ quasiNormalizer u, d.toCentralizer ⟨g, hgX⟩ = s := by
  have hgX : g ∈ quasiNormalizer u := (d.starLift.toEscapingLift.mem_quasiNormalizer_iff
    d.setting).mpr (by rw [hg]; exact Subgroup.mem_centralizer_singleton_iff.mp s.2)
  exact ⟨hgX, Subtype.ext hg⟩

theorem cycleType_phiU_of_genuine {s : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}}
    (hs1 : s ≠ 1) (hs : CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J)) :
    ((d.phiU s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  obtain ⟨g, hgs, hgg⟩ := hs
  obtain ⟨hgX, rfl⟩ := d.exists_toCentralizer_eq s hgs
  have hg1 : g ≠ 1 := fun h => hs1 (d.toCentralizer_eq_one_iff.mpr (Or.inl h))
  have hge : g ≠ centralElt J := fun h => hs1 (d.toCentralizer_eq_one_iff.mpr (Or.inr h))
  obtain ⟨hw1, hwe⟩ := d.quasiMk_ne_of_involution (w := ⟨g, hgX⟩) (Subtype.ext hgg) hg1 hge
  have hw2 : quasiMk u ⟨g, hgX⟩ * quasiMk u ⟨g, hgX⟩ = 1 := by
    rw [← map_mul, show (⟨g, hgX⟩ : quasiNormalizer u) * ⟨g, hgX⟩ = 1 from Subtype.ext hgg,
      map_one]
  obtain ⟨l, hl, k, hk, hlk, hll, hkk⟩ := d.exists_mul_eq_of_involution hw2 hw1 hwe
  rw [coe_phiU, rho4C, rho5C, liftC_toCentralizer, liftC_toCentralizer, ← hlk, map_mul, map_mul,
    d.rho4_of_mem hl, one_mul, d.rho5_of_mem_centralizer hk, mul_one]
  obtain ⟨hk1, hke⟩ := d.ne_of_mul_self_eq hkk
  obtain ⟨h4, h4'⟩ := d.rho4_fpf_of_mem_centralizer hk hk1 hke
  obtain ⟨h5, h5', h5''⟩ := d.rho5_of_mem_of_mul_self hl hll
  exact cycleType_permNine h4 h5 (k := 4) (by
    rw [perm4_card_support_of_fpf _ h4 h4', perm5_card_support_of_even _ h5'' h5 h5'])

theorem cycleType_phiU_of_not_genuine {s : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}}
    (hss : s * s = 1) (hs : ¬ CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J)) :
    ((d.phiU s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2} := by
  have hKn := d.oneComponent.centralizer_normal
  obtain ⟨g, hgs⟩ := QuotientGroup.mk_surjective (s : J ⧸ Subgroup.center J)
  obtain ⟨hgX, rfl⟩ := d.exists_toCentralizer_eq s hgs
  have hgg : g * g = centralElt J := by
    have hZ : g * g ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact congrArg Subtype.val hss
    rcases d.setting.mem_center_iff.mp hZ with h | h
    · exact absurd ⟨g, rfl, h⟩ hs
    · exact h
  set w := quasiMk u ⟨g, hgX⟩ with hw
  have hw2 : w * w = quasiCentral u := by
    rw [hw, ← map_mul, ← d.quasiMk_centralElt]
    exact congrArg (quasiMk u) (Subtype.ext hgg)
  have h4sq : d.rho4 w * d.rho4 w = 1 := by
    rw [← map_mul, hw2, d.rho4_of_mem d.quasiCentral_mem]
  have h5sq : d.rho5 w * d.rho5 w = 1 := by
    rw [← map_mul, hw2, d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer]
  rw [coe_phiU, rho4C, rho5C, liftC_toCentralizer, liftC_toCentralizer]
  refine cycleType_permNine h4sq h5sq (k := 2) ?_
  by_cases hLK : w ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))
  · obtain ⟨l, hl, k, hk, hlk⟩ := Subgroup.mem_sup_of_normal_right.mp hLK
    have hcl : l * k = k * l := Subgroup.mem_centralizer_iff.mp hk l hl
    have hsq : l * l * (k * k) = quasiCentral u := by
      rw [← hw2, ← hlk]
      calc l * l * (k * k) = l * (l * k) * k := by group
        _ = l * (k * l) * k := by rw [hcl]
        _ = l * k * (l * k) := by group
    have hllK : l * l ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
      rw [show l * l = quasiCentral u * (k * k)⁻¹ by rw [← hsq]; group]
      exact Subgroup.mul_mem _ d.quasiCentral_mem_centralizer
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ hk hk))
    rw [← hlk, map_mul, map_mul, d.rho4_of_mem hl, one_mul, d.rho5_of_mem_centralizer hk, mul_one]
    rcases d.eq_of_mem_of_mem_centralizer (L.mul_mem hl hl) hllK with hll | hll
    ·
      rw [hll, one_mul] at hsq
      have h5 : d.rho5 l = 1 := by
        rcases d.eq_of_mem_of_mul_self hl hll with rfl | rfl
        · exact map_one _
        · exact d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer
      obtain ⟨hk1, hke⟩ := d.ne_of_mul_self_eq hsq
      obtain ⟨h4, h4'⟩ := d.rho4_fpf_of_mem_centralizer hk hk1 hke
      rw [h5, perm4_card_support_of_fpf _ h4 h4', Perm.support_one, Finset.card_empty]
    ·
      rw [hll] at hsq
      have hkk : k * k = 1 := by
        calc k * k = quasiCentral u * quasiCentral u * (k * k) := by
              rw [d.quasiCentral_mul_self, one_mul]
          _ = quasiCentral u * (quasiCentral u * (k * k)) := by group
          _ = 1 := by rw [hsq, d.quasiCentral_mul_self]
      have h4 : d.rho4 k = 1 := by
        rcases d.eq_of_mem_centralizer_of_mul_self hk hkk with rfl | rfl
        · exact map_one _
        · exact d.rho4_of_mem d.quasiCentral_mem
      obtain ⟨h5, h5', h5''⟩ := d.rho5_of_mem_of_mul_self hl hll
      rw [h4, perm5_card_support_of_even _ h5'' h5 h5', Perm.support_one, Finset.card_empty]
  ·
    have h5 : Perm.sign (d.rho5 w) = -1 :=
      (Int.units_eq_one_or _).resolve_left fun h => hLK (d.mem_sup_iff_sign.mpr h)
    have h4 : Perm.sign (d.rho4 w) = -1 := by rw [d.sign_rho4_eq, h5]
    rw [perm4_card_support_of_odd _ h4sq h4, perm5_card_support_of_odd _ h5 h5sq]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
