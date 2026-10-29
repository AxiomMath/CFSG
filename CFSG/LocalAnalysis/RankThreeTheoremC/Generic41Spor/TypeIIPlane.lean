module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_card_inf_eq_prime {q : ℕ} (hq : q.Prime) {U T Z : Subgroup G} {y : G}
    (hU : Nat.card U = q ^ 2) (hZU : Z ≤ U) (hZT : Z ≤ T) (hZ : Nat.card Z = q) (hyU : y ∈ U)
    (hyT : y ∉ T) : Nat.card (U ⊓ T : Subgroup G) = q := by
  have hdvd1 : Nat.card Z ∣ Nat.card (U ⊓ T : Subgroup G) :=
    Subgroup.card_dvd_of_le (le_inf hZU hZT)
  have hdvd2 : Nat.card (U ⊓ T : Subgroup G) ∣ q ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ T ≤ U)
    rwa [hU] at this
  rw [hZ] at hdvd1
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hq).mp hdvd2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hmeq
    rw [hmeq] at hdvd1
    exact hq.one_lt.ne' (Nat.dvd_one.mp hdvd1)
  have hm2 : m ≠ 2 := by
    rintro rfl
    have heq : U ⊓ T = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmeq, hU])
    have hmem : y ∈ U ⊓ T := by
      rw [heq]
      exact hyU
    exact hyT hmem.2
  have hm1 : m = 1 := by omega
  rw [hmeq, hm1, pow_one]

theorem typeII_zpowers_sup_zpowers {q : ℕ} (hq : q.Prime) {a y : G} (ha : a ^ q = 1) (ha1 : a ≠ 1)
    (hy : y ^ q = 1) (hy1 : y ≠ 1) (hcomm : Commute a y) (hya : y ∉ Subgroup.zpowers a) :
    IsElemAbelian q (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) = q ^ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hacard : Nat.card (Subgroup.zpowers a) = q := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have hycard : Nat.card (Subgroup.zpowers y) = q := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy hy1]
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers y : Subgroup G) ∣ q := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
      rwa [hycard] at this
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hqq
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hycard, hqq])
      have hmem : y ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hya hmem.1
  have hcomm' : ∀ (u : Subgroup.zpowers a) (v : Subgroup.zpowers y),
      Commute ((Subgroup.zpowers a).subtype u) ((Subgroup.zpowers y).subtype v) := by
    intro u v
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    show Commute (u : G) (v : G)
    rw [← hi, ← hj]
    exact hcomm.zpow_zpow i j
  let f : (Subgroup.zpowers a) × (Subgroup.zpowers y) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers y).subtype hcomm'
  have hrange : f.range = Subgroup.zpowers a ⊔ Subgroup.zpowers y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨u, v⟩ huv
    have h : (u : G) * v = 1 := huv
    have hmem : (u : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers y :=
      ⟨u.2, by
        rw [eq_inv_of_mul_eq_one_left h]
        exact Subgroup.inv_mem _ v.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hv : (v : G) = 1 := by rw [hmem, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hmem, Subtype.ext hv⟩
  have hcard : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) = q ^ 2 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hacard,
      hycard, sq]
  refine ⟨⟨?_, ?_⟩, hcard⟩
  · have hU : Subgroup.zpowers a ⊔ Subgroup.zpowers y = Subgroup.closure {a, y} := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
        Set.insert_eq]
    rw [hU]
    refine Subgroup.isMulCommutative_closure ?_
    intro u hu v hv _
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact Commute.refl _
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hcomm
    · rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hcomm.symm
    · rw [Set.mem_singleton_iff] at hu hv
      rw [hu, hv]
  · intro u hu
    rw [← hrange] at hu
    obtain ⟨⟨u₁, u₂⟩, rfl⟩ := hu
    have hfu : f (u₁, u₂) = (u₁ : G) * u₂ := rfl
    have hc : Commute (u₁ : G) (u₂ : G) := hcomm' u₁ u₂
    rw [hfu, hc.mul_pow]
    have h1 : (u₁ : G) ^ q = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u₁.2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have h2 : (u₂ : G) ^ q = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u₂.2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
    rw [h1, h2, one_mul]

theorem j4_plane {P : Sylow 11 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hX : ExtraFacts IsJ4Type 11 J4Shape) (hc : PointConfig IsJ4Type G 11 P M x J) :
    IIPlane 11 P x J (u3U0 P x J) := by
  obtain ⟨hel, hcard, hle, hmem, -, hZTcard, -⟩ := typeII_U0_facts hX hc
  obtain ⟨-, -, -, hxJ⟩ := typeII_T_structure hX hc
  have hZU : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hZT : u3ZT P x J ≤ u3T P x J := inf_le_left
  have hxT : x ∉ u3T P x J := fun h => hxJ (h.2)
  exact ⟨hel, hcard, hle, hmem,
    typeII_card_inf_eq_prime hc.prime hcard hZU hZT hZTcard hmem hxT⟩

theorem mcl_plane {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hX : ExtraFacts IsMcLType 5 McLShape) (hc : PointConfig IsMcLType G 5 P M x J) :
    ∃ U : Subgroup G, IIPlane 5 P x J U ∧ ∃ a ∈ U ⊓ u3T P x J, ∃ t ∈ u3T P x J, t * a ≠ a * t := by
  obtain ⟨-, hTexp, hTnab, hxJ⟩ := typeII_T_structure hX hc
  have hp : (5 : ℕ).Prime := hc.prime
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨a, haT, t, htT, hat⟩ : ∃ a ∈ u3T P x J, ∃ t ∈ u3T P x J, t * a ≠ a * t := by
    by_contra hcon
    push Not at hcon
    exact hTnab (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => (hcon a ha b hb).symm)
  have haS : a ∈ u3S P x := haT.1
  have hax : Commute a x := Subgroup.mem_centralizer_singleton_iff.mp haS.2
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hat (by rw [one_mul, mul_one])
  have hap : a ^ 5 = 1 := hTexp a haT
  have hzT : Subgroup.zpowers a ≤ u3T P x J := Subgroup.zpowers_le.mpr haT
  have hxa : x ∉ Subgroup.zpowers a := fun h => hxJ ((hzT h).2)
  obtain ⟨hel, hcard⟩ := typeII_zpowers_sup_zpowers hp hap ha1 hxp hx1 hax hxa
  have hxT : x ∉ u3T P x J := fun h => hxJ (h.2)
  have haU : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hxU : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hZcard : Nat.card (Subgroup.zpowers a) = 5 := by
    haveI : Fact (5 : ℕ).Prime := ⟨hp⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hap ha1]
  refine ⟨Subgroup.zpowers a ⊔ Subgroup.zpowers x, ⟨hel, hcard, ?_, hxU, ?_⟩, a, ⟨haU, haT⟩, t, htT, hat⟩
  · exact sup_le (Subgroup.zpowers_le.mpr haS) (Subgroup.zpowers_le.mpr hxS)
  · exact typeII_card_inf_eq_prime hp hcard le_sup_left hzT hZcard hxU hxT

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
