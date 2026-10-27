module

public import CFSG.Goldschmidt.Basic
import CFSG.LocalAnalysis.ComponentClassification.OddCore
import CFSG.Adapters.Involutions
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

section OddCore

variable {G : Type*} [Group G]

theorem mem_map_conj {K : Subgroup G} {h y : G} :
    y ∈ K.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * y * h ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hy
    exact ⟨_, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_normalizer_oddCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreOf H : Set G) := by
  have heq : (oddCoreOf H).subgroupOf H = goldschmidtOddCore H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hn : ((oddCoreOf H).subgroupOf H).Normal := by
    rw [heq]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreOf_le H)).mp hn

theorem le_oddCoreOf {H N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ oddCoreOf H := by
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ goldschmidtOddCore H :=
    le_sSup ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN, hodd'⟩
  have hm := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at hm

theorem odd_card_oddCoreOf [Finite G] (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card H

theorem eq_one_of_pow_two_of_odd [Finite G] {K : Subgroup G} (hK : Odd (Nat.card K)) {x : G}
    (hx : x ∈ K) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem le_normalizer_oddCoreOf_of_le_normalizer [Finite G] {Q H : Subgroup G}
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer (oddCoreOf Q : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcard : Nat.card ((oddCoreOf Q).map (MulAut.conj h).toMonoidHom) =
      Nat.card (oddCoreOf Q) := Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hle : (oddCoreOf Q).map (MulAut.conj h).toMonoidHom ≤ oddCoreOf Q := by
    refine le_oddCoreOf ?_ (fun q hq => ?_) (hcard ▸ odd_card_oddCoreOf Q)
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHQ hh) x).mp (oddCoreOf_le Q hx)
    · have hq' : h⁻¹ * q * h ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hh)) q).mp hq
        simpa using this
      have hN := Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf Q hq')
      refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
      rw [mem_map_conj, mem_map_conj, hN]
      constructor <;> intro h' <;> convert h' using 1 <;> group

  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem exists_mul_of_eq_oddCoreOf_sup {Q B : Subgroup G} (hQ : Q = oddCoreOf Q ⊔ B)
    {q : G} (hq : q ∈ Q) : ∃ o ∈ oddCoreOf Q, ∃ b ∈ B, o * b = q := by
  have hBQ : B ≤ Q := hQ ▸ le_sup_right
  rw [hQ, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf Q) B
    (hBQ.trans (le_normalizer_oddCoreOf Q))] at hq
  obtain ⟨o, ho, b, hb, rfl⟩ := Set.mem_mul.mp hq
  exact ⟨o, ho, b, hb, rfl⟩

theorem isSolvable_of_eq_oddCoreOf_sup [Finite G] {Q B : Subgroup G} (hB : IsMulCommutative B)
    (hQ : Q = oddCoreOf Q ⊔ B) : Group.IsSolvable Q := by
  have hBQ : B ≤ Q := hQ ▸ le_sup_right
  have : Group.IsSolvable (goldschmidtOddCore Q) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card Q)
  have hsurj : ∀ x : Q ⧸ goldschmidtOddCore Q, ∃ b : G, ∃ hb : b ∈ B,
      x = QuotientGroup.mk (⟨b, hBQ hb⟩ : Q) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨o, ⟨o', ho', hoo'⟩, b, hb, hob⟩ := exists_mul_of_eq_oddCoreOf_sup hQ q.2
    refine ⟨b, hb, ?_⟩
    have hq : q = o' * ⟨b, hBQ hb⟩ := Subtype.ext (by rw [Subgroup.coe_mul, ← hob, ← hoo']; rfl)
    rw [hq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o').mpr ho', one_mul]
  have : Group.IsSolvable (Q ⧸ goldschmidtOddCore Q) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨b, hb, rfl⟩ := hsurj x
    obtain ⟨c, hc, rfl⟩ := hsurj y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hbc : b * c = c * b := congrArg Subtype.val (hB.is_comm.comm (⟨b, hb⟩ : B) ⟨c, hc⟩)
    exact congrArg _ (Subtype.ext hbc)
  refine Group.isSolvable_of_ker_le_range (goldschmidtOddCore Q).subtype
    (QuotientGroup.mk' (goldschmidtOddCore Q)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end OddCore

section Normalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  exact and_congr (hH h) (hK h)

theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem normalizer_le_normalizer_centralizer (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).1
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

end Normalizer

section NormalClosure

variable {G : Type*} [Group G]

theorem normalClosureIn_le_self (X A : Subgroup G) : normalClosureIn X A ≤ X :=
  Subgroup.map_subtype_le _

theorem le_normalClosureIn {X A : Subgroup G} (hAX : A ≤ X) : A ≤ normalClosureIn X A :=
  fun a ha => ⟨⟨a, hAX ha⟩, Subgroup.subset_normalClosure (show (⟨a, hAX ha⟩ : X) ∈
    A.subgroupOf X from ha), rfl⟩

theorem le_normalizer_normalClosureIn (X A : Subgroup G) :
    X ≤ Subgroup.normalizer (normalClosureIn X A : Set G) := by
  have heq : (normalClosureIn X A).subgroupOf X =
      Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hn : ((normalClosureIn X A).subgroupOf X).Normal := by
    rw [heq]
    exact Subgroup.normalClosure_normal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le_self X A)).mp hn

theorem normalClosureIn_le {X A K : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hAK : A ⊓ X ≤ K) :
    normalClosureIn X A ≤ K := by
  have : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hle : Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X) ≤ K.subgroupOf X :=
    Subgroup.normalClosure_le_normal fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hAK ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩)
  have hm := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hKX] at hm

end NormalClosure

section Cyclic

variable {G : Type*} [Group G]

theorem exists_plane [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G}
    (hV : IsPGroup p V) (hVc : ¬ IsCyclic V) :
    ∃ E : Subgroup G, E ≤ V ∧ (∀ e : E, e ^ p = 1) ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB, hBc⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (hp.odd_of_ne_two hp2) hV hVc
  refine ⟨B.map V.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro ⟨_, b, hb, rfl⟩
    have hb1 : (⟨b, hb⟩ : B) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B) _
    exact Subtype.ext (by simpa using congrArg (fun x : B => ((x : V) : G)) hb1)
  · rw [Subgroup.card_map_of_injective V.subtype_injective, hBc]

theorem normal_subgroupOf_zpowers_sup {N : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) :
    (N.subgroupOf (Subgroup.zpowers y ⊔ N)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le (Subgroup.zpowers_le.mpr hyN) Subgroup.le_normalizer)

theorem isCyclic_quotient_zpowers_sup {N : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G))
    [(N.subgroupOf (Subgroup.zpowers y ⊔ N)).Normal] :
    IsCyclic ((Subgroup.zpowers y ⊔ N : Subgroup G) ⧸
      N.subgroupOf (Subgroup.zpowers y ⊔ N)) := by
  set J := Subgroup.zpowers y ⊔ N with hJ
  set π := QuotientGroup.mk' (N.subgroupOf J)
  have hyJ : y ∈ J := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨π ⟨y, hyJ⟩, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf J) x
  have hj : (j : G) ∈ ((Subgroup.zpowers y ⊔ N : Subgroup G) : Set G) := j.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hyN)] at hj
  obtain ⟨z, hz, n, hn, hzn⟩ := Set.mem_mul.mp hj
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have hj' : j = ⟨y, hyJ⟩ ^ k * ⟨n, Subgroup.mem_sup_right hn⟩ := Subtype.ext (by simp [hzn])
  have hn1 : π ⟨n, Subgroup.mem_sup_right hn⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hn
  rw [hj', map_mul, hn1, mul_one, map_zpow]

theorem isCyclic_of_le_zpowers_sup {V N : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hV : V ≤ Subgroup.zpowers y ⊔ N)
    (hVN : V ⊓ N = ⊥) : IsCyclic V := by
  have := normal_subgroupOf_zpowers_sup hyN
  have := isCyclic_quotient_zpowers_sup hyN
  set J := Subgroup.zpowers y ⊔ N with hJ
  set π := QuotientGroup.mk' (N.subgroupOf J)
  refine isCyclic_of_injective (π.comp (Subgroup.inclusion hV)) fun v w hvw => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq] at hvw
  have hmem : (v : G)⁻¹ * w ∈ V ⊓ N :=
    ⟨V.mul_mem (V.inv_mem v.2) w.2, Subgroup.mem_subgroupOf.mp hvw⟩
  rw [hVN, Subgroup.mem_bot] at hmem
  exact Subtype.ext (inv_mul_eq_one.mp hmem)

theorem le_of_isPerfect_of_le_zpowers_sup {L N : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hL : L ≤ Subgroup.zpowers y ⊔ N)
    (hLp : ⁅L, L⁆ = L) : L ≤ N := by
  have := normal_subgroupOf_zpowers_sup hyN
  have := isCyclic_quotient_zpowers_sup hyN
  set J := Subgroup.zpowers y ⊔ N with hJ
  set π := QuotientGroup.mk' (N.subgroupOf J)
  rw [← hLp, Subgroup.commutator_le]
  intro x hx z hz
  have hcomm : π ⟨x, hL hx⟩ * π ⟨z, hL hz⟩ = π ⟨z, hL hz⟩ * π ⟨x, hL hx⟩ :=
    (IsCyclic.commGroup.mul_comm _ _)
  have h1 : π (⟨x, hL hx⟩ * ⟨z, hL hz⟩ * (⟨x, hL hx⟩ : J)⁻¹ * (⟨z, hL hz⟩ : J)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end Cyclic

section ZStar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_map_eq {N T : Subgroup G} (hT : fusionIsSylowIn 2 T N) :
    ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = T := by
  obtain ⟨hTN, hT2, hTmax⟩ := hT
  obtain ⟨P, hP⟩ := (hT2.comap_subtype (K := N)).exists_le_sylow
  refine ⟨P, hTmax _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _) fun t ht => ?_⟩
  exact ⟨⟨t, hTN ht⟩, hP (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

theorem commutator_mem_oddCoreOf {N T : Subgroup G} (hT : fusionIsSylowIn 2 T N) {z : G}
    (hzT : z ∈ T) (hzc : T ≤ Subgroup.centralizer ({z} : Set G)) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hiso : ∀ g ∈ N, g⁻¹ * z * g ∈ T → g⁻¹ * z * g = z) {g : G} (hg : g ∈ N) :
    g * z * g⁻¹ * z⁻¹ ∈ oddCoreOf N := by
  obtain ⟨P, hPT⟩ := exists_sylow_map_eq hT
  have hzN : z ∈ N := hT.1 hzT
  have hmemP : ∀ x : N, (x : G) ∈ T → x ∈ (P : Subgroup N) := fun x hx => by
    rw [← hPT] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  set z' : (P : Subgroup N) := ⟨⟨z, hzN⟩, hmemP _ hzT⟩ with hz'
  have hzZ : z' ∈ Subgroup.center (P : Subgroup N) := Subgroup.mem_center_iff.mpr fun y => by
    have hyT : ((y : N) : G) ∈ T := hPT ▸ ⟨y, y.2, rfl⟩
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hzc hyT)))
  have hzo : orderOf z' = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (Subtype.ext (by simpa [sq] using hz2))
    · intro h
      exact hz1 (congrArg (fun x : (P : Subgroup N) => ((x : N) : G)) h)
  have hwc : ∀ x : N, x⁻¹ * (z' : N) * x ∈ (P : Subgroup N) → x⁻¹ * (z' : N) * x = z' := by
    intro x hx
    have hxT : (x : G)⁻¹ * z * x ∈ T := hPT ▸ ⟨_, hx, rfl⟩
    exact Subtype.ext (hiso x x.2 hxT)
  have hcen := (CFSG.Adapters.glauberman_zStar P z' hzZ hzo hwc).2
  have hmk := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk (⟨g, hg⟩ : N))
  have hmem : (⟨g, hg⟩ : N) * (z' : N) * (⟨g, hg⟩ : N)⁻¹ * (z' : N)⁻¹ ∈ CFSG.oddCore N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
    group
  exact ⟨_, hmem, rfl⟩

end ZStar

end CFSG.Goldschmidt.Sec8
