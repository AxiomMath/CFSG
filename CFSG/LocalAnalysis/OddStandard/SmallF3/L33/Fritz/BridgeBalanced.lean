module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeBurnside
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Open

theorem eq_one_of_odd_of_commute {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hX : standardComponentIsStandard L)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (hcyc : ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (S : Subgroup ↥(centralizer (L : Set G))))
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) {u : G}
    (hu : u ∈ centralizer (L : Set G)) (hodd : Odd (orderOf u)) (hut : u * t = t * u) :
    u = 1 := by
  let C : Subgroup G := centralizer (L : Set G)
  let Q : Subgroup G := centralizer ({t} : Set G)
  obtain ⟨N, _hNnormal, hNodd, hall⟩ :=
    exists_normal_odd_complement (C := ↥C) hX.2.1 hcyc
  let H : Subgroup G := N.map C.subtype
  let M : Subgroup ↥Q := H.subgroupOf Q
  have hMnormal : M.Normal := by
    refine ⟨fun m hm q => ?_⟩
    change ((q * m * q⁻¹ : ↥Q) : G) ∈ N.map C.subtype
    have hmH : (m : G) ∈ N.map C.subtype := hm
    obtain ⟨c, hcN, hceq⟩ := Subgroup.mem_map.mp hmH
    have hceq' : (c : G) = (m : G) := hceq
    have hmC : (m : G) ∈ C := hceq' ▸ c.2
    have hqcomm : (q : G) * t = t * (q : G) :=
      mem_centralizer_singleton_iff.mp q.2
    have hqnorm : (q : G) ∈ normalizer C :=
      hX.mem_normalizer_centralizer_of_commute ht ht2 hqcomm
    have hconjC : (q : G) * (m : G) * (q : G)⁻¹ ∈ C :=
      (mem_normalizer_iff.mp hqnorm (m : G)).mp hmC
    have hodd_conj :
        Odd (orderOf (⟨(q : G) * (m : G) * (q : G)⁻¹, hconjC⟩ : ↥C)) := by
      rw [Subgroup.orderOf_mk, ← hceq']
      have h1 : orderOf ((q : G) * (c : G) * (q : G)⁻¹) = orderOf (c : G) := by
        have hconj := orderOf_injective (MulAut.conj (q : G)).toMonoidHom
          (MulAut.conj (q : G)).injective (c : G)
        simpa [MulAut.conj_apply] using hconj
      rw [h1, Subgroup.orderOf_coe]
      exact hNodd.of_dvd_nat (N.orderOf_dvd_natCard hcN)
    exact Subgroup.mem_map.mpr ⟨_, hall _ hodd_conj, rfl⟩
  have hoddM : Odd (Nat.card M) := by
    have hcardmap : Nat.card M = Nat.card (M.map Q.subtype) :=
      (Subgroup.card_map_of_injective (K := M) Q.subtype_injective).symm
    have hmaple : M.map Q.subtype ≤ H := by
      have h1 : M.map Q.subtype = H ⊓ Q := Subgroup.subgroupOf_map_subtype H Q
      rw [h1]
      exact inf_le_left
    have hcardH : Nat.card H = Nat.card N :=
      Subgroup.card_map_of_injective (K := N) C.subtype_injective
    have hdvd : Nat.card M ∣ Nat.card N := by
      rw [hcardmap, ← hcardH]
      exact Subgroup.card_dvd_of_le hmaple
    exact hNodd.of_dvd_nat hdvd
  have hMle : M ≤ CFSG.oddCore ↥Q := le_sSup ⟨hMnormal, hoddM⟩
  have hbalQ : CFSG.oddCore ↥Q = ⊥ := hbal
  have hMbot : M = ⊥ := by
    rw [hbalQ] at hMle
    exact bot_unique hMle
  have huN : (⟨u, hu⟩ : ↥C) ∈ N := hall ⟨u, hu⟩ (by simpa using hodd)
  have huQ : u ∈ Q := mem_centralizer_singleton_iff.mpr hut
  have huM : (⟨u, huQ⟩ : ↥Q) ∈ M := by
    change u ∈ N.map C.subtype
    exact Subgroup.mem_map.mpr ⟨⟨u, hu⟩, huN, rfl⟩
  have hone : (⟨u, huQ⟩ : ↥Q) = 1 := by
    simpa [hMbot] using huM
  simpa using Subtype.ext_iff.mp hone

theorem isPGroup_inf_of_balanced {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hX : standardComponentIsStandard L)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (hcyc : ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (S : Subgroup ↥(centralizer (L : Set G))))
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    IsPGroup 2 ↥(centralizer ({t} : Set G) ⊓ centralizer (L : Set G)) := by
  intro g
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd
    (orderOf_pos (g : G)).ne'
  refine ⟨a, ?_⟩
  have hdvd : 2 ^ a ∣ orderOf (g : G) := ⟨m, hgm⟩
  have hord : orderOf ((g : G) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hgm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hgt : (g : G) * t = t * g := mem_centralizer_singleton_iff.mp g.2.1
  have hu : (g : G) ^ 2 ^ a = 1 :=
    eq_one_of_odd_of_commute hX hbal hcyc ht ht2 (pow_mem g.2.2 _) (hord ▸ hm)
      ((Commute.pow_left hgt (2 ^ a)).eq)
  exact Subtype.ext (by simpa using hu)

end CFSG.OddStandard.SmallF3.L33
