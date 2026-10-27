module

public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

@[expose]
def oddOrderClosure (H : Subgroup G) : Subgroup G :=
  closure {g | g ∈ H ∧ Odd (orderOf g)}

theorem oddOrderClosure_eq_closure (H : Subgroup G) :
    oddOrderClosure H = closure {g | g ∈ H ∧ Odd (orderOf g)} := rfl

theorem mem_oddOrderClosure_of_mem_of_odd {H : Subgroup G} {g : G}
    (hg : g ∈ H) (hodd : Odd (orderOf g)) : g ∈ oddOrderClosure H :=
  Subgroup.subset_closure ⟨hg, hodd⟩

theorem oddOrderClosure_le_iff {H K : Subgroup G} :
    oddOrderClosure H ≤ K ↔ {g | g ∈ H ∧ Odd (orderOf g)} ⊆ K := by
  rw [oddOrderClosure_eq_closure]
  exact Subgroup.closure_le K

theorem oddOrderClosure_le (H : Subgroup G) : oddOrderClosure H ≤ H := by
  rw [oddOrderClosure_le_iff]
  exact fun _ hg => hg.1

theorem oddOrderClosure_mono {H K : Subgroup G} (h : H ≤ K) :
    oddOrderClosure H ≤ oddOrderClosure K := by
  rw [oddOrderClosure_eq_closure, oddOrderClosure_eq_closure]
  exact Subgroup.closure_mono fun _ hg => ⟨h hg.1, hg.2⟩

private theorem mem_normalizer_oddOrderClosure_generators {H : Subgroup G} {x : G}
    (hx : x ∈ normalizer (H : Set G)) :
    x ∈ normalizer ({g : G | g ∈ H ∧ Odd (orderOf g)} : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · rintro ⟨hgH, hgodd⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hx g).mp hgH, ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hgodd
  · rintro ⟨hgH, hgodd⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hx g).mpr hgH, ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq] at hgodd
    exact hgodd

theorem normalizer_le_normalizer_oddOrderClosure (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (oddOrderClosure H) := by
  intro x hx
  have hx' : x ∈ normalizer (closure {g : G | g ∈ H ∧ Odd (orderOf g)}) :=
    Subgroup.normalizer_le_normalizer_closure
      ({g : G | g ∈ H ∧ Odd (orderOf g)}) (mem_normalizer_oddOrderClosure_generators hx)
  simpa only [oddOrderClosure] using hx'

theorem conj_mem_oddOrderClosure {H : Subgroup G} {x k : G}
    (hx : x ∈ normalizer (H : Set G)) (hk : k ∈ oddOrderClosure H) :
    x * k * x⁻¹ ∈ oddOrderClosure H := by
  have hx' : x ∈ normalizer (oddOrderClosure H) :=
    normalizer_le_normalizer_oddOrderClosure H hx
  exact (Subgroup.mem_normalizer_iff.mp hx' k).mp hk

theorem normal_oddOrderClosure_subgroupOf (H : Subgroup G) :
    ((oddOrderClosure H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oddOrderClosure_le H)]
  exact (Subgroup.le_normalizer (H := H)).trans (normalizer_le_normalizer_oddOrderClosure H)

theorem map_oddOrderClosure_le {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G) :
    (oddOrderClosure H).map f ≤ oddOrderClosure (H.map f) := by
  rw [oddOrderClosure_eq_closure, MonoidHom.map_closure, oddOrderClosure_eq_closure]
  exact Subgroup.closure_mono fun y hy => by
    rcases hy with ⟨x, ⟨hxH, hxodd⟩, rfl⟩
    exact ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩,
      Odd.of_dvd_nat hxodd (orderOf_map_dvd f x)⟩

theorem map_oddOrderClosure {G' : Type*} [Group G'] (f : G ≃* G') (H : Subgroup G) :
    (oddOrderClosure H).map (f : G →* G') = oddOrderClosure (H.map (f : G →* G')) := by
  apply le_antisymm
  · exact map_oddOrderClosure_le (f : G →* G') H
  · let S : Set G := {g | g ∈ H ∧ Odd (orderOf g)}
    let S' : Set G' := {g | g ∈ H.map (f : G →* G') ∧ Odd (orderOf g)}
    have hset : (f : G →* G') '' S = S' := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxH, hxodd⟩, rfl⟩
        refine ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩, ?_⟩
        have hfx : orderOf ((f : G →* G') x) = orderOf x := MulEquiv.orderOf_eq f x
        rw [hfx]
        exact hxodd
      · rintro ⟨hy, hyodd⟩
        obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hy
        refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
        have hfx : orderOf ((f : G →* G') x) = orderOf x := MulEquiv.orderOf_eq f x
        rw [hfx] at hyodd
        exact hyodd
    have hmap : closure S' = (closure S).map (f : G →* G') := by
      rw [MonoidHom.map_closure]
      exact (congrArg Subgroup.closure hset).symm
    change closure S' ≤ (closure S).map (f : G →* G')
    exact hmap.le

variable [Finite G]

private theorem odd_of_orderOf_pow_two_pow {g : G} :
    Odd (orderOf (g ^ 2 ^ (orderOf g).factorization 2)) := by
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hdvd : 2 ^ (orderOf g).factorization 2 ∣ orderOf g :=
    Nat.ordProj_dvd (orderOf g) 2
  have hpow : orderOf (g ^ 2 ^ (orderOf g).factorization 2) =
      orderOf g / 2 ^ (orderOf g).factorization 2 :=
    orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd
  have hcompl : orderOf g / 2 ^ (orderOf g).factorization 2 = ordCompl[2] (orderOf g) := rfl
  rw [hpow, hcompl]
  exact (Nat.coprime_ordCompl Nat.prime_two hg0).odd_of_left

theorem pow_two_pow_mem_oddOrderClosure (H : Subgroup G) {g : G} (hg : g ∈ H) :
    ∃ k : ℕ, g ^ 2 ^ k ∈ oddOrderClosure H := by
  refine ⟨(orderOf g).factorization 2, ?_⟩
  exact mem_oddOrderClosure_of_mem_of_odd (H.pow_mem hg _) odd_of_orderOf_pow_two_pow

theorem index_oddOrderClosure_eq_two_pow (H : Subgroup G) :
    ∃ k : ℕ, ((oddOrderClosure H).subgroupOf H).index = 2 ^ k := by
  let N : Subgroup H := (oddOrderClosure H).subgroupOf H
  haveI hN : N.Normal := normal_oddOrderClosure_subgroupOf H
  have hquot : IsPGroup 2 (H ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨k, hk⟩ := pow_two_pow_mem_oddOrderClosure H (g := (g : G)) g.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) ((g : H) ^ 2 ^ k)).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := H ⧸ N)).mp hquot
  exact ⟨k, by rw [Subgroup.index_eq_card]; exact hk⟩

theorem sup_sylow_eq (H : Subgroup G) {Q : Subgroup G} (hQH : Q ≤ H)
    (hQ2 : IsPGroup 2 Q) (hQidx : ¬ 2 ∣ (Q.subgroupOf H).index) :
    oddOrderClosure H ⊔ Q = H := by
  let N : Subgroup G := oddOrderClosure H
  let NH : Subgroup H := N.subgroupOf H
  haveI hNH : NH.Normal := normal_oddOrderClosure_subgroupOf H
  have hNidx : ∃ k : ℕ, NH.index = 2 ^ k := index_oddOrderClosure_eq_two_pow H
  have hQH2 : IsPGroup 2 (Q.subgroupOf H) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  let S : Sylow 2 H := hQH2.toSylow hQidx
  have hScoe : (S : Subgroup H) = Q.subgroupOf H := IsPGroup.toSylow_coe hQH2 hQidx
  have hsupH : NH ⊔ (S : Subgroup H) = ⊤ :=
    CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top NH hNidx S
  have hNHQ : NH ⊔ Q.subgroupOf H = ⊤ := by
    rw [← hScoe]
    exact hsupH
  refine le_antisymm (sup_le (oddOrderClosure_le H) hQH) ?_
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈ ((NH ⊔ Q.subgroupOf H : Subgroup H) : Set H) := by
    rw [hNHQ]
    exact Subgroup.mem_top _
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨n, hn, q, hq, hnq⟩ := hmem
  have hnG : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
  have hqG : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have hnqG : (n : G) * (q : G) = h := congrArg Subtype.val hnq
  rw [← hnqG]
  exact Subgroup.mul_mem_sup hnG hqG

theorem oddOrderClosure_eq_self_of_odd_card (H : Subgroup G) (hH : Odd (Nat.card H)) :
    oddOrderClosure H = H := by
  apply le_antisymm (oddOrderClosure_le H)
  intro g hg
  have hodd : Odd (orderOf (⟨g, hg⟩ : H)) :=
    hH.of_dvd_nat (orderOf_dvd_natCard (⟨g, hg⟩ : H))
  exact mem_oddOrderClosure_of_mem_of_odd hg ((Subgroup.orderOf_coe (⟨g, hg⟩ : H)).symm ▸ hodd)

end CFSG.GroupTheory
