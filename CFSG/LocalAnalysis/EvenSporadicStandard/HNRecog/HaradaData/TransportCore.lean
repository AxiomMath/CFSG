module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS

private theorem harSqCard_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) (X : Subgroup H) (y : H) :
    harSqCard X y = harSqCard (X.map f) (f y) := by
  unfold harSqCard
  refine Nat.card_congr (Equiv.subtypeEquiv (Subgroup.equivMapOfInjective X f hf).toEquiv
    fun x => ?_)
  have hx : ((Subgroup.equivMapOfInjective X f hf x : X.map f) : K) = f x := rfl
  change (x : H) ^ 2 = y ↔
    ((Subgroup.equivMapOfInjective X f hf x : X.map f) : K) ^ 2 = f y
  rw [hx, ← map_pow]
  exact (hf.eq_iff).symm

private theorem harCoreData_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {a z : H} {S E T T' W0 : Subgroup H} {t : K}
    (ha : f a = t) (D : HarCoreData a z S E T T' W0)
    (hcent : ∀ x : K, x * t = t * x → (∀ y ∈ T.map f, x * y = y * x) → x ∈ E.map f) :
    HarCoreData t (f z) (S.map f) (E.map f) (T.map f) (T'.map f) (W0.map f) := by
  refine
    { t_sq := ?_, t_ne_one := ?_, z1_ne_one := ?_, z1_ne_t := ?_, t_mem := ?_, z1_mem := ?_,
      S_comm_t := ?_, T0_eq := ?_, Eg_norm := ?_, z1_comm := ?_, cent_le := hcent, centre := ?_,
      derived := ?_, W0_eq := ?_, card_T0_t := ?_, card_T0_z2 := ?_, card_T0'_t := ?_,
      card_T0'_z1 := ?_, card_T0'_z2 := ?_, card_W0_t := ?_, card_W0_z2 := ?_ }
  · rw [← ha, ← map_pow, D.t_sq, map_one]
  · exact fun h => D.t_ne_one (hf (by rw [ha, h, map_one]))
  · exact fun h => D.z1_ne_one (hf (by rw [h, map_one]))
  · exact fun h => D.z1_ne_t (hf (by rw [h, ← ha]))
  · rw [← ha]; exact Subgroup.mem_map_of_mem f D.t_mem
  · exact Subgroup.mem_map_of_mem f D.z1_mem
  · rintro _ ⟨s, hs, rfl⟩
    rw [← ha, ← map_mul, ← map_mul, D.S_comm_t s hs]
  · rw [D.T0_eq, Subgroup.map_inf S E f hf]
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem f (D.Eg_norm s hs e he)
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.z1_comm y hy]
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have hcomm' : ∀ y ∈ T, x * y = y * x := fun y hy =>
      hf (by rw [map_mul, map_mul]; exact hcomm (f y) (Subgroup.mem_map_of_mem f hy))
    rcases D.centre x hx hcomm' with h | h | h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (Or.inl (by rw [h, ha]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, map_mul, ha])))
  · rw [← Subgroup.map_commutator, D.derived]
  · rw [D.W0_eq, MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map]
    congr 1
    apply congrArg (fun A => ((T'.map f : Subgroup K) : Set K) ∪ A)
    ext w
    constructor
    · rintro ⟨y, ⟨hyT, hy2⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem f hyT, by rw [← map_pow, hy2, map_one]⟩
    · rintro ⟨⟨y, hyT, rfl⟩, hw2⟩
      exact ⟨y, ⟨hyT, hf (by rw [map_pow, hw2, map_one])⟩, rfl⟩
  · have h := harSqCard_map f hf T a
    rw [ha] at h
    rw [← h, D.card_T0_t]
  · have h := harSqCard_map f hf T (a * z)
    rw [map_mul, ha] at h
    rw [← h, D.card_T0_z2]
  · have h := harSqCard_map f hf T' a
    rw [ha] at h
    rw [← h, D.card_T0'_t]
  · exact (harSqCard_map f hf T' z).symm.trans D.card_T0'_z1
  · have h := harSqCard_map f hf T' (a * z)
    rw [map_mul, ha] at h
    rw [← h, D.card_T0'_z2]
  · have h := harSqCard_map f hf W0 a
    rw [ha] at h
    rw [← h, D.card_W0_t]
  · have h := harSqCard_map f hf W0 (a * z)
    rw [map_mul, ha] at h
    rw [← h, D.card_W0_z2]

theorem _root_.CFSG.EvenSporadicStandard.TwoHS.IsF5Centralizer.eq_commutator
    {H : Type} [Group H] {E : Subgroup H} (hE : TwoHS.IsF5Centralizer H E) :
    E = commutator H := by
  haveI : E.Normal := hE.normal
  apply le_antisymm
  ·
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥E) ∈ _root_.commutator ↥E := by
      rw [hE.perfect.commutator_eq_top]
      exact Subgroup.mem_top _
    have h1 := Subgroup.mem_map_of_mem E.subtype hx'
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  ·
    have hcomm : IsMulCommutative (H ⧸ E) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcard : Nat.card (H ⧸ E) = 2 := by
        rw [← Subgroup.index_eq_card, hE.index_eq_two]
      haveI : IsCyclic (H ⧸ E) := isCyclic_of_prime_card hcard
      infer_instance
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm

theorem TwoHSFacts.coe_eq {G : Type} [Group G] {t : G} (ht : orderOf t = 2)
    {a z b z₁ : ↥(centralizer ({t} : Set G))}
    (hF : TwoHSFacts ↥(centralizer ({t} : Set G)) a z b z₁) : (a : G) = t := by
  let t' : ↥(centralizer ({t} : Set G)) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have ht'cen : t' ∈ Subgroup.center ↥(centralizer ({t} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have ht'zp : t' ∈ zpowers a := by
    rw [hF.center_eq] at ht'cen
    exact ht'cen
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have ht'ne : t' ≠ 1 := fun h => ht1 (Subtype.ext_iff.mp h)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ht'zp
  have hk2 : t' = a ^ (k % 2) := by
    have h := zpow_mod_orderOf a k
    rw [hF.orderOf_a] at h
    exact hk.symm.trans h.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h] at hk2
    simp at hk2
    exact absurd hk2 ht'ne
  · rw [h] at hk2
    have hta : t' = a := by simpa using hk2
    exact (congrArg Subtype.val hta).symm

theorem harCoreData_map_subtype {G : Type} [Group G] {t : G}
    {a z : ↥(centralizer ({t} : Set G))}
    {S E T T' W0 : Subgroup ↥(centralizer ({t} : Set G))} (ha : (a : G) = t)
    (D : HarCoreData a z S E T T' W0) :
    HarCoreData t (z : G) (S.map (centralizer ({t} : Set G)).subtype)
      (E.map (centralizer ({t} : Set G)).subtype) (T.map (centralizer ({t} : Set G)).subtype)
      (T'.map (centralizer ({t} : Set G)).subtype) (W0.map (centralizer ({t} : Set G)).subtype) := by
  refine harCoreData_map (centralizer ({t} : Set G)).subtype Subtype.val_injective ha D ?_
  intro x hxt hxT
  have hxH : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hxt
  let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hxH⟩
  have hx'a : x' * a = a * x' := by
    apply Subtype.ext
    change x * (a : G) = (a : G) * x
    rw [ha]
    exact hxt
  have hx'T : ∀ y ∈ T, x' * y = y * x' := fun y hy => by
    apply Subtype.ext
    change x * (y : G) = (y : G) * x
    exact hxT ((centralizer ({t} : Set G)).subtype y) (Subgroup.mem_map_of_mem _ hy)
  exact Subgroup.mem_map_of_mem _ (D.cent_le x' hx'a hx'T)

end CFSG.EvenSporadicStandard.HNRecog
