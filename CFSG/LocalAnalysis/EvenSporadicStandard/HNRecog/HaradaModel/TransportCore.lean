module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.TwoHS

variable {H K : Type} [Group H] [Group K]

private theorem harSqCard_map (f : H →* K) (hf : Function.Injective f) (X : Subgroup H) (y : H) :
    harSqCard X y = harSqCard (X.map f) (f y) := by
  unfold harSqCard
  refine Nat.card_congr (Equiv.subtypeEquiv (Subgroup.equivMapOfInjective X f hf).toEquiv
    fun x => ?_)
  have hx : ((Subgroup.equivMapOfInjective X f hf x : X.map f) : K) = f x := rfl
  change (x : H) ^ 2 = y ↔
    ((Subgroup.equivMapOfInjective X f hf x : X.map f) : K) ^ 2 = f y
  rw [hx, ← map_pow]
  exact (hf.eq_iff).symm

private theorem harCoreData_map (f : H →* K) (hf : Function.Injective f) {a z : H}
    {S E T T' W0 : Subgroup H} {t : K} (ha : f a = t) (D : HarCoreData a z S E T T' W0)
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

theorem harCoreData_of_mulEquiv (e : H ≃* K) {a z : H} {S E T T' W0 : Subgroup H}
    (h : HarCoreData a z S E T T' W0) :
    HarCoreData (e a) (e z) (S.map e.toMonoidHom) (E.map e.toMonoidHom) (T.map e.toMonoidHom)
      (T'.map e.toMonoidHom) (W0.map e.toMonoidHom) := by
  refine harCoreData_map e.toMonoidHom e.injective rfl h ?_
  intro x hx hxT
  obtain ⟨y, rfl⟩ := e.surjective x
  refine Subgroup.mem_map_of_mem e.toMonoidHom (h.cent_le y ?_ ?_)
  · apply e.injective
    rw [map_mul, map_mul]
    exact hx
  · intro w hw
    apply e.injective
    rw [map_mul, map_mul]
    exact hxT (e.toMonoidHom w) (Subgroup.mem_map_of_mem e.toMonoidHom hw)

theorem isElemAbelian_comap_mulEquiv (e : H ≃* K) {B : Subgroup K}
    (h : CFSG.Open.IsElemAbelian 2 B) : CFSG.Open.IsElemAbelian 2 (B.comap e.toMonoidHom) := by
  obtain ⟨hcomm, hpow⟩ := h
  refine ⟨IsMulCommutative.of_comm (fun x y => ?_), fun x hx => ?_⟩
  · apply Subtype.ext
    apply e.injective
    change e ((x : H) * (y : H)) = e ((y : H) * (x : H))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨e.toMonoidHom (x : H), x.2⟩
      ⟨e.toMonoidHom (y : H), y.2⟩)
  · apply e.injective
    rw [map_pow, map_one]
    exact hpow (e.toMonoidHom x) hx

theorem card_map_mulEquiv (e : H ≃* K) (X : Subgroup H) :
    Nat.card ↥(X.map e.toMonoidHom) = Nat.card ↥X :=
  (Nat.card_congr (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).toEquiv).symm

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
