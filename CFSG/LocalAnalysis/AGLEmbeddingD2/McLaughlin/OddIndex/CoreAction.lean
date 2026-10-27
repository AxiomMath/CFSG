module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

section Action

variable {Y I : Type} [Group Y] [Group I]

@[expose] def ActInv (ρ : Y →* MulAut I) (K : Subgroup I) : Prop := ∀ y, ∀ x ∈ K, ρ y x ∈ K

variable {ρ : Y →* MulAut I} {K : Subgroup I}

theorem ActInv.inv (h : ActInv ρ K) (y : Y) {x : I} (hx : x ∈ K) : ρ y⁻¹ x ∈ K := h y⁻¹ x hx

theorem ActInv.map_eq (h : ActInv ρ K) (y : Y) : K.map (ρ y).toMonoidHom = K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h y x hx
  · intro x hx
    refine ⟨ρ y⁻¹ x, h.inv y hx, ?_⟩
    change ρ y (ρ y⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem ρ_inv_apply (ρ : Y →* MulAut I) (y : Y) (x : I) : ρ y⁻¹ (ρ y x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem ρ_apply_inv (ρ : Y →* MulAut I) (y : Y) (x : I) : ρ y (ρ y⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

@[expose] def actSub (ρ : Y →* MulAut I) (K : Subgroup I) (hK : ActInv ρ K) : Y →* MulAut ↥K where
  toFun y :=
    { toFun := fun x => ⟨ρ y x, hK y x x.2⟩
      invFun := fun x => ⟨ρ y⁻¹ x, hK.inv y x.2⟩
      left_inv := fun x => Subtype.ext (ρ_inv_apply ρ y x)
      right_inv := fun x => Subtype.ext (ρ_apply_inv ρ y x)
      map_mul' := fun x z => Subtype.ext (map_mul (ρ y) _ _) }
  map_one' := by
    ext x
    simp
  map_mul' := fun y z => by
    ext x
    simp [MulAut.mul_apply]

theorem actSub_apply (hK : ActInv ρ K) (y : Y) (x : ↥K) :
    ((actSub ρ K hK y x : ↥K) : I) = ρ y x := rfl

@[expose] noncomputable def actQuot (ρ : Y →* MulAut I) (K : Subgroup I) [K.Normal]
    (hK : ActInv ρ K) : Y →* MulAut (I ⧸ K) where
  toFun y := QuotientGroup.congr K K (ρ y) (hK.map_eq y)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp
  map_mul' := fun y z => by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    show QuotientGroup.mk (ρ (y * z) x) = QuotientGroup.mk (ρ y (ρ z x))
    rw [map_mul]
    rfl

theorem actQuot_mk [K.Normal] (hK : ActInv ρ K) (y : Y) (x : I) :
    actQuot ρ K hK y (QuotientGroup.mk x) = QuotientGroup.mk (ρ y x) := rfl

theorem exists_fixed_of_mk_fixed [Finite I] [K.Normal] (hK : ActInv ρ K) {a : Y} (ha : a ^ 3 = 1)
    (h3 : ¬ 3 ∣ Nat.card K) (x : I)
    (hx : actQuot ρ K hK a (QuotientGroup.mk x) = QuotientGroup.mk x) :
    ∃ x' : I, (QuotientGroup.mk x' : I ⧸ K) = QuotientGroup.mk x ∧ ρ a x' = x' := by
  classical
  let α : Type := {z : I // (QuotientGroup.mk z : I ⧸ K) = QuotientGroup.mk x}
  have : Fintype α := Fintype.ofFinite α
  have hmk : ∀ z : α, (QuotientGroup.mk (ρ a z.1) : I ⧸ K) = QuotientGroup.mk x := by
    intro z
    have := actQuot_mk hK a z.1
    rw [z.2, hx] at this
    exact this.symm
  let f : Function.End α := fun z => ⟨ρ a z.1, hmk z⟩
  have hf3 : f ^ 3 = 1 := by
    have hpow : f ^ 3 = f * f * f := by rw [pow_succ, pow_two]
    rw [hpow]
    funext z
    have h3' : ρ a (ρ a (ρ a z.1)) = z.1 := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      have : a * a * a = 1 := by rw [← ha, pow_succ, pow_two]
      rw [this, map_one]
      rfl
    exact Subtype.ext h3'
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := f) (by simpa using hf3)
  have hcard : Fintype.card α = Nat.card K := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun z => ⟨x⁻¹ * z.1, ?_⟩, fun k => ⟨x * k.1, ?_⟩, ?_, ?_⟩
    · exact (QuotientGroup.eq.1 z.2.symm)
    · exact (QuotientGroup.eq.2 (by simpa using k.2)).symm
    · intro z; apply Subtype.ext; simp
    · intro k; apply Subtype.ext; simp
  by_contra hno
  push Not at hno
  have hfix : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun z => ?_⟩
    have hz : f z.1 = z.1 := z.2
    exact hno z.1.1 z.1.2 (by
      have := congrArg Subtype.val hz
      exact this)
  rw [hfix, hcard] at hmod
  exact h3 ((Nat.modEq_zero_iff_dvd).1 hmod)

end Action

section Index

variable {I : Type} [Group I]

theorem relIndex_sup_eq [Finite I] (J K : Subgroup I) [K.Normal] :
    J.relIndex (J ⊔ K) = J.relIndex K := by
  have e1 : J.relIndex (J ⊔ K) * Nat.card ↥(J ⊓ (J ⊔ K)) = Nat.card ↥(J ⊔ K) :=
    Subgroup.relIndex_mul_card J (J ⊔ K)
  have e2 : K.relIndex (J ⊔ K) * Nat.card ↥(K ⊓ (J ⊔ K)) = Nat.card ↥(J ⊔ K) :=
    Subgroup.relIndex_mul_card K (J ⊔ K)
  have e3 : K.relIndex J * Nat.card ↥(K ⊓ J) = Nat.card J := Subgroup.relIndex_mul_card K J
  have e4 : J.relIndex K * Nat.card ↥(J ⊓ K) = Nat.card K := Subgroup.relIndex_mul_card J K
  rw [inf_eq_left.2 le_sup_left] at e1
  rw [inf_eq_left.2 le_sup_right, Subgroup.relIndex_sup_right] at e2
  have hpos : 0 < K.relIndex J := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, zero_mul] at e3
    exact Nat.card_pos.ne' e3.symm
  have hJK : 0 < Nat.card ↥(J ⊓ K) := Nat.card_pos
  have e5 : K.relIndex J * (J.relIndex (J ⊔ K) * Nat.card ↥(K ⊓ J)) =
      K.relIndex J * Nat.card K := by
    calc K.relIndex J * (J.relIndex (J ⊔ K) * Nat.card ↥(K ⊓ J))
        = J.relIndex (J ⊔ K) * (K.relIndex J * Nat.card ↥(K ⊓ J)) := by ring
      _ = J.relIndex (J ⊔ K) * Nat.card J := by rw [e3]
      _ = Nat.card ↥(J ⊔ K) := e1
      _ = K.relIndex J * Nat.card K := e2.symm
  have e6 := Nat.eq_of_mul_eq_mul_left hpos e5
  have : Nat.card ↥(K ⊓ J) = Nat.card ↥(J ⊓ K) := by rw [inf_comm]
  rw [this] at e6
  exact Nat.eq_of_mul_eq_mul_right hJK (e6.trans e4.symm)

theorem not_two_dvd_index_of_sub_quot [Finite I] (J K : Subgroup I) [K.Normal]
    (h1 : ¬ 2 ∣ J.relIndex K) (h2 : ¬ 2 ∣ ((J ⊔ K).map (QuotientGroup.mk' K)).index) :
    ¬ 2 ∣ J.index := by
  have e : J.index = J.relIndex (J ⊔ K) * (J ⊔ K).index :=
    (Subgroup.relIndex_mul_index le_sup_left).symm
  have hker : (QuotientGroup.mk' K).ker ≤ J ⊔ K := by
    rw [QuotientGroup.ker_mk']; exact le_sup_right
  rw [Subgroup.index_map_eq (J ⊔ K) (QuotientGroup.mk'_surjective K) hker] at h2
  rw [e, relIndex_sup_eq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
  · exact h1 h
  · exact h2 h

end Index

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
