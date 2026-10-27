module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

theorem coprime_cocycle {T C : Type*} [Group T] [Group C] [Finite T] [Finite C] (hT : IsPGroup 2 T)
    (hC : Odd (Nat.card C)) (σ : T →* MulAut C) (D : T → C)
    (hD : ∀ s t, D (s * t) = D s * σ s (D t)) :
    ∃ o : C, ∀ t, D t = o * σ t o⁻¹ := by
  have hsolv : Group.IsSolvable C := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
  have hcop : Nat.Coprime (Nat.card T) (Nat.card C) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hC)
  let _ : MulDistribMulAction T C := MulDistribMulAction.compHom C σ
  obtain ⟨x, hx⟩ := CFSG.exists_principal_cocycle_of_solvable_coprime (A := T) (N := C) hsolv hcop D
    (fun a b => hD a b)
  refine ⟨x, fun t => ?_⟩
  rw [hx t]
  change x * (σ t x)⁻¹ = x * σ t x⁻¹
  rw [map_inv]

theorem coprime_conj_homs {A : Type*} [Group A] [Finite A] {T : Type*} [Group T] [Finite T]
    (hT : IsPGroup 2 T) (C : Subgroup A) (hC : Odd (Nat.card C)) (Φ c : T →* A)
    (hnorm : ∀ t, c t ∈ Subgroup.normalizer (C : Set A)) (hdiff : ∀ t, Φ t * (c t)⁻¹ ∈ C) :
    ∃ o ∈ C, ∀ t, Φ t = o * c t * o⁻¹ := by
  let n : T →* ↥(Subgroup.normalizer (C : Set A)) := c.codRestrict _ hnorm
  let σ : T →* MulAut ↥C := C.normalizerMonoidHom.comp n
  let D : T → ↥C := fun t => ⟨Φ t * (c t)⁻¹, hdiff t⟩
  have hσ : ∀ (t : T) (x : ↥C), ((σ t x : ↥C) : A) = c t * (x : A) * (c t)⁻¹ := by
    intro t x
    simp [σ, n]
  have hD : ∀ s t, D (s * t) = D s * σ s (D t) := by
    intro s t
    apply Subtype.ext
    simp only [D, Subgroup.coe_mul, hσ, map_mul, mul_inv_rev]
    group
  obtain ⟨o, ho⟩ := coprime_cocycle hT hC σ D hD
  refine ⟨(o : A), o.2, fun t => ?_⟩
  have h1 := congrArg (fun x : ↥C => (x : A)) (ho t)
  simp only [D, Subgroup.coe_mul, hσ, Subgroup.coe_inv] at h1
  calc Φ t = (Φ t * (c t)⁻¹) * c t := by group
    _ = ((o : A) * (c t * (o : A)⁻¹ * (c t)⁻¹)) * c t := by rw [h1]
    _ = (o : A) * c t * (o : A)⁻¹ := by group

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
