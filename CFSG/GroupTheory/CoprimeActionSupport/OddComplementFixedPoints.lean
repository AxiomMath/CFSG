module


public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints

open scoped Pointwise

theorem exists_fixed {H : Type*} [Group H] [Finite H] (S B : Subgroup H) [S.Normal]
    (hS : IsPGroup 2 S) (hB : Odd (Nat.card B)) (hSB : S ⊔ B = ⊤)
    (X : Type*) [Finite X] [Nonempty X] [MulAction H X]
    (htrans : ∀ x y : X, ∃ s : S, s.val • x = y) :
    ∃ x : X, ∀ b : B, b.val • x = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hS
  have hBcop : Nat.Coprime (Nat.card S) (Nat.card B) := by
    rw [hk]; exact Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hB)
  have hinf : S ⊓ B = ⊥ := by
    have h1 : Nat.card ↥(S ⊓ B) ∣ Nat.card S := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(S ⊓ B) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_right
    have := Nat.eq_one_of_dvd_coprimes hBcop h1 h2
    exact (Subgroup.card_eq_one).1 this
  have hindex : S.index = Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := B)
    have h2 : S.relIndex B = S.index := by
      have := Subgroup.relIndex_sup_right (H := B) (K := S)
      rw [sup_comm, hSB, Subgroup.relIndex_top_right] at this
      exact this.symm
    rw [h2, hinf] at h1
    simpa using h1
  have hSidx_odd : Nat.Coprime (Nat.card S) S.index := by rw [hindex]; exact hBcop
  have hcardSB : Nat.card S * Nat.card B = Nat.card H := by
    rw [← hindex]; exact Subgroup.card_mul_index S
  have hBc : Subgroup.IsComplement' S B := Subgroup.isComplement'_of_coprime hcardSB hBcop
  obtain ⟨x0⟩ := ‹Nonempty X›
  set T : Subgroup H := MulAction.stabilizer H x0 with hT
  have hTS : T ⊔ S = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨s, hs⟩ := htrans x0 (h • x0)
    have : (s : H)⁻¹ * h ∈ T := by
      show ((s : H)⁻¹ * h) • x0 = x0
      rw [mul_smul, ← hs]; simp
    have e : h = (s : H) * ((s : H)⁻¹ * h) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right s.2) (Subgroup.mem_sup_left this)
  set S' : Subgroup T := S.subgroupOf T with hS'
  haveI : S'.Normal := Subgroup.Normal.subgroupOf inferInstance T
  have hS'p : IsPGroup 2 S' := hS.comap_subtype
  have hS'idx : S'.index = Nat.card B := by
    rw [← hindex]
    have := Subgroup.relIndex_sup_right (H := T) (K := S)
    rw [hTS, Subgroup.relIndex_top_right] at this
    rw [this]
    rfl
  have hS'cop : Nat.Coprime (Nat.card S') S'.index := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hS'p
    rw [hm, hS'idx]; exact Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hB)
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hS'cop
  set C' : Subgroup H := C.map T.subtype with hC'
  have hC'T : C' ≤ T := by
    rintro _ ⟨c, -, rfl⟩; exact c.2
  have hcardC' : Nat.card C' = Nat.card B := by
    rw [hC', Subgroup.card_map_of_injective T.subtype_injective, ← hS'idx]
    exact hC.symm.index_eq_card.symm
  have hC'c : Subgroup.IsComplement' S C' :=
    Subgroup.isComplement'_of_coprime (by rw [hcardC', hcardSB]) (by rw [hcardC']; exact hBcop)
  haveI : Group.IsSolvable S := by
    haveI : Group.IsNilpotent S := hS.isNilpotent
    infer_instance
  obtain ⟨n, hn, hBeq⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy S
    inferInstance hSidx_odd (H := C') (K := B)
    (Subgroup.isComplement'_def.1 hC'c).mul_eq (Subgroup.isComplement'_def.1 hBc).mul_eq
    (disjoint_iff.1 hC'c.disjoint) hinf
  refine ⟨(n : H)⁻¹ • x0, fun b => ?_⟩
  have hb : (b : H) ∈ C'.map (MulAut.conj n⁻¹).toMonoidHom := hBeq ▸ b.2
  obtain ⟨c, hc, hcb⟩ := hb
  have hcx : c • x0 = x0 := hC'T hc
  have : (b : H) = n⁻¹ * c * n := by
    rw [← hcb]; simp [MulAut.conj_apply]
  rw [this, mul_smul, mul_smul, smul_inv_smul, hcx]

end CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints
