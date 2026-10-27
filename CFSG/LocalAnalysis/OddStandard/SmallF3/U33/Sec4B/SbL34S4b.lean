module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHI74

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.Outside

variable {G : Type} [Group G] [Finite G]

private def conjHom (P Q : Subgroup G)
    (hPQ : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q) : ↥P →* MulAut ↥Q where
  toFun p :=
    { toFun := fun x => ⟨(p : G) * (x : G) * (p : G)⁻¹, hPQ p p.2 x x.2⟩
      invFun := fun x => ⟨(p : G)⁻¹ * (x : G) * (p : G),
        by simpa using hPQ p⁻¹ (P.inv_mem p.2) x x.2⟩
      left_inv := by
        intro x
        ext
        simp [mul_assoc]
      right_inv := by
        intro x
        ext
        simp [mul_assoc]
      map_mul' := by
        intro x y
        ext
        simp [mul_assoc] }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro p q
    ext x
    simp [mul_assoc]

private lemma conjHom_apply (P Q : Subgroup G)
    (hPQ : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q) (p : ↥P) (x : ↥Q) :
    ((conjHom P Q hPQ p x : ↥Q) : G) = (p : G) * (x : G) * (p : G)⁻¹ := rfl

theorem exists_stab_subgroup (Q P : Subgroup G) (hQ : IsSylSL34 Q) (hP : IsPGroup 2 P)
    (hPQ : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q)
    (hfix : ∀ p ∈ P, ∀ z ∈ Q ⊓ centralizer (Q : Set G), p * z * p⁻¹ = z) :
    ∃ R : Subgroup G, R ≤ P ∧ R.relIndex P ≤ 2 ∧
      ∀ r ∈ R, ∀ x ∈ Q, x⁻¹ * (r * x * r⁻¹) ∈ Q ⊓ centralizer (Q : Set G) := by
  have hfix' : ∀ p : ↥P, ∀ z ∈ center ↥Q, conjHom P Q hPQ p z = z := by
    intro p z hz
    apply Subtype.ext
    rw [conjHom_apply]
    have hzG : (z : G) ∈ Q ⊓ centralizer (Q : Set G) := by
      refine ⟨z.2, ?_⟩
      change ∀ q ∈ (Q : Set G), q * (z : G) = (z : G) * q
      intro q hq
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨q, hq⟩ : ↥Q))
    exact hfix p p.2 (z : G) hzG
  have hindex : ((chainStab ↥Q).comap (conjHom P Q hPQ)).index ≤ 2 :=
    GHI74_index_le_two (Q := ↥Q) hQ hP (conjHom P Q hPQ) hfix'
  let H : Subgroup ↥P := (chainStab ↥Q).comap (conjHom P Q hPQ)
  let R : Subgroup G := H.map P.subtype
  have hRle : R ≤ P := Subgroup.map_subtype_le H
  have hHindex : H.index ≤ 2 := hindex
  have hRrel : R.relIndex P ≤ 2 := by
    have htop : (⊤ : Subgroup ↥P).map P.subtype = P := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hrel : R.relIndex P = H.index := by
      conv_lhs => rw [← htop]
      rw [Subgroup.relIndex_map_map_of_injective (f := P.subtype) H ⊤ P.subtype_injective,
        Subgroup.relIndex_top_right]
    rw [hrel]
    exact hHindex
  refine ⟨R, hRle, hRrel, ?_⟩
  intro r hr x hx
  obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hr
  rw [← hp_eq]
  have hα : conjHom P Q hPQ p ∈ chainStab ↥Q := hp
  let w : ↥Q := (⟨x, hx⟩ : ↥Q)⁻¹ * conjHom P Q hPQ p ⟨x, hx⟩
  have hw : w ∈ center ↥Q := hα.1 ⟨x, hx⟩
  have hwG : (w : G) ∈ Q ⊓ centralizer (Q : Set G) := by
    refine ⟨w.2, ?_⟩
    change ∀ q ∈ (Q : Set G), q * (w : G) = (w : G) * q
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw (⟨q, hq⟩ : ↥Q))
  have hwval : (w : G) = x⁻¹ * ((p : G) * x * (p : G)⁻¹) := rfl
  rw [hwval] at hwG
  exact hwG

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
