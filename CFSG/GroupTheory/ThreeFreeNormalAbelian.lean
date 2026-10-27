module

public import CFSG.GroupTheory.ThreeGroupActionFixedPoint
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

@[expose] public section

namespace CFSG

variable {B : Type*} [Group B] [Finite B]

theorem not_three_dvd_card_of_irreducible_abelian_normal
    {X Y : Subgroup (MulAut B)}
    (hYX : Y ≤ X)
    (hYnorm : ∀ σ : MulAut B, σ ∈ X → ∀ y : MulAut B, y ∈ Y → σ * y * σ⁻¹ ∈ Y)
    (hYab : ∀ a : MulAut B, a ∈ Y → ∀ b : MulAut B, b ∈ Y → a * b = b * a)
    (hirr : ∀ U : Subgroup B, (∀ σ : MulAut B, σ ∈ X → Subgroup.map σ U = U) →
      U = ⊥ ∨ U = ⊤)
    (hB3 : IsPGroup 3 B) (hBnt : Nontrivial B)
    (hfaith : ∀ y : MulAut B, (∀ x : B, y x = x) → y = 1) :
    ¬ 3 ∣ Nat.card Y := by
  intro h3
  haveI : Finite (MulAut B) :=
    Finite.of_injective (fun f : MulAut B => (f : B → B))
      (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Finite Y := inferInstance
  letI : IsMulCommutative Y :=
    IsMulCommutative.of_comm
      (fun a b => Subtype.ext (hYab (a : MulAut B) a.2 (b : MulAut B) b.2))
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 Y := default
  have hPne : (P : Subgroup Y) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h3
  let Q : Subgroup (MulAut B) := (P : Subgroup Y).map Y.subtype
  have hQ3 : IsPGroup 3 Q :=
    (P.isPGroup').of_equiv
      (Subgroup.equivMapOfInjective (P : Subgroup Y) Y.subtype Y.subtype_injective)
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    have hmem : Y.subtype p ∈ Q := Subgroup.mem_map_of_mem Y.subtype hp
    rw [hbot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hQmem : ∀ σ : MulAut B, σ ∈ X → ∀ q : MulAut B, q ∈ Q → σ * q * σ⁻¹ ∈ Q := by
    intro σ hσ q hq
    rw [Subgroup.mem_map] at hq ⊢
    obtain ⟨p, hp, rfl⟩ := hq
    let p' : Y := ⟨σ * (p : MulAut B) * σ⁻¹, hYnorm σ hσ (p : MulAut B) p.2⟩
    refine ⟨p', ?_, rfl⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have hkY : (p : Y) ^ 3 ^ k = 1 := by
      simpa using congrArg (Subgroup.subtype (P : Subgroup Y)) hk
    have hkA : (p : MulAut B) ^ 3 ^ k = 1 := by
      simpa using congrArg (Subgroup.subtype Y) hkY
    have hp' : (p' : MulAut B) = MulAut.conj σ (p : MulAut B) := by
      rw [MulAut.conj_apply]
    have hp'pow : (p' : Y) ^ 3 ^ k = 1 := by
      apply Subtype.ext
      show (p' : MulAut B) ^ 3 ^ k = 1
      calc
        (p' : MulAut B) ^ 3 ^ k = (MulAut.conj σ (p : MulAut B)) ^ 3 ^ k := by rw [hp']
        _ = (MulAut.conj σ) ((p : MulAut B) ^ 3 ^ k) := by rw [map_pow]
        _ = (MulAut.conj σ) 1 := by rw [hkA]
        _ = 1 := by rw [map_one]
    have hp'3 : IsPGroup 3 (Subgroup.zpowers p') := by
      apply IsPGroup.of_card_dvd_pow (n := k)
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hp'pow
    exact IsPGroup.le_sylow_of_normal hp'3 P (Subgroup.mem_zpowers p')
  let C : Subgroup B :=
    { carrier := {x | ∀ q : MulAut B, q ∈ Q → q x = x}
      mul_mem' := by
        intro a b ha hb q hq
        rw [map_mul, ha q hq, hb q hq]
      one_mem' := by
        intro q _
        exact map_one q
      inv_mem' := by
        intro a ha q hq
        rw [map_inv, ha q hq] }
  have hCmem : ∀ x : B, x ∈ C ↔ ∀ q : MulAut B, q ∈ Q → q x = x := fun _ => Iff.rfl
  have hCinv : ∀ σ : MulAut B, σ ∈ X → Subgroup.map σ C = C := by
    intro σ hσ
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hCmem] at hx ⊢
      intro q hq
      have hq' : σ⁻¹ * q * σ ∈ Q := hQmem σ⁻¹ (inv_mem hσ) q hq
      calc
        q (σ x) = σ ((σ⁻¹ * q * σ) x) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
        _ = σ x := by rw [hx (σ⁻¹ * q * σ) hq']
    · intro y hy
      rw [hCmem] at hy
      have hy' : σ⁻¹ y ∈ C := by
        rw [hCmem]
        intro q hq
        have hq' : σ * q * σ⁻¹ ∈ Q := hQmem σ hσ q hq
        have hqu : (σ * q * σ⁻¹) y = y := hy (σ * q * σ⁻¹) hq'
        calc
          q (σ⁻¹ y) = σ⁻¹ (σ (q (σ⁻¹ y))) := by rw [MulAut.inv_apply_self]
          _ = σ⁻¹ ((σ * q * σ⁻¹) y) := by rw [MulAut.mul_apply, MulAut.mul_apply]
          _ = σ⁻¹ y := by rw [hqu]
      have hmem : σ (σ⁻¹ y) ∈ Subgroup.map σ C :=
        Subgroup.mem_map_of_mem (σ : B →* B) hy'
      rwa [MulAut.apply_inv_self] at hmem
  letI : MulDistribMulAction Q B := MulDistribMulAction.compHom B (Subgroup.subtype Q)
  obtain ⟨x, hxne, hxfix⟩ :=
    exists_nontrivial_fixed_point_of_isPGroup_three (Y := Q) (B := B) hQ3 hB3 hBnt
  have hsmul : ∀ (q' : Q) (y : B), q' • y = (q' : MulAut B) y := fun _ _ => rfl
  have hxC : x ∈ C := by
    rw [hCmem]
    intro q hq
    have h := hxfix ⟨q, hq⟩
    exact (hsmul ⟨q, hq⟩ x).trans h
  have hCne : C ≠ ⊥ := by
    intro hbot
    apply hxne
    exact Subgroup.mem_bot.mp (hbot ▸ hxC)
  rcases hirr C hCinv with hbot | htop
  · exact hCne hbot
  · exfalso
    have hQbot : Q = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro q hq
      apply hfaith q
      intro y
      have hy : y ∈ C := by
        rw [htop]
        exact Subgroup.mem_top y
      rw [hCmem] at hy
      exact hy q hq
    exact hQne hQbot

end CFSG
