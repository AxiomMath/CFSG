module

public import CFSG.LieType.Ree.SmallReeFixedCoordinates
public import CFSG.LieType.Ree.NormalPositiveGeneration
public import CFSG.LieType.Ree.PositiveTorusCentralizer

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def smallReeTorusElt
    (a : ℕ) (K : Type*) [CommRing K] (s : Kˣ) :
    (Module.End K (RootModule Tag.G2 K))ˣ :=
  torusElt Tag.G2 K ⟨0, by decide⟩ s * torusElt Tag.G2 K ⟨1, by decide⟩ (s ^ 3 ^ a)

@[expose] def smallReeTorusChar (a : ℕ) {K : Type*} [CommRing K] (s : Kˣ) (i : Fin 6) : Kˣ :=
  s ^ (∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * smallReeRoot i j) *
    (s ^ 3 ^ a) ^ (∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * smallReeRoot i j)

section Conj

variable {K : Type*} [CommRing K] {a : ℕ}

theorem smallReeTorusElt_conj_smallReeX
    (s : Kˣ) (i : Fin 6) (c : K) :
    smallReeTorusElt a K s * smallReeX K i c * (smallReeTorusElt a K s)⁻¹ =
      smallReeX K i ((smallReeTorusChar a s i : K) * c) := by
  have hα : IsRoot Tag.G2 (smallReeRoot i) := RootOps.isRootB_iff.1 (smallReeRoot_check i).1
  have e : ∀ x y z : (Module.End K (RootModule Tag.G2 K))ˣ,
      x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := fun x y z => by group
  rw [smallReeTorusElt, e, smallReeX, root_torus_conjugation _ hα, root_torus_conjugation _ hα,
    smallReeTorusChar, Units.val_mul, mul_assoc]
  rfl

theorem smallReeTorusElt_conj_smallReeP
    (s : Kˣ) (c₀ c₁ c₂ c₃ c₄ c₅ : K) :
    smallReeTorusElt a K s * smallReeP K c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeTorusElt a K s)⁻¹ =
      smallReeP K ((smallReeTorusChar a s 0 : K) * c₀) ((smallReeTorusChar a s 1 : K) * c₁)
        ((smallReeTorusChar a s 2 : K) * c₂) ((smallReeTorusChar a s 3 : K) * c₃)
        ((smallReeTorusChar a s 4 : K) * c₄) ((smallReeTorusChar a s 5 : K) * c₅) := by
  have h := fun x => (MulAut.conj_apply (smallReeTorusElt a K s) x).symm
  rw [h]
  simp only [smallReeP, map_mul, MulAut.conj_apply, smallReeTorusElt_conj_smallReeX]

theorem smallReeTorusChar_zero (s : Kˣ) : smallReeTorusChar a s 0 = s ^ (2 * 3 ^ a - 1) := by
  have e1 : ∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * smallReeRoot 0 j = -1 := by decide
  have e2 : ∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * smallReeRoot 0 j = 2 := by decide
  have hθ : 1 ≤ 2 * 3 ^ a := by have := Nat.one_le_pow a 3 (by norm_num); omega
  rw [smallReeTorusChar, e1, e2, ← zpow_natCast s (3 ^ a), ← zpow_mul, ← zpow_add,
    ← zpow_natCast]
  congr 1
  push_cast [Nat.cast_sub hθ]
  ring

theorem smallReeTorusChar_two (s : Kˣ) : smallReeTorusChar a s 2 = s ^ (1 - (3 ^ a : ℤ)) := by
  have e1 : ∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * smallReeRoot 2 j = 1 := by decide
  have e2 : ∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * smallReeRoot 2 j = -1 := by decide
  rw [smallReeTorusChar, e1, e2, ← zpow_natCast s (3 ^ a), ← zpow_mul, ← zpow_add]
  congr 1
  push_cast
  ring

theorem smallReeTorusChar_three (s : Kˣ) : smallReeTorusChar a s 3 = s ^ 3 ^ a := by
  have e1 : ∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * smallReeRoot 3 j = 0 := by decide
  have e2 : ∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * smallReeRoot 3 j = 1 := by decide
  rw [smallReeTorusChar, e1, e2, zpow_zero, zpow_one, one_mul]

theorem smallReeTorusElt_one
    : smallReeTorusElt a K 1 = 1 := by
  rw [smallReeTorusElt, one_pow, torusElt_one, torusElt_one, mul_one]

theorem smallReeTorusElt_mul
    (s t : Kˣ) :
    smallReeTorusElt a K (s * t) = smallReeTorusElt a K s * smallReeTorusElt a K t := by
  rw [smallReeTorusElt, smallReeTorusElt, smallReeTorusElt, mul_pow, torusElt_mul, torusElt_mul]
  exact Commute.mul_mul_mul_comm (torusElt_mul_comm _ _ _ _) _ _

end Conj

theorem smallReeP_mem_posUnipotent
    {K : Type*} [CommRing K] (c₀ c₁ c₂ c₃ c₄ c₅ : K) :
    smallReeP K c₀ c₁ c₂ c₃ c₄ c₅ ∈ posUnipotent Tag.G2 K := by
  unfold smallReeP
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact smallReeX_mem_posUnipotent K _ _

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

omit [Finite K] [CharP K G2.prime] in
theorem smallReeTorusElt_eq_reeTorus
    (s : Kˣ) :
    smallReeTorusElt a K s = ((G2.reeTorus a g2I0 s : adjointGroup G2.tag K) : ModGL G2.tag K) := by
  have hp : G2.perm g2I0 = g2I1 := by decide
  rw [reeTorus, hp]
  rfl

theorem smallReeTorusElt_mem
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (s : Kˣ) :
    smallReeTorusElt a K s ∈ G2.reeFixedTorus K a := by
  rw [smallReeTorusElt_eq_reeTorus]
  exact coe_reeTorus_mem_reeFixedTorus hK (by decide) s

theorem exists_smallReeTorusElt_eq
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeFixedTorus K a) :
    ∃ s : Kˣ, smallReeTorusElt a K s = g := by
  obtain ⟨hgH, hgΓ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨s, t, rfl⟩ := G2_torus_eq hgH
  have hga : torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t ∈ adjointGroup G2.tag K :=
    mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)
  have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ hga
  have e : (⟨_, hga⟩ : adjointGroup G2.tag K) =
      torusElement G2.tag K g2I0 s * torusElement G2.tag K g2I1 t := rfl
  have hp0 : G2.perm g2I0 = g2I1 := by decide
  have hp1 : G2.perm g2I1 = g2I0 := by decide
  rw [e, map_mul, finiteReeAut_eq_reeAut, reeAut_torusElement, reeAut_torusElement, hp0,
    hp1] at hF
  have hF' : torusElt G2.tag K g2I0 (t ^ G2.relationExponent a g2I1) *
      torusElt G2.tag K g2I1 (s ^ G2.relationExponent a g2I0) =
        torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 t :=
    (torusElt_mul_comm (τ := G2.tag) (R := K) g2I0 g2I1 _ _).trans hF
  obtain ⟨-, hts⟩ := G2_torusPair_inj hF'
  rw [G2_relationExponent.1] at hts
  exact ⟨s, by rw [← hts]; rfl⟩

omit [Finite K] [CharP K G2.prime] in
theorem smallReeTorusElt_injective
    : Function.Injective (smallReeTorusElt a K) := fun _ _ h =>
  (G2_torusPair_inj (K := K) h).1

theorem smallReeTorusElt_conj_smallReeCoord
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (s : Kˣ)
    (t b c : K) :
    smallReeTorusElt a K s * smallReeCoord a K t b c * (smallReeTorusElt a K s)⁻¹ =
      smallReeCoord a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t)
        (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b) ((s : K) ^ 3 ^ a * c) := by
  have hbij := bijOn_smallReeCoord (a := a) hK
  have hP := smallReeTorusElt_conj_smallReeP (a := a) s t (smallReeSigma a t) b c
    (smallReeSigma a b - t ^ 3 * smallReeSigma a t)
    (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2)
  rw [← smallReeCoord_eq_smallReeP] at hP
  have hmem : ((smallReeTorusElt a K s : ModGL G2.tag K) * smallReeCoord a K t b c *
      (smallReeTorusElt a K s)⁻¹ : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a := by
    have hh : (smallReeTorusElt a K s : ModGL G2.tag K) ∈ G2.reeGamma K a :=
      (Subgroup.mem_inf.1 (smallReeTorusElt_mem hK s)).2
    have hu : (smallReeCoord a K t b c : ModGL G2.tag K) ∈ G2.reeGamma K a :=
      (Subgroup.mem_inf.1 (hbij.1 (Set.mem_univ (t, b, c)))).2
    refine Subgroup.mem_inf.2 ⟨?_, (G2.reeGamma K a).mul_mem ((G2.reeGamma K a).mul_mem hh hu)
      ((G2.reeGamma K a).inv_mem hh)⟩
    have h1 := smallReeP_mem_posUnipotent (K := K) ((smallReeTorusChar a s 0 : K) * t)
      ((smallReeTorusChar a s 1 : K) * smallReeSigma a t) ((smallReeTorusChar a s 2 : K) * b)
      ((smallReeTorusChar a s 3 : K) * c)
      ((smallReeTorusChar a s 4 : K) * (smallReeSigma a b - t ^ 3 * smallReeSigma a t))
      ((smallReeTorusChar a s 5 : K) * (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2))
    rw [← hP] at h1
    exact h1
  obtain ⟨⟨t', b', c'⟩, -, he⟩ := hbij.2.2 hmem
  have he' := he
  change smallReeCoord a K t' b' c' = _ at he'
  rw [hP, smallReeCoord_eq_smallReeP] at he'
  obtain ⟨e0, -, e2, e3, -, -⟩ := smallReeP_injective he'
  change smallReeCoord a K t' b' c' = _ at he
  rw [← he, e0, e2, e3, smallReeTorusChar_zero, smallReeTorusChar_two, smallReeTorusChar_three,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

end ReeTag

theorem small_Ree_positive_torus_action
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∃ φ : Kˣ ≃* ReeTag.G2.reeFixedTorus K a,
      ∀ s, (φ s : ModGL ReeTag.G2.tag K) = smallReeTorusElt a K s) ∧
    (∀ (s : Kˣ) (t b c : K),
      smallReeTorusElt a K s * smallReeCoord a K t b c * (smallReeTorusElt a K s)⁻¹ =
        smallReeCoord a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t)
          (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b) ((s : K) ^ 3 ^ a * c)) ∧
    Function.Bijective (fun s : Kˣ => s ^ (2 * 3 ^ a - 1)) ∧
    Nat.card (Set.range fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))) = (3 ^ (2 * a + 1) - 1) / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, hcard⟩ :=
    small_Ree_field_power_identities a K hK
  let f : Kˣ →* ReeTag.G2.reeFixedTorus K a :=
    { toFun := fun s => ⟨smallReeTorusElt a K s, ReeTag.smallReeTorusElt_mem hK s⟩
      map_one' := Subtype.ext smallReeTorusElt_one
      map_mul' := fun s t => Subtype.ext (smallReeTorusElt_mul s t) }
  have hf : Function.Bijective f := by
    refine ⟨fun s s' h => ReeTag.smallReeTorusElt_injective (congrArg Subtype.val h),
      fun g => ?_⟩
    obtain ⟨s, hs⟩ := ReeTag.exists_smallReeTorusElt_eq g.2
    exact ⟨s, Subtype.ext hs⟩
  exact ⟨⟨MulEquiv.ofBijective f hf, fun s => rfl⟩,
    fun s t b c => ReeTag.smallReeTorusElt_conj_smallReeCoord hK s t b c, hbij, hcard⟩

end CFSG.LieType.Ree
