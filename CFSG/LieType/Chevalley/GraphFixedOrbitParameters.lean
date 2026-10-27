module

public import CFSG.LieType.Chevalley.GraphFixedData

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

variable (t : TwistTag)

theorem orbit_nonempty (a : Fin t.foldedTag.rank) : (t.orbit a).Nonempty := by
  revert a
  cases t <;> decide

@[expose] def orbitMin (a : Fin t.foldedTag.rank) : Fin t.tag.rank :=
  (t.orbit a).min' (t.orbit_nonempty a)

theorem orbitMin_mem (a : Fin t.foldedTag.rank) : t.orbitMin a ∈ t.orbit a :=
  Finset.min'_mem _ _

theorem orbitIndex_orbitMin (a : Fin t.foldedTag.rank) : t.orbitIndex (t.orbitMin a) = a :=
  (t.mem_orbit_iff).1 (t.orbitMin_mem a)

theorem orbit_eq_image_orbitMin (a : Fin t.foldedTag.rank) :
    t.orbit a = (Finset.range (t.orbit a).card).image fun k => (t.perm ^ k) (t.orbitMin a) := by
  revert a
  cases t <;> decide

theorem injOn_pow_orbitMin (a : Fin t.foldedTag.rank) :
    Set.InjOn (fun k => (t.perm ^ k) (t.orbitMin a)) (Finset.range (t.orbit a).card) := by
  have key : ∀ a, ∀ k ∈ Finset.range (t.orbit a).card, ∀ l ∈ Finset.range (t.orbit a).card,
      (t.perm ^ k) (t.orbitMin a) = (t.perm ^ l) (t.orbitMin a) → k = l := by
    cases t <;> decide
  exact fun k hk l hl h => key a k hk l hl h

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def orbitField (a : Fin t.foldedTag.rank) : Subfield K :=
  RingHom.eqLocusField (σ ^ (t.orbit a).card) (RingHom.id K)

@[expose] def orbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) : adjointGroup t.tag K :=
  ((List.range (t.orbit a).card).map fun k =>
    xElement ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod

@[expose] def orbitY
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) : adjointGroup t.tag K :=
  ((List.range (t.orbit a).card).map fun k =>
    yElement ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod

@[expose] def orbitN
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    adjointGroup t.tag K :=
  orbitX t K σ a u * orbitY t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) *
    orbitX t K σ a u

@[expose] def orbitH
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    adjointGroup t.tag K :=
  orbitN t K σ a u * (orbitN t K σ a 1)⁻¹

variable {t K σ}

theorem mem_orbitField {a : Fin t.foldedTag.rank} {c : K} :
    c ∈ orbitField t K σ a ↔ (σ ^ (t.orbit a).card) c = c :=
  RingHom.mem_eqLocusField

theorem coe_orbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) = ((List.range (t.orbit a).card).map fun k =>
      xUnit t.tag K ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod := by
  rw [orbitX, Subgroup.val_list_prod, List.map_map]
  rfl

theorem coe_orbitY
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) = ((List.range (t.orbit a).card).map fun k =>
      yUnit t.tag K ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod := by
  rw [orbitY, Subgroup.val_list_prod, List.map_map]
  rfl

end CFSG.LieType.Chevalley
