module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.WeakClosure

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit

variable {G : Type*} [Group G]

structure Hyp
    (t : G) (L E : Subgroup G)
    (p : L →* Equiv.Perm (Fin 693)) : Prop where
  todd : ToddOrbit.Hyp t L E p
  ds : DavisSolomonFacts G t L E
  cent : centralizer (E : Set G) ≤ E
  index_ne_two : ∀ K : Subgroup G, K.index ≠ 2

theorem centralizer_le_of_le_sup {t : G} {L E : Subgroup G} (htE : t ∈ E)
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G))
    (hCL : centralizer (L : Set G) = zpowers t) : centralizer (E : Set G) ≤ E := by
  rw [hCL, sup_eq_left.2 (zpowers_le.2 htE)] at hCE
  exact hCE

section Action

variable {E : Subgroup G} {t : G}

@[expose] def conjPerm (n : normalizer (E : Set G)) : Equiv.Perm (orb E t) where
  toFun s := ⟨n * s * (n : G)⁻¹, (conj_mem_orb_iff' n.2).2 s.2⟩
  invFun s := ⟨(n : G)⁻¹ * s * n, conj_mem_orb n.2 s.2⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

@[expose] def actHom : normalizer (E : Set G) →* Equiv.Perm (orb E t) where
  toFun := conjPerm
  map_one' := Equiv.ext fun s => Subtype.ext (by simp [conjPerm])
  map_mul' n m := Equiv.ext fun s => Subtype.ext (by
    simp only [conjPerm, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, Subgroup.coe_mul, mul_inv_rev]
    group)

theorem coe_actHom_apply (n : normalizer (E : Set G)) (s : orb E t) :
    ((actHom n s : orb E t) : G) = n * s * (n : G)⁻¹ := rfl

abbrev actRange (E : Subgroup G) (t : G) : Subgroup (Equiv.Perm (orb E t)) := actHom.range

@[expose] def tPt (E : Subgroup G) (t : G) : orb E t := ⟨t, t_mem_orb⟩

theorem actHom_smul_t_iff (n : normalizer (E : Set G)) :
    actHom n (tPt E t) = tPt E t ↔ (n : G) ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    change (n : G) * t * (n : G)⁻¹ = t at h'
    calc (n : G) * t = (n : G) * t * (n : G)⁻¹ * n := by group
      _ = t * n := by rw [h']
  · intro h
    refine Subtype.ext ?_
    change (n : G) * t * (n : G)⁻¹ = t
    rw [h, mul_inv_cancel_right]

theorem actRange_pretransitive :
    MulAction.IsPretransitive (actRange E t) (orb E t) := by
  refine ⟨fun s s' => ?_⟩
  obtain ⟨n, hn, hns⟩ := s.2
  obtain ⟨m, hm, hms⟩ := s'.2
  refine ⟨⟨actHom (⟨m, hm⟩⁻¹ * ⟨n, hn⟩ : normalizer (E : Set G)), ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
  change ((actHom (⟨m, hm⟩⁻¹ * ⟨n, hn⟩ : normalizer (E : Set G)) s : orb E t) : G) = s'
  rw [coe_actHom_apply, ← hns, ← hms]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem actHom_eq_one_of_mem
    {L : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}
    (H : ToddOrbit.Hyp t L E p) {n : normalizer (E : Set G)} (hn : (n : G) ∈ E) :
    actHom (E := E) (t := t) n = 1 := by
  refine Equiv.ext fun s => Subtype.ext ?_
  change (n : G) * s * (n : G)⁻¹ = s
  rw [H.E_comm hn (H.orb_subset_E s.2), mul_inv_cancel_right]

end Action

end CFSG.EvenSmallLie.UnitarySix.Hunt
