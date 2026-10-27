module

public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley Matrix

inductive ReeTag
  | G2 | F4
  deriving DecidableEq, Repr

namespace ReeTag

@[expose] def tag : ReeTag → Tag
  | G2 => .G2
  | F4 => .F4

@[expose] def prime : ReeTag → ℕ
  | G2 => 3
  | F4 => 2

@[expose] def longSet : (t : ReeTag) → Finset (Fin t.tag.rank)
  | G2 => ({0} : Finset (Fin 2))
  | F4 => ({0, 1} : Finset (Fin 4))

@[expose] def perm : (t : ReeTag) → Equiv.Perm (Fin t.tag.rank)
  | G2 => (Equiv.swap 0 1 : Equiv.Perm (Fin 2))
  | F4 => (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))

@[expose] def scale (t : ReeTag) (i : Fin t.tag.rank) : ℕ :=
  if i ∈ t.longSet then t.prime else 1

theorem symmetrizer_apply_self (t : ReeTag) (i : Fin t.tag.rank) :
    t.tag.symmetrizer i i = t.scale i := by
  cases t <;> revert i <;> decide +kernel

@[expose] def dualMap (t : ReeTag) : (Fin t.tag.rank → ℚ) →ₗ[ℚ] (Fin t.tag.rank → ℚ) where
  toFun v j := (t.scale (t.perm.symm j) : ℚ) * v (t.perm.symm j)
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem dualMap_single (t : ReeTag) (i : Fin t.tag.rank) :
    t.dualMap (Pi.single i 1) = (t.scale i : ℚ) • Pi.single (t.perm i) 1 := by
  funext j
  simp only [dualMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs with h
  · simp [h]
  · simp

@[expose] def quadForm (t : ReeTag) (α : Fin t.tag.rank → ℤ) : ℤ :=
  α ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ α)

@[expose] def lengthParam (t : ReeTag) (α : Fin t.tag.rank → ℤ) : ℚ :=
  (t.quadForm α : ℚ) / 2

@[expose] def duality (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℚ :=
  (t.lengthParam α)⁻¹ • t.dualMap fun j => (α j : ℚ)

@[expose] def shortRoots (t : ReeTag) : Set (Fin t.tag.rank → ℤ) :=
  {α | IsRoot t.tag α ∧ t.lengthParam α = 1}

@[expose] def longRoots (t : ReeTag) : Set (Fin t.tag.rank → ℤ) :=
  {α | IsRoot t.tag α ∧ t.lengthParam α = t.prime}

@[expose] def dualMapInt (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℤ :=
  fun j => (t.scale (t.perm.symm j) : ℤ) * α (t.perm.symm j)

@[expose] def dualRoot (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℤ :=
  fun j => 2 * t.dualMapInt α j / t.quadForm α

@[expose] def halfRootCount : ReeTag → ℕ
  | G2 => 6
  | F4 => 24

@[expose] def rootDualityCheck (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Bool :=
  decide ((t.quadForm α = 2 ∨ t.quadForm α = 2 * t.prime) ∧
    (∀ j, 2 * t.dualMapInt α j % t.quadForm α = 0) ∧
    t.tag.stringData.memDec t.tag.rootCertificate (t.dualRoot α) = true ∧
    t.dualRoot (t.dualRoot α) = α ∧
    t.quadForm (t.dualRoot α) * t.quadForm α = 4 * t.prime ∧
    (0 < height (t.dualRoot α) ↔ 0 < height α) ∧
    ∀ i, t.dualRoot (reflect t.tag i α) = reflect t.tag (t.perm i) (t.dualRoot α))

theorem rootDualityCheck_root (t : ReeTag) :
    ∀ k < t.tag.rootCertificate.roots.length,
      t.rootDualityCheck (t.tag.rootCertificate.root k) = true := by
  cases t <;> decide +kernel

variable {t : ReeTag} {α : Fin t.tag.rank → ℤ}

theorem rootDualityCheck_spec (hα : IsRoot t.tag α) :
    (t.quadForm α = 2 ∨ t.quadForm α = 2 * t.prime) ∧
      (∀ j, 2 * t.dualMapInt α j % t.quadForm α = 0) ∧
      IsRoot t.tag (t.dualRoot α) ∧
      t.dualRoot (t.dualRoot α) = α ∧
      t.quadForm (t.dualRoot α) * t.quadForm α = 4 * t.prime ∧
      (0 < height (t.dualRoot α) ↔ 0 < height α) ∧
      ∀ i, t.dualRoot (reflect t.tag i α) = reflect t.tag (t.perm i) (t.dualRoot α) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hα
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true (t.rootDualityCheck_root k hk)
  exact ⟨h1, h2,
    (StringData.memDec_iff t.tag.rootCertificate_check t.tag.stringData_check).1 h3, h4⟩

theorem dualMap_intCast (t : ReeTag) (α : Fin t.tag.rank → ℤ) :
    t.dualMap (fun j => (α j : ℚ)) = fun j => (t.dualMapInt α j : ℚ) := by
  funext j
  simp [dualMap, dualMapInt]

theorem duality_eq_of_dvd (h0 : t.quadForm α ≠ 0)
    (hd : ∀ j, t.quadForm α ∣ 2 * t.dualMapInt α j) :
    t.duality α = fun j => (t.dualRoot α j : ℚ) := by
  funext j
  obtain ⟨c, hc⟩ := hd j
  have hq : (t.quadForm α : ℚ) ≠ 0 := by exact_mod_cast h0
  have hc' : 2 * (t.dualMapInt α j : ℚ) = t.quadForm α * c := by exact_mod_cast hc
  simp only [duality, lengthParam, dualMap_intCast, Pi.smul_apply, smul_eq_mul, dualRoot, hc,
    Int.mul_ediv_cancel_left _ h0]
  rw [inv_div, div_mul_eq_mul_div, hc', mul_comm, mul_div_assoc, div_self hq, mul_one]

theorem quadForm_eq (hα : IsRoot t.tag α) :
    t.quadForm α = 2 ∨ t.quadForm α = 2 * t.prime :=
  (rootDualityCheck_spec hα).1

theorem quadForm_ne_zero (hα : IsRoot t.tag α) : t.quadForm α ≠ 0 := by
  rcases quadForm_eq hα with h | h <;> rw [h] <;> cases t <;> decide

theorem lengthParam_eq (hα : IsRoot t.tag α) :
    t.lengthParam α = 1 ∨ t.lengthParam α = t.prime := by
  rcases quadForm_eq hα with h | h
  · left
    rw [lengthParam, h]
    norm_num
  · right
    rw [lengthParam, h]
    push_cast
    ring

theorem isRoot_dualRoot (hα : IsRoot t.tag α) : IsRoot t.tag (t.dualRoot α) :=
  (rootDualityCheck_spec hα).2.2.1

theorem duality_eq_dualRoot (hα : IsRoot t.tag α) :
    t.duality α = fun j => (t.dualRoot α j : ℚ) :=
  duality_eq_of_dvd (quadForm_ne_zero hα) fun j =>
    Int.dvd_of_emod_eq_zero ((rootDualityCheck_spec hα).2.1 j)

theorem dualRoot_dualRoot (hα : IsRoot t.tag α) : t.dualRoot (t.dualRoot α) = α :=
  (rootDualityCheck_spec hα).2.2.2.1

theorem lengthParam_dualRoot_mul (hα : IsRoot t.tag α) :
    t.lengthParam (t.dualRoot α) * t.lengthParam α = t.prime := by
  have h := (rootDualityCheck_spec hα).2.2.2.2.1
  have h' : (t.quadForm (t.dualRoot α) : ℚ) * t.quadForm α = 4 * t.prime := by exact_mod_cast h
  rw [lengthParam, lengthParam, div_mul_div_comm, h']
  ring

theorem height_dualRoot_pos_iff (hα : IsRoot t.tag α) :
    0 < height (t.dualRoot α) ↔ 0 < height α :=
  (rootDualityCheck_spec hα).2.2.2.2.2.1

theorem dualRoot_reflect (hα : IsRoot t.tag α) (i : Fin t.tag.rank) :
    t.dualRoot (reflect t.tag i α) = reflect t.tag (t.perm i) (t.dualRoot α) :=
  (rootDualityCheck_spec hα).2.2.2.2.2.2 i

theorem dualRoot_single (t : ReeTag) (i : Fin t.tag.rank) :
    t.dualRoot (Pi.single i 1) = Pi.single (t.perm i) 1 := by
  cases t <;> revert i <;> decide +kernel

theorem lengthParam_eq_one_iff : t.lengthParam α = 1 ↔ t.quadForm α = 2 := by
  rw [lengthParam, div_eq_one_iff_eq two_ne_zero]
  exact_mod_cast Iff.rfl

theorem lengthParam_eq_prime_iff : t.lengthParam α = t.prime ↔ t.quadForm α = 2 * t.prime := by
  rw [lengthParam, div_eq_iff two_ne_zero, mul_comm]
  exact_mod_cast Iff.rfl

theorem prime_ne_one (t : ReeTag) : t.prime ≠ 1 := by
  cases t <;> decide

theorem lengthParam_eq_one_iff_ne (hα : IsRoot t.tag α) :
    t.lengthParam α = 1 ↔ t.lengthParam α ≠ t.prime := by
  have hp : (t.prime : ℚ) ≠ 1 := by exact_mod_cast t.prime_ne_one
  rcases lengthParam_eq hα with h | h <;> rw [h]
  · exact ⟨fun _ => hp.symm, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' hp, fun h' => absurd rfl h'⟩

theorem lengthParam_dualRoot_eq_one_iff (hα : IsRoot t.tag α) :
    t.lengthParam (t.dualRoot α) = 1 ↔ t.lengthParam α ≠ 1 := by
  have hp : (t.prime : ℚ) ≠ 1 := by exact_mod_cast t.prime_ne_one
  have hm := lengthParam_dualRoot_mul hα
  rcases lengthParam_eq hα with h | h <;> rw [h] at hm ⊢
  · rw [mul_one] at hm
    rw [hm]
    exact ⟨fun h' => absurd h' hp, fun h' => absurd rfl h'⟩
  · have hp0 : (t.prime : ℚ) ≠ 0 := by cases t <;> norm_num [prime]
    have : t.lengthParam (t.dualRoot α) = 1 := by
      have := mul_right_cancel₀ hp0 (hm.trans (one_mul _).symm)
      exact this
    exact ⟨fun _ => hp, fun _ => this⟩

theorem shortRoots_union_longRoots (t : ReeTag) :
    t.shortRoots ∪ t.longRoots = {α | IsRoot t.tag α} := by
  ext α
  simp only [shortRoots, longRoots, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hα
    rcases lengthParam_eq hα with h | h
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr ⟨hα, h⟩

theorem disjoint_shortRoots_longRoots (t : ReeTag) : Disjoint t.shortRoots t.longRoots := by
  rw [Set.disjoint_left]
  rintro α ⟨hα, h1⟩ ⟨-, hp⟩
  exact (lengthParam_eq_one_iff_ne hα).1 h1 hp

theorem bijOn_dualRoot (t : ReeTag) : Set.BijOn t.dualRoot t.longRoots t.shortRoots := by
  refine ⟨fun α hα => ⟨isRoot_dualRoot hα.1, (lengthParam_dualRoot_eq_one_iff hα.1).2 ?_⟩,
    fun α hα β hβ h => ?_, fun β hβ => ⟨t.dualRoot β, ⟨isRoot_dualRoot hβ.1, ?_⟩,
      dualRoot_dualRoot hβ.1⟩⟩
  · rw [hα.2]
    exact_mod_cast t.prime_ne_one
  · rw [← dualRoot_dualRoot hα.1, h, dualRoot_dualRoot hβ.1]
  · have h := lengthParam_dualRoot_mul hβ.1
    rwa [hβ.2, mul_one] at h

theorem shortRoots_eq (t : ReeTag) :
    t.shortRoots = ↑((rootFinset t.tag).filter fun α => t.quadForm α = 2) := by
  ext α
  simp only [shortRoots, Set.mem_ofPred_eq, Finset.coe_filter, mem_rootFinset,
    lengthParam_eq_one_iff]

theorem longRoots_eq (t : ReeTag) :
    t.longRoots = ↑((rootFinset t.tag).filter fun α => t.quadForm α = 2 * t.prime) := by
  ext α
  simp only [longRoots, Set.mem_ofPred_eq, Finset.coe_filter, mem_rootFinset,
    lengthParam_eq_prime_iff]

theorem ncard_shortRoots (t : ReeTag) : t.shortRoots.ncard = t.halfRootCount := by
  rw [shortRoots_eq, Set.ncard_coe_finset]
  cases t <;> decide +kernel

theorem ncard_longRoots (t : ReeTag) : t.longRoots.ncard = t.halfRootCount := by
  rw [longRoots_eq, Set.ncard_coe_finset]
  cases t <;> decide +kernel

end ReeTag

open ReeTag

theorem exceptional_root_duality (t : ReeTag) :
    (∀ α, IsRoot t.tag α →
      (t.lengthParam α = 1 ∨ t.lengthParam α = t.prime) ∧
      (IsRoot t.tag (t.dualRoot α) ∧ t.duality α = fun j => (t.dualRoot α j : ℚ)) ∧
      t.duality (t.dualRoot α) = (fun j => (α j : ℚ)) ∧
      t.lengthParam (t.dualRoot α) * t.lengthParam α = t.prime ∧
      (0 < height (t.dualRoot α) ↔ 0 < height α) ∧
      ∀ i, t.duality (reflect t.tag i α) =
        fun j => (reflect t.tag (t.perm i) (t.dualRoot α) j : ℚ)) ∧
    (∀ i, t.duality (Pi.single i 1) = fun j => ((Pi.single (t.perm i) 1 : Fin _ → ℤ) j : ℚ)) ∧
    t.shortRoots.ncard = t.halfRootCount ∧ t.longRoots.ncard = t.halfRootCount := by
  refine ⟨fun α hα => ⟨lengthParam_eq hα, ⟨isRoot_dualRoot hα, duality_eq_dualRoot hα⟩, ?_,
    lengthParam_dualRoot_mul hα, height_dualRoot_pos_iff hα, fun i => ?_⟩, fun i => ?_,
    ncard_shortRoots t, ncard_longRoots t⟩
  · rw [duality_eq_dualRoot (isRoot_dualRoot hα), dualRoot_dualRoot hα]
  · rw [duality_eq_dualRoot (.reflect i hα), dualRoot_reflect hα]
  · rw [duality_eq_dualRoot (.basis i), dualRoot_single]

end CFSG.LieType.Ree
