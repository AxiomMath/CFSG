module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BWeights
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartCoord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {φ : (Fin 6 → ZMod 2) → G} {A H : Subgroup G}

@[expose] noncomputable def conjCoord (φ : (Fin 6 → ZMod 2) → G) (m : G)
    (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  Function.invFun φ (m * φ v * m⁻¹)

theorem IsPerm6.conjCoord_spec (h : IsPerm6 φ A H) {m : G} (hm : m ∈ normalizer (A : Set G))
    (v : Fin 6 → ZMod 2) : φ (conjCoord φ m v) = m * φ v * m⁻¹ := by
  unfold conjCoord
  exact Function.invFun_eq ((h.mem_iff _).mp
    ((Subgroup.mem_normalizer_iff.mp hm (φ v)).mp (h.mem v)))

theorem IsPerm6.conjCoord_eq_iff (h : IsPerm6 φ A H) {m : G} (hm : m ∈ normalizer (A : Set G))
    (v u : Fin 6 → ZMod 2) : conjCoord φ m v = u ↔ m * φ v * m⁻¹ = φ u := by
  constructor
  · intro hvu
    rw [← h.conjCoord_spec hm v, hvu]
  · intro hmu
    exact h.injective (by rw [h.conjCoord_spec hm v, hmu])

theorem IsPerm6.conjCoord_add (h : IsPerm6 φ A H) {m : G} (hm : m ∈ normalizer (A : Set G))
    (v w : Fin 6 → ZMod 2) :
    conjCoord φ m (v + w) = conjCoord φ m v + conjCoord φ m w := by
  apply (h.conjCoord_eq_iff hm (v + w) (conjCoord φ m v + conjCoord φ m w)).mpr
  have h1 : φ (v + w) = φ v * φ w := h.map_add v w
  have h2 : φ (conjCoord φ m v + conjCoord φ m w)
      = φ (conjCoord φ m v) * φ (conjCoord φ m w) := h.map_add _ _
  rw [h1, h2, h.conjCoord_spec hm v, h.conjCoord_spec hm w]
  group

theorem IsPerm6.conjCoord_mul (h : IsPerm6 φ A H) {m m' : G} (hm : m ∈ normalizer (A : Set G))
    (hm' : m' ∈ normalizer (A : Set G)) (v : Fin 6 → ZMod 2) :
    conjCoord φ (m * m') v = conjCoord φ m (conjCoord φ m' v) := by
  apply (h.conjCoord_eq_iff ((normalizer (A : Set G)).mul_mem hm hm') v
    (conjCoord φ m (conjCoord φ m' v))).mpr
  rw [h.conjCoord_spec hm (conjCoord φ m' v), h.conjCoord_spec hm' v]
  group

theorem IsPerm6.conjCoord_one (h : IsPerm6 φ A H) (v : Fin 6 → ZMod 2) :
    conjCoord φ 1 v = v := by
  apply (h.conjCoord_eq_iff (normalizer (A : Set G)).one_mem v v).mpr
  simp

@[expose] def heartAltSet (φ : (Fin 6 → ZMod 2) → G) (A : Subgroup G) :
    Set (Equiv.Perm (Fin 8)) :=
  {σ | ∃ m ∈ normalizer (A : Set G), ∀ w : Fin 8 → ZMod 2, IsEvenVec w →
    conjCoord φ m (heartCoord w) = heartCoord (permVec σ w)}

theorem IsPerm6.one_mem_heartAltSet (h : IsPerm6 φ A H) : 1 ∈ heartAltSet φ A := by
  refine ⟨1, (normalizer (A : Set G)).one_mem, ?_⟩
  intro w _
  rw [h.conjCoord_one]
  rfl

theorem IsPerm6.mul_mem_heartAltSet (h : IsPerm6 φ A H) {σ τ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ heartAltSet φ A) (hτ : τ ∈ heartAltSet φ A) : σ * τ ∈ heartAltSet φ A := by
  rcases hσ with ⟨m, hm, hσ⟩
  rcases hτ with ⟨m', hm', hτ⟩
  refine ⟨m * m', (normalizer (A : Set G)).mul_mem hm hm', ?_⟩
  intro w hw
  rw [h.conjCoord_mul hm hm' (heartCoord w), hτ w hw]
  rw [hσ (permVec τ w) (isEvenVec_permVec τ hw)]
  exact congrArg heartCoord (sec5b_permVec_mul σ τ w).symm

theorem IsPerm6.inv_mem_heartAltSet (h : IsPerm6 φ A H) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ heartAltSet φ A) : σ⁻¹ ∈ heartAltSet φ A := by
  rcases hσ with ⟨m, hm, hσ⟩
  refine ⟨m⁻¹, (normalizer (A : Set G)).inv_mem hm, ?_⟩
  intro w hw
  have hw' : IsEvenVec (permVec σ⁻¹ w) := isEvenVec_permVec σ⁻¹ hw
  have hfix : permVec σ (permVec σ⁻¹ w) = w := by
    rw [← sec5b_permVec_mul, mul_inv_cancel]
    rfl
  have hinner : conjCoord φ m (heartCoord (permVec σ⁻¹ w)) = heartCoord w := by
    rw [hσ (permVec σ⁻¹ w) hw', hfix]
  calc conjCoord φ m⁻¹ (heartCoord w)
      = conjCoord φ m⁻¹ (conjCoord φ m (heartCoord (permVec σ⁻¹ w))) := by rw [hinner]
      _ = conjCoord φ (m⁻¹ * m) (heartCoord (permVec σ⁻¹ w)) := by
            rw [← h.conjCoord_mul ((normalizer (A : Set G)).inv_mem hm) hm
              (heartCoord (permVec σ⁻¹ w))]
      _ = conjCoord φ 1 (heartCoord (permVec σ⁻¹ w)) := by rw [inv_mul_cancel]
      _ = heartCoord (permVec σ⁻¹ w) := by rw [h.conjCoord_one]

@[expose] def IsPerm6.heartAlt (h : IsPerm6 φ A H) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := heartAltSet φ A
  one_mem' := h.one_mem_heartAltSet
  mul_mem' := h.mul_mem_heartAltSet
  inv_mem' := h.inv_mem_heartAltSet

theorem IsPerm6.isHeartA8_heartAlt (h : IsPerm6 φ A H)
    (hall : ∀ m ∈ normalizer (A : Set G), ∃ σ : Equiv.Perm (Fin 8), ∀ w : Fin 8 → ZMod 2,
      IsEvenVec w → conjCoord φ m (heartCoord w) = heartCoord (permVec σ w)) :
    IsHeartA8 A (normalizer (A : Set G)) h.heartAlt := by
  refine ⟨fun w => φ (heartCoord w), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bot_le
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  · exact le_rfl
  · intro m _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro hx
      rw [hx]
      group
    · intro hx
      have := congrArg (fun y => m⁻¹ * y * m) hx
      simpa [mul_assoc] using this
  · intro v _
    exact h.mem (heartCoord v)
  · intro v w _ _
    show (φ (heartCoord v) * φ (heartCoord w))⁻¹ * φ (heartCoord (v + w)) ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, sec5b_heartCoord_add, h.map_add]
    group
  · intro v hv
    rw [Subgroup.mem_bot]
    show φ (heartCoord v) = 1 ↔ v ∈ ({0, fun _ => 1} : Set (Fin 8 → ZMod 2))
    rw [← h.map_zero, h.injective.eq_iff, sec5b_heartCoord_eq_zero hv]
    constructor
    · rintro (h0 | h1)
      · exact Set.mem_insert_iff.mpr (Or.inl h0)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h1))
    · intro hvN
      rcases Set.mem_insert_iff.mp hvN with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Set.mem_singleton_iff.mp h1)
  · intro x hx
    obtain ⟨u, hu⟩ := (h.mem_iff x).mp hx
    obtain ⟨w, hw, hwc⟩ := sec5b_heartCoord_surj u
    refine ⟨w, hw, ?_⟩
    show (φ (heartCoord w))⁻¹ * x ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, ← hu, ← hwc]
    group
  · intro m hm
    obtain ⟨σ, hσ⟩ := hall m hm
    refine ⟨σ, ⟨m, hm, hσ⟩, ?_⟩
    intro v hv
    show (m * φ (heartCoord v) * m⁻¹)⁻¹ * φ (heartCoord (permVec σ v)) ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, ← h.conjCoord_spec hm (heartCoord v), hσ v hv]
    group
  · intro σ hσ
    obtain ⟨m, hm, hσ⟩ := hσ
    refine ⟨m, hm, ?_⟩
    intro v hv
    show (m * φ (heartCoord v) * m⁻¹)⁻¹ * φ (heartCoord (permVec σ v)) ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, ← h.conjCoord_spec hm (heartCoord v), hσ v hv]
    group

end CFSG.OddStandard.SmallF3.Omega
