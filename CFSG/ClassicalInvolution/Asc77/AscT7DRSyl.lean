module

public import CFSG.ClassicalInvolution.Asc77.AscSixEta
public import CFSG.ClassicalInvolution.Asc77.AscT7DRGrp6

public section

namespace CFSG.ClassicalInvolution.Asc77.T7DR

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77.T7C2

variable {G : Type} [Group G]

theorem exists_gens_of_isQuatSub {R : Subgroup G} (h : IsQuatSub R) :
    ∃ a b : G, a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧ b * a * b⁻¹ = a⁻¹ ∧
      ∃ k : ℕ, b * b = a ^ k := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have hne : NeZero (2 ^ k) := inferInstance
  set a₀ : ↥R := e.symm (QuaternionGroup.a 1) with ha₀
  set b₀ : ↥R := e.symm (QuaternionGroup.xa 0) with hb₀
  have hinv : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k))⁻¹ = QuaternionGroup.a (-1) := by
    apply inv_eq_of_mul_eq_one_right
    simp
  have hq : (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by
    apply mul_inv_eq_iff_eq_mul.mpr
    rw [hinv]
    simp
  have hab : b₀ * a₀ * b₀⁻¹ = a₀⁻¹ := by
    simp only [ha₀, hb₀, ← map_mul, ← map_inv]
    exact congrArg e.symm hq
  have hbb : b₀ * b₀ = a₀ ^ (2 ^ k) := by
    have hq2 : (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) * QuaternionGroup.xa 0 =
        (QuaternionGroup.a 1) ^ (2 ^ k) := by
      rw [QuaternionGroup.a_one_pow]
      simp
    simp only [ha₀, hb₀, ← map_mul, ← map_pow]
    exact congrArg e.symm hq2
  have hgen : Subgroup.closure ({a₀, b₀} : Set ↥R) = ⊤ := by
    rw [eq_top_iff]
    intro r _
    obtain ⟨q, hqr⟩ : ∃ q, e.symm q = r := ⟨e r, by simp⟩
    rw [← hqr]
    cases q with
    | a i =>
      have : (QuaternionGroup.a i : QuaternionGroup (2 ^ k)) = (QuaternionGroup.a 1) ^ i.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [this, map_pow]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [ha₀])) _
    | xa i =>
      have : (QuaternionGroup.xa i : QuaternionGroup (2 ^ k)) =
          QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ i.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
        simp
      rw [this, map_mul, map_pow]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp [hb₀]))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [ha₀])) _)
  refine ⟨(a₀ : G), (b₀ : G), a₀.2, b₀.2, ?_, ?_, ⟨2 ^ k, ?_⟩⟩
  · have h1 := congrArg (Subgroup.map R.subtype) hgen
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  · have := congrArg Subtype.val hab
    simpa using this
  · have := congrArg Subtype.val hbb
    simpa using this

theorem closure_eq_top_of_image {T : Subgroup G} {s : Set ↥T}
    (h : Subgroup.closure (T.subtype '' s) = T) : Subgroup.closure s = ⊤ := by
  apply Subgroup.map_injective T.subtype_injective
  rw [MonoidHom.map_closure, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem twoSubgroupsFourGenerated_of_sylow [Finite G] (S : Sylow 2 G)
    (h : ∀ H : Subgroup G, H ≤ (S : Subgroup G) → GenLE H 4) : TwoSubgroupsFourGenerated G := by
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow Q S
  have hle : conjSub g P ≤ (S : Subgroup G) := hg ▸ conjSub_mono hPQ
  have h4 := GenLE.conj (h _ hle) g⁻¹
  have hP' : (conjSub g P).map (MulAut.conj g⁻¹).toMonoidHom = P := conjSub_inv_conjSub g P
  rw [hP'] at h4
  exact h4

theorem genLE_four_of_omega5_sub [Finite G] {T : Subgroup G} {a b t : G} (ha : a ∈ T)
    (hb : b ∈ T) (ht : t ∈ T) (hT : Subgroup.closure ({a, b, t} : Set G) = T)
    (hbab : b * a * b⁻¹ = a⁻¹) (hb2 : ∃ k : ℤ, b * b = a ^ k) (ht2 : t * t = 1)
    (h5 : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a) (h6 : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b)
    {H : Subgroup G} (hH : H ≤ T) : GenLE H 4 := by
  have hS : Subgroup.closure ({(⟨a, ha⟩ : ↥T), ⟨b, hb⟩, ⟨t, ht⟩} : Set ↥T) = ⊤ := by
    apply closure_eq_top_of_image
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    exact hT
  obtain ⟨k, hk⟩ := hb2
  have key := genLE_four_of_omega5 (a := (⟨a, ha⟩ : ↥T)) (b := ⟨b, hb⟩) (t := ⟨t, ht⟩) hS
    (Subtype.ext (by simpa using hbab)) ⟨k, Subtype.ext (by simpa using hk)⟩
    (Subtype.ext (by simpa using ht2)) (Subtype.ext (by simpa using h5))
    (Subtype.ext (by simpa using h6)) (H.subgroupOf T)
  exact GenLE.of_subgroupOf hH key

theorem genLE_four_of_omega6_sub [Finite G] {T : Subgroup G} {a b s t : G} (ha : a ∈ T)
    (hb : b ∈ T) (hs : s ∈ T) (ht : t ∈ T) (hT : Subgroup.closure ({a, b, s, t} : Set G) = T)
    (hbab : b * a * b⁻¹ = a⁻¹) (hb2 : ∃ k : ℤ, b * b = a ^ k) (ht2 : t * t = 1)
    (hs2 : s * s = 1) (hst : s * t = t * s) (hsa : s * a * s⁻¹ = a⁻¹)
    (hsb : s * b * s⁻¹ = b * a) (h5a : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a)
    (h5b : a * (t * b * t⁻¹) = (t * b * t⁻¹) * a) (h5c : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b)
    (h5d : b * (t * b * t⁻¹) = (t * b * t⁻¹) * b) (h6 : t * (b * b) * t⁻¹ = b * b)
    {H : Subgroup G} (hH : H ≤ T) : GenLE H 4 := by
  have hS : Subgroup.closure
      ({(⟨a, ha⟩ : ↥T), ⟨b, hb⟩, ⟨s, hs⟩, ⟨t, ht⟩} : Set ↥T) = ⊤ := by
    apply closure_eq_top_of_image
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    exact hT
  obtain ⟨k, hk⟩ := hb2
  have key := genLE_four_of_omega6 (a := (⟨a, ha⟩ : ↥T)) (b := ⟨b, hb⟩) (s := ⟨s, hs⟩)
    (t := ⟨t, ht⟩) hS (Subtype.ext (by simpa using hbab)) ⟨k, Subtype.ext (by simpa using hk)⟩
    (Subtype.ext (by simpa using ht2)) (Subtype.ext (by simpa using hs2))
    (Subtype.ext (by simpa using hst)) (Subtype.ext (by simpa using hsa))
    (Subtype.ext (by simpa using hsb)) (Subtype.ext (by simpa using h5a))
    (Subtype.ext (by simpa using h5b)) (Subtype.ext (by simpa using h5c))
    (Subtype.ext (by simpa using h5d)) (Subtype.ext (by simpa using h6)) (H.subgroupOf T)
  exact GenLE.of_subgroupOf hH key

end CFSG.ClassicalInvolution.Asc77.T7DR
