module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Goldschmidt.Steps.G3aAut
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Walter.Bender1970.S2.Basic

public section

namespace CFSG.Goldschmidt

namespace G76

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_centralizer_of_bender
    {K T₀ B : Subgroup G} (hKq : CFSG.Open.IsQuasisimple K)
    (hQ : fusionIsBenderGroup (K ⧸ Subgroup.center K)) (P : Sylow 2 K)
    (hPT : (P : Subgroup K).map K.subtype = T₀)
    (hmap : (B.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center K)) =
      sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) :
        Sylow 2 (K ⧸ Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)))
    {α : G} (hαK : α ∈ Subgroup.normalizer (K : Set G))
    (hαT : α ∈ Subgroup.normalizer (T₀ : Set G))
    (hαB : α ∈ Subgroup.centralizer (B : Set G))
    (hαTB : ∀ t ∈ T₀, t⁻¹ * (α⁻¹ * t * α) ∈ B) :
    α ∈ T₀ ⊔ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  have hTK : T₀ ≤ K := by rw [← hPT]; exact Subgroup.map_subtype_le _
  have hmemP : ∀ p : K, p ∈ (P : Subgroup K) ↔ (p : G) ∈ T₀ := by
    intro p
    rw [← hPT]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      rwa [← Subtype.ext hqp]
  have hmem : ∀ x ∈ K, α⁻¹ * x * α ∈ K := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hαK) x).mp hx
    rwa [inv_inv] at this
  have hmem' : ∀ x ∈ K, α * x * α⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hαK x).mp hx
  let φ : MulAut K :=
    { toFun := fun x => ⟨α⁻¹ * x * α, hmem x x.2⟩
      invFun := fun x => ⟨α * x * α⁻¹, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ x : K, ((φ x : K) : G) = α⁻¹ * x * α := fun x => rfl
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set P' : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (K ⧸ Subgroup.center K)) = (P : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, h⟩ := G3a.exists_borelSetup hQ P'
  have hchar : (Subgroup.center K).map φ.toMonoidHom = Subgroup.center K :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set φ' : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) φ hchar with hφ'def
  have hφ' : ∀ x : K, φ' (π x) = π (φ x) := fun x => rfl
  have hTφ : ∀ p ∈ (P : Subgroup K), φ p ∈ (P : Subgroup K) := by
    intro p hp
    rw [hmemP, hφ]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hαT) p).mp ((hmemP p).mp hp)
    rwa [inv_inv] at this
  have hT' : ∀ t ∈ (P' : Subgroup (K ⧸ Subgroup.center K)),
      φ' t ∈ (P' : Subgroup (K ⧸ Subgroup.center K)) := by
    intro t ht
    rw [hP'] at ht ⊢
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨φ p, hTφ p hp, (hφ' p).symm⟩
  have hZ' : ∀ z ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)), φ' z = z := by
    intro z hz
    rw [← hmap] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    rw [hφ']
    congr 1
    apply Subtype.ext
    rw [hφ]
    have hc : (b : G) * α = α * b :=
      Subgroup.mem_centralizer_iff.mp hαB b (Subgroup.mem_subgroupOf.mp hb)
    calc α⁻¹ * b * α = α⁻¹ * ((b : G) * α) := by group
      _ = α⁻¹ * (α * b) := by rw [hc]
      _ = b := by group
  have hTZ' : ∀ t ∈ (P' : Subgroup (K ⧸ Subgroup.center K)),
      t⁻¹ * φ' t ∈ sylowCenter (P' : Subgroup (K ⧸ Subgroup.center K)) := by
    intro t ht
    rw [hP'] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    rw [hφ', ← map_inv, ← map_mul, ← hmap]
    refine ⟨p⁻¹ * φ p, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    have := hαTB (p : G) ((hmemP p).mp hp)
    simpa [hφ] using this
  obtain ⟨s', hs', hφs⟩ := h.eq_conj
    ((CFSG.ComponentClassification.AschbacherToolkit.BenderExt.benderData_of_isBenderGroup
      hQ).aut P') φ' hT' hZ' hTZ'
  rw [hP'] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  have hc : (s : G)⁻¹ * α⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    apply CFSG.Walter.mem_centralizer_of_commutator_mem_center hKq.1
    intro x hx
    have h1 : φ' (π ⟨x, hx⟩) = MulAut.conj (π s) (π ⟨x, hx⟩) := by rw [hφs]
    rw [hφ', MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    have h2 : (φ ⟨x, hx⟩)⁻¹ * (s * ⟨x, hx⟩ * s⁻¹) ∈ Subgroup.center K := by
      rw [← QuotientGroup.eq]
      exact h1
    set X : K := ⟨x, hx⟩ with hX
    set F := φ X with hF
    set w := F⁻¹ * (s * X * s⁻¹) with hw
    have hwc := Subgroup.mem_center_iff.mp h2
    have ht : s⁻¹ * F * s * X⁻¹ = w⁻¹ := by
      have e1 : s⁻¹ * F * s * X⁻¹ = X * (s⁻¹ * w⁻¹ * s) * X⁻¹ := by rw [hw]; group
      have e2 : s⁻¹ * w⁻¹ * s = w⁻¹ := by
        have := (Subgroup.center K).inv_mem h2
        have hc := Subgroup.mem_center_iff.mp this s
        calc s⁻¹ * w⁻¹ * s = s⁻¹ * (w⁻¹ * s) := by group
          _ = s⁻¹ * (s * w⁻¹) := by rw [hc]
          _ = w⁻¹ := by group
      rw [e1, e2]
      have hc := Subgroup.mem_center_iff.mp ((Subgroup.center K).inv_mem h2) X
      calc X * w⁻¹ * X⁻¹ = (w⁻¹ * X) * X⁻¹ := by rw [← hc]
        _ = w⁻¹ := by group
    refine ⟨s⁻¹ * F * s * X⁻¹, ht ▸ (Subgroup.center K).inv_mem h2, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hF, hφ, hX]
    group
  have hsT : (s : G) ∈ T₀ := (hmemP s).mp hs
  have e : α = ((s : G)⁻¹ * α⁻¹)⁻¹ * (s : G)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc))
    (Subgroup.mem_sup_left (T₀.inv_mem hsT))

end G76

end CFSG.Goldschmidt
