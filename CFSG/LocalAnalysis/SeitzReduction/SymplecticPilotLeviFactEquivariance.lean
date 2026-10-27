module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section FieldMap

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

theorem gram_map (ι : K →+* F) : (gram K n).map ι = gram F n := by
  ext a b
  rw [Matrix.map_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, apply_ite ι, map_zero]
  congr 1
  rcases a with i | i <;> simp [sgn]

variable (n) in
@[expose] noncomputable def spFieldMap (ι : K →+* F) : StatedSp n K →* StatedSp n F :=
  ((Matrix.GeneralLinearGroup.map ι).comp (StatedSp n K).subtype).codRestrict _ fun g =>
    mem_statedSp_iff.2 (by
      have h := congrArg (fun M => Matrix.map M ι) (mem_statedSp_iff.1 g.2)
      simp only [Matrix.map_mul, Matrix.transpose_map, gram_map] at h
      exact h)

theorem mat_spFieldMap (ι : K →+* F) (x : StatedSp n K) :
    mat n F (spFieldMap n ι x) = (mat n K x).map ι :=
  rfl

theorem spFieldMap_mem_spBlock (ι : K →+* F) {N : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ spBlock K N) : spFieldMap n ι x ∈ spBlock F N := by
  intro a b hab
  rw [mat_spFieldMap, Matrix.map_apply, hx a b hab]
  by_cases h : a = b
  · rw [h, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem spFieldMap_diagSp (ι : K →+* F) (t : Fin n → Kˣ) :
    spFieldMap n ι (diagSp K n t) = diagSp F n (liftParam ι t) := by
  refine mat_injective ?_
  rw [mat_spFieldMap, mat_diagSp, mat_diagSp, Matrix.diagonal_map (map_zero ι)]
  congr 1
  funext a
  rw [diagSpEntry_liftParam]

theorem liftParam_mul (ι : K →+* F) (t s : Fin n → Kˣ) :
    liftParam ι (t * s) = liftParam ι t * liftParam ι s := by
  funext i
  simp [liftParam]

theorem liftParam_mem_planeTorusParam (ι : K →+* F) {I : Finset (Fin n)} {t : Fin n → Kˣ}
    (ht : t ∈ planeTorusParam K I) : liftParam ι t ∈ planeTorusParam F I := fun i hi => by
  simp [liftParam, ht i hi]

theorem diagSp_mem_spBlock_compl {I : Finset (Fin n)} {t : Fin n → Kˣ}
    (ht : t ∈ planeTorusParam K I) : diagSp K n t ∈ spBlock K Iᶜ := by
  intro a b hab
  rw [mat_diagSp_apply]
  by_cases h : a = b
  · subst h
    have ha : a ∈ planeCoords I := by
      by_contra ha
      exact hab ⟨by rw [planeCoords_compl]; exact ha, by rw [planeCoords_compl]; exact ha⟩
    simp only [↓reduceIte]
    rw [diagSpEntry_eq_one_of_mem_planeTorusParam ht ha, Matrix.one_apply_eq]
  · simp only [h, ↓reduceIte]
    rw [Matrix.one_apply_ne h]

end FieldMap

section Normalized

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

theorem conjDiagSp_eq_conj_spFieldMap {k : Fin n} (t : Fin n → Kˣ)
    (x : spBlock F ({k}ᶜ : Finset (Fin n))) :
    ((conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam ι t) x : spBlock F ({k}ᶜ : Finset (Fin n))) :
        StatedSp n F) =
      spFieldMap n ι (diagSp K n (t * (Pi.mulSingle k (t k))⁻¹)) * (x : StatedSp n F) *
        (spFieldMap n ι (diagSp K n (t * (Pi.mulSingle k (t k))⁻¹)))⁻¹ := by
  set u : Fin n → Kˣ := Pi.mulSingle k (t k) with hu
  set t' : Fin n → Kˣ := t * u⁻¹ with ht'
  have hut : u * t' = t := by rw [ht', mul_comm, inv_mul_cancel_right]
  have hu' : u ∈ planeTorusParam K ({k}ᶜ : Finset (Fin n)) := fun i hi => by
    have hik : i ≠ k := by simpa using hi
    simp [hu, hik]
  have hdu : diagSp F n (liftParam ι u) ∈ spBlock F {k} := by
    have h := diagSp_mem_spBlock_compl (liftParam_mem_planeTorusParam ι hu')
    rwa [compl_compl] at h
  have hcomm : Commute (diagSp F n (liftParam ι u)) (x : StatedSp n F) :=
    commute_of_mem_spBlock_of_disjoint disjoint_compl_right hdu x.2
  rw [coe_conjDiagSp_apply, ← hut, liftParam_mul, map_mul, spFieldMap_diagSp,
    (commute_diagSp_diagSp (liftParam ι u) (liftParam ι t')).eq, mul_inv_rev,
    show ∀ a b c : StatedSp n F, b * a * c * (a⁻¹ * b⁻¹) = b * (a * c * a⁻¹) * b⁻¹
      from fun a b c => by group, hcomm.eq, mul_inv_cancel_right]

theorem torusEquivariant_top_of_normalized {k : Fin n}
    (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G))
    (hcent : Φ.range ≤ centralizer (modelToG e (rootTorusSp K k) : Set G)) :
    TorusEquivariant e ι {k}ᶜ ⊤ Φ := by
  intro t _ x
  set u : Fin n → Kˣ := Pi.mulSingle k (t k) with hu
  set t' : Fin n → Kˣ := t * u⁻¹ with ht'
  have hut : u * t' = t := by rw [ht', mul_comm, inv_mul_cancel_right]
  have ht'k : t' ∈ planeTorusParam K {k} := fun i hi => by
    rw [Finset.mem_singleton] at hi
    subst hi
    simp [ht', hu]
  have hdt' : diagSp K n t' ∈ spBlock K ({k}ᶜ : Finset (Fin n)) := diagSp_mem_spBlock_compl ht'k
  set y : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    ⟨spFieldMap n ι (diagSp K n t'), spFieldMap_mem_spBlock ι hdt'⟩ with hy
  have hconj : conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam ι t) x = y * x * y⁻¹ :=
    Subtype.ext (conjDiagSp_eq_conj_spFieldMap ι t x)
  have hΦy : Φ y = ((e.symm (diagSp K n t') : L) : G) := hN1 _ hdt'
  set Eu := ((e.symm (diagSp K n u) : L) : G) with hEu
  set Et := ((e.symm (diagSp K n t') : L) : G) with hEt
  have hE : ((e.symm (diagSp K n t) : L) : G) = Eu * Et := by
    rw [← hut, map_mul, map_mul, Subgroup.coe_mul]
  have hc : Eu ∈ modelToG e (rootTorusSp K k) := symm_mem_modelToG e ⟨t k, rfl⟩
  have hz : Φ (y * x * y⁻¹) ∈ Φ.range := ⟨_, rfl⟩
  have hcz := mem_centralizer_iff.1 (hcent hz) _ hc
  rw [map_mul, map_mul, map_inv, hΦy] at hcz
  rw [hconj, map_mul, map_mul, map_inv, hΦy, hE]
  calc Et * Φ x * Et⁻¹ = Eu * (Et * Φ x * Et⁻¹) * Eu⁻¹ := by rw [hcz, mul_inv_cancel_right]
    _ = Eu * Et * Φ x * (Eu * Et)⁻¹ := by group

theorem planeCore_eq_map_of_normalized [Finite G] [Finite F] (hK : 4 ≤ Nat.card K) {k : Fin n}
    {I : Finset (Fin n)} (hk : k ∉ I) (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Φ.range = neighbourCore e k)
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G)) :
    planeCore e I = ((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map Φ :=
  planeCore_eq_map_of_neighbourCore e ι hK hk Φ hker hrange
    ((torusEquivariant_top_of_normalized e ι Φ hN1 (hrange ▸
      CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_le_centralizer _)).of_top e ι _)

theorem pieceCore_string_eq_map_of_normalized [Finite G] [Finite F] (hK : 4 ≤ Nat.card K)
    {a b : ℕ} (hab : a < b) (hb : b < n) {k : Fin n}
    (hk : k ∉ Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)
    (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Φ.range = neighbourCore e k)
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G)) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      ((siegelBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
        (spBlock F ({k}ᶜ : Finset (Fin n)))).map Φ :=
  pieceCore_string_eq_map_of_neighbourCore e ι hK hab hb hk Φ hker hrange
    ((torusEquivariant_top_of_normalized e ι Φ hN1 (hrange ▸
      CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_le_centralizer _)).of_top e ι _)

end Normalized

section NormalizedProd

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

theorem torusEquivariantProd_top_of_normalized {k : Fin n}
    (Ψ : spBlock F ({k}ᶜ : Finset (Fin n)) × spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Ψ (⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩,
        ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩) = ((e.symm x : L) : G))
    (hcent : Ψ.range ≤ centralizer (modelToG e (rootTorusSp K k) : Set G)) :
    TorusEquivariantProd e ι {k}ᶜ ⊤ Ψ := by
  intro t _ x
  set u : Fin n → Kˣ := Pi.mulSingle k (t k) with hu
  set t' : Fin n → Kˣ := t * u⁻¹ with ht'
  have hut : u * t' = t := by rw [ht', mul_comm, inv_mul_cancel_right]
  have ht'k : t' ∈ planeTorusParam K {k} := fun i hi => by
    rw [Finset.mem_singleton] at hi
    subst hi
    simp [ht', hu]
  have hdt' : diagSp K n t' ∈ spBlock K ({k}ᶜ : Finset (Fin n)) := diagSp_mem_spBlock_compl ht'k
  set y₀ : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    ⟨spFieldMap n ι (diagSp K n t'), spFieldMap_mem_spBlock ι hdt'⟩ with hy₀
  have hconj : (conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam ι t) x.1,
      conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam ι t) x.2) = (y₀, y₀) * x * (y₀, y₀)⁻¹ := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact conjDiagSp_eq_conj_spFieldMap ι t x.1
    · exact conjDiagSp_eq_conj_spFieldMap ι t x.2
  have hΨy : Ψ (y₀, y₀) = ((e.symm (diagSp K n t') : L) : G) := hN1 _ hdt'
  set Eu := ((e.symm (diagSp K n u) : L) : G) with hEu
  set Et := ((e.symm (diagSp K n t') : L) : G) with hEt
  have hE : ((e.symm (diagSp K n t) : L) : G) = Eu * Et := by
    rw [← hut, map_mul, map_mul, Subgroup.coe_mul]
  have hc : Eu ∈ modelToG e (rootTorusSp K k) := symm_mem_modelToG e ⟨t k, rfl⟩
  have hz : Ψ ((y₀, y₀) * x * (y₀, y₀)⁻¹) ∈ Ψ.range := ⟨_, rfl⟩
  have hcz := mem_centralizer_iff.1 (hcent hz) _ hc
  rw [map_mul, map_mul, map_inv, hΨy] at hcz
  rw [hconj, map_mul, map_mul, map_inv, hΨy, hE]
  calc Et * Ψ x * Et⁻¹ = Eu * (Et * Ψ x * Et⁻¹) * Eu⁻¹ := by rw [hcz, mul_inv_cancel_right]
    _ = Eu * Et * Ψ x * (Eu * Et)⁻¹ := by group

theorem planeCore_eq_map_of_normalized_prod [Finite G] [Finite F] (hK : 4 ≤ Nat.card K)
    {k : Fin n} {I : Finset (Fin n)} (hk : k ∉ I)
    (Ψ : spBlock F ({k}ᶜ : Finset (Fin n)) × spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Ψ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n)) ×
      spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Ψ.range = neighbourCore e k)
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Ψ (⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩,
        ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩) = ((e.symm x : L) : G)) :
    planeCore e I = (((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).prod
      ((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n))))).map Ψ :=
  planeCore_eq_map_of_neighbourCore_prod e ι hK hk Ψ hker hrange
    ((torusEquivariantProd_top_of_normalized e ι Ψ hN1 (hrange ▸
      CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_le_centralizer _)).mono e ι le_top)

end NormalizedProd

end CFSG.SeitzReduction.SymplecticPilot
