module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactEquivariance

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section FieldBlock

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

theorem spFieldMap_spFieldMap {F' : Type} [Field F'] (ι : K →+* F) (ι' : F →+* F')
    (x : StatedSp n K) : spFieldMap n ι' (spFieldMap n ι x) = spFieldMap n (ι'.comp ι) x := by
  refine mat_injective ?_
  rw [mat_spFieldMap, mat_spFieldMap, mat_spFieldMap]
  ext a b
  rfl

theorem spFieldMap_id (x : StatedSp n K) : spFieldMap n (RingHom.id K) x = x := by
  refine mat_injective ?_
  rw [mat_spFieldMap]
  ext a b
  rfl

theorem spFieldMap_id_mk {N : Finset (Fin n)} (x : spBlock K N) :
    (⟨spFieldMap n (RingHom.id K) x, spFieldMap_mem_spBlock (RingHom.id K) x.2⟩ : spBlock K N) =
      x :=
  Subtype.ext (spFieldMap_id (x : StatedSp n K))

@[expose] noncomputable def fieldBlockSp (σ : F ≃+* F) (N : Finset (Fin n)) :
    MulAut (spBlock F N) where
  toFun x := ⟨spFieldMap n σ.toRingHom x, spFieldMap_mem_spBlock σ.toRingHom x.2⟩
  invFun x := ⟨spFieldMap n σ.symm.toRingHom x, spFieldMap_mem_spBlock σ.symm.toRingHom x.2⟩
  left_inv x := by
    apply Subtype.ext
    change spFieldMap n σ.symm.toRingHom (spFieldMap n σ.toRingHom (x : StatedSp n F)) = x
    refine mat_injective ?_
    rw [mat_spFieldMap, mat_spFieldMap]
    ext a b
    simp
  right_inv x := by
    apply Subtype.ext
    change spFieldMap n σ.toRingHom (spFieldMap n σ.symm.toRingHom (x : StatedSp n F)) = x
    refine mat_injective ?_
    rw [mat_spFieldMap, mat_spFieldMap]
    ext a b
    simp
  map_mul' x y := Subtype.ext (map_mul (spFieldMap n σ.toRingHom) (x : StatedSp n F) y)

theorem coe_fieldBlockSp_apply (σ : F ≃+* F) (N : Finset (Fin n)) (x : spBlock F N) :
    ((fieldBlockSp σ N x : spBlock F N) : StatedSp n F) = spFieldMap n σ.toRingHom x :=
  rfl

theorem fieldBlockSp_spFieldMap {ι : K →+* F} {σ : F ≃+* F} (hσι : ∀ c, σ (ι c) = ι c)
    {N : Finset (Fin n)} {x : StatedSp n K} (hx : x ∈ spBlock K N) :
    fieldBlockSp σ N ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ =
      ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ := by
  apply Subtype.ext
  rw [coe_fieldBlockSp_apply]
  change spFieldMap n σ.toRingHom (spFieldMap n ι x) = spFieldMap n ι x
  refine mat_injective ?_
  rw [mat_spFieldMap, mat_spFieldMap]
  ext a b
  exact hσι _

end FieldBlock

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ}

structure FieldNeighbourParam (e : L ≃* StatedSp n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    (k : Fin n) where
  Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G
  range_eq : Φ.range = neighbourCore e k
  ker_le : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n)))
  N1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
    Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G)
  N2 : TorusEquivariant e ι {k}ᶜ ⊤ Φ
  N3 : ∀ x : spBlock F ({k}ᶜ : Finset (Fin n)),
    t * Φ x * t⁻¹ = Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x)

structure SwapNeighbourParam (e : L ≃* StatedSp n K) (t : G) (k : Fin n) where
  Ψ : spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)) →* G
  range_eq : Ψ.range = neighbourCore e k
  ker_le : Ψ.ker ≤ center (spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)))
  diag : ∀ x : spBlock K ({k}ᶜ : Finset (Fin n)), Ψ (x, x) = ((e.symm x : L) : G)
  N2 : TorusEquivariantProd e (RingHom.id K) {k}ᶜ ⊤ Ψ
  swap : ∀ x y : spBlock K ({k}ᶜ : Finset (Fin n)), t * Ψ (x, y) * t⁻¹ = Ψ (y, x)

variable {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {k : Fin n}

@[expose] noncomputable def FieldNeighbourParam.ofNormalized
    (Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G) (hrange : Φ.range = neighbourCore e k)
    (hker : Φ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n))))
    (hN1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
      Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G))
    (hN3 : ∀ x : spBlock F ({k}ᶜ : Finset (Fin n)),
      t * Φ x * t⁻¹ = Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x)) :
    FieldNeighbourParam e t ι σ k where
  Φ := Φ
  range_eq := hrange
  ker_le := hker
  N1 := hN1
  N2 := torusEquivariant_top_of_normalized e ι Φ hN1
    (hrange ▸ CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_le_centralizer _)
  N3 := hN3

@[expose] noncomputable def SwapNeighbourParam.ofNormalized
    (Ψ : spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)) →* G)
    (hrange : Ψ.range = neighbourCore e k)
    (hker : Ψ.ker ≤ center (spBlock K ({k}ᶜ : Finset (Fin n)) ×
      spBlock K ({k}ᶜ : Finset (Fin n))))
    (hdiag : ∀ x : spBlock K ({k}ᶜ : Finset (Fin n)), Ψ (x, x) = ((e.symm x : L) : G))
    (hswap : ∀ x y : spBlock K ({k}ᶜ : Finset (Fin n)), t * Ψ (x, y) * t⁻¹ = Ψ (y, x)) :
    SwapNeighbourParam e t k where
  Ψ := Ψ
  range_eq := hrange
  ker_le := hker
  diag := hdiag
  N2 := torusEquivariantProd_top_of_normalized e (RingHom.id K) Ψ
    (fun x hx => by rw [spFieldMap_id_mk ⟨x, hx⟩]; exact hdiag ⟨x, hx⟩)
    (hrange ▸ CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_le_centralizer _)
  swap := hswap

theorem FieldNeighbourParam.N1' (P : FieldNeighbourParam e t ι σ k)
    (x : spBlock K ({k}ᶜ : Finset (Fin n))) :
    P.Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι x.2⟩ = ((e.symm x : L) : G) :=
  P.N1 x x.2

theorem FieldNeighbourParam.commute_of_fix (P : FieldNeighbourParam e t ι σ k)
    (hσι : ∀ c, σ (ι c) = ι c) (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))) :
    t * ((e.symm x : L) : G) * t⁻¹ = ((e.symm x : L) : G) := by
  rw [← P.N1 x hx, P.N3, fieldBlockSp_spFieldMap hσι hx]

theorem SwapNeighbourParam.conj_inl (P : SwapNeighbourParam e t k)
    (x : spBlock K ({k}ᶜ : Finset (Fin n))) : t * P.Ψ (x, 1) * t⁻¹ = P.Ψ (1, x) :=
  P.swap x 1

theorem SwapNeighbourParam.commute_inl_inr (P : SwapNeighbourParam e t k)
    (x y : spBlock K ({k}ᶜ : Finset (Fin n))) : Commute (P.Ψ (x, 1)) (P.Ψ (1, y)) := by
  have hxy : ((x, 1) : spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n))) *
      (1, y) = (1, y) * (x, 1) := by
    ext <;> simp
  change P.Ψ (x, 1) * P.Ψ (1, y) = P.Ψ (1, y) * P.Ψ (x, 1)
  rw [← map_mul, hxy, map_mul]

theorem SwapNeighbourParam.mul_conj_inl (P : SwapNeighbourParam e t k)
    (x : spBlock K ({k}ᶜ : Finset (Fin n))) :
    P.Ψ (x, 1) * (t * P.Ψ (x, 1) * t⁻¹) = ((e.symm x : L) : G) := by
  rw [P.conj_inl, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, P.diag]

theorem FieldNeighbourParam.injective [CharP F 2] (P : FieldNeighbourParam e t ι σ k) :
    Function.Injective P.Φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact P.ker_le.trans (center_spBlock_eq_bot _).le

theorem SwapNeighbourParam.injective [CharP K 2] (P : SwapNeighbourParam e t k) :
    Function.Injective P.Ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  refine P.ker_le.trans fun z hz => ?_
  have h1 : z.1 ∈ center (spBlock K ({k}ᶜ : Finset (Fin n))) := mem_center_iff.2 fun g => by
    have := congrArg Prod.fst (mem_center_iff.1 hz (g, 1))
    simpa using this
  have h2 : z.2 ∈ center (spBlock K ({k}ᶜ : Finset (Fin n))) := mem_center_iff.2 fun g => by
    have := congrArg Prod.snd (mem_center_iff.1 hz (1, g))
    simpa using this
  rw [center_spBlock_eq_bot, mem_bot] at h1 h2
  rw [mem_bot]
  exact Prod.ext h1 h2

end Param

section Pieces

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

theorem FieldNeighbourParam.planeCore_eq_map (P : FieldNeighbourParam e t ι σ k)
    (hK : 4 ≤ Nat.card K) {I : Finset (Fin n)} (hk : k ∉ I) :
    planeCore e I = ((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ :=
  planeCore_eq_map_of_neighbourCore e ι hK hk P.Φ P.ker_le P.range_eq (P.N2.of_top e ι _)

theorem FieldNeighbourParam.pieceCore_tail_eq_map (P : FieldNeighbourParam e t ι σ k)
    (hK : 4 ≤ Nat.card K) {a : ℕ} (hka : k.val < a) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      ((spBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val)).subgroupOf
        (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ :=
  pieceCore_tail_eq_map_of_neighbourCore e ι hK hka P.Φ P.ker_le P.range_eq (P.N2.of_top e ι _)

theorem FieldNeighbourParam.pieceCore_string_eq_map (P : FieldNeighbourParam e t ι σ k)
    (hK : 4 ≤ Nat.card K) {a b : ℕ} (hab : a < b) (hb : b < n)
    (hk : k ∉ Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      ((siegelBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
        (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ :=
  pieceCore_string_eq_map_of_neighbourCore e ι hK hab hb hk P.Φ P.ker_le P.range_eq
    (P.N2.of_top e ι _)

theorem FieldNeighbourParam.nonempty_mulEquiv_planeCore [CharP F 2]
    (P : FieldNeighbourParam e t ι σ k) (hK : 4 ≤ Nat.card K) {I : Finset (Fin n)} (hk : k ∉ I) :
    Nonempty (StatedSp I.card F ≃* planeCore e I) :=
  nonempty_mulEquiv_planeCore_of_conjDiagSp e ι hK (subset_compl_singleton_of_notMem hk)
    (modelToG_rootTorusSp_le_planeTorusSp e hk) P.Φ P.ker_le P.range_eq (P.N2.of_top e ι _)

omit [Finite F] in
theorem SwapNeighbourParam.planeCore_eq_map [Finite K] (P : SwapNeighbourParam e t k)
    (hK : 4 ≤ Nat.card K) {I : Finset (Fin n)} (hk : k ∉ I) :
    planeCore e I = (((spBlock K I).subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).prod
      ((spBlock K I).subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n))))).map P.Ψ :=
  planeCore_eq_map_of_neighbourCore_prod e (RingHom.id K) hK hk P.Ψ P.ker_le P.range_eq
    (P.N2.mono e (RingHom.id K) le_top)

omit [Finite F] in
theorem SwapNeighbourParam.pieceCore_string_eq_map [Finite K] (P : SwapNeighbourParam e t k)
    (hK : 4 ≤ Nat.card K) {a b : ℕ} (hab : a < b) (hb : b < n)
    (hk : k ∉ Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      (((siegelBlock K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
          (spBlock K ({k}ᶜ : Finset (Fin n)))).prod
        ((siegelBlock K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
          (spBlock K ({k}ᶜ : Finset (Fin n))))).map P.Ψ :=
  pieceCore_string_eq_map_of_neighbourCore_prod e (RingHom.id K) hK hab hb hk P.Ψ P.ker_le
    P.range_eq (P.N2.mono e (RingHom.id K) le_top)

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
