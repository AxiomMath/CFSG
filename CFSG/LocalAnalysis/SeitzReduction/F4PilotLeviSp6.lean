module

public import CFSG.Timmesfeld.LieEmbed.SpF4
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Universal.Unitary.Model

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
open scoped Matrix

section FieldMap

variable {K L : Type} [Field K] [Field L]

theorem map_symplecticGram (e : K →+* L) (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map e =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite]

theorem isSymplectic_map_iff (e : K →+* L) {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    (A.map e)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A.map e = Matrix.fromBlocks 0 1 (-1) 0 ↔
      Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [← map_symplecticGram e n, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective e.injective).eq_iff

theorem coe_map_GL (e : K →+* L) {ι : Type} [Fintype ι] [DecidableEq ι] (A : GL ι K) :
    ((Matrix.GeneralLinearGroup.map e A : GL ι L) : Matrix ι ι L) = (A : Matrix ι ι K).map e :=
  rfl

theorem map_GL_injective (e : K →+* L) {ι : Type} [Fintype ι] [DecidableEq ι] :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) e) := by
  intro A B h
  ext i j
  have h' := congrArg (fun g : GL ι L => (g : Matrix ι ι L) i j) h
  simp only [coe_map_GL, Matrix.map_apply] at h'
  exact e.injective h'

theorem isSymplectic_map_GL_iff (e : K →+* L) {n : ℕ} (A : GL (Fin n ⊕ Fin n) K) :
    (Matrix.GeneralLinearGroup.map e A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L)ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 *
          (Matrix.GeneralLinearGroup.map e A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) =
      Matrix.fromBlocks 0 1 (-1) 0 ↔
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [coe_map_GL]
  exact isSymplectic_map_iff e _

theorem map_statedSp_le (e : K →+* L) (n : ℕ) :
    (StatedSp n K).map (Matrix.GeneralLinearGroup.map e) ≤ StatedSp n L := by
  rw [StatedSp, MonoidHom.map_closure, closure_le]
  rintro _ ⟨A, hA, rfl⟩
  exact subset_closure ((isSymplectic_map_GL_iff e A).2 hA)

@[expose] noncomputable def statedSpMap (e : K →+* L) (n : ℕ) :
    ↥(StatedSp n K) →* ↥(StatedSp n L) :=
  ((Matrix.GeneralLinearGroup.map e).comp (StatedSp n K).subtype).codRestrict _ fun g =>
    map_statedSp_le e n ⟨g, g.2, rfl⟩

theorem coe_statedSpMap (e : K →+* L) (n : ℕ) (g : StatedSp n K) :
    ((statedSpMap e n g : StatedSp n L) : GL (Fin n ⊕ Fin n) L) =
      Matrix.GeneralLinearGroup.map e (g : GL (Fin n ⊕ Fin n) K) :=
  rfl

theorem statedSpMap_injective (e : K →+* L) (n : ℕ) : Function.Injective (statedSpMap e n) :=
  fun _ _ hgh => Subtype.ext (map_GL_injective e (congrArg Subtype.val hgh))

theorem statedSpMap_x (e : K →+* L) (n : ℕ) (γ : Fin n → ℤ) (c : K) :
    statedSpMap e n (Sp.x n K γ c) = Sp.x n L γ (e c) := by
  apply SpExtras.mat_injective
  rw [Sp.mat_x, SpExtras.mat_apply, coe_statedSpMap, coe_map_GL, ← SpExtras.mat_apply,
    Sp.mat_x]
  ext a b
  simp [Sp.Ex, Matrix.one_apply, apply_ite]

@[expose] noncomputable def statedSpCongr (e : K ≃+* L) (n : ℕ) :
    ↥(StatedSp n K) ≃* ↥(StatedSp n L) :=
  MonoidHom.toMulEquiv (statedSpMap (e : K →+* L) n) (statedSpMap (e.symm : L →+* K) n)
    (by
      ext g i j
      simp [coe_statedSpMap])
    (by
      ext g i j
      simp [coe_statedSpMap])

theorem coe_statedSpCongr (e : K ≃+* L) (n : ℕ) (g : StatedSp n K) :
    statedSpCongr e n g = statedSpMap (e : K →+* L) n g :=
  rfl

theorem statedSpCongr_x (e : K ≃+* L) (n : ℕ) (γ : Fin n → ℤ) (c : K) :
    statedSpCongr e n (Sp.x n K γ c) = Sp.x n L γ (e c) :=
  statedSpMap_x (e : K →+* L) n γ c

end FieldMap

section FieldFacts

theorem finite_of_natCard_eq_two_pow {α : Type*} {f : ℕ} (h : Nat.card α = 2 ^ f) : Finite α :=
  Nat.finite_of_card_ne_zero (by rw [h]; positivity)

variable {K : Type} [Field K] {f : ℕ}

theorem charP_two_of_natCard_eq_two_pow (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := finite_of_natCard_eq_two_pow hK
  let := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem one_le_of_natCard_eq_two_pow (hK : Nat.card K = 2 ^ f) : 1 ≤ f := by
  have := finite_of_natCard_eq_two_pow hK
  have h := Finite.one_lt_card (α := K)
  rw [hK] at h
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp at h
  · exact hf

theorem nonempty_ringEquiv_galoisField (hK : Nat.card K = 2 ^ f) :
    Nonempty (K ≃+* GaloisField 2 f) := by
  have := finite_of_natCard_eq_two_pow hK
  have hf := one_le_of_natCard_eq_two_pow hK
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (GaloisField 2 f)
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 f (by omega)])⟩

theorem sp6_field_condition [Finite K] :
    (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 3) ∨ (Nat.card K = 2 ∧ 3 ≤ 3) := by
  have hcard : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases (show Nat.card K = 2 ∨ Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h | h
  · exact Or.inr (Or.inr ⟨h, le_rfl⟩)
  · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
  · exact Or.inl (Or.inr h)

end FieldFacts

@[expose] def c3LeviRoots : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | IsRoot .F4 γ ∧ γ ⟨0, by decide⟩ = 0}

theorem mem_c3LeviRoots {γ : Fin (Tag.rank .F4) → ℤ} :
    γ ∈ c3LeviRoots ↔ IsRoot .F4 γ ∧ γ ⟨0, by decide⟩ = 0 :=
  Iff.rfl

theorem iform_highestRoot_F4 (γ : Fin (Tag.rank .F4) → ℤ) :
    Adjoint.iform γ (![2, 3, 4, 2] : Fin 4 → ℤ) = 2 * γ ⟨0, by decide⟩ := by
  have h : ∀ i : Fin (Tag.rank .F4),
      ∑ j, Tag.F4.symmetrizedCartan i j * (![2, 3, 4, 2] : Fin 4 → ℤ) j =
        if i = ⟨0, by decide⟩ then 2 else 0 := by
    decide +kernel
  simp only [Adjoint.iform, mul_assoc, ← Finset.mul_sum, h, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [mul_comm]

theorem mem_c3LeviRoots_iff_iform {γ : Fin (Tag.rank .F4) → ℤ} :
    γ ∈ c3LeviRoots ↔ IsRoot .F4 γ ∧ Adjoint.iform γ (![2, 3, 4, 2] : Fin 4 → ℤ) = 0 := by
  rw [mem_c3LeviRoots, iform_highestRoot_F4]
  exact and_congr_right fun _ => by omega

section Roots


theorem c3ToF4_mem_c3LeviRoots {v : Fin 3 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 3) ∅) :
    c3ToF4 v ∈ c3LeviRoots :=
  ⟨isRoot_c3ToF4 hv, c3ToF4_apply_zero v⟩

theorem c3ToF4_mem_c3LeviRoots_iff {v : Fin 3 → ℤ} :
    c3ToF4 v ∈ c3LeviRoots ↔ v ∈ roots (isFiniteType_cartanC 3) ∅ :=
  ⟨fun h => isRoot_c3ToF4_iff.1 h.1, c3ToF4_mem_c3LeviRoots⟩

theorem exists_c3ToF4_eq_of_mem_c3LeviRoots {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ c3LeviRoots) : ∃ v ∈ roots (isFiniteType_cartanC 3) ∅, c3ToF4 v = γ := by
  obtain ⟨v, hv, he⟩ := f4Roots_check γ (mem_rootFinset.2 hγ.1) hγ.2
  exact ⟨v, mem_roots_of_mem_c3Roots hv, he⟩

theorem image_c3ToF4_roots : c3ToF4 '' roots (isFiniteType_cartanC 3) ∅ = c3LeviRoots := by
  ext γ
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact c3ToF4_mem_c3LeviRoots hv
  · intro hγ
    obtain ⟨v, hv, rfl⟩ := exists_c3ToF4_eq_of_mem_c3LeviRoots hγ
    exact ⟨v, hv, rfl⟩

end Roots

section Levi


variable (K : Type) [Field K]

@[expose] noncomputable def C3Levi : Subgroup ↥(adjointGroup .F4 K) :=
  (rootSpan .F4 K c3LeviRoots).subgroupOf (adjointGroup .F4 K)

variable {K}

theorem mem_C3Levi_iff {g : adjointGroup .F4 K} :
    g ∈ C3Levi K ↔ (g : ModGL .F4 K) ∈ rootSpan .F4 K c3LeviRoots :=
  mem_subgroupOf

theorem map_subtype_C3Levi :
    (C3Levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K c3LeviRoots := by
  rw [C3Levi, subgroupOf_map_subtype, inf_of_le_left]
  exact iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem pinnedX_mem_C3Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ c3LeviRoots) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ C3Levi K :=
  mem_C3Levi_iff.2 (le_iSup₂ (f := fun γ (_ : γ ∈ c3LeviRoots) => rootSubgroup .F4 K γ) γ hγ
    (subset_closure ⟨c, rfl⟩))


theorem map_subtype_rootGroup {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((Adjoint.f4Datum K).rootGroup γ).map (adjointGroup .F4 K).subtype =
      rootSubgroup .F4 K γ := by
  change (Adjoint.rootGroup (Chevalley.rootOperatorFamily .F4) K γ).map _ = _
  rw [Adjoint.rootGroup_of_isRoot hγ,
    ← Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq (Chevalley.rootOperatorFamily .F4)
      K ⟨γ, hγ⟩, subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup γ)]

theorem C3Levi_eq_iSup_rootGroup :
    C3Levi K = ⨆ γ ∈ c3LeviRoots, (Adjoint.f4Datum K).rootGroup γ := by
  apply map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_subtype_C3Levi, rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hγ => (map_subtype_rootGroup hγ.1).symm

theorem rootGroup_le_C3Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ c3LeviRoots) :
    (Adjoint.f4Datum K).rootGroup γ ≤ C3Levi K := by
  rw [C3Levi_eq_iSup_rootGroup]
  exact le_iSup₂ (f := fun γ (_ : γ ∈ c3LeviRoots) => (Adjoint.f4Datum K).rootGroup γ) γ hγ

theorem f4Par_mem_C3Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ c3LeviRoots) (c : K) :
    Adjoint.f4Par K γ c ∈ C3Levi K :=
  rootGroup_le_C3Levi hγ (Adjoint.xPar_mem hγ.1 c)

theorem C3Levi_eq_closure :
    C3Levi K = closure {g | ∃ γ ∈ c3LeviRoots, ∃ c : K, Adjoint.f4Par K γ c = g} := by
  refine le_antisymm ?_ ((closure_le _).2 ?_)
  · rw [C3Levi_eq_iSup_rootGroup]
    refine iSup₂_le fun γ hγ g hg => ?_
    obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff hγ.1 g).1 hg
    exact subset_closure ⟨γ, hγ, c, rfl⟩
  · rintro _ ⟨γ, hγ, c, rfl⟩
    exact f4Par_mem_C3Levi hγ c

end Levi

section Iso


variable (K : Type) [Field K] [Finite K] [CharP K 2]

noncomputable def c3LeviHom : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K) :=
  (exists_spToF4 (K := K)).choose

variable {K}

theorem c3LeviHom_injective : Function.Injective (c3LeviHom K) :=
  (exists_spToF4 (K := K)).choose_spec.1

theorem c3LeviHom_x (γ : Fin 3 → ℤ) (c : K) :
    c3LeviHom K (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c :=
  (exists_spToF4 (K := K)).choose_spec.2 γ c

theorem map_c3LeviHom_rootGroup {v : Fin 3 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 3) ∅) :
    (Symplectic.rootGroup 3 K v).map (c3LeviHom K) =
      (Adjoint.f4Datum K).rootGroup (c3ToF4 v) := by
  apply SetLike.coe_injective
  rw [coe_map]
  exact (image_rootGroup_spToF4 c3LeviHom_x hv).symm

theorem range_c3LeviHom : (c3LeviHom K).range = C3Levi K := by
  have hmap : (c3LeviHom K).range = ⨆ v ∈ roots (isFiniteType_cartanC 3) ∅,
      (Symplectic.rootGroup 3 K v).map (c3LeviHom K) := by
    rw [MonoidHom.range_eq_map, ← (Symplectic.isCTGroupDatum 3 K).iSup_eq_top, Subgroup.map_iSup]
    refine iSup_congr fun v => ?_
    rw [Subgroup.map_iSup]
  rw [hmap, C3Levi_eq_iSup_rootGroup]
  refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun γ hγ => ?_)
  · rw [map_c3LeviHom_rootGroup hv]
    exact le_iSup₂ (f := fun γ (_ : γ ∈ c3LeviRoots) => (Adjoint.f4Datum K).rootGroup γ) _
      (c3ToF4_mem_c3LeviRoots hv)
  · obtain ⟨v, hv, rfl⟩ := exists_c3ToF4_eq_of_mem_c3LeviRoots hγ
    rw [← map_c3LeviHom_rootGroup hv]
    exact le_iSup₂ (f := fun v (_ : v ∈ roots (isFiniteType_cartanC 3) ∅) =>
      (Symplectic.rootGroup 3 K v).map (c3LeviHom K)) v hv

variable (K) in
@[expose] noncomputable def c3LeviEquiv : ↥(StatedSp 3 K) ≃* ↥(C3Levi K) :=
  (MonoidHom.ofInjective c3LeviHom_injective).trans (MulEquiv.subgroupCongr range_c3LeviHom)

theorem coe_c3LeviEquiv (g : StatedSp 3 K) :
    ((c3LeviEquiv K g : C3Levi K) : adjointGroup .F4 K) = c3LeviHom K g :=
  rfl

theorem c3LeviEquiv_x (γ : Fin 3 → ℤ) (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K γ c) : C3Levi K) : adjointGroup .F4 K) =
      Adjoint.f4Par K (c3ToF4 γ) c :=
  c3LeviHom_x γ c

theorem c3LeviEquiv_symm_f4Par {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅)
    (c : K) :
    (c3LeviEquiv K).symm ⟨Adjoint.f4Par K (c3ToF4 γ) c,
        f4Par_mem_C3Levi (c3ToF4_mem_c3LeviRoots hγ) c⟩ = Sp.x 3 K γ c := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (c3LeviEquiv_x γ c).symm

variable (K) in
@[expose] noncomputable def c3LeviEquivOfRingEquiv {L : Type} [Field L] (e : K ≃+* L) :
    ↥(C3Levi K) ≃* ↥(StatedSp 3 L) :=
  (c3LeviEquiv K).symm.trans (statedSpCongr e 3)

theorem c3LeviEquivOfRingEquiv_f4Par {L : Type} [Field L] (e : K ≃+* L) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : K) :
    c3LeviEquivOfRingEquiv K e ⟨Adjoint.f4Par K (c3ToF4 γ) c,
        f4Par_mem_C3Levi (c3ToF4_mem_c3LeviRoots hγ) c⟩ = Sp.x 3 L γ (e c) := by
  rw [c3LeviEquivOfRingEquiv, MulEquiv.trans_apply, c3LeviEquiv_symm_f4Par hγ, statedSpCongr_x]

theorem center_C3Levi_eq_bot : center (C3Levi K) = ⊥ := by
  rw [← map_center_eq (c3LeviEquiv K), center_statedSp_eq_bot, Subgroup.map_bot]

variable (K) in
noncomputable def c3LeviCenterQuotientEquiv :
    (↥(StatedSp 3 K) ⧸ center ↥(StatedSp 3 K)) ≃* ↥(C3Levi K) :=
  ((QuotientGroup.quotientMulEquivOfEq center_statedSp_eq_bot).trans
    QuotientGroup.quotientBot).trans (c3LeviEquiv K)

theorem isQuasisimple_C3Levi : CFSG.IsQuasisimple (C3Levi K) :=
  Unitary.isQuasisimple_of_mulEquiv (c3LeviEquiv K)
    (Symplectic.isQuasisimple 3 K (by norm_num) sp6_field_condition)

theorem isSimpleGroup_C3Levi : IsSimpleGroup (C3Levi K) := by
  have : IsSimpleGroup (C3Levi K ⧸ center (C3Levi K)) := (isQuasisimple_C3Levi (K := K)).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq center_C3Levi_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isQuasisimple_open_C3Levi : CFSG.Open.IsQuasisimple (C3Levi K) :=
  ⟨(isQuasisimple_C3Levi (K := K)).1.commutator_eq_top, (isQuasisimple_C3Levi (K := K)).2.1⟩

end Iso

section Main


variable {K : Type} [Field K] {f : ℕ}

theorem C3Levi_mulEquiv (hK : Nat.card K = 2 ^ f) :
    Nonempty (↥(C3Levi K) ≃* (lieUniversal .PSp 3 2 f Nat.prime_two).K) := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField hK
  exact ⟨c3LeviEquivOfRingEquiv K e⟩

theorem lieModel_C3Levi (hK : Nat.card K = 2 ^ f) :
    CFSG.Blueprint.LieModel (C3Levi K) .PSp 3 2 f := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have hf := one_le_of_natCard_eq_two_pow hK
  have hadm : StatedLieAdmissible .PSp 3 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have hmodel : CFSG.Blueprint.LieModel (↥(StatedSp 3 K) ⧸ center ↥(StatedSp 3 K)) .PSp 3 2 f :=
    Or.inl ⟨by decide, Symplectic.statedClassicalModel_center_quotient 3 K hadm hK⟩
  exact CurtisTits.lieModel_of_mulEquiv (c3LeviCenterQuotientEquiv K) hmodel

end Main

end CFSG.SeitzReduction.F4Pilot
