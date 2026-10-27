module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.LieEmbed TauCeti.GLSymplecticFin
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbedMat spIncl mat_spEmbed
  spEmbed_injective spIncl_mul_single_mul_transpose)

section Embed

variable {K : Type} [Field K]

@[expose] def succIdx : RootSubgroupIndex 2 → RootSubgroupIndex 3
  | .positiveLong i => .positiveLong i.succ
  | .negativeLong i => .negativeLong i.succ
  | .difference i j h => .difference i.succ j.succ fun e => h (Fin.succ_injective _ e)
  | .positiveSum i j h => .positiveSum i.succ j.succ (Fin.succ_lt_succ_iff.2 h)
  | .negativeSum i j h => .negativeSum i.succ j.succ (Fin.succ_lt_succ_iff.2 h)

theorem spIncl_mul_E_mul_transpose (r : RootSubgroupIndex 2) :
    spIncl (K := K) (Fin.succ : Fin 2 → Fin 3) * E K r *
        (spIncl (K := K) (Fin.succ : Fin 2 → Fin 3))ᵀ = E K (succIdx r) := by
  cases r <;>
    simp [E, succIdx, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      spIncl_mul_single_mul_transpose]

theorem spEmbed_elt (r : RootSubgroupIndex 2) (c : K) :
    spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2) (elt r c) = elt (succIdx r) c := by
  apply mat_injective
  rw [mat_spEmbed, mat_elt, mat_elt, spEmbedMat, add_sub_cancel_left, Matrix.mul_smul,
    Matrix.smul_mul, spIncl_mul_E_mul_transpose]

@[expose] def shiftC2 : (Fin 2 → ℤ) →+ (Fin 3 → ℤ) where
  toFun v := ![0, v 0, v 1]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    funext i
    fin_cases i <;> simp

theorem shiftC2_apply (v : Fin 2 → ℤ) : shiftC2 v = ![0, v 0, v 1] :=
  rfl

theorem toStd_shiftC2 (v : Fin 2 → ℤ) :
    toStd 3 (shiftC2 v) = ![0, toStd 2 v 0, toStd 2 v 1] := by
  funext a
  fin_cases a <;> simp [toStd, shiftC2]

theorem stdVec_succIdx (r : RootSubgroupIndex 2) :
    stdVec (succIdx r) = ![0, stdVec r 0, stdVec r 1] := by
  funext a
  cases r with
  | positiveLong i => fin_cases i <;> fin_cases a <;> rfl
  | negativeLong i => fin_cases i <;> fin_cases a <;> rfl
  | difference i j h => fin_cases i <;> fin_cases j <;> fin_cases a <;> rfl
  | positiveSum i j h => fin_cases i <;> fin_cases j <;> fin_cases a <;> rfl
  | negativeSum i j h => fin_cases i <;> fin_cases j <;> fin_cases a <;> rfl

theorem stdVec_succIdx_eq {r : RootSubgroupIndex 2} {v : Fin 2 → ℤ}
    (hr : stdVec r = toStd 2 v) : stdVec (succIdx r) = toStd 3 (shiftC2 v) := by
  rw [stdVec_succIdx, toStd_shiftC2, hr]

theorem shiftC2_mem_roots {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    shiftC2 v ∈ roots (isFiniteType_cartanC 3) ∅ := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  exact mem_roots_of_stdVec (stdVec_succIdx_eq hr)

theorem map_spEmbed_rootGroup {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    (Symplectic.rootGroup 2 K v).map (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)) =
      Symplectic.rootGroup 3 K (shiftC2 v) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  exact map_rootGroup_of_elt _ Function.surjective_id (spEmbed_elt r) hr (stdVec_succIdx_eq hr)

end Embed

@[expose] def c2ToF4 : (Fin 2 → ℤ) →+ (Fin (Tag.rank .F4) → ℤ) :=
  c3ToF4.comp shiftC2

theorem c2ToF4_apply (v : Fin 2 → ℤ) : c2ToF4 v = c3ToF4 (shiftC2 v) :=
  rfl

@[expose] def c2Roots : List (Fin 2 → ℤ) :=
  [![1, 0], ![0, 1], ![1, 1], ![2, 1], ![-1, 0], ![0, -1], ![-1, -1], ![-2, -1]]

@[expose] def rsi2 : List (RootSubgroupIndex 2) :=
  [.positiveLong 0, .positiveLong 1, .negativeLong 0, .negativeLong 1, .difference 0 1 (by decide),
    .difference 1 0 (by decide), .positiveSum 0 1 (by decide), .negativeSum 0 1 (by decide)]

theorem c2Roots_check : ∀ v ∈ c2Roots, ∃ r ∈ rsi2, stdVec r = toStd 2 v := by
  decide

theorem mem_roots_of_mem_c2Roots {v : Fin 2 → ℤ} (hv : v ∈ c2Roots) :
    v ∈ roots (isFiniteType_cartanC 2) ∅ := by
  obtain ⟨r, -, hr⟩ := c2Roots_check v hv
  exact mem_roots_of_stdVec hr

theorem c3Roots_shift_check : ∀ w ∈ c3Roots, w 0 = 0 → ∃ v ∈ c2Roots, shiftC2 v = w := by
  decide

section Roots


theorem c2ToF4_mem_b2LeviRoots {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    c2ToF4 v ∈ b2LeviRoots :=
  mem_b2LeviRoots.2 ⟨isRoot_c3ToF4 (shiftC2_mem_roots hv), c3ToF4_apply_zero (shiftC2 v), rfl⟩

theorem exists_c2ToF4_eq_of_mem_b2LeviRoots {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ b2LeviRoots) : ∃ v ∈ roots (isFiniteType_cartanC 2) ∅, c2ToF4 v = γ := by
  obtain ⟨hγr, hγ0, hγ3⟩ := mem_b2LeviRoots.1 hγ
  obtain ⟨w, hw, rfl⟩ := f4Roots_check γ (mem_rootFinset.2 hγr) hγ0
  have hw0 : w 0 = 0 := hγ3
  obtain ⟨v, hv, rfl⟩ := c3Roots_shift_check w hw hw0
  exact ⟨v, mem_roots_of_mem_c2Roots hv, rfl⟩

theorem image_c2ToF4_roots : c2ToF4 '' roots (isFiniteType_cartanC 2) ∅ = b2LeviRoots := by
  ext γ
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact c2ToF4_mem_b2LeviRoots hv
  · intro hγ
    obtain ⟨v, hv, rfl⟩ := exists_c2ToF4_eq_of_mem_b2LeviRoots hγ
    exact ⟨v, hv, rfl⟩

end Roots

section Levi


variable {K : Type} [Field K]

theorem mem_B2Levi_iff {g : adjointGroup .F4 K} :
    g ∈ B2Levi K ↔ (g : ModGL .F4 K) ∈ rootSpan .F4 K b2LeviRoots :=
  mem_subgroupOf

theorem map_subtype_B2Levi :
    (B2Levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K b2LeviRoots := by
  rw [B2Levi, subgroupOf_map_subtype, inf_of_le_left]
  exact iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem B2Levi_le_C3Levi : B2Levi K ≤ C3Levi K := by
  have hle : rootSpan .F4 K b2LeviRoots ≤ rootSpan .F4 K c3LeviRoots :=
    biSup_mono fun _ hγ => b2LeviRoots_subset_c3LeviRoots hγ
  exact fun _ hg => mem_C3Levi_iff.2 (hle (mem_B2Levi_iff.1 hg))


theorem B2Levi_eq_iSup_rootGroup :
    B2Levi K = ⨆ γ ∈ b2LeviRoots, (Adjoint.f4Datum K).rootGroup γ := by
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_subtype_B2Levi, rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hγ => (map_subtype_rootGroup (mem_b2LeviRoots.1 hγ).1).symm

end Levi

section Iso


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def b2LeviHom : ↥(StatedSp 2 K) →* ↥(adjointGroup .F4 K) :=
  (c3LeviHom K).comp (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2))

variable {K}

theorem b2LeviHom_apply (g : StatedSp 2 K) :
    b2LeviHom K g = c3LeviHom K (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2) g) :=
  rfl

theorem b2LeviHom_injective : Function.Injective (b2LeviHom K) :=
  c3LeviHom_injective.comp (spEmbed_injective (Fin.succ_injective 2))

theorem map_b2LeviHom_rootGroup {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    (Symplectic.rootGroup 2 K v).map (b2LeviHom K) =
      (Adjoint.f4Datum K).rootGroup (c2ToF4 v) := by
  rw [b2LeviHom, ← Subgroup.map_map, map_spEmbed_rootGroup hv,
    map_c3LeviHom_rootGroup (shiftC2_mem_roots hv), c2ToF4_apply]

theorem range_b2LeviHom : (b2LeviHom K).range = B2Levi K := by
  have hmap : (b2LeviHom K).range = ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅,
      (Symplectic.rootGroup 2 K v).map (b2LeviHom K) := by
    rw [MonoidHom.range_eq_map, ← (Symplectic.isCTGroupDatum 2 K).iSup_eq_top, Subgroup.map_iSup]
    refine iSup_congr fun v => ?_
    rw [Subgroup.map_iSup]
  rw [hmap, B2Levi_eq_iSup_rootGroup]
  refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun γ hγ => ?_)
  · rw [map_b2LeviHom_rootGroup hv]
    exact le_iSup₂ (f := fun γ (_ : γ ∈ b2LeviRoots) => (Adjoint.f4Datum K).rootGroup γ) _
      (c2ToF4_mem_b2LeviRoots hv)
  · obtain ⟨v, hv, rfl⟩ := exists_c2ToF4_eq_of_mem_b2LeviRoots hγ
    rw [← map_b2LeviHom_rootGroup hv]
    exact le_iSup₂ (f := fun v (_ : v ∈ roots (isFiniteType_cartanC 2) ∅) =>
      (Symplectic.rootGroup 2 K v).map (b2LeviHom K)) v hv

variable (K) in
@[expose] noncomputable def b2LeviEquiv : ↥(StatedSp 2 K) ≃* ↥(B2Levi K) :=
  (MonoidHom.ofInjective b2LeviHom_injective).trans (MulEquiv.subgroupCongr range_b2LeviHom)

theorem coe_b2LeviEquiv (g : StatedSp 2 K) :
    ((b2LeviEquiv K g : B2Levi K) : adjointGroup .F4 K) = b2LeviHom K g :=
  rfl

theorem center_B2Levi_eq_bot : center (B2Levi K) = ⊥ := by
  rw [← map_center_eq (b2LeviEquiv K), center_statedSp_eq_bot_of_charTwo, Subgroup.map_bot]

theorem isSimpleGroup_B2Levi (hq : 4 ≤ Nat.card K) : IsSimpleGroup (B2Levi K) := by
  have hqs : CFSG.IsQuasisimple (B2Levi K) :=
    Unitary.isQuasisimple_of_mulEquiv (b2LeviEquiv K)
      (Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr hq)))
  have : IsSimpleGroup (B2Levi K ⧸ center (B2Levi K)) := hqs.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq center_B2Levi_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

variable (K) in
@[expose] noncomputable def b2LeviEquivOfRingEquiv {L : Type} [Field L] (e : K ≃+* L) :
    ↥(B2Levi K) ≃* ↥(StatedSp 2 L) :=
  (b2LeviEquiv K).symm.trans (statedSpCongr e 2)

end Iso

section Main


variable {K : Type} [Field K] {f : ℕ}

theorem B2Levi_mulEquiv (hK : Nat.card K = 2 ^ f) :
    Nonempty (↥(B2Levi K) ≃* (lieUniversal .PSp 2 2 f Nat.prime_two).K) := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField hK
  exact ⟨b2LeviEquivOfRingEquiv K e⟩

end Main

end CFSG.SeitzReduction.F4Pilot
