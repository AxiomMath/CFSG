module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusSetup4
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 Matrix Multiplicative

variable {V : Type} [CommGroup V]

@[expose] noncomputable def plusNil {n : ℕ} (B : SLq n) : Matrix (Fin 2) (Fin 2) (Fq n) :=
  (B : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ - 1

theorem plus_mem_fixV_zpowers_iff {b : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers b) ↔ b v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

namespace PlusCoord

variable {Y : Subgroup (MulAut V)} {n : ℕ} (c : PlusCoord Y n)

theorem ι₂_vec_eq (B : SLq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.ι₂ B (c.vec M) = c.vec (M + M * plusNil B) := by
  rw [c.ι₂_vec, plusNil, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

theorem ι₂_vec_mul_inv (B : SLq n) (X : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.ι₂ B (c.vec X) * (c.vec X)⁻¹ = c.vec (X * plusNil B) := by
  rw [c.ι₂_vec_eq, c.vec_add, mul_inv_cancel_comm]

theorem ι₂_fix_iff (B : SLq n) {w : V} (hw : w ∈ fixV Y) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.ι₂ B (w * c.vec M) = w * c.vec M ↔ M * plusNil B = 0 := by
  rw [map_mul, hw _ (c.ι₂_mem B), c.ι₂_vec_eq, mul_right_inj, c.vec_injective.eq_iff,
    add_eq_left]

theorem exists_of_involution {b : MulAut V} (hb : b ∈ c.fac₂) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) :
    ∃ B : SLq n, c.ι₂ B = b ∧ plusNil B * plusNil B = 0 ∧ plusNil B ≠ 0 := by
  obtain ⟨B, rfl⟩ := hb
  refine ⟨B, rfl, ?_, ?_⟩
  · apply sub_one_sq_eq_zero_of_sq_eq_one
    have h1 : B ^ 2 = 1 := c.ι₂_injective (by rw [map_pow, hb2, map_one])
    have h2 : (B : Matrix (Fin 2) (Fin 2) (Fq n)) * B = 1 := by
      simpa [sq] using congrArg (fun A : SLq n => (A : Matrix (Fin 2) (Fin 2) (Fq n))) h1
    rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  · intro h0
    apply hb1
    have h1 : (B : Matrix (Fin 2) (Fin 2) (Fq n)) = 1 := by
      rw [← Matrix.transpose_inj, Matrix.transpose_one]
      exact sub_eq_zero.mp h0
    rw [show B = 1 from Subtype.ext h1, map_one]

variable {B : SLq n}

theorem mem_fixV_zpowers_iff' {v : V} :
    v ∈ fixV (Subgroup.zpowers (c.ι₂ B)) ↔
      ∃ w ∈ fixV Y, ∃ M, M * plusNil B = 0 ∧ w * c.vec M = v := by
  rw [plus_mem_fixV_zpowers_iff]
  constructor
  · intro h
    obtain ⟨w, hw, M, rfl⟩ := c.exists_decomp v
    exact ⟨w, hw, M, (c.ι₂_fix_iff B hw M).mp h, rfl⟩
  · rintro ⟨w, hw, M, hM, rfl⟩
    exact (c.ι₂_fix_iff B hw M).mpr hM

theorem mem_commV_zpowers_iff (hN : plusNil B * plusNil B = 0) (hN0 : plusNil B ≠ 0)
    (hb2 : c.ι₂ B ^ 2 = 1) {p : V} :
    p ∈ commV (Subgroup.zpowers (c.ι₂ B)) ↔ ∃ M, M * plusNil B = 0 ∧ c.vec M = p := by
  constructor
  · intro hp
    have hle : commV (Subgroup.zpowers (c.ι₂ B)) ≤
        fixV (Subgroup.zpowers (c.ι₂ B)) ⊓ commV Y := by
      refine commV_zpowers_le_of_forall hb2 fun v => ?_
      obtain ⟨w, hw, X, rfl⟩ := c.exists_decomp v
      have h1 : c.ι₂ B (w * c.vec X) * (w * c.vec X)⁻¹ = c.vec (X * plusNil B) := by
        rw [map_mul, hw _ (c.ι₂_mem B), mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
          c.ι₂_vec_mul_inv]
      rw [h1]
      refine Subgroup.mem_inf.mpr ⟨?_, c.vec_mem _⟩
      rw [plus_mem_fixV_zpowers_iff, c.ι₂_vec_eq, Matrix.mul_assoc, hN, Matrix.mul_zero,
        add_zero]
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp (hle hp)
    obtain ⟨M, rfl⟩ := c.exists_vec h2
    refine ⟨M, ?_, rfl⟩
    have h3 := (plus_mem_fixV_zpowers_iff.mp h1)
    rw [c.ι₂_vec_eq, c.vec_injective.eq_iff, add_eq_left] at h3
    exact h3
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨X, rfl⟩ := exists_mul_eq_of_mul_eq_zero hN hN0 hM
    rw [← c.ι₂_vec_mul_inv]
    exact Subgroup.subset_closure ⟨c.ι₂ B, Subgroup.mem_zpowers _, c.vec X, rfl⟩

theorem commV_zpowers_le : commV (Subgroup.zpowers (c.ι₂ B)) ≤ commV Y :=
  B19.commV_mono (Subgroup.zpowers_le.mpr (c.ι₂_mem B))

theorem commV_zpowers_inf : commV (Subgroup.zpowers (c.ι₂ B)) ⊓ fixV Y = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hp
  rw [Subgroup.mem_bot]
  have h3 : commV (Subgroup.zpowers (c.ι₂ B)) ⊓ fixV Y ≤ commV Y ⊓ fixV Y :=
    inf_le_inf_right _ c.commV_zpowers_le
  have h4 := h3 hp
  rw [inf_comm, c.inf, Subgroup.mem_bot] at h4
  exact h4

theorem fixV_zpowers_eq (hN : plusNil B * plusNil B = 0) (hN0 : plusNil B ≠ 0)
    (hb2 : c.ι₂ B ^ 2 = 1) :
    fixV (Subgroup.zpowers (c.ι₂ B)) = commV (Subgroup.zpowers (c.ι₂ B)) ⊔ fixV Y := by
  refine le_antisymm (fun v hv => ?_) (sup_le (fun p hp => ?_) (fun w hw x hx => ?_))
  · obtain ⟨w, hw, M, hM, rfl⟩ := (c.mem_fixV_zpowers_iff').mp hv
    have hp : c.vec M ∈ commV (Subgroup.zpowers (c.ι₂ B)) :=
      (c.mem_commV_zpowers_iff hN hN0 hb2).mpr ⟨M, hM, rfl⟩
    exact Subgroup.mem_sup.mpr ⟨c.vec M, hp, w, hw, mul_comm _ _⟩
  · obtain ⟨M, hM, rfl⟩ := (c.mem_commV_zpowers_iff hN hN0 hb2).mp hp
    exact (c.mem_fixV_zpowers_iff').mpr ⟨1, Subgroup.one_mem _, M, hM, one_mul _⟩
  · exact hw x (Subgroup.zpowers_le.mpr (c.ι₂_mem B) hx)

theorem rootfix_of (hN : plusNil B * plusNil B = 0) (hN0 : plusNil B ≠ 0) {B' : SLq n}
    (hcomm : c.ι₂ B' * c.ι₂ B = c.ι₂ B * c.ι₂ B') {v : V}
    (hv : v ∈ fixV (Subgroup.zpowers (c.ι₂ B))) : c.ι₂ B' v = v := by
  obtain ⟨w, hw, M, hM, rfl⟩ := (c.mem_fixV_zpowers_iff').mp hv
  have h1 : B' * B = B * B' := c.ι₂_injective (by rw [map_mul, map_mul, hcomm])
  have h2 : (B' : Matrix (Fin 2) (Fin 2) (Fq n)) * B = B * B' := by
    simpa using congrArg (fun A : SLq n => (A : Matrix (Fin 2) (Fin 2) (Fq n))) h1
  have hL : ((B' : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ).det = 1 := by
    rw [Matrix.det_transpose]
    exact B'.2
  have hLN : (B' : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ * plusNil B =
      plusNil B * (B' : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ := by
    rw [plusNil, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.transpose_mul, ← Matrix.transpose_mul, h2]
  have h3 := mul_eq_of_comm_sq_eq_zero hN hN0 hL hLN hM
  rw [map_mul, hw _ (c.ι₂_mem B'), c.ι₂_vec, h3]

theorem natE_of (hN : plusNil B * plusNil B = 0) (hN0 : plusNil B ≠ 0) (hb2 : c.ι₂ B ^ 2 = 1) :
    IsNatSectionBy (slAct n) c.fac₁ (commV (Subgroup.zpowers (c.ι₂ B))) ⊥ := by
  obtain ⟨σ, τ, hτ, hker⟩ := exists_vecMulVec_of_sq_eq_zero hN hN0
  have hEU : commV (Subgroup.zpowers (c.ι₂ B)) ≤ commV Y := c.commV_zpowers_le
  refine ⟨fun d hd p hp => ?_, c.fac₁Equiv, ?_⟩
  · refine commV_mapsTo_of_comm (fun x hx => ?_) hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (c.fac_comm d hd _ ⟨B, rfl⟩) k).eq
  let β' : ↥(commV (Subgroup.zpowers (c.ι₂ B))) →* Multiplicative (Fin 2 → Fq n) :=
    (AddMonoidHom.toMultiplicative (Matrix.mulVec.addMonoidHomLeft τ)).comp
      (c.φ.toMonoidHom.comp (Subgroup.inclusion hEU))
  have hβ' : ∀ (M : Matrix (Fin 2) (Fin 2) (Fq n))
      (h : c.vec M ∈ commV (Subgroup.zpowers (c.ι₂ B))), β' ⟨c.vec M, h⟩ = ofAdd (M *ᵥ τ) := by
    intro M h
    show ofAdd (toAdd (c.φ ⟨c.vec M, hEU h⟩) *ᵥ τ) = _
    rw [c.φ_vec, toAdd_ofAdd]
  refine ⟨β', fun m => ?_, ?_, ?_⟩
  · have hM : vecMulVec (toAdd m) σ * plusNil B * plusNil B = 0 := by
      rw [Matrix.mul_assoc, hN, Matrix.mul_zero]
    have hmem := (c.mem_commV_zpowers_iff hN hN0 hb2).mpr ⟨_, hM, rfl⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hβ', Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec, hτ]
    simp
  · ext ⟨p, hp⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    obtain ⟨M, hM, rfl⟩ := (c.mem_commV_zpowers_iff hN hN0 hb2).mp hp
    rw [hβ', show ((⟨c.vec M, hp⟩ : ↥(commV (Subgroup.zpowers (c.ι₂ B)))) : V) = c.vec M from rfl,
      c.vec_eq_one_iff]
    constructor
    · intro h
      have h1 : M *ᵥ τ = 0 := by simpa using congrArg toAdd h
      rw [hker M hM, h1]
      ext i j
      simp
    · rintro rfl
      simp
  · rintro x ⟨p, hp⟩ hxp
    obtain ⟨M, hM, rfl⟩ := (c.mem_commV_zpowers_iff hN hN0 hb2).mp hp
    have h1 : (x : MulAut V) (c.vec M) =
        c.vec ((c.fac₁Equiv x : Matrix (Fin 2) (Fin 2) (Fq n)) * M) := by
      rw [← c.ι₁_fac₁Equiv x, c.ι₁_vec]
    have h2 : (⟨(x : MulAut V) (c.vec M), hxp⟩ : ↥(commV (Subgroup.zpowers (c.ι₂ B)))) =
        ⟨c.vec ((c.fac₁Equiv x : Matrix (Fin 2) (Fin 2) (Fq n)) * M), h1 ▸ hxp⟩ :=
      Subtype.ext h1
    rw [h2, hβ', hβ']
    simp only [slAct, toAdd_ofAdd, Matrix.mulVec_mulVec]

end PlusCoord

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
