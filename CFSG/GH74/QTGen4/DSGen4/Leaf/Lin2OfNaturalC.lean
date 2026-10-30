module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalB
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel

public section

namespace CFSG.GH74.QTGen4.DSGen4.Lin2C

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.DSGen4.Lin2A CFSG.GH74.QTGen4.DSGen4.Lin2B
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 a5_card)
open Certificates.A5GL42 (HN aN bN Facts)
open scoped commutatorElement Matrix

section Pre

variable {G : Type} [Group G] [Finite G]

theorem mem_pCore_iff_pCoreOf {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := by
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem le_normalizer_pCore {L : Subgroup G} :
    L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
  (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf L)

theorem a5Pre_self {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L)
    (he : IsElemAbelian 2 (pCoreOf 2 L)) (h16 : Nat.card (pCoreOf 2 L) = 16) :
    A5Pre L L (pCoreOf 2 L) ⊥ := by
  have hQnorm : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCore
  have hcomm : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (he.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm1 : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
  refine ⟨le_rfl, Subgroup.le_normalizer, hQnorm, ?_, ⟨bot_le, ?_, ?_⟩, ?_, ?_, hq, ?_⟩
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      simp
    · intro hx
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx]
      group
  · exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [Subgroup.mem_bot]
      exact hcomm1 a ha b hb
  · exact fun e he' => by
      rw [Subgroup.mem_bot]
      exact he.2 e he'
  · rw [Subgroup.relIndex_bot_left]
    exact h16
  · exact fun q hq' e he' => by
      rw [Subgroup.mem_bot]
      exact hcomm1 q hq' e he'
  · by_contra hcon
    push Not at hcon
    have hLQ : L ≤ pCoreOf 2 L := by
      intro l hl
      apply hc
      refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun e he' => ?_⟩
      have h1 := hcon l hl e he'
      rw [Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
    have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact a5_card
    have htop : CFSG.Open.pCore 2 ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact (mem_pCore_iff_pCoreOf x).mpr (hLQ x.2)
    have h1 : Nat.card (oTwoQuot ↥L) = 1 := by
      show Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) = 1
      rw [htop]
      exact Subgroup.index_top
    omega

theorem blockU_le_pCoreOf {L : Subgroup G} : blockU L ≤ pCoreOf 2 L := by
  unfold blockU blockQ
  rw [Subgroup.commutator_le]
  intro q hq l hl
  rw [commutatorElement_def]
  have h1 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCore hl)) q⁻¹).mp (Subgroup.inv_mem _ hq)
  have h2 := Subgroup.mul_mem _ hq h1
  simpa [mul_assoc] using h2

theorem comm_mem_blockU {L : Subgroup G} (ℓ : ↥L) {q : G} (hq : q ∈ pCoreOf 2 L) :
    (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ blockU L := by
  have h := Subgroup.commutator_mem_commutator ℓ.2 hq
  rw [Subgroup.commutator_comm] at h
  exact h

end Pre

@[expose] def linMul {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F)) (T : Mat4) :
    Multiplicative (Fin 4 → ZMod 2) →* Multiplicative (Fin 2 → F) where
  toFun v := Multiplicative.ofAdd (κ (T *ᵥ Multiplicative.toAdd v))
  map_one' := by simp
  map_mul' x y := by simp [Matrix.mulVec_add]

theorem toAdd_linMul {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F)) (T : Mat4) (v : Multiplicative (Fin 4 → ZMod 2)) :
    Multiplicative.toAdd (linMul κ T v) = κ (T *ᵥ Multiplicative.toAdd v) :=
  rfl

theorem y0_ne_one : y0 ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  show ¬ (CFSG.QuasithinUnique.A5.Delta5.b0⁻¹ = 1)
  decide +kernel

theorem aN_mul_self : aN * aN = 1 := by
  decide

theorem bN_cube : bN * bN * bN = 1 := by
  decide

theorem aN_det_ne : aN.det ≠ 0 := by
  have h : (aN * aN).det = 1 := by
    rw [aN_mul_self, Matrix.det_one]
  rw [Matrix.det_mul] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem bN_det_ne : bN.det ≠ 0 := by
  have h : (bN * bN * bN).det = 1 := by
    rw [bN_cube, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul] at h
  intro h0
  rw [h0, zero_mul, zero_mul] at h
  exact zero_ne_one h

theorem exists_intertwiner (hF : Facts) (ι Wu : Alt5 →* GL (Fin 4) (ZMod 2))
    (hVx : ι x0 ≠ 1) (hVff : ∀ v : Fin 4 → ZMod 2, ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0)
    (hWx : Wu x0 ≠ 1) (hWff : ∀ v : Fin 4 → ZMod 2, ((Wu y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0) :
    ∃ TU : GL (Fin 4) (ZMod 2), ∀ σ : Alt5, TU * ι σ = Wu σ * TU := by
  have hιx : ι x0 * ι x0 = 1 := by rw [← map_mul, x0_sq, map_one]
  have hιy : ι y0 ^ 3 = 1 := by rw [← map_pow, y0_cube, map_one]
  have hιxy : (ι x0 * ι y0) ^ 5 = 1 := by rw [← map_mul, ← map_pow, x0_y0_pow_five, map_one]
  have hWx2 : Wu x0 * Wu x0 = 1 := by rw [← map_mul, x0_sq, map_one]
  have hWy : Wu y0 ^ 3 = 1 := by rw [← map_pow, y0_cube, map_one]
  have hWxy : (Wu x0 * Wu y0) ^ 5 = 1 := by rw [← map_mul, ← map_pow, x0_y0_pow_five, map_one]
  obtain ⟨gV, hgV1, hgV2⟩ := exists_natural_conj hF (ι x0) (ι y0) hιx hVx hιy hιxy hVff
  obtain ⟨hW, hW1, hW2⟩ := exists_natural_conj hF (Wu x0) (Wu y0) hWx2 hWx hWy hWxy hWff
  obtain ⟨aNU, haNU⟩ : ∃ u : GL (Fin 4) (ZMod 2), (u : Mat4) = aN :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero aN aN_det_ne, rfl⟩
  obtain ⟨bNU, hbNU⟩ : ∃ u : GL (Fin 4) (ZMod 2), (u : Mat4) = bN :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero bN bN_det_ne, rfl⟩
  have hgX : gV * ι x0 = aNU * gV := Units.ext (by rw [Units.val_mul, Units.val_mul, haNU]; exact hgV1)
  have hgY : gV * ι y0 = bNU * gV := Units.ext (by rw [Units.val_mul, Units.val_mul, hbNU]; exact hgV2)
  have hWX : hW * Wu x0 = aNU * hW := Units.ext (by rw [Units.val_mul, Units.val_mul, haNU]; exact hW1)
  have hWY : hW * Wu y0 = bNU * hW := Units.ext (by rw [Units.val_mul, Units.val_mul, hbNU]; exact hW2)
  have hTX : hW⁻¹ * gV * ι x0 = Wu x0 * (hW⁻¹ * gV) := by
    calc hW⁻¹ * gV * ι x0 = hW⁻¹ * (gV * ι x0) := by group
      _ = hW⁻¹ * (aNU * gV) := by rw [hgX]
      _ = hW⁻¹ * (aNU * hW) * (hW⁻¹ * gV) := by group
      _ = hW⁻¹ * (hW * Wu x0) * (hW⁻¹ * gV) := by rw [← hWX]
      _ = Wu x0 * (hW⁻¹ * gV) := by group
  have hTY : hW⁻¹ * gV * ι y0 = Wu y0 * (hW⁻¹ * gV) := by
    calc hW⁻¹ * gV * ι y0 = hW⁻¹ * (gV * ι y0) := by group
      _ = hW⁻¹ * (bNU * gV) := by rw [hgY]
      _ = hW⁻¹ * (bNU * hW) * (hW⁻¹ * gV) := by group
      _ = hW⁻¹ * (hW * Wu y0) * (hW⁻¹ * gV) := by rw [← hWY]
      _ = Wu y0 * (hW⁻¹ * gV) := by group
  refine ⟨hW⁻¹ * gV, ?_⟩
  have hfg : (MulAut.conj (hW⁻¹ * gV)).toMonoidHom.comp ι = Wu := by
    apply MonoidHom.eq_of_eqOn_top
    rw [← closure_x0_y0]
    apply MonoidHom.eqOn_closure
    intro σ hσ
    obtain rfl | rfl : σ = x0 ∨ σ = y0 := hσ
    · show (hW⁻¹ * gV) * ι x0 * (hW⁻¹ * gV)⁻¹ = Wu x0
      rw [mul_inv_eq_iff_eq_mul]
      exact hTX
    · show (hW⁻¹ * gV) * ι y0 * (hW⁻¹ * gV)⁻¹ = Wu y0
      rw [mul_inv_eq_iff_eq_mul]
      exact hTY
  intro σ
  have h := congrArg (fun f : Alt5 →* GL (Fin 4) (ZMod 2) => f σ) hfg
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

end CFSG.GH74.QTGen4.DSGen4.Lin2C
