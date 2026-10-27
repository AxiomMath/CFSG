module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidCen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTorus

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {f : ℕ}

@[expose] def tdiagv (u : K) : HypIndex 1 2 → K
  | .inl _ => u
  | .inr (.inl _) => u⁻¹
  | .inr (.inr _) => u

@[expose] def bdiagv (u : K) (i : Fin (2 + 2)) : K :=
  Sum.elim (fun _ => u⁻¹) (fun _ => u) (finSumFinEquiv.symm i)

theorem bdiagv_inl (u : K) (a : Fin 2) : bdiagv u (finSumFinEquiv (.inl a)) = u⁻¹ := by
  simp [bdiagv]

theorem bdiagv_inr (u : K) (a : Fin 2) : bdiagv u (finSumFinEquiv (.inr a)) = u := by
  simp [bdiagv]

theorem blk_smul_one_eq_diagonal (u : K) :
    blk (u⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K)) (u • (1 : Matrix (Fin 2) (Fin 2) K)) =
      diagonal (bdiagv u) := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  rw [blk_apply_fs, diagonal_apply]
  simp only [finSumFinEquiv.injective.eq_iff]
  rcases a with a | a <;> rcases b with b | b
  · rw [fromBlocks_apply₁₁, Matrix.smul_apply, one_apply, bdiagv_inl]
    simp only [Sum.inl.injEq]
    split_ifs <;> simp
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, Matrix.smul_apply, one_apply, bdiagv_inr]
    simp only [Sum.inr.injEq]
    split_ifs <;> simp

theorem uFrame_torus (hk : 2 ≤ 2) (s u : K) :
    blk (u⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K)) (u • (1 : Matrix (Fin 2) (Fin 2) K)) *
        uFrame hk s = uFrame hk s * diagonal (tdiagv u) := by
  rw [blk_smul_one_eq_diagonal]
  ext i a
  rw [diagonal_mul, mul_diagonal]
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective i
  rcases a with a | j | a
  · rcases b with b | b
    · have h1 : uFrame hk s (finSumFinEquiv (.inl b)) (.inl a) = 0 := uv₀_inl hk b
      rw [h1, mul_zero, zero_mul]
    · rw [bdiagv_inr]
      simp only [tdiagv]
      ring
  · rcases b with b | b
    · rw [bdiagv_inl]
      simp only [tdiagv]
      ring
    · have h1 : uFrame hk s (finSumFinEquiv (.inr b)) (.inr (.inl j)) = 0 := by
        change (Pi.single (zIdx j) (1 : K) : Fin (2 + 2) → K) (finSumFinEquiv (.inr b)) = 0
        refine Pi.single_eq_of_ne (fun e => ?_) _
        unfold zIdx at e
        rw [dite_eq_left (show (j : ℕ) < 2 from j.2)] at e
        exact Sum.inr_ne_inl (finSumFinEquiv.injective e)
      rw [h1, mul_zero, zero_mul]
  · rcases b with b | b
    · have h1 : uFrame hk s (finSumFinEquiv (.inl b)) (.inr (.inr a)) = 0 := by
        change uf₀ hk s (finSumFinEquiv (.inl b)) = 0
        rw [uf₀, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr),
          Pi.single_eq_of_ne (finSumFinEquiv.injective.ne Sum.inl_ne_inr), smul_zero, smul_zero,
          add_zero]
      rw [h1, mul_zero, zero_mul]
    · rw [bdiagv_inr]
      simp only [tdiagv]
      ring

section Conj

variable [CharP K 2] (h : UnitaryFieldData 2 f K) (hk : 2 ≤ 2) {s : K} (hs : s + h.bar s = 1)

@[expose] noncomputable def hdc (c : rootsOfUnity (2 ^ f + 1) K) : hypSU h 1 2 :=
  (hypTransport h (isHypTransport_uFrame h hk hs)).symm (torusU K f c)

theorem coe_hdc (c : rootsOfUnity (2 ^ f + 1) K) :
    ((hdc h hk hs c : hypSU h 1 2) : GL (HypIndex 1 2) K).val =
      diagonal (tdiagv ((c : Kˣ) : K)) := by
  rw [hdc, coe_hypTransport_symm, coe_torusU, Units.val_inv_eq_inv_val, Matrix.mul_assoc,
    uFrame_torus hk s, ← Matrix.mul_assoc, transportInv_mul (isHypTransport_uFrame h hk hs),
    Matrix.one_mul]

theorem hypTransport_hdc (c : rootsOfUnity (2 ^ f + 1) K) :
    hypTransport h (isHypTransport_uFrame h hk hs) (hdc h hk hs c) = torusU K f c :=
  MulEquiv.apply_symm_apply _ _

end Conj

section TConj

variable [CharP K 2] (h : UnitaryFieldData 2 f K) (hk : 2 ≤ 2) {s : K} (hs : s + h.bar s = 1)

theorem hdc_inv (c : rootsOfUnity (2 ^ f + 1) K) : (hdc h hk hs c)⁻¹ = hdc h hk hs c⁻¹ := by
  rw [hdc, hdc, map_inv, map_inv]

theorem hdc_mulVec_e (c : rootsOfUnity (2 ^ f + 1) K) :
    ((hdc h hk hs c : hypSU h 1 2) : GL (HypIndex 1 2) K).val *ᵥ Pi.single hE 1 =
      ((c : Kˣ) : K) • Pi.single hE 1 := by
  rw [coe_hdc]
  ext a
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases ha : a = hE
  · subst ha
    rfl
  · rw [Pi.single_eq_of_ne ha, mul_zero, mul_zero]

theorem map_stabE_hdc (c : rootsOfUnity (2 ^ f + 1) K) :
    (stabE (ε := 2) h).map (MulAut.conj (hdc h hk hs c)).toMonoidHom = stabE h := by
  have hle : ∀ c' : rootsOfUnity (2 ^ f + 1) K,
      (stabE (ε := 2) h).map (MulAut.conj (hdc h hk hs c')).toMonoidHom ≤ stabE h := by
    rintro c' _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_stabE] at hg
    rw [mem_stabE]
    have hu0 : ((c' : Kˣ) : K) ≠ 0 := Units.ne_zero _
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Units.val_mul,
      hdc_inv]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hdc_mulVec_e, mulVec_smul, hg, mulVec_smul,
      hdc_mulVec_e, smul_smul]
    rw [show ((c'⁻¹ : rootsOfUnity (2 ^ f + 1) K) : Kˣ) = ((c' : Kˣ))⁻¹ from rfl,
      Units.val_inv_eq_inv_val, inv_mul_cancel₀ hu0, one_smul]
  exact Subgroup.eq_of_le_of_card_ge (hle c)
    (Subgroup.card_map_of_injective (MulAut.conj (hdc h hk hs c)).injective).ge

@[expose] noncomputable def tconj (c : rootsOfUnity (2 ^ f + 1) K) : MulAut (stabE (ε := 2) h) :=
  ((MulAut.conj (hdc h hk hs c)).subgroupMap (stabE h)).trans
    (MulEquiv.subgroupCongr (map_stabE_hdc h hk hs c))

theorem coe_tconj (c : rootsOfUnity (2 ^ f + 1) K) (g : stabE (ε := 2) h) :
    ((tconj h hk hs c g : stabE (ε := 2) h) : hypSU h 1 2) =
      hdc h hk hs c * g * (hdc h hk hs c)⁻¹ :=
  rfl

theorem smat_tconj (c : rootsOfUnity (2 ^ f + 1) K) (g : stabE (ε := 2) h) :
    smat h (tconj h hk hs c g) =
      diagonal (tdiagv ((c : Kˣ) : K)) * smat h g * diagonal (tdiagv ((c : Kˣ) : K)⁻¹) := by
  change ((hdc h hk hs c * g * (hdc h hk hs c)⁻¹ : hypSU h 1 2) : GL (HypIndex 1 2) K).val = _
  rw [hdc_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_hdc,
    coe_hdc, show ((c⁻¹ : rootsOfUnity (2 ^ f + 1) K) : Kˣ) = ((c : Kˣ))⁻¹ from rfl,
    Units.val_inv_eq_inv_val]

theorem avec_tconj (c : rootsOfUnity (2 ^ f + 1) K) (g : stabE (ε := 2) h) :
    avec h (tconj h hk hs c g) = (((c : Kˣ) : K)⁻¹ * ((c : Kˣ) : K)⁻¹) • avec h g := by
  funext k
  change smat h (tconj h hk hs c g) (.inr (.inl k)) hF = _
  rw [smat_tconj, mul_diagonal, diagonal_mul]
  simp only [tdiagv, Pi.smul_apply, smul_eq_mul, avec]
  ring

theorem tconj_of_mem_tvSub (c : rootsOfUnity (2 ^ f + 1) K) {t : stabE (ε := 2) h}
    (ht : t ∈ tvSub h) : tconj h hk hs c t = t := by
  obtain ⟨c', hc'⟩ := exists_eichM_zero_of_avec h ht.1 ht.2
  have hcomm : hdc h hk hs c * (t : hypSU h 1 2) = t * hdc h hk hs c := by
    refine Subtype.ext (Units.ext ?_)
    change ((hdc h hk hs c : hypSU h 1 2) : GL (HypIndex 1 2) K).val * smat h t =
      smat h t * ((hdc h hk hs c : hypSU h 1 2) : GL (HypIndex 1 2) K).val
    rw [hc', coe_hdc, eichM_zero_left]
    ext i j
    rw [diagonal_mul, mul_diagonal]
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [tdiagv, one_apply, Fin.eq_zero, mul_comm]
  apply Subtype.ext
  rw [coe_tconj, hcomm, mul_inv_cancel_right]

end TConj

section Fix

variable [CharP K 2] (h : UnitaryFieldData 2 f K) (hk : 2 ≤ 2) {s : K} (hs : s + h.bar s = 1)

theorem tconj_fixfree {c : rootsOfUnity (2 ^ f + 1) K} (hc : c ≠ 1) (x : stabE (ε := 2) h)
    (hx : avec h (tconj h hk hs c x) = avec h x) : avec h x = 0 := by
  set u : K := ((c : Kˣ) : K) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hu1 : u ≠ 1 := by
    intro h1
    apply hc
    apply Subtype.ext
    apply Units.ext
    rw [← hu, h1]
    rfl
  have hu2 : u⁻¹ * u⁻¹ ≠ 1 := by
    intro h1
    have h2 : u * u = 1 := by
      have e : u * u = (u⁻¹ * u⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
      rw [e, h1, inv_one]
    have h3 : (u - 1) * (u - 1) = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2 + (1 - u) * h2'
    exact hu1 (sub_eq_zero.mp (mul_self_eq_zero.mp h3))
  rw [avec_tconj] at hx
  have h1 : (u⁻¹ * u⁻¹ - 1) • avec h x = 0 := by rw [sub_smul, hx, one_smul, sub_self]
  exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hu2)

end Fix

end CFSG.ComponentClassification.RankTwoClassical.URigid
