module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents

public section

namespace CFSG.LieType.SteinbergBR

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.LieType.CentralExt CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def hPerp {n : ℕ} (W : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {y | ∀ w ∈ W, stdHermForm h n w y = 0}
  add_mem' {x y} hx hy w hw := by rw [map_add, hx w hw, hy w hw, add_zero]
  zero_mem' _ _ := map_zero _
  smul_mem' c x hx w hw := by rw [map_smul, hx w hw, smul_zero]

theorem mem_hPerp {n : ℕ} {W : Submodule K (Fin n → K)} {y : Fin n → K} :
    y ∈ hPerp h W ↔ ∀ w ∈ W, stdHermForm h n w y = 0 :=
  Iff.rfl

@[expose] noncomputable def hBar {n : ℕ} (W : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {v | (fun i => h.bar (v i)) ∈ W}
  add_mem' {x y} hx hy := by
    have e : (fun i => h.bar ((x + y) i)) = (fun i => h.bar (x i)) + fun i => h.bar (y i) := by
      funext i
      simp [map_add]
    change (fun i => h.bar ((x + y) i)) ∈ W
    rw [e]
    exact W.add_mem hx hy
  zero_mem' := by
    have e : (fun i => h.bar ((0 : Fin n → K) i)) = 0 := by
      funext i
      simp
    change (fun i => h.bar ((0 : Fin n → K) i)) ∈ W
    rw [e]
    exact W.zero_mem
  smul_mem' c x hx := by
    have e : (fun i => h.bar ((c • x) i)) = h.bar c • fun i => h.bar (x i) := by
      funext i
      simp [map_mul]
    change (fun i => h.bar ((c • x) i)) ∈ W
    rw [e]
    exact W.smul_mem _ hx

theorem card_hBar {n : ℕ} (W : Submodule K (Fin n → K)) : Nat.card (hBar h W) = Nat.card W := by
  refine Nat.card_congr
    { toFun := fun v => ⟨fun i => h.bar ((v : Fin n → K) i), v.2⟩
      invFun := fun w => ⟨fun i => h.bar ((w : Fin n → K) i), ?_⟩
      left_inv := fun v => Subtype.ext (funext fun i => h.bar_bar _)
      right_inv := fun w => Subtype.ext (funext fun i => h.bar_bar _) }
  change (fun i => h.bar (h.bar ((w : Fin n → K) i))) ∈ W
  simp only [h.bar_bar]
  exact w.2

theorem finrank_hBar {n : ℕ} (W : Submodule K (Fin n → K)) :
    finrank K (hBar h W) = finrank K W := by
  have := h.finite
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := hBar h W)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := W)
  rw [card_hBar] at h1
  have hK : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  exact Nat.pow_right_injective hK (h1.symm.trans h2)

theorem hPerp_eq_orthogonal {n : ℕ} (W : Submodule K (Fin n → K)) :
    hPerp h W = (Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).orthogonal (hBar h W) := by
  ext y
  rw [mem_hPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hy v hv
    have e := hy _ hv
    rw [stdHermForm_apply] at e
    rw [Matrix.toBilin'_apply', one_mulVec, dotProduct]
    simpa only [h.bar_bar] using e
  · intro hy w hw
    have hv : (fun i => h.bar (w i)) ∈ hBar h W := by
      change (fun i => h.bar (h.bar (w i))) ∈ W
      simpa only [h.bar_bar] using hw
    have e := hy _ hv
    rw [Matrix.toBilin'_apply', one_mulVec, dotProduct] at e
    rw [stdHermForm_apply]
    exact e

theorem finrank_hPerp {n : ℕ} (W : Submodule K (Fin n → K)) :
    finrank K (hPerp h W) = n - finrank K W := by
  have hnd : (Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero (by simp))
  rw [hPerp_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal hnd, finrank_hBar,
    Module.finrank_fin_fun]

@[expose] def fixSpace {n : ℕ} (U : Subgroup (GL (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ u ∈ U, u • v = v}
  add_mem' {x y} hx hy u hu := by rw [smul_add, hx u hu, hy u hu]
  zero_mem' u _ := smul_zero u
  smul_mem' c x hx u hu := by rw [smul_comm, hx u hu]

theorem stdHermForm_smul {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ unitarySU p f K n)
    (x y : Fin n → K) : stdHermForm h n (g • x) (g • y) = stdHermForm h n x y :=
  ((mem_unitarySU_iff_isometry h).1 hg).2 x y

theorem smul_mem_fixSpace {n : ℕ} {U : Subgroup (GL (Fin n) K)} {g : GL (Fin n) K}
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) {v : Fin n → K} (hv : v ∈ fixSpace U) :
    g • v ∈ fixSpace U := by
  intro u hu
  calc u • g • v = g • (g⁻¹ * u * g) • v := by rw [mul_smul, mul_smul, smul_inv_smul]
    _ = g • v := by rw [hv _ (hg u hu)]

theorem smul_mem_hPerp {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ unitarySU p f K n)
    {X : Submodule K (Fin n → K)} (hX : ∀ v ∈ X, g⁻¹ • v ∈ X) {y : Fin n → K}
    (hy : y ∈ hPerp h X) : g • y ∈ hPerp h X := by
  intro w hw
  have e := stdHermForm_smul h hg (g⁻¹ • w) y
  rw [smul_inv_smul] at e
  rw [e]
  exact hy _ (hX w hw)

include h in
theorem exists_flag_of_isPGroup {U : Subgroup (GL (Fin 3) K)} (hUS : U ≤ unitarySU p f K 3)
    (hUp : IsPGroup p U) (hU1 : U ≠ ⊥) :
    ∃ J J₂ : Submodule K (Fin 3 → K), J ≤ J₂ ∧ finrank K J = 1 ∧ finrank K J₂ = 2 ∧
      ∀ g : GL (Fin 3) K, g ∈ unitarySU p f K 3 → (∀ u ∈ U, g * u * g⁻¹ ∈ U) →
        (∀ u ∈ U, g⁻¹ * u * g ∈ U) → (∀ v ∈ J, g • v ∈ J) ∧ ∀ v ∈ J₂, g • v ∈ J₂ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  set W := fixSpace U with hW
  obtain ⟨u, huU, hu1⟩ := U.bot_or_exists_ne_one.resolve_left hU1
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hu1
    apply Units.ext
    ext i j
    have hv : u • (Pi.single j (1 : K) : Fin 3 → K) = (Pi.single j (1 : K) : Fin 3 → K) := by
      have hmem : (Pi.single j (1 : K) : Fin 3 → K) ∈ W := htop ▸ Submodule.mem_top
      exact hmem u huU
    have e := congrFun hv i
    change ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j (1 : K)) i = _ at e
    rw [mulVec_single_one, col_apply] at e
    rw [e, Units.val_one, one_apply, Pi.single_apply]
  have hWlt : finrank K W < 3 := by
    have := Submodule.finrank_lt hWtop
    rwa [Module.finrank_fin_fun] at this
  let X : SubMulAction U (Fin 3 → K) :=
    { carrier := hPerp h W
      smul_mem' := fun u y hy w hw => by
        have hw' : (u : GL (Fin 3) K) • w = w := hw u u.2
        calc stdHermForm h 3 w (u • y) =
            stdHermForm h 3 ((u : GL (Fin 3) K) • w) ((u : GL (Fin 3) K) • y) := by rw [hw']; rfl
          _ = stdHermForm h 3 w y := stdHermForm_smul h (hUS u.2) w y
          _ = 0 := hy w hw }
  have hcard : p ∣ Nat.card X := by
    change p ∣ Nat.card (hPerp h W)
    rw [Module.natCard_eq_pow_finrank (K := K) (V := hPerp h W), h.card]
    refine dvd_pow (dvd_pow_self p (by have := h.one_le; omega)) ?_
    rw [finrank_hPerp]
    omega
  have h0 : (⟨0, (hPerp h W).zero_mem⟩ : X) ∈ MulAction.fixedPoints U X :=
    fun u => Subtype.ext (smul_zero (u : GL (Fin 3) K))
  obtain ⟨b, hb, hb0⟩ := hUp.exists_fixed_point_of_prime_dvd_card_of_fixed_point X hcard h0
  set J := W ⊓ hPerp h W with hJ
  have hbW : (b : Fin 3 → K) ∈ W := fun u hu => congrArg Subtype.val (hb ⟨u, hu⟩)
  have hbJ : (b : Fin 3 → K) ∈ J := ⟨hbW, b.2⟩
  have hJ0 : J ≠ ⊥ := by
    intro hJb
    rw [hJb, Submodule.mem_bot] at hbJ
    exact hb0 (Subtype.ext hbJ.symm)
  have hJiso : J ≤ hPerp h J := fun x hx w hw => hx.2 w hw.1
  have h1 : 1 ≤ finrank K J := Submodule.one_le_finrank_iff.2 hJ0
  have h2 : finrank K J ≤ finrank K (hPerp h J) := Submodule.finrank_mono hJiso
  rw [finrank_hPerp] at h2
  have hJ1 : finrank K J = 1 := by omega
  have hJinv : ∀ g : GL (Fin 3) K, g ∈ unitarySU p f K 3 → (∀ u ∈ U, g * u * g⁻¹ ∈ U) →
      (∀ u ∈ U, g⁻¹ * u * g ∈ U) → ∀ v ∈ J, g • v ∈ J := by
    intro g hgS hg1 hg2 v hv
    refine ⟨smul_mem_fixSpace hg2 hv.1, smul_mem_hPerp h hgS (fun w hw => ?_) hv.2⟩
    exact smul_mem_fixSpace (fun u hu => by rw [inv_inv]; exact hg1 u hu) hw
  refine ⟨J, hPerp h J, hJiso, hJ1, by rw [finrank_hPerp, hJ1], fun g hgS hg1 hg2 =>
    ⟨hJinv g hgS hg1 hg2, fun v hv => smul_mem_hPerp h hgS (fun w hw => ?_) hv⟩⟩
  exact hJinv g⁻¹ (inv_mem hgS) (fun u hu => by rw [inv_inv]; exact hg2 u hu)
    (fun u hu => by rw [inv_inv]; exact hg1 u hu) w hw

end CFSG.LieType.SteinbergBR
