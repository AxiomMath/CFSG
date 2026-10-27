module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFacts
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFacts
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCubeInputs
public import Certificates.Certificate3095
public import Certificates.Certificate3089
public import Certificates.Certificate3093
public import Certificates.Certificate3094
public import Certificates.Certificate2151
public import Certificates.Certificate2152
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2158
public import Certificates.Certificate2161
public import Certificates.Certificate2162

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

@[expose] noncomputable def uP :
    Equiv.Perm (Fin 276) :=
    (bcbM : Equiv.Perm (Fin 276)) * sP

theorem uP_eq :
    uP =
    (bcbM : Equiv.Perm (Fin 276)) * sP := rfl

theorem mu_perm
    (x : edgeGroup) :
    ((bcbM * (psi x : co3M) * bcbM⁻¹ : co3M) : Equiv.Perm (Fin 276)) = uP * perm x * uP⁻¹ := by
  rw [coe_mul, coe_mul, coe_psi, coe_inv, uP_eq]
  group

theorem uP_cube :
    uP ^ 3 =
    (kpM : Equiv.Perm (Fin 276)) := by
  rw [uP_eq]
  exact kp_facts.2.2.2.2

theorem kpM_inv :
    kpM⁻¹ = kpM :=
    inv_eq_of_mul_eq_one_right kp_facts.2.2.1

theorem psi_comm_y
    {x : edgeGroup} (hx : x * yH = yH * x) : psi x *
    yH = yH * psi x := by
  rw [← psi_yH, ← map_mul, ← map_mul, hx]

theorem bcb_conj_mem
    {w : edgeGroup}
    (hw : w * yH = yH * w) :
    ∃ w' : edgeGroup, (w' : co3M) = bcbM * w * bcbM⁻¹ ∧ w' * yH = yH * w' := by
  have hwy : (w : co3M) * yM = yM * w := congrArg Subtype.val hw
  have hwa : (w : co3M) * ma = ma * w := mem_centralizer_singleton_iff.1 w.2
  have hmem : bcbM * w * bcbM⁻¹ ∈ edgeGroup := by
    rw [mem_centralizer_singleton_iff, ← bcb_facts.2.2.1]
    calc bcbM * w * bcbM⁻¹ * (bcbM * yM * bcbM⁻¹) = bcbM * (w * yM) * bcbM⁻¹ := by group
      _ = bcbM * (yM * w) * bcbM⁻¹ := by rw [hwy]
      _ = bcbM * yM * bcbM⁻¹ * (bcbM * w * bcbM⁻¹) := by group
  refine ⟨⟨_, hmem⟩, rfl, Subtype.ext ?_⟩
  show bcbM * w * bcbM⁻¹ * yM = yM * (bcbM * w * bcbM⁻¹)
  rw [← bcb_facts.2.1]
  calc bcbM * w * bcbM⁻¹ * (bcbM * ma * bcbM⁻¹) = bcbM * (w * ma) * bcbM⁻¹ := by group
    _ = bcbM * (ma * w) * bcbM⁻¹ := by rw [hwa]
    _ = bcbM * ma * bcbM⁻¹ * (bcbM * w * bcbM⁻¹) := by group

theorem mu_mem
    {x : edgeGroup}
    (hx : x * yH = yH * x) :
    ∃ x' : edgeGroup, (x' : co3M) = bcbM * psi x * bcbM⁻¹ ∧ x' * yH = yH * x' :=
  bcb_conj_mem (psi_comm_y hx)

theorem chain_iff
    (z : edgeGroup) :
    (∀ x₀ x₁ x₂ : edgeGroup, x₀ * yH = yH * x₀ →
      (x₁ : co3M) = bcbM * psi x₀ * bcbM⁻¹ → (x₂ : co3M) = bcbM * psi x₁ * bcbM⁻¹ →
      bcbM * psi x₂ * bcbM⁻¹ = ((z * x₀ * z⁻¹ : edgeGroup) : co3M)) ↔
    ∀ x₀ : edgeGroup, x₀ * yH = yH * x₀ →
      (kpM : Equiv.Perm (Fin 276)) * perm x₀ * kpM = perm (z * x₀ * z⁻¹) := by
  have key : ∀ x₀ x₁ x₂ : edgeGroup, (x₁ : co3M) = bcbM * psi x₀ * bcbM⁻¹ →
      (x₂ : co3M) = bcbM * psi x₁ * bcbM⁻¹ →
      ((bcbM * psi x₂ * bcbM⁻¹ : co3M) : Equiv.Perm (Fin 276)) =
        (kpM : Equiv.Perm (Fin 276)) * perm x₀ * kpM := by
    intro x₀ x₁ x₂ h1 h2
    have h1' : perm x₁ = uP * perm x₀ * uP⁻¹ := by
      rw [← mu_perm]; exact congrArg Subtype.val h1
    have h2' : perm x₂ = uP * perm x₁ * uP⁻¹ := by
      rw [← mu_perm]; exact congrArg Subtype.val h2
    rw [mu_perm, h2', h1']
    have hkinv : (kpM : Equiv.Perm (Fin 276)) = (kpM : Equiv.Perm (Fin 276))⁻¹ := by
      rw [← coe_inv, kpM_inv]
    calc uP * (uP * (uP * perm x₀ * uP⁻¹) * uP⁻¹) * uP⁻¹ = uP ^ 3 * perm x₀ * (uP ^ 3)⁻¹ := by
          simp only [pow_three]; group
      _ = _ := by rw [uP_cube, ← hkinv]
  constructor
  · intro h x₀ hx₀
    obtain ⟨x₁, h1, hx₁⟩ := mu_mem hx₀
    obtain ⟨x₂, h2, -⟩ := mu_mem hx₁
    rw [← key x₀ x₁ x₂ h1 h2]
    exact congrArg Subtype.val (h x₀ x₁ x₂ hx₀ h1 h2)
  · intro h x₀ x₁ x₂ hx₀ h1 h2
    apply Subtype.ext
    rw [key x₀ x₁ x₂ h1 h2]
    exact h x₀ hx₀

theorem fix_iff
    (z : edgeGroup) :
    bcbM * psi z * bcbM⁻¹ = z ↔ uP * perm z = perm z * uP := by
  constructor
  · intro h
    have h' : uP * perm z * uP⁻¹ = perm z := by
      rw [← mu_perm]; exact congrArg Subtype.val h
    calc uP * perm z = uP * perm z * uP⁻¹ * uP := by group
      _ = perm z * uP := by rw [h']
  · intro h
    apply Subtype.ext
    show ((bcbM * (psi z : co3M) * bcbM⁻¹ : co3M) : Equiv.Perm (Fin 276)) = perm z
    rw [mu_perm, h, mul_inv_cancel_right]

theorem cube_check :
    ∀ j < 4608, commutesA 276 hList[j]! yArr = true →
      ((allLt 4608 fun i => !commutesA 276 hList[i]! yArr ||
        eqA 276 (compA 276 kpArr (compA 276 hList[i]! (compA 276 kpArr hList[j]!)))
          (compA 276 hList[j]! hList[i]!)) &&
        eqA 276 (compA 276 uArr hList[j]!) (compA 276 hList[j]! uArr)) =
      (eqA 276 hList[j]! kpArr || eqA 276 hList[j]! kpcArr) :=
  Certificates.certificate3095

theorem rep_uP :
    Rep 276 uArr uP := by
  rw [uP_eq]
  exact rep_compA rep_bcb rep_g3

theorem rep_kpc :
    Rep 276 kpcArr
    ((kpM * mc : co3M) : Equiv.Perm (Fin 276)) := by
  rw [coe_mul, coe_mc]
  exact rep_compA rep_kp rep_g2

theorem conj_iff_kp
    {z x₀ : edgeGroup} {s t : Array ℕ}
    (hs : Rep 276 s (perm z))
    (ht : Rep 276 t (perm x₀)) :
    eqA 276 (compA 276 kpArr (compA 276 t (compA 276 kpArr s))) (compA 276 s t) = true ↔
      (kpM : Equiv.Perm (Fin 276)) * perm x₀ * kpM = perm (z * x₀ * z⁻¹) := by
  rw [eqA_iff (rep_compA rep_kp (rep_compA ht (rep_compA rep_kp hs))) (rep_compA hs ht)]
  have hp : perm (z * x₀ * z⁻¹) = perm z * perm x₀ * (perm z)⁻¹ := by
    simp only [perm, coe_mul, coe_inv]
  rw [hp]
  constructor
  · intro h
    rw [← mul_assoc, ← mul_assoc] at h
    rw [← h]
    group
  · intro h
    rw [← mul_assoc, ← mul_assoc, h]
    group

theorem cube_iff
    (z : edgeGroup)
    (hz : z * yH = yH * z) :
    ((∀ x₀ x₁ x₂ : edgeGroup, x₀ * yH = yH * x₀ →
      (x₁ : co3M) = bcbM * psi x₀ * bcbM⁻¹ → (x₂ : co3M) = bcbM * psi x₁ * bcbM⁻¹ →
      bcbM * psi x₂ * bcbM⁻¹ = ((z * x₀ * z⁻¹ : edgeGroup) : co3M)) ∧
      bcbM * psi z * bcbM⁻¹ = z) ↔ (z : co3M) = kpM ∨ (z : co3M) = kpM * mc := by
  obtain ⟨j, hj, rfl⟩ := exists_eltH z
  have hc := cube_check j hj ((commutesA_iff (rep_eltH hj) rep_yH).2 hz)
  rw [chain_iff, fix_iff]
  have hrhs : ((eltH j : co3M) = kpM ∨ (eltH j : co3M) = kpM * mc) ↔
      (eqA 276 hList[j]! kpArr || eqA 276 hList[j]! kpcArr) = true := by
    rw [Bool.or_eq_true, eqA_iff (rep_eltH hj) rep_kp, eqA_iff (rep_eltH hj) rep_kpc]
    exact ⟨fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val),
      fun h => h.imp Subtype.ext Subtype.ext⟩
  rw [hrhs, ← hc, Bool.and_eq_true, allLt_iff,
    eqA_iff (rep_compA rep_uP (rep_eltH hj)) (rep_compA (rep_eltH hj) rep_uP)]
  refine and_congr_left' ⟨fun h i hi => ?_, fun h x₀ hx₀ => ?_⟩
  · rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hy : commutesA 276 hList[i]! yArr = true
    · exact Or.inr ((conj_iff_kp (rep_eltH hj) (rep_eltH hi)).2
        (h _ ((commutesA_iff (rep_eltH hi) rep_yH).1 hy)))
    · exact Or.inl (Bool.eq_false_iff.2 hy)
  · obtain ⟨i, hi, rfl⟩ := exists_eltH x₀
    have hy := (commutesA_iff (rep_eltH hi) rep_yH).2 hx₀
    have := h i hi
    rw [Bool.or_eq_true, Bool.not_eq_true', hy] at this
    exact (conj_iff_kp (rep_eltH hj) (rep_eltH hi)).1
      (this.resolve_left Bool.false_ne_true.symm)

theorem psi_center
    (z : edgeGroup) (hz : z ∈ center edgeGroup) :
    psi z = z ↔ z = 1 ∨ z = eH * aH := by
  have hea : eH ≠ aH := fun h => involutions.2.2 (congrArg Subtype.val h).symm
  have hpea : psi (eH * aH) = eH * aH := by
    rw [map_mul, psi_eH, psi_aH, (mem_center_iff.1 aH_mem_center eH)]
  rcases (center_edgeGroup z).1 hz with rfl | rfl | rfl | rfl
  · simp
  · rw [psi_eH]
    constructor
    · intro h; exact absurd h.symm hea
    · rintro (h | h)
      · exact absurd h (fun h' => by
          have := congrArg (fun x : edgeGroup => orderOf x) h'
          simp only [orderOf_one] at this
          rw [show orderOf eH = 2 by
            rw [← orderOf_injective edgeGroup.subtype Subtype.val_injective eH]
            exact involutions.2.1] at this
          omega)
      · have h2 : aH = 1 := by
          have := congrArg (fun x => eH⁻¹ * x) h
          simpa using this.symm
        exact absurd h2 (fun h' => by
          have := congrArg Subtype.val h'
          exact ma_ne_one this)
  · rw [psi_aH]
    constructor
    · intro h; exact absurd h hea
    · rintro (h | h)
      · exact absurd (congrArg Subtype.val h) ma_ne_one
      · have h2 : eH = 1 := by
          have := congrArg (fun x => x * aH⁻¹) h
          simpa using this.symm
        exact absurd h2 (fun h' => by
          have := congrArg (fun x : edgeGroup => orderOf x) h'
          simp only [orderOf_one] at this
          rw [show orderOf eH = 2 by
            rw [← orderOf_injective edgeGroup.subtype Subtype.val_injective eH]
            exact involutions.2.1] at this
          omega)
  · simp [hpea]

theorem cubeData :
    CubeData :=
    ⟨cube_iff, psi_center⟩

end CFSG.EvenSmallLie.SympSix.Co3Ident
