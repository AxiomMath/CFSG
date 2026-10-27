module

public import CFSG.CGT.PushingUpLit.CGT6M.J2FiveData
public import CFSG.CGT.PushingUpLit.CGT6M.FiveLift
public import CFSG.Sporadic.Bridge.J2Native

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Sporadic.Bridge.J2

set_option maxRecDepth 100000 in
theorem lwordL_wordX : lwordL natX natXi wordX idL = matX := by decide +kernel

set_option maxRecDepth 100000 in
theorem lwordL_wordG : lwordL natX natXi wordG idL = matG := by decide +kernel

theorem wfM_mats : wfM matX = true ∧ wfM matG = true := by decide +kernel

@[expose] def matY : List (List ℕ) := mulL (mulL matG matX) (mulL matG matG)

set_option maxRecDepth 100000 in
theorem mat_checks : mulL matG (mulL matG matG) = idL ∧
    mulL matX (mulL matX (mulL matX (mulL matX matX))) = idL ∧
    mulL matX matY = mulL matY matX ∧
    mulL (mulL (mulL matG matY) (mulL matG matG)) (mulL matX matY) = idL ∧
    toM matX 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 := by
  decide +kernel

noncomputable abbrev mat (u : seedGroup) : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  ((u : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5))

theorem mat_mul (u v : seedGroup) : mat (u * v) = mat u * mat v := rfl

theorem mat_one : mat (1 : seedGroup) = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ e => Subtype.ext (Units.ext e)

theorem mat_mulL {u v : seedGroup} {P Q : List (List ℕ)} (hP : wfM P = true)
    (hQ : wfM Q = true) (hu : mat u = toM P) (hv : mat v = toM Q) :
    mat (u * v) = toM (mulL P Q) := by
  rw [mat_mul, hu, hv, toM_mulL hP hQ]

noncomputable def xU : seedGroup :=
  ⟨CFSG.Sporadic.Bridge.wordProd natU wordX, natWord_mem wordX⟩

noncomputable def gU : seedGroup :=
  ⟨CFSG.Sporadic.Bridge.wordProd natU wordG, natWord_mem wordG⟩

theorem mat_xU : mat xU = toM matX := val_natWord lwordL_wordX

theorem mat_gU : mat gU = toM matG := val_natWord lwordL_wordG

theorem exists_five_data_seedGroup :
    ∃ a b g : seedGroup, a ≠ 1 ∧ a ^ 5 = 1 ∧ Commute a b ∧ g * a * g⁻¹ = b ∧
      g * b * g⁻¹ = (a * b)⁻¹ := by
  obtain ⟨hX, hG⟩ := wfM_mats
  obtain ⟨h3, h5, hc, h4, h0⟩ := mat_checks
  have hGG : mat (gU * gU) = toM (mulL matG matG) := mat_mulL hG hG mat_gU mat_gU
  have hGGG : gU * (gU * gU) = 1 :=
    mat_injective (by rw [mat_mulL hG (wfM_mulL hG) mat_gU hGG, h3, toM_idL, mat_one])
  have hginv : gU⁻¹ = gU * gU := inv_eq_of_mul_eq_one_right hGGG
  have hGX : mat (gU * xU) = toM (mulL matG matX) := mat_mulL hG hX mat_gU mat_xU
  have hY : mat (gU * xU * (gU * gU)) = toM matY :=
    mat_mulL (wfM_mulL hG) (wfM_mulL hG) hGX hGG
  have hYw : wfM matY = true := wfM_mulL (wfM_mulL hG)
  refine ⟨xU, gU * xU * (gU * gU), gU, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h0
    have := congrArg (fun u => mat u 0 0) h
    simpa [mat_xU, mat_one] using this
  · have e : xU ^ 5 = xU * (xU * (xU * (xU * xU))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    have h2 : mat (xU * xU) = toM (mulL matX matX) := mat_mulL hX hX mat_xU mat_xU
    have h3' : mat (xU * (xU * xU)) = toM (mulL matX (mulL matX matX)) :=
      mat_mulL hX (wfM_mulL hX) mat_xU h2
    have h4' : mat (xU * (xU * (xU * xU))) = toM (mulL matX (mulL matX (mulL matX matX))) :=
      mat_mulL hX (wfM_mulL hX) mat_xU h3'
    exact mat_injective (by rw [mat_mulL hX (wfM_mulL hX) mat_xU h4', h5, toM_idL, mat_one])
  · refine mat_injective ?_
    rw [mat_mulL hX hYw mat_xU hY, mat_mulL hYw hX hY mat_xU, hc]
  · rw [hginv]
  · have hGY : mat (gU * (gU * xU * (gU * gU))) = toM (mulL matG matY) :=
      mat_mulL hG hYw mat_gU hY
    have hGYG : mat (gU * (gU * xU * (gU * gU)) * (gU * gU)) =
        toM (mulL (mulL matG matY) (mulL matG matG)) :=
      mat_mulL (wfM_mulL hG) (wfM_mulL hG) hGY hGG
    have hXY : mat (xU * (gU * xU * (gU * gU))) = toM (mulL matX matY) :=
      mat_mulL hX hYw mat_xU hY
    have hall : gU * (gU * xU * (gU * gU)) * (gU * gU) * (xU * (gU * xU * (gU * gU))) = 1 :=
      mat_injective (by
        rw [mat_mulL (wfM_mulL (wfM_mulL hG)) (wfM_mulL hX) hGYG hXY, h4, toM_idL, mat_one])
    rw [hginv]
    exact eq_inv_of_mul_eq_one_left hall

theorem false_of_j2_image {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V ≤ 2 ^ 8) {L : Type*} [Group L] [Finite L] (ρ : L →* MulAut V)
    (hρ : Function.Injective ρ) (π : L →* Blueprint.NativeSporadic.J2)
    (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) : False := by
  obtain ⟨a, b, g, ha1, ha5, hab, hga, hgb⟩ := exists_five_data_seedGroup
  let e : seedGroup ≃* Blueprint.NativeSporadic.J2 := nativeEquiv.symm
  refine false_of_five_data_image hV hcard ρ hρ π hπ hK (a := e a) (b := e b) (g := e g)
    ?_ ?_ ?_ ?_ ?_
  · exact fun h => ha1 (e.injective (by rw [h, map_one]))
  · rw [← map_pow, ha5, map_one]
  · exact hab.map e
  · have h := congrArg e hga
    simp only [map_mul, map_inv] at h
    exact h
  · have h := congrArg e hgb
    simp only [map_mul, map_inv] at h
    exact h

end CFSG.CGT.PushingUpLit.CGT6M
