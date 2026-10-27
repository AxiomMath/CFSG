module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Centralizer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnRoot

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley

section Vec

variable {K : Type} [Field K]

theorem unG2_vec_apply (i : Fin d4.rank) :
    a2tcVec (K := K) 1 1 (-1) 1 i = if i = nd 2 then -1 else 1 := by
  fin_cases i <;> rfl

theorem unG2_neg_one_fix (σ : K ≃+* K) : Units.map σ.toRingHom.toMonoidHom (-1 : Kˣ) = -1 :=
  Units.ext (by simp)

theorem unG2_vec_fix (σ : K ≃+* K) (i : Fin d4.rank) :
    Units.map σ.toRingHom.toMonoidHom (a2tcVec (K := K) 1 1 (-1) 1 i) =
      a2tcVec (K := K) 1 1 (-1) 1 i := by
  rw [unG2_vec_apply]
  split_ifs
  · exact unG2_neg_one_fix σ
  · exact map_one _

theorem unG2_vec_rho (i : Fin d4.rank) :
    a2tcVec (K := K) 1 1 (-1) 1 (rhoPerm i) = a2tcVec (K := K) 1 1 (-1) 1 i := by
  fin_cases i <;> rfl

theorem unG2_vec_mul_self :
    a2tcVec (K := K) 1 1 (-1) 1 * a2tcVec (K := K) 1 1 (-1) 1 = 1 := by
  funext i
  rw [Pi.mul_apply, unG2_vec_apply]
  split_ifs <;> simp

theorem unG2_vec_inv_map (ε : K ≃+* K) (i : Fin d4.rank) :
    (Units.map ε.toRingHom.toMonoidHom (a2tcVec (K := K) 1 1 (-1) 1 i))⁻¹ =
      a2tcVec (K := K) 1 1 (-1) 1 i := by
  rw [unG2_vec_apply]
  split_ifs
  · rw [unG2_neg_one_fix ε]
    simp
  · simp

theorem unG2_rootChar_apply (β : Fin d4.rank → ℤ) :
    rootChar (τ := TwistTag.D4.tag) (a2tcVec (K := K) 1 1 (-1) 1) β = (-1) ^ β (nd 2) := by
  unfold rootChar
  rw [Finset.prod_eq_single (nd 2)]
  · simp [unG2_vec_apply]
  · intro i _ hi
    simp [unG2_vec_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unG2_rootChar :
    rootChar (τ := TwistTag.D4.tag) (a2tcVec (K := K) 1 1 (-1) 1) (d43Lift (hexPos (-3))) = -1 := by
  have h2 : d43Lift (hexPos (-3)) (nd 2) = -1 := by decide
  rw [unG2_rootChar_apply, h2]
  simp

end Vec

section Act

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem unG2_conj_neg_three (hσ3 : ∀ x, σ.toRingHom (σ.toRingHom (σ.toRingHom x)) = x)
    {g : adjointGroup d4 K}
    (hg : (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (a2tcVec 1 1 (-1) 1))
    {y : adjointGroup d4 K} (hy : y ∈ twistedRootSubgroupD4 σ.toRingHom (hexPos (-3))) :
    g * y * g⁻¹ = y⁻¹ := by
  have hγ : IsRoot .G2 (hexPos (-3)) := isRoot_hexPos (by norm_num) (by norm_num)
  have hs : ¬ d43Long (hexPos (-3)) := by
    unfold d43Long
    decide
  obtain ⟨u, rfl⟩ := (mem_iff_d43XSh hσ3 hγ hs y).1 hy
  have hβ := isRoot_d43Lift hγ
  have hne := rho_d43Lift_ne hγ hs
  have e := a2cen_torus_conj_xOrbit (σ := σ) hg (unG2_vec_fix σ) unG2_vec_rho hβ u
  rw [unG2_rootChar, Units.val_neg, Units.val_one, neg_one_mul] at e
  change g * xOrbit σ.toRingHom (d43Lift (hexPos (-3))) u * g⁻¹ =
    (xOrbit σ.toRingHom (d43Lift (hexPos (-3))) u)⁻¹
  rw [e]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← xOrbit_add σ.toRingHom hβ hne, add_neg_cancel, xOrbit_zero]

end Act

section Main

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.un_hex_abelian (h : A2Core σ d q) {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k)
    (hk2 : k % 2 ≠ 0) {x y : twistedGroup σ.toRingHom}
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) k) (hy : y ∈ hexGroup (twistedX σ.toRingHom) k) :
    x * y = y * x := by
  have _ := h
  have _ := hk2
  have hγ : IsRoot .G2 (hexPos k) := isRoot_hexPos hk.1 hk.2
  have hx' : ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos k) := hx
  have hy' : ((y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos k) := hy
  exact Subtype.ext (commute_of_mem_twistedRootSubgroupD4 σ.toRingHom hγ hx' hy').eq

theorem A2Core.un_chat (h : A2Core σ d q) (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∃ t : twistedGroup σ.toRingHom, t ∈ ⨆ i, hHat σ.toRingHom i ∧ a2Phi h φ t = t ∧
      a2Phi h (unTau σ ε) t = t ∧ t * t = 1 ∧
      ∀ y ∈ hexGroup (twistedX σ.toRingHom) (-3), t * y * t⁻¹ = y⁻¹ := by
  have _ := hεσ
  obtain ⟨g, hg, hgc⟩ := a2_torus_mem h (a := 1) (b := -1) (map_one _) (unG2_neg_one_fix σ)
  have hgΓ : g ∈ twistedGroup σ.toRingHom :=
    (iSup_le fun i => hHatE_le_twistedGroup h.cube_apply i) hg
  have hgc' : (g : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag (a2tcVec 1 1 (-1) 1) := hgc
  have htmat : (((⟨g, hgΓ⟩ : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (a2tcVec 1 1 (-1) 1) := hgc'
  refine ⟨⟨g, hgΓ⟩, mem_iSup_hHat_of_mem_hHatE σ.toRingHom h.cube_apply hg, ?_, ?_, ?_, ?_⟩
  · rw [a2Phi_eq_iff h φ hφ, htmat, a2tor_conj_rootDiagUnit]
    exact congrArg _ (funext (unG2_vec_fix σ))
  · refine Subtype.ext (Subtype.ext ?_)
    rw [coe_a2Phi_unTau, htmat, ← unAmb_apply, unAmb_rootDiagUnit]
    exact congrArg _ (funext (unG2_vec_inv_map ε))
  · refine Subtype.ext (Subtype.ext ?_)
    show (g : ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K) = 1
    rw [hgc', ← rootDiagUnit_mul, unG2_vec_mul_self, rootDiagUnit_one]
  · intro y hy
    exact Subtype.ext (unG2_conj_neg_three h.cube_apply hgc' hy)

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
