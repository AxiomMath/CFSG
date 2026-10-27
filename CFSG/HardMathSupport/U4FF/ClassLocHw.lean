module

public import CFSG.HardMathSupport.U4FF.ClassLocSound

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups

section Eigen

variable {fs : List FK} (S : LocSpec fs) {k : Type*} [Field k] [CharP k 2]

theorem LocSpec.locMat_eigen {v : Fin (ambDim fs) → ZMod 2} (hv : S.Pi *ᵥ v = v) (g : SL(4, k))
    (w : k) (hamb : ambRepF k fs g *ᵥ (fun x => f2 k (v x)) = w • (fun x => f2 k (v x))) :
    S.locMat k g *ᵥ (S.Pmk k *ᵥ (fun x => f2 k (v x))) =
      w • (S.Pmk k *ᵥ (fun x => f2 k (v x))) := by
  set vk : Fin (ambDim fs) → k := fun x => f2 k (v x) with hvk
  have hPi : S.Pik k *ᵥ vk = vk := by
    rw [LocSpec.Pik_eq_map, hvk, map_mulVec', hv]
  have hz := (S.Stab_all (k := k) g).2
  have hBP : S.Bk k *ᵥ (S.Pmk k *ᵥ vk) = vk - (S.zetak k ⬝ᵥ vk) • S.zk k := by
    have h1 : S.Pik k *ᵥ vk = (S.Bk k * S.Pmk k) *ᵥ vk +
        (vecMulVec (S.zk k) (S.zetak k)) *ᵥ vk := by
      unfold LocSpec.Pik
      rw [Matrix.add_mulVec]
    rw [hPi, vecMulVec_mulVec', ← Matrix.mulVec_mulVec] at h1
    rw [eq_sub_iff_add_eq]
    exact h1.symm
  have hmain : S.locMat k g *ᵥ (S.Pmk k *ᵥ vk) =
      S.Pmk k *ᵥ (ambRepF k fs g *ᵥ (S.Bk k *ᵥ (S.Pmk k *ᵥ vk))) := by
    unfold LocSpec.locMat
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmain, hBP, Matrix.mulVec_sub, Matrix.mulVec_smul, hz, hamb, Matrix.mulVec_sub]
  simp only [Matrix.mulVec_smul, S.Pmk_z k]
  simp

end Eigen

section Hw

variable (a b c : Bool) (h1 : LocValid1 a b c)

include h1

@[expose] noncomputable def yloc (k : Type*) [Field k] [CharP k 2] : Fin (locM a b c) → k :=
  (locSpec a b c h1).Pmk k *ᵥ (fun x => f2 k (hwVec (fsOf a b c) x))

theorem Pi_mulVec_hw :
    (locSpec a b c h1).Pi *ᵥ hwVec (fsOf a b c) = hwVec (fsOf a b c) := by
  have hb := h1.1
  have hp := h1.2.1
  have hPi := toMat_piMasks (fsOf a b c) (locM a b c) (locData a b c).bcols
    (locData a b c).pmcols (locData a b c).z (locData a b c).zeta hb hp
  have hs := size_piMasks (fsOf a b c) (locData a b c).bcols (locData a b c).pmcols
    (locData a b c).z (locData a b c).zeta hp
  have h := toMat_apply _ (ambDim (fsOf a b c)) (ambDim (fsOf a b c)) hs
    (1 <<< hwEnc (fsOf a b c))
  have e9 := h1.2.2.2.2.2.2.2.2.1
  change MCols.apply (MCols.add (MCols.mul (locData a b c).bcols (locData a b c).pmcols)
    (MCols.mul (MCols.col (locData a b c).z) (zrowOf (ambDim (fsOf a b c))
      (locData a b c).zeta))) (1 <<< hwEnc (fsOf a b c)) = 1 <<< hwEnc (fsOf a b c) at e9
  rw [e9, hPi] at h
  exact h.symm

theorem ambDF_mulVec_hw {i j : Fin 4} (hij : i < j) {r : ℕ}
    (hr : r ∈ Finset.range ((fsOf a b c).length + 1)) (hr1 : 1 ≤ r) :
    ambDF (fsOf a b c) i j r *ᵥ hwVec (fsOf a b c) = 0 := by
  have e10 := h1.2.2.2.2.2.2.2.2.2.1 i j hij r hr hr1
  have ht : (tabD (fsOf a b c) i j r).size = ambDim (fsOf a b c) := tab_size _
  have hD : (tabD (fsOf a b c) i j r).toMat (ambDim (fsOf a b c)) (ambDim (fsOf a b c)) =
      ambDF (fsOf a b c) i j r := toMat_tab _
  have h := toMat_apply _ (ambDim (fsOf a b c)) (ambDim (fsOf a b c)) ht (1 <<< hwEnc (fsOf a b c))
  rw [e10, hD] at h
  funext x
  have := congrFun h x
  rw [bitF_zero] at this
  exact this.symm

variable {k : Type*} [Field k] [CharP k 2]

theorem locMat_upper_fix {i j : Fin 4} (hij : i ≠ j) (hlt : i < j) (t : k) :
    (locSpec a b c h1).locMat k (Matrix.SpecialLinearGroup.transvection hij t) *ᵥ yloc a b c h1 k =
      yloc a b c h1 k :=
  LocSpec.locMat_fixes (locSpec a b c h1) (Pi_mulVec_hw a b c h1)
    (fun i j hij r hr hr1 => ambDF_mulVec_hw a b c h1 hij hr hr1) hij hlt t

theorem yloc_eq_map :
    yloc a b c h1 k = fun x => f2 k (((locSpec a b c h1).Pm *ᵥ hwVec (fsOf a b c)) x) := by
  unfold yloc LocSpec.Pmk
  rw [map_mulVec' (f2 k) (locSpec a b c h1).Pm (hwVec (fsOf a b c))]

theorem yloc_ne_zero : yloc a b c h1 k ≠ 0 := by
  obtain ⟨i, hi, hbit⟩ := h1.2.2.2.2.2.2.2.2.2.2
  have hp := h1.2.1
  have h := toMat_apply (locData a b c).pmcols (locM a b c) (ambDim (fsOf a b c)) hp
    (1 <<< hwEnc (fsOf a b c))
  intro h0
  rw [yloc_eq_map] at h0
  have hi' : i < locM a b c := Finset.mem_range.mp hi
  have h0i : f2 k (((locSpec a b c h1).Pm *ᵥ hwVec (fsOf a b c)) ⟨i, hi'⟩) = 0 :=
    congrFun h0 ⟨i, hi'⟩
  have h00 : ((locSpec a b c h1).Pm *ᵥ hwVec (fsOf a b c)) ⟨i, hi'⟩ = 0 := by
    have := (map_eq_zero_iff (f2 k) (f2 k).injective).mp h0i
    exact this
  have h2 := congrFun h ⟨i, hi'⟩
  change bitF (yMasks (fsOf a b c) (locData a b c)) i = ((locSpec a b c h1).Pm *ᵥ
    hwVec (fsOf a b c)) ⟨i, hi'⟩ at h2
  rw [h00] at h2
  have : bitF (yMasks (fsOf a b c) (locData a b c)) i = 1 := by simp [bitF, hbit]
  rw [this] at h2
  exact one_ne_zero h2

theorem Pm_hwVec_eq :
    (locSpec a b c h1).Pm *ᵥ hwVec (fsOf a b c) =
      fun i : Fin (locM a b c) => bitF (yMasks (fsOf a b c) (locData a b c)) (i : ℕ) :=
  (toMat_apply (locData a b c).pmcols (locM a b c) (ambDim (fsOf a b c)) h1.2.1
    (1 <<< hwEnc (fsOf a b c))).symm

end Hw

section PiIotaData

@[expose] def pirMat (a b c : Bool) :
    Matrix (Fin (locM true true true)) (Fin (locM a b c)) (ZMod 2) :=
  (locData a b c).pir.toMat (locM true true true) (locM a b c)

@[expose] def iolMat (a b c : Bool) :
    Matrix (Fin (locM a b c)) (Fin (locM true true true)) (ZMod 2) :=
  (locData a b c).iol.toMat (locM a b c) (locM true true true)

variable (a b c : Bool) (h3 : LocValid3 a b c)

include h3

theorem picMat_mul_pirMat : picMat a b c * pirMat a b c = 1 := by
  have e := toMat_mul (locData a b c).pic (locData a b c).pir (locM a b c) (locM true true true)
    (locM a b c) h3.1 h3.2.1
  rw [h3.2.2.2.2.1, toMat_one] at e
  exact e.symm

theorem iolMat_mul_iocMat : iolMat a b c * iocMat a b c = 1 := by
  have e := toMat_mul (locData a b c).iol (locData a b c).ioc (locM a b c) (locM true true true)
    (locM a b c) h3.2.2.2.1 h3.2.2.1
  rw [h3.2.2.2.2.2.1, toMat_one] at e
  exact e.symm

variable (h1 : LocValid1 a b c) (hρ : LocValid1 true true true)

include h1 hρ

theorem picMat_mulVec_hw :
    picMat a b c *ᵥ ((locSpec true true true hρ).Pm *ᵥ hwVec (fsOf true true true)) =
      (locSpec a b c h1).Pm *ᵥ hwVec (fsOf a b c) := by
  rw [Pm_hwVec_eq true true true hρ, Pm_hwVec_eq a b c h1]
  have h := toMat_apply (locData a b c).pic (locM a b c) (locM true true true) h3.1
    (yMasks (fsOf true true true) (locData true true true))
  rw [h3.2.2.2.2.2.2.1] at h
  exact h.symm

variable {k : Type*} [Field k] [CharP k 2]

theorem picMat_mulVec_yloc :
    (picMat a b c).map (f2 k) *ᵥ yloc true true true hρ k = yloc a b c h1 k := by
  have := congrArg (fun v : Fin (locM a b c) → ZMod 2 => fun x => f2 k (v x))
    (picMat_mulVec_hw a b c h3 h1 hρ)
  simp only at this
  rw [yloc_eq_map true true true hρ, yloc_eq_map a b c h1, ← this]
  rw [map_mulVec' (f2 k) (picMat a b c)]

end PiIotaData

end CFSG.HardMathSupport.U4FF
