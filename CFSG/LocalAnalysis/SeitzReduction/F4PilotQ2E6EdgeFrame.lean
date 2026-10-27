module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg TauCeti.GLSymplecticFin
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat mat_injective)
open CFSG.Timmesfeld.LieEmbed (c3ToF4)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedSp)

local instance f4PilotQ2E6EdgeFrameNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4Par_one_of_map_rootGroup (hK : Nat.card K = 2)
    {f : adjointGroup .F4 K →* adjointGroup .F4 K} (hf : Function.Injective f)
    {γ γ' : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hγ' : IsRoot .F4 γ')
    (hmap : ((Adjoint.f4Datum K).rootGroup γ).map f = (Adjoint.f4Datum K).rootGroup γ') :
    f (Adjoint.f4Par K γ 1) = Adjoint.f4Par K γ' 1 := by
  have hmem : f (Adjoint.f4Par K γ 1) ∈ (Adjoint.f4Datum K).rootGroup γ' := by
    rw [← hmap]
    exact ⟨_, Adjoint.xPar_mem hγ 1, rfl⟩
  obtain ⟨c, hc⟩ := (Adjoint.mem_rootGroup_iff hγ' _).1 hmem
  rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK c with h0 | h1
  · exfalso
    have hinj : Function.Injective (Adjoint.f4Par K γ) := Adjoint.xPar_injective hγ
    rw [h0, Adjoint.xPar_zero, eq_comm, ← map_one f] at hc
    have h1 : Adjoint.f4Par K γ 1 = Adjoint.f4Par K γ 0 := by
      rw [hf hc]
      exact (Adjoint.xPar_zero _).symm
    exact one_ne_zero (hinj h1)
  · rw [← hc, h1]

theorem graphAutF4_f4Par_one (hK : Nat.card K = 2) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    graphAutF4 K (Adjoint.f4Par K γ 1) = Adjoint.f4Par K (psiF4 γ) 1 :=
  f4Par_one_of_map_rootGroup (f := (graphAutF4 K).toMonoidHom) hK (graphAutF4 K).injective hγ
    (isRoot_psiF4 hγ) (map_graphAutF4_rootGroup hγ)

theorem wRep_conj_f4Par_one (hK : Nat.card K = 2) (ω : List ℕ) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    wRep K ω * Adjoint.f4Par K γ 1 * (wRep K ω)⁻¹ = Adjoint.f4Par K (wordAct ω γ) 1 := by
  have hr : IsRoot .F4 (wordAct ω γ) := by
    rw [← wordW_smul_eq_wordAct]
    exact IsRoot.smul hγ _
  exact f4Par_one_of_map_rootGroup (f := (MulAut.conj (wRep K ω)).toMonoidHom) hK
    (MulAut.conj (wRep K ω)).injective hγ hr (map_wRep_rootGroup ω hγ)

variable (K) in
@[expose] noncomputable def edgeRho (ω' : List ℕ) : StatedSp 3 K →* adjointGroup .F4 K :=
  (MulAut.conj (wRep K ω')).toMonoidHom.comp ((graphAutF4 K).toMonoidHom.comp (c3LeviHom K))

theorem edgeRho_injective (ω' : List ℕ) : Function.Injective (edgeRho K ω') :=
  (MulAut.conj (wRep K ω')).injective.comp ((graphAutF4 K).injective.comp c3LeviHom_injective)

theorem edgeRho_x (hK : Nat.card K = 2) (ω' : List ℕ) {δ : Fin 3 → ℤ}
    (hδ : IsRoot .F4 (c3ToF4 δ)) :
    edgeRho K ω' (Sp.x 3 K δ 1) = Adjoint.f4Par K (wordAct ω' (psiF4 (c3ToF4 δ))) 1 := by
  rw [edgeRho, MonoidHom.comp_apply, MonoidHom.comp_apply, c3LeviHom_x, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, graphAutF4_f4Par_one hK hδ, MulAut.conj_apply,
    wRep_conj_f4Par_one hK ω' (isRoot_psiF4 hδ)]

theorem frame_conj_graphAutF4_f4Par (hK : Nat.card K = 2) (h : adjointGroup .F4 K)
    (ω : List ℕ) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    h * wRep K ω * graphAutF4 K (Adjoint.f4Par K γ 1) * (h * wRep K ω)⁻¹ =
      h * Adjoint.f4Par K (wordAct ω (psiF4 γ)) 1 * h⁻¹ := by
  rw [graphAutF4_f4Par_one hK hγ, ← wRep_conj_f4Par_one hK ω (isRoot_psiF4 hγ)]
  group

section Sp

variable {F : Type} [Field F] [CharP F 2]

noncomputable abbrev spP01 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.positiveSum 0 1 (by decide)) 1
noncomputable abbrev spM01 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.negativeSum 0 1 (by decide)) 1
noncomputable abbrev spD01 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.difference 0 1 (by decide)) 1
noncomputable abbrev spD10 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.difference 1 0 (by decide)) 1
noncomputable abbrev spL0 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.positiveLong 0) 1
noncomputable abbrev spN0 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.negativeLong 0) 1
noncomputable abbrev spL1 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.positiveLong 1) 1
noncomputable abbrev spN1 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.negativeLong 1) 1
noncomputable abbrev spD12 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.difference 1 2 (by decide)) 1
noncomputable abbrev spD21 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.difference 2 1 (by decide)) 1
noncomputable abbrev spP12 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.positiveSum 1 2 (by decide)) 1
noncomputable abbrev spM12 (F : Type) [Field F] : StatedSp 3 F :=
  elt (.negativeSum 1 2 (by decide)) 1

noncomputable abbrev spH (F : Type) [Field F] : StatedSp 3 F := spN0 F * spD01 F * spP01 F

theorem sp_hz : spH F * (spL0 F * spN0 F) = spP01 F * spM01 F * (spD01 F * spD10 F) * spH F := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul]
  have h := edgeSp_hz
  simp only [edgeSpH, edgeSpZr, edgeSpZb] at h
  rw [h]

theorem sp_hz' : spH F * (spL1 F * spN1 F) = spP01 F * spM01 F * (spD10 F * spD01 F) * spH F := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul]
  have h := edgeSp_hz'
  simp only [edgeSpH, edgeSpZr] at h
  rw [h]

theorem sp_hu : spH F * (spD12 F * spM12 F) = spD12 F * spM12 F * spH F := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul]
  have h := edgeSp_hu
  simp only [edgeSpH] at h
  rw [h]

theorem sp_hu' : spH F * (spD21 F * spP12 F) = spD21 F * spP12 F * spH F := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul]
  have h := edgeSp_hu'
  simp only [edgeSpH] at h
  rw [h]

theorem sp_zr_cube : spP01 F * spM01 F * (spP01 F * spM01 F) * (spP01 F * spM01 F) = 1 := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul, map_one]
  have h := edgeSp_zr_cube
  simp only [edgeSpZr] at h
  rw [h, edgeCast_map_one]

theorem sp_zr_ne_one : spP01 F * spM01 F ≠ 1 := by
  intro h1
  have h := congrArg (mat 3 F) h1
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul, map_one] at h
  apply edgeSp_zr_ne_one
  apply Matrix.map_injective (edgeCast_injective (K := F))
  exact h.trans edgeCast_map_one.symm

theorem sp_zr_comm : spP01 F * spM01 F * (spD01 F * spD10 F) =
    spD01 F * spD10 F * (spP01 F * spM01 F) := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, ← Matrix.map_mul]
  have h := edgeSp_zr_comm
  simp only [edgeSpZr, edgeSpZb] at h
  rw [h]

end Sp

open CFSG.LieType.Universal.Symplectic (stdVec toStd) in
theorem edgeRho_elt (hK : Nat.card K = 2) (ω' : List ℕ) {r : RootSubgroupIndex 3}
    {δ : Fin 3 → ℤ} (hr : stdVec r = toStd 3 δ) (hδ : IsRoot .F4 (c3ToF4 δ))
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : wordAct ω' (psiF4 (c3ToF4 δ)) = γ) :
    edgeRho K ω' (elt r 1) = Adjoint.f4Par K γ 1 := by
  rw [← Sp.x_eq hr, edgeRho_x hK ω' hδ, hγ]

open CFSG.LieType.Universal.Symplectic (stdVec toStd) in
theorem c3LeviHom_elt_one {r : RootSubgroupIndex 3} {δ : Fin 3 → ℤ}
    (hr : stdVec r = toStd 3 δ) : c3LeviHom K (elt r 1) = Adjoint.f4Par K (c3ToF4 δ) 1 := by
  rw [← Sp.x_eq hr, c3LeviHom_x]

open CFSG.LieType.Universal.Symplectic (stdVec toStd) in
theorem frame_c3LeviHom_elt (hK : Nat.card K = 2) (h : adjointGroup .F4 K) (ω : List ℕ)
    {r : RootSubgroupIndex 3} {δ : Fin 3 → ℤ} (hr : stdVec r = toStd 3 δ)
    (hδ : IsRoot .F4 (c3ToF4 δ)) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : wordAct ω (psiF4 (c3ToF4 δ)) = γ) :
    h * wRep K ω * graphAutF4 K (c3LeviHom K (elt r 1)) * (h * wRep K ω)⁻¹ =
      h * Adjoint.f4Par K γ 1 * h⁻¹ := by
  rw [c3LeviHom_elt_one hr, frame_conj_graphAutF4_f4Par hK h ω hδ, hγ]

theorem edge_frame_mul (g : adjointGroup .F4 K) (a b : StatedSp 3 K) :
    g * graphAutF4 K (c3LeviHom K (a * b)) * g⁻¹ =
      g * graphAutF4 K (c3LeviHom K a) * g⁻¹ * (g * graphAutF4 K (c3LeviHom K b) * g⁻¹) := by
  rw [map_mul, map_mul]
  group

theorem edge_conj_mul_conj (h x y : adjointGroup .F4 K) : h * x * h⁻¹ * (h * y * h⁻¹) =
    h * (x * y) * h⁻¹ := by
  group

theorem edge_conj_eq_of_mul_eq {h x y : adjointGroup .F4 K} (hxy : h * x = y * h) :
    h * x * h⁻¹ = y := by
  rw [hxy, mul_inv_cancel_right]

theorem commute_f4Par_one_of_check {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ rootFinset .F4)
    (hδ : δ ∈ rootFinset .F4)
    (h : (Adjoint.iform γ δ = 0 ∧ γ + δ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 γ) (psiF4 δ) = 0 ∧ psiF4 γ + psiF4 δ ∉ rootFinset .F4)) :
    Commute (Adjoint.f4Par K γ 1) (Adjoint.f4Par K δ 1) := by
  simp only [mem_rootFinset] at h
  exact commute_of_mem_rootGroup (mem_rootFinset.1 hγ) (mem_rootFinset.1 hδ) h
    (Adjoint.xPar_mem (mem_rootFinset.1 hγ) 1) (Adjoint.xPar_mem (mem_rootFinset.1 hδ) 1)

theorem edge_conj_mul_split (g x y : adjointGroup .F4 K) :
    g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by
  group

section One

abbrev edgeV1221 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 1]

abbrev edgeV1121 : Fin (Tag.rank .F4) → ℤ := ![1, 1, 2, 1]

abbrev edgeW1 : List ℕ := [3, 2, 1, 0, 2, 1, 2]

noncomputable abbrev edgeH1 (K : Type) [Field K] : adjointGroup .F4 K :=
  Adjoint.f4Par K (-edgeV1221) 1 * Adjoint.f4Par K (Pi.single 1 1) 1 * Adjoint.f4Par K rootR 1

section Letters

variable (hK : Nat.card K = 2)
include hK

theorem edgeRho1_P01 : edgeRho K edgeW1 (spP01 K) = Adjoint.f4Par K rootR 1 :=
  edgeRho_elt hK _ (δ := ![1, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_M01 : edgeRho K edgeW1 (spM01 K) = Adjoint.f4Par K (-rootR) 1 :=
  edgeRho_elt hK _ (δ := ![-1, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_D01 : edgeRho K edgeW1 (spD01 K) = Adjoint.f4Par K (Pi.single 1 1) 1 :=
  edgeRho_elt hK _ (δ := ![1, 0, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_D10 : edgeRho K edgeW1 (spD10 K) = Adjoint.f4Par K (-Pi.single 1 1) 1 :=
  edgeRho_elt hK _ (δ := ![-1, 0, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_L0 : edgeRho K edgeW1 (spL0 K) = Adjoint.f4Par K edgeV1221 1 :=
  edgeRho_elt hK _ (δ := ![2, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_N0 : edgeRho K edgeW1 (spN0 K) = Adjoint.f4Par K (-edgeV1221) 1 :=
  edgeRho_elt hK _ (δ := ![-2, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_L1 : edgeRho K edgeW1 (spL1 K) = Adjoint.f4Par K edgeV1121 1 :=
  edgeRho_elt hK _ (δ := ![0, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_N1 : edgeRho K edgeW1 (spN1 K) = Adjoint.f4Par K (-edgeV1121) 1 :=
  edgeRho_elt hK _ (δ := ![0, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_D12 : edgeRho K edgeW1 (spD12 K) = Adjoint.f4Par K (Pi.single 0 1) 1 :=
  edgeRho_elt hK _ (δ := ![0, 1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_D21 : edgeRho K edgeW1 (spD21 K) = Adjoint.f4Par K (-Pi.single 0 1) 1 :=
  edgeRho_elt hK _ (δ := ![0, -1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_P12 : edgeRho K edgeW1 (spP12 K) = Adjoint.f4Par K root1242 1 :=
  edgeRho_elt hK _ (δ := ![0, 1, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho1_M12 : edgeRho K edgeW1 (spM12 K) = Adjoint.f4Par K (-root1242) 1 :=
  edgeRho_elt hK _ (δ := ![0, -1, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

end Letters

section Identities

variable (hK : Nat.card K = 2)
include hK

theorem edgeH1_mul_chainZ : edgeH1 K * chainZ K edgeV1221 =
    chainZ K rootR * chainZ K (Pi.single 1 1) * edgeH1 K := by
  have h := congrArg (edgeRho K edgeW1) (sp_hz (F := K))
  simp only [map_mul, edgeRho1_P01 hK, edgeRho1_M01 hK, edgeRho1_D01 hK, edgeRho1_D10 hK,
    edgeRho1_L0 hK, edgeRho1_N0 hK] at h
  simp only [edgeH1, chainZ]
  exact h

theorem edgeH1_mul_chainZ' : edgeH1 K * chainZ K edgeV1121 =
    chainZ K rootR * (Adjoint.f4Par K (-Pi.single 1 1) 1 * Adjoint.f4Par K (Pi.single 1 1) 1) *
      edgeH1 K := by
  have h := congrArg (edgeRho K edgeW1) (sp_hz' (F := K))
  simp only [map_mul, edgeRho1_P01 hK, edgeRho1_M01 hK, edgeRho1_D01 hK, edgeRho1_D10 hK,
    edgeRho1_L1 hK, edgeRho1_N1 hK, edgeRho1_N0 hK] at h
  simp only [edgeH1, chainZ]
  exact h

theorem edgeH1_mul_relay : edgeH1 K * relayAlign K root1242 = relayAlign K root1242 * edgeH1 K := by
  have h := congrArg (edgeRho K edgeW1) (sp_hu (F := K))
  simp only [map_mul, edgeRho1_P01 hK, edgeRho1_D01 hK, edgeRho1_N0 hK, edgeRho1_D12 hK,
    edgeRho1_M12 hK] at h
  simp only [edgeH1, relayAlign]
  exact h

theorem edgeH1_mul_relay' :
    edgeH1 K * relayAlign' K root1242 = relayAlign' K root1242 * edgeH1 K := by
  have h := congrArg (edgeRho K edgeW1) (sp_hu' (F := K))
  simp only [map_mul, edgeRho1_P01 hK, edgeRho1_D01 hK, edgeRho1_N0 hK, edgeRho1_D21 hK,
    edgeRho1_P12 hK] at h
  simp only [edgeH1, relayAlign']
  exact h

theorem chainZ_rootR_eq_edgeRho : chainZ K rootR = edgeRho K edgeW1 (spP01 K * spM01 K) := by
  rw [map_mul, edgeRho1_P01 hK, edgeRho1_M01 hK, chainZ]

theorem orderOf_chainZ_rootR : orderOf (chainZ K rootR) = 3 := by
  rw [chainZ_rootR_eq_edgeRho hK, orderOf_injective _ (edgeRho_injective edgeW1)]
  refine orderOf_eq_prime ?_ sp_zr_ne_one
  rw [pow_three, ← mul_assoc]
  exact sp_zr_cube

theorem chainZ_rootR_comm_a2 :
    chainZ K rootR * chainZ K (Pi.single 1 1) = chainZ K (Pi.single 1 1) * chainZ K rootR := by
  have h := congrArg (edgeRho K edgeW1) (sp_zr_comm (F := K))
  simp only [map_mul, edgeRho1_P01 hK, edgeRho1_M01 hK, edgeRho1_D01 hK, edgeRho1_D10 hK] at h
  simp only [chainZ]
  exact h

end Identities

section Frame

variable (hK : Nat.card K = 2)
include hK

theorem commute_edgeH1_f4Par {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ rootFinset .F4)
    (h1 : (Adjoint.iform (-edgeV1221) γ = 0 ∧ -edgeV1221 + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 (-edgeV1221)) (psiF4 γ) = 0 ∧
        psiF4 (-edgeV1221) + psiF4 γ ∉ rootFinset .F4))
    (h2 : (Adjoint.iform (Pi.single 1 1) γ = 0 ∧ Pi.single 1 1 + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 (Pi.single 1 1)) (psiF4 γ) = 0 ∧
        psiF4 (Pi.single 1 1) + psiF4 γ ∉ rootFinset .F4))
    (h3 : (Adjoint.iform rootR γ = 0 ∧ rootR + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 rootR) (psiF4 γ) = 0 ∧ psiF4 rootR + psiF4 γ ∉ rootFinset .F4)) :
    Commute (edgeH1 K) (Adjoint.f4Par K γ 1) :=
  ((commute_f4Par_one_of_check (by decide +kernel) hγ h1).mul_left
    (commute_f4Par_one_of_check (by decide +kernel) hγ h2)).mul_left
    (commute_f4Par_one_of_check (by decide +kernel) hγ h3)

theorem frame1_chainZ_rootR :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (chainZ K rootR) * (edgeH1 K * wRep K [3, 2])⁻¹ =
      chainZ K rootR * chainZ K (Pi.single 1 1) := by
  have e1 : wordAct [3, 2] (psiF4 rootR) = edgeV1221 := by decide +kernel
  have e2 : wordAct [3, 2] (psiF4 (-rootR)) = -edgeV1221 := by decide +kernel
  have h1 := frame_conj_graphAutF4_f4Par hK (edgeH1 K) [3, 2] isRoot_rootR
  have h2 := frame_conj_graphAutF4_f4Par hK (edgeH1 K) [3, 2] (IsRoot.neg isRoot_rootR)
  rw [e1] at h1
  rw [e2] at h2
  calc edgeH1 K * wRep K [3, 2] * graphAutF4 K (chainZ K rootR) * (edgeH1 K * wRep K [3, 2])⁻¹
      = edgeH1 K * wRep K [3, 2] * (graphAutF4 K (Adjoint.f4Par K rootR 1) *
          graphAutF4 K (Adjoint.f4Par K (-rootR) 1)) * (edgeH1 K * wRep K [3, 2])⁻¹ :=
        congrArg (fun X => edgeH1 K * wRep K [3, 2] * X * (edgeH1 K * wRep K [3, 2])⁻¹)
          (map_mul (graphAutF4 K) _ _)
    _ = _ := edge_conj_mul_split _ _ _
    _ = edgeH1 K * Adjoint.f4Par K edgeV1221 1 * (edgeH1 K)⁻¹ *
          (edgeH1 K * Adjoint.f4Par K (-edgeV1221) 1 * (edgeH1 K)⁻¹) := congrArg₂ (· * ·) h1 h2
    _ = edgeH1 K * chainZ K edgeV1221 * (edgeH1 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = chainZ K rootR * chainZ K (Pi.single 1 1) := edge_conj_eq_of_mul_eq (edgeH1_mul_chainZ hK)

theorem frame1_cPrime :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spL0 K * spN0 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ =
      chainZ K rootR * (Adjoint.f4Par K (-Pi.single 1 1) 1 * Adjoint.f4Par K (Pi.single 1 1) 1) :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH1 K * Adjoint.f4Par K edgeV1121 1 * (edgeH1 K)⁻¹ *
          (edgeH1 K * Adjoint.f4Par K (-edgeV1121) 1 * (edgeH1 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![2, 2, 1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![-2, -2, -1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH1 K * chainZ K edgeV1121 * (edgeH1 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH1_mul_chainZ' hK)

theorem frame1_P12 :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spP12 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = Adjoint.f4Par K rootE1mE2Align 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 1, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH1_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

theorem frame1_M12 :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spM12 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = Adjoint.f4Par K (-rootE1mE2Align) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, -1, -1]) (by decide)
    (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel)).trans
    (edge_conj_eq_of_mul_eq (commute_edgeH1_f4Par hK (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).eq)

theorem frame1_D12 :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spD12 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = Adjoint.f4Par K v0120 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH1_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

theorem frame1_D21 :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spD21 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = Adjoint.f4Par K (-v0120) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, -1, 0]) (by decide)
    (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel)).trans
    (edge_conj_eq_of_mul_eq (commute_edgeH1_f4Par hK (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).eq)

theorem frame1_relay :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spD01 K * spM01 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = relayAlign K root1242 :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH1 K * Adjoint.f4Par K (Pi.single 0 1) 1 * (edgeH1 K)⁻¹ *
          (edgeH1 K * Adjoint.f4Par K (-root1242) 1 * (edgeH1 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![1, 0, 0]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![-1, -2, -1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH1 K * relayAlign K root1242 * (edgeH1 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH1_mul_relay hK)

theorem frame1_relay' :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (spD10 K * spP01 K)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = relayAlign' K root1242 :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH1 K * Adjoint.f4Par K (-Pi.single 0 1) 1 * (edgeH1 K)⁻¹ *
          (edgeH1 K * Adjoint.f4Par K root1242 1 * (edgeH1 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![-1, 0, 0]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![1, 2, 1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH1 K * relayAlign' K root1242 * (edgeH1 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH1_mul_relay' hK)

end Frame

end One

section Three

abbrev edgeW3 : List ℕ := [3, 2, 1, 0, 2, 1, 3]

noncomputable abbrev edgeH3 (K : Type) [Field K] : adjointGroup .F4 K :=
  Adjoint.f4Par K (-rootS) 1 * Adjoint.f4Par K rootE1mE2Align 1 * Adjoint.f4Par K rootR 1

section Letters

variable (hK : Nat.card K = 2)
include hK

theorem edgeRho3_P01 : edgeRho K edgeW3 (spP01 K) = Adjoint.f4Par K rootR 1 :=
  edgeRho_elt hK _ (δ := ![1, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_M01 : edgeRho K edgeW3 (spM01 K) = Adjoint.f4Par K (-rootR) 1 :=
  edgeRho_elt hK _ (δ := ![-1, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_D01 : edgeRho K edgeW3 (spD01 K) = Adjoint.f4Par K rootE1mE2Align 1 :=
  edgeRho_elt hK _ (δ := ![1, 0, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_D10 : edgeRho K edgeW3 (spD10 K) = Adjoint.f4Par K (-rootE1mE2Align) 1 :=
  edgeRho_elt hK _ (δ := ![-1, 0, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_L0 : edgeRho K edgeW3 (spL0 K) = Adjoint.f4Par K rootS 1 :=
  edgeRho_elt hK _ (δ := ![2, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_N0 : edgeRho K edgeW3 (spN0 K) = Adjoint.f4Par K (-rootS) 1 :=
  edgeRho_elt hK _ (δ := ![-2, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_L1 : edgeRho K edgeW3 (spL1 K) = Adjoint.f4Par K v1110 1 :=
  edgeRho_elt hK _ (δ := ![0, 2, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_N1 : edgeRho K edgeW3 (spN1 K) = Adjoint.f4Par K (-v1110) 1 :=
  edgeRho_elt hK _ (δ := ![0, -2, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_D12 : edgeRho K edgeW3 (spD12 K) = Adjoint.f4Par K (Pi.single 0 1) 1 :=
  edgeRho_elt hK _ (δ := ![0, 1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_D21 : edgeRho K edgeW3 (spD21 K) = Adjoint.f4Par K (-Pi.single 0 1) 1 :=
  edgeRho_elt hK _ (δ := ![0, -1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_P12 : edgeRho K edgeW3 (spP12 K) = Adjoint.f4Par K rootE2pE3Align 1 :=
  edgeRho_elt hK _ (δ := ![0, 1, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

theorem edgeRho3_M12 : edgeRho K edgeW3 (spM12 K) = Adjoint.f4Par K (-rootE2pE3Align) 1 :=
  edgeRho_elt hK _ (δ := ![0, -1, -1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)

end Letters

section Identities

variable (hK : Nat.card K = 2)
include hK

theorem edgeH3_mul_chainZ : edgeH3 K * chainZ K rootS =
    chainZ K rootR * chainZ K rootE1mE2Align * edgeH3 K := by
  have h := congrArg (edgeRho K edgeW3) (sp_hz (F := K))
  simp only [map_mul, edgeRho3_P01 hK, edgeRho3_M01 hK, edgeRho3_D01 hK, edgeRho3_D10 hK,
    edgeRho3_L0 hK, edgeRho3_N0 hK] at h
  simp only [edgeH3, chainZ]
  exact h

theorem edgeH3_mul_chainZ' : edgeH3 K * chainZ K v1110 =
    chainZ K rootR * (Adjoint.f4Par K (-rootE1mE2Align) 1 * Adjoint.f4Par K rootE1mE2Align 1) *
      edgeH3 K := by
  have h := congrArg (edgeRho K edgeW3) (sp_hz' (F := K))
  simp only [map_mul, edgeRho3_P01 hK, edgeRho3_M01 hK, edgeRho3_D01 hK, edgeRho3_D10 hK,
    edgeRho3_L1 hK, edgeRho3_N1 hK, edgeRho3_N0 hK] at h
  simp only [edgeH3, chainZ]
  exact h

theorem edgeH3_mul_relay :
    edgeH3 K * relayAlign K rootE2pE3Align = relayAlign K rootE2pE3Align * edgeH3 K := by
  have h := congrArg (edgeRho K edgeW3) (sp_hu (F := K))
  simp only [map_mul, edgeRho3_P01 hK, edgeRho3_D01 hK, edgeRho3_N0 hK, edgeRho3_D12 hK,
    edgeRho3_M12 hK] at h
  simp only [edgeH3, relayAlign]
  exact h

theorem edgeH3_mul_relay' :
    edgeH3 K * relayAlign' K rootE2pE3Align = relayAlign' K rootE2pE3Align * edgeH3 K := by
  have h := congrArg (edgeRho K edgeW3) (sp_hu' (F := K))
  simp only [map_mul, edgeRho3_P01 hK, edgeRho3_D01 hK, edgeRho3_N0 hK, edgeRho3_D21 hK,
    edgeRho3_P12 hK] at h
  simp only [edgeH3, relayAlign']
  exact h

theorem chainZ_rootR_comm_e1e2 :
    chainZ K rootR * chainZ K rootE1mE2Align = chainZ K rootE1mE2Align * chainZ K rootR := by
  have h := congrArg (edgeRho K edgeW3) (sp_zr_comm (F := K))
  simp only [map_mul, edgeRho3_P01 hK, edgeRho3_M01 hK, edgeRho3_D01 hK, edgeRho3_D10 hK] at h
  simp only [chainZ]
  exact h

end Identities

section Frame

variable (hK : Nat.card K = 2)
include hK

theorem commute_edgeH3_f4Par {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ rootFinset .F4)
    (h1 : (Adjoint.iform (-rootS) γ = 0 ∧ -rootS + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 (-rootS)) (psiF4 γ) = 0 ∧
        psiF4 (-rootS) + psiF4 γ ∉ rootFinset .F4))
    (h2 : (Adjoint.iform rootE1mE2Align γ = 0 ∧ rootE1mE2Align + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 rootE1mE2Align) (psiF4 γ) = 0 ∧
        psiF4 rootE1mE2Align + psiF4 γ ∉ rootFinset .F4))
    (h3 : (Adjoint.iform rootR γ = 0 ∧ rootR + γ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 rootR) (psiF4 γ) = 0 ∧ psiF4 rootR + psiF4 γ ∉ rootFinset .F4)) :
    Commute (edgeH3 K) (Adjoint.f4Par K γ 1) :=
  ((commute_f4Par_one_of_check (by decide +kernel) hγ h1).mul_left
    (commute_f4Par_one_of_check (by decide +kernel) hγ h2)).mul_left
    (commute_f4Par_one_of_check (by decide +kernel) hγ h3)

theorem frame3_chainZ_rootR :
    edgeH3 K * wRep K [] * graphAutF4 K (chainZ K rootR) * (edgeH3 K * wRep K [])⁻¹ =
      chainZ K rootR * chainZ K rootE1mE2Align := by
  have e1 : wordAct [] (psiF4 rootR) = rootS := by decide +kernel
  have e2 : wordAct [] (psiF4 (-rootR)) = -rootS := by decide +kernel
  have h1 := frame_conj_graphAutF4_f4Par hK (edgeH3 K) [] isRoot_rootR
  have h2 := frame_conj_graphAutF4_f4Par hK (edgeH3 K) [] (IsRoot.neg isRoot_rootR)
  rw [e1] at h1
  rw [e2] at h2
  calc edgeH3 K * wRep K [] * graphAutF4 K (chainZ K rootR) * (edgeH3 K * wRep K [])⁻¹
      = edgeH3 K * wRep K [] * (graphAutF4 K (Adjoint.f4Par K rootR 1) *
          graphAutF4 K (Adjoint.f4Par K (-rootR) 1)) * (edgeH3 K * wRep K [])⁻¹ :=
        congrArg (fun X => edgeH3 K * wRep K [] * X * (edgeH3 K * wRep K [])⁻¹)
          (map_mul (graphAutF4 K) _ _)
    _ = _ := edge_conj_mul_split _ _ _
    _ = edgeH3 K * Adjoint.f4Par K rootS 1 * (edgeH3 K)⁻¹ *
          (edgeH3 K * Adjoint.f4Par K (-rootS) 1 * (edgeH3 K)⁻¹) := congrArg₂ (· * ·) h1 h2
    _ = edgeH3 K * chainZ K rootS * (edgeH3 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = chainZ K rootR * chainZ K rootE1mE2Align := edge_conj_eq_of_mul_eq (edgeH3_mul_chainZ hK)

theorem frame3_cPrime :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spL0 K * spN0 K)) *
        (edgeH3 K * wRep K [])⁻¹ =
      chainZ K rootR * (Adjoint.f4Par K (-rootE1mE2Align) 1 * Adjoint.f4Par K rootE1mE2Align 1) :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH3 K * Adjoint.f4Par K v1110 1 * (edgeH3 K)⁻¹ *
          (edgeH3 K * Adjoint.f4Par K (-v1110) 1 * (edgeH3 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![2, 2, 1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![-2, -2, -1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH3 K * chainZ K v1110 * (edgeH3 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH3_mul_chainZ' hK)

theorem frame3_P12 :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spP12 K)) *
        (edgeH3 K * wRep K [])⁻¹ = Adjoint.f4Par K v0120 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 1, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH3_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

theorem frame3_M12 :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spM12 K)) *
        (edgeH3 K * wRep K [])⁻¹ = Adjoint.f4Par K (-v0120) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, -1, -1]) (by decide)
    (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel)).trans
    (edge_conj_eq_of_mul_eq (commute_edgeH3_f4Par hK (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).eq)

theorem frame3_D12 :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spD12 K)) *
        (edgeH3 K * wRep K [])⁻¹ = Adjoint.f4Par K (Pi.single 1 1) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 1, 0]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH3_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

theorem frame3_D21 :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spD21 K)) *
        (edgeH3 K * wRep K [])⁻¹ = Adjoint.f4Par K (-Pi.single 1 1) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, -1, 0]) (by decide)
    (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel)).trans
    (edge_conj_eq_of_mul_eq (commute_edgeH3_f4Par hK (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).eq)

theorem frame3_relay :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spD01 K * spM01 K)) *
        (edgeH3 K * wRep K [])⁻¹ = relayAlign K rootE2pE3Align :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH3 K * Adjoint.f4Par K (Pi.single 0 1) 1 * (edgeH3 K)⁻¹ *
          (edgeH3 K * Adjoint.f4Par K (-rootE2pE3Align) 1 * (edgeH3 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![1, 0, 0]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![-1, -2, -1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH3 K * relayAlign K rootE2pE3Align * (edgeH3 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH3_mul_relay hK)

theorem frame3_relay' :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (spD10 K * spP01 K)) *
        (edgeH3 K * wRep K [])⁻¹ = relayAlign' K rootE2pE3Align :=
  calc _ = _ := edge_frame_mul _ _ _
    _ = edgeH3 K * Adjoint.f4Par K (-Pi.single 0 1) 1 * (edgeH3 K)⁻¹ *
          (edgeH3 K * Adjoint.f4Par K rootE2pE3Align 1 * (edgeH3 K)⁻¹) :=
        congrArg₂ (· * ·)
          (frame_c3LeviHom_elt hK _ _ (δ := ![-1, 0, 0]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
          (frame_c3LeviHom_elt hK _ _ (δ := ![1, 2, 1]) (by decide)
            (mem_rootFinset.1 (by decide +kernel)) (by decide +kernel))
    _ = edgeH3 K * relayAlign' K rootE2pE3Align * (edgeH3 K)⁻¹ := edge_conj_mul_conj _ _ _
    _ = _ := edge_conj_eq_of_mul_eq (edgeH3_mul_relay' hK)

end Frame

end Three

end CFSG.SeitzReduction.F4Pilot
