module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Layer

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}

theorem LayerCtx.hOspan (L : LayerCtx Ω c) : classicalInvolutionOddCore ↥(pSpan (PY Ω c)) = ⊥ := by
  have hspan := pSpan_PY (Ω := Ω) (c := c) L.h2
  have hOY : classicalInvolutionOddCore ↥(rLayer Ω c) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp L.hO
  exact classicalInvolutionOddCore_eq_bot_of_mulEquiv (MulEquiv.subgroupCongr hspan).symm hOY

theorem LayerCtx.XC (L : LayerCtx Ω c) : pSpan (PY Ω c) ≤ Subgroup.centralizer ({c} : Set Y) := by
  rw [pSpan_PY L.h2]
  exact TwinPerpV3.rLayer_le_centralizer _ _

theorem LayerCtx.conj_X (L : LayerCtx Ω c) {g y : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y))
    (hy : y ∈ pSpan (PY Ω c)) : g * y * g⁻¹ ∈ pSpan (PY Ω c) := by
  have hperm : ∀ J ∈ PY Ω c, conjSub g J ∈ PY Ω c := by
    intro J hJ
    refine ⟨L.hΩ.conjInvariant g J hJ.1, ?_⟩
    have := conjSub_mono (n := g) hJ.2
    rwa [conjSub_eq_self_of_mem hg] at this
  exact conj_mem hperm y hy

theorem LayerCtx.rho_ae (L : LayerCtx Ω c) {y : Y} (hy : y ∈ pSpan (PY Ω c)) :
    L.ρ y ∈ TL4.aeModel 6 := by
  rw [L.hρ.onSpan y hy]
  exact TL4.AECov.mem_aeModel L.I ⟨y, hy⟩

theorem LayerCtx.rho_surj (L : LayerCtx Ω c) {x : AEQ 6} (hx : x ∈ TL4.aeModel 6) :
    ∃ y ∈ pSpan (PY Ω c), L.ρ y = x := by
  have hx' : x ∈ L.I.φ.range := by
    rw [L.I.range_eq]
    exact hx
  obtain ⟨w, rfl⟩ := hx'
  exact ⟨w.1, w.2, by rw [L.hρ.onSpan _ w.2]⟩

theorem LayerCtx.rho_c (L : LayerCtx Ω c) (hcX : c ∈ pSpan (PY Ω c)) : L.ρ c = 1 := by
  have hz : (⟨c, hcX⟩ : ↥(pSpan (PY Ω c))) ∈ Subgroup.center ↥(pSpan (PY Ω c)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (L.XC g.2))
  have := center_le_ker (by norm_num : 5 ≤ 6) L.I hz
  rw [L.hρ.onSpan c hcX]
  exact MonoidHom.mem_ker.mp this

theorem LayerCtx.perm_of_mem_pCoreOf (L : LayerCtx Ω c) {y : Y}
    (hy : y ∈ pCoreOf 2 (pSpan (PY Ω c))) :
    ∃ hyX : y ∈ pSpan (PY Ω c), TC.Thin.permQ 6 (L.I.φ ⟨y, hyX⟩) = 1 := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨y'.2, ?_⟩
  have hTM : ((pCore 2 ↥(pSpan (PY Ω c))).map L.I.φ) ≤ aeBarOver (alternatingGroup (Fin 6)) := by
    rw [← TL4.aeModel_eq]
    rintro _ ⟨p, -, rfl⟩
    exact TL4.AECov.mem_aeModel L.I p
  have hTn : ∀ x ∈ aeBarOver (alternatingGroup (Fin 6)), ∀ t ∈ (pCore 2 ↥(pSpan (PY Ω c))).map L.I.φ,
      x * t * x⁻¹ ∈ (pCore 2 ↥(pSpan (PY Ω c))).map L.I.φ := by
    intro x hx t ht
    rw [← TL4.aeModel_eq] at hx
    have hx' : x ∈ L.I.φ.range := by
      rw [L.I.range_eq]
      exact hx
    obtain ⟨w, rfl⟩ := hx'
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨w * p * w⁻¹, (pCore_normal (p := 2) (G := ↥(pSpan (PY Ω c)))).conj_mem p hp w, by simp⟩
  have hT2 : IsPGroup 2 ↥((pCore 2 ↥(pSpan (PY Ω c))).map L.I.φ) :=
    (pCore_isPGroup (p := 2) (G := ↥(pSpan (PY Ω c)))).map L.I.φ
  have hle := le_ker_permQ_of_normal (n := 6) (A := alternatingGroup (Fin 6)) le_rfl
    (fun N hNA hNn hN2 => eq_bot_of_normal_two_alternating (by norm_num) hNA hNn hN2) hTM hTn hT2
  exact hle ⟨y', hy', rfl⟩

theorem LayerCtx.mem_pCoreOf_of_perm (L : LayerCtx Ω c) {y : Y} (hy : y ∈ pSpan (PY Ω c))
    (hp : TC.Thin.permQ 6 (L.I.φ ⟨y, hy⟩) = 1) : y ∈ pCoreOf 2 (pSpan (PY Ω c)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan (PY Ω c) with hX
  set N : Subgroup ↥X := ((TC.Thin.permQ 6).comp L.I.φ).ker with hN
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hN2 : IsPGroup 2 ↥N := by
    intro z
    have hz : TC.Thin.permQ 6 (L.I.φ z.1) = 1 := z.2
    have hsq : L.I.φ z.1 * L.I.φ z.1 = 1 := mul_self_of_mem_ker_permQ hz
    have hnn : z.1 * z.1 ∈ L.I.φ.ker := by rw [MonoidHom.mem_ker, map_mul, hsq]
    obtain ⟨k, hk⟩ := (L.I.isPGroup_ker L.hOspan) ⟨z.1 * z.1, hnn⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (z.1 * z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : (z.1 : ↥X) ^ 2 ^ (k + 1) = 1 := by
      calc (z.1 : ↥X) ^ 2 ^ (k + 1) = ((z.1 : ↥X) ^ 2) ^ 2 ^ k := by rw [pow_succ, mul_comm, pow_mul]
        _ = (z.1 * z.1) ^ 2 ^ k := by rw [sq]
        _ = 1 := hk'
    simpa using h1
  have hle : N ≤ pCore 2 ↥X := le_sSup ⟨hNn, hN2⟩
  exact ⟨⟨y, hy⟩, hle (by rw [hN, MonoidHom.mem_ker, MonoidHom.comp_apply]; exact hp), rfl⟩

theorem LayerCtx.mem_pCoreOf_iff (L : LayerCtx Ω c) {y : Y} :
    y ∈ pCoreOf 2 (pSpan (PY Ω c)) ↔ y ∈ pSpan (PY Ω c) ∧ TC.Thin.permQ 6 (L.ρ y) = 1 := by
  constructor
  · intro hy
    obtain ⟨hyX, hp⟩ := L.perm_of_mem_pCoreOf hy
    exact ⟨hyX, by rw [L.hρ.onSpan y hyX]; exact hp⟩
  · rintro ⟨hyX, hp⟩
    exact L.mem_pCoreOf_of_perm hyX (by rw [← L.hρ.onSpan y hyX]; exact hp)

theorem eq_or_eq_of_card_le_two {α : Type*} [Finite α] (hcard : Nat.card α ≤ 2) {a b : α} (hab : a ≠ b)
    (z : α) : z = a ∨ z = b := by
  by_contra hz
  push Not at hz
  have hinj : Function.Injective (![a, b, z] : Fin 3 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso
         simp at hij
         first
           | exact hab hij | exact hab hij.symm | exact hz.1 hij | exact hz.1 hij.symm
           | exact hz.2 hij | exact hz.2 hij.symm)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem LayerCtx.rho_ker (L : LayerCtx Ω c) (hcard : Nat.card ↥(pCoreOf 2 (pSpan (PY Ω c))) = 32)
    (hcX : c ∈ pSpan (PY Ω c)) (hc1 : c ≠ 1) :
    ∀ y ∈ pSpan (PY Ω c), L.ρ y = 1 → y = 1 ∨ y = c := by
  classical
  set X := pSpan (PY Ω c) with hX
  have hle : pCoreOf 2 X ≤ X := Subgroup.map_subtype_le _
  let ψ : ↥(pCoreOf 2 X) →* AEQ 6 := L.I.φ.comp (Subgroup.inclusion hle)
  have hψ : ∀ z : ↥(pCoreOf 2 X), ψ z = L.ρ (z : Y) := fun z => by
    rw [L.hρ.onSpan _ (hle z.2)]
    rfl
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hcard] at hmul
  have h16 : 16 ≤ Nat.card ↥ψ.range := by
    have hmem : ∀ x : {x : AEQ 6 // InU x}, x.1 ∈ ψ.range := by
      intro x
      obtain ⟨y, hy, hyx⟩ := L.rho_surj x.2.1
      have hyE : y ∈ pCoreOf 2 X := L.mem_pCoreOf_iff.2 ⟨hy, by rw [hyx]; exact x.2.2⟩
      exact ⟨⟨y, hyE⟩, by rw [hψ]; exact hyx⟩
    have := Nat.card_le_card_of_injective
      (fun x : {x : AEQ 6 // InU x} => (⟨x.1, hmem x⟩ : ↥ψ.range))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥ψ.range => (z : AEQ 6)) h))
    exact sixteen_le_card_U.trans this
  have hker : Nat.card ↥ψ.ker ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 * 16 ≤ Nat.card ↥ψ.ker * Nat.card ↥ψ.range := Nat.mul_le_mul hcon h16
    omega
  have hcE : c ∈ pCoreOf 2 X :=
    L.mem_pCoreOf_iff.2 ⟨hcX, by rw [L.rho_c hcX]; exact map_one _⟩
  intro y hy hρy
  have hyE : y ∈ pCoreOf 2 X := L.mem_pCoreOf_iff.2 ⟨hy, by rw [hρy]; exact map_one _⟩
  have hyk : (⟨y, hyE⟩ : ↥(pCoreOf 2 X)) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ]
    exact hρy
  have hck : (⟨c, hcE⟩ : ↥(pCoreOf 2 X)) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ]
    exact L.rho_c hcX
  have hne : (⟨1, ψ.ker.one_mem⟩ : ↥ψ.ker) ≠ ⟨⟨c, hcE⟩, hck⟩ := by
    intro h
    exact hc1 (congrArg (fun z : ↥ψ.ker => ((z : ↥(pCoreOf 2 X)) : Y)) h).symm
  rcases eq_or_eq_of_card_le_two hker hne ⟨⟨y, hyE⟩, hyk⟩ with h | h
  · left
    exact congrArg (fun z : ↥ψ.ker => ((z : ↥(pCoreOf 2 X)) : Y)) h
  · right
    exact congrArg (fun z : ↥ψ.ker => ((z : ↥(pCoreOf 2 X)) : Y)) h

theorem estr_of (L : LayerCtx Ω c) (hcard : Nat.card ↥(pCoreOf 2 (pSpan (PY Ω c))) = 32)
    (hcE : c ∈ pCoreOf 2 (pSpan (PY Ω c)))
    (hsq : ∀ x ∈ pCoreOf 2 (pSpan (PY Ω c)), x * x = 1)
    (hconj : ∀ g ∈ Subgroup.centralizer ({c} : Set Y), ∀ e ∈ pCoreOf 2 (pSpan (PY Ω c)),
      g * e * g⁻¹ ∈ pCoreOf 2 (pSpan (PY Ω c))) :
    EStr c (pSpan (PY Ω c)) (pCoreOf 2 (pSpan (PY Ω c))) L.ρ := by
  have hcX : c ∈ pSpan (PY Ω c) := (L.mem_pCoreOf_iff.1 hcE).1
  exact
    { hc := L.hc
      hc1 := L.hc1
      XC := L.XC
      rho_mul := L.hρ.mul
      rho_one := L.hρ.one
      X_conj := fun g hg y hy => L.conj_X hg hy
      rho_ae := fun y hy => L.rho_ae hy
      rho_surj := fun x hx => L.rho_surj hx
      rho_ker := L.rho_ker hcard hcX L.hc1
      c_mem := hcX
      rho_c := L.rho_c hcX
      E_iff := fun y => L.mem_pCoreOf_iff
      E_card := hcard
      E_sq := hsq
      E_conj := hconj }

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
