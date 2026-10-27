module

public import CFSG.GF2Type.Smith1979.GammaU.Transport
public import CFSG.GF2Type.Smith1979.GammaU.PairBridge
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPair
public import CFSG.GF2Type.Smith1979.GammaU.Enum
public import Certificates.Certificate16966
public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
import Certificates.Kernel.GammaU.BaseBridge
public import Certificates.Certificate16968

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem idR_mem_enumGrp (gs : List (Array ℕ)) : idR ∈ Enum.enumGrp gs :=
  mem_bfsClosure _ _ _ [idR] _ [] idR (by simp)

theorem mem_genGrp_iff {gs : List (Array ℕ)} (hgs : Viol.GensOK gs)
    (hc : Enum.closedCheck gs (Enum.enumGrp gs) = true) (U : V12 ≃ₗ[ZMod 2] V12) :
    U ∈ Viol.genGrp gs ↔ ∃ x ∈ Enum.enumGrp gs, ∀ v, U v = linOfRows x v := by
  constructor
  · exact fun hU => Enum.complete (idR_mem_enumGrp gs) hc U hU
  · rintro ⟨x, hx, hUx⟩
    obtain ⟨-, U', hU', hU'x⟩ := Enum.enumGrp_sound hgs x hx
    have : U = U' := LinearEquiv.ext fun v => by rw [hUx, hU'x]
    rw [this]
    exact hU'

theorem map_conj_map_conj (a b : V12 ≃ₗ[ZMod 2] V12) (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    (N.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      N.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem nlOKAt_spec {i : ℕ} {W : List (Array ℕ × Array ℕ)}
    (h : CFSG.GammaU.Native.nlOKAt (CFSG.GammaU.Native.spanList CFSG.GammaU.Native.d0)
      (CFSG.GammaU.Native.compOf i) W = true) :
    ∀ p ∈ W,
      gammaUN p.1 = true ∧ gammaUN p.2 = true ∧ mulR p.1 p.2 = idR ∧ mulR p.2 p.1 = idR ∧
        appN p.1 a0 = a0 ∧ (∀ d ∈ d0, appN p.1 d ∈ spanList d0) ∧
        (∀ d ∈ d0, appN p.2 d ∈ spanList d0) ∧
        (∀ x ∈ compOf i, mulR (mulR p.1 x) p.2 ∈ compOf i) ∧
        ∀ x ∈ compOf i, mulR (mulR p.2 x) p.1 ∈ compOf i := by
  rintro ⟨g, gi⟩ hp
  have := List.all_eq_true.1 h (g, gi) hp
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    native_gammaUN, native_mulR, native_idR, native_appN, native_a0, native_d0, native_spanList,
    native_compOf] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem nlMem_gen {i : ℕ} {g gi : Array ℕ} (hg : gammaUN g = true) (hmul : mulR g gi = idR)
    (ha : appN g a0 = a0) (hd : ∀ d ∈ d0, appN g d ∈ spanList d0)
    (hdi : ∀ d ∈ d0, appN gi d ∈ spanList d0) (hc : ∀ x ∈ compOf i, mulR (mulR g x) gi ∈ compOf i)
    (hci : ∀ x ∈ compOf i, mulR (mulR gi x) g ∈ compOf i) : NLMem i (toU g hg) where
  mem := gammaUN_spec hg
  fix := by rw [toU_apply, ← vecOf_appN, ha]
  d0 y := by
    constructor
    · intro hy
      have := mem_spanOf_d0_of_rows hdi hy
      rwa [← inv_rows hg hmul, inv_apply_apply] at this
    · intro hy
      rw [toU_apply]
      exact mem_spanOf_d0_of_rows hd hy
  norm l := by
    constructor
    · rintro ⟨x, hx, hlx⟩
      refine ⟨mulR (mulR gi x) g, hci x hx, fun y => ?_⟩
      rw [linOfRows_mulR, linOfRows_mulR, ← hlx, ← inv_rows hg hmul, ← toU_apply g hg]
      simp only [LinearEquiv.mul_apply, inv_apply_apply]
    · rintro ⟨x, hx, hlx⟩
      refine ⟨mulR (mulR g x) gi, hc x hx, fun y => ?_⟩
      rw [linOfRows_mulR, linOfRows_mulR, ← hlx, ← inv_rows hg hmul, ← toU_apply g hg]
      simp only [LinearEquiv.mul_apply]

theorem pair_census
    {i : ℕ} (hi : i = 0 ∨ i = 1) {r₁ r₂ : Array ℕ}
    (hr₁ : r₁ ∈ unitaryElts i) (hr₂ : r₂ ∈ unitaryElts i) (hne : r₁ ≠ r₂) {n₁ n₂ : ℕ}
    (hn₁ : n₁ ∈ colPts r₁) (hn₂ : n₂ ∈ colPts r₂) {De₁ De₂ : Submodule (ZMod 2) V12}
    {Le₁ Le₂ : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H₁ : Hyp (vecOf n₁) De₁ Le₁)
    (H₂ : Hyp (vecOf n₂) De₂ Le₂) (hs₁ : ∃ l ∈ Le₁, ∀ y, l y = linOfRows r₁ y)
    (hs₂ : ∃ l ∈ Le₂, ∀ y, l y = linOfRows r₂ y) (ha₁ : vecOf a0 ∈ De₁) (ha₂ : vecOf a0 ∈ De₂)
    (hc₁ : Nat.card (candGrp i Le₁) = 1152) (hc₂ : Nat.card (candGrp i Le₂) = 1152) :
    Viol.Violation (candGrp i Le₁ ⊔ candGrp i Le₂) (compOf i) (compOf i) ∨
      ResGrp i (candGrp i Le₁ ⊔ candGrp i Le₂) := by
  have hi32 : i < 32 := by omega
  have h63 := Certificates.certificate16963
  have h64 := Certificates.certificate16964
  obtain ⟨r0, T, m, te, hB, hP⟩ := Certificates.certificate16968 i hi
  obtain ⟨U, h₁, h₂, hU, hUR, hh₁, hh₂, hrr₁, hrr₂, hcfg⟩ := hP r₁ hr₁ r₂ hr₂ hne
  obtain ⟨G₁, hG₁, hR₁⟩ :=
    census_conj_cfg h63 h64 hi32 hB (hU.mul hh₁) hrr₁ hcfg hn₁ H₁ hs₁ ha₁ hc₁
  obtain ⟨G₂, hG₂, hR₂⟩ :=
    census_conj_cfg h63 h64 hi32 hB (hU.mul hh₂) hrr₂ hG₁ hn₂ H₂ hs₂ ha₂ hc₂
  have hsup : candGrp i Le₁ ⊔ candGrp i Le₂ = (G₁.map (MulAut.conj h₁).toMonoidHom ⊔
      G₂.map (MulAut.conj h₂).toMonoidHom).map (MulAut.conj U).toMonoidHom := by
    rw [hR₁, hR₂, Subgroup.map_sup, map_conj_map_conj, map_conj_map_conj]
  rw [hsup]
  rcases hG₂ with hv | hres
  · exact Or.inl (violation_conj Certificates.certificate16966 hi32 hU hv)
  · exact Or.inr (hUR _ hres)

end CFSG.GF2Type.Smith1979.GammaU.StepA
