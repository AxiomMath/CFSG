module

public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.CurtisTits.Perfect
public import CFSG.Adapters.SpecialLinearPerfect

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem isRoot_d4Root
    {k : ℕ} (hk : k < (Tag.rootCertificate d4).roots.length) :
    IsRoot d4 (d4Root k) :=
  RootCertificate.isRoot_root (Tag.rootCertificate_check d4) k hk

theorem rho_d4Root_22 : rho (d4Root 22) = d4Root 22 := by decide

theorem rho_d4Root_21 : rho (d4Root 21) = d4Root 21 := by decide

theorem d4Root_two : d4Root 2 = Pi.single (nd 2) 1 := by decide

theorem commutator_xPar_d4Root
    (s t : K) :
    ⁅𝕩 (d4Root 22) s, 𝕩 (d4Root 21) t⁆ = 𝕩 (Pi.single (nd 2) 1) (s * t) := by
  have h22 : 22 < (Tag.rootCertificate d4).roots.length := by decide
  have h21 : 21 < (Tag.rootCertificate d4).roots.length := by decide
  have h2 : 2 < (Tag.rootCertificate d4).roots.length := by decide
  have hcheck : RootOps.repCheck d4 22 21 [(1, 1, 2, 1)] = true := by decide +kernel
  have key := commutator_eltElement_of_repCheck (τ := d4)
    (RootOps.d4_allValid : RootOps.allValid d4 = true) hcheck h2
    (α := ⟨d4Root 22, isRoot_d4Root h22⟩) (β := ⟨d4Root 21, isRoot_d4Root h21⟩)
    (RootOps.rootPos_eq h22 rfl) (RootOps.rootPos_eq h21 rfl) s t
  have hr : RootOps.rootAt d4 2 h2 = ⟨Pi.single (nd 2) 1, isRoot_single d4 (nd 2)⟩ :=
    Subtype.ext d4Root_two
  rw [commutatorElement_def, xPar_of_isRoot (isRoot_d4Root h22),
    xPar_of_isRoot (isRoot_d4Root h21), xPar_of_isRoot (isRoot_single d4 (nd 2)), key, hr]
  congr 1
  push_cast
  ring

section Fundamental

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem xPar_d4Root_mem_twistedGroup
    {k : ℕ} (hk : k < (Tag.rootCertificate d4).roots.length)
    (hfix : rho (d4Root k) = d4Root k) {c : K} (hc : σ c = c) :
    𝕩 (d4Root k) c ∈ twistedGroup σ :=
  twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_d4Root hk))
    (xPar_mem_of_fixed hσ (isRoot_d4Root hk) hfix hc)

theorem twistedRootGroup_long_le_commutator :
    twistedRootGroup σ (Pi.single (ng 0) 1) ≤ commutator (twistedGroup σ) := by
  intro x hx
  rw [mem_twistedRootGroup] at hx
  obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
    proj_single_two rho_single_two _).1 hx
  have h22 : 22 < (Tag.rootCertificate d4).roots.length := by decide
  have h21 : 21 < (Tag.rootCertificate d4).roots.length := by decide
  set y : twistedGroup σ := ⟨_, xPar_d4Root_mem_twistedGroup hσ h22 rho_d4Root_22 hc⟩
  set z : twistedGroup σ := ⟨_, xPar_d4Root_mem_twistedGroup hσ h21 rho_d4Root_21 (map_one σ)⟩
  have e : x = ⁅y, z⁆ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, y, z]
    rw [← commutatorElement_def, commutator_xPar_d4Root, mul_one, hxc]
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z)

theorem twistedRootGroup_short_le_commutator
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)) :
    twistedRootGroup σ (Pi.single (ng 1) 1) ≤ commutator (twistedGroup σ) := by
  intro x hx
  rw [mem_twistedRootGroup] at hx
  obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_single d4 (nd 0))
    proj_single_zero rho_single_zero_ne _).1 hx
  have e : x = slShort σ hσ (sl2Upper c) := by
    apply Subtype.ext
    rw [slShort_upper, hc, xOrbit_single]
  have hmem : sl2Upper c ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Group.isPerfect_def.1 hSL]
    exact Subgroup.mem_top _
  have hle : (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).map (slShort σ hσ) ≤
      commutator (twistedGroup σ) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rw [e]
  exact hle (Subgroup.mem_map_of_mem _ hmem)

theorem twistedRootGroup_single_le_commutator
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)) (i : Fin (Tag.rank .G2)) :
    twistedRootGroup σ (Pi.single i 1) ≤ commutator (twistedGroup σ) := by
  match i with
  | ⟨0, _⟩ => exact twistedRootGroup_long_le_commutator hσ
  | ⟨1, _⟩ => exact twistedRootGroup_short_le_commutator hσ hSL

theorem twistedGroup_isPerfect
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Group.IsPerfect (twistedGroup σ) :=
  isPerfect_of_rootGroup_single_le_commutator (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ).two_smul_le
    fun i => twistedRootGroup_single_le_commutator hσ hSL i

end Fundamental

theorem sigma_three_of_card [Finite K] {σ : K →+* K} {q : ℕ} (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) (c : K) : σ (σ (σ c)) = c := by
  have := Fintype.ofFinite K
  rw [hσq, hσq, hσq, ← pow_mul, ← pow_mul, show q * (q * q) = q ^ 3 by ring, ← hK,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem four_le_pow_three {q : ℕ} (hq : 2 ≤ q) : 4 ≤ q ^ 3 :=
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3

theorem twistedGroup_isPerfect_of_card
    [Finite K] {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) : Group.IsPerfect (twistedGroup σ) :=
  twistedGroup_isPerfect (sigma_three_of_card hK hσq)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K
      (hK ▸ four_le_pow_three hq))

end CFSG.LieType.Steinberg.TwistedD4
