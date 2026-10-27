module

public import CFSG.Sporadic.Co1.Module.LeechOddFacts
public import CFSG.Monster.GMS.CoTwoAssembly
public import Certificates.Certificate38950

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd
open scoped Matrix

namespace CFSG.GF2Type.Widths1112

attribute [local instance] CFSG.Sporadic.Co1.Module.Odd.vecAct
  CFSG.Sporadic.Co1.Module.Odd.vecSMul

attribute [local irreducible] CFSG.Sporadic.Co1.Module.Odd.rr
  CFSG.Sporadic.Co1.Module.Odd.regsRows

theorem co1_spin
    (U : Submodule (ZMod 2) Vec24) (hωU : omega0 ∈ U) (_hTS : ∀ u ∈ U, q₀ u = 0)
    (hU : ∀ A : NativeSporadic.Co1, co1Act A omega0 = omega0 → ∀ u ∈ U, co1Act A u ∈ U)
    {y : Vec24} (hyU : y ∈ U) (hy : y ∉ Submodule.span (ZMod 2) {omega0}) :
    ∃ u ∈ U, u ≠ omega0 ∧ u ∈ CFSG.Monster.GMS.co1Orbit 0 := by
  have hfix23 : co1Act (CFSG.Sporadic.Co1.Module.Odd.reg 23) omega0 = omega0 := by
    have h : CFSG.Sporadic.Co1.Module.Odd.reg 23 • omega0 = omega0 :=
      MulAction.mem_stabilizer_iff.1
        (CFSG.Sporadic.Co1.Module.Odd.reg_fix_of_mem (i := 23) (by decide))
    rw [CFSG.Sporadic.Co1.Module.Odd.smul_eq_co1Act] at h
    exact h
  have hfix17 : co1Act (CFSG.Sporadic.Co1.Module.Odd.reg 17) omega0 = omega0 := by
    have h : CFSG.Sporadic.Co1.Module.Odd.reg 17 • omega0 = omega0 :=
      MulAction.mem_stabilizer_iff.1
        (CFSG.Sporadic.Co1.Module.Odd.reg_fix_of_mem (i := 17) (by decide))
    rw [CFSG.Sporadic.Co1.Module.Odd.smul_eq_co1Act] at h
    exact h
  have h23 : ∀ u ∈ U, rowsMatrix 24 (rr 23) *ᵥ u ∈ U := by
    intro u hu
    have h := hU (CFSG.Sporadic.Co1.Module.Odd.reg 23) hfix23 u hu
    rwa [CFSG.Sporadic.Co1.Module.Odd.co1Act_eq_mulVec, CFSG.Sporadic.Co1.Module.Odd.mat_reg] at h
  have h17 : ∀ u ∈ U, rowsMatrix 24 (rr 17) *ᵥ u ∈ U := by
    intro u hu
    have h := hU (CFSG.Sporadic.Co1.Module.Odd.reg 17) hfix17 u hu
    rwa [CFSG.Sporadic.Co1.Module.Odd.co1Act_eq_mulVec, CFSG.Sporadic.Co1.Module.Odd.mat_reg] at h
  obtain ⟨u, hu, hne, x, hx, rfl, ht⟩ :=
    Certificates.certificate38950 U hωU h23 h17 y hyU hy
  refine ⟨toVecD 24 x, hu, hne, ?_⟩
  rw [CFSG.Sporadic.Co1.Module.Odd.co1Orbit_zero_eq]
  exact (CFSG.Sporadic.Co1.Module.Odd.isT2_iff x hx).1 ht
attribute [local instance] CFSG.Sporadic.Co1.Module.Odd.vecAct
  CFSG.Sporadic.Co1.Module.Odd.vecSMul

private theorem co1F3_conj (g A : NativeSporadic.Co1) (u : Vec24) :
    co1Act (g * A * g⁻¹) (co1Act g u) = co1Act g (co1Act A u) := by
  rw [← co1Act_mul' (g * A * g⁻¹) g, show g * A * g⁻¹ * g = g * A by group, co1Act_mul' g A]

private theorem co1F3_cancel (g : NativeSporadic.Co1) (y : Vec24) :
    co1Act g (co1Act g⁻¹ y) = y := by
  rw [← co1Act_mul', mul_inv_cancel, co1Act_one']

private theorem co1F3_cancel' (g : NativeSporadic.Co1) (y : Vec24) :
    co1Act g⁻¹ (co1Act g y) = y := by
  rw [← co1Act_mul', inv_mul_cancel, co1Act_one']

private noncomputable def co1F3Lin (g : NativeSporadic.Co1) : Vec24 →ₗ[ZMod 2] Vec24 :=
  Matrix.mulVecLin (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2))

private theorem co1F3Lin_apply (g : NativeSporadic.Co1) (u : Vec24) :
    co1F3Lin g u = co1Act g u := rfl

private theorem co1F3_smul (g : NativeSporadic.Co1) (a : ZMod 2) (x : Vec24) :
    co1Act g (a • x) = a • co1Act g x := by
  rw [← co1F3Lin_apply, ← co1F3Lin_apply, map_smul]

private theorem co1F3_mem_comap (g : NativeSporadic.Co1) (U : Submodule (ZMod 2) Vec24)
    (u : Vec24) : u ∈ U.comap (co1F3Lin g) ↔ co1Act g u ∈ U := by
  rw [Submodule.mem_comap, co1F3Lin_apply]

private theorem co1F3_orbit_zero :
    CFSG.Monster.GMS.co1Orbit 0 =
      Set.range fun h : NativeSporadic.Co1 => co1Act h CFSG.Sporadic.Co1.Module.v₂ :=
  rfl

private theorem co1F3_transport
    (g : NativeSporadic.Co1) (U : Submodule (ZMod 2) Vec24)
    (hgU : co1Act g omega0 ∈ U) (hTS : ∀ u ∈ U, q₀ u = 0)
    (hinv : ∀ A : NativeSporadic.Co1, co1Act A (co1Act g omega0) = co1Act g omega0 →
      ∀ u ∈ U, co1Act A u ∈ U)
    {y : Vec24} (hyU : y ∈ U) (hy : y ∉ Submodule.span (ZMod 2) {co1Act g omega0}) :
    ∃ u ∈ U, u ≠ co1Act g omega0 ∧ u ∈ CFSG.Monster.GMS.co1Orbit 0 := by
  have hω : omega0 ∈ U.comap (co1F3Lin g) := (co1F3_mem_comap g U omega0).2 hgU
  have hTS' : ∀ u ∈ U.comap (co1F3Lin g), q₀ u = 0 := by
    intro u hu
    have h1 : q₀ (co1Act g u) = 0 := hTS _ ((co1F3_mem_comap g U u).1 hu)
    rwa [q₀_co1Act] at h1
  have hU' : ∀ A : NativeSporadic.Co1, co1Act A omega0 = omega0 →
      ∀ u ∈ U.comap (co1F3Lin g), co1Act A u ∈ U.comap (co1F3Lin g) := by
    intro A hA u hu
    have hB : co1Act (g * A * g⁻¹) (co1Act g omega0) = co1Act g omega0 := by
      rw [← co1Act_mul' (g * A * g⁻¹) g, show g * A * g⁻¹ * g = g * A by group,
        co1Act_mul' g A, hA]
    have h2 : co1Act (g * A * g⁻¹) (co1Act g u) ∈ U :=
      hinv (g * A * g⁻¹) hB (co1Act g u) ((co1F3_mem_comap g U u).1 hu)
    have h3 : co1Act g (co1Act A u) ∈ U := by
      rw [← co1F3_conj g A u]
      exact h2
    exact (co1F3_mem_comap g U (co1Act A u)).2 h3
  have hy'U : co1Act g⁻¹ y ∈ U.comap (co1F3Lin g) := by
    rw [co1F3_mem_comap, co1F3_cancel]
    exact hyU
  have hy'ns : co1Act g⁻¹ y ∉ Submodule.span (ZMod 2) {omega0} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    apply hy
    have hyeq : y = a • co1Act g omega0 := by
      calc y = co1Act g (co1Act g⁻¹ y) := (co1F3_cancel g y).symm
        _ = co1Act g (a • omega0) := by rw [ha]
        _ = a • co1Act g omega0 := co1F3_smul g a omega0
    rw [hyeq]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  obtain ⟨u', hu'U, hu'ne, hu'orb⟩ :=
    co1_spin (U.comap (co1F3Lin g)) hω hTS' hU' hy'U hy'ns
  rw [co1F3_orbit_zero] at hu'orb
  obtain ⟨h, hh⟩ := hu'orb
  have hh' : co1Act h CFSG.Sporadic.Co1.Module.v₂ = u' := hh
  refine ⟨co1Act g u', (co1F3_mem_comap g U u').1 hu'U, ?_, ?_⟩
  · intro heq
    apply hu'ne
    calc u' = co1Act g⁻¹ (co1Act g u') := (co1F3_cancel' g u').symm
      _ = co1Act g⁻¹ (co1Act g omega0) := by rw [heq]
      _ = omega0 := co1F3_cancel' g omega0
  · rw [co1F3_orbit_zero]
    refine Set.mem_range.2 ⟨g * h, ?_⟩
    show co1Act (g * h) CFSG.Sporadic.Co1.Module.v₂ = co1Act g u'
    rw [← hh', co1Act_mul']

theorem co1_hF3
    (v : Vec24) (hv : v ≠ 0) (hq : q₀ v = 0) (U : Submodule (ZMod 2) Vec24) (hvU : v ∈ U)
    (hdim : 2 ≤ Module.finrank (ZMod 2) U) (hTS : ∀ u ∈ U, q₀ u = 0)
    (hinv : ∀ A : NativeSporadic.Co1, co1Act A v = v → ∀ u ∈ U, co1Act A u ∈ U) :
    ∃ u ∈ U, u ≠ v ∧ u ∈ CFSG.Monster.GMS.co1Orbit 0 := by
  have hsing : v ∈ {w : Vec24 | q₀ w = 0 ∧ w ≠ 0} := ⟨hq, hv⟩
  rw [singular_eq_union] at hsing
  rcases hsing with h2 | h4
  ·
    exfalso
    have hvco : v ∈ CFSG.Monster.GMS.co1Orbit 0 := by
      rw [co1Orbit_zero_eq]
      exact h2
    have hbilU : ∀ x ∈ U, ∀ y ∈ U, bil₀ x y = 0 := by
      intro x hx y hy
      rw [← polar_q₀]
      show q₀ (x + y) - q₀ x - q₀ y = 0
      rw [hTS _ (U.add_mem hx hy), hTS x hx, hTS y hy]
      simp
    have hF := CFSG.Monster.GMS.co2McLFacts
    rcases hF.irred_co2 v hvco U hvU (fun y hy => hbilU y hy v hvU)
        (fun A hA y hy => hinv A hA y hy) with hspan | hperp
    · rw [hspan, finrank_span_singleton hv] at hdim
      omega
    · obtain ⟨y₁, y₂, h₁, h₂, h₁₂⟩ := hF.nondeg_co2 v hvco
      have h0 := hbilU y₁ (hperp y₁ h₁) y₂ (hperp y₂ h₂)
      rw [h₁₂] at h0
      exact absurd h0 (by decide)
  ·
    have hv4 : v ∈ MulAction.orbit NativeSporadic.Co1 omega0 := by
      rw [orbit_omega0]
      exact h4
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hv4
    have hg' : co1Act g omega0 = v := hg
    subst hg'
    obtain ⟨y, hyU, hy⟩ : ∃ y ∈ U, y ∉ Submodule.span (ZMod 2) {co1Act g omega0} := by
      by_contra hcon
      have hle : U ≤ Submodule.span (ZMod 2) {co1Act g omega0} := by
        intro y hy
        by_contra hn
        exact hcon ⟨y, hy, hn⟩
      have hfin := Submodule.finrank_mono hle
      rw [finrank_span_singleton hv] at hfin
      omega
    exact co1F3_transport g U hvU hTS hinv hyU hy

private theorem gms_co1Act_apply (g : NativeSporadic.Co1) (x : Fin 24 → ZMod 2) :
    CFSG.Monster.GMS.co1Act g x = CFSG.Sporadic.Co1.Module.co1Act g x := rfl

private theorem co1Act_inv_cancel_mod (g : NativeSporadic.Co1) (x : Fin 24 → ZMod 2) :
    CFSG.Sporadic.Co1.Module.co1Act g⁻¹ (CFSG.Sporadic.Co1.Module.co1Act g x) = x := by
  rw [← CFSG.Sporadic.Co1.Module.Odd.co1Act_mul', inv_mul_cancel,
    CFSG.Sporadic.Co1.Module.Odd.co1Act_one']

private theorem co1Act_v₂_ne_zero (g : NativeSporadic.Co1) :
    CFSG.Sporadic.Co1.Module.co1Act g CFSG.Sporadic.Co1.Module.v₂ ≠ 0 := by
  intro h
  apply CFSG.Sporadic.Co1.Module.v₂_ne_zero
  have h1 := co1Act_inv_cancel_mod g CFSG.Sporadic.Co1.Module.v₂
  rw [h] at h1
  rw [← h1]
  simp only [CFSG.Sporadic.Co1.Module.co1Act, Matrix.mulVec_zero]

theorem co1_hgood :
    ∀ u ∈ CFSG.Monster.GMS.co1Orbit 0, u ≠ 0 ∧ q₀ u = 0 ∧
      ∀ Y : Submodule (ZMod 2) Vec24, u ∈ Y →
        (∀ y ∈ Y, QuadraticMap.polar q₀ y u = 0) →
        (∀ A : NativeSporadic.Co1, co1Act A u = u → ∀ y ∈ Y, co1Act A y ∈ Y) →
        Y = Submodule.span (ZMod 2) {u} ∨ ∀ y, QuadraticMap.polar q₀ y u = 0 → y ∈ Y := by
  intro u hu
  have hu' : u ∈ Set.range fun g : NativeSporadic.Co1 =>
      CFSG.Monster.GMS.co1Act g (CFSG.Sporadic.Co1.Module.reps 0) := hu
  obtain ⟨g, hg⟩ := hu'
  have hg' : CFSG.Sporadic.Co1.Module.co1Act g CFSG.Sporadic.Co1.Module.v₂ = u := hg
  have hu0 : u ≠ 0 := by
    rw [← hg']
    exact co1Act_v₂_ne_zero g
  have hq0 : q₀ u = 0 := by
    rw [← hg']
    exact (CFSG.Sporadic.Co1.Module.q₀_co1Act g CFSG.Sporadic.Co1.Module.v₂).trans
      CFSG.Sporadic.Co1.Module.q₀_v₂
  refine ⟨hu0, hq0, ?_⟩
  intro Y huY hperp hstab
  have hpol : ∀ y : Fin 24 → ZMod 2,
      QuadraticMap.polar q₀ y u = CFSG.Sporadic.Co1.Module.bil₀ y u :=
    fun y => CFSG.Sporadic.Co1.Module.polar_q₀ y u
  have hperp' : ∀ y ∈ Y, CFSG.Sporadic.Co1.Module.bil₀ y u = 0 := by
    intro y hy
    rw [← hpol y]
    exact hperp y hy
  have hstab' : ∀ A ∈ CFSG.Monster.GMS.co1Stab u, ∀ y ∈ Y,
      CFSG.Monster.GMS.co1Act A y ∈ Y := by
    intro A hA y hy
    have hA' : CFSG.Sporadic.Co1.Module.co1Act A u = u :=
      (gms_co1Act_apply A u).symm.trans (CFSG.Monster.GMS.CoTwoModule.mem_co1Stab.1 hA)
    rw [gms_co1Act_apply]
    exact hstab A hA' y hy
  rcases CFSG.Monster.GMS.co2McLFacts.irred_co2 u hu Y huY hperp' hstab' with h | h
  · exact Or.inl h
  · refine Or.inr fun y hy => h y ?_
    rw [hpol y] at hy
    exact hy

end CFSG.GF2Type.Widths1112
