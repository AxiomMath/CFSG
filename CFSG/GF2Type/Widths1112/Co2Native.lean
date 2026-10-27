module

public import Certificates.Certificate38953
public import Certificates.Certificate38954
public import Certificates.Certificate38955
public import CFSG.GF2Type.Widths1112.Co2Forms
public import CFSG.GF2Type.Widths1112.Co2Orbits

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

theorem co2_irr_rep0
    (Y : Submodule (ZMod 2) Vec22) (hrY : toVecD 22 (w12Co2Rep 0) ∈ Y)
    (hperp : ∀ y ∈ Y, bil₀₂ y (toVecD 22 (w12Co2Rep 0)) = 0)
    (hinv : ∀ A : NativeSporadic.Co2, co2Act A (toVecD 22 (w12Co2Rep 0)) = toVecD 22 (w12Co2Rep 0) →
      ∀ y ∈ Y, co2Act A y ∈ Y) :
    Y = Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep 0)} ∨
      ∀ y, bil₀₂ y (toVecD 22 (w12Co2Rep 0)) = 0 → y ∈ Y :=
  Certificates.certificate38953.1 Y hrY hperp hinv

theorem co2_pair_rep0 :
    ∃ a b : Vec22, bil₀₂ a (toVecD 22 (w12Co2Rep 0)) = 0 ∧
      bil₀₂ b (toVecD 22 (w12Co2Rep 0)) = 0 ∧ bil₀₂ a b = 1 :=
  Certificates.certificate38953.2

theorem co2_spin_rep1
    (U : Submodule (ZMod 2) Vec22) (hrU : toVecD 22 (w12Co2Rep 1) ∈ U)
    (hperp : ∀ u ∈ U, bil₀₂ u (toVecD 22 (w12Co2Rep 1)) = 0)
    (hU : ∀ A : NativeSporadic.Co2, co2Act A (toVecD 22 (w12Co2Rep 1)) = toVecD 22 (w12Co2Rep 1) →
      ∀ u ∈ U, co2Act A u ∈ U)
    (y : Vec22) (hyU : y ∈ U) (hy : y ∉ Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep 1)}) :
    ∃ u ∈ U, u ≠ toVecD 22 (w12Co2Rep 1) ∧ u ∈ co2Orbit 0 :=
  Certificates.certificate38954 U hrU hperp hU y hyU hy

theorem co2_spin_rep2
    (U : Submodule (ZMod 2) Vec22) (hrU : toVecD 22 (w12Co2Rep 2) ∈ U)
    (hperp : ∀ u ∈ U, bil₀₂ u (toVecD 22 (w12Co2Rep 2)) = 0)
    (hU : ∀ A : NativeSporadic.Co2, co2Act A (toVecD 22 (w12Co2Rep 2)) = toVecD 22 (w12Co2Rep 2) →
      ∀ u ∈ U, co2Act A u ∈ U)
    (y : Vec22) (hyU : y ∈ U) (hy : y ∉ Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep 2)}) :
    ∃ u ∈ U, u ≠ toVecD 22 (w12Co2Rep 2) ∧ u ∈ co2Orbit 0 :=
  Certificates.certificate38955 U hrU hperp hU y hyU hy

private theorem co2F3_conj (g A : NativeSporadic.Co2) (u : Vec22) :
    co2Act (g * A * g⁻¹) (co2Act g u) = co2Act g (co2Act A u) := by
  rw [← co2Act_mul (g * A * g⁻¹) g, show g * A * g⁻¹ * g = g * A by group, co2Act_mul g A]

private theorem co2F3_mem_comap (g : NativeSporadic.Co2) (U : Submodule (ZMod 2) Vec22)
    (u : Vec22) : u ∈ U.comap (co2Lin g) ↔ co2Act g u ∈ U := by
  rw [Submodule.mem_comap, co2Lin_apply]

private theorem co2F3_zero (g : NativeSporadic.Co2) : co2Act g 0 = 0 :=
  (co2Lin_apply g 0).symm.trans (map_zero (co2Lin g))

private theorem co2F3_polar (y u : Vec22) : QuadraticMap.polar q₀₂ y u = bil₀₂ y u :=
  polar_q₀₂ y u

private theorem co2F3_stab (g : NativeSporadic.Co2) (r : Vec22) (U : Submodule (ZMod 2) Vec22)
    (hU : ∀ A : NativeSporadic.Co2, co2Act A (co2Act g r) = co2Act g r → ∀ u ∈ U, co2Act A u ∈ U) :
    ∀ A : NativeSporadic.Co2, co2Act A r = r →
      ∀ u ∈ U.comap (co2Lin g), co2Act A u ∈ U.comap (co2Lin g) := by
  intro A hA u hu
  have hB : co2Act (g * A * g⁻¹) (co2Act g r) = co2Act g r := by
    rw [co2F3_conj, hA]
  have h2 : co2Act (g * A * g⁻¹) (co2Act g u) ∈ U :=
    hU (g * A * g⁻¹) hB (co2Act g u) ((co2F3_mem_comap g U u).1 hu)
  have h3 : co2Act g (co2Act A u) ∈ U := by
    rw [← co2F3_conj g A u]
    exact h2
  exact (co2F3_mem_comap g U (co2Act A u)).2 h3

theorem co2_hgood :
    ∀ u ∈ co2Orbit 0, u ≠ 0 ∧ q₀₂ u = 0 ∧
      ∀ Y : Submodule (ZMod 2) Vec22, u ∈ Y →
        (∀ y ∈ Y, QuadraticMap.polar q₀₂ y u = 0) →
        (∀ A : NativeSporadic.Co2, co2Act A u = u → ∀ y ∈ Y, co2Act A y ∈ Y) →
        Y = Submodule.span (ZMod 2) {u} ∨ ∀ y, QuadraticMap.polar q₀₂ y u = 0 → y ∈ Y := by
  intro u hu
  have hu' : u ∈ Set.range fun g : NativeSporadic.Co2 => co2Act g (toVecD 22 (w12Co2Rep 0)) := hu
  obtain ⟨g, hg⟩ := hu'
  have hg' : co2Act g (toVecD 22 (w12Co2Rep 0)) = u := hg
  obtain ⟨hr0, hq0⟩ := co2_rep_singular (by norm_num : (0 : ℕ) < 3)
  have hu0 : u ≠ 0 := by
    intro h
    apply hr0
    have e : co2Act g⁻¹ u = toVecD 22 (w12Co2Rep 0) := by
      rw [← hg']
      exact co2Act_inv_apply g _
    rw [← e, h]
    exact co2F3_zero g⁻¹
  have hq : q₀₂ u = 0 := by
    rw [← hg', q₀₂_co2Act]
    exact hq0
  refine ⟨hu0, hq, ?_⟩
  intro Y huY hperp hstab
  have hrY : toVecD 22 (w12Co2Rep 0) ∈ Y.comap (co2Lin g) := by
    rw [co2F3_mem_comap, hg']
    exact huY
  have hperp' : ∀ y ∈ Y.comap (co2Lin g), bil₀₂ y (toVecD 22 (w12Co2Rep 0)) = 0 := by
    intro y hy
    have h1 : bil₀₂ (co2Act g y) u = 0 :=
      (co2F3_polar (co2Act g y) u).symm.trans (hperp (co2Act g y) ((co2F3_mem_comap g Y y).1 hy))
    rw [← hg', bil₀₂_co2Act] at h1
    exact h1
  have hinv' : ∀ A : NativeSporadic.Co2,
      co2Act A (toVecD 22 (w12Co2Rep 0)) = toVecD 22 (w12Co2Rep 0) →
      ∀ y ∈ Y.comap (co2Lin g), co2Act A y ∈ Y.comap (co2Lin g) :=
    co2F3_stab g (toVecD 22 (w12Co2Rep 0)) Y (fun A hA => hstab A (by rw [hg'] at hA; exact hA))
  rcases co2_irr_rep0 (Y.comap (co2Lin g)) hrY hperp' hinv' with hspan | hall
  · left
    apply le_antisymm
    · intro y hy
      have hy' : co2Act g⁻¹ y ∈ Y.comap (co2Lin g) := by
        rw [co2F3_mem_comap, co2Act_apply_inv]
        exact hy
      rw [hspan, Submodule.mem_span_singleton] at hy'
      obtain ⟨a, ha⟩ := hy'
      refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
      rw [← hg', ← co2Act_smul, ha, co2Act_apply_inv]
    · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 huY)
  · right
    intro y hy
    have hy' : co2Act g⁻¹ y ∈ Y.comap (co2Lin g) := by
      apply hall
      have e := bil₀₂_co2Act g (co2Act g⁻¹ y) (toVecD 22 (w12Co2Rep 0))
      rw [co2Act_apply_inv, hg'] at e
      rw [← e]
      exact (co2F3_polar y u).symm.trans hy
    rw [co2F3_mem_comap, co2Act_apply_inv] at hy'
    exact hy'

private theorem co2F3_of_orbit
    {i : ℕ}
    (hspin : ∀ U : Submodule (ZMod 2) Vec22, toVecD 22 (w12Co2Rep i) ∈ U →
      (∀ u ∈ U, bil₀₂ u (toVecD 22 (w12Co2Rep i)) = 0) →
      (∀ A : NativeSporadic.Co2, co2Act A (toVecD 22 (w12Co2Rep i)) = toVecD 22 (w12Co2Rep i) →
        ∀ u ∈ U, co2Act A u ∈ U) →
      ∀ y ∈ U, y ∉ Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep i)} →
        ∃ u ∈ U, u ≠ toVecD 22 (w12Co2Rep i) ∧ u ∈ co2Orbit 0)
    (v : Vec22) (hv0 : v ≠ 0) (hvi : v ∈ co2Orbit i) (U : Submodule (ZMod 2) Vec22)
    (hvU : v ∈ U) (hdim : 2 ≤ Module.finrank (ZMod 2) U) (hTS : ∀ u ∈ U, q₀₂ u = 0)
    (hinv : ∀ A : NativeSporadic.Co2, co2Act A v = v → ∀ u ∈ U, co2Act A u ∈ U) :
    ∃ u ∈ U, u ≠ v ∧ u ∈ co2Orbit 0 := by
  obtain ⟨g, hg⟩ : ∃ g : NativeSporadic.Co2, co2Act g (toVecD 22 (w12Co2Rep i)) = v := hvi
  obtain ⟨y, hyU, hy⟩ : ∃ y ∈ U, y ∉ Submodule.span (ZMod 2) {v} := by
    by_contra hcon
    have hle : U ≤ Submodule.span (ZMod 2) {v} := by
      intro y hy
      by_contra hn
      exact hcon ⟨y, hy, hn⟩
    have hfin := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv0] at hfin
    omega
  have hrU : toVecD 22 (w12Co2Rep i) ∈ U.comap (co2Lin g) := by
    rw [co2F3_mem_comap, hg]
    exact hvU
  have hTS' : ∀ u ∈ U.comap (co2Lin g), q₀₂ u = 0 := by
    intro u hu
    have h1 := hTS _ ((co2F3_mem_comap g U u).1 hu)
    rwa [q₀₂_co2Act] at h1
  have hperp' : ∀ u ∈ U.comap (co2Lin g), bil₀₂ u (toVecD 22 (w12Co2Rep i)) = 0 := by
    intro u hu
    rw [← polar_q₀₂, hTS' _ ((U.comap (co2Lin g)).add_mem hu hrU), hTS' u hu, hTS' _ hrU]
    simp
  have hinv' : ∀ A : NativeSporadic.Co2,
      co2Act A (toVecD 22 (w12Co2Rep i)) = toVecD 22 (w12Co2Rep i) →
      ∀ u ∈ U.comap (co2Lin g), co2Act A u ∈ U.comap (co2Lin g) :=
    co2F3_stab g (toVecD 22 (w12Co2Rep i)) U (fun A hA => hinv A (by rw [hg] at hA; exact hA))
  have hy'U : co2Act g⁻¹ y ∈ U.comap (co2Lin g) := by
    rw [co2F3_mem_comap, co2Act_apply_inv]
    exact hyU
  have hy'ns : co2Act g⁻¹ y ∉ Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep i)} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    apply hy
    refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
    rw [← hg, ← co2Act_smul, ha, co2Act_apply_inv]
  obtain ⟨u', hu'U, hu'ne, hu'orb⟩ :=
    hspin (U.comap (co2Lin g)) hrU hperp' hinv' _ hy'U hy'ns
  refine ⟨co2Act g u', (co2F3_mem_comap g U u').1 hu'U, ?_, co2Orbit_closed 0 g hu'orb⟩
  intro heq
  apply hu'ne
  calc u' = co2Act g⁻¹ (co2Act g u') := (co2Act_inv_apply g u').symm
    _ = co2Act g⁻¹ v := by rw [heq]
    _ = toVecD 22 (w12Co2Rep i) := by rw [← hg, co2Act_inv_apply]

theorem co2_hF3
    (v : Vec22) (hv : v ≠ 0) (hq : q₀₂ v = 0) (U : Submodule (ZMod 2) Vec22) (hvU : v ∈ U)
    (hdim : 2 ≤ Module.finrank (ZMod 2) U) (hTS : ∀ u ∈ U, q₀₂ u = 0)
    (hinv : ∀ A : NativeSporadic.Co2, co2Act A v = v → ∀ u ∈ U, co2Act A u ∈ U) :
    ∃ u ∈ U, u ≠ v ∧ u ∈ co2Orbit 0 := by
  have hbilU : ∀ x ∈ U, ∀ y ∈ U, bil₀₂ x y = 0 := by
    intro x hx y hy
    rw [← polar_q₀₂, hTS _ (U.add_mem hx hy), hTS x hx, hTS y hy]
    simp
  rcases co2_cover hv hq with h0 | h12
  ·
    exfalso
    have hperpU : ∀ y ∈ U, QuadraticMap.polar q₀₂ y v = 0 := fun y hy =>
      (co2F3_polar y v).trans (hbilU y hy v hvU)
    rcases (co2_hgood v h0).2.2 U hvU hperpU hinv with hspan | hall
    · rw [hspan, finrank_span_singleton hv] at hdim
      omega
    · obtain ⟨g, hg⟩ : ∃ g : NativeSporadic.Co2, co2Act g (toVecD 22 (w12Co2Rep 0)) = v := h0
      obtain ⟨a, b, ha, hb, hab⟩ := co2_pair_rep0
      have hy1 : co2Act g a ∈ U := by
        apply hall
        rw [co2F3_polar, ← hg, bil₀₂_co2Act, ha]
      have hy2 : co2Act g b ∈ U := by
        apply hall
        rw [co2F3_polar, ← hg, bil₀₂_co2Act, hb]
      have h := hbilU _ hy1 _ hy2
      rw [bil₀₂_co2Act, hab] at h
      exact absurd h (by decide)
  · rcases h12 with h1 | h2
    · exact co2F3_of_orbit (i := 1) co2_spin_rep1 v hv h1 U hvU hdim hTS hinv
    · exact co2F3_of_orbit (i := 2) co2_spin_rep2 v hv h2 U hvU hdim hTS hinv

end CFSG.GF2Type.Widths1112
