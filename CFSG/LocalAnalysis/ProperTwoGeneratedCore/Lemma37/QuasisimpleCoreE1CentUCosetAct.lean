module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUCoset
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

@[expose] def fourRepM : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def fourList : Fin 4 → Perm (Fin 4) := ![1, fourRep, fourRepM, fourRep * fourRepM]

theorem fourList_facts : (∀ i, Perm.sign (fourList i) = 1) ∧
    (∀ i, i ≠ 0 → fourList i * fourList i = 1 ∧ ∀ j, fourList i j ≠ j) ∧
    Perm.sign (swap (2 : Fin 4) 3) = -1 := by
  decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem rho4_eq_of {g : QuasiQuotient u} {σ : Perm (Fin 4)}
    (h : ∀ i, (d.kappa (σ i))⁻¹ * (g * d.kappa i) ∈ d.lyGroup) : d.rho4 g = σ :=
  Equiv.ext fun i => (d.rho4_apply_eq_iff g i (σ i)).mpr (h i)

theorem mul_yBar_mem_lyGroup {l : QuasiQuotient u} (hl : l ∈ L) : l * d.yBar ∈ d.lyGroup :=
  Subgroup.mul_mem _ (d.le_lyGroup hl) d.yBar_mem_lyGroup

theorem rho4_of_mem {l : QuasiQuotient u} (hl : l ∈ L) : d.rho4 l = 1 :=
  d.rho4_eq_of fun i => by
    rw [Perm.one_apply, Subgroup.mem_centralizer_iff.mp (d.kappa_mem i) l hl, inv_mul_cancel_left]
    exact d.le_lyGroup hl

theorem mem_lyGroup_of_rho4 {g : QuasiQuotient u} (hg : d.rho4 g = 1) : g ∈ d.lyGroup := by
  have h := (d.rho4_apply_eq_iff g 0 0).mp (by rw [hg]; rfl)
  simpa [kappa] using h

theorem inv_mul_quasiCentral_mul (g : QuasiQuotient u) :
    g⁻¹ * (quasiCentral u * g) = quasiCentral u := by
  rw [← d.commute_quasiCentral g, inv_mul_cancel_left]

theorem rho4_quasiBar : d.rho4 (quasiBar u) = fourRep := by
  refine d.rho4_eq_of fun i => ?_
  fin_cases i
  · change (quasiBar u)⁻¹ * (quasiBar u * 1) ∈ d.lyGroup
    rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · change (1 : QuasiQuotient u)⁻¹ * (quasiBar u * quasiBar u) ∈ d.lyGroup
    rw [inv_one, one_mul]
    exact d.le_lyGroup d.quasiCentral_mem
  · change (quasiBar u * d.mBar)⁻¹ * (quasiBar u * d.mBar) ∈ d.lyGroup
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · change d.mBar⁻¹ * (quasiBar u * (quasiBar u * d.mBar)) ∈ d.lyGroup
    rw [← mul_assoc (quasiBar u), d.inv_mul_quasiCentral_mul]
    exact d.le_lyGroup d.quasiCentral_mem

theorem mBar_mul_quasiBar : d.mBar * quasiBar u = quasiBar u * d.mBar * quasiCentral u := by
  have h1 := d.quasiBar_mul_mBar
  have hee := d.quasiCentral_mul_self
  calc d.mBar * quasiBar u = d.mBar * quasiBar u * (quasiCentral u * quasiCentral u) := by
        rw [hee, mul_one]
    _ = quasiBar u * d.mBar * quasiCentral u := by rw [← mul_assoc, ← h1]

theorem rho4_mBar : d.rho4 d.mBar = fourRepM := by
  refine d.rho4_eq_of fun i => ?_
  have hee := d.quasiCentral_mul_self
  have hmm := d.mBar_mul_self
  have hmu := d.mBar_mul_quasiBar
  fin_cases i
  · change d.mBar⁻¹ * (d.mBar * 1) ∈ d.lyGroup
    rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · change (quasiBar u * d.mBar)⁻¹ * (d.mBar * quasiBar u) ∈ d.lyGroup
    rw [hmu, inv_mul_cancel_left]
    exact d.le_lyGroup d.quasiCentral_mem
  · change (1 : QuasiQuotient u)⁻¹ * (d.mBar * d.mBar) ∈ d.lyGroup
    rw [inv_one, one_mul, hmm]
    exact d.le_lyGroup d.quasiCentral_mem
  · change (quasiBar u)⁻¹ * (d.mBar * (quasiBar u * d.mBar)) ∈ d.lyGroup
    have h1 : (quasiBar u)⁻¹ * (d.mBar * (quasiBar u * d.mBar)) = 1 := by
      calc (quasiBar u)⁻¹ * (d.mBar * (quasiBar u * d.mBar)) =
          (quasiBar u)⁻¹ * (d.mBar * quasiBar u) * d.mBar := by group
        _ = (quasiBar u)⁻¹ * (quasiBar u * d.mBar * quasiCentral u) * d.mBar := by rw [hmu]
        _ = d.mBar * (quasiCentral u * d.mBar) := by group
        _ = d.mBar * (d.mBar * quasiCentral u) := by rw [d.commute_quasiCentral d.mBar]
        _ = 1 := by rw [← mul_assoc, hmm, hee]
    rw [h1]
    exact Subgroup.one_mem _

theorem rho4_yBar : d.rho4 d.yBar = swap 2 3 := by
  refine d.rho4_eq_of fun i => ?_
  have hεL : ∀ {ε : QuasiQuotient u}, (ε = 1 ∨ ε = quasiCentral u) → ε ∈ L := by
    rintro ε (rfl | rfl)
    exacts [L.one_mem, d.quasiCentral_mem]
  have hεc : ∀ {ε : QuasiQuotient u}, (ε = 1 ∨ ε = quasiCentral u) → ∀ g, g * ε = ε * g := by
    rintro ε (rfl | rfl) g
    · group
    · exact d.commute_quasiCentral g
  obtain ⟨ε₁, hε₁, hyu⟩ : ∃ ε₁ : QuasiQuotient u, (ε₁ = 1 ∨ ε₁ = quasiCentral u) ∧
      d.yBar * quasiBar u = quasiBar u * ε₁ * d.yBar := by
    rcases d.yBar_conj_quasiBar with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      calc d.yBar * quasiBar u = d.yBar * quasiBar u * d.yBar⁻¹ * d.yBar := by group
        _ = quasiBar u * 1 * d.yBar := by rw [h, mul_one]
    · refine ⟨quasiCentral u, Or.inr rfl, ?_⟩
      calc d.yBar * quasiBar u = d.yBar * quasiBar u * d.yBar⁻¹ * d.yBar := by group
        _ = quasiBar u * quasiCentral u * d.yBar := by rw [h]
  obtain ⟨ε₂, hε₂, hym⟩ : ∃ ε₂ : QuasiQuotient u, (ε₂ = 1 ∨ ε₂ = quasiCentral u) ∧
      d.yBar * d.mBar = quasiBar u * d.mBar * ε₂ * d.yBar := by
    rcases d.yBar_conj_mBar with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      calc d.yBar * d.mBar = d.yBar * d.mBar * d.yBar⁻¹ * d.yBar := by group
        _ = quasiBar u * d.mBar * 1 * d.yBar := by rw [h, mul_one]
    · refine ⟨quasiCentral u, Or.inr rfl, ?_⟩
      calc d.yBar * d.mBar = d.yBar * d.mBar * d.yBar⁻¹ * d.yBar := by group
        _ = quasiBar u * d.mBar * quasiCentral u * d.yBar := by rw [h]
  fin_cases i
  · change (1 : QuasiQuotient u)⁻¹ * (d.yBar * 1) ∈ d.lyGroup
    rw [inv_one, one_mul, mul_one]
    exact d.yBar_mem_lyGroup
  · change (quasiBar u)⁻¹ * (d.yBar * quasiBar u) ∈ d.lyGroup
    rw [hyu, mul_assoc, inv_mul_cancel_left]
    exact d.mul_yBar_mem_lyGroup (hεL hε₁)
  · change (quasiBar u * d.mBar)⁻¹ * (d.yBar * d.mBar) ∈ d.lyGroup
    rw [hym, mul_assoc, inv_mul_cancel_left]
    exact d.mul_yBar_mem_lyGroup (hεL hε₂)
  · change d.mBar⁻¹ * (d.yBar * (quasiBar u * d.mBar)) ∈ d.lyGroup
    set c := quasiCentral u * ε₁ * ε₂ with hc
    have hcent : ∀ g : QuasiQuotient u, g * c = c * g := fun g => by
      rw [hc, show g * (quasiCentral u * ε₁ * ε₂) = (g * quasiCentral u) * ε₁ * ε₂ by group,
        d.commute_quasiCentral g, mul_assoc (quasiCentral u), hεc hε₁ g,
        show quasiCentral u * (ε₁ * g) * ε₂ = quasiCentral u * ε₁ * (g * ε₂) by group,
        hεc hε₂ g]
      group
    have h1 : d.yBar * (quasiBar u * d.mBar) = d.mBar * c * d.yBar := by
      calc d.yBar * (quasiBar u * d.mBar) = d.yBar * quasiBar u * d.mBar := by group
        _ = quasiBar u * ε₁ * (d.yBar * d.mBar) := by rw [hyu]; group
        _ = quasiBar u * ε₁ * (quasiBar u * d.mBar * ε₂ * d.yBar) := by rw [hym]
        _ = quasiBar u * (ε₁ * quasiBar u) * d.mBar * ε₂ * d.yBar := by group
        _ = quasiBar u * quasiBar u * ε₁ * d.mBar * ε₂ * d.yBar := by
          rw [← hεc hε₁ (quasiBar u)]; group
        _ = quasiCentral u * ε₁ * (d.mBar * ε₂) * d.yBar := by group
        _ = quasiCentral u * ε₁ * ε₂ * d.mBar * d.yBar := by rw [hεc hε₂ d.mBar]; group
        _ = d.mBar * c * d.yBar := by rw [← hcent d.mBar]
    rw [h1, mul_assoc, inv_mul_cancel_left]
    exact d.mul_yBar_mem_lyGroup (L.mul_mem (L.mul_mem d.quasiCentral_mem (hεL hε₁)) (hεL hε₂))

theorem rho4_kappa (i : Fin 4) : d.rho4 (d.kappa i) = fourList i := by
  fin_cases i
  · exact map_one _
  · exact d.rho4_quasiBar
  · exact d.rho4_mBar
  · change d.rho4 (quasiBar u * d.mBar) = fourRep * fourRepM
    rw [map_mul, d.rho4_quasiBar, d.rho4_mBar]

theorem exists_rho4_of_mem_centralizer {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    ∃ i, d.rho4 k = fourList i ∧ (i = 0 → k = 1 ∨ k = quasiCentral u) := by
  obtain ⟨i, hi⟩ := d.exists_kappa hk
  rcases hi with rfl | rfl
  · refine ⟨i, d.rho4_kappa i, fun h => ?_⟩
    subst h
    exact Or.inl rfl
  · refine ⟨i, by rw [map_mul, d.rho4_of_mem d.quasiCentral_mem, mul_one, d.rho4_kappa],
      fun h => ?_⟩
    subst h
    exact Or.inr (one_mul _)

theorem sign_rho4_of_mem_centralizer {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) : Perm.sign (d.rho4 k) = 1 := by
  obtain ⟨i, hi, -⟩ := d.exists_rho4_of_mem_centralizer hk
  rw [hi]
  exact fourList_facts.1 i

theorem rho4_fpf_of_mem_centralizer {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) (hk1 : k ≠ 1)
    (hke : k ≠ quasiCentral u) : d.rho4 k * d.rho4 k = 1 ∧ ∀ j, d.rho4 k j ≠ j := by
  obtain ⟨i, hi, hi0⟩ := d.exists_rho4_of_mem_centralizer hk
  have hi0' : i ≠ 0 := fun h => by
    rcases hi0 h with h1 | h1
    exacts [hk1 h1, hke h1]
  rw [hi]
  exact fourList_facts.2.1 i hi0'

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
