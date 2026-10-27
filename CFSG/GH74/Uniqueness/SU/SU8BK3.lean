module

public import CFSG.GH74.Uniqueness.SU.SU8BK2
public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.LocA CFSG.GH74.Uniqueness.SU.SU8.BLift
open scoped commutatorElement

namespace BK

variable {X : Type} [Group X] [Finite X] {O L A : Subgroup X} [O.Normal] [L.Normal]

omit [Finite X] in
theorem inn_of_K (hinn : ∀ φ : MulAut ↥(Kb O L), ∃ g : ↥(Kb O L), φ = MulAut.conj g) :
    ∀ g : X, ∃ m ∈ L, ∀ l ∈ L,
      QuotientGroup.mk' O (g * l * g⁻¹) = QuotientGroup.mk' O (m * l * m⁻¹) := by
  intro g
  obtain ⟨k₀, hk₀⟩ := hinn (MulAut.conjNormal (QuotientGroup.mk' O g))
  obtain ⟨m, hm, hmk⟩ := k₀.2
  refine ⟨m, hm, fun l hl => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(Kb O L) =>
    ((φ ⟨QuotientGroup.mk' O l, ⟨l, hl, rfl⟩⟩ : ↥(Kb O L)) : X ⧸ O)) hk₀
  simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  simp only [map_mul, map_inv]
  rw [hmk]
  exact h1

theorem htwo_K (pre : PreHyp O L A) (hO : pPrimeCore 2 (X ⧸ O) = ⊥)
    (hsq : ∀ P : Sylow 2 ↥(Kb O L), ∀ g ∈ (P : Subgroup ↥(Kb O L)), g ^ 2 ∈ center ↥(Kb O L) →
      g ^ 2 = 1)
    (hZP : ∀ P : Sylow 2 ↥(Kb O L), center ↥(P : Subgroup ↥(Kb O L)) =
      (center ↥(Kb O L)).subgroupOf (P : Subgroup ↥(Kb O L)))
    (hSz : Nonempty ((↥(Kb O L) ⧸ center ↥(Kb O L)) ≃* CFSG.Theory.Comparator.SzModel 1))
    (hAL : A ≤ L) (hZ : Nat.card ↥(Z0 (Kb O L)) = 2) (hA : 2 < Nat.card A) :
    ∃ p ∈ L, (∃ s : ℕ, p ^ (2 ^ s) ∈ O) ∧ (∀ a ∈ A, p⁻¹ * a * p ∈ A ⊔ O) ∧
      ∃ a ∈ A, p * a * p⁻¹ * a⁻¹ ∉ O := by
  classical
  let q : X →* X ⧸ O := QuotientGroup.mk' O
  obtain ⟨P, P', hP', hPP'⟩ := exists_omega pre hsq
  have hBT := benderType_khat hSz
  have hLH := locHyp_of_omega pre hBT ⟨P', hP'⟩
  obtain ⟨t, hc⟩ := hBT.exists_benderCore P'
  let ch : LocChoice hLH := ⟨P', hP', t, hc⟩
  have hinf := ch.inf_eq
  have hZA := Z0_le_map pre hO hsq
  have hcenP : center ↥(Kb O L) ≤ (P : Subgroup ↥(Kb O L)) :=
    (isPGroup_center hO).le_sylow_of_normal P
  let ua : ↥A → ↥(Kb O L) := fun a => ⟨q a.1, ⟨a.1, hAL a.2, rfl⟩⟩
  have key : ∀ a : ↥A, ua a ∈ (P : Subgroup ↥(Kb O L)) ∧
      ∀ p ∈ (P : Subgroup ↥(Kb O L)), ⁅p, ua a⁆ ∈ center ↥(Kb O L) := by
    intro a
    have hθmem : (rho O L (ua a) : (X ⧸ O) ⧸ Z0 (Kb O L)) ∈
        A.map (theta O L) ⊓ L.map (theta O L) := by
      refine ⟨⟨a.1, a.2, rfl⟩, ⟨a.1, hAL a.2, rfl⟩⟩
    have hw : rho O L (ua a) ∈ rootCenter (P' : Subgroup ↥(L.map (theta O L))) := by
      rw [← hinf]
      exact Subgroup.mem_subgroupOf.mpr hθmem
    obtain ⟨hwP, hwc⟩ := mem_rootCenter_iff.mp hw
    rw [hPP'] at hwP
    obtain ⟨p₁, hp₁, hp₁w⟩ := Subgroup.mem_map.mp hwP
    refine ⟨?_, fun p hp => ?_⟩
    · have hker : p₁⁻¹ * ua a ∈ (rho O L).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hp₁w, inv_mul_cancel]
      rw [rho_ker] at hker
      have := (P : Subgroup ↥(Kb O L)).mul_mem hp₁ (hcenP hker)
      simpa using this
    · have hpP' : rho O L p ∈ (P' : Subgroup ↥(L.map (theta O L))) := by
        rw [hPP']
        exact Subgroup.mem_map_of_mem _ hp
      have hcomm := hwc _ hpP'
      rw [← rho_ker, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
  have hex : ∃ a : ↥A, ∃ p ∈ (P : Subgroup ↥(Kb O L)), p * ua a ≠ ua a * p := by
    by_contra hcon
    push Not at hcon
    have hAZ : ∀ a : ↥A, q a.1 ∈ Z0 (Kb O L) := by
      intro a
      obtain ⟨huaP, -⟩ := key a
      have hcen : (⟨ua a, huaP⟩ : ↥(P : Subgroup ↥(Kb O L))) ∈
          center ↥(P : Subgroup ↥(Kb O L)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcon a g g.2)
      rw [hZP P] at hcen
      have hz : ua a ∈ center ↥(Kb O L) := Subgroup.mem_subgroupOf.mp hcen
      exact mem_Z0.mpr ⟨(ua a).2, fun k hk =>
        congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨k, hk⟩).symm)⟩
    have hinj : Function.Injective (fun a : ↥A => (⟨q a.1, hAZ a⟩ : ↥(Z0 (Kb O L)))) := by
      intro a b hab
      apply Subtype.ext
      exact mk_inj_of_exp_two pre.odd pre.exp a.2 b.2 (congrArg Subtype.val hab)
    have := Nat.card_le_card_of_injective _ hinj
    omega
  obtain ⟨a₁, p, hp, hne⟩ := hex
  obtain ⟨p₀, hp₀L, hp₀'⟩ := p.2
  have hp₀ : q p₀ = (p : X ⧸ O) := hp₀'
  refine ⟨p₀, hp₀L, ?_, ?_, a₁.1, a₁.2, ?_⟩
  · obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have h1 : p ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    have h2 : q (p₀ ^ (2 ^ k)) = 1 := by
      rw [map_pow, hp₀]
      have := congrArg Subtype.val h1
      simpa using this
    exact h2
  · intro a ha
    obtain ⟨-, hcm⟩ := key ⟨a, ha⟩
    have hpinv : p⁻¹ ∈ (P : Subgroup ↥(Kb O L)) := (P : Subgroup ↥(Kb O L)).inv_mem hp
    have hZc : ((⁅p⁻¹, ua ⟨a, ha⟩⁆ : ↥(Kb O L)) : X ⧸ O) ∈ Z0 (Kb O L) := by
      refine mem_Z0.mpr ⟨(⁅p⁻¹, ua ⟨a, ha⟩⁆ : ↥(Kb O L)).2, fun k hk => ?_⟩
      have := Subgroup.mem_center_iff.mp (hcm p⁻¹ hpinv) ⟨k, hk⟩
      exact congrArg Subtype.val this.symm
    obtain ⟨a'', ha'', ha''e⟩ := hZA _ hZc
    have hc₀ : ((⁅p⁻¹, ua ⟨a, ha⟩⁆ : ↥(Kb O L)) : X ⧸ O) =
        (p : X ⧸ O)⁻¹ * q a * (p : X ⧸ O) * (q a)⁻¹ := by
      simp [commutatorElement_def, ua]
    have e1 : q (p₀⁻¹ * a * p₀) = (p : X ⧸ O)⁻¹ * q a * (p : X ⧸ O) := by
      simp only [map_mul, map_inv, hp₀]
    have e2 : q (a''  * a) = q (p₀⁻¹ * a * p₀) := by
      rw [e1, map_mul, ha''e, hc₀]
      group
    have hy : (a'' * a)⁻¹ * (p₀⁻¹ * a * p₀) ∈ O :=
      QuotientGroup.eq.mp e2
    have e3 : p₀⁻¹ * a * p₀ = (a'' * a) * ((a'' * a)⁻¹ * (p₀⁻¹ * a * p₀)) := by group
    rw [e3]
    exact Subgroup.mul_mem_sup (A.mul_mem ha'' ha) hy
  · intro h
    have h1 : q (p₀ * a₁.1 * p₀⁻¹ * a₁.1⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
    simp only [map_mul, map_inv, hp₀] at h1
    have h2 : (p : X ⧸ O) * q a₁.1 = q a₁.1 * (p : X ⧸ O) :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    exact hne (Subtype.ext h2)

theorem caseB_of_K
    (pre : PreHyp O L A) (hO : pPrimeCore 2 (X ⧸ O) = ⊥)
    (hqs : IsQuasisimple ↥(Kb O L)) (hne : center ↥(Kb O L) ≠ ⊥)
    (hSz : Nonempty ((↥(Kb O L) ⧸ center ↥(Kb O L)) ≃* CFSG.Theory.Comparator.SzModel 1))
    (hKI5 : K.KI5) {z : X} (hzA : z ∈ ACx O L A) (hz1 : z ≠ 1) :
    CaseB L A (ACx O L A) z := by
  have hZ2 : IsPGroup 2 ↥(center ↥(Kb O L)) := isPGroup_center hO
  obtain ⟨hcard, hZP, -, hinn, hsq, -⟩ := hKI5 ↥(Kb O L) hqs hZ2 hne hSz
  have hcardZ : Nat.card ↥(Z0 (Kb O L)) = Nat.card ↥(center ↥(Kb O L)) :=
    Subgroup.card_map_of_injective (Kb O L).subtype_injective
  have hperf : _root_.commutator ↥(Kb O L) = ⊤ := Group.isPerfect_def.mp hqs.1
  have hZA := Z0_le_map pre hO hsq
  have hB : BHyp (theta O L) O L A :=
    bhyp_of_K pre.odd pre.exp pre.comm pre.split hperf hZA (by rw [hcardZ]; exact hcard)
  obtain ⟨P, P', hP', hPP'⟩ := exists_omega pre hsq
  have hLH := locHyp_of_omega pre (benderType_khat hSz) ⟨P', hP'⟩
  obtain ⟨Yh, hLoc⟩ := hLH.exists_out
  have hLoc3 : LocOut (L.map (theta O L)) (A.map (theta O L)) Yh 3 := hLoc
  have hZ2' : Nat.card ↥(A ⊓ (theta O L).ker) = 2 → Nat.card ↥(center ↥(Kb O L)) = 2 := by
    intro hk2
    rw [← hcardZ, ← card_inf_ker pre.odd pre.exp hZA]
    exact hk2
  refine hB.caseB hLoc3 hzA hz1 ?_ ?_
  · intro hk2 hAL
    have hZ2'' := hZ2' hk2
    have hA3 : 2 < Nat.card A := by
      have h1 := hB.card_A hLoc3
      have h2 : 0 < Nat.card (ACx O L A) := Nat.card_pos
      omega
    exact htwo_K pre hO hsq hZP hSz hAL (by rw [hcardZ]; exact hZ2'') hA3
  · intro hk2
    exact inn_of_K (hinn (hZ2' hk2))

end BK

end CFSG.GH74.Uniqueness.SU.SU8
