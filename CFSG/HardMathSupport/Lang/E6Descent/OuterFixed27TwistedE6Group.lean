module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwistedDiag


variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

theorem exists_cube_root [IsAlgClosed Ω] (h30 : (3 : Ω) ≠ 0) :
    ∃ ζ : Ωˣ, ζ ^ 3 = 1 ∧ orderOf ζ = 3 := by
  have : NeZero ((3 : ℕ) : Ω) := ⟨by exact_mod_cast h30⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω 3
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω 3
  have hu : IsUnit ζ0 := hζ0.isUnit (by norm_num)
  have hζ3 : hu.unit ^ 3 = 1 := Units.ext (by simpa using hζ0.pow_eq_one)
  refine ⟨hu.unit, hζ3, orderOf_eq_prime hζ3 fun h => ?_⟩
  have h1 : ζ0 = 1 := by simpa using congrArg Units.val h
  exact hζ0.ne_one (by norm_num) h1

theorem exists_fixed_group [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    (h30 : (3 : Ω) ≠ 0) {w : WeylGroup Tag.E6} (hw3 : w ^ 3 = 1) :
    ∃ F : Subgroup (ModGL Tag.E6 Ω), F ≤ thetaFixed Fr ∧ F ≤ DiagTorus.Dgrp Ω ∧
      (∀ f ∈ F, f ^ 3 = 1) ∧
      (∀ f ∈ F, ∀ d ∈ DiagTorus.Dgrp Ω, f * (d * canonicalRep (coxeterSystem Tag.E6) Ω w) =
        (d * canonicalRep (coxeterSystem Tag.E6) Ω w) * f) ∧
      27 ≤ Nat.card F ∧ (w = 1 → 81 ≤ Nat.card F) := by
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root (Ω := Ω) h30
  have hcard : Nat.card ((DiagTorus.fixSub w).map (DiagTorus.Psi (K := Ω) hζ)) =
      Nat.card (DiagWeyl.FixSet w) := by
    rw [Subgroup.card_map_of_injective (DiagTorus.Psi_injective hζ hζ'), DiagTorus.card_fixSub]
  obtain ⟨h27, h81⟩ := DiagWeyl.card_fixed_ge' hw3
  obtain ⟨k, hk⟩ := h3
  have hzq : ζ ^ (q + 1) = 1 := by rw [hk, pow_mul, hζ, one_pow]
  refine ⟨(DiagTorus.fixSub w).map (DiagTorus.Psi hζ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    rw [DiagTorus.Psi_apply]
    refine ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _),
      (theta_rootDiagUnit_eq_iff Fr hFr _).2 fun i => ?_⟩
    rw [DiagTorus.theta, ← pow_mul, mul_comm, pow_mul, hzq, one_pow]
  · rintro _ ⟨u, -, rfl⟩
    exact DiagTorus.Psi_mem_Dgrp hζ u
  · rintro _ ⟨u, -, rfl⟩
    exact DiagTorus.Psi_pow_three hζ u
  · rintro _ ⟨u, hu, rfl⟩ d hd
    have hc := DiagTorus.conj_Psi (K := Ω) hζ w (Multiplicative.toAdd u) hu
    rw [ofAdd_toAdd] at hc
    have hc' : canonicalRep (coxeterSystem Tag.E6) Ω w * DiagTorus.Psi hζ u =
        DiagTorus.Psi hζ u * canonicalRep (coxeterSystem Tag.E6) Ω w :=
      mul_inv_eq_iff_eq_mul.1 hc
    have hcd := DiagTorus.Dgrp_comm (DiagTorus.Psi_mem_Dgrp (K := Ω) hζ u) hd
    calc DiagTorus.Psi hζ u * (d * canonicalRep (coxeterSystem Tag.E6) Ω w) =
        (DiagTorus.Psi hζ u * d) * canonicalRep (coxeterSystem Tag.E6) Ω w := by group
      _ = d * (DiagTorus.Psi hζ u * canonicalRep (coxeterSystem Tag.E6) Ω w) := by
          rw [hcd]; group
      _ = d * (canonicalRep (coxeterSystem Tag.E6) Ω w * DiagTorus.Psi hζ u) := by rw [hc']
      _ = (d * canonicalRep (coxeterSystem Tag.E6) Ω w) * DiagTorus.Psi hζ u := by group
  · rw [hcard]
    exact h27
  · intro hw1
    rw [hcard]
    exact h81 hw1

end TwistedDiag

theorem twentySeven_dvd_of_fixed_group {Γ : Type*} [Group Γ] (R N C : Subgroup Γ) [Finite R]
    (_hNR : N ≤ R) (hCR : C ≤ R) (hC : (C.subgroupOf R).Normal) (hCidx : C.relIndex R ≤ 3)
    (hN : ¬ 3 ∣ N.relIndex R)
    (hF : ∀ y ∈ N, y ^ 3 = 1 → ∃ F : Subgroup Γ, F ≤ R ∧ (∀ f ∈ F, f ^ 3 = 1) ∧
      (∀ f ∈ F, f * y = y * f) ∧ 27 ≤ Nat.card F ∧ (y ∈ F → 81 ≤ Nat.card F))
    {x : Γ} (hxR : x ∈ R) (hx3 : x ^ 3 = 1) :
    27 ∣ Nat.card ↥(Subgroup.centralizer {x} ⊓ C) := by
  classical
  set Cs : Subgroup R := C.subgroupOf R with hCs
  set Ns : Subgroup R := N.subgroupOf R with hNs
  set x' : R := ⟨x, hxR⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  obtain ⟨u, -, d, hd, m, hm, hdm⟩ := DiagGroup.exists_conj_mem_mul (⊤ : Subgroup R) Ns ⊥
    le_top (by simp) (by simp) (by simp) (by
      rw [Subgroup.relIndex_top_right]
      exact hN) (x := x') (by simp) hx'3
  rw [Subgroup.mem_bot] at hd
  subst hd
  rw [one_mul] at hdm
  have hy3 : (u⁻¹ * x' * u) ^ 3 = 1 := by
    have := conj_pow (a := u⁻¹) (b := x') (i := 3)
    rw [inv_inv] at this
    rw [this, hx'3]
    simp
  have hmN : (m : Γ) ∈ N := hm
  have hm3 : (m : Γ) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3
    rw [hdm] at this
    simpa using this
  obtain ⟨F, hFR, hF3, hFy, hF27, hF81⟩ := hF m hmN hm3
  set Fs : Subgroup R := F.subgroupOf R with hFs
  have hFcard : Nat.card Fs = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv
  have key := DiagGroup.twentySeven_dvd_card_centralizer Cs ⊤ Fs (y := m)
    (by rw [← hdm]; exact hy3) (Subgroup.mem_top _) le_top
    (by rw [Subgroup.relIndex_top_right]; exact hCidx)
    (fun f hf => Subtype.ext (by simpa using hF3 f hf))
    (fun f hf => Subtype.ext (hFy f hf))
    (by rw [hFcard]; exact hF27)
    (fun hyF => by rw [hFcard]; exact hF81 hyF)
  have hnorm : u ∈ Subgroup.normalizer (Cs : Set R) := by
    have := hC
    exact Subgroup.mem_normalizer_iff.2 fun c => ⟨fun hc => hC.conj_mem c hc u, fun hc => by
      have := hC.conj_mem _ hc u⁻¹
      simpa [mul_assoc] using this⟩
  rw [← hdm, DiagGroup.card_centralizer_inf_conj Cs hnorm] at key
  have hcard : Nat.card ↥(Subgroup.centralizer {x} ⊓ C) =
      Nat.card ↥(Subgroup.centralizer {x'} ⊓ Cs) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, hCR c.2.2⟩, ?_, c.2.2⟩
        invFun := fun z => ⟨z.1.1, ?_, z.2.2⟩
        left_inv := fun c => rfl
        right_inv := fun z => rfl }
    · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2.1
      exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h)
    · have h := Subgroup.mem_centralizer_singleton_iff.1 z.2.1
      exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h)
  rw [hcard]
  exact key

end CFSG.HardMathSupport.Lang.E6Descent
