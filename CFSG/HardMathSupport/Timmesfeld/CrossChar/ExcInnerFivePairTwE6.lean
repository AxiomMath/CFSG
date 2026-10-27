module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Roots

theorem twE6PhiOneWeyl_smul_perm (x : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6PhiOneWeyl • permLattice TwistTag.E6.perm x =
      toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ x := by
  rw [twE6PhiOneWeyl_smul, permLattice_E6_perm_perm]

theorem twE6PhiOneWeyl_smul_perm_single_of_mem {i : Fin TwistTag.E6.tag.rank}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) :
    twE6PhiOneWeyl • permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single i 1 := by
  rw [twE6PhiOneWeyl_smul_perm]
  rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel

theorem twE6PhiOneWeyl_pair_data {i : Fin TwistTag.E6.tag.rank} (hi : i = 0 ∨ i = 5) :
    twE6PhiOneWeyl • permLattice TwistTag.E6.perm (twE6PhiOneWeyl •
        permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) =
      Pi.single i 1 ∧
    iform (Pi.single i 1) (twE6PhiOneWeyl •
      permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 ∧
    ¬ IsRoot TwistTag.E6.tag (Pi.single i 1 + twE6PhiOneWeyl •
      permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) ∧
    ¬ IsRoot TwistTag.E6.tag (Pi.single i 1 - twE6PhiOneWeyl •
      permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by
  simp only [twE6PhiOneWeyl_smul_perm]
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_⟩
  · rcases hi with rfl | rfl <;> decide +kernel
  · rcases hi with rfl | rfl <;> decide +kernel
  · have hmem := isRoot_iff_mem_artifactRoots.1 h
    rcases hi with rfl | rfl <;> revert hmem <;> decide +kernel
  · have hmem := isRoot_iff_mem_artifactRoots.1 h
    rcases hi with rfl | rfl <;> revert hmem <;> decide +kernel

private theorem prime_pow_ne_six {ℓ f : ℕ} (hℓ : ℓ.Prime) : ℓ ^ f ≠ 6 := by
  intro h
  have h2 : 2 ∣ ℓ := Nat.prime_two.dvd_of_dvd_pow (by rw [h]; norm_num)
  have h3 : 3 ∣ ℓ := Nat.prime_three.dvd_of_dvd_pow (by rw [h]; norm_num)
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h2
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 h3
  omega

end Roots

section Field

theorem eq_zero_of_conj_torusElt_three_E6 {L : Type} [Field L] {ℓ f j N : ℕ} (hℓ : ℓ.Prime)
    (hj : j < f) (hq8 : 8 ≤ ℓ ^ f) (hN : ℓ ^ f ≤ N + 1) {z : ModGL Tag.E6 L} {ζ : Lˣ}
    (hζ : orderOf ζ = N)
    (hz : z * torusElt Tag.E6 L 3 (ζ ^ (ℓ ^ j)) * z⁻¹ = torusElt Tag.E6 L 3 ζ) : j = 0 := by
  have hcong : ∀ α : Label Tag.E6, ∃ b : Label Tag.E6,
      ((N : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan 3 m * b.latticeWeight m) -
        ((ℓ ^ j : ℕ) : ℤ) * ∑ m, Tag.E6.cartan 3 m * α.latticeWeight m := by
    intro α
    obtain ⟨b, hb⟩ := exists_label_of_conj_torusElt_on z ζ (ζ ^ (ℓ ^ j)) {3}
      (fun i hi => by
        obtain rfl := Set.mem_singleton_iff.1 hi
        exact hz) α
    refine ⟨b, ?_⟩
    have h1 := hb 3 rfl
    rw [← zpow_natCast, ← zpow_mul] at h1
    have h2 := (zpow_eq_zpow_iff_modEq.1 h1).symm.dvd
    rw [hζ] at h2
    exact_mod_cast h2
  obtain ⟨b₁, h₁⟩ := hcong (Sum.inr ⟨Pi.single 3 1, isRoot_single _ 3⟩)
  obtain ⟨b₂, h₂⟩ := hcong (Sum.inr ⟨-Pi.single 1 1, IsRoot.neg (isRoot_single _ 1)⟩)
  have e₁ : (∑ m, Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m) = 2 := by
    decide +kernel
  have e₂ : (∑ m, Tag.E6.cartan 3 m * (-Pi.single 1 1 : Fin Tag.E6.rank → ℤ) m) = 1 := by
    decide +kernel
  change _ ∣ _ - _ * ∑ m, Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m at h₁
  change _ ∣ _ - _ * ∑ m, Tag.E6.cartan 3 m * (-Pi.single 1 1 : Fin Tag.E6.rank → ℤ) m at h₂
  rw [e₁, mul_comm ((ℓ ^ j : ℕ) : ℤ) 2] at h₁
  rw [e₂, mul_one] at h₂
  exact eq_zero_of_coroot_test hℓ hj hq8 hN (abs_pairing_label_le_E6 b₁ 3)
    (abs_pairing_label_le_E6 b₂ 3) h₁ h₂

theorem twisted_field_exponent_twOne {L : Type} [Field L] {ℓ f j : ℕ} (hℓ : ℓ.Prime)
    (hj : j < 2 * f) (hq8 : 8 ≤ ℓ ^ f) {z : ModGL Tag.E6 L} {ζ : Lˣ}
    (hζ : orderOf ζ = ℓ ^ f - 1)
    (hz : z * torusElt Tag.E6 L 3 (ζ ^ (ℓ ^ j)) * z⁻¹ = torusElt Tag.E6 L 3 ζ) :
    j = 0 ∨ j = f := by
  have hN : ℓ ^ f ≤ (ℓ ^ f - 1) + 1 := by omega
  rcases Nat.lt_or_ge j f with hjf | hjf
  · exact Or.inl (eq_zero_of_conj_torusElt_three_E6 hℓ hjf hq8 hN hζ hz)
  · right
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hjf
    have hζq : ζ ^ (ℓ ^ f) = ζ := by
      have h1 : ζ ^ (ℓ ^ f - 1) = 1 := by
        rw [← hζ]
        exact pow_orderOf_eq_one ζ
      calc ζ ^ (ℓ ^ f) = ζ ^ ((ℓ ^ f - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = ζ := by rw [pow_succ, h1, one_mul]
    have hz' : z * torusElt Tag.E6 L 3 (ζ ^ (ℓ ^ j')) * z⁻¹ = torusElt Tag.E6 L 3 ζ := by
      rw [pow_add, pow_mul, hζq] at hz
      exact hz
    have := eq_zero_of_conj_torusElt_three_E6 hℓ (by omega) hq8 hN hζ hz'
    omega

end Field

section Frame


theorem exists_rigid_frame_twistedE6_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6PhiOneWeyl)
    (hq8 : 8 ≤ ℓ ^ f) :
    ∃ Z : Fin TwistTag.E6.tag.rank → Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)),
      (∀ i, Z i ≤ (LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0).Γ) ∧
      (∀ i, ⁅Z i, Z i⁆ = Z i) ∧
      (∀ i, Z i ≤ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {Pi.single i 1, -Pi.single i 1,
        twE6PhiOneWeyl • permLattice TwistTag.E6.perm (Pi.single i 1),
        -(twE6PhiOneWeyl • permLattice TwistTag.E6.perm (Pi.single i 1))}) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ ℓ ^ f - 1 → ∀ i, ∃ x ∈ Z i, orderOf x = p) ∧
      ∀ δ : MulAut (LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0).Γ,
        (∀ x : (LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0).Γ,
          (∃ i, (x : ModGL TwistTag.E6.tag (AlgebraicClosure K)) ∈ Z i) → δ x = x) → δ = 1 := by
  classical
  set L := AlgebraicClosure K with hLdef
  set D := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0 with hDdef
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : ExpChar L ℓ := ExpChar.prime hℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hqL : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨-, -, -, -, -, k, -, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K (by rw [hK]; rfl)
  let _ : Algebra k L := ((algebraMap K L).comp k.subtype).toAlgebra
  have : Finite k := Subtype.finite
  have hdeg : entryDegreeBound TwistTag.E6.tag < ℓ ^ f := by
    have h2 : entryDegreeBound TwistTag.E6.tag = 2 := rfl
    omega
  have hpieces : ∀ i : Fin TwistTag.E6.tag.rank, ∃ Zi : Subgroup (ModGL TwistTag.E6.tag L),
      Zi ≤ D.Γ ∧ ⁅Zi, Zi⁆ = Zi ∧
      Zi ≤ rootSpan TwistTag.E6.tag L {Pi.single i 1, -Pi.single i 1,
        twE6PhiOneWeyl • permLattice TwistTag.E6.perm (Pi.single i 1),
        -(twE6PhiOneWeyl • permLattice TwistTag.E6.perm (Pi.single i 1))} ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ ℓ ^ f - 1 → ∃ x ∈ Zi, orderOf x = p) ∧
      (∀ z : ModGL TwistTag.E6.tag L, (∀ x ∈ Zi, Commute z x) →
        ∀ x ∈ rootRankOneGroup TwistTag.E6.tag L (Pi.single i 1), Commute z x) ∧
      ((i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
        ∀ ζ : Lˣ, ζ ^ (ℓ ^ f - 1) = 1 → torusElt TwistTag.E6.tag L i ζ ∈ Zi) := by
    intro i
    by_cases hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4
    · obtain ⟨X, hXΓ, hXp, hXspan, hXtor, hXcomm⟩ := exists_frame_fixed_twist (K₀ := k)
        hkcard hFr (by omega) hdeg hg0C hg0 (twE6PhiOneWeyl_smul_perm_single_of_mem hi)
      refine ⟨X, hXΓ, hXp, hXspan.trans (biSup_mono ?_), fun p hp hp2 hpq => ?_, hXcomm,
        fun _ => hXtor⟩
      · intro γ hγ
        rcases hγ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · obtain ⟨ζ, hζord⟩ := exists_orderOf_eq_of_natCast_ne_zero (L := L) (N := p)
          (natCast_ne_zero_of_dvd_pow_sub_one hqL (by omega) le_rfl (by rw [pow_one]; exact hpq))
        have hζq : ζ ^ (ℓ ^ f - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζord]; exact hpq)
        have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
          have h1 := orderOf_dvd_of_pow_eq_one h
          rw [hζord] at h1
          have h2 := Nat.le_of_dvd (by norm_num) h1
          have h3 := hp.two_le
          exact hp2 (by omega)
        refine ⟨_, hXtor ζ hζq, ?_⟩
        have h1 := orderOf_canonicalRep_conj_torusElt (K := L) hp
          (1 : WeylGroup TwistTag.E6.tag) i hζord hζ2
        rwa [canonicalRep_one, one_mul, inv_one, mul_one] at h1
    · have hi' : i = 0 ∨ i = 5 := by
        fin_cases i
        · exact Or.inl rfl
        · exact absurd (Or.inl rfl) hi
        · exact absurd (Or.inr (Or.inl rfl)) hi
        · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hi
        · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hi
        · exact Or.inr rfl
      obtain ⟨hww, h0, hpr, hmr⟩ := twE6PhiOneWeyl_pair_data hi'
      obtain ⟨Y, hYΓ, hYp, hYspan, hYord, hYcomm⟩ := exists_frame_pair_twist
        (t := TwistTag.E6) rfl (K := K) hFr (by omega) hK hg0C hg0 (isRoot_single _ i) hww h0
        hpr hmr
      exact ⟨Y, hYΓ, hYp, hYspan, fun p hp hp2 hpq => hYord p hp hp2
        (hpq.trans (sub_one_dvd_sq_sub_one _)), hYcomm, fun h => absurd h hi⟩
  choose Z hZΓ hZp hZspan hZord hZcomm hZtor using hpieces
  refine ⟨Z, hZΓ, hZp, hZspan, fun p hp hp2 hpq i => hZord i p hp hp2 hpq, fun δ hδ => ?_⟩
  have hΦ : D.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hΓM : D.Γ ≤ D.model := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact D.model.mul_mem (D.model.mul_mem (D.model.mul_mem ha hb) (D.model.inv_mem ha))
      (D.model.inv_mem hb)
  have hΓC : D.Γ ≤ adjointGroup TwistTag.E6.tag L := fun x hx => (hΓM hx).1
  have hKF : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, hcoe, hfa, hnf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  set Sfix : Set (ModGL TwistTag.E6.tag L) := {x | ∃ i, x ∈ Z i} with hSfix
  have hSΓ : Sfix ⊆ D.Γ := fun x ⟨i, hi⟩ => hZΓ i hi
  refine eq_one_of_fix_of_centralizes hℓ (by omega) hKF hΓC
    (twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ) (coe_twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ)
    (fun α => ?_) Sfix hSΓ (fun j hj z hz => ?_) (fun Z' hZ' => ?_) δ
    (fun x hx => hδ ⟨x, hSΓ hx⟩ hx)
  ·
    obtain ⟨g, u, δ', hα⟩ := hnf α
    refine ⟨(g : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u), δ', fun h => ?_⟩
    rw [hα]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, hfa]
    group
  ·
    obtain ⟨ζ, hζord⟩ := exists_orderOf_eq_of_natCast_ne_zero (L := L) (N := ℓ ^ f - 1)
      (natCast_ne_zero_of_dvd_pow_sub_one hqL (by omega) le_rfl
        (dvd_of_eq (by rw [pow_one])))
    have hζq : ζ ^ (ℓ ^ f - 1) = 1 := by
      rw [← hζord]
      exact pow_orderOf_eq_one ζ
    have h1 := hz _ ⟨3, hZtor 3 (Or.inr (Or.inr (Or.inl rfl))) ζ hζq⟩
    rw [units_map_entrywiseHom_torusElt] at h1
    have hζσ : Units.map (iterateFrobenius L ℓ j).toMonoidHom ζ = ζ ^ (ℓ ^ j) :=
      Units.ext (by rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        iterateFrobenius_def, Units.val_pow_eq_pow_val])
    rw [hζσ] at h1
    rcases twisted_field_exponent_twOne (z := z) hℓ hj hq8 hζord h1.symm with hj0 | hjf
    · refine ⟨1, fun x _ => ?_⟩
      rw [hj0, iterateFrobenius_zero, one_mul, inv_one, mul_one]
      exact Units.ext (entrywise_id _)
    ·
      have hFrf : iterateFrobenius L ℓ j = Fr := RingHom.ext fun c => by
        rw [iterateFrobenius_def, hFr, hjf]
      refine ⟨(D.n * diagramMap TwistTag.E6 L)⁻¹, fun x hx => ?_⟩
      rw [hFrf]
      have hxM := (D.mem_model.1 (hΓM hx)).2
      rw [hΦ] at hxM
      simp only [twistHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] at hxM
      calc Units.map (entrywiseHom Fr) x =
          (D.n * diagramMap TwistTag.E6 L)⁻¹ *
            (D.n * (diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) x *
              (diagramMap TwistTag.E6 L)⁻¹) * D.n⁻¹) * (D.n * diagramMap TwistTag.E6 L) := by
            group
        _ = _ := by rw [hxM, inv_inv]
  ·
    exact commute_adjointGroup_of_simple fun i => hZcomm i Z' fun x hx => hZ' x ⟨i, hx⟩

theorem setupRigid_twistedE6_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6PhiOneWeyl)
    (hq8 : 8 ≤ ℓ ^ f) {p : ℕ} (hp2 : p ≠ 2) (hpq1 : p ∣ ℓ ^ f - 1)
    [IsAlgClosed (AlgebraicClosure K)] (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr twE6PhiOneWeyl hg0C hg0) :
    SetupRigid S := by
  obtain ⟨D, ρ, frob, E, hp, hq, hqpow, hpq, hfin, hEle, hEexp, hEall⟩ := S
  simp only at hSD
  subst hSD
  obtain ⟨Z, hZΓ, hZp, hZspan, hZord, hrig⟩ :=
    exists_rigid_frame_twistedE6_one hℓ hf hK hσ hFr hg0C hg0 hq8
  refine setupRigid_of_frame _ Z (fun i => Pi.single i 1) (fun i => isRoot_single _ i) hZΓ hZp
    (fun i => ?_) (fun i => hZord p hp hp2 hpq1 i) hrig
  have hρ := frobRootMap_ofTwist_apply (pow_pos hℓ.pos f) hFr hg0C hg0 frob (isRoot_single _ i)
  change Z i ≤ rootSpan TwistTag.E6.tag _
    {Pi.single i 1, -Pi.single i 1, ρ (Pi.single i 1), -ρ (Pi.single i 1)}
  rw [hρ]
  exact hZspan i

theorem setupRigidAtTwistedE6_one {p : ℕ} (hp2 : p ≠ 2) {Q : ℕ → Prop}
    (hQ : ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → Q (ℓ ^ f) → p ∣ ℓ ^ f - 1 ∧ 8 ≤ ℓ ^ f) :
    SetupRigidAtTwistedE6 twE6PhiOneWeyl p Q := by
  intro ℓ f hℓ hf hQq K _ hK σ hσ Fr hFr g0 hg0C hg0 S hSD
  obtain ⟨hpq1, hq8⟩ := hQ ℓ f hℓ hf hQq
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  exact setupRigid_twistedE6_one hℓ hf hK hσ hFr hg0C hg0 hq8 hp2 hpq1 S hSD

theorem eight_le_of_five_dvd_sub_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (h5 : 5 ∣ ℓ ^ f - 1) : 8 ≤ ℓ ^ f := by
  have h2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have h6 := prime_pow_ne_six (f := f) hℓ
  omega

theorem twistedE6LangTorusPlaneBalance_one_five_of_components (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1 :=
  twistedE6LangTorusPlaneBalance_one_five_of_setupRigidAt
    (setupRigidAtTwistedE6_one (by norm_num) fun ℓ f hℓ hf (hq : 5 ∣ ℓ ^ f - 1) =>
      ⟨hq, eight_le_of_five_dvd_sub_one hℓ hf hq⟩) hsub hin hsu htw hex

theorem crossCharInnerAt_twistedE6_five_of_components_only (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    CrossCharInnerAt .twistedE6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 :=
  crossCharInnerAt_twistedE6_five_of_components hsub hin hsu htw hex
    (twistedE6LangTorusPlaneBalance_one_five_of_components hsub hin hsu htw hex)

end Frame

end CFSG.HardMathSupport.Timmesfeld.CrossChar
