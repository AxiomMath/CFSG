module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairFrame

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

theorem e6PhiTwoWeyl_smul_eq_mulVec (x : Fin Tag.E6.rank → ℤ) :
    e6PhiTwoWeyl • x = toMat Tag.E6.rank e6TwoMat *ᵥ x := by
  rw [wordProd_smul_eq_wordMat_mulVec, e6Two_wordMat]

theorem e6PhiTwoWeyl_smul_single_of_mem {i : Fin Tag.E6.rank}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) :
    e6PhiTwoWeyl • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = -Pi.single i 1 := by
  rw [e6PhiTwoWeyl_smul_eq_mulVec]
  rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel

theorem e6PhiTwoWeyl_pair_data {i : Fin Tag.E6.rank} (hi : i = 0 ∨ i = 5) :
    e6PhiTwoWeyl • e6PhiTwoWeyl • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 ∧
      iform (Pi.single i 1) (e6PhiTwoWeyl • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 ∧
      ¬ IsRoot Tag.E6 (Pi.single i 1 + e6PhiTwoWeyl • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∧
      ¬ IsRoot Tag.E6 (Pi.single i 1 - e6PhiTwoWeyl • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
  simp only [e6PhiTwoWeyl_smul_eq_mulVec]
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_⟩
  · rcases hi with rfl | rfl <;> decide +kernel
  · rcases hi with rfl | rfl <;> decide +kernel
  · have hmem := isRoot_iff_mem_artifactRoots.1 h
    rcases hi with rfl | rfl <;> revert hmem <;> decide +kernel
  · have hmem := isRoot_iff_mem_artifactRoots.1 h
    rcases hi with rfl | rfl <;> revert hmem <;> decide +kernel

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · refine ⟨q - 1, ?_⟩
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [h1, hq]
    ring

end Roots

section Field

theorem e6_d4_check : ∀ l ∈ Tag.E6.artifactRoots,
    ¬ (((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m : Fin Tag.E6.rank, Tag.E6.cartan 1 m * l.getD m 0) -
          ((2 ^ 1 : ℕ) : ℤ) * ∑ m : Fin Tag.E6.rank,
            Tag.E6.cartan 1 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m ∧
      ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m : Fin Tag.E6.rank, Tag.E6.cartan 2 m * l.getD m 0) -
          ((2 ^ 1 : ℕ) : ℤ) * ∑ m : Fin Tag.E6.rank,
            Tag.E6.cartan 2 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m ∧
      ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m : Fin Tag.E6.rank, Tag.E6.cartan 3 m * l.getD m 0) -
          ((2 ^ 1 : ℕ) : ℤ) * ∑ m : Fin Tag.E6.rank,
            Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m ∧
      ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m : Fin Tag.E6.rank, Tag.E6.cartan 4 m * l.getD m 0) -
          ((2 ^ 1 : ℕ) : ℤ) * ∑ m : Fin Tag.E6.rank,
            Tag.E6.cartan 4 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m) := by
  decide +kernel

theorem not_e6_d4_label (b : Label Tag.E6)
    (h1 : ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan 1 m * b.latticeWeight m) -
      ((2 ^ 1 : ℕ) : ℤ) * ∑ m, Tag.E6.cartan 1 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m)
    (h2 : ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan 2 m * b.latticeWeight m) -
      ((2 ^ 1 : ℕ) : ℤ) * ∑ m, Tag.E6.cartan 2 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m)
    (h3 : ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan 3 m * b.latticeWeight m) -
      ((2 ^ 1 : ℕ) : ℤ) * ∑ m, Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m)
    (h4 : ((2 ^ 2 + 1 : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan 4 m * b.latticeWeight m) -
      ((2 ^ 1 : ℕ) : ℤ) * ∑ m, Tag.E6.cartan 4 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m) :
    False := by
  rcases b with l | ⟨β, hβ⟩
  · simp only [Label.latticeWeight, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_sub] at h3
    revert h3
    decide +kernel
  · have hmem := isRoot_iff_mem_artifactRoots.1 hβ
    have hget : ∀ m : Fin Tag.E6.rank, (List.ofFn β).getD m 0 = β m := fun m => by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hc := e6_d4_check _ hmem
    simp only [hget] at hc
    exact hc ⟨h1, h2, h3, h4⟩

theorem field_exponent_e6Two {L : Type} [Field L] {ℓ f j : ℕ} (hℓ : ℓ.Prime) (hj : j < f)
    (hq4 : 4 ≤ ℓ ^ f) (hq8 : ℓ ^ f ≠ 8) {z : ModGL Tag.E6 L} {ζ : Lˣ}
    (hζ : orderOf ζ = ℓ ^ f + 1)
    (hz : ∀ i : Fin Tag.E6.rank, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
      z * torusElt Tag.E6 L i (ζ ^ (ℓ ^ j)) * z⁻¹ = torusElt Tag.E6 L i ζ) : j = 0 := by
  have hcong : ∀ I : Set (Fin Tag.E6.rank), (∀ i ∈ I, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
      ∀ α : Label Tag.E6, ∃ b : Label Tag.E6, ∀ i ∈ I,
        ((ℓ ^ f + 1 : ℕ) : ℤ) ∣ (∑ m, Tag.E6.cartan i m * b.latticeWeight m) -
          ((ℓ ^ j : ℕ) : ℤ) * ∑ m, Tag.E6.cartan i m * α.latticeWeight m := by
    intro I hI α
    obtain ⟨b, hb⟩ := exists_label_of_conj_torusElt_on z ζ (ζ ^ (ℓ ^ j)) I
      (fun i hi => hz i (hI i hi)) α
    refine ⟨b, fun i hi => ?_⟩
    have h1 := hb i hi
    rw [← zpow_natCast, ← zpow_mul] at h1
    have h2 := (zpow_eq_zpow_iff_modEq.1 h1).symm.dvd
    rw [hζ] at h2
    exact_mod_cast h2
  by_cases h8 : 8 ≤ ℓ ^ f
  ·
    obtain ⟨b₁, hb₁⟩ := hcong {3} (fun i hi => Or.inr (Or.inr (Or.inl hi)))
      (Sum.inr ⟨Pi.single 3 1, isRoot_single _ 3⟩)
    obtain ⟨b₂, hb₂⟩ := hcong {3} (fun i hi => Or.inr (Or.inr (Or.inl hi)))
      (Sum.inr ⟨-Pi.single 1 1, IsRoot.neg (isRoot_single _ 1)⟩)
    have h₁ := hb₁ 3 rfl
    have h₂ := hb₂ 3 rfl
    have e₁ : (∑ m, Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m) = 2 := by
      decide +kernel
    have e₂ : (∑ m, Tag.E6.cartan 3 m * (-Pi.single 1 1 : Fin Tag.E6.rank → ℤ) m) = 1 := by
      decide +kernel
    change _ ∣ _ - _ * ∑ m, Tag.E6.cartan 3 m * (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) m at h₁
    change _ ∣ _ - _ * ∑ m, Tag.E6.cartan 3 m * (-Pi.single 1 1 : Fin Tag.E6.rank → ℤ) m at h₂
    rw [e₁, mul_comm ((ℓ ^ j : ℕ) : ℤ) 2] at h₁
    rw [e₂, mul_one] at h₂
    exact eq_zero_of_coroot_test hℓ hj h8 (by omega) (abs_pairing_label_le_E6 b₁ 3)
      (abs_pairing_label_le_E6 b₂ 3) h₁ h₂
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · omega
    ·
      have hℓ2 : ℓ = 2 := by
        by_contra hne
        have h3 : 3 ≤ ℓ := by
          have := hℓ.two_le
          omega
        have : 9 ≤ ℓ ^ f := calc
          9 = 3 ^ 2 := by norm_num
          _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left h3 2
          _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf2
        omega
      subst hℓ2
      have hf : f = 2 := by
        by_contra hne
        have : 8 ≤ 2 ^ f := calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hf
      by_contra hj0
      have hj1 : j = 1 := by omega
      subst hj1
      obtain ⟨b, hb⟩ := hcong {1, 2, 3, 4} (fun i hi => hi)
        (Sum.inr ⟨Pi.single 3 1, isRoot_single _ 3⟩)
      exact not_e6_d4_label b (hb 1 (by simp)) (hb 2 (by simp)) (hb 3 (by simp))
        (hb 4 (by simp))

end Field

section Frame


theorem exists_rigid_frame_E6_two {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiTwoWeyl)
    (hK4 : 4 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8) :
    ∃ Z : Fin Tag.E6.rank → Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      (∀ i, Z i ≤ (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0).Γ) ∧
      (∀ i, ⁅Z i, Z i⁆ = Z i) ∧
      (∀ i, Z i ≤ rootSpan Tag.E6 (AlgebraicClosure K) {Pi.single i 1, -Pi.single i 1,
        e6PhiTwoWeyl • Pi.single i 1, -(e6PhiTwoWeyl • Pi.single i 1)}) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K + 1 → ∀ i, ∃ x ∈ Z i, orderOf x = p) ∧
      ∀ δ : MulAut (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0).Γ,
        (∀ x : (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0).Γ,
          (∃ i, (x : ModGL Tag.E6 (AlgebraicClosure K)) ∈ Z i) → δ x = x) → δ = 1 := by
  classical
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set D := LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0 with hD
  obtain ⟨ℓ, f, hℓ, hf, hK, hchar⟩ := exists_char_data K L
  have : ExpChar L ℓ := ExpChar.prime hℓ
  have hdeg : entryDegreeBound Tag.E6 < Nat.card K := by
    have h2 : entryDegreeBound Tag.E6 = 2 := rfl
    omega
  have hpieces : ∀ i : Fin Tag.E6.rank, ∃ Zi : Subgroup (ModGL Tag.E6 L),
      Zi ≤ D.Γ ∧ ⁅Zi, Zi⁆ = Zi ∧
      Zi ≤ rootSpan Tag.E6 L {Pi.single i 1, -Pi.single i 1, e6PhiTwoWeyl • Pi.single i 1,
        -(e6PhiTwoWeyl • Pi.single i 1)} ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K + 1 → ∃ x ∈ Zi, orderOf x = p) ∧
      (∀ z : ModGL Tag.E6 L, (∀ x ∈ Zi, Commute z x) →
        ∀ x ∈ rootRankOneGroup Tag.E6 L (Pi.single i 1), Commute z x) ∧
      ((i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
        ∀ ζ : Lˣ, ζ ^ (Nat.card K + 1) = 1 → torusElt Tag.E6 L i ζ ∈ Zi) := by
    intro i
    by_cases hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4
    · obtain ⟨X, hXΓ, hXp, hXspan, hXtor, hXcomm⟩ :=
        exists_frame_inverted hFr hK4 hdeg hg0C hg0 (e6PhiTwoWeyl_smul_single_of_mem hi)
      refine ⟨X, hXΓ, hXp, hXspan.trans (biSup_mono ?_), fun p hp hp2 hpq => ?_, hXcomm,
        fun _ => hXtor⟩
      · intro γ hγ
        rcases hγ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K (L := L) hpq
        have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
          have h1 := orderOf_dvd_of_pow_eq_one h
          rw [hζord] at h1
          have h2 := Nat.le_of_dvd (by norm_num) h1
          have h3 := hp.two_le
          exact hp2 (by omega)
        refine ⟨_, hXtor ζ hζq, ?_⟩
        have h1 := orderOf_canonicalRep_conj_torusElt (K := L) hp (1 : WeylGroup Tag.E6) i
          hζord hζ2
        rwa [canonicalRep_one, one_mul, inv_one, mul_one] at h1
    · have hi' : i = 0 ∨ i = 5 := by
        fin_cases i
        · exact Or.inl rfl
        · exact absurd (Or.inl rfl) hi
        · exact absurd (Or.inr (Or.inl rfl)) hi
        · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hi
        · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hi
        · exact Or.inr rfl
      obtain ⟨hww, h0, hpr, hmr⟩ := e6PhiTwoWeyl_pair_data hi'
      obtain ⟨Y, hYΓ, hYp, hYspan, hYord, hYcomm⟩ := exists_frame_pair_untw (τ := Tag.E6) rfl
        hFr hK4 hg0C hg0 (isRoot_single _ i) hww h0 hpr hmr
      exact ⟨Y, hYΓ, hYp, hYspan, fun p hp hp2 hpq => hYord p hp hp2
        (hpq.trans (add_one_dvd_sq_sub_one _)), hYcomm, fun h => absurd h hi⟩
  choose Z hZΓ hZp hZspan hZord hZcomm hZtor using hpieces
  refine ⟨Z, hZΓ, hZp, hZspan, fun p hp hp2 hpq i => hZord i p hp hp2 hpq, fun δ hδ => ?_⟩
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype) :=
    langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFr D rfl Nat.prime_seven (by norm_num)
      (commutator_adjointGroup_E6_eq_top K)
  have hΓ : D.Γ = langModel Tag.E6 K L g0 := by
    rw [hd.Γ_eq, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  set e : adjointGroup Tag.E6 K ≃* D.Γ :=
    (langModelMulEquiv Tag.E6 K L g0).trans (MulEquiv.subgroupCongr hΓ.symm) with he_def
  have he : ∀ h : adjointGroup Tag.E6 K, (e h : ModGL Tag.E6 L) =
      g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL Tag.E6 K) * g0 := fun h => by
    show ((langModelMulEquiv Tag.E6 K L g0 h : langModel Tag.E6 K L g0) : ModGL Tag.E6 L) = _
    rw [coe_langModelMulEquiv, inv_inv]
  have hΓC : D.Γ ≤ adjointGroup Tag.E6 L := by
    rw [hΓ]
    exact langModel_le_adjointGroup Tag.E6 K L hg0C
  set Sfix : Set (ModGL Tag.E6 L) := {x | ∃ i, x ∈ Z i} with hSfix
  have hSΓ : Sfix ⊆ D.Γ := fun x ⟨i, hi⟩ => hZΓ i hi
  refine eq_one_of_fix_of_centralizes hℓ hf hK hΓC e he (fun α => ?_) Sfix hSΓ
    (fun j hj z hz => ?_) (fun Z' hZ' => ?_) δ (fun x hx => hδ ⟨x, hSΓ hx⟩ hx)
  ·
    obtain ⟨g, a, σ, ε, hα⟩ :=
      (ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K).2.2 α
    refine ⟨(g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε, σ, fun h => ?_⟩
    rw [hα h]
    group
  ·
    obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K (L := L) (dvd_refl _)
    have hj0 : j = 0 := by
      refine field_exponent_e6Two (z := z) hℓ hj (by rw [← hK]; exact hK4) (by rw [← hK]; exact hK8)
        (by rw [hζord, hK]) fun i hi => ?_
      have h1 := hz _ ⟨i, hZtor i hi ζ hζq⟩
      rw [units_map_entrywiseHom_torusElt] at h1
      have hζσ : Units.map (iterateFrobenius L ℓ j).toMonoidHom ζ = ζ ^ (ℓ ^ j) :=
        Units.ext (by rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
          iterateFrobenius_def, Units.val_pow_eq_pow_val])
      rw [hζσ] at h1
      exact h1.symm
    refine ⟨1, fun x _ => ?_⟩
    rw [hj0, iterateFrobenius_zero, one_mul, inv_one, mul_one]
    exact Units.ext (entrywise_id _)
  ·
    exact commute_adjointGroup_of_simple fun i => hZcomm i Z' fun x hx => hZ' x ⟨i, hx⟩

theorem setupRigid_E6_two {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiTwoWeyl)
    (hK4 : 4 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8) {p : ℕ} (hp2 : p ≠ 2)
    (hpq1 : p ∣ Nat.card K + 1) [IsAlgClosed (AlgebraicClosure K)]
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0) :
    SetupRigid S := by
  obtain ⟨D, ρ, frob, E, hp, hq, hqpow, hpq, hfin, hEle, hEexp, hEall⟩ := S
  simp only at hSD
  subst hSD
  obtain ⟨Z, hZΓ, hZp, hZspan, hZord, hrig⟩ := exists_rigid_frame_E6_two hFr hg0C hg0 hK4 hK8
  refine setupRigid_of_frame _ Z (fun i => Pi.single i 1) (fun i => isRoot_single _ i) hZΓ hZp
    (fun i => ?_) (fun i => hZord p hp hp2 hpq1 i) hrig
  have hρ := frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 frob (isRoot_single _ i)
  change Z i ≤ rootSpan Tag.E6 _
    {Pi.single i 1, -Pi.single i 1, ρ (Pi.single i 1), -ρ (Pi.single i 1)}
  rw [hρ]
  exact hZspan i

theorem setupRigidAtFrobenius_E6_two {p : ℕ} (hp2 : p ≠ 2) {Q : ℕ → Prop}
    (hQ : ∀ q, Q q → p ∣ q + 1 ∧ 4 ≤ q ∧ q ≠ 8) :
    SetupRigidAtFrobenius Tag.E6 e6PhiTwoWeyl p Q := by
  intro K _ _ Fr hFr g0 hg0C hg0 S hSD hQK
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨hpq1, hK4, hK8⟩ := hQ _ hQK
  exact setupRigid_E6_two hFr hg0C hg0 hK4 hK8 hp2 hpq1 S hSD

theorem langTorusPlaneBalance_E6_two_five_of_components (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    LangTorusPlaneBalance Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1 :=
  langTorusPlaneBalance_E6_two_five_of_setupRigidAt
    (setupRigidAtFrobenius_E6_two (by norm_num) fun q (hq : 5 ∣ q + 1) =>
      ⟨hq, by omega, by omega⟩) hsub hin hsu htw hex

theorem crossCharInnerAt_E6_five_dvd_add_one_of_components (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card + 1) ∧ p = 5 :=
  crossCharInnerAt_E6_five_dvd_add_one
    (langTorusPlaneBalance_E6_two_five_of_components hsub hin hsu htw hex)

end Frame

end CFSG.HardMathSupport.Timmesfeld.CrossChar
