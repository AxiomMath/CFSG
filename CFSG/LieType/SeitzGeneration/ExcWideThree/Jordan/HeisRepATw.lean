module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepAUntw

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


namespace HeisA

variable {L : Type} [Field L]

theorem rootChar_perm_pow (a : Fin Tag.E6.rank → Lˣ) (q : ℕ) (ρ : Equiv.Perm (Fin Tag.E6.rank))
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => (a ^ q) (ρ.symm i)) v = rootChar a (permLattice ρ.symm v) ^ q := by
  simp only [rootChar, permLattice, Pi.pow_apply, Equiv.symm_symm, Function.comp_apply]
  rw [← Finset.prod_pow]
  rw [← Equiv.prod_comp ρ.symm (fun j => (a j ^ v (ρ j)) ^ q)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Equiv.apply_symm_apply]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem permLattice_symm_permLattice (ρ : Equiv.Perm (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    permLattice ρ.symm (permLattice ρ v) = v := by
  ext i
  simp [permLattice]

theorem permLattice_permLattice_symm (ρ : Equiv.Perm (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    permLattice ρ (permLattice ρ.symm v) = v := by
  ext i
  simp [permLattice]

theorem image_kernel_of_perm [IsAlgClosed L] {a : Fin Tag.E6.rank → Lˣ}
    {g : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} {q : ℕ} (hpq : Nat.Coprime 3 q)
    (ha3 : ∀ i, a i ^ 3 = 1) (hroot : ∀ β, IsRoot Tag.E6 β → IsRoot Tag.E6 (g β))
    (hsurj : ∀ β, IsRoot Tag.E6 β → ∃ α, IsRoot Tag.E6 α ∧ g α = β)
    (hχ : ∀ β, rootChar a (g β) = rootChar a β ^ q) : g '' rootCharKernel a = rootCharKernel a := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hχα⟩, rfl⟩
    exact ⟨hroot α hα, by rw [hχ, hχα, one_pow]⟩
  · rintro ⟨hβ, hχβ⟩
    obtain ⟨α, hα, rfl⟩ := hsurj β hβ
    refine ⟨α, ⟨hα, ?_⟩, rfl⟩
    have h1 : rootChar a α ^ q = 1 := by rw [← hχ]; exact hχβ
    have h2 : rootChar a α ^ 3 = 1 := rootChar_pow_eq_one a ha3 α
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [hpq] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)

theorem exists_fixed_tw [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) (hpq : Nat.Coprime 3 (ℓ ^ f)) {a b : Fin Tag.E6.rank → Lˣ}
    {w : WeylGroup Tag.E6} (D : CompData a w) (hw : w ∈ rootCharStabilizer a)
    (ha3 : ∀ i, a i ^ 3 = 1) {u y : ModGL Tag.E6 L}
    (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (hy : y = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (hy3 : y ^ 3 = 1) (w' : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank))
    (hρ : ∀ i j, Tag.E6.cartan (ρ i) (ρ j) = Tag.E6.cartan i j) {P : ModGL Tag.E6 L}
    (hP : ActsAs P (permLattice ρ))
    (hPN : P ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)))
    (hPd : ∀ c : Fin Tag.E6.rank → Lˣ, P * rootDiagUnit Tag.E6 c * P⁻¹ =
      rootDiagUnit Tag.E6 (fun i => c (ρ.symm i)))
    (hT : canonicalRep (coxeterSystem Tag.E6) L w' *
      (P * entrywiseFrobGL Tag.E6 L ℓ f (rootDiagUnit Tag.E6 a) * P⁻¹) *
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = rootDiagUnit Tag.E6 a)
    (hΦy : (canonicalRep (coxeterSystem Tag.E6) L w' * P) * entrywiseFrobGL Tag.E6 L ℓ f y *
      (canonicalRep (coxeterSystem Tag.E6) L w' * P)⁻¹ = y) :
    ∃ x ∈ familyGroup (K := L) (fun _ : Unit => a), x ≠ 1 ∧ x ^ ℓ = 1 ∧ y * x * y⁻¹ = x ∧
      (canonicalRep (coxeterSystem Tag.E6) L w' * P) * entrywiseFrobGL Tag.E6 L ℓ f x *
        (canonicalRep (coxeterSystem Tag.E6) L w' * P)⁻¹ = x := by
  have hT1 : rootDiagUnit Tag.E6 a = canonicalRep (coxeterSystem Tag.E6) L w' *
      rootDiagUnit Tag.E6 (fun i => (a ^ ℓ ^ f) (ρ.symm i)) *
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ := by
    have h := hT
    rw [entrywiseFrobGL_rootDiagUnit_eq_pow ℓ f a, hPd] at h
    exact h.symm
  have hχ0 : ∀ v, rootChar a (w' • v) = rootChar a (permLattice ρ.symm v) ^ ℓ ^ f := by
    intro v
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) a _ w').1 hT1 v
    rw [this]
    exact rootChar_perm_pow a (ℓ ^ f) ρ v
  have hn : ActsAs (canonicalRep (coxeterSystem Tag.E6) L w' * P)
      (fun v => w' • permLattice ρ v) := (actsAs_canonicalRep w').mul hP
  have hroot : ∀ β, IsRoot Tag.E6 β → IsRoot Tag.E6 (w' • permLattice ρ β) :=
    fun β hβ => IsRoot.smul (IsRoot.permLattice hρ hβ) w'
  have hsurj : ∀ β, IsRoot Tag.E6 β → ∃ α, IsRoot Tag.E6 α ∧ w' • permLattice ρ α = β := by
    intro β hβ
    refine ⟨permLattice ρ.symm (w'⁻¹ • β), ?_, ?_⟩
    · exact IsRoot.permLattice (cartan_perm_symm hρ) (IsRoot.smul hβ w'⁻¹)
    · rw [permLattice_permLattice_symm, smul_inv_smul]
  have hχ : ∀ β, rootChar a (w' • permLattice ρ β) = rootChar a β ^ ℓ ^ f := by
    intro β
    rw [hχ0, permLattice_symm_permLattice]
  have himg := image_kernel_of_perm hpq ha3 hroot hsurj hχ
  have hTn : canonicalRep (coxeterSystem Tag.E6) L w' * P ∈
      Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) :=
    mul_mem (canonicalRep_mem_normalizer w') hPN
  have hnN := mem_normalizer_familyGroup_of_actsAs hn hTn himg
  have hgSig : ∀ β ∈ rootCharKernel a, w' • permLattice ρ β ∈ rootCharKernel a :=
    fun β hβ => by
      have h' : w' • permLattice ρ β ∈
          (fun v => w' • permLattice ρ v) '' rootCharKernel a := ⟨β, hβ, rfl⟩
      rwa [himg] at h'
  exact exists_fixed_norm hf D hw hu hy hy3 hn hgSig hnN hΦy

end HeisA

theorem twE6HeisFrameFixedEltA_holds : TwE6HeisFrameFixedEltA := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hd hE hcard F hA
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι : K →+* L := algebraMap K L with hι
  have hpq : Nat.Coprime 3 (ℓ ^ f) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hFrEq : F.Fr = iterateFrobenius L ℓ f := RingHom.ext fun c => by
    rw [F.hFr, iterateFrobenius_def]
  obtain ⟨g0, hg0e⟩ : ∃ g0 : ModGL Tag.E6 L, g0 = F.g0 := ⟨_, rfl⟩
  obtain ⟨P, hPe⟩ : ∃ P : ModGL Tag.E6 L, P = diagramMap TwistTag.E6 L := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ModGL Tag.E6 L →* ModGL Tag.E6 L,
      T = twistHom TwistTag.E6 L F.Fr := ⟨_, rfl⟩
  obtain ⟨w', hw'e⟩ : ∃ w' : WeylGroup Tag.E6, w' = F.w' := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁e⟩ : ∃ B : ModGL Tag.E6 L,
      B = baseChangeGL ι (F.g₁ : ModGL TwistTag.E6.tag K) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂e⟩ : ∃ B : ModGL Tag.E6 L,
      B = baseChangeGL ι (F.g₂ : ModGL TwistTag.E6.tag K) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ModGL Tag.E6 L, y = g0⁻¹ * B₂ * g0 := ⟨_, rfl⟩
  have hTw : ∀ g : ModGL Tag.E6 L, T g = P * entrywiseFrobGL Tag.E6 L ℓ f g * P⁻¹ := fun g => by
    rw [hTdef, hPe, hFrEq]
    rfl
  have hg0 : T g0 = g0 * canonicalRep (coxeterSystem Tag.E6) L w' := by
    rw [hTdef, hg0e, hw'e]
    exact F.hg0
  have hFix : T B₂ = B₂ := by
    rw [hTdef, hB₂e]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L F.Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ F.Fr F.hFr
        (Subgroup.mem_map_of_mem _ F.g₂.2))).2
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hg₂3 : F.g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ F.hE₂)
  have hd₂3 : (F.g₂ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hB₂3' : (baseChangeGL ι (F.g₂ : ModGL TwistTag.E6.tag K)) ^ 3 = 1 := by
    rw [← map_pow, hd₂3, map_one]
  have hB₂3 : B₂ ^ 3 = 1 := by
    rw [hB₂e]
    exact hB₂3'
  have hy3 : y ^ 3 = 1 := by
    have := conj_pow (a := g0⁻¹) (b := B₂) (i := 3)
    simp only [inv_inv] at this
    rw [hydef, this, hB₂3]
    group
  have hy : y = F.u⁻¹ * (rootDiagUnit Tag.E6 F.b * canonicalRep (coxeterSystem Tag.E6) L F.w) *
      F.u := by
    rw [hydef, hg0e, hB₂e]
    exact F.hg₂
  obtain ⟨C, π, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9⟩ := classA_components hA
  let D : HeisA.CompData F.a F.w := ⟨C, π, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9⟩
  have hT : canonicalRep (coxeterSystem Tag.E6) L w' *
      (P * entrywiseFrobGL Tag.E6 L ℓ f (rootDiagUnit Tag.E6 F.a) * P⁻¹) *
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = rootDiagUnit Tag.E6 F.a := by
    rw [← hTw, hTdef, hw'e]
    exact (mem_twistedTorusOf.1 F.hT).2
  have hPd : ∀ c : Fin Tag.E6.rank → Lˣ, P * rootDiagUnit Tag.E6 c * P⁻¹ =
      rootDiagUnit Tag.E6 (fun i => c (TwistTag.E6.perm.symm i)) := fun c => by
    have h := diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.E6) c
    have h' : P * rootDiagUnit Tag.E6 c =
        rootDiagUnit Tag.E6 (fun i => c (TwistTag.E6.perm.symm i)) * P := by
      rw [hPe]
      exact h
    rw [h', mul_inv_cancel_right]
  have hP : HeisA.ActsAs P (permLattice TwistTag.E6.perm) := by
    rw [hPe]
    exact HeisA.actsAs_diagramMap
  have hPN : P ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) := by
    rw [hPe]
    exact CFSG.LieType.AlgebraicGroups.diagramMap_mem_normalizer TwistTag.E6
  have hΦy : (canonicalRep (coxeterSystem Tag.E6) L w' * P) * entrywiseFrobGL Tag.E6 L ℓ f y *
      (canonicalRep (coxeterSystem Tag.E6) L w' * P)⁻¹ = y := by
    have h1 : canonicalRep (coxeterSystem Tag.E6) L w' * T y *
        (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = y := by
      rw [hydef, map_mul, map_mul, map_inv, hg0, hFix]
      group
    rw [hTw] at h1
    calc _ = canonicalRep (coxeterSystem Tag.E6) L w' *
          (P * entrywiseFrobGL Tag.E6 L ℓ f y * P⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ := by group
      _ = y := h1
  obtain ⟨x, hxM, hx1, hxℓ, hxy, hxn⟩ := HeisA.exists_fixed_tw (L := L) (ℓ := ℓ) (f := f) hf hpq
    D F.hw F.ha3 F.hu hy hy3 w' TwistTag.E6.perm
    (fun i j => TwistTag.cartan_perm TwistTag.E6 i j) hP hPN hPd hT hΦy
  have hxcent := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => F.a) hxM)
  have hxn' : canonicalRep (coxeterSystem Tag.E6) L w' * T x *
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = x := by
    rw [hTw]
    calc _ = (canonicalRep (coxeterSystem Tag.E6) L w' * P) * entrywiseFrobGL Tag.E6 L ℓ f x *
          (canonicalRep (coxeterSystem Tag.E6) L w' * P)⁻¹ := by group
      _ = x := hxn
  have hB₁ : g0⁻¹ * B₁ * g0 = rootDiagUnit Tag.E6 F.a := by
    rw [hg0e, hB₁e]
    exact F.hg₁
  obtain ⟨hv1, hvℓ, hvF, hvc1, hvc2⟩ := HeisA.fixed_elt_of_norm (Fr := T) hg0 hxn' hx1 hxℓ hxy
    (hxcent.2 ()) hB₁ hydef.symm
  have hg0C : g0 ∈ adjointGroup Tag.E6 L := by
    rw [hg0e]
    exact F.hg0C
  refine ⟨g0 * x * g0⁻¹, mul_mem (mul_mem hg0C hxcent.1) (inv_mem hg0C), hv1, hvℓ, ?_, ?_, ?_⟩
  · rw [hTdef] at hvF
    exact hvF
  · rw [hB₁e] at hvc1
    exact hvc1
  · rw [hB₂e] at hvc2
    exact hvc2

end CFSG.LieType.SeitzGeneration.ExcWideThree
