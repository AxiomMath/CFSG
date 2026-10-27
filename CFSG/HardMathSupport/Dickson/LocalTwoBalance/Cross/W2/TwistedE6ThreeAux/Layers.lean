module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Frame
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularIso
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Layer

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


theorem dvd_cube_sub_one {q p : ℕ} (hq : 1 ≤ q) (h : p ∣ q ^ 2 + q + 1) : p ∣ q ^ 3 - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h1 : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
  have h2 : (m + 1) ^ 3 - 1 = m * ((m + 1) ^ 2 + (m + 1) + 1) := by omega
  rw [h2]
  exact Dvd.dvd.mul_left h m

theorem dvd_card_SL3 {F : Type} [Field F] [Finite F] {p : ℕ} (h : p ∣ Nat.card F ^ 3 - 1) :
    p ∣ Nat.card (SL(3, F)) := by
  rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_three]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _

variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}

variable (Fr) in
abbrev phi3Layer (y : ModGL Tag.E6 Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  ⁅rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr,
    rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr⁆

theorem layerA2 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    (c₀ e : twistedE6RootGroup K σ)
    (hy : frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    (hyp : orderOf (frameEmb K σ Ω g c₀ e) = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13) :
    ∃ R : Subgroup (twistedE6RootGroup K σ),
      (∀ u, u ∈ R ↔ frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e)) ∧
      R ≤ Subgroup.centralizer ({e} : Set (twistedE6RootGroup K σ)) ∧
      (∀ η : MulAut (twistedE6RootGroup K σ), η e = e → ∀ r ∈ R, η r ∈ R) ∧
      CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime p (Nat.card R) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, hcl, -, -⟩ := hcent _ hy hyp
  obtain ⟨-, hPQ, hDD, ⟨k, hkmem, ⟨eP⟩⟩, hqs, -, -, -, -⟩ := hcl hA2
  set ψ := frameEmb K σ Ω g c₀ with hψ
  have hψinj : Function.Injective ψ := frameEmb_injective c₀
  set X : Subgroup (twistedE6RootGroup K σ) := Subgroup.centralizer ({e} : Set _) with hX
  have hRmap : ⁅X, X⁆.map ψ = phi3Layer Fr (ψ e) := by
    rw [Subgroup.map_commutator, hX, map_centralizer_frameEmb]
    exact hDD.trans hPQ.symm
  have hkeq : k = RingHom.eqLocusField σ.toRingHom (RingHom.id K) := by
    ext c
    rw [hkmem c, RingHom.mem_eqLocusField, RingHom.id_apply]
  have hkcard : Nat.card k = ℓ ^ f := by
    rw [hkeq]
    exact natCard_eqLocusField hℓ hf hK hσ
  have hpP : ¬ Nat.Coprime p (Nat.card (phi3Layer Fr (ψ e))) := by
    rw [Nat.card_congr eP.toEquiv, Nat.Prime.coprime_iff_not_dvd hp, not_not]
    apply dvd_card_SL3
    rw [hkcard]
    exact dvd_cube_sub_one (Nat.one_le_pow _ _ hℓ.pos) hpq
  obtain ⟨hq, hpR, hmem⟩ := layer_transfer ψ hψinj _ _ hRmap hqs hpP
  exact ⟨⁅X, X⁆, hmem, derivedCentralizer_le e, fun η hη r hr => apply_mem_derivedCentralizer hη hr,
    hq, hpR⟩

theorem layerA2A2 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    (c₀ e : twistedE6RootGroup K σ)
    (hy : frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    (hyp : orderOf (frameEmb K σ Ω g c₀ e) = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 supportA2A2) :
    ∃ R : Subgroup (twistedE6RootGroup K σ),
      (∀ u, u ∈ R ↔ frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e)) ∧
      R ≤ Subgroup.centralizer ({e} : Set (twistedE6RootGroup K σ)) ∧
      (∀ η : MulAut (twistedE6RootGroup K σ), η e = e → ∀ r ∈ R, η r ∈ R) ∧
      CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime p (Nat.card R) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, -, hcl, -⟩ := hcent _ hy hyp
  obtain ⟨-, ⟨k₂, hk₂mem, ψ₂, -, -, hker, ⟨eP⟩⟩, -, -, -, hqs, -, hres, -, -⟩ := hcl hA2A2
  set ψ := frameEmb K σ Ω g c₀ with hψ
  have hψinj : Function.Injective ψ := frameEmb_injective c₀
  set X : Subgroup (twistedE6RootGroup K σ) := Subgroup.centralizer ({e} : Set _) with hX
  have hRmap : ((CFSG.perfectResidual X).map X.subtype).map ψ = phi3Layer Fr (ψ e) := by
    rw [map_inSubgroup_perfectResidual_of_injective ψ hψinj, hX, map_centralizer_frameEmb]
    exact hres
  have hFr2 : ∀ c, (Fr.comp Fr) c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  have hk₂eq : k₂ = RingHom.eqLocusField (Fr.comp Fr) (RingHom.id Ω) := by
    ext c
    rw [hk₂mem c, RingHom.mem_eqLocusField, hFr2, RingHom.id_apply, ← pow_mul, mul_comm f 2]
  have hk₂card : Nat.card k₂ = (ℓ ^ f) ^ 2 := by
    rw [hk₂eq, natCard_eqLocusField_frob hℓ (by omega) hFr2, ← pow_mul, mul_comm]
  have : Finite k₂ := Nat.finite_of_card_ne_zero (by
    rw [hk₂card]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hdvd : p ∣ Nat.card (SL(3, k₂)) := by
    apply dvd_card_SL3
    have h2 : ((ℓ ^ f) ^ 2) ^ 3 = ((ℓ ^ f) ^ 3) ^ 2 := by ring
    rw [hk₂card, h2]
    have h1 := dvd_cube_sub_one (Nat.one_le_pow _ _ hℓ.pos) hpq
    have h3 := Nat.sub_dvd_pow_sub_pow ((ℓ ^ f) ^ 3) 1 2
    rw [one_pow] at h3
    exact h1.trans h3
  have hpP : ¬ Nat.Coprime p (Nat.card (phi3Layer Fr (ψ e))) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ₂.ker
    rw [Nat.card_congr eP.toEquiv, hker] at h1
    rw [h1] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact h
    · exfalso
      have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  obtain ⟨hq, hpR, hmem⟩ := layer_transfer ψ hψinj _ _ hRmap hqs hpP
  exact ⟨(CFSG.perfectResidual X).map X.subtype, hmem, map_perfectResidual_le_self X,
    fun η hη r hr => apply_mem_perfectResidual_centralizer hη hr, hq, hpR⟩

theorem fixes_layer (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {H E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hH : innerAut (twistedE6RootGroup K σ) ≤ H) {z : MulAut (twistedE6RootGroup K σ)}
    (hz : z ∈ localDeltaIn p H E) (c₀ e : twistedE6RootGroup K σ)
    (hbE : MulAut.conj e ∈ E) (he1 : e ≠ 1)
    (hy : frameEmb K σ Ω g c₀ e ∈ phi3TStar K σ.toRingHom Ω Fr g)
    (hyp : orderOf (frameEmb K σ Ω g c₀ e) = p)
    (htype : (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (frameEmb K σ Ω g c₀ e) = parabolicRoots Tag.E6 supportA2A2) :
    z e = e ∧ ∀ u, frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e) → z u = u := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    KE.conj_injective_of_center_eq_bot hC
  obtain ⟨R, hRmem, hRD, hRst, hq, hpR⟩ : ∃ R : Subgroup (twistedE6RootGroup K σ),
      (∀ u, u ∈ R ↔ frameEmb K σ Ω g c₀ u ∈ phi3Layer Fr (frameEmb K σ Ω g c₀ e)) ∧
      R ≤ Subgroup.centralizer ({e} : Set (twistedE6RootGroup K σ)) ∧
      (∀ η : MulAut (twistedE6RootGroup K σ), η e = e → ∀ r ∈ R, η r ∈ R) ∧
      CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime p (Nat.card R) := by
    rcases htype with h | h
    · exact layerA2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ e hy hyp h
    · exact layerA2A2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ e hy hyp h
  obtain ⟨hze, hzR⟩ := fixes_of_mem_localDeltaIn_of_stable hp hinj hH hz hbE he1 R hRD hRst hq hpR
  exact ⟨hze, fun u hu => hzR u ((hRmem u).2 hu)⟩

theorem type_of_mem_kernel (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ phi3TStar K σ.toRingHom Ω Fr g) (hyp : orderOf y = p)
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ torusRootKernel y) :
    (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2 := by
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨htype, -, -, -, -⟩ := hcent y hy hyp
  rcases htype with h | h | h
  · rw [h] at hα
    exact absurd hα (Set.notMem_empty _)
  · exact Or.inl h
  · exact Or.inr h

theorem layerA2_eq (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ phi3TStar K σ.toRingHom Ω Fr g) (hyp : orderOf y = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 support13) :
    phi3Layer Fr y = rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr ∧
      phi3Layer Fr y ≤ phi3CStar K σ.toRingHom Ω g := by
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, hcl, -, -⟩ := hcent y hy hyp
  obtain ⟨-, hPQ, -, -, -, -, hPC, -, -⟩ := hcl hA2
  exact ⟨hPQ, hPC⟩

theorem layerA2A2_le (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ phi3TStar K σ.toRingHom Ω Fr g) (hyp : orderOf y = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) :
    phi3Layer Fr y ≤ phi3CStar K σ.toRingHom Ω g := by
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, -, hcl, -⟩ := hcent y hy hyp
  obtain ⟨-, -, -, -, -, -, hPC, -, -, -⟩ := hcl hA2A2
  exact hPC

theorem layer_le_CStar (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ phi3TStar K σ.toRingHom Ω Fr g) (hyp : orderOf y = p)
    (htype : (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) :
    phi3Layer Fr y ≤ phi3CStar K σ.toRingHom Ω g := by
  rcases htype with h | h
  · exact (layerA2_eq hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp h).2
  · exact layerA2A2_le hℓ hf hK hσ hFr hp hp3 hpq hg hgn hy hyp h

theorem mem_torus_of_commute_A2A2 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {y : ModGL Tag.E6 Ω} (hy : y ∈ phi3TStar K σ.toRingHom Ω Fr g) (hyp : orderOf y = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2)
    {h : ModGL Tag.E6 Ω} (hh : h ∈ adjointGroup Tag.E6 Ω) (hcy : h * y = y * h)
    (hcP : ∀ u ∈ phi3Layer Fr y, h * u = u * h) : h ∈ torusGroup Tag.E6 Ω := by
  obtain ⟨-, hcent, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, -, hcl, -⟩ := hcent y hy hyp
  obtain ⟨hCG, -, -, -, -, -, -, -, hcent1, -⟩ := hcl hA2A2
  have h1 : h ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel y) := by
    rw [← hCG]
    exact ⟨hh, Subgroup.mem_centralizer_singleton_iff.2 hcy⟩
  exact hcent1 ⟨h1, Subgroup.mem_centralizer_iff.2 fun u hu => (hcP u hu).symm⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
