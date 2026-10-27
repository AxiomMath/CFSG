module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom)

open CFSG.HardMathSupport.Foote.Coordinator (blockP)

open scoped Matrix MatrixGroups

section Certs

private lemma e8T3_diag_data {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    {Fr : L →+* L} {Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L}
    (hFr : ∀ c : L, Fr c = c ^ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    {n g0 : ModGL Tag.E8 L}
    (hT : twistedTorusOf n Φ =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom Tag.E8 L))
    {x : adjointGroup Tag.E8 K} (hx : orderOf x = p)
    (c : adjointGroup Tag.E8 K)
    (hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ)
    (b : Fin Tag.E8.rank → Lˣ)
    (hb : rootDiagUnit Tag.E8 b = g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0) :
    b ∈ fixedCharTuples (weylMatrix (e8T3We ε)) Fr ∧
      (∀ i, b i ^ p = 1) ∧ b ≠ 1 ∧
      (∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
        rootDiagUnit Tag.E8 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
          {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E8))) ∧
      (∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b) ∧
      (∀ α ∈ rootCharKernel b, e8T3W • α ∈ rootCharKernel b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E8 L) := rootDiagUnit_injective
  set h : ModGL Tag.E8 L := g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 with hhdef
  have hbh : rootDiagUnit Tag.E8 b = h := hb
  have hbT : b ∈ fixedCharTuples (weylMatrix (e8T3We ε)) Fr := by
    have hmem : rootDiagUnit Tag.E8 b ∈ twistedTorusOf n Φ := by
      rw [hbh, hhdef]
      exact hh
    rw [hT] at hmem
    obtain ⟨b', hb', hb'e⟩ := hmem
    have hbb : b' = b := rootDiagUnit_injective (by
      show rootDiagUnit Tag.E8 b' = rootDiagUnit Tag.E8 b
      exact hb'e)
    rwa [← hbb]
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (adjEmb Tag.E8 K L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (adjEmb Tag.E8 K L (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (adjEmb Tag.E8 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective (adjEmb Tag.E8 K L) adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit Tag.E8 b) = p := by rw [hbh]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (weylMatrix (e8T3We ε)) Fr hFr hp hbT hap hb1
  have hstab : ∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit Tag.E8 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E8)) := by
    intro a hap' ha1 hmem
    rw [hT] at hmem
    obtain ⟨a', ha', hae⟩ := hmem
    have haa : a' = a := hinj0 hae
    subst haa
    exact rootCharStabilizer_subset_closure_of_fixed (weylMatrix (e8T3We ε)) Fr hFr hp ha' hap'
      ha1 (fun z' hz' hzM' =>
        (dualWeylStabilizer_eq_closure_of_card z' (e8T3_dualStab_prime hp hp3 hε hpf hz' hzM')).le)
  have hSneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hSw : ∀ α ∈ rootCharKernel b, e8T3We ε • α ∈ rootCharKernel b := fun α hα =>
    ⟨CFSG.LieType.Chevalley.IsRoot.smul hα.1 _, by
      rw [← weylMatrix_mulVec, mem_fixedCharTuples_iff.1 hbT α, hα.2]
      exact map_one _⟩
  have hS3 : ∀ α ∈ rootCharKernel b, e8T3W • α ∈ rootCharKernel b :=
    stab_of_We hε hSneg hSw
  exact ⟨hbT, hap, hb1, hstab, hSneg, hS3⟩

private lemma e8T3_family_data (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    {b : Fin Tag.E8.rank → Lˣ} {u : WeylGroup Tag.E8}
    (hSu : (fun γ => u • γ) '' rootCharKernel b = parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hS3 : ∀ α ∈ rootCharKernel b, e8T3W • α ∈ rootCharKernel b) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f) (rootCharKernel b) P ∧
      P () = rootSpan Tag.E8 L (rootCharKernel b) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      (∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
        ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ∧
      (∀ y : Fin Tag.E8.rank → ℤ,
        ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) +
          ε • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) + y = 0) ∧
      rootCharKernel b = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hnC : n ∈ adjointGroup Tag.E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ y : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • y = e8T3We ε • y := fun y => by rw [hnW]
  have hrelT : ∀ y : Fin Tag.E8.rank → ℤ,
      (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • y + (u * e8T3W * u⁻¹) • y + y = 0 :=
    fun y => rel_conj e8T3W_rel u y
  have hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    intro β hβ
    rw [← hSu] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    rw [conj_smul_apply, ← hSu]
    exact ⟨e8T3W • α, hS3 α hα, rfl⟩
  have h1 : ∀ y : Fin Tag.E8.rank → ℤ,
      ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y = ε • ((u * e8T3W * u⁻¹) • y) := by
    intro y
    have := conj_smul_eq hε hnWv u⁻¹ y
    rw [hnW] at this
    simpa using this
  have hmaps : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    intro β hβ
    rw [h1 β]
    exact parabolicRoots_zsmul (hmapsT β hβ) hε
  have hrel : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • α) +
        ε • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • α) + α = 0 := by
    intro α hα
    have hee : ∀ y : Fin Tag.E8.rank → ℤ, ε • ε • y = y := fun y => by
      have : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
      rw [smul_smul, this, one_smul]
    rw [h1 α, h1 (ε • (u * e8T3W * u⁻¹) • α), smul_zsmul_E8, hee, hee]
    exact hrelT α
  have hrelFull : ∀ y : Fin Tag.E8.rank → ℤ,
      ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) +
        ε • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) + y = 0 := by
    intro y
    have hee : ∀ z : Fin Tag.E8.rank → ℤ, ε • ε • z = z := fun z => by
      have : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
      rw [smul_smul, this, one_smul]
    rw [h1 y, h1 (ε • (u * e8T3W * u⁻¹) • y), smul_zsmul_E8, hee, hee]
    exact hrelT y
  have hSeq : rootCharKernel b = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8
      (e6Nodes Tag.E8) := by
    rw [← preimage_eq_image_inv]
    exact set_eq_preimage u hSu
  obtain ⟨P, hfam, hPval, -⟩ := e8_e6_family (k := K) hE6 hf hK hε u⁻¹ n hnm hnC
    (fun α hα => by rw [hnW]; exact hmaps α hα)
    (fun α hα => by rw [hnW]; exact hrel α hα)
  have hfam' : IsSigmaFamily n (iterateFrobenius L ℓ f) (rootCharKernel b) P := by
    rw [hSeq]; exact hfam
  have hPval' : P () = rootSpan Tag.E8 L (rootCharKernel b) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hPval, ← hSeq]
  exact ⟨P, hfam', hPval', hmaps, hrelFull, hSeq⟩

lemma e8T3_embedding_data (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom Tag.E8 L))
    {x : adjointGroup Tag.E8 K} (hx : orderOf x = p) (c : adjointGroup Tag.E8 K)
    (hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (b : Fin Tag.E8.rank → Lˣ)
    (hb : rootDiagUnit Tag.E8 b = g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0)
    (hS : ∃ u : WeylGroup Tag.E8, (fun γ => u • γ) '' rootCharKernel b =
      parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∃ (ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) →* ModGL Tag.E8 L)
      (u : WeylGroup Tag.E8) (P : Unit → Subgroup (ModGL Tag.E8 L)),
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb Tag.E8 K L
        (c * (y : adjointGroup Tag.E8 K) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel b)) ∧
      (∀ y, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup Tag.E8 L) ∧
      (rootSpan Tag.E8 L (rootCharKernel b) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≤ ψ.range ∧
      ((fun γ => u • γ) '' rootCharKernel b = parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ∧
      (rootCharKernel b = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ∧
      (∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
        ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ∧
      (∀ y : Fin Tag.E8.rank → ℤ,
        ((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) +
          ε • (((u⁻¹)⁻¹ * e8T3We ε * u⁻¹) • y) + y = 0) ∧
      IsSigmaFamily n (iterateFrobenius L ℓ f) (rootCharKernel b) P ∧
      P () = rootSpan Tag.E8 L (rootCharKernel b) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ y : L, iterateFrobenius L ℓ f y = y ^ Nat.card K := fun y => by
    rw [hK, iterateFrobenius_def]
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L :=
    Units.map (entrywiseHom (iterateFrobenius L ℓ f)) with hΦdef
  obtain ⟨hbT, hap, hb1, hstab, hSneg, hS3⟩ :=
    e8T3_diag_data (ε := ε) hε hFr hp hp3 hpf hT hx c hh b hb
  obtain ⟨u, hSu⟩ := hS
  obtain ⟨P, hfam, hPval, hmaps, hrelFull, hSeq⟩ :=
    e8T3_family_data (ε := ε) hE6 hε hf hK n hnm hnW hSu hS3
  have hfamP : IsSigmaFamily n (iterateFrobenius L ℓ f) (rootCharKernel b) P := hfam
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  set ι : adjointGroup Tag.E8 K →* ModGL Tag.E8 L := adjEmb Tag.E8 K L with hιdef
  set h : ModGL Tag.E8 L := g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 with hhdef
  have hbh : rootDiagUnit Tag.E8 b = h := hb
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit Tag.E8 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := rootDiagUnit_injective (ha.trans hbh.symm)
    rw [this]
  have hle := rootSpan_le_centralizer (K := L) b (fun α hα => hα)
  have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ (rootCharKernel b)) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    · exact hh
    · have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh] at h1
      exact h1
  have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit Tag.E8 a = h →
      rootCharKernel a ⊆ rootCharKernel b := fun a ha => by
    rw [hker a ha]
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, -⟩ :=
    sigma_embedding_data_of_stab ι adjEmb_injective adjEmb_mem Φ
      (adjEmb_frobenius (iterateFrobenius L ℓ f) hFr)
      n g0 hg0C hg0 hperf hp hstab (fun α hα => hα.1) hSneg P hPfin hPq hPQ hPR hPadj
      hPnorm hPcent hx c hcS hkerZ
  refine ⟨ψ, u, P, hψinj, hψ, hψHQ, hψR, hψadj, ?_, hSu, hSeq, hmaps, hrelFull, hfamP, hPval⟩
  rw [← hPval]; exact hPψ ()

private lemma e8T3_pullback_data {K : Type} [Field K] {L : Type} [Field L]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {n : ModGL Tag.E8 L} {b : Fin Tag.E8.rank → Lˣ} {x : adjointGroup Tag.E8 K}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) →* ModGL Tag.E8 L}
    {P0 : Subgroup (ModGL Tag.E8 L)}
    (hψinj : Function.Injective ψ) (hPq : CFSG.IsQuasisimple P0)
    (hPval : P0 = rootSpan Tag.E8 L (rootCharKernel b) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hrange : P0 ≤ ψ.range)
    (hψHQ : ∀ y, ψ y ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel b))
    (hψR : ∀ y, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * n⁻¹ = ψ y)
    (hPnorm : ∀ y ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel b),
      y ∈ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      ∀ u ∈ P0, y * u * y⁻¹ ∈ P0) :
    ∃ J : Subgroup (adjointGroup Tag.E8 K),
      J = (P0.comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype ∧
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal ∧
      CFSG.IsQuasisimple J ∧ Nat.card J = Nat.card P0 := by
  classical
  have hN : (P0.comap ψ).Normal := by
    refine ⟨fun u hu d => ?_⟩
    rw [Subgroup.mem_comap] at hu ⊢
    have hd : ψ d ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel b) := hψHQ d
    have hfix : ψ d ∈ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
      mem_twistedFixedPoints.2 (hψR d)
    have h := hPnorm (ψ d) hd hfix (ψ u) hu
    simpa only [map_mul, map_mul, map_inv] using h
  have hJn : (((P0.comap ψ).map
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype).subgroupOf
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal := by
    have hcoe : ((P0.comap ψ).map
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) = P0.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype_injective
        (Subgroup.comap ψ P0)
    rw [hcoe]
    exact hN
  have hq : CFSG.IsQuasisimple (P0.comap ψ) :=
    CFSG.StandardType.E6Nonsplit.isQuasisimple_comap_of_layer ψ hψinj hrange hPq
  have hJq : CFSG.IsQuasisimple ((P0.comap ψ).map
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (P0.comap ψ)
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype_injective) hq
  have hcard : Nat.card ((P0.comap ψ).map
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype) = Nat.card P0 := by
    rw [Subgroup.card_map_of_injective
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype_injective,
      ← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq, inf_of_le_right hrange]
  exact ⟨(P0.comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype,
    rfl, Subgroup.map_subtype_le _, hJn, hJq, hcard⟩

theorem e8T3_perx_layers (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom Tag.E8 L))
    {x : adjointGroup Tag.E8 K} (hx : orderOf x = p) (c : adjointGroup Tag.E8 K)
    (hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (b : Fin Tag.E8.rank → Lˣ)
    (hb : rootDiagUnit Tag.E8 b = g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0)
    (hS : ∃ u : WeylGroup Tag.E8, (fun γ => u • γ) '' rootCharKernel b =
      parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∃ (ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) →* ModGL Tag.E8 L)
      (J : Subgroup (adjointGroup Tag.E8 K)),
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb Tag.E8 K L
        (c * (y : adjointGroup Tag.E8 K) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel b)) ∧
      (∀ y, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup Tag.E8 L) ∧
      (∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))),
        ∀ u ∈ rootSpan Tag.E8 L (rootCharKernel b) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))),
        ψ y * u * (ψ y)⁻¹ ∈ rootSpan Tag.E8 L (rootCharKernel b) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      J = ((rootSpan Tag.E8 L (rootCharKernel b) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).comap ψ).map
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype ∧
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
      (((J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal)) ∧
      CFSG.IsQuasisimple J ∧ p ∣ Nat.card J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦdef
  obtain ⟨ψ, u, P, hψinj, hψ, hψHQ, hψR, hψadj, hrange, hSu, hSeq, hmaps, hrelFull, hfam,
    hPval⟩ :=
    e8T3_embedding_data (hE6 := hE6) (hε := hε) (K := K) (hf := hf) (hK := hK)
      (hp := hp) (hp3 := hp3) (hpf := hpf) (L := L) (n := n) (hnm := hnm) (hnW := hnW)
      (g0 := g0) (hg0C := hg0C) (hg0 := hg0) (hperf := hperf) (hT := hT) (hx := hx)
      (c := c) (hh := hh) (b := b) (hb := hb) (hS := hS)
  obtain ⟨-, hPq, -, -, -, hPnorm, -⟩ := hfam
  have hrange' : P () ≤ ψ.range := by rwa [← hPval] at hrange
  obtain ⟨J, hJ, hJle, hJn, hJq, hJcard⟩ :=
    e8T3_pullback_data (P0 := P ()) hψinj (hPq ()) hPval hrange' hψHQ hψR
      (fun y hy hyf u hu => hPnorm () y hy hyf u hu)
  rw [hPval] at hJ
  have hpP6 : p ∣ Nat.card (P ()) := by
    rw [hPval]
    have h := dvd_card_rootSpan_image_inf_twistedFixedPoints_e6 hε K hf hK L hp hp3 hpf n hnm hnW
      u⁻¹ hmaps hrelFull
    rwa [← hSeq] at h
  refine ⟨ψ, J, hψinj, hψ, hψHQ, hψR, hψadj, ?_, hJ, hJle, hJn, hJq, ?_⟩
  · intro y u hu
    have hu' : u ∈ P () := by rwa [← hPval] at hu
    have h := hPnorm () (ψ y) (hψHQ y) (mem_twistedFixedPoints.2 (hψR y)) u hu'
    rwa [hPval] at h
  · rw [hJcard]
    exact hpP6

theorem det_cartanBlock_edge (a b : Fin Tag.E8.rank) (h : (a, b) ∈ e8Edges) :
    (cartanBlock Tag.E8 ({a, b} : Set (Fin Tag.E8.rank))).det = 3 := by
  simp only [e8Edges, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;>
    (obtain ⟨rfl, rfl⟩ := h <;> decide)

theorem dvd_card_rootSpan_image_inf_twistedFixedPoints_a2 {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (v : WeylGroup Tag.E8) (a b : Fin Tag.E8.rank) (hab : (a, b) ∈ e8Edges)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 ({a, b} : Set (Fin Tag.E8.rank)),
      (v⁻¹ * e8T3We ε * v) • β ∈ parabolicRoots Tag.E8 ({a, b} : Set (Fin Tag.E8.rank)))
    (hrel : ∀ x : Fin Tag.E8.rank → ℤ,
      (v⁻¹ * e8T3We ε * v) • (v⁻¹ * e8T3We ε * v) • x +
        ε • ((v⁻¹ * e8T3We ε * v) • x) + x = 0) :
    p ∣ Nat.card ↥(rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8
      ({a, b} : Set (Fin Tag.E8.rank))) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, iterateFrobenius_def]
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from
      pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFr, hK, hx]⟩⟩
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ = v⁻¹ * e8T3We ε * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV, hnW]
  have hq0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [hK, Nat.cast_pow, CharP.cast_eq_zero L ℓ, zero_pow (by omega : f ≠ 0)]
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  haveI : Nonempty ↥({a, b} : Set (Fin Tag.E8.rank)) :=
    ⟨⟨a, by simp⟩⟩
  have hdet : (cartanBlock Tag.E8 ({a, b} : Set (Fin Tag.E8.rank))).det ≠ 0 := by
    rw [det_cartanBlock_edge a b hab]
    norm_num
  have hpd : ¬ p ∣ (cartanBlock Tag.E8 ({a, b} : Set (Fin Tag.E8.rank))).det.natAbs := by
    rw [det_cartanBlock_edge a b hab]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 ({a, b} : Set (Fin Tag.E8.rank)),
      IsRoot Tag.E8 r := fun r hr => hr.1
  rcases hε with rfl | rfl
  · have hpf' : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ)) := by
        push_cast
        simpa using hpf
      exact_mod_cast h
    have hq : ((Nat.card K : L) ^ 2 + Nat.card K + 1) ≠ 0 := by
      rw [hq0]
      norm_num
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_add (τ := Tag.E8) (Ω := L)
      (by rfl : Tag.E8.symmetrizer = 1) hFr n' hn'm ({a, b} : Set (Fin Tag.E8.rank))
      (by rw [hπn']; exact hmaps) (fun x => by rw [hπn']; simpa using hrel x) hdet hp hpd hq hpf'
    have hmap := map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h
  · have hpf' : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have hcast : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
        have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
        rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
        push_cast
        ring
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ)) := by
        rw [hcast]
        simpa [sub_eq_add_neg] using hpf
      exact_mod_cast h
    have hq : ((Nat.card K : L) ^ 2 - Nat.card K + 1) ≠ 0 := by
      rw [hq0]
      norm_num
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_sub (τ := Tag.E8) (Ω := L)
      (by rfl : Tag.E8.symmetrizer = 1) hFr n' hn'm ({a, b} : Set (Fin Tag.E8.rank))
      (by rw [hπn']; exact hmaps)
      (fun x => by rw [hπn']; simpa [sub_eq_add_neg] using hrel x) hdet hp hpd hq2 hq hpf'
    have hmap := map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h

theorem isQuasisimple_a2Layer {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (hSv : ∀ α ∈ sigmaSetE8 v, e8T3We ε • α ∈ sigmaSetE8 v)
    (hSneg : ∀ α ∈ sigmaSetE8 v, -α ∈ sigmaSetE8 v) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E8 L (sigmaSetE8 v) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨P, hP, hfac, -⟩ := layer_A2 hf hk hε hq2 v n hnm hnC hnW hSv hSneg
  rw [← hP]
  exact hfac.quasi ()


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
