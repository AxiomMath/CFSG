module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUnitaryElt
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.E6FourFamily
public import CFSG.RankThree.PartOne.KE.E6FourKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (exists_mem_unitarySet_orderOf)
open scoped Matrix MatrixGroups

section PerXOdd

theorem e6_four_perx_odd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E6 K L (c * (y : adjointGroup .E6 K) * c⁻¹) * g0) ∧
      ∀ b : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 →
        (rootCharKernel b = ∅ → ∀ y, ψ y ∈ torusGroup .E6 L) ∧
        ((rootCharKernel b).Nonempty →
          ∃ Pt : Subgroup (ModGL .E6 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
            (∀ y ∈ ψ.range, (∀ u ∈ Pt, y * u = u * y) → y ∈ torusGroup .E6 L) ∧
            ∃ Y₀ ∈ Pt, orderOf Y₀ = p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓ : ℓ.Prime := Fact.out
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
  set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E6 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .E6 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hstab : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit .E6 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup .E6)) := by
    intro a hap' ha1 haT
    rw [hT] at haT
    obtain ⟨a', ha', haa⟩ := haT
    have : a' = a := hinj0 haa
    subst this
    exact e6Four_stab_of_fixed Fr hFr hp hp3 hord hΦ ha' hap' ha1
  have core : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .E6 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .E6 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .E6 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .E6 L) →
        (∀ i, ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L,
          Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .E6 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .E6 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), V.Normal →
            Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) b hsub
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data_of_stab ι adjEmb_injective adjEmb_mem Φ
      (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj
      hPnorm hPcent hx c hcS hkerZ
  have hkd := e6Four_kernel_of_fixed Fr hFr hp hp3 hΦ hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hunit⟩
  ·
    have hspan : rootSpan .E6 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, -, hψV⟩ := core (rootCharKernel b) rfl
      (fun α hα => hα.1) hrootneg (ι' := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun _ y => ?_, fun hne => ?_⟩⟩
    · have h1 := hψHQ y
      rw [hspan, sup_bot_eq] at h1
      exact h1
    · exfalso
      rw [hker b' hb', hA] at hne
      exact Set.not_nonempty_empty hne
  ·
    obtain ⟨P, hP, hP1, ⟨h₀, hh₀⟩, ⟨H, hH⟩⟩ :=
      e6_four_family hℓ hf (k := K) hK Fr hFr' n hnm hnW v hunit
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core (sigmaSetE6A3 v) hSeq
      (sigmaSetE6A3_isRoot v) (sigmaSetE6A3_neg v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun hem => ?_, fun _ => ?_⟩⟩
    · exfalso
      rw [hker b' hb', hSeq] at hem
      have hmem : sigmaRootE6A3 v 0 1 ∈ sigmaSetE6A3 v :=
        mem_sigmaSetE6A3_iff.2 ⟨0, 1, by decide, rfl⟩
      rw [hem] at hmem
      exact hmem
    · have hcomm : ⁅ψ.range, ψ.range⁆ = P () := by
        refine commutator_range_eq_of_family ψ (H := torusGroup .E6 L)
          (Q := rootSpan .E6 L (sigmaSetE6A3 v)) (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
          (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
        · exact torusGroup_le_normalizer_rootSpan (sigmaSetE6A3_isRoot v)
        · intro a ha a' ha'
          obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
          exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
        · exact Subgroup.isPerfect_iff.1 (hPq ()).1
      refine ⟨P (), hPq (), hcomm, ?_, ?_⟩
      · rintro y ⟨y0, rfl⟩ hy
        have h3 := hPcent (ψ y0) (hψHQ y0) (mem_twistedFixedPoints.2 (hψR y0))
          (fun i u hu => hy u hu)
        exact (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf _ _ _ h3)).1
      ·
        have hpq' : p ∣ (ℓ ^ f) ^ 2 + 1 := by
          have h0 : ((Nat.card K ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
            push_cast
            exact hΦ
          rw [hK] at h0
          exact (ZMod.natCast_eq_zero_iff _ p).1 h0
        obtain ⟨Y, hYU, hYo⟩ := exists_mem_unitarySet_orderOf (Ω := L) hf hp hpq'
        let Y' : SL(4, L) := ⟨(Y : Matrix (Fin 4) (Fin 4) L), hYU.2.1⟩
        have hY' : Matrix.SpecialLinearGroup.toGL Y' = Y := Units.ext rfl
        let Z : SL(4, L) := H * Y' * H⁻¹
        have hZ : Matrix.SpecialLinearGroup.toGL Z =
            Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hY']
        refine ⟨rhoSigmaE6A3 L v Z, hH Z ⟨Y, by rwa [hK], hZ⟩, ?_⟩
        rw [orderOf_injective _ (rhoSigmaE6A3_injective v) Z,
          ← orderOf_injective (Matrix.SpecialLinearGroup.toGL : SL(4, L) →* GL (Fin 4) L)
            Matrix.SpecialLinearGroup.toGL_injective Z, hZ,
          show Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹ =
            (MulAut.conj (Matrix.SpecialLinearGroup.toGL H)).toMonoidHom Y from rfl,
          orderOf_injective _ (MulAut.conj (Matrix.SpecialLinearGroup.toGL H)).injective Y, hYo]


end PerXOdd

end CFSG.RankThree.PartOne.KE
