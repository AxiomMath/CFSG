module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApPerX
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApPlane

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem ap_Z0_of_families {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hq : (ℓ ^ f) % 3 = 2) {L : Type} [Field L] [Algebra K L] [CharP L ℓ]
    [IsAlgClosed L] {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * trialityOpposition L)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L))
    {SA SB : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hSA : ∀ α ∈ SA, IsRoot TwistTag.D4.tag α) (hSAn : ∀ α ∈ SA, -α ∈ SA)
    (hSB : ∀ α ∈ SB, IsRoot TwistTag.D4.tag α) (hSBn : ∀ α ∈ SB, -α ∈ SB)
    (hfamA : ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L SA ∧
      P ≤ twistedFixedPoints (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L SA,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L SA,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
        (∀ u ∈ P, y * u = u * y) →
          y ∈ subtorusSigma (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) SA))
    (hfamB : ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L SB ∧
      P ≤ twistedFixedPoints (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L SB,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L SB,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
        (∀ u ∈ P, y * u = u * y) →
          y ∈ subtorusSigma (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) SB))
    (hkerA : ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
      rootCharKernel (τ := TwistTag.D4.tag) ![ω, ω, 1, ω] ⊆ SA ∧
        ∀ α ∈ SA, rootChar (τ := TwistTag.D4.tag)
          (![ω, ω, 1, ω] : Fin TwistTag.D4.tag.rank → Lˣ) α = 1)
    (hkerB : ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
      rootCharKernel (τ := TwistTag.D4.tag) ![1, 1, ω, 1] ⊆ SB ∧
        ∀ α ∈ SB, rootChar (τ := TwistTag.D4.tag)
          (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) α = 1)
    (hAroot : (Pi.single (2 : Fin TwistTag.D4.tag.rank) 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ SA)
    (hBroot : ∀ i : Fin TwistTag.D4.tag.rank, i ≠ 2 →
      (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ SB)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hEcard : Nat.card E = 3 ^ 2)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEψ : ∀ e ∈ E, g0⁻¹ * triEmb K σ L e * g0 ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (Z₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hZc : ∀ t ∈ Z₀, ∀ e ∈ E, t * e = e * t) (hZab : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a)
    (hZn : ∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), ∀ t ∈ Z₀,
      s * t * s⁻¹ ∈ Z₀) :
    ∀ t ∈ Z₀, t = 1 := by
  classical
  obtain ⟨ω, hω3, hω1, xA, hxA, xB, hxB, hbA, hbB⟩ := ap_plane_elements hq E hEcard hE3 hEψ
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  have hzM : trialityOpposition L ∈ monomialSubgroup TwistTag.D4.tag L :=
    trialityOpposition_mem_monomialSubgroup
  have hωne : ∀ (a : Fin TwistTag.D4.tag.rank → Lˣ), a ≠ 1 →
      ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      x ∈ E → rootDiagUnit TwistTag.D4.tag a = g0⁻¹ * triEmb K σ L x * g0 → x ≠ 1 := by
    intro a ha1 x hx hxa hx1
    apply ha1
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [hxa, hx1, map_one, mul_one, inv_mul_cancel, rootDiagUnit_one]
  have hAne : (![ω, ω, 1, ω] : Fin TwistTag.D4.tag.rank → Lˣ) ≠ 1 := fun h =>
    hω1 (by simpa using congrFun h 0)
  have hBne : (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) ≠ 1 := fun h =>
    hω1 (by simpa using congrFun h 2)
  have hxA1 : xA ≠ 1 := hωne _ hAne xA hxA hbA
  have hxB1 : xB ≠ 1 := hωne _ hBne xB hxB hbB
  have hxAp : orderOf xA = 3 := orderOf_eq_prime (hE3 xA hxA) hxA1
  have hxBp : orderOf xB = 3 := orderOf_eq_prime (hE3 xB hxB) hxB1
  have hAT : rootDiagUnit TwistTag.D4.tag (![ω, ω, 1, ω] : Fin TwistTag.D4.tag.rank → Lˣ) ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    rw [hbA]
    exact hEψ xA hxA
  have hBT : rootDiagUnit TwistTag.D4.tag (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    rw [hbB]
    exact hEψ xB hxB
  obtain ⟨hAker, hAone⟩ := hkerA ω hω3 hω1
  obtain ⟨hBker, hBone⟩ := hkerB ω hω3 hω1
  have hAcen := (rootDiagUnit_mem_centralizer_rootSpan_iff
    (![ω, ω, 1, ω] : Fin TwistTag.D4.tag.rank → Lˣ) hSA).2 hAone
  have hBcen := (rootDiagUnit_mem_centralizer_rootSpan_iff
    (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) hSB).2 hBone
  have hperxA := ap_perx hq hg0C hg0 hperf hcomm hSA hSAn hfamA hxAp hbA hAT hAcen hAker
  have hperxB := ap_perx hq hg0C hg0 hperf hcomm hSB hSBn hfamB hxBp hbB hBT hBcen hBker
  have hψ : ∀ {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
      {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      x ∈ E → x ≠ 1 →
      (∀ V : Subgroup (Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        V.Normal → Group.IsSolvable V → ∀ v ∈ V, d4QPsi (triEmb K σ L) g0 1 x v ∈
          subtorusSigma (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) S) →
      ∀ t ∈ Z₀, g0⁻¹ * triEmb K σ L t * g0 ∈ subtorusSigma (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) S := by
    intro S x hxE hx1 hperx t ht
    have hxt : t ∈ Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hZc t ht x hxE)
    let V : Subgroup (Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
      Z₀.subgroupOf _
    have hVn : V.Normal := ⟨fun y hy s => by
      have h := hZn x hxE hx1 (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) s.2
        (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (Subgroup.mem_subgroupOf.1 hy)
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact h⟩
    have hVs : Group.IsSolvable V := by
      have : IsMulCommutative V := ⟨⟨fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        exact hZab _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)⟩⟩
      infer_instance
    let tt : Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      ⟨t, hxt⟩
    have h := hperx V hVn hVs tt (Subgroup.mem_subgroupOf.2 ht)
    rwa [d4QPsi_apply, one_mul, inv_one, mul_one] at h
  intro t ht
  have h1 := hψ hxA hxA1 hperxA t ht
  have h2 := hψ hxB hxB1 hperxB t ht
  obtain ⟨hT1, hC1⟩ := Subgroup.mem_inf.1 h1
  obtain ⟨-, hC2⟩ := Subgroup.mem_inf.1 h2
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hT1).1
  rw [ha] at hC1 hC2
  have hcA := (rootDiagUnit_mem_centralizer_rootSpan_iff a hSA).1 hC1
  have hcB := (rootDiagUnit_mem_centralizer_rootSpan_iff a hSB).1 hC2
  have ha1 : a = 1 := by
    funext i
    by_cases hi : i = 2
    · subst hi
      have := hcA _ hAroot
      rwa [CTTorus.rootChar_single] at this
    · have := hcB _ (hBroot i hi)
      rwa [CTTorus.rootChar_single] at this
  have : triEmb K σ L t = 1 := by
    have h3 : g0⁻¹ * triEmb K σ L t * g0 = 1 := by rw [ha, ha1, rootDiagUnit_one]
    calc triEmb K σ L t = g0 * (g0⁻¹ * triEmb K σ L t * g0) * g0⁻¹ := by group
      _ = 1 := by rw [h3]; group
  exact triEmb_injective (this.trans (map_one _).symm)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
