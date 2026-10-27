module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCLocalComponents
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCInnerPlaneDefs

public section

namespace CFSG.RankThree.PartOne
open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
theorem orthogonal_inner_plane_local_core_centralization3
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (_hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1)
    (x : orthDerived Q) (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a)
    (hxp : orderOf x = p) :
    (FixedLayerListed Q (x : V ≃ₗ[K] V) →
      supportedFixedDerived Q (x : V ≃ₗ[K] V) ≤ orthDerived Q ∧
      ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), 1 ≤ n ∧ n ≤ 2 ∧
        (⨆ i, C i) = fixedComponentImage Q (x : V ≃ₗ[K] V) ∧
        (∀ i, C i ≠ ⊥ ∧ CFSG.IsQuasisimple ↥(C i) ∧
          C i ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
          ((C i).subgroupOf (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
          IsComponent (((C i).map
            (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
            (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
        ∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) ∧
    (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 2 → ∀ w₀ : orthDerived Q, w₀ ^ p = 1 →
        (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) →
        (∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          (QuotientGroup.mk w₀ : ProjOrthDerived Q) * n = n * QuotientGroup.mk w₀) ∧
        (QuotientGroup.mk w₀ : ProjOrthDerived Q) ∈
          Assembly.pCoreOf p (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) ∧
    (∀ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep →
      (∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
        componentImage Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(componentImage Q (x : V ≃ₗ[K] V) h) ∧
        IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
      (((componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V)).subgroupOf
        (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).Normal) ∧
      ⁅inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        (componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V)).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))⁆ = ⊥ ∧
      ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
          ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
        ∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
          ∃ z k : ProjOrthDerived Q, y = z * k ∧ Commute z k ∧
            z ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
            (∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), Commute z n) ∧
            z ^ p = 1 ∧
            k ∈ (componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔
              fixedLayerImage Q (x : V ≃ₗ[K] V)) ∧ k ^ p = 1)) ∧
    ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
      (∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
        ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
          s * MulAut.conj y = MulAut.conj y * s) ∧
      ∀ g ∈ A, ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        s * MulAut.conj g = MulAut.conj g * s) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have ha : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue3 hQ hT hp hpne hK4 hpl B hB a ha x hxa hxp
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set S := inSubgroup (aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))) with hS
  have hNeq' : N = centralizerImage Q xe := (hmain Rep0 hRep0).1
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  have hwpow : ∀ w₀ : orthDerived Q, w₀ ^ p = 1 → (w₀ : V ≃ₗ[K] V) ^ p = 1 := fun w₀ hw₀ => by
    have := congrArg Subtype.val hw₀
    simpa using this
  have hwN : ∀ w₀ : orthDerived Q, (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q xe (X - 1) →
      ρ w₀ ∈ N := fun w₀ hw₀B => by
    rw [hNeq']
    exact Subgroup.mem_map.mpr ⟨w₀, Subgroup.mem_subgroupOf.mpr
      (supportedBlock_le_isometryCentralizer _ hw₀B), rfl⟩
  have hJN : fixedComponentImage Q xe ≤ N := by
    rw [hNeq']
    exact fixedComponentImage_le_centralizerImage
  have hbin : finrank K (fixedSpace xe) = 2 → ∀ w₀ : orthDerived Q, w₀ ^ p = 1 →
      (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q xe (X - 1) →
      ∀ n ∈ N, ρ w₀ * n = n * ρ w₀ := by
    intro hdim w₀ hw₀p hw₀B n hn
    rw [hNeq'] at hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have hRep : IsOrbitRepresentatives xe Rep0 := hRep0
    have := hx.commute_fixed_of_mem_orthDerived hp2 hQ hRep hdim
      (Subgroup.mem_subgroupOf.mp hm) m.2 hw₀B (hwpow w₀ hw₀p)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this.symm
  have hlayer : FixedLayerListed Q xe → ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, C i) = fixedComponentImage Q xe ∧
      (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ N ∧ ((C i).subgroupOf N).IsSubnormal) ∧
      (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) := by
    intro hlist
    obtain ⟨n, C, hn1, hn2, hsup, hC, hcomm, -⟩ := hx.fixedLayer_data hlist
    refine ⟨n, C, hn1, hn2, hsup, fun i => ?_, hcomm⟩
    rw [hNeq']
    exact hC i
  have hSlayer : FixedLayerListed Q xe → ∀ s ∈ S, ∀ u ∈ fixedComponentImage Q xe,
      s * MulAut.conj u = MulAut.conj u * s := by
    intro hlist s hs u hu
    obtain ⟨n, C, -, -, hsup, hC, -⟩ := hlayer hlist
    have hcent : (fixedComponentImage Q xe).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        Subgroup.centralizer (S : Set (MulAut (ProjOrthDerived Q))) := by
      rw [← hsup, Subgroup.map_iSup]
      refine iSup_le fun i => ?_
      have h0 := commutator_core_map_conj_eq_bot_of_subnormal hp hB a hinj (hC i).2.1
        (hC i).2.2 (hC i).1
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
      exact h0
    exact Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem _ hu)) s hs
  have hsw : ∀ w₀ : orthDerived Q, w₀ ^ p = 1 → (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q xe (X - 1) →
      ∀ s ∈ S, s * MulAut.conj (ρ w₀) = MulAut.conj (ρ w₀) * s := by
    intro w₀ hw₀p hw₀B s hs
    rcases hx.residue_cases3 hp hpne hK4 hw₀B (hwpow w₀ hw₀p) with h1 | h2 | ⟨hlist, hmem⟩
    · have : w₀ = 1 := Subtype.ext h1
      rw [this, map_one, map_one, one_mul, mul_one]
    · exact commute_core_conj_of_central hp hB a hinj (hwN w₀ hw₀B)
        (hbin h2 w₀ hw₀p hw₀B) (by rw [← map_pow, hw₀p, map_one]) s hs
    · exact hSlayer hlist s hs (ρ w₀) (Subgroup.mem_map.mpr
        ⟨w₀, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩)
  refine ⟨fun hlist => ⟨hx.supportedFixedDerived_le_orthDerived, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨n, C, hn1, hn2, hsup, hC, hcomm⟩ := hlayer hlist
    refine ⟨n, C, hn1, hn2, hsup, fun i => ⟨ne_bot_of_isQuasisimple (hC i).1, (hC i).1,
      (hC i).2.1, (hC i).2.2, ?_⟩, hcomm⟩
    exact isComponent_conj_subgroupOf_of_subnormal hB a hinj (hC i).2.1 (hC i).2.2 (hC i).1
  · intro hdim w₀ hw₀p hw₀B
    refine ⟨hbin hdim w₀ hw₀p hw₀B, ?_⟩
    refine mem_pCoreOf_of_central (hwN w₀ hw₀B) (hbin hdim w₀ hw₀p hw₀B) ?_
    show ρ w₀ ^ p = 1
    rw [← map_pow, hw₀p, map_one]
  · intro Rep hRep
    obtain ⟨-, -, -, -, -, hspec, hSD, hfac⟩ := hmain Rep hRep
    have hDle : componentProduct Q xe Rep ⊔ fixedLayerImage Q xe ≤ N := by
      rw [hNeq']
      exact sup_le (componentProduct_le_centralizerImage Rep) fixedLayerImage_le_centralizerImage
    refine ⟨fun h hh hne hm => ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, -, h3, h4, -, -, h7⟩ := hspec h hh hne hm
      exact ⟨h1, h3, h4, h7⟩
    · rw [hNeq']
      exact normal_subgroupOf_sup (componentProduct_le_centralizerImage Rep)
        fixedLayerImage_le_centralizerImage (normal_componentProduct Rep) hx.normal_fixedLayerImage
    · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hSD
        exact hSD
      · unfold fixedLayerImage
        split_ifs with hlist
        · rintro _ ⟨u, hu, rfl⟩
          exact Subgroup.mem_centralizer_iff.mpr fun s hs => hSlayer hlist s hs u hu
        · rw [Subgroup.map_bot]
          exact bot_le
    · intro hpm y hy hyp
      obtain ⟨z, k, w, hyzkw, hzk, hzw, hkw, hzN, hzc, hzp, hkD, hkp, ⟨w₀, hw₀ρ, hw₀p, hw₀B, -, -⟩,
        -⟩ := hfac hpm y hy hyp
      have hwp : w ^ p = 1 := by
        rw [← hw₀ρ]
        show ρ w₀ ^ p = 1
        rw [← map_pow, hw₀p, map_one]
      rcases hx.residue_cases3 hp hpne hK4 hw₀B (hwpow w₀ hw₀p) with h1 | h2 | ⟨hlist, hmem⟩
      · have hw1 : w = 1 := by
          rw [← hw₀ρ, show w₀ = 1 from Subtype.ext h1]
          rfl
        exact ⟨z, k, by rw [hyzkw, hw1, mul_one], hzk, hzN, hzc, hzp,
          Subgroup.mem_sup_left hkD, hkp⟩
      · have hwc := hbin h2 w₀ hw₀p hw₀B
        have hwN' : w ∈ N := by rw [← hw₀ρ]; exact hwN w₀ hw₀B
        have hwc' : ∀ n ∈ N, Commute w n := fun n hn => by
          rw [← hw₀ρ]; exact hwc n hn
        refine ⟨z * w, k, ?_, hzk.mul_left hkw.symm, mul_mem hzN hwN',
          fun n hn => (hzc n hn).mul_left (hwc' n hn), ?_, Subgroup.mem_sup_left hkD, hkp⟩
        · rw [hyzkw, mul_assoc, mul_assoc, hkw.eq]
        · rw [hzw.mul_pow, hzp, hwp, one_mul]
      · have hwJ : w ∈ fixedLayerImage Q xe := by
          rw [fixedLayerImage_of_listed hlist]
          exact Subgroup.mem_map.mpr ⟨w₀, Subgroup.mem_subgroupOf.mpr hmem, hw₀ρ⟩
        refine ⟨z, k * w, by rw [hyzkw, mul_assoc], hzk.mul_right hzw, hzN, hzc, hzp,
          mul_mem (Subgroup.mem_sup_left hkD) (Subgroup.mem_sup_right hwJ), ?_⟩
        rw [hkw.mul_pow, hkp, hwp, one_mul]
  · intro hpm
    obtain ⟨hy, hAS⟩ : (∀ y ∈ N, orderOf y = p → ∀ s ∈ S, s * MulAut.conj y = MulAut.conj y * s) ∧
        ∀ g ∈ A, ∀ s ∈ S, s * MulAut.conj g = MulAut.conj g * s := by
      have hy : ∀ y ∈ N, orderOf y = p → ∀ s ∈ S, s * MulAut.conj y = MulAut.conj y * s := by
        intro y hy hyp s hs
        obtain ⟨-, -, -, -, -, -, -, hfac⟩ := hmain Rep0 hRep0
        obtain ⟨z, k, w, hyzkw, -, -, -, hzN, hzc, hzp, hkD, hkp, ⟨w₀, hw₀ρ, hw₀p, hw₀B, -, -⟩,
          hSzk⟩ := hfac hpm y hy hyp
        have hsw' : s * MulAut.conj w = MulAut.conj w * s := by
          rw [← hw₀ρ]
          exact hsw w₀ hw₀p hw₀B s hs
        obtain ⟨hsz, hsk⟩ := hSzk s hs
        rw [hyzkw, map_mul, map_mul]
        calc s * (MulAut.conj z * MulAut.conj k * MulAut.conj w)
            = (s * MulAut.conj z) * MulAut.conj k * MulAut.conj w := by simp only [mul_assoc]
          _ = MulAut.conj z * (s * MulAut.conj k) * MulAut.conj w := by
            rw [hsz]; simp only [mul_assoc]
          _ = MulAut.conj z * (MulAut.conj k * s) * MulAut.conj w := by rw [hsk]
          _ = MulAut.conj z * MulAut.conj k * (s * MulAut.conj w) := by simp only [mul_assoc]
          _ = MulAut.conj z * MulAut.conj k * (MulAut.conj w * s) := by rw [hsw']
          _ = MulAut.conj z * MulAut.conj k * MulAut.conj w * s := by simp only [mul_assoc]
      refine ⟨hy, fun g hg s hs => ?_⟩
      by_cases hg1 : g = 1
      · rw [hg1, map_one, mul_one, one_mul]
      · have hgN : g ∈ N := by
          have := hA.1
          rw [hN, Subgroup.mem_centralizer_singleton_iff]
          have := mul_comm' (⟨g, hg⟩ : ↥A) ⟨a, haA⟩
          exact congrArg Subtype.val this
        exact hy g hgN (orderOf_eq_prime (hA.2 g hg) hg1) s hs
    exact ⟨hy, hAS⟩
end CFSG.RankThree.PartOne