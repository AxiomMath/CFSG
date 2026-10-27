module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCComponentFacts

public section

namespace CFSG.RankThree.PartOne
open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
theorem orthogonal_primary_local_components_and_fixed_residue3
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p) :
    (∃ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) ∧
    ∀ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep →
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        ((isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      OrbitProduct Q (x : V ≃ₗ[K] V) Rep ∧
      FixedFactor Q (x : V ≃ₗ[K] V) ∧
      (∀ (h : K[X]) (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap), h ∈ Rep → h ≠ X - 1 →
        h ≠ reciprocalPolynomial h →
          PairedFactor Q (x : V ≃ₗ[K] V) h (irreducible_of_mem_primaryFactors hh)) ∧
      (∀ (h : K[X]) (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap), h ∈ Rep → h ≠ X - 1 →
        h = reciprocalPolynomial h →
          SelfDualFactor Q (x : V ≃ₗ[K] V) h (irreducible_of_mem_primaryFactors hh)) ∧
      (∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
        IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
        componentImage Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
        IsQuasisimple ↥(componentImage Q (x : V ≃ₗ[K] V) h) ∧
        componentImage Q (x : V ≃ₗ[K] V) h ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
        ((componentImage Q (x : V ≃ₗ[K] V) h).subgroupOf
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).Normal ∧
        IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
      ⁅inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        (componentProduct Q (x : V ≃ₗ[K] V) Rep).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))⁆ = ⊥ ∧
      ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
          ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
        ∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
          ∃ z k w : ProjOrthDerived Q, y = z * k * w ∧ Commute z k ∧ Commute z w ∧
            Commute k w ∧ z ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
            (∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), Commute z n) ∧
            z ^ p = 1 ∧ k ∈ componentProduct Q (x : V ≃ₗ[K] V) Rep ∧ k ^ p = 1 ∧
            (∃ w₀ : orthDerived Q, (QuotientGroup.mk w₀ : ProjOrthDerived Q) = w ∧ w₀ ^ p = 1 ∧
              (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) ∧
              (∀ v : V, (∀ u ∈ fixedSpace (x : V ≃ₗ[K] V), QuadraticMap.polar Q v u = 0) →
                (w₀ : V ≃ₗ[K] V) v = v) ∧
              ∀ u ∈ fixedSpace (x : V ≃ₗ[K] V),
                (w₀ : V ≃ₗ[K] V) u ∈ fixedSpace (x : V ≃ₗ[K] V) ∧
                  Q ((w₀ : V ≃ₗ[K] V) u) = Q u) ∧
            ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
                (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
              s * MulAut.conj z = MulAut.conj z * s ∧ s * MulAut.conj k = MulAut.conj k * s) := by
  classical
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨-, -, hZcard, hsimple, hnonab, -, hodd, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  obtain ⟨x₀, ⟨hx₀a, hx₀p⟩, huniq, hcent⟩ := hlift p hp (by omega) a ha
  have hxx₀ : x = x₀ := huniq x hxa hxp
  subst hxx₀
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := by
    rw [hcent]
    exact map_centralizer_eq_centralizerImage x
  refine ⟨hx.exists_orbitRepresentatives, fun Rep hRep => ?_⟩
  have hcomp : ∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
      specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
      IsQuasisimple ↥(componentImage Q (x : V ≃ₗ[K] V) h) ∧
      componentImage Q (x : V ≃ₗ[K] V) h ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      ((componentImage Q (x : V ≃ₗ[K] V) h).subgroupOf
        (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).Normal := by
    intro h hmem hne1 hm
    have hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap := hRep.1 hmem
    have hFΩ := hx.specialBlock_le_orthDerived3 hp hpne hK4 hh hne1 hm
    have hq := hx.quasisimple_specialBlock3 hp hpne hK4 hh hne1 hm
    refine ⟨hFΩ, isQuasisimple_map_projective hFΩ hq, ?_, ?_⟩
    · rw [hNeq]
      exact componentImage_le_centralizerImage
    · rw [hNeq]
      exact normal_componentImage
  have hDS : (componentProduct Q (x : V ≃ₗ[K] V) Rep).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      Subgroup.centralizer (inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))) :
          Set (MulAut (ProjOrthDerived Q))) := by
    unfold componentProduct
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hmem => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hc => ?_
    obtain ⟨-, hqJ, hJN, hJnorm⟩ := hcomp h hmem hc.1 hc.2
    have h0 := commutator_core_map_conj_eq_bot hp hB a hinj hJN hJnorm hqJ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    exact h0
  refine ⟨hNeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr s hs hrs g hg g' hg' => ?_, fun r hr => hx.disjoint_supportedBlock hRep hr, ?_⟩
    · exact hx.commute_supportedBlock (hRep.1 hr) (hRep.1 hs) (fun e => hrs e.symm)
        (hRep.ne_reciprocal hr hs hrs) hg hg'
    · exact le_antisymm (iSup₂_le fun r _ => supportedBlock_le_isometryCentralizer r)
        (hx.isometryCentralizer_le hRep)
  · exact ⟨fixedBlockEquiv hx, fun g w => rfl⟩
  · intro h hh hmem hne1 hne
    exact ⟨hx.pairedModel hh hne1 hne, hx.blockGL_bijective_paired hh hne⟩
  · intro h hh hmem hne1 hself
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      hx.exists_selfDual_hermitian hp2 hh hne1 hself
    unfold SelfDualFactor
    exact ⟨hx.selfDualModel hp2 hh hne1 hself, hx.blockGL_injective hh, d, H, hdeg, hH, hadd1,
      hadd2, hleft, hright, hsymm, fun γ => hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH γ⟩
  · intro h hmem hne1 hm
    obtain ⟨hFΩ, hqJ, hJN, hJnorm⟩ := hcomp h hmem hne1 hm
    refine ⟨hFΩ, hx.quasisimple_specialBlock3 hp hpne hK4 (hRep.1 hmem) hne1 hm, ?_, hqJ, hJN,
        hJnorm,
      isComponent_conj_subgroupOf hB a hinj hJN hJnorm hqJ⟩
    have := CFSG.LocalCores.isQuasisimple_nontrivial hqJ
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hDS
  · intro hpm y hy hyp
    have hy' := hy
    rw [hNeq] at hy'
    unfold centralizerImage at hy'
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy'
    set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
    have h1 : (ρ m) ^ p = 1 := by
      rw [← hyp]
      exact pow_orderOf_eq_one _
    have hZ2 : ∀ z : ↥(orthDerived Q), z ∈ (scalars K V).subgroupOf (orthDerived Q) →
        z ^ 2 = 1 := by
      intro z hz
      have hord : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
          Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      have hle : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ≤ 2 :=
        (Nat.le_of_dvd hpos hord).trans hZcard
      have hop : 0 < orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) :=
        orderOf_pos _
      have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
        interval_cases h : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q)))
        · exact one_dvd _
        · exact dvd_refl _
      exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h2)
    have hmp : m ^ p ∈ (scalars K V).subgroupOf (orthDerived Q) := by
      have : ρ (m ^ p) = 1 := by rw [map_pow, h1]
      exact (QuotientGroup.eq_one_iff (m ^ p)).mp this
    have hmp2 : (m ^ p) ^ 2 = 1 := hZ2 _ hmp
    set v : ↥(orthDerived Q) := m ^ (p + 1) with hvdef
    have hvp : v ^ p = 1 := by
      obtain ⟨k, hk⟩ := hp2.add_one
      have hexp : (p + 1) * p = (p * 2) * k := by rw [hk]; ring
      rw [hvdef, ← pow_mul, hexp, pow_mul, pow_mul, hmp2, one_pow]
    have hρv : ρ v = ρ m := by
      rw [hvdef, map_pow, pow_succ, h1, one_mul]
    have hvM : (v : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) := by
      have := pow_mem (Subgroup.mem_subgroupOf.mp hm) (p + 1)
      simpa [hvdef, Subgroup.coe_pow] using this
    have hvp' : (v : V ≃ₗ[K] V) ^ p = 1 := by
      have := congrArg Subtype.val hvp
      simpa using this
    obtain ⟨z₀, k₀, w₀, hv_eq, hz₀M, hz₀c, hz₀p, hk₀M, hk₀D, hk₀p, hw₀B, hw₀p, hkw⟩ :=
      hx.exists_factorization hp hp2 hRep hpm hvM hvp'
    have hΩ : ∀ g : V ≃ₗ[K] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → g ^ p = 1 →
        g ∈ orthDerived Q := by
      intro g hg hgp
      refine hodd g hg ?_
      have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · rw [h]; exact odd_one
      · rw [h]; exact hp2
    have hO : ∀ g, g ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) →
        g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg => (Subgroup.mem_inf.mp hg).1
    have hz₀Ω := hΩ z₀ (hO _ hz₀M) hz₀p
    have hk₀Ω := hΩ k₀ (hO _ hk₀M) hk₀p
    have hw₀M := supportedBlock_le_isometryCentralizer (X - 1) hw₀B
    have hw₀Ω := hΩ w₀ (hO _ hw₀M) hw₀p
    set zΩ : ↥(orthDerived Q) := ⟨z₀, hz₀Ω⟩ with hzΩ
    set kΩ : ↥(orthDerived Q) := ⟨k₀, hk₀Ω⟩ with hkΩ
    set wΩ : ↥(orthDerived Q) := ⟨w₀, hw₀Ω⟩ with hwΩ
    have hvfac : v = zΩ * kΩ * wΩ := Subtype.ext hv_eq
    have hzΩc : ∀ n : ↥(orthDerived Q), (n : V ≃ₗ[K] V) ∈ isometryCentralizer Q
        (x : V ≃ₗ[K] V) → zΩ * n = n * zΩ := fun n hn => Subtype.ext (hz₀c _ hn)
    have hzN : ρ zΩ ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
      rw [hNeq]
      exact Subgroup.mem_map.mpr ⟨zΩ, Subgroup.mem_subgroupOf.mpr hz₀M, rfl⟩
    have hzcomm : ∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        ρ zΩ * n = n * ρ zΩ := by
      intro n hn
      rw [hNeq] at hn
      obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hn
      rw [← map_mul, ← map_mul, hzΩc m' (Subgroup.mem_subgroupOf.mp hm')]
    have hzp : ρ zΩ ^ p = 1 := by
      rw [← map_pow]
      have : zΩ ^ p = 1 := Subtype.ext hz₀p
      rw [this, map_one]
    have hkD : ρ kΩ ∈ componentProduct Q (x : V ≃ₗ[K] V) Rep := by
      rw [componentProduct_eq (fun h hmem hne hm =>
        hx.specialBlock_le_orthDerived3 hp hpne hK4 (hRep.1 hmem) hne hm)]
      exact Subgroup.mem_map.mpr ⟨kΩ, Subgroup.mem_subgroupOf.mpr hk₀D, rfl⟩
    refine ⟨ρ zΩ, ρ kΩ, ρ wΩ, ?_, ?_, ?_, ?_, hzN, fun n hn => hzcomm n hn, hzp, hkD, ?_, ?_, ?_⟩
    · rw [← hρv, hvfac, map_mul, map_mul]
    · have : zΩ * kΩ = kΩ * zΩ := hzΩc kΩ hk₀M
      show ρ zΩ * ρ kΩ = ρ kΩ * ρ zΩ
      rw [← map_mul, ← map_mul, this]
    · have : zΩ * wΩ = wΩ * zΩ := hzΩc wΩ hw₀M
      show ρ zΩ * ρ wΩ = ρ wΩ * ρ zΩ
      rw [← map_mul, ← map_mul, this]
    · have : kΩ * wΩ = wΩ * kΩ := Subtype.ext hkw
      show ρ kΩ * ρ wΩ = ρ wΩ * ρ kΩ
      rw [← map_mul, ← map_mul, this]
    · rw [← map_pow]
      have : kΩ ^ p = 1 := Subtype.ext hk₀p
      rw [this, map_one]
    · refine ⟨wΩ, rfl, Subtype.ext hw₀p, hw₀B, fun u hu => ?_, fun u hu => ?_⟩
      · exact (mem_supportedBlock.mp hw₀B).2 u (hx.perp_fixed_le_others hu)
      · refine ⟨mem_fixedSpace_of_apply (supportedBlock_le_centralizer _ hw₀B) hu, ?_⟩
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hO _ hw₀M) u
    · intro s hs
      refine ⟨commute_core_conj_of_central hp hB a hinj hzN hzcomm hzp s hs, ?_⟩
      exact Subgroup.mem_centralizer_iff.mp (hDS ⟨ρ kΩ, hkD, rfl⟩) s hs
end CFSG.RankThree.PartOne