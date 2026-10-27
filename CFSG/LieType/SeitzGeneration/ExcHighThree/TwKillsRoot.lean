module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillCore

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

section Descent

theorem twisted_descent_E6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hx : x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hxF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x) (hxp : x ^ p = 1) :
    ∃ u ∈ twistedE6RootGroup K σ, baseChangeGL (algebraMap K (AlgebraicClosure K)) u = x := by
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := ℓ) (f := f) hℓ hf K hK σ.toRingHom
      hσ (AlgebraicClosure K) Fr hFr
  have hNR : ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr) =
      ⁅(⊤ : Subgroup (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)), ⊤⁆ := by
    have h1 : ⁅CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
        CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
        Subgroup.map (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr).subtype
          ⁅(⊤ : Subgroup (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hder, h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  haveI hnorm : (((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).Normal := by
    rw [hNR]
    infer_instance
  have hxR : x ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2 ⟨hx, hxF⟩
  have hPR : Subgroup.zpowers x ≤ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    Subgroup.zpowers_le.2 hxR
  have hPp : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hxp, one_zpow]
  haveI : Finite (Subgroup.zpowers x) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hxp⟩).finite_zpowers
  have hle := le_of_isPGroup_of_index_eq_pow hPR hp Nat.prime_three hp3 hk hPp
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 (hle (Subgroup.mem_zpowers x))
  exact ⟨u, hu, hux⟩

end Descent

theorem twHighKillNR_two_of_kill (hKR : ExcWideThree.TwE6KillRoot) : TwHighKillNR_two := by
  intro q K _ _ σ hK hσ E₀ hexp hcard Fr hFr v g0 hg0C hg0 hcont α hα hkill
  by_cases h3 : ringChar K = 3
  ·
    rw [h3]
    refine ⟨E₀, ?_, IsPGroup.of_card hcard, Subgroup.le_normalizer⟩
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  ·
    let A : Subgroup (ModGL TwistTag.E6.tag K) := E₀.map (twistedE6RootGroup K σ).subtype
    let D : ExcWideThree.TwLangData K σ q A :=
      { v := v, Fr := Fr, hFr := hFr, g0 := g0, hg0C := hg0C, hg0 := hg0, c := 1,
        hcI := one_mem _, hc := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
          simp only [one_mul, inv_one, mul_one]
          exact hcont y hy }
    have hkill' : ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨a, ha, hχ⟩ := hkill y hy
      exact ⟨a, by simpa [D] using ha, hχ⟩
    obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ := hKR K σ q h3 hσ hK A D α hα hkill'
    let g : ↥(twistedE6RootGroup K σ) := ⟨u, hu⟩
    have hg1 : g ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
    have hgn : g ^ (ringChar K ^ n) = 1 := Subtype.ext (by simpa using hn)
    refine ⟨Subgroup.zpowers g, ?_, ?_, ?_⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      exact hg1
    · unfold IsPGroup
      intro h
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h.2
      refine ⟨n, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hgn, one_zpow]
    · intro y hy
      have hA : (twistedE6RootGroup K σ).subtype y ∈ A := Subgroup.mem_map_of_mem _ hy
      have hyc : Commute g y := Subtype.ext (hcomm _ hA)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        have hcm : y * g ^ m = g ^ m * y := (hyc.symm.zpow_right m).eq
        have hconj : y * g ^ m * y⁻¹ = g ^ m := by
          rw [hcm, mul_assoc, mul_inv_cancel, mul_one]
        rw [hconj]
        exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) m
      · intro hh
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hh
        have hcm : y * g ^ m = g ^ m * y := (hyc.symm.zpow_right m).eq
        have hh' : h = g ^ m := by
          calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
            _ = y⁻¹ * g ^ m * y := by rw [hm]
            _ = g ^ m := by
              calc y⁻¹ * g ^ m * y = y⁻¹ * (g ^ m * y) := by group
                _ = y⁻¹ * (y * g ^ m) := by rw [hcm]
                _ = g ^ m := by group
        rw [hh']
        exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) m

theorem twE6KillRoot_proof : ExcWideThree.TwE6KillRoot := by
  intro K _ _ σ q h3 hσ hK A D α hα hkill
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push_neg at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := exists_pow_ringChar_of_card_sq K q hK hq2
  set p := ringChar K with hp_def
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) p f :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hqf]
  set M : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (MulAut.conj D.c).toMonoidHom) with hM
  have hMmem : ∀ z ∈ M, ∃ x ∈ A,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨x, hx, rfl⟩
  have hT : ∀ z ∈ M, D.g0⁻¹ * z * D.g0 ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hMmem z hz
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hsz' : D.g0 * s * D.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹) := hsz
    have hs_eq : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 = s := by
      rw [← hsz']
      group
    rw [hs_eq]
    exact hs
  have hk : ∀ z ∈ M, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * z * D.g0 ∧ rootChar a α = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hMmem z hz
    obtain ⟨a, ha, hχ⟩ := hkill x hx
    exact ⟨a, ha, hχ⟩
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    twisted_kill_core (L := AlgebraicClosure K) p f hf1 D.Fr hFrEq D.v D.g0 D.hg0C D.hg0 M hT α hα hk
  have hFrq : ∀ c : AlgebraicClosure K, D.Fr c = c ^ (p ^ f) := fun c => by rw [D.hFr c, hqf]
  obtain ⟨u₀, hu₀C, hu₀⟩ := twisted_descent_E6 (ℓ := p) (f := f) hpr hf1 K
    (hK.trans (by rw [hqf])) σ (fun c => by rw [hσ c, hqf]) D.Fr hFrq hpr h3 huLad huLF huLp
  have hcN : D.c⁻¹ ∈ Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL_le_normalizer K σ (inv_mem D.hcI)
  set u : ModGL TwistTag.E6.tag K := D.c⁻¹ * u₀ * D.c with hu
  have huC : u ∈ twistedE6RootGroup K σ := by
    have h := (Subgroup.mem_normalizer_iff.1 hcN u₀).1 hu₀C
    rw [inv_inv] at h
    exact h
  refine ⟨u, huC, ?_, ⟨1, ?_⟩, ?_⟩
  · intro h
    have hu0 : u₀ = 1 := by
      rw [hu] at h
      calc u₀ = D.c * (D.c⁻¹ * u₀ * D.c) * D.c⁻¹ := by group
        _ = 1 := by rw [h]; group
    apply huL1
    rw [← hu₀, hu0, map_one]
  · have hu₀p : u₀ ^ p = 1 := (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))) (by
      rw [map_pow, hu₀, huLp, map_one])
    rw [pow_one, hu, show D.c⁻¹ * u₀ * D.c = D.c⁻¹ * u₀ * (D.c⁻¹)⁻¹ by rw [inv_inv], conj_pow, hu₀p]
    group
  · intro x hx
    have hz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) ∈ M :=
      Subgroup.mem_map_of_mem _ hx
    have hcomm := huLc _ hz
    rw [← hu₀] at hcomm
    have key0 : u₀ * (D.c * x * D.c⁻¹) = (D.c * x * D.c⁻¹) * u₀ := by
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) u₀ (D.c * x * D.c⁻¹),
        map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) (D.c * x * D.c⁻¹) u₀]
      exact hcomm
    show u * x = x * u
    calc u * x = D.c⁻¹ * (u₀ * (D.c * x * D.c⁻¹)) * D.c := by rw [hu]; group
      _ = D.c⁻¹ * ((D.c * x * D.c⁻¹) * u₀) * D.c := by rw [key0]
      _ = x * u := by rw [hu]; group

theorem twHighKillNR_two : TwHighKillNR_two := twHighKillNR_two_of_kill twE6KillRoot_proof

end CFSG.LieType.SeitzGeneration.ExcHighThree
