module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.Chevalley

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_singularData_of_plane {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) :
    ∃ x ∈ A, x ≠ 1 ∧ SingularCentralizerData σ (ℓ ^ f) x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) ℓ f c = c ^ (ℓ ^ f) :=
    fun c => by rw [iterateFrobenius_def]
  have hq1 : (1 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_pow _ _ hℓ.pos
  have hd0 : 0 ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  have hpd' : p ∣ d := by
    rw [← hd] at hpd
    exact_mod_cast hpd
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, -⟩ := triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ
    (AlgebraicClosure K) _ hFr hε hd
  obtain ⟨-, hplane⟩ := threeSix_dichotomy_of_singular hℓ hf K hK σ hσ (AlgebraicClosure K) _
    hFr hε hd hgG hFg hp hp3 hpd' fun a ha hord hne x hx =>
      singularCentralizerData_threeSix hℓ hf K hK σ hσ (AlgebraicClosure K) _ hFr hε hd hgG hFg hp
        hp3 hpd' a ha hord hne x hx
  exact (hplane A hA hAcard).2


theorem pow_three_mem_range_of_fixes_singular {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hdata : SingularCentralizerData σ (ℓ ^ f) x)
    (z : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hz : ∀ r ∈ ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆, z r = r) :
    z ^ 3 ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  classical
  obtain ⟨hex, ⟨Θ, hΘ, hΘker, -⟩, -, -⟩ := triality_normal_form_full hℓ hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ⟩ := hex z
  obtain ⟨-, -, -, X, hXR, hXk⟩ := hdata
  have hfix : ∀ c ∈ Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X),
      δ c = c := by
    have hle : Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        LinearMap.trace K (RootModule TwistTag.D4.tag K)
          ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X) ≤
        (δ : K →+* K).eqLocusField (RingHom.id K) := by
      rw [Subfield.closure_le]
      rintro _ ⟨r, hr, rfl⟩
      exact fieldActor_trace_fixed σ hgδ (hz r (hXR hr))
    exact fun c hc => hle hc
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, htop, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (show 1 ≤ 3 * f by omega) hK3
  obtain ⟨j, hj⟩ : ∃ j : ℕ, fr ^ j = δ := by
    have hmem : δ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top δ
    obtain ⟨k, hk⟩ := hmem
    refine ⟨(k % (orderOf fr : ℤ)).toNat, ?_⟩
    rw [← hk, ← zpow_natCast]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have : 0 < orderOf fr := by rw [hord]; omega
      omega))]
    exact zpow_mod_orderOf fr k
  have hkcard : Nat.card (Subfield.closure
      ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        LinearMap.trace K (RootModule TwistTag.D4.tag K)
          ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X)) =
        ℓ ^ f := hXk
  have hfj : f ∣ j := by
    refine dvd_of_forall_pow_prime_pow_eq hℓ _ hkcard (fun c => ?_)
    have h1 := hfix c c.2
    rw [← hj] at h1
    have h2 : (fr ^ j) (c : K) = (c : K) ^ ℓ ^ j := ringAut_pow_apply_of_frobenius hfr j (c : K)
    exact Subtype.ext (h2.symm.trans h1)
  have hδ3 : δ ^ 3 = 1 := by
    rw [← hj, ← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (by
      rw [hord]
      obtain ⟨c, hc⟩ := hfj
      exact ⟨c, by rw [hc]; ring⟩)
  have : Θ (z ^ 3) = 1 := by
    rw [map_pow, hΘ z g δ hgδ, hδ3]
  rw [← hΘker]
  exact this

end CFSG.GH74.GLS.Stage2.Bender.Thm1
