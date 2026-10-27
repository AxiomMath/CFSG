module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311g2
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.HardMathSupport.Seitz.TrialityEven.RouteCModel
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreThree
public import CFSG.HardMathSupport.Seitz.Proving.OrderThreeSLConj
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.StandardPairFacts
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.HardMathSupport.Seitz.TrialityEven.FrameLiftEven
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311k

open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem conj_mem_rClosure {E : Subgroup G} {r : ℕ} {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G))
    {h : G} (hh : h ∈ Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1}) :
    y * h * y⁻¹ ∈ Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
  set S := {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hS
  have hle : (Subgroup.closure S).map (MulAut.conj y).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
    refine Subgroup.subset_closure ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy x).1 hx, ?_, ?_, n, ?_⟩
    · intro h1
      apply hx1
      have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
      rw [this, h1]
      group
    · have := hkx.map (MulAut.conj y).toMonoidHom
      simpa [MulAut.conj_apply] using this
    · show (MulAut.conj y).toMonoidHom k ^ (r ^ n) = 1
      rw [← map_pow, hn, map_one]
  exact hle ⟨h, hh, rfl⟩

theorem normalizer_le_normalizer_rClosure (E : Subgroup G) (r : ℕ) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer
      ((Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_rClosure hy hh, fun hh => ?_⟩
  have h1 := conj_mem_rClosure (Subgroup.inv_mem _ hy) hh
  have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
  rwa [e] at h1

theorem le_normalizer_of_frattini [Finite G] {p : ℕ} [Fact p.Prime] {H X : Subgroup G} (S : Sylow p G)
    (hSX : (S : Subgroup G) ≤ X) (hSH : (S : Subgroup G) ≤ Subgroup.normalizer (H : Set G))
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hR : ⁅X, X⁆ ≤ Subgroup.normalizer (H : Set G)) :
    X ≤ Subgroup.normalizer (H : Set G) := by
  classical
  set M : Subgroup G := ⁅X, X⁆ ⊔ (S : Subgroup G) with hM
  have hSM : (S : Subgroup G) ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (H : Set G) := sup_le hR hSH
  intro g hg
  have hgSM : ((g • S : Sylow p G) : Subgroup G) ≤ M := by
    intro y hy
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 hy
    have e : (MulAut.conj g) • s = ⁅g, s⁆ * s := by
      rw [MulAut.smul_def, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hg (hSX hs))) (hSM hs)
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (S.subtype hSM) ((g • S).subtype hgSM)
  rw [Sylow.smul_subtype] at hm
  have hm' : (m : G) • S = g • S := Sylow.subtype_injective hm
  have hn : (m : G)⁻¹ * g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    have h1 : ((m : G)⁻¹ * g) • S = S := by rw [mul_smul, ← hm', inv_smul_smul]
    exact Sylow.smul_eq_iff_mem_normalizer.1 h1
  have h2 := Subgroup.mul_mem _ (hMN m.2) (hNS hn)
  rwa [mul_inv_cancel_left] at h2

theorem rClosure_eq_top_of_frattini [Finite G] [IsSimpleGroup G] {p r : ℕ} [Fact p.Prime] (E : Subgroup G)
    (S : Sylow p G) (hES : E ≤ S) (hSab : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a)
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (E : Set G))
    (h0 : Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤)
    (hR : ∀ x ∈ E, x ≠ 1 → ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ ≤
      Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1})
    (hne : ∃ x ∈ E, x ≠ 1 ∧
      ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆ ≠ ⊥) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  set H := Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hH
  have hNE := normalizer_le_normalizer_rClosure E r
  rw [← hH] at hNE
  have hSE : (S : Subgroup G) ≤ Subgroup.normalizer (E : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (E : Set G))
    intro s hs e he
    exact hSab e (hES he) s hs
  have hC : ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (H : Set G) := by
    intro x hx hx1
    refine le_normalizer_of_frattini S ?_ (hSE.trans hNE) (hNS.trans hNE)
      ((hR x hx hx1).trans Subgroup.le_normalizer)
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSab s hs x (hES hx)
  have htop : Subgroup.normalizer (H : Set G) = ⊤ := by
    rw [eq_top_iff, ← h0, Subgroup.closure_le]
    rintro k ⟨x, hx, hx1, hkx⟩
    exact hC x hx hx1 (Subgroup.mem_centralizer_singleton_iff.2 hkx)
  have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases hHn.eq_bot_or_eq_top with hbot | hh
  · exfalso
    obtain ⟨x, hx, hx1, hR1⟩ := hne
    apply hR1
    rw [eq_bot_iff, ← hbot]
    exact hR x hx hx1
  · exact hh

end Abstract

section ThreeSix

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


theorem exists_tsIota_rElement_ne_one (Ω : Type) [Field Ω] {ℓ : ℕ} [CharP Ω ℓ] (k : Subfield Ω) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) k,
      tsIota Ω (Matrix.SpecialLinearGroup.map k.subtype A) ≠ 1 ∧
        tsIota Ω (Matrix.SpecialLinearGroup.map k.subtype A) ^ ℓ = 1 := by
  set A : Matrix.SpecialLinearGroup (Fin 2) k := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hA
  set w := Matrix.SpecialLinearGroup.map k.subtype A with hw
  have hwval : (w : Matrix (Fin 2) (Fin 2) Ω) = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hpow : ∀ n : ℕ, ((w ^ n : Matrix.SpecialLinearGroup (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) =
      !![1, (n : Ω); 0, 1] := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, hwval]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hwℓ : w ^ ℓ = 1 := by
    refine Subtype.ext ?_
    rw [hpow, CharP.cast_eq_zero, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨A, ?_, ?_⟩
  · intro h
    have h1 : d4A2Iota Ω w = 1 := Subtype.ext h
    have h2 := d4A2Rep_d4A2Iota Ω w
    rw [h1, map_one] at h2
    have h3 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) Ω =>
      (B : Matrix (Fin 3) (Fin 3) Ω) 0 1) h2
    simp only [Matrix.SpecialLinearGroup.coe_one, coe_sl2BlockSL3, sl2Block, hwval] at h3
    simp at h3
  · show ((d4A2Iota Ω w : subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω) ^ ℓ = 1
    rw [← Subgroup.coe_pow, ← map_pow, hwℓ, map_one, Subgroup.coe_one]

theorem derived_centralizer_le_closure_rElements_threeSix {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ d) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p) (hne : (survivingRoots a).Nonempty)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ≤
      Subgroup.closure {k | k ∈ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
        k ^ ℓ = 1} ∧
    ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ≠ ⊥ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  obtain ⟨-, -, -, hall⟩ := triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨-, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, -, -, -, -, -, -, hsurv, -, -⟩ := hp' p hp hp3 hpd
  have ha1 : rootDiagUnit TwistTag.D4.tag a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hTp : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p :=
    ⟨ha, by rw [← hord]; exact pow_orderOf_eq_one _⟩
  obtain ⟨i, hi⟩ : ∃ i, survivingRoots a = trialitySigma i := by
    by_contra hnot
    push Not at hnot
    have hnoline : ∀ i, rootDiagUnit TwistTag.D4.tag a ∉ threeSixLine Ω Fr ε p i :=
      fun i hi => hnot i ((hsurv a hTp ha1).1 i hi)
    exact hne.ne_empty ((hsurv a hTp ha1).2 hnoline)
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4, (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  obtain ⟨-, -, hR, -, -, hq, hZ, -, -, -, z, -, X, hXR, -, hXs, -⟩ :=
    triality_three_six_singular_fixed_centralizers hℓ hf K hK σ hσ Ω Fr hFr hε hd g hgG hFg hp hp3 hpd a
      ha hord v hv x hx
  rw [hR]
  set R := threeSixSingularR Ω K σ Fr ε v g with hRdef
  have hRC : R ≤ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [← hR, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂) (Subgroup.inv_mem _ hg₁))
      (Subgroup.inv_mem _ hg₂)
  obtain ⟨A, hA1, hAℓ⟩ := exists_tsIota_rElement_ne_one Ω (ℓ := ℓ) (RingHom.eqLocusField Fr (RingHom.id Ω))
  obtain ⟨y, hyX, hy⟩ := hXs A
  have hyR : y ∈ R := hXR hyX
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, map_one] at hy
    apply hA1
    have e : tsIota Ω (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) =
        z⁻¹ * (z * tsIota Ω (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id Ω)).subtype A) *
          z⁻¹) * z := by group
    rw [e, ← hy]
    group
  have hyℓ : y ^ ℓ = 1 := by
    apply threeSixEmb_injective K Ω σ
    rw [map_pow, hy, map_one, conj_pow, hAℓ]
    group
  set N : Subgroup R := Subgroup.normalClosure {u : R | u ^ ℓ = 1} with hN
  have hyℓ' : (⟨y, hyR⟩ : R) ^ ℓ = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hyℓ)
  have hyN : (⟨y, hyR⟩ : R) ∈ N := Subgroup.subset_normalClosure hyℓ'
  have hNc : ¬ N ≤ Subgroup.center R := by
    intro hc
    have hyc := hc hyN
    have hy1' : (⟨y, hyR⟩ : R) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    have hord' : orderOf (⟨y, hyR⟩ : R) = ℓ := orderOf_eq_prime hyℓ' hy1'
    have hdvd : ℓ ∣ Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) := by
      rw [← hZ, ← hord']
      exact Subgroup.orderOf_dvd_natCard _ hyc
    have hdvdZ : (ℓ : ℤ) ∣ (Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) : ℤ) := Int.natCast_dvd_natCast.2 hdvd
    have h3 : ℓ ∣ 3 := by
      have := hdvdZ.trans (Int.gcd_dvd_left ..)
      exact_mod_cast this
    have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3
    have h3' : (ℓ : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε := hdvdZ.trans (Int.gcd_dvd_right ..)
    have h3f : (ℓ : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) := by
      push_cast
      exact dvd_pow_self _ (by omega)
    have hε3 : (ℓ : ℤ) ∣ ε := by
      have := dvd_sub h3f h3'
      simpa using this
    rw [hℓ3] at hε3
    rcases hε with rfl | rfl <;> norm_num at hε3
  have htop : N = ⊤ := by
    rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.normal_le_center_or_eq_top hq.1 hq.2.1 N with hc | htop
    · exact absurd hc hNc
    · exact htop
  refine ⟨fun r hr => ?_, ?_⟩
  · have hrN : (⟨r, hr⟩ : R) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    have hle : N ≤ Subgroup.closure {u : R | u ^ ℓ = 1} := by
      rw [hN, Subgroup.normalClosure]
      refine Subgroup.closure_mono ?_
      intro u hu
      obtain ⟨b, hb, hbu⟩ := Group.mem_conjugatesOfSet_iff.1 hu
      obtain ⟨c, rfl⟩ := isConj_iff.1 hbu
      show (c * b * c⁻¹) ^ ℓ = 1
      rw [conj_pow, show b ^ ℓ = 1 from hb]
      group
    have h1 := Subgroup.mem_map_of_mem R.subtype (hle hrN)
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hRC u.2, ?_⟩
    rw [← map_pow, show u ^ ℓ = 1 from hu, map_one]
  · intro hbot
    apply hy1
    have : y ∈ (⊥ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hbot ▸ hyR
    exact (Subgroup.mem_bot).1 this

theorem rClosure_eq_top_threeSix {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (h0 : ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
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
  set Ω := AlgebraicClosure K with hΩ
  set Fr := iterateFrobenius Ω ℓ f with hFrdef
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨-, ⟨iso⟩, hp'⟩ := hall g hgG hFg
  obtain ⟨⟨S, hST⟩, -, -, -, -, -, -, -, hreg, hplanes⟩ := hp' p hp hp3 hpd'
  obtain ⟨c, hEc, ⟨M, hME, hMcard, hMsing⟩, -⟩ := hplanes E hE hcard
  set T := threeSixFixedTorus K Ω σ Fr ε g with hT
  set F := threeSixFixedTorsion K Ω σ Fr ε p g with hF
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have h1 : iso (⟨a, ha⟩ * ⟨b, hb⟩) = iso (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (iso.injective h1)
  have hFT : F ≤ T := Subgroup.comap_mono (Subgroup.map_mono fun h hh => hh.1)
  have hTF : ∀ y ∈ T, y ^ p = 1 → y ∈ F := by
    intro y hy hyp
    obtain ⟨u, hu, huy⟩ := hy
    refine ⟨u, ⟨hu, ?_⟩, huy⟩
    have h1 : (MulAut.conj g).toMonoidHom (u ^ p) = 1 := by
      rw [map_pow, huy, ← map_pow, hyp, map_one]
    have h2 := (MulAut.conj g).injective (h1.trans (map_one _).symm)
    exact h2
  haveI : CFSG.IsElementaryAbelian p E := hE
  have hFea : CFSG.IsElementaryAbelian p F := by
    rw [← hEc]
    exact CFSG.IsElementaryAbelian.map (MulAut.conj c).toMonoidHom
  have hFcard : Nat.card F = p ^ 2 := by
    rw [← hEc, Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard]
  have hTN : T ≤ Subgroup.normalizer ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro t ht s hs
    exact hTcomm s (hST hs) t ht
  have hFS : F ≤ (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have hFp : IsPGroup p F := IsPGroup.of_card (n := 2) hFcard
    have hQ := IsPGroup.to_sup_of_normal_left' S.isPGroup' hFp (hFT.trans hTN)
    have := S.is_maximal' hQ le_sup_left
    rw [← this]
    exact le_sup_right
  have hNSF : Subgroup.normalizer ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
      Subgroup.normalizer (F : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have key : ∀ n ∈ Subgroup.normalizer ((S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        ∀ y ∈ F, n * y * n⁻¹ ∈ F := by
      intro n hn y hy
      have hyS : y ∈ (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hFS hy
      have h1 : n * y * n⁻¹ ∈ (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := (Subgroup.mem_normalizer_iff.1 hn y).1 hyS
      refine hTF _ (hST h1) ?_
      rw [conj_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := F) y hy]
      group
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key n hn y, fun hy => ?_⟩
    have h1 := key n⁻¹ (Subgroup.inv_mem _ hn) _ hy
    have e : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rwa [e] at h1
  have hFtop : Subgroup.closure {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} = ⊤ := by
    have hdata : ∀ x ∈ F, x ≠ 1 → ∃ a : Fin TwistTag.D4.tag.rank → Ωˣ,
        rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p ∧ rootDiagUnit TwistTag.D4.tag a ≠ 1 ∧
          threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
      intro x hx hx1
      obtain ⟨u, hu, hux⟩ := hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu.1.1
      have hxa : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
        rw [← hux]
        rfl
      refine ⟨a, hu, fun h1 => hx1 ?_, hxa⟩
      apply threeSixEmb_injective K Ω σ
      rw [hxa, h1, map_one]
      group
    refine rClosure_eq_top_of_frattini F S hFS (fun a ha b hb => hTcomm a (hST ha) b (hST hb)) hNSF
      (h0 F hFea hFcard) ?_ ?_
    · intro x hx hx1
      obtain ⟨a, hu, ha1, hxa⟩ := hdata x hx hx1
      by_cases hemp : survivingRoots a = ∅
      · obtain ⟨hcent, -⟩ := hreg a hu ha1 hemp x hxa
        rw [hcent, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        rw [commutatorElement_def, hTcomm g₁ hg₁ g₂ hg₂, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · obtain ⟨hle, -⟩ := derived_centralizer_le_closure_rElements_threeSix hℓ hf K hK σ hσ Ω Fr hFr hε hd
          hgG hFg hp hp3 hpd' a hu.1 (orderOf_eq_prime hu.2 ha1) (Set.nonempty_iff_ne_empty.2 hemp) x hxa
        refine hle.trans (Subgroup.closure_mono ?_)
        rintro k ⟨hk, hkℓ⟩
        exact ⟨x, hx, hx1, Subgroup.mem_centralizer_singleton_iff.1 hk, 1, by rw [pow_one]; exact hkℓ⟩
    ·
      have hM1 : M ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hMcard
        exact hp.one_lt.ne hMcard
      obtain ⟨⟨x₀, hx₀M⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hM1
      have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
      have hyF : c * x₀ * c⁻¹ ∈ F := by
        rw [← hEc]
        exact ⟨x₀, hME hx₀M, rfl⟩
      have hy1 : c * x₀ * c⁻¹ ≠ 1 := by
        intro h
        apply hx₀1'
        rw [← conj_eq_one_iff (a := c)]
        exact h
      obtain ⟨a, hu, ha1, hxa⟩ := hdata _ hyF hy1
      have hne := hMsing x₀ hx₀M a hxa
      exact ⟨c * x₀ * c⁻¹, hyF, hy1, (derived_centralizer_le_closure_rElements_threeSix hℓ hf K hK σ hσ Ω Fr
        hFr hε hd hgG hFg hp hp3 hpd' a hu.1 (orderOf_eq_prime hu.2 ha1) hne _ hxa).2⟩
  have h1 := Inputs2311f.uniClosure_map_conj (r := ℓ) c E
  rw [hEc, hFtop] at h1
  have h2 := congrArg (Subgroup.comap (MulAut.conj c).toMonoidHom) h1
  rwa [Subgroup.comap_top, Subgroup.comap_map_eq_self_of_injective (MulAut.conj c).injective, eq_comm] at h2

end ThreeSix

section CatPhi36

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false


theorem closure_cenGen_threeSix_model {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hpℓ : p ≠ ℓ := CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.prime_ne_of_dvd_phi hℓ hf hp hpd
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact CFSG.HardMathSupport.Seitz.TrialityEven.closure_cenGen_routeC_even hf K hK σ hσ hε hp hp5 hpd E hE
      hcard
  · rcases hε with rfl | rfl
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_one_proved (r := p) (by omega)
        ℓ f hℓ hℓ2 hf K hK σ hσ hp hpℓ hpd E hE hcard
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hp5
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hp5
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSome_holds p hp5)
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSomeThree_holds p hp5))
        ℓ f hℓ hℓ2 hf K hK σ hσ hp hpℓ hpd E hE hcard

theorem uniSeitzPlanes_triality_inner_phi36 :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ∃ q : TauCeti.PrimePower,
      d.1 = .trialityD4 q ∧ (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, q, hq, hpq⟩
  obtain rfl : d = .trialityD4 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨-, hsimp⟩ := finite_isSimpleGroup_cat_trialityD4 hv
  haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulEquiv.isSimpleGroup e.symm
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p (by
      have := q.exponent_pos; omega) hK3
  have hchar : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_trialityD4]
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨ε, hε, hpdε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + ε * (q.p ^ q.exponent : ℕ) + 1 := by
    rcases hpq with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [← hqc, one_mul]
      exact_mod_cast h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
      have := Int.natCast_dvd_natCast.mpr h
      rw [← hqc]
      rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at this
      convert this using 1
      ring
  set E₀C := E.comap (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* _) with hE₀C
  have hE₀C : IsElemAbelian p E₀C := isElemAbelian_comap_conj hinj hE
  have hmap : E₀C.map (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* _) = E := Subgroup.map_comap_eq_self hin
  have hE₀Cc : Nat.card E₀C = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  set E₀ := E₀C.map e.toMonoidHom with hE₀
  have hE₀ea : CFSG.IsElementaryAbelian p E₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀C e.toMonoidHom)
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, hE₀Cc]
  have htop := rClosure_eq_top_threeSix q.prime_p q.exponent_pos K hK σ hσ hε hp (by omega) hpdε
    (fun E' hE' hc' => closure_cenGen_threeSix_model q.prime_p q.exponent_pos K hK σ hσ hε hp hp5 hpdε E' hE'
      hc') E₀ hE₀ea hE₀c
  have htopC := Inputs2311g.uniClosure_eq_top_of_mulEquiv e E₀C htop
  rw [hchar, UniPlaneGen, eq_top_iff, ← htopC, Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hkx, n, hn⟩
  refine mem_uniPlaneClosure (e := MulAut.conj x) hx (fun h => hx1 ?_) ?_ hn
  · exact hinj (h.trans (map_one _).symm)
  · rw [MulAut.conj_apply, ← hkx.eq]
    group

end CatPhi36

section FrameThree

open Subgroup TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KEXC CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Seitz.TrialityEven CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false


theorem rClosure_eq_top_frame_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq4 : 4 ≤ ℓ ^ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hd : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.IsElementaryAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (hF : ∃ F : D4PhiFrame K σ (ℓ ^ f) ε, F.Contains E) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} = ⊤ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨r', hr', hr'5, hr'd, hr'q⟩ :=
    exists_prime_ge_five_dvd_phi_pm hq4 hε hd
  have : Fact r'.Prime := ⟨hr'⟩
  have hf0 : f ≠ 0 := by omega
  have hr'ℓ : r' ≠ ℓ := fun h => hr'q (by rw [h]; exact dvd_pow_self ℓ hf0)
  obtain ⟨F, c₁, hc₁⟩ := hF
  obtain ⟨P, hPexp, hPcard⟩ := exists_plane_of_dvd_phi_pm (ℓ := ℓ)
    hf K hK σ hσ hε hr' (by omega) hr'd
  have hPp : IsPGroup r' P := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2)⟩
  obtain ⟨c₂, hc₂⟩ := exists_conj_into_frame_torus_pm (ℓ := ℓ) hf K
    hK σ hσ hε hr' (by omega) hr'd F P hPp
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
  have hPea : CFSG.IsElementaryAbelian r' P := by
    refine { exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2
  set c := c₁⁻¹ * c₂ with hc
  set E' := P.map (MulAut.conj c).toMonoidHom with hE'
  have hE'ea : CFSG.IsElementaryAbelian r' E' := CFSG.IsElementaryAbelian.map _
  have hE'card : Nat.card E' = r' ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective,
      hPcard]
  have htop' := rClosure_eq_top_threeSix hℓ hf K hK σ hσ hε hr' (by omega) hr'd
    (fun E₁ hE₁ hc₁' => closure_cenGen_threeSix_model hℓ hf K hK σ hσ hε hr' hr'5 hr'd E₁ hE₁ hc₁') E' hE'ea
    hE'card
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hΩ : ringChar (AlgebraicClosure K) = ℓ := ringChar.eq _ ℓ
  have hι : Function.Injective
      ((triEmb K σ (AlgebraicClosure K)).comp (MulAut.conj c₁).toMonoidHom) :=
    triEmb_injective.comp (MulAut.conj c₁).injective
  have hT := twistedTorus_D4_eq_map_of_weylImage F.Fr F.hn F.w F.hnw
    (d4T36M ε) F.hw
  have htup : ∀ z, F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c₁ * z * c₁⁻¹) *
        F.g0 ∈ twistedTorusOf F.n
          (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) →
      ∃ b ∈ fixedCharTuples (d4T36M ε) F.Fr,
        rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * ((triEmb K σ (AlgebraicClosure K)).comp
          (MulAut.conj c₁).toMonoidHom) z * F.g0 := by
    intro z hz
    rw [hT] at hz
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hz
    exact ⟨b, hb, hbz⟩
  rw [eq_top_iff, ← htop', Subgroup.closure_le]
  rintro k ⟨y, hy, hy1, hky, n, hn⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
  have hconj : c₁ * ((MulAut.conj c).toMonoidHom y₀) * c₁⁻¹ = c₂ * y₀ * c₂⁻¹ := by
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨by', hbyF, hby⟩ := htup ((MulAut.conj c).toMonoidHom y₀) (by
    rw [hconj]
    exact hc₂ y₀ hy₀)
  have hyr : ((MulAut.conj c).toMonoidHom y₀) ^ r' = 1 := by
    rw [← map_pow, hPexp y₀ hy₀, map_one]
  obtain ⟨x, hxE, hx1, hle⟩ := exists_centralizer_le_of_frameTuples_pm
    hε hι (fun g => triEmb_mem_adjointGroup _) F.hg0C (by rw [hΩ]; exact hℓ3) hE
    hEcard (fun x hx => htup x (hc₁ x hx)) hr' hr'5 (by rw [hΩ]; exact Ne.symm hr'ℓ) hy1 hyr hbyF hby
  exact Subgroup.subset_closure ⟨x, hxE, hx1, Subgroup.mem_centralizer_singleton_iff.1
    (hle (Subgroup.mem_centralizer_singleton_iff.2 hky.eq)), n, hn⟩

theorem uniSeitzPlanes_triality_inner_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ d.1.characteristic ≠ 2 ∧
      ¬ NormalizesRSubgroup d E ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧
        ¬ (3 ∣ q.card + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
          Nat.card K = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          ∃ e : Cat d ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
            D4PlaneInTorusMinus q.p q.exponent q.prime_p K σ
              ((E.comap (MulAut.conj : Cat d →* _)).map e.toMonoidHom)) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, hch, hnR, q, hq, htw⟩
  obtain rfl : d = .trialityD4 q := hq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨-, hsimp⟩ := finite_isSimpleGroup_cat_trialityD4 hv
  haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulEquiv.isSimpleGroup e.symm
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p (by
      have := q.exponent_pos; omega) hK3
  have hchar : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_trialityD4]
  have hq2 : q.p ≠ 2 := fun h => hch (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  set E₀C := E.comap (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* _) with hE₀C
  have hE₀C : CFSG.Open.IsElemAbelian 3 E₀C := isElemAbelian_comap_conj hinj hE
  have hmap : E₀C.map (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* _) = E := Subgroup.map_comap_eq_self hin
  have hE₀Cc : Nat.card E₀C = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  set E₀ := E₀C.map e.toMonoidHom with hE₀
  have hE₀ea : CFSG.IsElementaryAbelian 3 E₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀C e.toMonoidHom)
  have hE₀c : Nat.card E₀ = 3 ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, hE₀Cc]
  have hanis : ∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup q.p R → R ≠ ⊥ →
      ¬ E₀ ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro R hRp hR1 hle
    apply hnR
    have h := CFSG.LieType.SeitzGeneration.ExcHighThree.exists_normalized_of_native e (E₀C := E₀C)
      ⟨R, hR1, hRp, fun g hg => ?_⟩
    · rw [hmap] at h
      obtain ⟨R', hR'1, hR'p, hR'n⟩ := h
      exact ⟨R', hR'1, by rw [hchar]; exact hR'p, hR'n⟩
    · have hgN := hle hg
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hgN z).1 hz
      · intro hy
        refine ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff.1 hgN _).2 ?_, ?_⟩
        · have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
          rw [e1]
          exact hy
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have h3q : ¬ 3 ∣ q.p ^ q.exponent := fun h =>
    hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4' : q.p ≠ 4 := fun h => by
        have := q.prime_p
        rw [h] at this
        norm_num at this
      omega
    calc 4 ≤ q.p := by omega
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have hmapea : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 (E₀.map (β⁻¹).toMonoidHom) := fun β => by
    haveI := hE₀ea
    exact CFSG.IsElementaryAbelian.map _
  have hmapcard : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card (E₀.map (β⁻¹).toMonoidHom) = 3 ^ 2 := fun β => by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective, hE₀c]
  have htop : Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (q.p ^ n) = 1} = ⊤ := by
    rcases (by omega : (q.p ^ q.exponent) % 3 = 1 ∨ (q.p ^ q.exponent) % 3 = 2) with hq1 | hq2'
    · obtain ⟨β, hFr, -⟩ := d4_toral_q1 hq2 q.exponent_pos hq1 K hK σ hσ E₀ hE₀ea hE₀c hanis
      have hd3 : (3 : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + 1 * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
        obtain ⟨k, hk⟩ : ∃ k, q.p ^ q.exponent = 3 * k + 1 := ⟨q.p ^ q.exponent / 3, by omega⟩
        rw [hk]
        exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩
      exact Inputs2311g.uniClosure_eq_top_of_mulEquiv (β⁻¹) E₀
        (rClosure_eq_top_frame_three q.prime_p hq3 q.exponent_pos hq4 K hK σ hσ (Or.inl rfl) hd3 _
          (hmapea β) (hmapcard β) hFr)
    · rcases d4Minus_plane_dichotomy q.prime_p hq2 hq3 q.exponent_pos hq2' K hK σ hσ E₀ hE₀ea hE₀c with
        hT0 | ⟨β, hFr, -⟩
      · exfalso
        refine htw ⟨?_, K, inferInstance, inferInstance, σ, hK, hσ, e, hT0⟩
        rw [hqc]
        omega
      · have hd3 : (3 : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 + (-1) * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
          obtain ⟨k, hk⟩ : ∃ k, q.p ^ q.exponent = 3 * k + 2 := ⟨q.p ^ q.exponent / 3, by omega⟩
          rw [hk]
          exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩
        exact Inputs2311g.uniClosure_eq_top_of_mulEquiv (β⁻¹) E₀
          (rClosure_eq_top_frame_three q.prime_p hq3 q.exponent_pos hq4 K hK σ hσ (Or.inr rfl) hd3 _
            (hmapea β) (hmapcard β) hFr)
  have htopC := Inputs2311g.uniClosure_eq_top_of_mulEquiv e E₀C htop
  rw [hchar, UniPlaneGen, eq_top_iff, ← htopC, Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hkx, n, hn⟩
  refine mem_uniPlaneClosure (e := MulAut.conj x) hx (fun h => hx1 ?_) ?_ hn
  · exact hinj (h.trans (map_one _).symm)
  · rw [MulAut.conj_apply, ← hkx.eq]
    group

end FrameThree


section D4GraphShortThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator (orderThreeSL orderThreeSL_pow_three)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem commutator_entry_orderThreeSL_excD4 (X : SL2 K)
    (hX : (X : Matrix (Fin 2) (Fin 2) K) = !![1, -1; 0, 1]) :
    ((⁅X⁻¹ * (orderThreeSL K * X * (orderThreeSL K)⁻¹),
        X⁻¹ * (orderThreeSL K ^ 2 * X * (orderThreeSL K ^ 2)⁻¹)⁆ : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = 6 := by
  have hA : ((orderThreeSL K : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, -1] := rfl
  have hXi : ((X⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hX, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hAi : (((orderThreeSL K)⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![-1, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hA2 : ((orderThreeSL K ^ 2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![-1, -1; 1, 0] := by
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA2i : (((orderThreeSL K ^ 2)⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA2, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have ha : ((X⁻¹ * (orderThreeSL K * X * (orderThreeSL K)⁻¹) : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![2, 1; 1, 1] := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, hXi, hA, hX, hAi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hb : ((X⁻¹ * (orderThreeSL K ^ 2 * X * (orderThreeSL K ^ 2)⁻¹) : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, 2] := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, hXi, hA2, hX, hA2i]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, ha,
    hb, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem eq_top_of_normal_of_entry_ne_zero_excD4 [Finite K] (h4 : 4 ≤ Nat.card K) (M : Subgroup (SL2 K))
    [M.Normal] {W : SL2 K} (hW : W ∈ M) (hW01 : (W : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0) : M = ⊤ := by
  have hq := CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4
  rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.normal_le_center_or_eq_top hq.1 hq.2.1 M with hc | htop
  · exfalso
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hc hW)
    apply hW01
    rw [← hr]
    simp
  · exact htop

theorem uniPlaneClosure_d4_graphShortThree_excD4 [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (h4 : 4 ≤ Nat.card K) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hγE : d4Graph K 1 ∈ E)
    (hxE : MulAut.conj (sl2Short K (orderThreeSL K)) ∈ E) : uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  set H := uniPlaneClosure (ringChar K) E with hH
  set A₀ : SL2 K := orderThreeSL K with hA₀
  have hA₀3 : A₀ ^ 3 = 1 := orderThreeSL_pow_three K
  have hγ1 := d4Graph_one_ne_one_excD4 (K := K)
  have hK3 : 3 ≤ Nat.card K := by omega
  have hCγ : ∀ y, d4Graph K 1 y = y → y ∈ H := by
    intro y hy
    have hy' := fixedSubgroup_d4Graph_one_le_closure_rElements_excD4 hK3 hy
    refine (Subgroup.closure_le _).2 ?_ hy'
    rintro s ⟨hs, hsr⟩
    exact mem_uniPlaneClosure (n := 1) hγE hγ1 hs (by rw [pow_one]; exact hsr)
  set t := outerTripleExcD4 K (1, A₀, A₀ ^ 2) with ht
  set x := sl2Short K A₀ with hx
  have hxt : x * d4Graph K 1 t = t := by
    rw [ht, d4Graph_one_outerTripleExcD4, hx, sl2Short_eq_outerTripleExcD4, ← map_mul]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show A₀ * A₀ ^ 2 = 1
      rw [← pow_succ', hA₀3]
    · show A₀ * 1 = A₀
      rw [mul_one]
    · show A₀ * A₀ = A₀ ^ 2
      rw [sq]
  have hβ : MulAut.conj x * d4Graph K 1 = MulAut.conj t * d4Graph K 1 * (MulAut.conj t)⁻¹ := by
    have h2' : x = t * (d4Graph K 1 t)⁻¹ := eq_mul_inv_of_mul_eq hxt
    refine MulEquiv.ext fun y => ?_
    have h3' : (MulAut.conj t)⁻¹ y = t⁻¹ * y * t := by
      rw [← map_inv, MulAut.conj_apply, inv_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, h3', MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, h2']
    group
  have hβE : MulAut.conj x * d4Graph K 1 ∈ E := E.mul_mem hxE hγE
  have hβ1 : MulAut.conj x * d4Graph K 1 ≠ 1 := by
    rw [hβ]
    intro h
    apply hγ1
    have e : d4Graph K 1 =
        (MulAut.conj t)⁻¹ * (MulAut.conj t * d4Graph K 1 * (MulAut.conj t)⁻¹) * MulAut.conj t := by
      group
    rw [e, h]
    group
  have hCβ : ∀ y, d4Graph K 1 y = y → t * y * t⁻¹ ∈ H := by
    intro y hy
    have hy' := fixedSubgroup_d4Graph_one_le_closure_rElements_excD4 hK3 hy
    have hle : (Subgroup.closure {s | s ∈ fixedSubgroup (d4Graph K 1) ∧ s ^ ringChar K = 1}).map
        (MulAut.conj t).toMonoidHom ≤ H := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s, ⟨hs, hsr⟩, rfl⟩
      refine mem_uniPlaneClosure (n := 1) hβE hβ1 ?_ ?_
      · rw [hβ, MulAut.mul_apply, MulAut.mul_apply]
        have h1 : (MulAut.conj t)⁻¹ ((MulAut.conj t).toMonoidHom s) = s := by
          rw [← map_inv]
          simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
          group
        rw [h1]
        have hs' : d4Graph K 1 s = s := hs
        rw [hs']
        rfl
      · rw [pow_one]
        show (MulAut.conj t).toMonoidHom s ^ ringChar K = 1
        rw [← map_pow, hsr, map_one]
    have := hle ⟨y, hy', rfl⟩
    simpa [MulAut.conj_apply] using this
  have hΔ : ∀ X : SL2 K, outerTripleExcD4 K (X, X, X) ∈ H := fun X =>
    hCγ _ (d4Graph_one_outerTripleExcD4 X X X)
  have hΔt : ∀ X : SL2 K, outerTripleExcD4 K (X, A₀ * X * A₀⁻¹, A₀ ^ 2 * X * (A₀ ^ 2)⁻¹) ∈ H := by
    intro X
    have h := hCβ _ (d4Graph_one_outerTripleExcD4 X X X)
    rwa [ht, conj_outerTripleExcD4] at h
  set X : SL2 K := ⟨!![1, -1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hXdef
  have hXv : (X : Matrix (Fin 2) (Fin 2) K) = !![1, -1; 0, 1] := rfl
  set a : SL2 K := X⁻¹ * (A₀ * X * A₀⁻¹) with ha
  set b : SL2 K := X⁻¹ * (A₀ ^ 2 * X * (A₀ ^ 2)⁻¹) with hb
  have hg₁ : outerTripleExcD4 K (1, a, b) ∈ H := by
    have e : outerTripleExcD4 K (1, a, b) = (outerTripleExcD4 K (X, X, X))⁻¹ *
        outerTripleExcD4 K (X, A₀ * X * A₀⁻¹, A₀ ^ 2 * X * (A₀ ^ 2)⁻¹) := by
      rw [← map_inv, ← map_mul]
      congr 1
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show 1 = X⁻¹ * X
        rw [inv_mul_cancel]
      · rfl
      · rfl
    rw [e]
    exact H.mul_mem (H.inv_mem (hΔ X)) (hΔt X)
  have hconj : ∀ Z : SL2 K, ∀ Y₁ Y₃ : SL2 K, outerTripleExcD4 K (Z, Z, Z) * outerTripleExcD4 K (1, Y₁, Y₃) *
      (outerTripleExcD4 K (Z, Z, Z))⁻¹ = outerTripleExcD4 K (1, Z * Y₁ * Z⁻¹, Z * Y₃ * Z⁻¹) := by
    intro Z Y₁ Y₃
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show Z * 1 * Z⁻¹ = 1
      group
    · rfl
    · rfl
  have hψ1 : outerTripleExcD4 K (1, ⁅a, b⁆, 1) ∈ H := by
    have h := H.mul_mem hg₁ (H.inv_mem (H.mul_mem (H.mul_mem (hΔ b) hg₁) (H.inv_mem (hΔ b))))
    rw [hconj] at h
    have e : ((1 : SL2 K), ⁅a, b⁆, (1 : SL2 K)) =
        ((1 : SL2 K), a, b) * ((1 : SL2 K), b * a * b⁻¹, b * b * b⁻¹)⁻¹ := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp only [Prod.snd_mul, Prod.fst_mul, Prod.snd_inv, Prod.fst_inv, commutatorElement_def]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    rw [e, map_mul, map_inv]
    exact h
  have hψ3 : outerTripleExcD4 K (1, 1, ⁅b, a⁆) ∈ H := by
    have h := H.mul_mem hg₁ (H.inv_mem (H.mul_mem (H.mul_mem (hΔ a) hg₁) (H.inv_mem (hΔ a))))
    rw [hconj] at h
    have e : ((1 : SL2 K), (1 : SL2 K), ⁅b, a⁆) =
        ((1 : SL2 K), a, b) * ((1 : SL2 K), a * a * a⁻¹, a * b * a⁻¹)⁻¹ := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp only [Prod.snd_mul, Prod.fst_mul, Prod.snd_inv, Prod.fst_inv]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv, commutatorElement_def]
        group
    rw [e, map_mul, map_inv]
    exact h
  have h6 : (6 : K) ≠ 0 := by
    have : (6 : K) = 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h3
  have hW : ((⁅a, b⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
    rw [ha, hb, commutator_entry_orderThreeSL_excD4 X hXv]
    exact h6
  have hW' : ((⁅b, a⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
    have e : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simpa using hW
  have hψ1all : ∀ W : SL2 K, sl2At K ⟨1, by decide⟩ W ∈ H := by
    let M : Subgroup (SL2 K) := H.comap (sl2At K ⟨1, by decide⟩)
    have hM : ∀ W, W ∈ M ↔ outerTripleExcD4 K (1, W, 1) ∈ H := by
      intro W
      show sl2At K ⟨1, by decide⟩ W ∈ H ↔ _
      rw [outerTripleExcD4_apply]
      simp
    haveI : M.Normal := ⟨fun W hW Z => by
      rw [hM] at hW ⊢
      have h := H.mul_mem (H.mul_mem (hΔ Z) hW) (H.inv_mem (hΔ Z))
      rw [hconj] at h
      convert h using 2
      refine Prod.ext rfl (Prod.ext rfl ?_)
      show 1 = Z * 1 * Z⁻¹
      group⟩
    have htop := eq_top_of_normal_of_entry_ne_zero_excD4 h4 M ((hM _).2 hψ1) hW
    intro W
    have : W ∈ M := by rw [htop]; exact Subgroup.mem_top W
    exact this
  have hψ3all : ∀ W : SL2 K, sl2At K ⟨3, by decide⟩ W ∈ H := by
    let M : Subgroup (SL2 K) := H.comap (sl2At K ⟨3, by decide⟩)
    have hM : ∀ W, W ∈ M ↔ outerTripleExcD4 K (1, 1, W) ∈ H := by
      intro W
      show sl2At K ⟨3, by decide⟩ W ∈ H ↔ _
      rw [outerTripleExcD4_apply]
      simp
    haveI : M.Normal := ⟨fun W hW Z => by
      rw [hM] at hW ⊢
      have h := H.mul_mem (H.mul_mem (hΔ Z) hW) (H.inv_mem (hΔ Z))
      rw [hconj] at h
      convert h using 2
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      show 1 = Z * 1 * Z⁻¹
      group⟩
    have htop := eq_top_of_normal_of_entry_ne_zero_excD4 h4 M ((hM _).2 hψ3) hW'
    intro W
    have : W ∈ M := by rw [htop]; exact Subgroup.mem_top W
    exact this
  have hψ0all : ∀ W : SL2 K, sl2At K ⟨0, by decide⟩ W ∈ H := by
    intro W
    have e : sl2At K ⟨0, by decide⟩ W =
        sl2Short K W * (sl2At K ⟨3, by decide⟩ W)⁻¹ * (sl2At K ⟨1, by decide⟩ W)⁻¹ := by
      rw [sl2Short_apply]
      group
    rw [e]
    exact H.mul_mem (H.mul_mem (hCγ _ (d4Graph_one_sl2Short W)) (H.inv_mem (hψ3all W)))
      (H.inv_mem (hψ1all W))
  have hψ2all : ∀ W : SL2 K, sl2At K ⟨2, by decide⟩ W ∈ H := fun W => hCγ _ (d4Graph_one_sl2Two W)
  refine eq_top_of_simple_mem fun i c => ?_
  rw [xPar_single_eq_sl2At, xPar_neg_single_eq_sl2At]
  fin_cases i
  · exact ⟨hψ0all _, hψ0all _⟩
  · exact ⟨hψ1all _, hψ1all _⟩
  · exact ⟨hψ2all _, hψ2all _⟩
  · exact ⟨hψ3all _, hψ3all _⟩

theorem uniSeitzPlanes_dFour_graphShortThree :
    UniSeitzPlanes fun d p E => p = 3 ∧ d.1.characteristic ≠ 2 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧
      3 ∣ q.card + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
        ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K), ∃ A : SL2 K, A ^ 3 = 1 ∧ A ≠ 1 ∧
          d4Graph K 1 ∈ E.map (MulAut.congr e).toMonoidHom ∧
          MulAut.conj (sl2Short K A) ∈ E.map (MulAut.congr e).toMonoidHom := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, hchar2, q, rfl, h3q, K, _, _, hK, e, A, hA3, hA1, hγ, hxE⟩
  have hchar : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_D]
  have hK' : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK'
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq2 : q.p ≠ 2 := fun h => hchar2 (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have hnat : ∀ n : ℕ, n.Prime → n ≠ q.p → (n : K) ≠ 0 := by
    intro n hn hnq h
    rw [CharP.cast_eq_zero_iff K q.p] at h
    exact hnq ((Nat.prime_dvd_prime_iff_eq q.prime_p hn).1 h).symm
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hnat 2 Nat.prime_two (Ne.symm hq2)
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hnat 3 Nat.prime_three (Ne.symm hq3)
  have h3K : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3q
  have h4 : 4 ≤ Nat.card K := by
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4' : q.p ≠ 4 := fun h => by
        have := q.prime_p
        rw [h] at this
        norm_num at this
      omega
    rw [hK']
    calc 4 ≤ q.p := by omega
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  obtain ⟨S, hS⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_conj_eq_orderThreeSL h3K hA3 hA1
  set s := sl2Short K S with hs
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  set E'' := E'.map (MulAut.congr (MulAut.conj s)).toMonoidHom with hE''
  have hsγ : d4Graph K 1 s = s := d4Graph_one_sl2Short S
  have hγ'' : d4Graph K 1 ∈ E'' := by
    have e1 : (MulAut.congr (MulAut.conj s)).toMonoidHom (d4Graph K 1) = d4Graph K 1 := by
      refine MulEquiv.ext fun y => ?_
      show (MulAut.conj s) ((d4Graph K 1) ((MulAut.conj s).symm y)) = (d4Graph K 1) y
      rw [MulAut.conj_symm_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hsγ]
      group
    rw [← e1]
    exact Subgroup.mem_map_of_mem _ hγ
  have hx'' : MulAut.conj (sl2Short K (orderThreeSL K)) ∈ E'' := by
    have e1 : (MulAut.congr (MulAut.conj s)).toMonoidHom (MulAut.conj (sl2Short K A)) =
        MulAut.conj (sl2Short K (orderThreeSL K)) := by
      rw [mulAut_congr_conj, MulAut.conj_apply, hs, ← map_inv, ← map_mul, ← map_mul, hS]
    rw [← e1]
    exact Subgroup.mem_map_of_mem _ hxE
  have htop := uniPlaneClosure_d4_graphShortThree_excD4 h2 h3 h4 hγ'' hx''
  rw [hring] at htop
  rw [hchar, ← uniPlaneGen_map_congr e, ← uniPlaneGen_map_congr (MulAut.conj s)]
  exact htop

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem exists_conj_sl2Two_or_sl2Short_excD4 [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {x : ↥(adjointGroup Tag.D4 K)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hγx : d4Graph K 1 x = x) :
    ∃ h : ↥(adjointGroup Tag.D4 K), d4Graph K 1 h = h ∧ ∃ A : SL2 K,
      h * x * h⁻¹ = sl2At K ⟨2, by decide⟩ A ∨ h * x * h⁻¹ = sl2Short K A := by
  have hK3' : 3 ≤ Nat.card K := by omega
  set Φ := fixSubgroupEquivG2 K hK3'
  set y : ↥(fixSubgroup (d4Graph K 1)) := ⟨x, mem_fixSubgroup.2 hγx⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simp [y, hx3])
  have hy1 : y ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hz3 : Φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hz1 : Φ y ≠ 1 := fun h => hy1 (Φ.injective (h.trans (map_one Φ).symm))
  obtain ⟨g, j, A, hj⟩ := g2_exists_conj_simpleRootSL2 hK3 hK4 hz3 hz1
  set h := Φ.symm g
  have hΦ : Φ (h * y * h⁻¹) = g * Φ y * g⁻¹ := by simp [h]
  have hhγ : d4Graph K 1 (h : ↥(adjointGroup Tag.D4 K)) = h := mem_fixSubgroup.1 h.2
  refine ⟨h, hhγ, A, ?_⟩
  fin_cases j
  · left
    have e : h * y * h⁻¹ = sl2TwoFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2_sl2Two]))
    exact congrArg Subtype.val e
  · right
    have e : h * y * h⁻¹ = sl2ShortFix A :=
      Φ.injective (Subtype.ext (by rw [hΦ, hj, fixSubgroupEquivG2_sl2Short]))
    exact congrArg Subtype.val e

theorem mem_center_of_sl2Short_eq_one_excD4 {B : SL2 K} (hB : sl2Short K B = 1) :
    B ∈ Subgroup.center (SL2 K) := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.mem_center_of_commute_sl2At
    (i := ⟨0, by decide⟩) fun X => ?_
  have h0 : sl2At K ⟨0, by decide⟩ B = (sl2At K ⟨1, by decide⟩ B * sl2At K ⟨3, by decide⟩ B)⁻¹ := by
    rw [sl2Short_apply] at hB
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_assoc]
    exact hB
  rw [h0]
  refine Commute.inv_left (Commute.mul_left ?_ ?_)
  · exact sl2At_commute (K := K) (i := ⟨1, by decide⟩) (j := ⟨0, by decide⟩) (by decide) (by decide)
      (by decide) B X
  · exact sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨0, by decide⟩) (by decide) (by decide)
      (by decide) B X

theorem mulAut_congr_trans_excD4 {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃] (e : G₁ ≃* G₂)
    (f : G₂ ≃* G₃) (φ : MulAut G₁) :
    (MulAut.congr (e.trans f)).toMonoidHom φ =
      (MulAut.congr f).toMonoidHom ((MulAut.congr e).toMonoidHom φ) :=
  MulEquiv.ext fun _ => rfl

theorem mem_map_congr_trans_conj_excD4 {C : Type*} [Group C] {E : Subgroup (MulAut C)}
    (e : C ≃* ↥(adjointGroup Tag.D4 K)) {h : ↥(adjointGroup Tag.D4 K)} (hh : d4Graph K 1 h = h)
    (hγ : d4Graph K 1 ∈ E.map (MulAut.congr e).toMonoidHom) {x : ↥(adjointGroup Tag.D4 K)}
    (hx : MulAut.conj x ∈ E.map (MulAut.congr e).toMonoidHom) :
    d4Graph K 1 ∈ E.map (MulAut.congr (e.trans (MulAut.conj h))).toMonoidHom ∧
      MulAut.conj (h * x * h⁻¹) ∈ E.map (MulAut.congr (e.trans (MulAut.conj h))).toMonoidHom := by
  have hmap : E.map (MulAut.congr (e.trans (MulAut.conj h))).toMonoidHom =
      (E.map (MulAut.congr e).toMonoidHom).map (MulAut.congr (MulAut.conj h)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  rw [hmap]
  constructor
  · have e1 : (MulAut.congr (MulAut.conj h)).toMonoidHom (d4Graph K 1) = d4Graph K 1 := by
      refine MulEquiv.ext fun y => ?_
      show (MulAut.conj h) ((d4Graph K 1) ((MulAut.conj h).symm y)) = (d4Graph K 1) y
      rw [MulAut.conj_symm_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hh]
      group
    rw [← e1]
    exact Subgroup.mem_map_of_mem _ hγ
  · have e1 : (MulAut.congr (MulAut.conj h)).toMonoidHom (MulAut.conj x) = MulAut.conj (h * x * h⁻¹) := by
      rw [mulAut_congr_conj, MulAut.conj_apply]
    rw [← e1]
    exact Subgroup.mem_map_of_mem _ hx

theorem uniSeitzPlanes_dFour_graphG2Type :
    UniSeitzPlanes fun d p E => p = 3 ∧ d.1.characteristic ≠ 2 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
        ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K), d4Graph K 1 ∈ E.map (MulAut.congr e).toMonoidHom ∧
          ∃ x : ↥(adjointGroup Tag.D4 K), x ≠ 1 ∧ MulAut.conj x ∈ E.map (MulAut.congr e).toMonoidHom := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, hchar2, q, hq, K, hF, hfin, hK, e, hγ, x, hx1, hxE⟩
  obtain rfl : d = .D 4 q := hq
  have hchar : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_D]
  have hK' : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK'
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq2 : q.p ≠ 2 := fun h => hchar2 (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have hK3 : ringChar K ≠ 3 := by rw [hring]; exact hq3
  have h4 : 4 ≤ Nat.card K := by
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4' : q.p ≠ 4 := fun h => by
        have := q.prime_p
        rw [h] at this
        norm_num at this
      omega
    rw [hK']
    calc 4 ≤ q.p := by omega
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  have hE'el : IsElemAbelian 3 E' := isElemAbelian_map_congr e hE
  have hinj : Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hE'el.2 _ hxE)
  have hγx : d4Graph K 1 x = x := by
    have hcomm : d4Graph K 1 * MulAut.conj x = MulAut.conj x * d4Graph K 1 := by
      have := hE'el.1.is_comm.comm (⟨_, hγ⟩ : E') ⟨_, hxE⟩
      exact congrArg Subtype.val this
    apply hinj
    have e1 : MulAut.conj (d4Graph K 1 x) = d4Graph K 1 * MulAut.conj x * (d4Graph K 1)⁻¹ := by
      refine MulEquiv.ext fun y => ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      congr 1
      congr 1
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [e1, hcomm, mul_inv_cancel_right]
  obtain ⟨h, hhγ, A, hlong | hshort⟩ := exists_conj_sl2Two_or_sl2Short_excD4 hK3 h4 hx3 hx1 hγx
  · obtain ⟨hγ', hx'⟩ := mem_map_congr_trans_conj_excD4 e hhγ hγ hxE
    rw [hlong] at hx'
    have hA1 : sl2At K ⟨2, by decide⟩ A ≠ 1 := by
      rw [← hlong]
      intro h0
      apply hx1
      rw [← conj_eq_one_iff (a := h)]
      exact h0
    exact Inputs2311g.uniSeitzPlanes_dFour_graphLong _ 3 hp hp2 hpd hex E hE hc
      ⟨hchar2, q, rfl, K, hF, hfin, hK, e.trans (MulAut.conj h), A, hA1, hγ', hx'⟩
  · obtain ⟨hγ', hx'⟩ := mem_map_congr_trans_conj_excD4 e hhγ hγ hxE
    rw [hshort] at hx'
    have hs1 : sl2Short K A ≠ 1 := by
      rw [← hshort]
      intro h0
      apply hx1
      rw [← conj_eq_one_iff (a := h)]
      exact h0
    have hs3 : sl2Short K A ^ 3 = 1 := by rw [← hshort, conj_pow, hx3]; group
    set B := A ^ 4 with hBdef
    have hA3c : A ^ 3 ∈ Subgroup.center (SL2 K) :=
      mem_center_of_sl2Short_eq_one_excD4 (by rw [map_pow]; exact hs3)
    have hA6 : A ^ 6 = 1 := by
      have := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.sq_eq_one_of_mem_center hA3c
      rw [← pow_mul] at this
      exact this
    have hB3 : B ^ 3 = 1 := by
      rw [hBdef, ← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, hA6, one_pow]
    have hsB : sl2Short K B = sl2Short K A := by
      rw [hBdef, map_pow, show 4 = 3 + 1 by norm_num, pow_succ, hs3, one_mul]
    have hB1 : B ≠ 1 := fun h0 => hs1 (by rw [← hsB, h0, map_one])
    rw [← hsB] at hx'
    by_cases h3q : 3 ∣ q.card + 1
    · exact uniSeitzPlanes_dFour_graphShortThree _ 3 hp hp2 hpd hex E hE hc
        ⟨rfl, hchar2, q, rfl, h3q, K, hF, hfin, hK, e.trans (MulAut.conj h), B, hB3, hB1, hγ', hx'⟩
    ·
      have h3n : ¬ 3 ∣ Nat.card K := by
        rw [hK']
        intro h0
        exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
          (Nat.prime_three.dvd_of_dvd_pow h0)).symm
      have h3K : 3 ∣ Nat.card K - 1 := by
        rw [hK] at h3n
        rw [hK]
        omega
      obtain ⟨P, t, hPt⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3K B
        ⟨1, by rw [pow_one]; exact hB3⟩
      have ht3 : t ^ 3 = 1 := by
        apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective (K := K)
        rw [map_pow, map_one, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply, ← hPt, conj_pow, hB3]
        group
      have ht1 : t ≠ 1 := by
        intro h0
        apply hB1
        have : P * B * P⁻¹ = 1 := by
          rw [hPt, h0]
          exact (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom K).map_one
        rwa [conj_eq_one_iff] at this
      obtain ⟨hγ'', hx''⟩ := mem_map_congr_trans_conj_excD4 (e.trans (MulAut.conj h))
        (d4Graph_one_sl2Short P) hγ' hx'
      rw [← map_inv, ← map_mul, ← map_mul, hPt] at hx''
      exact Inputs2311g.uniSeitzPlanes_dFour_graphShortSplit _ 3 hp hp2 hpd hex E hE hc
        ⟨rfl, q, rfl, K, hF, hfin, hK, (e.trans (MulAut.conj h)).trans (MulAut.conj (sl2Short K P)), t, ht3,
          ht1, hγ'', hx''⟩

end D4GraphShortThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311k
