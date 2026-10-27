module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixCoreTools

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups C5

theorem d4A2Sigma_eq_stdA2 : d4A2Sigma = trialityStdA2 := by
  ext v
  simp only [d4A2Sigma, trialityStdA2, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem le_normalizer_commutator_self {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    H ≤ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_conj_mem (Y := G) (U := ⁅H, H⁆) fun z hz => ?_
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)
  have h1 : (MulAut.conj x).toMonoidHom z ∈ ⁅H, H⁆.map (MulAut.conj x).toMonoidHom := ⟨z, hz, rfl⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hle hle h1


theorem d4C_comp5 {r p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (r ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (r ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((r ^ f : ℕ) : ℤ) ^ 2 + ε * (r ^ f : ℕ) + 1) (hpd : p ∣ d)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hy : orderOf y = p) (hyr : RFree r y) :
    Comp5Concl r y := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = r ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K r := finite_field_prime_power_characteristic hr (by omega) hK3
  have : CharP (AlgebraicClosure K) r :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective r
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) r f c = c ^ (r ^ f) := fun c =>
    iterateFrobenius_def r f c
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ := triality_three_six_tori_Sylow_and_root_kernels hr hf K
    hK σ hσ (AlgebraicClosure K) _ hFr hε hd
  obtain ⟨hTι, -, hp'⟩ := hall g hgG hFg
  obtain ⟨⟨S, hS⟩, -, -, -, hline, -, -, hsurv, -, -⟩ := hp' p hp (by omega) hpd
  have : Finite (threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) r f)
      ε p 0) := Nat.finite_of_card_ne_zero (by rw [hline 0]; exact hp.ne_zero)
  have : Nontrivial (threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) r f)
      ε p 0) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hline 0]; exact hp.one_lt)
  obtain ⟨⟨h, hhL⟩, hh1⟩ := exists_ne (1 : threeSixLine (AlgebraicClosure K)
    (iterateFrobenius (AlgebraicClosure K) r f) ε p 0)
  have hh1' : h ≠ 1 := fun e => hh1 (Subtype.ext e)
  have hT := (Subgroup.mem_inf.1 hhL).1
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hT.1).1
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p := orderOf_eq_prime hT.2 hh1'
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4, (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp 0
    exact ⟨w, by rw [(hsurv a hT hh1').1 0 hhL, d4A2Sigma_eq_stdA2, ← hw]⟩
  obtain ⟨x, hx⟩ : g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ ∈ (threeSixEmb K _ σ).range :=
    hTι ⟨_, hT.1, rfl⟩
  obtain ⟨-, -, hR, hSL, hSU, -, -, -, -, hk, -⟩ :=
    triality_three_six_singular_fixed_centralizers hr hf K hK σ hσ (AlgebraicClosure K) _ hFr hε
      hd g hgG hFg hp (by omega) hpd a hT.1 hord v hv x hx
  set M := centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hMdef
  have hTM : threeSixFixedTorus K (AlgebraicClosure K) σ (iterateFrobenius _ r f) ε g ≤ M := by
    intro t ht
    obtain ⟨t₀, ht₀, hteq⟩ := ht
    rw [hMdef, mem_centralizer_singleton_iff]
    apply threeSixEmb_injective K (AlgebraicClosure K) σ
    rw [map_mul, map_mul, ← hteq, hx]
    have hc := rootDiagUnit_mul_comm_of_mem_torusGroup a (Subgroup.mem_inf.1 ht₀).1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * t₀ * g⁻¹ * (g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) =
        g * (t₀ * rootDiagUnit TwistTag.D4.tag a) * g⁻¹ := by group
      _ = g * (rootDiagUnit TwistTag.D4.tag a * t₀) * g⁻¹ := by rw [hc]
      _ = _ := by group
  have hM : ¬ p ∣ M.index := fun hdvd =>
    S.not_dvd_index (hdvd.trans (index_dvd_of_le (hS.trans hTM)))
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    apply hh1'
    have h1 := congrArg (fun z => g⁻¹ * z * g) hx
    simp only [mul_one, inv_mul_cancel] at h1
    rw [h1]
    group
  have hLt : ⁅M, M⁆ ≠ ⊤ := by
    intro hLtop
    have hMM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
    have hMtop : M = ⊤ := top_le_iff.1 (hLtop ▸ hMM)
    have hxc : x ∈ center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [mem_center_iff]
      intro z
      have hz : z ∈ M := by rw [hMtop]; exact mem_top z
      rw [hMdef, mem_centralizer_singleton_iff] at hz
      exact hz
    rw [exceptional_fixed_center_trivial TwistTag.D4 K σ, mem_bot] at hxc
    exact hx1 hxc
  rcases hε with rfl | rfl
  · obtain ⟨e, -⟩ := hSL rfl
    have : Finite (RingHom.eqLocusField (iterateFrobenius (AlgebraicClosure K) r f)
        (RingHom.id (AlgebraicClosure K))) :=
      Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hr.ne_zero)
    obtain ⟨hQ, hC, hrL⟩ := typ_sl hr hr2 hf (Or.inr rfl) hk (Or.inl rfl)
      (e.symm.trans (MulEquiv.subgroupCongr hR.symm))
    exact comp5Concl_of_block hM (le_normalizer_commutator_self M) hLt hQ hC hrL hy hyr
  · obtain ⟨U, hU, e, -⟩ := hSU rfl
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := nonempty_statedSU_mulEquiv (Ω := AlgebraicClosure K) hf hU
    obtain ⟨hQ, hC, hrL⟩ := typ_su3 hr hr2 hf hF
      ((e'.trans e.symm).trans (MulEquiv.subgroupCongr hR.symm))
    exact comp5Concl_of_block hM (le_normalizer_commutator_self M) hLt hQ hC hrL hy hyr

end CFSG.OddStandard.GH71.S55
