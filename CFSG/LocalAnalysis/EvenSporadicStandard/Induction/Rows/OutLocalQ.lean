module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSOutModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSVPairs
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

section Fields

variable {G : Type} [Group G] [Finite G]

theorem sol78Fusion39_of_twoCentral {L K : Subgroup G} {u : G} (hu2 : orderOf u = 2)
    (hKcen : u ∈ centralizer (K : Set G)) (h35 : K = componentProduct K u) (hKL : K ≤ L)
    (huK : u ∉ K) (hfuse : TwoCentralFused K) : Sol78Fusion39 L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have huu := mul_self_eq_one_of_orderOf hu2
  intro v hv g hg
  obtain ⟨hug, hKg⟩ := map_conj_eq_of_hyp35 h35 hg
  obtain ⟨k, hk, ε, hε, rfl⟩ := mem_sup_zpowers_cases hu2 hKu hv.1.1
  obtain ⟨hεε, hgε⟩ := eps_facts hu2 hug hε
  have hεc : ∀ x ∈ K, x * ε = ε * x := by
    intro x hx
    rcases hε with rfl | rfl
    · simp
    · exact hKu x hx
  have hkk : k * k = 1 := by
    have h1 := mul_self_eq_one_of_orderOf hv.1.2.2
    calc k * k = k * k * (ε * ε) := by rw [hεε, mul_one]
      _ = k * ε * (k * ε) := by
        calc k * k * (ε * ε) = k * (k * ε) * ε := by simp only [mul_assoc]
          _ = k * (ε * k) * ε := by rw [hεc k hk]
          _ = k * ε * (k * ε) := by simp only [mul_assoc]
      _ = 1 := h1
  by_cases hk1 : k = 1
  · subst hk1
    exact ⟨1, ⟨one_mem _, one_mem _⟩, by simp [hgε]⟩
  have huc : u ∈ vCandidates K u := by
    refine ⟨mem_sup_right (mem_zpowers u), fun hz => huK ?_, hu2⟩
    rw [mem_center_map_iff] at hz
    exact hz.1
  have hmax := hv.2 u huc
  have hKC : K ⊓ centralizer ({u} : Set G) = K :=
    inf_eq_left.2 fun k hk => mem_centralizer_singleton_iff.2 (hKu k hk)
  rw [hKC] at hmax
  have hkm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({k} : Set G)) := by
    refine hmax.trans (twoAdic_mono ?_)
    intro x hx
    obtain ⟨hxK, hxc⟩ := hx
    refine ⟨hxK, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * (k * ε) = k * ε * x := mem_centralizer_singleton_iff.1 hxc
    have h2 : x * k * ε = k * x * ε := by
      calc x * k * ε = x * (k * ε) := by rw [mul_assoc]
        _ = k * ε * x := h1
        _ = k * (ε * x) := by rw [mul_assoc]
        _ = k * (x * ε) := by rw [hεc x hxK]
        _ = k * x * ε := by rw [mul_assoc]
    exact mul_right_cancel h2
  set k' := g * k * g⁻¹ with hk'
  have hk'K : k' ∈ K := conj_mem_of_map_eq hKg hk
  have hk'2 : k' * k' = 1 := by
    calc k' * k' = g * (k * k) * g⁻¹ := by rw [hk']; group
      _ = 1 := by rw [hkk]; group
  have hk'1 : k' ≠ 1 := by
    intro h
    apply hk1
    have : g * k * g⁻¹ = g * 1 * g⁻¹ := by rw [← hk', h]; group
    simpa using this
  have hk'm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({k'} : Set G)) := by
    rw [hk', twoAdic_inf_centralizer_conj hKg k]
    exact hkm
  obtain ⟨c, hcK, hck⟩ := hfuse k hk k' hk'K hkk hk'2 hk1 hk'1 hkm hk'm
  refine ⟨c, ⟨hKL hcK, mem_centralizer_singleton_iff.2 (hKu c hcK)⟩, ?_⟩
  have hcε : c * ε * c⁻¹ = ε := by
    calc c * ε * c⁻¹ = ε * c * c⁻¹ := by rw [hεc c hcK]
      _ = ε := by group
  calc g * (k * ε) * g⁻¹ = (g * k * g⁻¹) * (g * ε * g⁻¹) := by group
    _ = k' * ε := by rw [← hk', hgε]
    _ = (c * k * c⁻¹) * (c * ε * c⁻¹) := by rw [hck, hcε]
    _ = c * (k * ε) * c⁻¹ := by group

theorem sol78Generate_of_twoCentral {L K : Subgroup G} {u z : G} (hu2 : orderOf u = 2)
    (hKcen : u ∈ centralizer (K : Set G)) (hKL : K ≤ L) (huK : u ∉ K)
    (hfuse : TwoCentralFused K) (hz : z ∈ K) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({z} : Set G)))
    (hgen₀ : ∀ l ∈ L, l * u * l⁻¹ = u * z → K ⊔ K.map (conjHom l) = L)
    (hgen₁ : ∀ l ∈ L, l * u * l⁻¹ = z → K ⊔ K.map (conjHom l) = L) : Sol78Generate L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have huu := mul_self_eq_one_of_orderOf hu2
  intro l hl hw
  obtain ⟨v, hv, hwv, -⟩ := hw
  obtain ⟨k, hk, ε, hε, rfl⟩ := mem_sup_zpowers_cases hu2 hKu hv.1.1
  have hεc : ∀ x ∈ K, x * ε = ε * x := by
    intro x hx
    rcases hε with rfl | rfl
    · simp
    · exact hKu x hx
  have hεε : ε * ε = 1 := (eps_facts hu2 (g := 1) (by group) hε).1
  have hkk : k * k = 1 := by
    have h1 := mul_self_eq_one_of_orderOf hv.1.2.2
    calc k * k = k * k * (ε * ε) := by rw [hεε, mul_one]
      _ = k * ε * (k * ε) := by
        calc k * k * (ε * ε) = k * (k * ε) * ε := by simp only [mul_assoc]
          _ = k * (ε * k) * ε := by rw [hεc k hk]
          _ = k * ε * (k * ε) := by simp only [mul_assoc]
      _ = 1 := h1
  have hk1 : k ≠ 1 := by
    intro hk1
    rcases hε with hε1 | hεu
    · exact ne_one_of_orderOf hv.1.2.2 (by rw [hε1, hk1, mul_one])
    · have h1 : l * u * l⁻¹ = 1 := by rw [hwv, hεu, hk1, one_mul, huu]
      have hu1 : u = 1 := by
        have := congrArg (fun x => l⁻¹ * x * l) h1
        simpa [mul_assoc] using this
      exact ne_one_of_orderOf hu2 hu1
  have huc : u ∈ vCandidates K u := by
    refine ⟨mem_sup_right (mem_zpowers u), fun hz' => huK ?_, hu2⟩
    rw [mem_center_map_iff] at hz'
    exact hz'.1
  have hmax := hv.2 u huc
  have hKC : K ⊓ centralizer ({u} : Set G) = K :=
    inf_eq_left.2 fun k hk => mem_centralizer_singleton_iff.2 (hKu k hk)
  rw [hKC] at hmax
  have hkm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({k} : Set G)) := by
    refine hmax.trans (twoAdic_mono ?_)
    intro x hx
    obtain ⟨hxK, hxc⟩ := hx
    refine ⟨hxK, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * (k * ε) = k * ε * x := mem_centralizer_singleton_iff.1 hxc
    have h2 : x * k * ε = k * x * ε := by
      calc x * k * ε = x * (k * ε) := by rw [mul_assoc]
        _ = k * ε * x := h1
        _ = k * (ε * x) := by rw [mul_assoc]
        _ = k * (x * ε) := by rw [hεc x hxK]
        _ = k * x * ε := by rw [mul_assoc]
    exact mul_right_cancel h2
  obtain ⟨c, hcK, hck⟩ := hfuse z hz k hk hz2 hkk hz1 hk1 hzm hkm
  have hcL : c ∈ L := hKL hcK
  have hKc : K.map (conjHom c) = K := map_conj_eq_of_mem hcK
  have hL0 : c⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hcL) hl
  have hlc : l = c * (c⁻¹ * l) := by group
  have hcinv : c⁻¹ * u = u * c⁻¹ := (Commute.inv_left (hKu c hcK)).eq
  have hck' : c⁻¹ * k * c = z := by rw [← hck]; group
  rcases hε with hε1 | hεu
  · rw [hε1, mul_one] at hwv
    have h1 : (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = u * z := by
      calc (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = c⁻¹ * (l * u * l⁻¹) * c := by group
        _ = c⁻¹ * (u * k) * c := by rw [hwv]
        _ = (c⁻¹ * u) * k * c := by simp only [mul_assoc]
        _ = (u * c⁻¹) * k * c := by rw [hcinv]
        _ = u * (c⁻¹ * k * c) := by simp only [mul_assoc]
        _ = u * z := by rw [hck']
    have hg := hgen₀ _ hL0 h1
    rw [hlc]
    exact generate_conj_reduce hcL hKc hg
  · rw [hεu] at hwv
    have hk' : l * u * l⁻¹ = k := by
      rw [hwv]
      calc u * (k * u) = u * (u * k) := by rw [← hKu k hk]
        _ = (u * u) * k := by rw [mul_assoc]
        _ = k := by rw [huu, one_mul]
    have h1 : (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = z := by
      calc (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = c⁻¹ * (l * u * l⁻¹) * c := by group
        _ = c⁻¹ * k * c := by rw [hk']
        _ = z := hck'
    have hg := hgen₁ _ hL0 h1
    rw [hlc]
    exact generate_conj_reduce hcL hKc hg

omit [Finite G] in
theorem sol78Fusion39_of_oneClassK {L K : Subgroup G} {u : G}
    (hKcen : u ∈ centralizer (K : Set G)) (h35 : K = componentProduct K u) (hKL : K ≤ L)
    (huK : u ∈ K) (hone : OneClassOutside K) : Sol78Fusion39 L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have hKsup : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 huK)
  intro v hv g hg
  obtain ⟨hug, hKg⟩ := map_conj_eq_of_hyp35 h35 hg
  have hw := vMaximal_conj hKg hug hv
  have hvK : v ∈ K := hKsup ▸ hv.1.1
  have hwK : g * v * g⁻¹ ∈ K := hKsup ▸ hw.1.1
  obtain ⟨c, hcK, hc⟩ := hone v hvK (g * v * g⁻¹) hwK
    (mul_self_eq_one_of_orderOf hv.1.2.2) (mul_self_eq_one_of_orderOf hw.1.2.2)
    (ne_one_of_orderOf hv.1.2.2) (ne_one_of_orderOf hw.1.2.2) hv.1.2.1 hw.1.2.1
  exact ⟨c, ⟨hKL hcK, mem_centralizer_singleton_iff.2 (hKu c hcK)⟩, hc.symm⟩

omit [Finite G] in
theorem sol78Generate_of_oneClassK {L K : Subgroup G} {u v₀ : G}
    (hKcen : u ∈ centralizer (K : Set G)) (hKL : K ≤ L) (huK : u ∈ K)
    (hone : OneClassOutside K) (hv₀ : v₀ ∈ vCandidates K u)
    (hgen : ∀ l ∈ L, l * u * l⁻¹ = u * v₀ → K ⊔ K.map (conjHom l) = L) :
    Sol78Generate L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have hKsup : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 huK)
  intro l hl hw
  obtain ⟨v, hv, hwv, -⟩ := hw
  have hvK : v ∈ K := hKsup ▸ hv.1.1
  have hv₀K : v₀ ∈ K := hKsup ▸ hv₀.1
  obtain ⟨c, hcK, hc⟩ := hone v₀ hv₀K v hvK
    (mul_self_eq_one_of_orderOf hv₀.2.2) (mul_self_eq_one_of_orderOf hv.1.2.2)
    (ne_one_of_orderOf hv₀.2.2) (ne_one_of_orderOf hv.1.2.2) hv₀.2.1 hv.1.2.1
  have hcL : c ∈ L := hKL hcK
  have hKc : K.map (conjHom c) = K := map_conj_eq_of_mem hcK
  have hL0 : c⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hcL) hl
  have hlc : l = c * (c⁻¹ * l) := by group
  have hcinv : c⁻¹ * u = u * c⁻¹ := (Commute.inv_left (hKu c hcK)).eq
  have h1 : (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = u * v₀ := by
    calc (c⁻¹ * l) * u * (c⁻¹ * l)⁻¹ = c⁻¹ * (l * u * l⁻¹) * c := by group
      _ = c⁻¹ * (u * v) * c := by rw [hwv]
      _ = (c⁻¹ * u) * v * c := by simp only [mul_assoc]
      _ = (u * c⁻¹) * v * c := by rw [hcinv]
      _ = u * (c⁻¹ * v * c) := by simp only [mul_assoc]
      _ = u * v₀ := by rw [← hc]; group
  have hg := hgen _ hL0 h1
  rw [hlc]
  exact generate_conj_reduce hcL hKc hg

theorem mem_vMaximal_of_twoCentral_odd {K : Subgroup G} {u z : G} (hu2 : orderOf u = 2)
    (huK : u ∉ K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hZ : ∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → Odd (orderOf x))
    (hz : z ∈ K) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({z} : Set G))) :
    z ∈ vMaximal K u ∧ z * u ∈ vMaximal K u := by
  have huu := mul_self_eq_one_of_orderOf hu2
  have hzu : z * u = u * z := hKu z hz
  have hmaxall : ∀ v' ∈ vCandidates K u, twoAdic (K ⊓ centralizer ({v'} : Set G)) ≤ twoAdic K :=
    fun v' _ => twoAdic_mono inf_le_left
  have hzo : orderOf z = 2 := orderOf_eq_two_of_mul_self hz2 hz1
  refine ⟨⟨⟨mem_sup_left hz, fun hc => ?_, hzo⟩,
    fun v' hv' => (hmaxall v' hv').trans hzm⟩, ?_⟩
  · rw [mem_center_map_iff] at hc
    have := hZ z hz fun k hk => hc.2 k hk
    rw [hzo] at this
    exact absurd this (by decide)
  have hzuK : z * u ∈ K ⊔ zpowers u :=
    mul_mem (mem_sup_left hz) (mem_sup_right (mem_zpowers u))
  have hzu2 : z * u * (z * u) = 1 := by
    calc z * u * (z * u) = z * (u * z) * u := by simp only [mul_assoc]
      _ = z * (z * u) * u := by rw [← hzu]
      _ = z * z * (u * u) := by simp only [mul_assoc]
      _ = 1 := by rw [hz2, huu, one_mul]
  have hzu1 : z * u ≠ 1 := by
    intro h
    apply huK
    have : u = z⁻¹ * (z * u) := by group
    rw [this, h, mul_one]
    exact K.inv_mem hz
  refine ⟨⟨hzuK, fun hc => ?_, orderOf_eq_two_of_mul_self hzu2 hzu1⟩, fun v' hv' => ?_⟩
  · rw [mem_center_map_iff] at hc
    apply huK
    have : u = z⁻¹ * (z * u) := by group
    rw [this]
    exact K.mul_mem (K.inv_mem hz) hc.1
  · refine (hmaxall v' hv').trans (hzm.trans (twoAdic_mono ?_))
    intro x hx
    refine ⟨hx.1, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * z = z * x := mem_centralizer_singleton_iff.1 hx.2
    have h2 : x * u = u * x := hKu x hx.1
    calc x * (z * u) = (x * z) * u := by rw [mul_assoc]
      _ = z * (x * u) := by rw [h1, mul_assoc]
      _ = z * (u * x) := by rw [h2]
      _ = z * u * x := by rw [mul_assoc]

end Fields

section Model

variable {Y Y' : Type} [Group Y] [Group Y'] {LY E : Subgroup Y} {φ : ↥E →* Y'}
  {D : Subgroup Y'} {tY : Y}

structure OutFacts {G : Type} [Group G] (L K : Subgroup G) (u : G) : Prop where
  u_not_mem : u ∉ K
  odd_center : ∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → Odd (orderOf x)
  fused : TwoCentralFused K
  normalized : ∀ c ∈ L ⊓ centralizer ({u} : Set G), K.map (conjHom c) = K
  rep : ∃ z ∈ K, z * z = 1 ∧ z ≠ 1 ∧ twoAdic K ≤ twoAdic (K ⊓ centralizer ({z} : Set G)) ∧
    (∃ l ∈ L, l * u * l⁻¹ = u * z) ∧ (∀ l ∈ L, l * u * l⁻¹ ≠ z) ∧
    ∀ l ∈ L, l * u * l⁻¹ = u * z → K ⊔ K.map (conjHom l) = L

theorem OutFacts.local39 {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (F : OutFacts L K u) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKcen : u ∈ centralizer (K : Set G)) (h35 : K = componentProduct K u) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  obtain ⟨huK, hZ, hfuse, -, z, hz, hz2, hz1, hzm, ⟨l, hl, hlconj⟩, hnoconj, hgen⟩ := F
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  exact ⟨vPairs_nonempty_of_mem (mem_vMaximal_of_twoCentral_odd hu2 huK hKu hZ hz hz2 hz1 hzm).1
      ⟨l, hl, hlconj⟩,
    sol78Fusion39_of_twoCentral hu2 hKcen h35 hKL huK hfuse,
    sol78Generate_of_twoCentral hu2 hKcen hKL huK hfuse hz hz2 hz1 hzm hgen
      (fun l hl h => absurd h (hnoconj l hl))⟩

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.OutRowModel.outFacts_of_fields [Finite ↥E]
    (M : OutRowModel LY E φ D tY) {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKcen : u ∈ centralizer (K : Set G))
    (Ψ : ↥L →* Y) (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ LY) (hΨR : ∀ y ∈ LY, ∃ x, Ψ x = y) (hΨu : Ψ ⟨u, hu⟩ = tY)
    (hKperf : Group.IsPerfect K) (hKcard : Nat.card K = Nat.card D) : OutFacts L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have hq := M.quot
  have := hKperf
  let ΨK : ↥K →* Y := Ψ.comp (Subgroup.inclusion hKL)
  have hΨK : Function.Injective ΨK := hΨ.comp (Subgroup.inclusion_injective hKL)
  have hΨKu : ∀ k : ↥K, ΨK k * tY = tY * ΨK k := by
    intro k
    rw [← hΨu]
    show Ψ (Subgroup.inclusion hKL k) * Ψ ⟨u, hu⟩ = Ψ ⟨u, hu⟩ * Ψ (Subgroup.inclusion hKL k)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKu k k.2)
  let KP : Subgroup Y := ΨK.range
  have hKPE : KP ≤ E := by
    rintro _ ⟨k, rfl⟩
    exact (M.E_iff _).2 ⟨hΨL _, hΨKu k⟩
  let KE : Subgroup ↥E := KP.subgroupOf E
  let eKP : ↥K ≃* ↥KP := MonoidHom.ofInjective hΨK
  let eKE : ↥K ≃* ↥KE := eKP.trans (Subgroup.subgroupOfEquivOfLe hKPE).symm
  have hKEperf : Group.IsPerfect KE :=
    Group.IsPerfect.ofSurjective (f := eKE.toMonoidHom) eKE.surjective
  have hKEcard : Nat.card KE = Nat.card D := (Nat.card_congr eKE.toEquiv).symm.trans hKcard
  let eD : ↥KE ≃* ↥D := hq.restrictEquiv hKEperf hKEcard
  let eK : ↥K ≃* ↥D := eKE.trans eD
  have hZ : ∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → x = 1 :=
    center_trivial_of_equiv eK hq.simple hq.noncomm
  have huK : u ∉ K := fun huK => ne_one_of_orderOf hu2 (hZ u huK fun k hk => (hKu k hk).symm)
  have hfuse : TwoCentralFused K := twoCentralFused_of_equiv eK M.D_fuse
  have hnorm : ∀ c ∈ L ⊓ centralizer ({u} : Set G), K.map (conjHom c) = K := by
    intro c hc
    have hcL : c ∈ L := hc.1
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.1 hc.2
    have hcE : Ψ ⟨c, hcL⟩ ∈ E := by
      refine (M.E_iff _).2 ⟨hΨL _, ?_⟩
      rw [← hΨu, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcu
    have hN := hq.normal hKEperf hKEcard
    have hle : K.map (conjHom c) ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      have hkE : (⟨ΨK ⟨k, hk⟩, hKPE ⟨⟨k, hk⟩, rfl⟩⟩ : ↥E) ∈ KE := ⟨⟨k, hk⟩, rfl⟩
      have h1 := hN.conj_mem _ hkE ⟨Ψ ⟨c, hcL⟩, hcE⟩
      rw [Subgroup.mem_subgroupOf] at h1
      obtain ⟨k', hk'⟩ := h1
      have h2 : Ψ (⟨c, hcL⟩ * ⟨k, hKL hk⟩ * ⟨c, hcL⟩⁻¹) = Ψ (Subgroup.inclusion hKL k') := by
        rw [map_mul, map_mul, map_inv]
        exact hk'.symm
      have h3 := hΨ h2
      have h4 : c * k * c⁻¹ = (k' : G) := congrArg Subtype.val h3
      show c * k * c⁻¹ ∈ K
      rw [h4]
      exact k'.2
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (conjHom_injective c)])
  let AE : ↥E := ⟨M.A, M.A_mem⟩
  let BE : ↥E := ⟨M.B, M.B_mem⟩
  have hAKE : AE ∈ KE := hq.odd_mem hKEperf hKEcard M.A_odd
  have hBKE : BE ∈ KE := hq.odd_mem hKEperf hKEcard M.B_odd
  have hcl_le : Subgroup.closure {AE, BE} ≤ KE := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hAKE
    · exact hBKE
  have hcl_eq : Subgroup.closure {AE, BE} = KE := by
    refine Subgroup.eq_of_le_of_card_ge hcl_le ?_
    rw [hKEcard, ← M.gen_card]
    have h1 : (Subgroup.closure {AE, BE}).map φ = Subgroup.closure {φ AE, φ BE} := by
      rw [MonoidHom.map_closure, Set.image_pair]
    rw [← h1]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have hKP_eq : Subgroup.closure {M.A, M.B} = KP := by
    have h1 : (Subgroup.closure {AE, BE}).map E.subtype = Subgroup.closure {M.A, M.B} := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← h1, hcl_eq]
    exact Subgroup.map_subgroupOf_eq_of_le hKPE
  have hzKP : M.z ∈ KP := hKP_eq ▸ M.z_mem
  obtain ⟨zK, hzK⟩ := hzKP
  have hzE : M.z ∈ E := hKPE ⟨zK, hzK⟩
  have hzGK : (zK : G) ∈ K := zK.2
  have hzG2 : (zK : G) * (zK : G) = 1 := by
    have : ΨK (zK * zK) = ΨK 1 := by rw [map_mul, hzK, M.z_sq, map_one]
    exact congrArg Subtype.val (hΨK this)
  have hzG1 : (zK : G) ≠ 1 := by
    intro h
    apply M.z_ne
    rw [← hzK]
    have : zK = 1 := Subtype.ext h
    rw [this, map_one]
  obtain ⟨lL, hlL⟩ := hΨR M.l M.l_mem
  have hlGL : (lL : G) ∈ L := lL.2
  have hlGconj : (lL : G) * u * (lL : G)⁻¹ = u * (zK : G) := by
    have h1 : Ψ (lL * ⟨u, hu⟩ * lL⁻¹) = Ψ (⟨u, hu⟩ * Subgroup.inclusion hKL zK) := by
      rw [map_mul, map_mul, map_inv, map_mul, hlL, hΨu]
      show M.l * tY * M.l⁻¹ = tY * ΨK zK
      rw [hzK]
      exact M.l_conj
    have h2 := hΨ h1
    exact congrArg Subtype.val h2
  have hnoconj : ∀ l' ∈ L, l' * u * l'⁻¹ ≠ (zK : G) := by
    intro l' hl' h
    apply M.z_not_conj (Ψ ⟨l', hl'⟩) (hΨL _)
    have h1 : Ψ (⟨l', hl'⟩ * ⟨u, hu⟩ * ⟨l', hl'⟩⁻¹) = Ψ (Subgroup.inclusion hKL zK) :=
      congrArg Ψ (Subtype.ext h)
    rw [map_mul, map_mul, map_inv, hΨu] at h1
    exact h1.trans hzK
  have hzm : twoAdic K ≤ twoAdic (K ⊓ centralizer ({(zK : G)} : Set G)) := by
    have hcardeq := card_inf_centralizer_eq_of_equiv eK hzGK
    have heqz : ((eK ⟨(zK : G), hzGK⟩ : ↥D) : Y') = φ ⟨M.z, hzE⟩ := by
      have : (⟨ΨK zK, hKPE ⟨zK, rfl⟩⟩ : ↥E) = ⟨M.z, hzE⟩ := Subtype.ext hzK
      rw [← this]
      exact hq.restrictEquiv_apply hKEperf hKEcard _
    have h1 := M.z_two hzE (heqz ▸ (eK ⟨(zK : G), hzGK⟩).2)
    rw [← twoAdic_eq_of_equiv eK] at h1
    unfold twoAdic at h1 ⊢
    rw [hcardeq, heqz]
    exact h1
  have hgen_lG : K ⊔ K.map (conjHom (lL : G)) = L := by
    refine le_antisymm (sup_le hKL ?_) ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact L.mul_mem (L.mul_mem hlGL (hKL hk)) (L.inv_mem hlGL)
    · intro g hg
      let H : Subgroup ↥L := (K ⊔ K.map (conjHom (lL : G))).subgroupOf L
      let HY : Subgroup Y := H.map Ψ
      have hAP : M.A ∈ KP := hKP_eq ▸ Subgroup.subset_closure (Set.mem_insert _ _)
      have hBP : M.B ∈ KP := hKP_eq ▸ Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hmemHY : ∀ y ∈ KP, y ∈ HY ∧ M.l * y * M.l⁻¹ ∈ HY := by
        rintro _ ⟨a, rfl⟩
        refine ⟨⟨Subgroup.inclusion hKL a, ?_, rfl⟩, ⟨lL * Subgroup.inclusion hKL a * lL⁻¹, ?_, ?_⟩⟩
        · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left a.2)
        · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨(a : G), a.2, rfl⟩)
        · rw [map_mul, map_mul, map_inv, hlL]
          rfl
      have hgenHY : Subgroup.closure {M.A, M.B, M.l * M.A * M.l⁻¹, M.l * M.B * M.l⁻¹} ≤ HY := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl | rfl | rfl)
        · exact (hmemHY _ hAP).1
        · exact (hmemHY _ hBP).1
        · exact (hmemHY _ hAP).2
        · exact (hmemHY _ hBP).2
      obtain ⟨h, hH, hhg⟩ := hgenHY (M.gen (hΨL ⟨g, hg⟩))
      have : h = ⟨g, hg⟩ := hΨ hhg
      rw [this] at hH
      exact Subgroup.mem_subgroupOf.1 hH
  exact ⟨huK, fun x hx hxc => by rw [hZ x hx hxc, orderOf_one]; exact odd_one, hfuse, hnorm,
    (zK : G), hzGK, hzG2, hzG1, hzm, ⟨(lL : G), hlGL, hlGconj⟩,
    fun l hl h => hnoconj l hl h, generate_of_one hlGL hlGconj hnorm hgen_lG⟩

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.OutRowModel.local39_of_fields [Finite ↥E]
    (M : OutRowModel LY E φ D tY) {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKcen : u ∈ centralizer (K : Set G))
    (h35 : K = componentProduct K u) (Ψ : ↥L →* Y) (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ LY) (hΨR : ∀ y ∈ LY, ∃ x, Ψ x = y) (hΨu : Ψ ⟨u, hu⟩ = tY)
    (hKperf : Group.IsPerfect K) (hKcard : Nat.card K = Nat.card D) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u :=
  (M.outFacts_of_fields hu hu2 hKL hKcen Ψ hΨ hΨL hΨR hΨu hKperf hKcard).local39 hu2 hKL hKcen h35

end Model

end CFSG.EvenSporadicStandard.Induction
