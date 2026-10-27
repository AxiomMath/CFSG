module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitParity
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitReal
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqElem
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqU1

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_orbit_four
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hall : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁))
    {K₁ : Subgroup G} (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁) {s₂ s₃ s₄ : G}
    (hs₂ : s₂ ∈ S) (hs₃ : s₃ ∈ S) (hs₄ : s₄ ∈ S) (h2 : conjugate K₁ s₂ ≠ K₁)
    (h3 : conjugate K₁ s₃ ≠ K₁) (h4 : conjugate K₁ s₄ ≠ K₁)
    (h32 : conjugate K₁ s₃ ≠ conjugate K₁ s₂) (h42 : conjugate K₁ s₄ ≠ conjugate K₁ s₂)
    (h43 : conjugate K₁ s₄ ≠ conjugate K₁ s₃) {e₁ : G} (he₁ : e₁ ∈ S ⊓ K₁) (he₁o : orderOf e₁ = 2)
    {a : G} (ha : a ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) (ha2 : a * a = 1)
    (haQ : a ∉ coreActionKernel L) :
    ∃ g₂ ∈ S, ∃ g₃ ∈ S, ∃ g₄ ∈ S, conjugate K₁ g₂ ≠ K₁ ∧ conjugate K₁ g₃ ≠ K₁ ∧
      conjugate K₁ g₄ ≠ K₁ ∧ conjugate K₁ g₃ ≠ conjugate K₁ g₂ ∧
      conjugate K₁ g₄ ≠ conjugate K₁ g₂ ∧ conjugate K₁ g₄ ≠ conjugate K₁ g₃ ∧
      e₁ * (g₂⁻¹ * e₁ * g₂) * (g₃⁻¹ * e₁ * g₃) * (g₄⁻¹ * e₁ * g₄) ∈ coreActionKernel L ∧
      ∀ g ∈ S, g⁻¹ * e₁ * g = e₁ ∨ g⁻¹ * e₁ * g = g₂⁻¹ * e₁ * g₂ ∨
        g⁻¹ * e₁ * g = g₃⁻¹ * e₁ * g₃ ∨ g⁻¹ * e₁ * g = g₄⁻¹ * e₁ * g₄ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hSyl
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  set C := centralizer ({u} : Set G) with hC
  have hcomp : ∀ g ∈ S, conjugate K₁ g ≤ C ∧ IsPComponent 2 ((conjugate K₁ g).subgroupOf C) ∧
      ¬ ⁅conjugate K₁ g, oddIn L ⊓ C⁆ ≤ oddIn (conjugate K₁ g) := fun g hg =>
    conj_component hS hU hheld hSol hGW hMax hset hu huc hK₁u hK₁p hK₁n hg
  have hpar := fun g (hg : g ∈ S) => parity_of_component hS hU hheld hSol hGW hMax hL34 hset hu
    (hcomp g hg).1 (hcomp g hg).2.1 (hcomp g hg).2.2
    (hall _ (hcomp g hg).1 (hcomp g hg).2.1 (hcomp g hg).2.2)
  have hcard : ∀ g ∈ S, Nat.card ↥(S ⊓ conjugate K₁ g) = 2 := fun g hg =>
    card_inf_component hS hU hheld hSol hGW hMax hset hu huc (hcomp g hg).1 (hcomp g hg).2.1
      (hcomp g hg).2.2 (hall _ (hcomp g hg).1 (hcomp g hg).2.1 (hcomp g hg).2.2)
  have he₁2 : e₁ * e₁ = 1 := by rw [← pow_two, ← he₁o, pow_orderOf_eq_one]
  have he₁1 : e₁ ≠ 1 := fun h => by rw [h, orderOf_one] at he₁o; exact absurd he₁o (by decide)
  have hmem : ∀ g ∈ S, g⁻¹ * e₁ * g ∈ S ⊓ conjugate K₁ g := by
    intro g hg
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) (mem_inf.mp he₁).1) hg, ?_⟩
    rw [mem_conjugate_iff, show g * (g⁻¹ * e₁ * g) * g⁻¹ = e₁ by group]
    exact (mem_inf.mp he₁).2
  have hinv : ∀ g : G, g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = 1 := by
    intro g
    rw [show g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = g⁻¹ * (e₁ * e₁) * g by group, he₁2]
    group
  have hne1 : ∀ g : G, g⁻¹ * e₁ * g ≠ 1 := fun g h => he₁1 (by
    calc e₁ = g * (g⁻¹ * e₁ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hord : ∀ g : G, orderOf (g⁻¹ * e₁ * g) = 2 := fun g =>
    orderOf_eq_prime (by rw [pow_two]; exact hinv g) (hne1 g)
  have hsame : ∀ g ∈ S, ∀ h ∈ S, conjugate K₁ g = conjugate K₁ h →
      g⁻¹ * e₁ * g = h⁻¹ * e₁ * h := by
    intro g hg h hh hgh
    exact eq_of_card_two (hcard h hh) (hgh ▸ hmem g hg) (hmem h hh) (hne1 g) (hne1 h)
  have hoth : ∀ g ∈ S, ∀ h ∈ S, conjugate K₁ g ≠ conjugate K₁ h →
      h⁻¹ * e₁ * h ∈ coreActionKernel (conjugate K₁ g) := fun g hg h hh hgh =>
    le_coreActionKernel_of_ne (hcomp g hg).1 (hcomp h hh).1 (hcomp g hg).2.1 (hcomp h hh).2.1
      hgh (mem_inf.mp (hmem h hh)).2
  have hN : ∀ g ∈ S, ∀ h ∈ S, h⁻¹ * e₁ * h ∈ S ⊓ normalizer (conjugate K₁ g : Set G) := by
    intro g hg h hh
    refine mem_inf.mpr ⟨(mem_inf.mp (hmem h hh)).1, ?_⟩
    by_cases hgh : conjugate K₁ g = conjugate K₁ h
    · rw [hgh]
      exact le_normalizer (mem_inf.mp (hmem h hh)).2
    · exact (mem_coreActionKernel.mp (hoth g hg h hh hgh)).1
  have hcomm : ∀ g ∈ S, ∀ h ∈ S, g⁻¹ * e₁ * g * (h⁻¹ * e₁ * h) = h⁻¹ * e₁ * h * (g⁻¹ * e₁ * g) := by
    intro g hg h hh
    by_cases hgh : conjugate K₁ g = conjugate K₁ h
    · rw [hsame g hg h hh hgh]
    · exact commute_of_ne (hcomp g hg).1 (hcomp h hh).1 (hcomp g hg).2.1 (hcomp h hh).2.1 hgh
        hS2 (mem_inf.mp (hmem g hg)).1 (mem_inf.mp (hmem g hg)).2 (mem_inf.mp (hmem h hh)).1
        (mem_inf.mp (hmem h hh)).2
  have hPQ : ∀ g ∈ S, ∀ h ∈ S, ∀ q ∈ S ⊓ coreActionKernel L,
      ((q ∈ coreActionKernel (conjugate K₁ g) ∨ q * t ∈ coreActionKernel (conjugate K₁ g)) ↔
        (q ∈ coreActionKernel (conjugate K₁ h) ∨ q * t ∈ coreActionKernel (conjugate K₁ h))) :=
    fun g hg h hh q hq => ((hpar g hg).2.1 q hq).trans ((hpar h hh).2.1 q hq).symm
  have hown : ∀ g ∈ S, ¬ (g⁻¹ * e₁ * g ∈ coreActionKernel (conjugate K₁ g) ∨
      g⁻¹ * e₁ * g * t ∈ coreActionKernel (conjugate K₁ g)) := fun g hg =>
    (hpar g hg).2.2 _ (hmem g hg) (hord g)
  have hpair : ∀ g ∈ S, ∀ h ∈ S, ∀ k ∈ S, conjugate K₁ g ≠ conjugate K₁ h →
      conjugate K₁ k ≠ conjugate K₁ g → conjugate K₁ k ≠ conjugate K₁ h →
      g⁻¹ * e₁ * g * (h⁻¹ * e₁ * h) ∉ coreActionKernel L := by
    intro g hg h hh k hk hgh hkg hkh hC
    have hQ : g⁻¹ * e₁ * g * (h⁻¹ * e₁ * h) ∈ S ⊓ coreActionKernel L :=
      mem_inf.mpr ⟨mul_mem (mem_inf.mp (hmem g hg)).1 (mem_inf.mp (hmem h hh)).1, hC⟩
    have h1 := (hpar g hg).1 _ (hN g hg g hg) _ (hN g hg h hh)
    have h2 : g⁻¹ * e₁ * g * (h⁻¹ * e₁ * h) ∈ coreActionKernel (conjugate K₁ k) :=
      mul_mem (hoth k hk g hg hkg) (hoth k hk h hh hkh)
    have h3 := (hPQ k hk g hg _ hQ).mp (Or.inl h2)
    rw [h1] at h3
    exact hown g hg (h3.mpr (Or.inl (hoth g hg h hh hgh)))
  have hsingle : ∀ g ∈ S, ∀ k ∈ S, conjugate K₁ k ≠ conjugate K₁ g →
      g⁻¹ * e₁ * g ∉ coreActionKernel L := by
    intro g hg k hk hkg hC
    have h3 := (hPQ k hk g hg _ (mem_inf.mpr ⟨(mem_inf.mp (hmem g hg)).1, hC⟩)).mp
      (Or.inl (hoth k hk g hg hkg))
    exact hown g hg h3
  have hs1 : (1 : G) ∈ S := one_mem _
  have hc1 : conjugate K₁ 1 = K₁ := conjugate_one K₁
  have he1' : (1 : G)⁻¹ * e₁ * 1 = e₁ := by group
  have hd : ∀ g ∈ S, ∀ h ∈ S, ∀ k ∈ S, conjugate K₁ g ≠ conjugate K₁ h →
      conjugate K₁ k ≠ conjugate K₁ g → conjugate K₁ k ≠ conjugate K₁ h →
      (g⁻¹ * e₁ * g)⁻¹ * (h⁻¹ * e₁ * h) ∉ coreActionKernel L := by
    intro g hg h hh k hk hgh hkg hkh
    rw [inv_eq_of_mul_eq_one_right (hinv g)]
    exact hpair g hg h hh k hk hgh hkg hkh
  have hK1 : ∀ x, conjugate K₁ x ≠ K₁ → conjugate K₁ x ≠ conjugate K₁ 1 := fun x h => by
    rwa [hc1]
  have hK1' : ∀ x, conjugate K₁ x ≠ K₁ → conjugate K₁ 1 ≠ conjugate K₁ x := fun x h => by
    rw [hc1]
    exact h.symm
  have hn1 : e₁ ∉ coreActionKernel L := by
    have h := hsingle 1 hs1 s₂ hs₂ (hK1 s₂ h2)
    rwa [he1'] at h
  have hn12 : e₁⁻¹ * (s₂⁻¹ * e₁ * s₂) ∉ coreActionKernel L := by
    have h := hd 1 hs1 s₂ hs₂ s₃ hs₃ (hK1' s₂ h2) (hK1 s₃ h3) h32
    rwa [he1'] at h
  have hn13 : e₁⁻¹ * (s₃⁻¹ * e₁ * s₃) ∉ coreActionKernel L := by
    have h := hd 1 hs1 s₃ hs₃ s₂ hs₂ (hK1' s₃ h3) (hK1 s₂ h2) h32.symm
    rwa [he1'] at h
  have hn14 : e₁⁻¹ * (s₄⁻¹ * e₁ * s₄) ∉ coreActionKernel L := by
    have h := hd 1 hs1 s₄ hs₄ s₂ hs₂ (hK1' s₄ h4) (hK1 s₂ h2) h42.symm
    rwa [he1'] at h
  obtain ⟨ρ⟩ := AutL34.exists_real (GSThmB.commutator_eq_self_of_isPComponent hLt hLpt) htypeL
  have hconj : ∀ g ∈ S, ∃ g' ∈ S,
      (g'⁻¹ * (g⁻¹ * e₁ * g) * g')⁻¹ * (g⁻¹ * e₁ * g * a) ∈ coreActionKernel L := fun g hg =>
    ρ.exists_conj_mul_center hSyl (mem_inf.mp he₁).1 he₁2 (fun x hx y hy => hcomm x hx y hy) ha
      hs₂ hs₃ hs₄ hn1 (hsingle s₂ hs₂ 1 hs1 (hK1' s₂ h2)) (hsingle s₃ hs₃ 1 hs1 (hK1' s₃ h3))
      (hsingle s₄ hs₄ 1 hs1 (hK1' s₄ h4)) hn12 hn13 hn14
      (hd s₂ hs₂ s₃ hs₃ 1 hs1 h32.symm (hK1' s₂ h2) (hK1' s₃ h3))
      (hd s₂ hs₂ s₄ hs₄ 1 hs1 h42.symm (hK1' s₂ h2) (hK1' s₄ h4))
      (hd s₃ hs₃ s₄ hs₄ 1 hs1 h43.symm (hK1' s₃ h3) (hK1' s₄ h4)) hg
  have hP2 : ∀ g ∈ S, ∀ x ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
      ∀ y ∈ S ⊓ normalizer (conjugate K₁ g : Set G), y ∈ coreActionKernel (conjugate K₁ g) →
        ((x * y ∈ coreActionKernel (conjugate K₁ g) ∨
            x * y * t ∈ coreActionKernel (conjugate K₁ g)) ↔
          (x ∈ coreActionKernel (conjugate K₁ g) ∨ x * t ∈ coreActionKernel (conjugate K₁ g))) :=
    fun g hg x hx y hy hyC => by
      rw [(hpar g hg).1 x hx y hy]
      exact ⟨fun h => h.mpr (Or.inl hyC), fun h => ⟨fun _ => Or.inl hyC, fun _ => h⟩⟩
  have haL : a ∈ normalizer (L : Set G) := hSyl.1 (mem_inf.mp (mem_inf.mp ha).1).1
  have haS : a ∈ S := (mem_inf.mp (mem_inf.mp ha).1).1
  obtain ⟨g₂, hg₂, hk₂⟩ := hconj 1 hs1
  rw [he1'] at hk₂
  have hd1 : conjugate K₁ g₂ ≠ K₁ := by
    intro h
    have h' : g₂⁻¹ * e₁ * g₂ = e₁ := by
      have h'' := hsame g₂ hg₂ 1 hs1 (by rw [h, hc1])
      rwa [he1'] at h''
    rw [h', ← mul_assoc, inv_mul_cancel, one_mul] at hk₂
    exact haQ hk₂
  obtain ⟨s, hs, hsK, hsg⟩ : ∃ s ∈ S, conjugate K₁ s ≠ K₁ ∧ conjugate K₁ s ≠ conjugate K₁ g₂ := by
    rcases exists_of_three_avoiding h32.symm h42.symm h43.symm K₁ (conjugate K₁ g₂) with
      h | h | h
    · exact ⟨s₂, hs₂, h⟩
    · exact ⟨s₃, hs₃, h⟩
    · exact ⟨s₄, hs₄, h⟩
  obtain ⟨g', hg', hk₄⟩ := hconj s hs
  have hg₄ : s * g' ∈ S := mul_mem hs hg'
  rw [show g'⁻¹ * (s⁻¹ * e₁ * s) * g' = (s * g')⁻¹ * e₁ * (s * g') by group] at hk₄
  have hd3 : conjugate K₁ (s * g') ≠ conjugate K₁ s := by
    intro h
    rw [hsame _ hg₄ s hs h, ← mul_assoc, inv_mul_cancel, one_mul] at hk₄
    exact haQ hk₄
  set e₂ := g₂⁻¹ * e₁ * g₂ with he₂
  set e₃ := s⁻¹ * e₁ * s with he₃
  set e₄ := (s * g')⁻¹ * e₁ * (s * g') with he₄
  have hq : e₁ * e₂ * e₃ * e₄ ∈ coreActionKernel L := by
    have h1 := mul_mem (conj_mem_coreActionKernel haL (inv_mem hk₂)) (inv_mem hk₄)
    have heq : e₁ * e₂ * e₃ * e₄ = a * (e₂⁻¹ * (e₁ * a))⁻¹ * a⁻¹ * (e₄⁻¹ * (e₃ * a))⁻¹ := by
      calc e₁ * e₂ * e₃ * e₄ = e₁⁻¹ * e₂ * (a * a)⁻¹ * e₃⁻¹ * e₄ := by
            rw [ha2, inv_one, mul_one, inv_eq_of_mul_eq_one_right he₁2,
              inv_eq_of_mul_eq_one_right (hinv s)]
        _ = a * (e₂⁻¹ * (e₁ * a))⁻¹ * a⁻¹ * (e₄⁻¹ * (e₃ * a))⁻¹ := by group
    rw [heq]
    exact h1
  have hqQ : e₁ * e₂ * e₃ * e₄ ∈ S ⊓ coreActionKernel L := mem_inf.mpr
    ⟨mul_mem (mul_mem (mul_mem (mem_inf.mp he₁).1 (mem_inf.mp (hmem g₂ hg₂)).1)
      (mem_inf.mp (hmem s hs)).1) (mem_inf.mp (hmem _ hg₄)).1, hq⟩
  have hc12 : e₁ * e₂ = e₂ * e₁ := by
    have h := hcomm 1 hs1 g₂ hg₂
    rwa [he1'] at h
  have hc13 : e₁ * e₃ = e₃ * e₁ := by
    have h := hcomm 1 hs1 s hs
    rwa [he1'] at h
  have hc23 : e₂ * e₃ = e₃ * e₂ := hcomm g₂ hg₂ s hs
  have hd4 : conjugate K₁ (s * g') ≠ K₁ := by
    intro h
    have h' : e₄ = e₁ := by
      have h'' := hsame _ hg₄ 1 hs1 (by rw [h, hc1])
      rwa [he1'] at h''
    apply hpair g₂ hg₂ s hs 1 hs1 hsg.symm (hK1' g₂ hd1) (hK1' s hsK)
    have h5 : e₁ * e₂ * e₃ * e₄ = e₂ * e₃ := by
      rw [h']
      calc e₁ * e₂ * e₃ * e₁ = e₂ * e₁ * e₃ * e₁ := by rw [hc12]
        _ = e₂ * (e₁ * e₃) * e₁ := by group
        _ = e₂ * (e₃ * e₁) * e₁ := by rw [hc13]
        _ = e₂ * e₃ * (e₁ * e₁) := by group
        _ = e₂ * e₃ := by rw [he₁2, mul_one]
    rw [← h5]
    exact hq
  have hd5 : conjugate K₁ (s * g') ≠ conjugate K₁ g₂ := by
    intro h
    have h' : e₄ = e₂ := hsame _ hg₄ g₂ hg₂ h
    apply hpair 1 hs1 s hs g₂ hg₂ (hK1' s hsK) (hK1 g₂ hd1) hsg.symm
    rw [he1']
    have h5 : e₁ * e₂ * e₃ * e₄ = e₁ * e₃ := by
      rw [h']
      calc e₁ * e₂ * e₃ * e₂ = e₁ * (e₂ * e₃) * e₂ := by group
        _ = e₁ * (e₃ * e₂) * e₂ := by rw [hc23]
        _ = e₁ * e₃ * (e₂ * e₂) := by group
        _ = e₁ * e₃ := by rw [hinv g₂, mul_one]
    rw [← h5]
    exact hq
  refine ⟨g₂, hg₂, s, hs, s * g', hg₄, hd1, hsK, hd4, hsg, hd5, hd3, hq, fun g hg => ?_⟩
  by_cases hg1 : conjugate K₁ g = K₁
  · left
    have h := hsame g hg 1 hs1 (by rw [hg1, hc1])
    rwa [he1'] at h
  by_cases hg2 : conjugate K₁ g = conjugate K₁ g₂
  · exact Or.inr (Or.inl (hsame g hg g₂ hg₂ hg2))
  by_cases hg3 : conjugate K₁ g = conjugate K₁ s
  · exact Or.inr (Or.inr (Or.inl (hsame g hg s hs hg3)))
  by_cases hg4 : conjugate K₁ g = conjugate K₁ (s * g')
  · exact Or.inr (Or.inr (Or.inr (hsame g hg _ hg₄ hg4)))
  exfalso
  have he₁g : e₁ ∈ coreActionKernel (conjugate K₁ g) := by
    have h := hoth g hg 1 hs1 (hK1 g hg1)
    rwa [he1'] at h
  have hqg : e₁ * e₂ * e₃ * e₄ ∈ coreActionKernel (conjugate K₁ g) :=
    mul_mem (mul_mem (mul_mem he₁g (hoth g hg g₂ hg₂ hg2)) (hoth g hg s hs hg3))
      (hoth g hg _ hg₄ hg4)
  have h1 := (hPQ g hg 1 hs1 _ hqQ).mp (Or.inl hqg)
  have hN1 : e₁ ∈ S ⊓ normalizer (conjugate K₁ 1 : Set G) := by
    have h := hN 1 hs1 1 hs1
    rwa [he1'] at h
  have hN12 := mul_mem hN1 (hN 1 hs1 g₂ hg₂)
  have hN123 := mul_mem hN12 (hN 1 hs1 s hs)
  rw [hP2 1 hs1 _ hN123 _ (hN 1 hs1 _ hg₄) (hoth 1 hs1 _ hg₄ (hK1' _ hd4)),
    hP2 1 hs1 _ hN12 _ (hN 1 hs1 s hs) (hoth 1 hs1 s hs (hK1' s hsK)),
    hP2 1 hs1 _ hN1 _ (hN 1 hs1 g₂ hg₂) (hoth 1 hs1 g₂ hg₂ (hK1' g₂ hd1))] at h1
  apply hown 1 hs1
  rw [he1']
  exact h1

end CFSG.ComponentClassification.HSFLit.L34Uniq
