module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitPin
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SDefs

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem l34Lemma511OrbitStepC_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) :
    L34Lemma511OrbitStepC := by
  intro G _ _ L t S T hset u hu huc hall K₁ hK₁u hK₁p hK₁n s₂ hs₂ s₃ hs₃ s₄ hs₄ h2 h3 h4 h32
    h42 h43 e₁ he₁ he₁o hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, -, -, hSyl, htS, -, -⟩ := hset'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S)
    hu.1
  have huQ := not_mem_coreActionKernel_of_unbalancing hS hU hheld hSol hGW hMax hL34 hset hu
  obtain ⟨i, a, hua, htiQ, ha, ha2, haQ⟩ :=
    exists_mul_center_of_unbalancing hS hU hheld hSol hGW hMax hL34 hset hu huc
  have htiS : t ^ i ∈ S := (mem_inf.mp htiQ).1
  have htiL : t ^ i ∈ coreActionKernel L := (mem_inf.mp htiQ).2
  obtain ⟨g₂, hg₂, g₃, hg₃, g₄, hg₄, hd2, hd3, hd4, hd32, hd42, hd43, hq, horb⟩ :=
    exists_orbit_four hS hU hheld hSol hGW hMax hL34 hset hu huc hall hK₁u hK₁p hK₁n hs₂ hs₃
      hs₄ h2 h3 h4 h32 h42 h43 he₁ he₁o ha ha2 haQ
  have hcomp : ∀ g ∈ S, conjugate K₁ g ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 ((conjugate K₁ g).subgroupOf (centralizer ({u} : Set G))) ∧
      ¬ ⁅conjugate K₁ g, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn (conjugate K₁ g) :=
    fun g hg => conj_component hS hU hheld hSol hGW hMax hset hu huc hK₁u hK₁p hK₁n hg
  have hpar : ∀ g ∈ S, (∀ x ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
      ∀ y ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
        (x * y ∈ coreActionKernel (conjugate K₁ g) ∨
            x * y * t ∈ coreActionKernel (conjugate K₁ g)) ↔
          ((x ∈ coreActionKernel (conjugate K₁ g) ∨ x * t ∈ coreActionKernel (conjugate K₁ g)) ↔
            (y ∈ coreActionKernel (conjugate K₁ g) ∨
              y * t ∈ coreActionKernel (conjugate K₁ g)))) ∧
      (∀ q ∈ S ⊓ coreActionKernel L, (q ∈ coreActionKernel (conjugate K₁ g) ∨
          q * t ∈ coreActionKernel (conjugate K₁ g)) ↔ (q = 1 ∨ q = t)) ∧
      ∀ e ∈ S ⊓ conjugate K₁ g, orderOf e = 2 → ¬ (e ∈ coreActionKernel (conjugate K₁ g) ∨
        e * t ∈ coreActionKernel (conjugate K₁ g)) := fun g hg =>
    parity_of_component hS hU hheld hSol hGW hMax hL34 hset hu (hcomp g hg).1 (hcomp g hg).2.1
      (hcomp g hg).2.2 (hall _ (hcomp g hg).1 (hcomp g hg).2.1 (hcomp g hg).2.2)
  have he₁2 : e₁ * e₁ = 1 := by rw [← pow_two, ← he₁o, pow_orderOf_eq_one]
  have hmem : ∀ g ∈ S, g⁻¹ * e₁ * g ∈ S ⊓ conjugate K₁ g := by
    intro g hg
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) (mem_inf.mp he₁).1) hg, ?_⟩
    rw [mem_conjugate_iff, show g * (g⁻¹ * e₁ * g) * g⁻¹ = e₁ by group]
    exact (mem_inf.mp he₁).2
  have hinv : ∀ g : G, g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = 1 := by
    intro g
    rw [show g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = g⁻¹ * (e₁ * e₁) * g by group, he₁2]
    group
  have hne1 : ∀ g : G, g⁻¹ * e₁ * g ≠ 1 := fun g h => by
    have he₁1 : e₁ ≠ 1 := fun h' => by
      rw [h', orderOf_one] at he₁o
      exact absurd he₁o (by decide)
    apply he₁1
    calc e₁ = g * (g⁻¹ * e₁ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hord : ∀ g : G, orderOf (g⁻¹ * e₁ * g) = 2 := fun g =>
    orderOf_eq_prime (by rw [pow_two]; exact hinv g) (hne1 g)
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
  have hcomm : ∀ g ∈ S, ∀ h ∈ S, conjugate K₁ g ≠ conjugate K₁ h →
      g⁻¹ * e₁ * g * (h⁻¹ * e₁ * h) = h⁻¹ * e₁ * h * (g⁻¹ * e₁ * g) := fun g hg h hh hgh =>
    commute_of_ne (hcomp g hg).1 (hcomp h hh).1 (hcomp g hg).2.1 (hcomp h hh).2.1 hgh
      (GrS5.IsSylowTwoIn.isPGroup hSyl) (mem_inf.mp (hmem g hg)).1 (mem_inf.mp (hmem g hg)).2
      (mem_inf.mp (hmem h hh)).1 (mem_inf.mp (hmem h hh)).2
  have hs1 : (1 : G) ∈ S := one_mem _
  have hc1 : conjugate K₁ 1 = K₁ := conjugate_one K₁
  have he1' : (1 : G)⁻¹ * e₁ * 1 = e₁ := by group
  have hK1' : ∀ x, conjugate K₁ x ≠ K₁ → conjugate K₁ 1 ≠ conjugate K₁ x := fun x h => by
    rw [hc1]
    exact h.symm
  have hK1 : ∀ x, conjugate K₁ x ≠ K₁ → conjugate K₁ x ≠ conjugate K₁ 1 := fun x h => by
    rwa [hc1]
  have hεN : ∀ g ∈ S, ∀ h ∈ S, ∀ ε : G, (ε = 1 ∨ ε = h⁻¹ * e₁ * h) →
      ε ∈ S ⊓ normalizer (conjugate K₁ g : Set G) := by
    rintro g hg h hh ε (rfl | rfl)
    · exact one_mem _
    · exact hN g hg h hh
  have hεC : ∀ g ∈ S, ∀ h ∈ S, conjugate K₁ g ≠ conjugate K₁ h → ∀ ε : G,
      (ε = 1 ∨ ε = h⁻¹ * e₁ * h) → ε ∈ coreActionKernel (conjugate K₁ g) := by
    rintro g hg h hh hgh ε (rfl | rfl)
    · exact one_mem _
    · exact hoth g hg h hh hgh
  have hεP : ∀ g ∈ S, ∀ ε : G, (ε = 1 ∨ ε = g⁻¹ * e₁ * g) →
      ((ε ∈ coreActionKernel (conjugate K₁ g) ∨ ε * t ∈ coreActionKernel (conjugate K₁ g)) ↔
        ε = 1) := by
    rintro g hg ε (rfl | rfl)
    · exact ⟨fun _ => rfl, fun _ => Or.inl (one_mem _)⟩
    · exact ⟨fun h => absurd h ((hpar g hg).2.2 _ (hmem g hg) (hord g)),
        fun h => absurd h (hne1 g)⟩
  have hL : ∀ g ∈ S, ∀ x ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
      x ∈ coreActionKernel (conjugate K₁ g) → ∀ y ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
        ((x * y ∈ coreActionKernel (conjugate K₁ g) ∨
            x * y * t ∈ coreActionKernel (conjugate K₁ g)) ↔
          (y ∈ coreActionKernel (conjugate K₁ g) ∨ y * t ∈ coreActionKernel (conjugate K₁ g))) :=
    fun g hg x hx hxC y hy => by
      rw [(hpar g hg).1 x hx y hy]
      exact ⟨fun h => h.mp (Or.inl hxC), fun h => ⟨fun _ => h, fun _ => Or.inl hxC⟩⟩
  have hR : ∀ g ∈ S, ∀ x ∈ S ⊓ normalizer (conjugate K₁ g : Set G),
      ∀ y ∈ S ⊓ normalizer (conjugate K₁ g : Set G), y ∈ coreActionKernel (conjugate K₁ g) →
        ((x * y ∈ coreActionKernel (conjugate K₁ g) ∨
            x * y * t ∈ coreActionKernel (conjugate K₁ g)) ↔
          (x ∈ coreActionKernel (conjugate K₁ g) ∨ x * t ∈ coreActionKernel (conjugate K₁ g))) :=
    fun g hg x hx y hy hyC => by
      rw [(hpar g hg).1 x hx y hy]
      exact ⟨fun h => h.mpr (Or.inl hyC), fun h => ⟨fun _ => Or.inl hyC, fun _ => h⟩⟩
  have huK : ∀ g ∈ S, u ∈ coreActionKernel (conjugate K₁ g) := by
    intro g hg
    have hc : u ∈ centralizer ((conjugate K₁ g : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun k hk => mem_centralizer_singleton_iff.mp ((hcomp g hg).1 hk)
    refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ hc, fun j hj => ?_⟩
    have hjt : j * u = u * j := mem_centralizer_iff.mp hc j hj
    rw [show j⁻¹ * u⁻¹ * j * u = 1 by
      calc j⁻¹ * u⁻¹ * j * u = j⁻¹ * u⁻¹ * (j * u) := by group
        _ = j⁻¹ * u⁻¹ * (u * j) := by rw [hjt]
        _ = 1 := by group]
    exact one_mem _
  set e₂ := g₂⁻¹ * e₁ * g₂ with he₂
  set e₃ := g₃⁻¹ * e₁ * g₃ with he₃
  set e₄ := g₄⁻¹ * e₁ * g₄ with he₄
  have hc1 : ∀ g ∈ S, conjugate K₁ g ≠ K₁ → e₁ * (g⁻¹ * e₁ * g) = g⁻¹ * e₁ * g * e₁ :=
    fun g hg hgK => by
      have h := hcomm 1 hs1 g hg (hK1' g hgK)
      rwa [he1'] at h
  have hEJ : closure (conjSet S e₁) ≤ zpowers e₁ ⊔ (zpowers e₂ ⊔ (zpowers e₃ ⊔ zpowers e₄)) := by
    rw [closure_le]
    rintro x ⟨g, hg, rfl⟩
    rcases horb g hg with h | h | h | h <;> rw [SetLike.mem_coe, h]
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_sup_left (mem_zpowers _))
    · exact mem_sup_right (mem_sup_right (mem_sup_left (mem_zpowers _)))
    · exact mem_sup_right (mem_sup_right (mem_sup_right (mem_zpowers _)))
  have hJS : ∀ g ∈ S, zpowers e₁ ⊔ (zpowers e₂ ⊔ (zpowers e₃ ⊔ zpowers e₄)) ≤
      S ⊓ normalizer (conjugate K₁ g : Set G) := by
    intro g hg
    have h1 : e₁ ∈ S ⊓ normalizer (conjugate K₁ g : Set G) := by
      have h := hN g hg 1 hs1
      rwa [he1'] at h
    exact sup_le (zpowers_le.mpr h1) (sup_le (zpowers_le.mpr (hN g hg g₂ hg₂))
      (sup_le (zpowers_le.mpr (hN g hg g₃ hg₃)) (zpowers_le.mpr (hN g hg g₄ hg₄))))
  have hES : closure (conjSet S e₁) ≤ S := hEJ.trans ((hJS 1 hs1).trans inf_le_left)
  have hQN : closure (conjSet S e₁) ≤
      normalizer ((S ⊓ coreActionKernel L : Subgroup G) : Set G) := fun x hx =>
    L34Inv.mem_normalizer_inf' (le_normalizer (hES hx))
      (normalizer_le_normalizer_coreActionKernel L (hSyl.1 (hES hx)))
  have huEQ : u ∈ ((closure (conjSet S e₁) ⊔ S ⊓ coreActionKernel L : Subgroup G) : Set G) := by
    rw [hua]
    exact mul_mem (mem_sup_right (mem_inf.mpr ⟨htiS, htiL⟩)) (hZ ha)
  rw [coe_mul_of_left_le_normalizer_right _ _ hQN] at huEQ
  obtain ⟨e, heE, q, hqQ, heq⟩ := huEQ
  obtain ⟨ε₁, ε₂, ε₃, ε₄, hε₁, hε₂, hε₃, hε₄, rfl⟩ := decomp_four_involutions he₁2 (hinv g₂)
    (hinv g₃) (hinv g₄) (hc1 g₂ hg₂ hd2) (hc1 g₃ hg₃ hd3) (hc1 g₄ hg₄ hd4)
    (hcomm g₂ hg₂ g₃ hg₃ hd32.symm) (hcomm g₂ hg₂ g₄ hg₄ hd42.symm)
    (hcomm g₃ hg₃ g₄ hg₄ hd43.symm) (hEJ heE)
  have hε₁' : ε₁ = 1 ∨ ε₁ = 1⁻¹ * e₁ * 1 := by rwa [he1']
  have hPe : ∀ g ∈ S, ((ε₁ * (ε₂ * (ε₃ * ε₄)) ∈ coreActionKernel (conjugate K₁ g) ∨
      ε₁ * (ε₂ * (ε₃ * ε₄)) * t ∈ coreActionKernel (conjugate K₁ g)) ↔ (q⁻¹ = 1 ∨ q⁻¹ = t)) := by
    intro g hg
    have heJ := hJS g hg (hEJ heE)
    have hu' : u ∈ S ⊓ normalizer (conjugate K₁ g : Set G) :=
      mem_inf.mpr ⟨huS, (mem_coreActionKernel.mp (huK g hg)).1⟩
    have hq' : q⁻¹ ∈ S ⊓ normalizer (conjugate K₁ g : Set G) := by
      rw [show q⁻¹ = u⁻¹ * (ε₁ * (ε₂ * (ε₃ * ε₄))) by rw [← heq]; group]
      exact mul_mem (inv_mem hu') heJ
    rw [show ε₁ * (ε₂ * (ε₃ * ε₄)) = u * q⁻¹ by rw [← heq]; group, (hpar g hg).1 u hu' q⁻¹ hq',
      (hpar g hg).2.1 q⁻¹ (inv_mem hqQ)]
    exact ⟨fun h => h.mp (Or.inl (huK g hg)), fun h => ⟨fun _ => h, fun _ => Or.inl (huK g hg)⟩⟩
  have hN1 := fun g (hg : g ∈ S) => hεN g hg 1 hs1 ε₁ hε₁'
  have hP₁ : ε₁ = 1 ↔ (q⁻¹ = 1 ∨ q⁻¹ = t) := by
    have h := hPe 1 hs1
    rw [hR 1 hs1 ε₁ (hN1 1 hs1) _ (mul_mem (hεN 1 hs1 g₂ hg₂ ε₂ hε₂)
      (mul_mem (hεN 1 hs1 g₃ hg₃ ε₃ hε₃) (hεN 1 hs1 g₄ hg₄ ε₄ hε₄)))
      (mul_mem (hεC 1 hs1 g₂ hg₂ (hK1' g₂ hd2) ε₂ hε₂) (mul_mem
        (hεC 1 hs1 g₃ hg₃ (hK1' g₃ hd3) ε₃ hε₃) (hεC 1 hs1 g₄ hg₄ (hK1' g₄ hd4) ε₄ hε₄))),
      hεP 1 hs1 ε₁ hε₁'] at h
    exact h
  have hP₂ : ε₂ = 1 ↔ (q⁻¹ = 1 ∨ q⁻¹ = t) := by
    have h := hPe g₂ hg₂
    rw [hL g₂ hg₂ ε₁ (hN1 g₂ hg₂) (hεC g₂ hg₂ 1 hs1 (hK1 g₂ hd2) ε₁ hε₁') _
      (mul_mem (hεN g₂ hg₂ g₂ hg₂ ε₂ hε₂)
        (mul_mem (hεN g₂ hg₂ g₃ hg₃ ε₃ hε₃) (hεN g₂ hg₂ g₄ hg₄ ε₄ hε₄))),
      hR g₂ hg₂ ε₂ (hεN g₂ hg₂ g₂ hg₂ ε₂ hε₂) _
        (mul_mem (hεN g₂ hg₂ g₃ hg₃ ε₃ hε₃) (hεN g₂ hg₂ g₄ hg₄ ε₄ hε₄))
        (mul_mem (hεC g₂ hg₂ g₃ hg₃ hd32.symm ε₃ hε₃) (hεC g₂ hg₂ g₄ hg₄ hd42.symm ε₄ hε₄)),
      hεP g₂ hg₂ ε₂ hε₂] at h
    exact h
  have hP₃ : ε₃ = 1 ↔ (q⁻¹ = 1 ∨ q⁻¹ = t) := by
    have h := hPe g₃ hg₃
    rw [hL g₃ hg₃ ε₁ (hN1 g₃ hg₃) (hεC g₃ hg₃ 1 hs1 (hK1 g₃ hd3) ε₁ hε₁') _
      (mul_mem (hεN g₃ hg₃ g₂ hg₂ ε₂ hε₂)
        (mul_mem (hεN g₃ hg₃ g₃ hg₃ ε₃ hε₃) (hεN g₃ hg₃ g₄ hg₄ ε₄ hε₄))),
      hL g₃ hg₃ ε₂ (hεN g₃ hg₃ g₂ hg₂ ε₂ hε₂) (hεC g₃ hg₃ g₂ hg₂ hd32 ε₂ hε₂) _
        (mul_mem (hεN g₃ hg₃ g₃ hg₃ ε₃ hε₃) (hεN g₃ hg₃ g₄ hg₄ ε₄ hε₄)),
      hR g₃ hg₃ ε₃ (hεN g₃ hg₃ g₃ hg₃ ε₃ hε₃) ε₄ (hεN g₃ hg₃ g₄ hg₄ ε₄ hε₄)
        (hεC g₃ hg₃ g₄ hg₄ hd43.symm ε₄ hε₄), hεP g₃ hg₃ ε₃ hε₃] at h
    exact h
  have hP₄ : ε₄ = 1 ↔ (q⁻¹ = 1 ∨ q⁻¹ = t) := by
    have h := hPe g₄ hg₄
    rw [hL g₄ hg₄ ε₁ (hN1 g₄ hg₄) (hεC g₄ hg₄ 1 hs1 (hK1 g₄ hd4) ε₁ hε₁') _
      (mul_mem (hεN g₄ hg₄ g₂ hg₂ ε₂ hε₂)
        (mul_mem (hεN g₄ hg₄ g₃ hg₃ ε₃ hε₃) (hεN g₄ hg₄ g₄ hg₄ ε₄ hε₄))),
      hL g₄ hg₄ ε₂ (hεN g₄ hg₄ g₂ hg₂ ε₂ hε₂) (hεC g₄ hg₄ g₂ hg₂ hd42 ε₂ hε₂) _
        (mul_mem (hεN g₄ hg₄ g₃ hg₃ ε₃ hε₃) (hεN g₄ hg₄ g₄ hg₄ ε₄ hε₄)),
      hL g₄ hg₄ ε₃ (hεN g₄ hg₄ g₃ hg₃ ε₃ hε₃) (hεC g₄ hg₄ g₃ hg₃ hd43 ε₃ hε₃) ε₄
        (hεN g₄ hg₄ g₄ hg₄ ε₄ hε₄), hεP g₄ hg₄ ε₄ hε₄] at h
    exact h
  apply huQ
  rw [← heq]
  refine mul_mem ?_ (mem_inf.mp hqQ).2
  by_cases hcc : q⁻¹ = 1 ∨ q⁻¹ = t
  · rw [hP₁.mpr hcc, hP₂.mpr hcc, hP₃.mpr hcc, hP₄.mpr hcc, one_mul, one_mul, one_mul]
    exact one_mem _
  · rw [hε₁.resolve_left fun h => hcc (hP₁.mp h), hε₂.resolve_left fun h => hcc (hP₂.mp h),
      hε₃.resolve_left fun h => hcc (hP₃.mp h), hε₄.resolve_left fun h => hcc (hP₄.mp h)]
    have h := hq
    rwa [mul_assoc, mul_assoc] at h

end CFSG.ComponentClassification.HSFLit.L34Uniq
