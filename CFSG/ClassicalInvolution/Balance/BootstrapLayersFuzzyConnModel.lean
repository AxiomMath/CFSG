module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnLink
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyModel

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement MatrixGroups

section Central

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_of_central_lifts (hp2 : p ≠ 2)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (hfund : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e) {X : Type} [Group X]
    (ψ : (modelUniv t n p e Fact.out).K →* X) (hker : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {w₁ w₂ : (modelUniv t n p e Fact.out).K} (hw₁ : w₁ ∈ R₁) (hw₂ : w₂ ∈ R₂)
    (hc₁ : ∀ r ∈ R₁, w₁ * r = r * w₁) (hc₂ : ∀ r ∈ R₂, w₂ * r = r * w₂) (h₁ : ψ w₁ ≠ 1)
    (h₂ : ψ w₂ ≠ 1) (hsq₁ : ψ w₁ * ψ w₁ = 1) (hsq₂ : ψ w₂ * ψ w₂ = 1) :
    ∃ g : (modelUniv t n p e Fact.out).K, g * w₁ * g⁻¹ = w₂ := by
  have hne₁ : w₁ ≠ 1 := fun h => h₁ (by rw [h, map_one])
  have hne₂ : w₂ ≠ 1 := fun h => h₂ (by rw [h, map_one])
  by_cases hspecial : t = .G2 ∨ t = .trialityD4
  · have hne : ¬ (t = .PSL ∧ n = 2) := by
      rintro ⟨h, -⟩
      rcases hspecial with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
    have hMFZ := ModelFacts.fundNoncentral_generic p t n e hfund hadm hne
    have hsq : ∀ {R : Subgroup (modelUniv t n p e Fact.out).K},
        R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D →
        ∀ {w : (modelUniv t n p e Fact.out).K}, w ∈ R → ψ w * ψ w = 1 → w * w = 1 := by
      intro R hR w hwR hψ
      have hcen : w * w ∈ Subgroup.center (modelUniv t n p e Fact.out).K :=
        hker (by rw [MonoidHom.mem_ker, map_mul, hψ])
      refine hMFZ R hR (w * w) (R.mul_mem hwR hwR) fun y => ?_
      have := Subgroup.mem_center_iff.mp hcen y
      have h2 : w * w * y * (w * w)⁻¹ * y⁻¹ = 1 := by
        rw [← this]
        group
      rw [h2]
      exact one_mem _
    exact twoClassInvolutionsConj p t n e hp2 hspecial hadm R₁ hR₁ R₂ hR₂ w₁ hw₁ w₂ hw₂
      (hsq hR₁ hw₁ hsq₁) (hsq hR₂ hw₂ hsq₂) hne₁ hne₂ hc₁ hc₂
  · rw [not_or] at hspecial
    obtain ⟨hG2, hD4⟩ := hspecial
    obtain ⟨g, hg⟩ : ∃ g : (modelUniv t n p e Fact.out).K, R₂ = conjSub g R₁ :=
      ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm hG2 hD4 R₁ hR₁ R₂ hR₂
    obtain ⟨ε⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
      hR₁
    have hw'R : g⁻¹ * w₂ * g ∈ R₁ := by
      have : w₂ ∈ conjSub g R₁ := hg ▸ hw₂
      exact mem_conjSub_iff.mp this
    have hc' : ∀ r ∈ R₁, (g⁻¹ * w₂ * g) * r = r * (g⁻¹ * w₂ * g) := by
      intro r hr
      have hmem : g * r * g⁻¹ ∈ R₂ := by
        rw [hg]
        exact conj_mem_conjSub hr
      have := hc₂ _ hmem
      calc (g⁻¹ * w₂ * g) * r = g⁻¹ * (w₂ * (g * r * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r * g⁻¹) * w₂) * g := by rw [this]
        _ = r * (g⁻¹ * w₂ * g) := by group
    have hcentral : ∀ {w : (modelUniv t n p e Fact.out).K} (hw : w ∈ R₁),
        (∀ r ∈ R₁, w * r = r * w) → ε ⟨w, hw⟩ = 1 ∨ ε ⟨w, hw⟩ = -1 := by
      intro w hw hc
      refine (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp ?_
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨r, rfl⟩ := ε.surjective s
      rw [← map_mul, ← map_mul]
      exact congrArg ε (Subtype.ext (hc r.1 r.2).symm)
    have hneg : ∀ {w : (modelUniv t n p e Fact.out).K} (hw : w ∈ R₁), w ≠ 1 →
        (∀ r ∈ R₁, w * r = r * w) → ε ⟨w, hw⟩ = -1 := by
      intro w hw hw1 hc
      rcases hcentral hw hc with h | h
      · exfalso
        apply hw1
        have : (⟨w, hw⟩ : R₁) = 1 := ε.injective (by rw [h, map_one])
        exact congrArg Subtype.val this
      · exact h
    have hw'1 : g⁻¹ * w₂ * g ≠ 1 := by
      intro h
      apply hne₂
      calc w₂ = g * (g⁻¹ * w₂ * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h1 := hneg hw₁ hne₁ hc₁
    have h2 := hneg hw'R hw'1 hc'
    have hεeq : (⟨w₁, hw₁⟩ : R₁) = ⟨g⁻¹ * w₂ * g, hw'R⟩ := ε.injective (h1.trans h2.symm)
    have hw : w₁ = g⁻¹ * w₂ * g := congrArg Subtype.val hεeq
    exact ⟨g, by rw [hw]; group⟩

end Central

section OddQuotInvolutions

variable {G : Type} [Group G] {a : G}

theorem oddQuotMk_sq_eq_one {z : G} (hzC : z ∈ Subgroup.centralizer ({a} : Set G))
    (hz : z * z = 1) : oddQuotMk a ⟨z, hzC⟩ * oddQuotMk a ⟨z, hzC⟩ = 1 := by
  rw [← map_mul]
  have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z, hzC⟩ = 1 := Subtype.ext hz
  rw [this, map_one]

theorem oddQuotMk_ne_one [Finite G] {z : G} (hzC : z ∈ Subgroup.centralizer ({a} : Set G))
    (hz : z * z = 1) (hz1 : z ≠ 1) : oddQuotMk a ⟨z, hzC⟩ ≠ 1 := fun h =>
  hz1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz) h))

end OddQuotInvolutions

section Transport

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem SecData.exists_conj_of_vertices (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (hp2 : p ≠ 2) (j : Fin D.card) (h4 : 4 ≤ p ^ D.exp j) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (hK₁ : K₁ ∈ Φ) (hK₂ : K₂ ∈ Φ) (hz₁ : IsCentralInvolution K₁ z₁)
    (hz₂ : IsCentralInvolution K₂ z₂)
    (h₁ : modOdd a K₁ ≤ (secComponentHom hs.normalizes D j).range)
    (h₂ : modOdd a K₂ ≤ (secComponentHom hs.normalizes D j).range) :
    ∃ (g : G) (hg : g ∈ Subgroup.centralizer ({a} : Set G)),
      oddQuotMk a ⟨g, hg⟩ ∈ (secComponentHom hs.normalizes D j).range ∧ g * z₁ * g⁻¹ = z₂ := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set ψ := secComponentHom hs.normalizes D j with hψ
  have hC₁ : K₁ ≤ C := hs.le K₁ hK₁
  have hC₂ : K₂ ≤ C := hs.le K₂ hK₂
  have hz₁C : z₁ ∈ C := hC₁ hz₁.mem
  have hz₂C : z₂ ∈ C := hC₂ hz₂.mem
  obtain ⟨R₁, hR₁, hR₁K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hK₁, hC₁⟩ h₁
  obtain ⟨R₂, hR₂, hR₂K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hK₂, hC₂⟩ h₂
  have hperf := ModelFacts.fundPerfect_core (D.tag j) (D.rank j) p (D.exp j) hp2 (D.isFundTag j)
    (D.admissible j) h4
  obtain ⟨w₁, hw₁R, hw₁, hw₁c⟩ := hs.exists_central_lift D j hz₁ hz₁C hR₁K
    (commutator_self_eq_of_le (hperf R₁ hR₁))
  obtain ⟨w₂, hw₂R, hw₂, hw₂c⟩ := hs.exists_central_lift D j hz₂ hz₂C hR₂K
    (commutator_self_eq_of_le (hperf R₂ hR₂))
  have hne₁ : ψ w₁ ≠ 1 := by
    rw [hw₁]
    exact oddQuotMk_ne_one hz₁C hz₁.sq hz₁.ne_one
  have hne₂ : ψ w₂ ≠ 1 := by
    rw [hw₂]
    exact oddQuotMk_ne_one hz₂C hz₂.sq hz₂.ne_one
  obtain ⟨g₀, hg₀⟩ := exists_conj_of_central_lifts hp2 (D.isFundTag j) (D.admissible j) ψ
    (secComponentHom_ker_le_center hs.normalizes D j) hR₁ hR₂ hw₁R hw₂R hw₁c hw₂c hne₁ hne₂
    (by rw [hw₁]; exact oddQuotMk_sq_eq_one hz₁C hz₁.sq)
    (by rw [hw₂]; exact oddQuotMk_sq_eq_one hz₂C hz₂.sq)
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore ↥C) (ψ g₀)
  have hc' : oddQuotMk a c = ψ g₀ := hc
  have himg : oddQuotMk a (c * ⟨z₁, hz₁C⟩ * c⁻¹) = oddQuotMk a ⟨z₂, hz₂C⟩ := by
    have h1 := congrArg ψ hg₀
    rw [map_mul, map_mul, map_inv, hw₁, hw₂, ← hc'] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hmem : ((c : G) * z₁ * (c : G)⁻¹)⁻¹ * z₂ ∈ oddCoreIn C :=
    ⟨_, QuotientGroup.eq.mp himg, rfl⟩
  have hx2 : (c : G) * z₁ * (c : G)⁻¹ * ((c : G) * z₁ * (c : G)⁻¹) = 1 := by
    calc (c : G) * z₁ * (c : G)⁻¹ * ((c : G) * z₁ * (c : G)⁻¹)
        = (c : G) * (z₁ * z₁) * (c : G)⁻¹ := by group
      _ = 1 := by rw [hz₁.sq]; group
  obtain ⟨y, hy, hyc⟩ := exists_mem_oddCoreIn_conj_eq (X := C) hx2 hz₂.sq hmem
  have hyC : y ∈ C := oddCoreIn_le C hy
  refine ⟨y * c, C.mul_mem hyC c.2, ?_, ?_⟩
  · have : oddQuotMk a ⟨y * c, C.mul_mem hyC c.2⟩ = oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a c := by
      rw [← map_mul]
      rfl
    rw [this, oddQuotMk_eq_one_of_mem_oddCoreIn hy hyC, one_mul, hc']
    exact MonoidHom.mem_range.mpr ⟨g₀, rfl⟩
  · calc y * c * z₁ * (y * c)⁻¹ = y * ((c : G) * z₁ * (c : G)⁻¹) * y⁻¹ := by group
      _ = z₂ := hyc

end Transport

end CFSG.ClassicalInvolution.Balance.Bootstrap
