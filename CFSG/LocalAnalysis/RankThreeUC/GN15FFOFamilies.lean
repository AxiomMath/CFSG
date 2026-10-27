module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFODispatch
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOffender
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutNormal
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Component
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOBase
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Cooperstein.Coordinator
open scoped commutatorElement

namespace FFO

@[expose] def InvertsOddOn (Fam : (Y : Type) → [Group Y] → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W), Function.Injective ρ → CFSG.Open.IsKGroup G →
    CFSG.pCore 2 G = ⊥ → ∀ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A →
    CFSG.RankThree.FFModules.IsBestOffender ρ A → ∀ L : Subgroup G,
    CFSG.Open.IsComponentOf L ⊤ → A ≤ Subgroup.normalizer (L : Set G) → ⁅L, A⁆ = L →
    ∀ a ∈ A, a ∉ L ⊔ Subgroup.centralizer (L : Set G) →
    ∀ y ∈ Subgroup.normalizer (L : Set G), a * y * a⁻¹ = y⁻¹ →
      ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e →
        y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G) →
        (r ≠ 3 → ¬ A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) →
          Fam (↥L ⧸ Subgroup.center ↥L) r → y ∈ L ⊔ Subgroup.centralizer (L : Set G)

end FFO

@[expose] def FFOffenderInvertsOddPSL : Prop := FFO.InvertsOddOn FFO.FamPSL

@[expose] def FFOffenderInvertsOddPSU : Prop := FFO.InvertsOddOn FFO.FamPSU

@[expose] def FFOffenderInvertsOddD4 : Prop := FFO.InvertsOddOn FFO.FamD4

namespace FFO

variable {G : Type} [Group G]

theorem mem_of_inverter_mem {L : Subgroup G} {a y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (ha : a ∈ L ⊔ Subgroup.centralizer (L : Set G))
    (hinv : a * y * a⁻¹ = y⁻¹) {r e : ℕ} (hr2 : r ≠ 2) (hr : r.Prime) (hord : y ^ (r ^ e) = 1) :
    y ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have h1 := JOut.commutator_mem_sup_centralizer_of_mem hy ha
  have h2 : ⁅y, a⁆ = y ^ 2 := by
    have : a * y⁻¹ * a⁻¹ = y := by
      have := congrArg (·⁻¹) hinv
      simpa [mul_assoc] using this
    rw [commutatorElement_def]
    calc y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
      _ = y ^ 2 := by rw [this, pow_two]
  rw [h2] at h1
  have hodd : Odd (r ^ e) := (hr.odd_of_ne_two hr2).pow
  obtain ⟨m, hm⟩ := hodd
  have : y = (y ^ 2) ^ (m + 1) := by
    have e1 : (y ^ 2) ^ (m + 1) = y ^ (r ^ e) * y := by
      rw [← pow_mul, hm, ← pow_succ]
      congr 1
    rw [e1, hord, one_mul]
  rw [this]
  exact pow_mem h1 _

end FFO

theorem ffOffenderInvertsOdd_of_families
    (hFF : FFModuleTheorem) (hPSL : FFOffenderInvertsOddPSL) (hPSU : FFOffenderInvertsOddPSU)
    (hD4 : FFOffenderInvertsOddD4) : FFOffenderInvertsOdd := by
  intro G _ _ W _ _ _ ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha y hy hinv r e hr hr2 hord
  by_contra hyK
  have : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := hL.2.2.2
    have := hs.toNontrivial
    have : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
    have : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    exact not_subsingleton _ ‹_›
  have hLne : ⁅L, A⁆ ≠ ⊥ := by rw [hLA]; exact hLbot
  have hFFc := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_component hFF G W ρ
    hρ hK hO2 A hAel hAb L hL hLne
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hAN ha
  have hy1 : y ^ (r ^ e) = 1 := by rw [← hord]; exact pow_orderOf_eq_one y
  have haK : a ∉ L ⊔ Subgroup.centralizer (L : Set G) := fun haK =>
    hyK (FFO.mem_of_inverter_mem hy haK hinv hr2 hr hy1)
  obtain ⟨k, hk1, hk2⟩ := FFO.exists_pow_not_mem_pow_mem hord hyK
  have hy'N : y ^ (r ^ k) ∈ Subgroup.normalizer (L : Set G) := pow_mem hy _
  have hinv' : a * y ^ (r ^ k) * a⁻¹ = (y ^ (r ^ k))⁻¹ := FFO.conj_pow_eq_inv hinv _
  obtain ⟨j, -, hord'⟩ := (Nat.dvd_prime_pow hr).1 (hord ▸ orderOf_pow_dvd (x := y) (r ^ k))
  have hnn : r ≠ 3 → ¬ A ≤ Subgroup.normalizer (Subgroup.zpowers (y ^ (r ^ k)) : Set G) :=
    fun hr3 hAy => hk1 (by
      have hodd : Odd (orderOf (y ^ (r ^ k))) := by
        rw [hord']
        exact (hr.odd_of_ne_two hr2).pow
      have h3 : ¬ 3 ∣ orderOf (y ^ (r ^ k)) := by
        rw [hord']
        intro h
        exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      rw [eq_one_of_inverted_of_normalizes hρ hAel hAb hodd h3 hAy ha hinv']
      exact one_mem _)
  rcases FFO.outer_cases hr hr2 hFFc with hc | hN | hC | hF | hF | hF
  · exact hyK (FFO.mem_of_outer_commutative hc haN hy hinv hr2 hr hy1)
  · exact FFO.false_of_outPNice hr hr2 hN haN hy'N hinv' hk2 hk1
  · exact FFO.false_of_outPCentral hr hr2 hC haN hy'N hinv' hk2 hk1
  · exact hk1 (hPSL G W ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK _ hy'N hinv' r j hr hr2 hord'
      hk2 hnn hF)
  · exact hk1 (hPSU G W ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK _ hy'N hinv' r j hr hr2 hord'
      hk2 hnn hF)
  · exact hk1 (hD4 G W ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK _ hy'N hinv' r j hr hr2 hord'
      hk2 hnn hF)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
