module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionReduction
public import CFSG.HardMathSupport.Lang.Coordinator.ONanOuterSylowCyc
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.Open (IsCatalogGroup StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Blueprint (ChevalleyExceptionalModel classicalTags chevalleyExceptionalTags)
open CFSG.AGLEmbedding.OuterSylow (mem_inner_of_lie_model_cyc mem_inner_of_not_dvd_card_outer)

section Residues

@[expose] def N1PSL : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ), StatedClassicalModel K .PSL n ℓ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p ∣ ℓ ^ f - 1 →
      ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f - 1) →
      ∀ S : Subgroup K, IsPGroup p S → ¬ p ∣ S.index → ¬ IsMulCommutative S

@[expose] def N1PSU : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ), StatedClassicalModel K .PSU n ℓ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p ∣ ℓ ^ f + 1 →
      ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f + 1) →
      ∀ S : Subgroup K, IsPGroup p S → ¬ p ∣ S.index → ¬ IsMulCommutative S

@[expose] def N1E6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), ChevalleyExceptionalModel K .E6 ℓ f →
    3 ∣ ℓ ^ f - 1 →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → ¬ IsMulCommutative S

@[expose] def N1TwE6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), ChevalleyExceptionalModel K .twistedE6 ℓ f →
    3 ∣ ℓ ^ f + 1 →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → ¬ IsMulCommutative S

@[expose] def N1D4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), StatedClassicalModel K .POmegaPlus 4 ℓ f →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → ¬ IsMulCommutative S

@[expose] def N13D4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), ChevalleyExceptionalModel K .trialityD4 ℓ f →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → ¬ IsMulCommutative S

@[expose] def SP3PSL : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), StatedClassicalModel K .PSL 3 ℓ f →
    3 ∣ ℓ ^ f - 1 → ¬ 9 ∣ ℓ ^ f - 1 →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → IsMulCommutative S →
    ∀ α : MulAut K, α ^ 3 = 1 → (∀ s ∈ S, α s = s) → α ∈ inner K

@[expose] def SP3PSU : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), StatedClassicalModel K .PSU 3 ℓ f →
    3 ∣ ℓ ^ f + 1 → ¬ 9 ∣ ℓ ^ f + 1 →
    ∀ S : Subgroup K, IsPGroup 3 S → ¬ 3 ∣ S.index → IsMulCommutative S →
    ∀ α : MulAut K, α ^ 3 = 1 → (∀ s ∈ S, α s = s) → α ∈ inner K

end Residues

@[expose] def ReducedOuterSylowAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K →
    ∀ S : Subgroup K, IsPGroup p S → ¬ p ∣ S.index → IsMulCommutative S →
    ∀ α : MulAut K, α ^ p = 1 → (∀ s ∈ S, α s = s) → α ∈ inner K

theorem apply_eq_of_commute_conj {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) {α : MulAut K}
    {s : K} (h : α * MulAut.conj s = MulAut.conj s * α) : α s = s := by
  have key : ∀ z : K, α s * z * (α s)⁻¹ = s * z * s⁻¹ := by
    intro z
    obtain ⟨y, rfl⟩ := α.surjective z
    have := congrArg (fun β : MulAut K => β y) h
    simpa [MulAut.conj_apply, map_mul, map_inv] using this
  have hc : s⁻¹ * α s ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : (s⁻¹ * α s) * z * (s⁻¹ * α s)⁻¹ = z := by
      calc (s⁻¹ * α s) * z * (s⁻¹ * α s)⁻¹ = s⁻¹ * (α s * z * (α s)⁻¹) * s := by group
        _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [key z]
        _ = z := by group
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem kFactInnerAction_of_reduced (hred : ReducedOuterSylowAbelian) : KFactInnerAction := by
  intro p hp hp2 K _ _ hs hnab hcat P hP hab φ hφ hc
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  by_cases hin : φ ∈ inner K
  · exact exists_eq_conj_of_mem_inner hZ P hφ hc hin
  · exfalso
    obtain ⟨α, hαp, hαout, hαc⟩ := exists_outer_order_p_of_outer_centralizes hs hnab P hab hφ hc hin
    have hpK : p ∣ Nat.card K := by
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hP
        rw [pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      exact (dvd_pow_self p hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup K))
    exact hαout (hred K hs hnab hcat p hp hp2 hpK P P.isPGroup' (Sylow.not_dvd_index P) hab α hαp
      (fun s hs' => apply_eq_of_commute_conj hZ (hαc s hs')))

theorem cases_of_dvd_lieOrderDivisor {t : StatedLieTag} {n q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ lieOrderDivisor t n q) :
    (t = .PSL ∧ p ∣ n ∧ p ∣ q - 1) ∨ (t = .PSU ∧ p ∣ n ∧ p ∣ q + 1) ∨
      (t = .E6 ∧ p = 3 ∧ 3 ∣ q - 1) ∨ (t = .twistedE6 ∧ p = 3 ∧ 3 ∣ q + 1) := by
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h4 : ¬ p ∣ 4 := fun h => h2 (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))
  have hp1 : ¬ p ∣ 1 := hp.not_dvd_one
  cases t <;> simp only [lieOrderDivisor] at h
  · exact Or.inl ⟨rfl, h.trans (Nat.gcd_dvd_left _ _), h.trans (Nat.gcd_dvd_right _ _)⟩
  · exact Or.inr (Or.inl ⟨rfl, h.trans (Nat.gcd_dvd_left _ _), h.trans (Nat.gcd_dvd_right _ _)⟩)
  · exact absurd (h.trans (Nat.gcd_dvd_left _ _)) h2
  · exact absurd h h2
  · exact absurd (h.trans (Nat.gcd_dvd_left _ _)) h4
  · exact absurd (h.trans (Nat.gcd_dvd_left _ _)) h4
  · exact absurd h hp1
  · exact absurd h hp1
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (h.trans (Nat.gcd_dvd_left _ _))
    subst hp3
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h.trans (Nat.gcd_dvd_right _ _)⟩))
  · exact absurd (h.trans (Nat.gcd_dvd_left _ _)) h2
  · exact absurd h hp1
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (h.trans (Nat.gcd_dvd_left _ _))
    subst hp3
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h.trans (Nat.gcd_dvd_right _ _)⟩))
  · exact absurd h hp1
  · exact absurd h hp1
  · exact absurd h hp1
  · exact absurd h hp1
  · exact absurd h hp1

theorem mem_inner_of_lie_model_abelian (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc)
    (hPSL : N1PSL) (hPSU : N1PSU) (hE6 : N1E6) (hTwE6 : N1TwE6) (hD4 : N1D4) (h3D4 : N13D4)
    (hSPL : SP3PSL) (hSPU : SP3PSU)
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) (hmodel : CFSG.Blueprint.LieModel K t n ℓ f)
    (ht : t ≠ .Tits) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K)
    {S : Subgroup K} (hS : IsPGroup p S) (hSidx : ¬ p ∣ S.index) (hab : IsMulCommutative S)
    {α : MulAut K} (hαp : α ^ p = 1) (hαS : ∀ s ∈ S, α s = s) : α ∈ inner K := by
  have hcl : t ∈ classicalTags → StatedClassicalModel K t n ℓ f := hmodel.statedClassicalModel
  have hch : t ∈ chevalleyExceptionalTags → ChevalleyExceptionalModel K t ℓ f :=
    hmodel.chevalleyExceptionalModel
  by_cases hdiv : p ∣ lieOrderDivisor t n (ℓ ^ f)
  · rcases cases_of_dvd_lieOrderDivisor hp hp2 hdiv with
      ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩ | ⟨rfl, rfl, h3⟩ | ⟨rfl, rfl, h3⟩
    · have hcl' := hcl (by simp [classicalTags])
      by_cases hspec : n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f - 1
      · obtain ⟨rfl, rfl, h9⟩ := hspec
        exact hSPL K ℓ f hcl' hpq h9 S hS hSidx hab α hαp hαS
      · exact absurd hab (hPSL K n ℓ f hcl' p hp hp2 hpn hpq hspec S hS hSidx)
    · have hcl' := hcl (by simp [classicalTags])
      by_cases hspec : n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f + 1
      · obtain ⟨rfl, rfl, h9⟩ := hspec
        exact hSPU K ℓ f hcl' hpq h9 S hS hSidx hab α hαp hαS
      · exact absurd hab (hPSU K n ℓ f hcl' p hp hp2 hpn hpq hspec S hS hSidx)
    · exact absurd hab (hE6 K ℓ f (hch (by simp [chevalleyExceptionalTags])) h3 S hS hSidx)
    · exact absurd hab (hTwE6 K ℓ f (hch (by simp [chevalleyExceptionalTags])) h3 S hS hSidx)
  · have hD4' : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) := by
      rintro ⟨rfl, rfl, rfl⟩
      exact absurd hab (hD4 K ℓ f (hcl (by simp [classicalTags])) S hS hSidx)
    have hT3 : ¬ (t = .trialityD4 ∧ p = 3) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab (h3D4 K ℓ f (hch (by simp [chevalleyExceptionalTags])) S hS hSidx)
    exact mem_inner_of_lie_model_cyc hLie hb hadm hmodel ht hp hp2 hpK hdiv hD4' hT3 hS hSidx
      hαp hαS

section Dispatch


theorem reducedOuterSylowAbelian_of_residues (hPSL : N1PSL) (hPSU : N1PSU) (hE6 : N1E6)
    (hTwE6 : N1TwE6) (hD4 : N1D4) (h3D4 : N13D4) (hSPL : SP3PSL) (hSPU : SP3PSU) :
    ReducedOuterSylowAbelian := by
  intro K _ _ hs hnab hcat p hp hp2 hpK S hSp hSidx hSab α hαp hαS
  have : IsSimpleGroup K := hs
  have : Fact p.Prime := ⟨hp⟩
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [classicalTags] at h
      · simp [chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine mem_inner_of_not_dvd_card_outer hp (fun hd => ?_) hαp
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · exact mem_inner_of_lie_model_abelian
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds
        hPSL hPSU hE6 hTwE6 hD4 h3D4 hSPL hSPU hadm hmodel ht hp hp2 hpK hSp hSidx hSab hαp hαS
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem kFactInnerAction_of_residues (hPSL : N1PSL) (hPSU : N1PSU) (hE6 : N1E6)
    (hTwE6 : N1TwE6) (hD4 : N1D4) (h3D4 : N13D4) (hSPL : SP3PSL) (hSPU : SP3PSU) :
    KFactInnerAction :=
  kFactInnerAction_of_reduced
    (reducedOuterSylowAbelian_of_residues hPSL hPSU hE6 hTwE6 hD4 h3D4 hSPL hSPU)

end Dispatch

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
