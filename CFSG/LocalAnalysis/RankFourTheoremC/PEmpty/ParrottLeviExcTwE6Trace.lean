module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQBasic
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs Subgroup

namespace PB3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

theorem commutatorElement_mul_mul {G : Type*} [Group G] {a b c d : G} (hbc : Commute b c)
    (had : Commute a d) (hxa : Commute ⁅b, d⁆ a) (hxc : Commute ⁅b, d⁆ c) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅b, d⁆ := by
  have h1 : d * a⁻¹ * d⁻¹ = a⁻¹ := by
    rw [← had.inv_left.eq]
    group
  have h2 : ⁅b, d⁆ * a⁻¹ * c⁻¹ = a⁻¹ * c⁻¹ * ⁅b, d⁆ := by
    rw [hxa.inv_right.eq, mul_assoc, hxc.inv_right.eq, ← mul_assoc]
  calc ⁅a * b, c * d⁆ = a * (b * c) * d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹ := by group
    _ = a * c * ⁅b, d⁆ * (d * a⁻¹ * d⁻¹) * c⁻¹ := by rw [hbc.eq]; group
    _ = a * c * (⁅b, d⁆ * a⁻¹ * c⁻¹) := by rw [h1]; group
    _ = ⁅a, c⁆ * ⁅b, d⁆ := by rw [h2]; group

theorem isRoot_two_three : IsRoot .E6 (Pi.single (nd 2) 1 + Pi.single (nd 3) 1) := by
  have h := (IsRoot.basis (τ := .E6) (nd 2)).reflect (nd 3)
  rwa [show reflect .E6 (nd 3) (Pi.single (nd 2) 1) = Pi.single (nd 2) 1 + Pi.single (nd 3) 1 by
    decide] at h

theorem isRoot_four_three : IsRoot .E6 (Pi.single (nd 4) 1 + Pi.single (nd 3) 1) := by
  have h := (IsRoot.basis (τ := .E6) (nd 4)).reflect (nd 3)
  rwa [show reflect .E6 (nd 3) (Pi.single (nd 4) 1) = Pi.single (nd 4) 1 + Pi.single (nd 3) 1 by
    decide] at h

theorem rho_two_three :
    rho (Pi.single (nd 2) 1 + Pi.single (nd 3) 1) = Pi.single (nd 4) 1 + Pi.single (nd 3) 1 := by
  decide

theorem rho_two_three_ne :
    rho (Pi.single (nd 2) 1 + Pi.single (nd 3) 1) ≠ Pi.single (nd 2) 1 + Pi.single (nd 3) 1 := by
  rw [rho_two_three]
  decide

theorem rho_neg_two : rho (-Pi.single (nd 2) 1) = -Pi.single (nd 4) 1 := by
  decide

theorem rho_neg_two_ne : rho (-Pi.single (nd 2) 1) ≠ -Pi.single (nd 2) 1 := by
  rw [rho_neg_two]
  decide

theorem rho_three : rho (Pi.single (nd 3) 1) = Pi.single (nd 3) 1 := by
  decide

theorem isRoot_three : IsRoot .E6 (Pi.single (nd 3) 1) :=
  isRoot_single _ _


theorem proj_three : proj (Pi.single (nd 3) 1) = Pi.single (nf 1) 1 :=
  proj_single _

variable {k : Type} [Field k] (θ : k →+* k)

theorem commutator_xPair_eq [CharP k 2] (hθ : ∀ c, θ (θ c) = c) (u : k) :
    ((⁅xPair θ hθ isRoot_two_three rho_two_three_ne u,
        xPair θ hθ (isRoot_neg_single _ (nd 2)) rho_neg_two_ne 1⁆ : fixedGroup k θ) :
      e6Data_valid.minGroup k) = e6Data_valid.xm k (Pi.single (nd 3) 1) (u + θ u) := by
  have hs : ∀ γ, ((twistSign γ : ℤ) : k) = 1 := fun γ => by
    rcases twistSign_eq_one_or γ with h | h <;> simp [h, CharTwo.neg_eq]
  have hsign : ∀ σ : k, IsSign σ → σ = 1 := fun σ hσ => by
    rcases hσ with rfl | rfl
    · rfl
    · exact CharTwo.neg_eq 1
  have e : ((⁅xPair θ hθ isRoot_two_three rho_two_three_ne u,
        xPair θ hθ (isRoot_neg_single _ (nd 2)) rho_neg_two_ne 1⁆ : fixedGroup k θ) :
      e6Data_valid.minGroup k) =
      ⁅(xPair θ hθ isRoot_two_three rho_two_three_ne u : e6Data_valid.minGroup k),
        (xPair θ hθ (isRoot_neg_single _ (nd 2)) rho_neg_two_ne 1 : e6Data_valid.minGroup k)⁆ :=
    rfl
  rw [e, xPair_val, xPair_val, hs, hs, one_mul, one_mul, map_one, rho_two_three, rho_neg_two]
  have hs1 : (Pi.single (nd 2) 1 + Pi.single (nd 3) 1 + -Pi.single (nd 2) 1 :
      Fin (Tag.rank .E6) → ℤ) = Pi.single (nd 3) 1 := by abel
  have hs2 : (Pi.single (nd 4) 1 + Pi.single (nd 3) 1 + -Pi.single (nd 4) 1 :
      Fin (Tag.rank .E6) → ℤ) = Pi.single (nd 3) 1 := by abel
  have h3 : IsRoot .E6 (Pi.single (nd 3) 1) := isRoot_single _ (nd 3)
  obtain ⟨σ₁, hσ₁, hc₁⟩ := (e6Data_valid.commutator_xm k isRoot_two_three
    (isRoot_neg_single _ (nd 2)) (by rw [hs1]; exact h3.ne_zero)).1 (by rw [hs1]; exact h3)
  obtain ⟨σ₂, hσ₂, hc₂⟩ := (e6Data_valid.commutator_xm k isRoot_four_three
    (isRoot_neg_single _ (nd 4)) (by rw [hs2]; exact h3.ne_zero)).1 (by rw [hs2]; exact h3)
  have hca := hc₁ u 1
  have hbd := hc₂ (θ u) 1
  rw [hs1, hsign σ₁ hσ₁] at hca
  rw [hs2, hsign σ₂ hσ₂] at hbd
  have hbc := commute_xm isRoot_four_three (isRoot_neg_single _ (nd 2)) (by decide)
    (not_isRoot_of_form (by decide)) (θ u) (1 : k)
  have had := commute_xm isRoot_two_three (isRoot_neg_single _ (nd 4)) (by decide)
    (not_isRoot_of_form (by decide)) u (1 : k)
  have hxa := commute_xm h3 isRoot_two_three (by decide) (not_isRoot_of_form (by decide))
    (1 * θ u * 1) u
  have hxc := commute_xm h3 (isRoot_neg_single _ (nd 2)) (by decide)
    (not_isRoot_of_form (by decide)) (1 * θ u * 1) (1 : k)
  rw [← hbd] at hxa hxc
  rw [commutatorElement_mul_mul hbc had hxa hxc, hca, hbd, ← e6Data_valid.xm_add]
  congr 1
  ring

theorem rootGroup_two_three_le_levi (hθ : ∀ c, θ (θ c) = c)
    {C : Finset (Fin (twistedDatum k θ).rank)} (h1 : nf 1 ∈ C) (h2 : nf 2 ∈ C) :
    (twistedDatum k θ).rootGroup (proj (Pi.single (nd 2) 1 + Pi.single (nd 3) 1)) ≤
      levi (twistedDatum k θ).rootGroup C := by
  have key : ∀ i : Fin (Tag.rank .F4), i ≠ nf 1 → i ≠ nf 2 →
      proj (Pi.single (nd 2) 1 + Pi.single (nd 3) 1) i = 0 := by
    decide
  have h := Levi.rootGroup_le_leviC_of_support (D := twistedDatum k θ)
    (e := C.orderEmbOfFin rfl) rfl
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (by rw [twistedDatum_roots]; exact isRoot_proj isRoot_two_three)
    (fun j hj => by
      rw [Finset.range_orderEmbOfFin, Finset.mem_coe] at hj
      exact key j (ne_of_mem_of_not_mem h1 hj).symm (ne_of_mem_of_not_mem h2 hj).symm)
  rwa [Levi.leviC, Finset.image_orderEmbOfFin_univ] at h

theorem rootGroup_neg_two_le_levi {C : Finset (Fin (twistedDatum k θ).rank)} (h2 : nf 2 ∈ C) :
    (twistedDatum k θ).rootGroup (-Pi.single (nf 2) 1) ≤ levi (twistedDatum k θ).rootGroup C :=
  le_sup_right.trans (rankOne_le_levi _ h2)

theorem mem_commutator_levi [CharP k 2] (hθ : ∀ c, θ (θ c) = c)
    {C : Finset (Fin (twistedDatum k θ).rank)} (h1 : nf 1 ∈ C) (h2 : nf 2 ∈ C) (u : k)
    {g : fixedGroup k θ}
    (hg : (g : e6Data_valid.minGroup k) = e6Data_valid.xm k (Pi.single (nd 3) 1) (u + θ u)) :
    g ∈ ⁅levi (twistedDatum k θ).rootGroup C, levi (twistedDatum k θ).rootGroup C⁆ := by
  have e : g = ⁅xPair θ hθ isRoot_two_three rho_two_three_ne u,
      xPair θ hθ (isRoot_neg_single _ (nd 2)) rho_neg_two_ne 1⁆ :=
    Subtype.ext (hg.trans (commutator_xPair_eq θ hθ u).symm)
  have hy := xPair_mem θ hθ isRoot_two_three rho_two_three_ne u
  have hz := xPair_mem θ hθ (isRoot_neg_single _ (nd 2)) rho_neg_two_ne 1
  rw [proj_neg_single] at hz
  rw [e]
  exact commutator_mem_commutator (rootGroup_two_three_le_levi θ hθ h1 h2 hy)
    (rootGroup_neg_two_le_levi θ h2 hz)

end PB3


variable {k : Type} [Field k] (θ : k →+* k)

theorem rootGroup_one_le_commutator_levi_of_two [CharP k 2] (hθ : ∀ c, θ (θ c) = c)
    (htr : ∀ c : k, θ c = c → ∃ u : k, c = u + θ u)
    {C : Finset (Fin (twistedDatum k θ).rank)} (h1 : nf 1 ∈ C) (h2 : nf 2 ∈ C) :
    (twistedDatum k θ).rootGroup (Pi.single (nf 1) 1) ≤
      ⁅levi (twistedDatum k θ).rootGroup C, levi (twistedDatum k θ).rootGroup C⁆ := by
  intro g hg
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed θ PB3.isRoot_three PB3.proj_three
    PB3.rho_three g).1 hg
  obtain ⟨u, rfl⟩ := htr c hc
  exact PB3.mem_commutator_levi θ hθ h1 h2 u hgc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6
