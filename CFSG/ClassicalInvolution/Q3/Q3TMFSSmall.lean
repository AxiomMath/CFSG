module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.SmallCases.NobqLyOut
public import CFSG.Sporadic.Schreier.M11
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.OuterAutomorphisms

section Embedding

theorem index_dvd_card_outer {G : Type*} [Group G] (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) : F.index ∣ Nat.card (Outer F) := by
  let ψ : G →* Outer F := (QuotientGroup.mk' (inner F)).comp (MulAut.conjNormal : G →* MulAut F)
  have hψF : ∀ x ∈ F, ψ x = 1 := by
    intro x hx
    show (QuotientGroup.mk' (inner F)) (MulAut.conjNormal x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext y
    simp [MulAut.conjNormal_apply]
  let ψ' : G ⧸ F →* Outer F := QuotientGroup.lift F ψ hψF
  have hinj : Function.Injective ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    have h1 : ψ g = 1 := hq
    have h2 : (MulAut.conjNormal g : MulAut F) ∈ inner F := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨f, hf⟩ := h2
    have hg : g⁻¹ * (f : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have key := congrArg (fun α : MulAut F => ((α ⟨y, hy⟩ : F) : G)) hf
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at key
      calc y * (g⁻¹ * (f : G)) = g⁻¹ * (g * y * g⁻¹) * f := by group
        _ = g⁻¹ * ((f : G) * y * (f : G)⁻¹) * f := by rw [key]
        _ = g⁻¹ * f * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hg
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, hg]
    exact f.2
  exact Subgroup.card_dvd_of_injective ψ' hinj

theorem false_of_three_dvd_index {Y : Type} [Group Y] [Finite Y] (T : Subgroup Y) [T.Normal]
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) (hout : Nat.card (Outer T) ≤ 2)
    (h3 : 3 ∣ T.index) : False := by
  have : Finite (MulAut T) := Nobq.finite_mulAut_of_finite T
  have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
  have h3' : 3 ∣ Nat.card (Outer T) := h3.trans (index_dvd_card_outer T hC)
  have := Nat.le_of_dvd hpos h3'
  omega

end Embedding

section Simple

theorem nonempty_genFittingFStar_equiv (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Nonempty (genFittingFStar G ≃* G) :=
  ⟨(MulEquiv.subgroupCongr
    (CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnab)).trans Subgroup.topEquiv⟩

theorem genFittingFStar_simple (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    IsSimpleGroup (genFittingFStar G) ∧ ∃ a b : genFittingFStar G, a * b ≠ b * a := by
  obtain ⟨eF⟩ := nonempty_genFittingFStar_equiv G hnab
  refine ⟨eF.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

end Simple

theorem false_of_sporadic_of_three_dvd_index
    {Y : Type} [Group Y] [Finite Y] (T : Subgroup Y) [T.Normal] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hsimp : IsSimpleGroup T) (hcent : Subgroup.centralizer (T : Set Y) = ⊥) (h3 : 3 ∣ T.index)
    (h : NativeSporadic.IsSporadic (genFittingFStar ↥T) .M11 ∨
      NativeSporadic.IsSporadic (genFittingFStar ↥T) .M12) : False := by
  obtain ⟨eF⟩ := nonempty_genFittingFStar_equiv ↥T hnab
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have hc : Nat.card (Outer ↥T) = Nat.card (Outer NativeSporadic.M11) :=
      Nat.card_congr (equivalence (eF.symm.trans e)).toEquiv
    exact false_of_three_dvd_index T hcent
      (hc ▸ CFSG.Sporadic.Schreier.at_m11_schreier.1) h3
  · obtain ⟨e⟩ := h
    have hc : Nat.card (Outer ↥T) = Nat.card (Outer NativeSporadic.M12) :=
      Nat.card_congr (equivalence (eF.symm.trans e)).toEquiv
    exact false_of_three_dvd_index T hcent
      (hc ▸ CFSG.ComponentClassification.M12Cover.card_outer.le) h3

@[expose] def OddLieTightMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) → OddLieType (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

@[expose] def SmallOddLieTightMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) → TwoSubgroupsFourGenerated (genFittingFStar G) →
    OddLieType (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

@[expose] def SmallRangeOuter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T : Subgroup Y) [T.Normal], IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → Subgroup.centralizer (T : Set Y) = ⊥ →
    TwoSubgroupsFourGenerated (genFittingFStar ↥T) →
    (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → 3 ∣ T.index →
    (∃ (R : Subgroup T) (S : Sylow 2 R) (t : T), TightDatum R S t) → False

theorem OddLieTightMember.small (h : OddLieTightMember) : SmallOddLieTightMember :=
  fun G _ _ _ _ hnab _ hodd => h G hnab hodd

theorem smallRangeOuter_of_parts (hGH : GH74SectionalModels) (hodd : SmallOddLieTightMember) :
    SmallRangeOuter := by
  intro Y _ _ T _ hsimp hnab hcent hF hfree h3 ⟨R, S, t, hD⟩
  obtain ⟨hFs, hFnab⟩ := genFittingFStar_simple ↥T hnab
  have hcase := Nobq.normalOddByQuaternionSmall_of_gh74' hGH ↥T hFnab R S hD.quat t hD.mem
    hD.order hD.cent hD.normal hD.twoGroup hF
  rcases hcase with h | h | h
  · obtain ⟨z', J, hJ⟩ := hodd ↥T hFnab hF h R S hD.quat t hD.mem hD.order hD.cent hD.normal
      hD.twoGroup
    exact hfree z' J hJ
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hcent h3 (Or.inl h)
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hcent h3 (Or.inr h)

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
