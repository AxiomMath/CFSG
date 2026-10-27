module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Zstar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Main
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19A
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen4
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt69
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Conj
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs9
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.SDWr
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Trans

variable {G : Type} [Group G] [Finite G]

theorem exists_order_three_conj_in {A V : Subgroup G} (h3 : 3 ∣ AutOrd A V) :
    ∃ g ∈ normalizer (V : Set G) ⊓ A, ∃ σ : MulAut ↥V, orderOf σ = 3 ∧
      ∀ v : ↥V, ((σ v : ↥V) : G) = g * v * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := normalizer (V : Set G) ⊓ A
  have hNle : N ≤ normalizer (V : Set G) := inf_le_left
  let α : ↥N →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hNle)
  have hker : α.ker = (centralizer (V : Set G) ⊓ A).subgroupOf N := by
    ext ⟨g, hg⟩
    have h1 : α ⟨g, hg⟩ = 1 ↔ g ∈ centralizer (V : Set G) := by
      have := Subgroup.normalizerMonoidHom_ker V
      have h2 : (⟨g, hNle hg⟩ : ↥(normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker ↔
          g ∈ centralizer (V : Set G) := by
        rw [this]; exact Iff.rfl
      rw [← h2]; exact Iff.rfl
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h1]
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hg.2⟩, fun h => h.1⟩
  have hcard : Nat.card α.range = AutOrd A V := by
    rw [← Subgroup.index_ker, hker]; rfl
  have h3dvd : 3 ∣ Nat.card α.range := by rw [hcard]; exact h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hσ : orderOf (x : MulAut ↥V) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨(g : G), g.2, (x : MulAut ↥V), hσ, fun v => ?_⟩
  rw [← hg]
  rfl

theorem conj_of_three_dvd_in {A V : Subgroup G} (h4 : IVK.IsFourSubgroup V)
    (h3 : 3 ∣ AutOrd A V) :
    ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ c ∈ normalizer (V : Set G) ⊓ A, c * v * c⁻¹ = w := by
  have hEA : IsElementaryAbelian 2 ↥V := h4.1
  have hcardV : Nat.card ↥V = 4 := h4.2
  have : IsKleinFour ↥V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVne : V ≠ ⊥ := by
      intro hb
      rw [hb] at hcardV
      simp at hcardV
    have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    exact ⟨hcardV, hEA.exponent_eq_prime⟩
  obtain ⟨g, hgC, σ, hσ, hσg⟩ := exists_order_three_conj_in h3
  have hfix : ∀ u : ↥V, σ u = u → u = 1 := fun u hu => klein_aut_order_three_fixed_free σ hσ hu
  have hσ3 : σ * σ * σ = 1 := by
    have : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    simpa [pow_succ] using this
  intro v hv hv1 w hw hw1
  set v' : ↥V := ⟨v, hv⟩ with hv'
  set w' : ↥V := ⟨w, hw⟩ with hw'
  have hv'1 : v' ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hs1 : σ v' ≠ 1 := fun h => hv'1 (σ.injective (by rw [h, map_one]))
  have hsv : σ v' ≠ v' := fun h => hv'1 (hfix v' h)
  have hs2_1 : σ (σ v') ≠ 1 := fun h => hs1 (σ.injective (by rw [h, map_one]))
  have hs2_s : σ (σ v') ≠ σ v' := fun h => hsv (σ.injective h)
  have hs2_v : σ (σ v') ≠ v' := by
    intro h
    apply hsv
    have h1 : σ (σ (σ v')) = σ v' := by rw [h]
    have h2 : σ (σ (σ v')) = v' := by
      have := congrArg (fun m : MulAut ↥V => m v') hσ3
      simpa using this
    exact h1.symm.trans h2
  have hs2 : σ (σ v') = v' * σ v' :=
    IsKleinFour.eq_mul_of_ne_all hv'1 hs1 (Ne.symm hsv) hs2_1 hs2_v hs2_s
  have hcases : w' = v' ∨ w' = σ v' ∨ w' = σ (σ v') := by
    by_cases h1 : w' = v'
    · exact Or.inl h1
    by_cases h2 : w' = σ v'
    · exact Or.inr (Or.inl h2)
    right; right
    rw [hs2]
    exact IsKleinFour.eq_mul_of_ne_all hv'1 hs1 (Ne.symm hsv) hw'1 h1 h2
  have hgcon : ∀ u : ↥V, ((σ u : ↥V) : G) = g * u * g⁻¹ := hσg
  rcases hcases with h | h | h
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    calc 1 * v * (1 : G)⁻¹ = v := by group
      _ = w := (congrArg Subtype.val h).symm
  · refine ⟨g, hgC, ?_⟩
    have := congrArg Subtype.val h
    rw [hgcon] at this
    exact this.symm
  · refine ⟨g * g, Subgroup.mul_mem _ hgC hgC, ?_⟩
    have := congrArg Subtype.val h
    rw [hgcon, hgcon] at this
    calc g * g * v * (g * g)⁻¹ = g * (g * v * g⁻¹) * g⁻¹ := by group
      _ = w := this.symm

theorem transOn_of_three_dvd {U : Subgroup G} (h4 : IVK.IsFourSubgroup U)
    (h3 : 3 ∣ AutOrd (⊤ : Subgroup G) U) : TransOn U := by
  intro a ha ha1 b hb hb1
  obtain ⟨c, hc, hca⟩ := conj_of_three_dvd_in h4 h3 a ha ha1 b hb hb1
  exact ⟨c, hc.1, hca⟩

end Trans

section Four

variable {G : Type} [Group G] [Finite G]

theorem isFour_zpowers_sup {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a) : IVK.IsFourSubgroup (zpowers a ⊔ zpowers b) := by
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hc) m n).eq
  have hsq : ∀ x ∈ zpowers a, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ha, one_zpow]
  have hsq' : ∀ x ∈ zpowers b, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hb, one_zpow]
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rcases eq_one_or_eq_of_mem_zpowers ha hxa with h | h
    · rw [h]; exact one_mem _
    · rcases eq_one_or_eq_of_mem_zpowers hb hxb with h' | h'
      · rw [h']; exact one_mem _
      · exact absurd (h.symm.trans h') hab
  have hcard : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
    have := (GroupTheory.card_sup_mul_card_inf_of_commute (zpowers a) (zpowers b) hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha2, hb2] at this
    exact this
  refine ⟨?_, hcard⟩
  have hel : ∀ x ∈ zpowers a ⊔ zpowers b, ∀ y ∈ zpowers a ⊔ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have hha : h₁ * h₂ = h₂ * h₁ := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh₁
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh₂
      exact (Commute.zpow_zpow_self a m n).eq
    have hkb : k₁ * k₂ = k₂ * k₁ := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk₁
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk₂
      exact (Commute.zpow_zpow_self b m n).eq
    have hhk1 := hcomm h₂ hh₂ k₁ hk₁
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hhk1]
      _ = (h₁ * h₂) * (k₁ * k₂) := by group
      _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hha, hkb]
      _ = h₂ * (h₁ * k₂) * k₁ := by group
      _ = h₂ * (k₂ * h₁) * k₁ := by rw [hcomm h₁ hh₁ k₂ hk₂]
      _ = h₂ * k₂ * (h₁ * k₁) := by group
  have hel2 : ∀ x ∈ zpowers a ⊔ zpowers b, x * x = 1 := by
    intro x hx
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    calc h₁ * k₁ * (h₁ * k₁) = (h₁ * h₁) * (k₁ * k₁) := by
          rw [mul_assoc, ← mul_assoc k₁, ← hcomm h₁ hh₁ k₁ hk₁]; group
      _ = 1 := by rw [hsq h₁ hh₁, hsq' k₁ hk₁, one_mul]
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hel _ a.2 _ b.2)⟩⟩, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  apply Subtype.ext
  simpa [pow_two] using hel2 x x.2

theorem isFour_map_of_inj {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
    {E : Subgroup X} (hE : IsElementaryAbelian 2 ↥E) (hc : Nat.card ↥E = 2 ^ 2) :
    IVK.IsFourSubgroup (E.map f) := by
  refine ⟨?_, ?_⟩
  · have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b =>
      hE.toIsMulCommutative.is_comm.comm a b
    have hexp : ∀ a : ↥E, a ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 ↥E)
    refine
      { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun a => ?_) }
    · obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : Y) * b = b * a
      rw [← ha'', ← hb'', ← map_mul, ← map_mul]
      exact congrArg f (congrArg Subtype.val (hcomm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.1 a.2
      apply Subtype.ext
      show (a : Y) ^ 2 = 1
      rw [← ha'', ← map_pow]
      have h2 : a' ^ 2 = 1 := by simpa using congrArg Subtype.val (hexp ⟨a', ha'⟩)
      rw [h2, map_one]
  · rw [Nat.card_congr (E.equivMapOfInjective f hf).toEquiv.symm, hc]
    norm_num

omit [Finite G] in
theorem sq_eq_one_of_isFour {U : Subgroup G} (hU : IVK.IsFourSubgroup U) {a : G} (ha : a ∈ U) : a * a = 1 := by
  have := hU.1
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
  simpa [pow_two] using h

omit [Finite G] in
theorem mul_comm_of_isFour {U : Subgroup G} (hU : IVK.IsFourSubgroup U) {a b : G} (ha : a ∈ U) (hb : b ∈ U) :
    a * b = b * a := by
  have := hU.1
  have h := IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem eq_zpowers_sup_of_isFour {U : Subgroup G} (hU : IVK.IsFourSubgroup U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : U = zpowers a ⊔ zpowers b := by
  have h4 := isFour_zpowers_sup (sq_eq_one_of_isFour hU ha) (sq_eq_one_of_isFour hU hb) ha1 hb1 hab (mul_comm_of_isFour hU ha hb)
  have hle : zpowers a ⊔ zpowers b ≤ U := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hU.2, h4.2])).symm

omit [Finite G] in
theorem comm_of_mem_zpowers_sup {x z t u : G} (hxz : x * z = z * x) (hxt : x * t = t * x)
    (hzt : z * t = t * z) (hu : u ∈ zpowers z ⊔ zpowers t) : u * x = x * u := by
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute z t from hzt) m n).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hu
  have h1 : a * x = x * a := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute z x from hxz.symm) m).eq
  have h2 : b * x = x * b := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute t x from hxt.symm) m).eq
  calc a * b * x = a * (b * x) := by group
    _ = a * (x * b) := by rw [h2]
    _ = (a * x) * b := by group
    _ = (x * a) * b := by rw [h1]
    _ = x * (a * b) := by group

end Four

section Residual

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem LC_le_O2Of {M : Subgroup G} (hCM : Cen z ≤ M) : LC z ≤ O2Of M := by
  have hle : LC z ≤ (oPrimePResidual 2 ↥(Cen z)).map (Cen z).subtype :=
    Subgroup.map_mono inf_le_left
  refine hle.trans ?_
  unfold O2Of
  rw [Subgroup.map_le_iff_le_comap]
  unfold oPrimePResidual
  rw [Subgroup.map_le_iff_le_comap, oResidual, Subgroup.closure_le]
  intro w hw
  have hwM : (((w : ↥(oPrimeResidual 2 ↥(Cen z))) : ↥(Cen z)) : G) ∈ M := hCM w.1.2
  refine ⟨⟨(((w : ↥(oPrimeResidual 2 ↥(Cen z))) : ↥(Cen z)) : G), hwM⟩, Subgroup.subset_closure ?_, rfl⟩
  change Nat.Coprime (orderOf (⟨(((w : ↥(oPrimeResidual 2 ↥(Cen z))) : ↥(Cen z)) : G), hwM⟩ : ↥M)) 2
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact hw

theorem le_O2Of_of_sylow_le {M X S₀ : Subgroup G} (hXM : X ≤ M)
    (hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 S₀ X) (hle : S₀ ≤ O2Of M) : X ≤ O2Of M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oResidual 2 ↥M).Normal := oResidual_normal' 2 ↥M
  have hQ : IsPGroup 2 (↥M ⧸ oResidual 2 ↥M) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le (oResidual 2 ↥M) le_rfl
  let f : ↥X →* (↥M ⧸ oResidual 2 ↥M) :=
    (QuotientGroup.mk' (oResidual 2 ↥M)).comp (Subgroup.inclusion hXM)
  have hres : oResidual 2 ↥X ≤ f.ker := CFSG.RankThree.Transfer.oResidual_le_ker_of_isPGroup f hQ
  have hQX : IsPGroup 2 (↥X ⧸ f.ker) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le f.ker hres
  obtain ⟨P, hP⟩ := hS₀.exists_sylow_eq_subgroupOf
  have hPker : (P : Subgroup ↥X) ≤ f.ker := by
    intro x hx
    rw [hP] at hx
    have hxK : (x : G) ∈ O2Of M := hle hx
    obtain ⟨m, hm, hmx⟩ := hxK
    have hmx' : m = ⟨(x : G), hXM x.2⟩ := Subtype.ext hmx
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (oResidual 2 ↥M) ⟨(x : G), hXM x.2⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hmx']
    exact hm
  have htop := CFSG.RankThree.Transfer.map_mk_eq_top_of_isPGroup P f.ker hQX
  have hbot : (P : Subgroup ↥X).map (QuotientGroup.mk' f.ker) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rwa [QuotientGroup.ker_mk'])
  have hker : f.ker = ⊤ := by
    rw [hbot] at htop
    have hsub : Subsingleton (↥X ⧸ f.ker) := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup (↥X ⧸ f.ker)) := by rw [htop]; trivial
      have hb : b ∈ (⊥ : Subgroup (↥X ⧸ f.ker)) := by rw [htop]; trivial
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk x : ↥X ⧸ f.ker) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this
  intro x hx
  have hx1 : f ⟨x, hx⟩ = 1 := by
    have : (⟨x, hx⟩ : ↥X) ∈ f.ker := by rw [hker]; trivial
    exact this
  have hx2 : QuotientGroup.mk' (oResidual 2 ↥M) ⟨x, hXM hx⟩ = 1 := hx1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
  exact ⟨⟨x, hXM hx⟩, hx2, rfl⟩

end Residual

section Layer

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem layer_ne_bot_of_normal {W : Subgroup A} (hW : W.Normal) (hne : layer ↥W ≠ ⊥) : layer A ≠ ⊥ := by
  by_contra hbot
  apply hne
  by_contra hne'
  have hex : ∃ K : Subgroup ↥W, IsComponent K := by
    by_contra hno
    push Not at hno
    exact hne' (CFSG.LocalCores.layer_eq_bot_of_forall hno)
  obtain ⟨K, hK⟩ := hex
  have hK' : IsComponent (K.map W.subtype) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective W.subtype W.subtype_injective) hK.1,
      hK.2.trans' hW.isSubnormal⟩
  have hle : K.map W.subtype ≤ layer A := CFSG.LocalCores.component_le_layer hK'
  rw [hbot, le_bot_iff] at hle
  have hnt : Nontrivial ↥(K.map W.subtype) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hle

omit [Finite A] in
theorem layer_ne_bot_of_normal_sub {W Y : Subgroup A} (hWY : W ≤ Y) (hn : (W.subgroupOf Y).Normal)
    (hne : layer ↥W ≠ ⊥) : layer ↥Y ≠ ⊥ := by
  refine layer_ne_bot_of_normal hn ?_
  intro hbot
  apply hne
  have h := layer_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hWY)
  rw [hbot, Subgroup.map_bot] at h
  exact h.symm

end Layer

section BarOf

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem exists_zpow_of_mem_barOf {t : G} (htC : t ∈ Cen z) {b : CentralizerBar z}
    (hb : b ∈ barOf z (zpowers t)) : ∃ n : ℤ, b = (toBar z ⟨t, htC⟩) ^ n := by
  obtain ⟨c, hc, rfl⟩ := hb
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hc)
  refine ⟨n, ?_⟩
  have : c = (⟨t, htC⟩ : ↥(Cen z)) ^ n := by
    apply Subtype.ext
    simpa using hn.symm
  rw [this, map_zpow]

end BarOf

end CFSG.GH74.GLS.Stage2.Bender.Thm2
