module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110i
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110g
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts6
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut IsFiTwentyTwo)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  (mem_gLAPPrimeCoreOf_iff le_normalizer_gLAPPrimeCoreOf mem_normalizer_gLAPPrimeCoreOf
    card_gLAPPrimeCoreOf_coprime)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Inputs

@[expose] def IsD4Comp {X : Type} [Group X] (Y L : Subgroup X) : Prop :=
  GLAPComponent 5 Y L ∧
    CFSG.Models.LieModel (barOf 5 L ⧸ Subgroup.center (barOf 5 L)) .POmegaPlus 4 2 1

@[expose] def InputD4ThreeRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), CFSG.Open.IsKGroup ↥Y → ∀ 𝒞 : Set (Subgroup G),
    (∀ L ∈ 𝒞, IsD4Comp Y L) → 4 * 𝒞.ncard ≤ CFSG.Open.pRank 3 (⨆ L ∈ 𝒞, L)

@[expose] def InputD4LayerGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), CFSG.Open.IsKGroup ↥Y → ∀ 𝒞 : Set (Subgroup G),
    (∀ L ∈ 𝒞, IsD4Comp Y L) → 2 ≤ 𝒞.ncard →
      ∀ S : Subgroup G, IsSylowIn 3 (⨆ L ∈ 𝒞, L) S → (⨆ L ∈ 𝒞, L) ≤ GLBCore 3 3 S

@[expose] def InputFi22GammaThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsFiTwentyTwo X → ∀ P : Subgroup X, IsPGroup 5 ↥P →
    Nat.card ↥P = 5 ^ 2 →
      (Nat.card ↥(Claims1110b.gammaK0 P)).factorization 3 < (Nat.card X).factorization 3

end Inputs

section AutD4

theorem card_le_of_isD4Comp {Y L F : Subgroup G} (hL : IsD4Comp Y L)
    (hF : IsElemAbelian 5 F) (hFL : F ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥F ≤ 5 ^ 2 * Nat.card ↥(centModIn F L) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set T := barOf 5 L ⧸ Subgroup.center (barOf 5 L) with hT
  have hTm : StatedClassicalModel T .POmegaPlus 4 2 1 := by
    rcases hL.2.2 with h | ⟨h4, -⟩
    · exact h
    · norm_num at h4
  obtain ⟨eT⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hTm
    CFSG.EvenSmallLie.OmegaEight.statedClassicalModel_omegaT
  have hAut : Nat.card (MulAut T) = 1045094400 := by
    rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr eT, CFSG.EvenSmallLie.OmegaEight.card_mulAut_omegaT]
  have hq : CFSG.Open.IsQuasisimple (barOf 5 L) := Lemma1313.isQuasisimple_barOf_of_pComp hL.1
  set φ : ↥F →* MulAut T :=
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (barOf 5 L)).comp
      ((barAut 5 L).comp (Subgroup.inclusion hFL)) with hφ
  have hinj := CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hq.1
  have hker : ∀ f : ↥F, φ f = 1 → (f : G) ∈ centModIn F L := by
    intro f hf
    have h1 : barAut 5 L (Subgroup.inclusion hFL f) = 1 := by
      apply hinj
      rw [map_one]
      exact hf
    have h2 := Claims1110d.comm_mem_core_of_barAut_eq_one (hFL f.2) h1
    refine mem_centModIn.2 ⟨f.2, hFL f.2, fun l hl => ?_⟩
    have h3 := Subgroup.inv_mem _ (h2 l hl)
    have e : ((f : G) * l * (f : G)⁻¹ * l⁻¹)⁻¹ = l * f * l⁻¹ * (f : G)⁻¹ := by group
    rwa [e] at h3
  have hkc : Nat.card ↥φ.ker ≤ Nat.card ↥(centModIn F L) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥F) : G), hker k k.2⟩) ?_
    intro k₁ k₂ h
    have h' : ((k₁ : ↥F) : G) = ((k₂ : ↥F) : G) :=
      congrArg (fun z : ↥(centModIn F L) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hrc : Nat.card ↥φ.range ≤ 5 ^ 2 := by
    have hp : IsPGroup 5 ↥φ.range :=
      (Claims1110.isPGroup_of_elemAb hF).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : 5 ^ k ∣ 1045094400 := hk ▸ hAut ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have h3 : 5 ^ 3 ∣ 1045094400 := (pow_dvd_pow 5 (by omega)).trans hdvd
      norm_num at h3
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
  rw [h]
  exact Nat.mul_le_mul hrc hkc

end AutD4

section Fi22Index

open CFSG.Monster.B.Fischer CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.EvenSmallLie.OmegaEight

theorem inputFi22GammaThree_holds :
    InputFi22GammaThree := by
  intro X _ _ hX P hPp hPc
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hf5, h25, -⟩ := CFSG.HardMathSupport.Solomon.Proving.fi22Facts_holds X hX
  have hPc' : Nat.card P = 5 ^ (Nat.card X).factorization 5 := by rw [hPc, hf5]
  have hPsyl : IsSylowIn 5 ⊤ P :=
    Claims1110.isSylowIn_of_card le_top hPp (by rw [Subgroup.card_top]; exact hPc')
  have hord : ∀ x ∈ P, x ≠ 1 → orderOf x = 5 := by
    intro x hxP hx1
    have hd : orderOf x ∣ 5 ^ 2 := hPc ▸ Subgroup.orderOf_dvd_natCard P hxP
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hjx
      exact absurd hjx hx1
    · rw [hjx, pow_one]
    · exact absurd hjx (h25 x)
  have hlay : ∀ x ∈ P, x ≠ 1 →
      Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥ ∧
        5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) := by
    intro x hxP hx1
    obtain ⟨ψ⟩ := SporFacts.input14_21_holds X hX x (hord x hxP hx1)
    refine ⟨Claims1110e.center_eq_bot_of_isAltType_five ⟨ψ⟩, ?_⟩
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hγ := Claims1110f.gammaK0_eq_glbCore hPc hPsyl hord hlay
  obtain ⟨φ₀⟩ := hX
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let φ : X ≃* fi22P := (φ₀.trans β.symm).trans fi22PermEquiv
  obtain ⟨x, y, Γ, hD, hΓ, ⟨θ⟩⟩ := Claims1110g.model_main
  have hcardP : Nat.card fi22P = 5 ^ 2 * 2582470066176 := by rw [card_fi22P]; norm_num
  have hm5 : ¬ 5 ∣ 2582470066176 := by norm_num
  have hf : (Nat.card fi22P).factorization 5 = 2 := by
    rw [hcardP, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm5, add_zero, Nat.Prime.factorization_pow (by norm_num)]
    simp
  have hP'c : Nat.card (P.map φ.toMonoidHom) = 5 ^ (Nat.card fi22P).factorization 5 := by
    rw [Subgroup.card_map_of_injective φ.injective, hPc, hf]
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hcardP hm5 (Sylow.ofCard _ hP'c)
  have hT : (Subgroup.closure ({x, y} : Set fi22P)).map (MulAut.conj g).toMonoidHom =
      P.map φ.toMonoidHom := by
    rw [← closure_pair_map x y (MulAut.conj g)]
    simp only [MulAut.conj_apply]
    rw [hg, Sylow.coe_ofCard]
  set ψ : X ≃* fi22P := φ.trans (MulAut.conj g).symm with hψdef
  have hψ : (Claims1110b.gammaK0 P).map ψ.toMonoidHom = Γ := by
    have h1 : (GLBCore 5 1 P).map φ.toMonoidHom = Γ.map (MulAut.conj g).toMonoidHom := by
      rw [Claims1110g.glbCore_map_eq 1 φ P, ← hT, ← Claims1110g.glbCore_map_eq 1 (MulAut.conj g), hΓ]
    have h2 : ψ.toMonoidHom = (MulAut.conj g).symm.toMonoidHom.comp φ.toMonoidHom := rfl
    rw [hγ, h2, ← Subgroup.map_map, h1, Subgroup.map_map]
    convert Subgroup.map_id Γ
    ext z
    simp
  have hcardΓ : Nat.card ↥(Claims1110b.gammaK0 P) = 1045094400 := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hψ, Nat.card_congr θ.toEquiv,
      card_autT]
  have hcardX : Nat.card X = 64561751654400 := by
    rw [Nat.card_congr φ.toEquiv, card_fi22P]
  rw [hcardΓ, hcardX, show (1045094400 : ℕ) = 3 ^ 6 * 1433600 by norm_num,
    show (64561751654400 : ℕ) = 3 ^ 9 * 3280076800 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 1433600),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 3280076800),
    Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_three]
  simp

end Fi22Index

section Tools

theorem pRank_le_of_isSylowIn {p : ℕ} [Fact p.Prime] {X Q : Subgroup G} (hQ : IsSylowIn p X Q) :
    CFSG.Open.pRank p X ≤ CFSG.Open.pRank p Q := by
  obtain ⟨E, hEX, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt X
  obtain ⟨x, -, S, hSp, hSX, hQS, hES⟩ :=
    exists_conj_le_pGroup' hQ.1 hQ.2.1 hEX (Claims1110.isPGroup_of_elemAb hEel)
  have hSQ : S = Q := hQ.2.2 S hSX hSp hQS
  rw [hSQ] at hES
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hES (Claims1110.isElemAbelian_conj x hEel)
    (by rw [Claims1110.card_conj, hEc])

theorem conj_mem_centModIn_of_gLBConj {R L : Subgroup G} {g c : G} (hg : g ∈ R)
    (hc : c ∈ centModIn R (GLBConj g L)) : g * c * g⁻¹ ∈ centModIn R L := by
  obtain ⟨hcR, hcN, hcL⟩ := mem_centModIn.1 hc
  refine mem_centModIn.2 ⟨R.mul_mem (R.mul_mem hg hcR) (R.inv_mem hg), ?_, fun l hl => ?_⟩
  · rw [mem_normalizer_iff_gLBConj_eq] at hcN ⊢
    have h1 := congrArg (GLBConj g⁻¹) hcN
    rwa [gLBConj_gLBConj, gLBConj_gLBConj, gLBConj_inv_gLBConj, ← mul_assoc] at h1
  · have hl' : g⁻¹ * l * g ∈ GLBConj g L := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hl
    have h1 := hcL _ hl'
    rw [glaPPrimeCoreOf_gLBConj, mem_gLBConj] at h1
    have e : g * (g⁻¹ * l * g * c * (g⁻¹ * l * g)⁻¹ * c⁻¹) * g⁻¹ =
        l * (g * c * g⁻¹) * l⁻¹ * (g * c * g⁻¹)⁻¹ := by group
    rwa [e] at h1

@[expose] def commModCoreSub (X : Subgroup G) (z : G) : Subgroup G where
  carrier := {x | x ∈ X ∧ z * x * z⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 5 X}
  mul_mem' := by
    rintro x y ⟨hxX, hx⟩ ⟨hyX, hy⟩
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    have h2 : x * (z * y * z⁻¹ * y⁻¹) * x⁻¹ ∈ GLAPPrimeCoreOf 5 X :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_gLAPPrimeCoreOf 5 X hxX) _).1 hy
    have e : z * (x * y) * z⁻¹ * (x * y)⁻¹ = (z * x * z⁻¹ * x⁻¹) * (x * (z * y * z⁻¹ * y⁻¹) * x⁻¹) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ hx h2
  one_mem' := ⟨X.one_mem, by rw [mul_one, mul_inv_cancel, one_mul, inv_one]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxX, hx⟩
    refine ⟨X.inv_mem hxX, ?_⟩
    have h2 : x⁻¹ * (z * x * z⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ GLAPPrimeCoreOf 5 X :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_gLAPPrimeCoreOf 5 X (X.inv_mem hxX)) _).1
        (Subgroup.inv_mem _ hx)
    have e : z * x⁻¹ * z⁻¹ * x⁻¹⁻¹ = x⁻¹ * (z * x * z⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h2

theorem le_sup_normalizer_of_isSylowIn {p : ℕ} [Fact p.Prime] {M J S : Subgroup G}
    (hMJ : M ≤ Subgroup.normalizer (J : Set G)) (hS : IsSylowIn p J S) :
    M ≤ J ⊔ Subgroup.normalizer (S : Set G) := by
  intro g hg
  have hSc := Claims1110.card_of_isSylowIn hS
  have hS' : GLBConj g S ≤ J := by
    have h1 := gLBConj_mono g hS.1
    rwa [gLBConj_eq_of_mem_normalizer (hMJ hg)] at h1
  obtain ⟨j, hjJ, hj⟩ := Claims1110.exists_conj_eq_of_card hS.1 hS' hS.2.1
    (Claims1110.isPGroup_conj g hS.2.1) hSc (by rw [Claims1110.card_conj, hSc])
  rw [gLBConj_gLBConj] at hj
  have hgj : g * j ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_iff_gLBConj_eq.2 hj
  have e : g = (g * j) * j⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgj) (Subgroup.mem_sup_left (J.inv_mem hjJ))

theorem exists_mem_normalizer_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime] {Q Q' : Subgroup G} (hQ' : IsPGroup p ↥Q')
    (hlt : Q < Q') : ∃ x ∈ Q', x ∉ Q ∧ x ∈ Subgroup.normalizer (Q : Set G) := by
  haveI : Group.IsNilpotent ↥Q' := hQ'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q')
  set H : Subgroup ↥Q' := Q.subgroupOf Q' with hH
  have hHtop : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (lt_iff_le_not_ge.1 hlt).2
    intro x hx
    have : (⟨x, hx⟩ : ↥Q') ∈ H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨⟨x, hxQ'⟩, hxN, hxH⟩ := SetLike.exists_of_lt (hnc H hHtop)
  refine ⟨x, hxQ', fun hxQ => hxH (Subgroup.mem_subgroupOf.2 hxQ), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨y, hlt.le hy⟩).1 (Subgroup.mem_subgroupOf.2 hy)
    simpa using Subgroup.mem_subgroupOf.1 h1
  · intro hy
    have hyQ' : y ∈ Q' := by
      have h1 : x * y * x⁻¹ ∈ Q' := hlt.le hy
      have h2 := Q'.mul_mem (Q'.mul_mem (Q'.inv_mem hxQ') h1) hxQ'
      simpa [mul_assoc] using h2
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨y, hyQ'⟩).2 (Subgroup.mem_subgroupOf.2 (by simpa using hy))
    exact Subgroup.mem_subgroupOf.1 h1

theorem le_normalizer_iSup_of_invariant {Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (h𝒟 : ∀ L ∈ 𝒟, ∀ g ∈ Y, GLBConj g L ∈ 𝒟) :
    Y ≤ Subgroup.normalizer ((⨆ L ∈ 𝒟, L : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Y, GLBConj g (⨆ L ∈ 𝒟, L) ≤ ⨆ L ∈ 𝒟, L := by
    intro g hg
    rw [gLBConj_iSup_eq]
    refine iSup_le fun L => ?_
    rw [gLBConj_iSup_eq]
    exact iSup_le fun hL => le_iSup₂_of_le (GLBConj g L) (h𝒟 L hL g hg) le_rfl
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g hg) ?_
  have h1 := gLBConj_mono g (key g⁻¹ (Y.inv_mem hg))
  rwa [gLBConj_gLBConj_inv] at h1

theorem isD4Comp_gLBConj {Y L : Subgroup G} (hL : IsD4Comp Y L) {g : G} (hg : g ∈ Y) :
    IsD4Comp Y (GLBConj g L) := by
  refine ⟨?_, ?_⟩
  · have h1 := glaPComponent_gLBConj hL.1 g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h1
  · exact CFSG.Models.LieModel.of_mulEquiv (Claims139.centerQuotCongr (conjQuotEquiv 5 g L)) hL.2

end Tools

section Wreath

theorem eq_one_of_forall_centModIn {M R K₁ A₀ : Subgroup G} {𝒞 𝒟 : Set (Subgroup G)} (hRM : R ≤ M)
    (hRp : IsPGroup 5 ↥R) (h𝒟inv : ∀ L ∈ 𝒟, ∀ g ∈ M, GLBConj g L ∈ 𝒟) (h𝒞𝒟 : 𝒞 ⊆ 𝒟)
    (h𝒞M : ∀ L ∈ 𝒞, GLAPComponent 5 M L) (hK₁𝒞 : K₁ ≤ ⨆ L ∈ 𝒞, L) (hK₁M : K₁ ≤ M)
    (hs : IsSimpleGroup (barOf 5 K₁)) (hnab : ∃ u v : barOf 5 K₁, u * v ≠ v * u) (hA₀K₁ : A₀ ≤ K₁)
    (hA₀el : IsElemAbelian 5 A₀) (hZ : omegaOne 5 (centerOf R) ≤ A₀) {r : G} (hr : r ∈ R)
    (hc : ∀ L ∈ 𝒟, r ∈ centModIn R L) : r = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := R ⊓ ⨅ L ∈ 𝒟, centModIn R L with hC
  have hmemC : ∀ x, x ∈ C ↔ x ∈ R ∧ ∀ L ∈ 𝒟, x ∈ centModIn R L := by
    intro x
    simp only [hC, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hCR : C ≤ R := inf_le_left
  have hCn : (C.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCR]
    have key : ∀ g ∈ R, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      obtain ⟨hcR, hcL⟩ := (hmemC c).1 hc
      refine (hmemC _).2 ⟨R.mul_mem (R.mul_mem hg hcR) (R.inv_mem hg), fun L hL => ?_⟩
      exact conj_mem_centModIn_of_gLBConj hg (hcL _ (h𝒟inv L hL g (hRM hg)))
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact key g hg c
    · intro hc
      have := key g⁻¹ (R.inv_mem hg) _ hc
      simpa [mul_assoc] using this
  by_contra hr1
  have hCne : C ≠ ⊥ := by
    intro hb
    have hrC : r ∈ C := (hmemC r).2 ⟨hr, hc⟩
    rw [hb, Subgroup.mem_bot] at hrC
    exact hr1 hrC
  obtain ⟨z, hzC, hzZ, hz1⟩ := Claims1110b.exists_mem_omegaOne_centerOf hRp hCR hCn hCne
  have hzA : z ∈ A₀ := hZ hzZ
  obtain ⟨-, hzL⟩ := (hmemC z).1 hzC
  have hle : (⨆ L ∈ 𝒞, L) ≤ commModCoreSub M z := by
    refine iSup₂_le fun L hL => fun x hx => ⟨(h𝒞M L hL).1 hx, ?_⟩
    have h1 := Subgroup.inv_mem _ ((mem_centModIn.1 (hzL L (h𝒞𝒟 hL))).2.2 x hx)
    have e : (x * z * x⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * x⁻¹ := by group
    rw [e] at h1
    exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 (h𝒞M L hL).2.1 h1
  exact hz1 (eq_one_of_comm_mem_coprime (card_gLAPPrimeCoreOf_coprime 5 M)
    (hK₁M.trans (le_normalizer_gLAPPrimeCoreOf 5 M)) hs hnab (hA₀K₁ hzA) (hA₀el.2 z hzA)
    fun k hk => ((hK₁𝒞.trans hle) hk).2)

theorem step6WreathClaim_of_inputs (h119 : Lemma119Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hR1 : InputD4ThreeRank)
    (hR3 : InputD4LayerGen) (hR4 : InputFi22GammaThree) : Step6WreathClaim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY K₁ hK₁ hK₁le hA0K₁ hs
    hnab hlie 𝒞 h𝒞 hK₁𝒞 h𝒞st h𝒞tr hcase
  obtain ⟨rfl, hfi⟩ := hb
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hAel : IsElemAbelian 5 A := hsc.2.2.1
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have haA : a ∈ A := h.ha.1
  have haM : a ∈ M := hAM haA
  have ha5 : a ^ 5 = 1 := hAel.2 a haA
  have hK₁M : K₁ ≤ M := hK₁.1.trans inf_le_left
  have hZ₁ : Subgroup.center (barOf 5 K₁) = ⊥ := by
    haveI := hs
    exact CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hlieZ : CFSG.Models.LieModel (barOf 5 K₁ ⧸ Subgroup.center (barOf 5 K₁)) .POmegaPlus 4 2 1 :=
    CFSG.Models.LieModel.of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ₁.symm)) hlie
  have h𝒞D4 : ∀ L ∈ 𝒞, IsD4Comp M L := by
    intro L hL
    obtain ⟨e⟩ := AltFacts6.diag_iso_of_family hp haM ha5 h.ha.2 hK₁ h𝒞 hK₁𝒞 h𝒞st h𝒞tr hL
      (Or.inl (hcase L hL))
    exact ⟨h𝒞 L hL, CFSG.Models.LieModel.of_mulEquiv e hlieZ⟩
  set 𝒟 : Set (Subgroup G) := {L | IsD4Comp M L} with h𝒟def
  have h𝒞𝒟 : 𝒞 ⊆ 𝒟 := fun L hL => h𝒞D4 L hL
  have h𝒟inv : ∀ L ∈ 𝒟, ∀ g ∈ M, GLBConj g L ∈ 𝒟 := fun L hL g hg => isD4Comp_gLBConj hL hg
  obtain ⟨L₀, hL₀⟩ : ∃ L, L ∈ 𝒞 := by
    by_contra hcon
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := iSup₂_eq_bot.2 fun L hL => absurd ⟨L, hL⟩ hcon
    rw [hbot] at hK₁𝒞
    exact AltFacts6.ne_bot_of_pComponent hp hK₁ (le_bot_iff.1 hK₁𝒞)
  have hL₀a : GLBConj a L₀ ∈ 𝒞 := h𝒞st L₀ hL₀ a (Subgroup.mem_zpowers a)
  have h2𝒟 : 2 ≤ 𝒟.ncard := by
    have h1 : ({L₀, GLBConj a L₀} : Set (Subgroup G)).ncard = 2 := Set.ncard_pair (hcase L₀ hL₀).symm
    rw [← h1]
    exact Set.ncard_le_ncard (Set.insert_subset_iff.2 ⟨h𝒞𝒟 hL₀, Set.singleton_subset_iff.2 (h𝒞𝒟 hL₀a)⟩)
      (Set.toFinite _)
  set J : Subgroup G := ⨆ L ∈ 𝒟, L with hJdef
  have hJM : J ≤ M := iSup₂_le fun L hL => hL.1.1
  have hMJ : M ≤ Subgroup.normalizer (J : Set G) := le_normalizer_iSup_of_invariant h𝒟inv
  have hMK : CFSG.Open.IsKGroup ↥M :=
    h.standing.kProper.isKGroup M (isTwoLocal_ne_top h.standing h.pre.1.1)
  have hJ3 : 4 * 𝒟.ncard ≤ CFSG.Open.pRank 3 J := hR1 G M hMK 𝒟 fun L hL => hL
  have hm : m ≤ 2 * 𝒟.ncard := by
    have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
    have hBel : IsElemAbelian 5 B := hS.bOne.1.1
    obtain ⟨y, -, T, hTp, hTM, hRT, hBT⟩ :=
      exists_conj_le_pGroup' hR.1 hR.2.1 hBM (Claims1110.isPGroup_of_elemAb hBel)
    have hTR : T = R := hR.2.2 T hTM hTp hRT
    rw [hTR] at hBT
    set F := GLBConj y B with hFdef
    have hFel : IsElemAbelian 5 F := Claims1110.isElemAbelian_conj y hBel
    have hFc : Nat.card ↥F = 5 ^ m := by rw [hFdef, Claims1110.card_conj, hS.standing.card_eq hS.bOne]
    have hFM : F ≤ M := hBT.trans hR.1
    have hFrk : CFSG.Open.pRank 5 F = m := by
      have h1 := l1110_card_eq_pow_pRank hFel
      rw [hFc] at h1
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1).symm
    have hFrank : GLATwoLocalRank 5 ↥M ≤ CFSG.Open.pRank 5 F := by
      rw [hFrk]
      exact (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp M).trans
        hS.standing.rank_eq.le
    have hFN : ∀ L ∈ 𝒟, F ≤ Subgroup.normalizer (L : Set G) := by
      intro L hL
      by_contra hn
      have h1 := (h112 G m 5 hS.standing M F L hFel hFM hFrank hL.1 hn).1
      norm_num at h1
    have hfaith : ∀ f ∈ F, (∀ L ∈ 𝒟, f ∈ centModIn F L) → f = 1 := by
      intro f hf hfL
      refine eq_one_of_forall_centModIn hR.1 hR.2.1 h𝒟inv h𝒞𝒟 h𝒞 hK₁𝒞 hK₁M hs hnab hA0K₁ hA0el hZ.le (hBT hf)
        fun L hL => ?_
      obtain ⟨-, hfN, hfc⟩ := mem_centModIn.1 (hfL L hL)
      exact mem_centModIn.2 ⟨hBT hf, hfN, hfc⟩
    classical
    haveI : Fintype ↥𝒟 := Fintype.ofFinite _
    let H : ↥𝒟 → Subgroup ↥F := fun L => (centModIn F L.1).subgroupOf F
    have hbot : (⨅ L, H L) = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Subgroup.mem_iInf] at hf
      have h1 : (f : G) = 1 := hfaith f f.2 fun L hL => Subgroup.mem_subgroupOf.1 (hf ⟨L, hL⟩)
      exact Subgroup.mem_bot.2 (Subtype.ext h1)
    have hidx : ∀ L : ↥𝒟, (H L).index ≤ 5 ^ 2 := by
      intro L
      have h1 := card_le_of_isD4Comp L.2 hFel (hFN L.1 L.2)
      have h2 : Nat.card ↥(H L) = Nat.card ↥(centModIn F L.1) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (fun x hx => (mem_centModIn.1 hx).1 : centModIn F L.1 ≤ F)).toEquiv
      have h3 := (H L).card_mul_index
      rw [h2] at h3
      have hpos : 0 < Nat.card ↥(centModIn F L.1) := Nat.card_pos
      by_contra hcon
      push Not at hcon
      have : Nat.card ↥(centModIn F L.1) * 5 ^ 2 < Nat.card ↥(centModIn F L.1) * (H L).index :=
        Nat.mul_lt_mul_of_pos_left hcon hpos
      omega
    have hle := Subgroup.index_iInf_le H
    rw [hbot, Subgroup.index_bot] at hle
    have hprod : ∏ L : ↥𝒟, (H L).index ≤ (5 ^ 2) ^ (Finset.univ : Finset ↥𝒟).card :=
      Finset.prod_le_pow_card _ _ _ fun L _ => hidx L
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← pow_mul] at hprod
    rw [hFc] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 (hle.trans hprod)
  have hWC : GLAWeakCoreLocal G 3 := by
    obtain ⟨E₃, hE₃J, hE₃el, hE₃c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) J
    obtain ⟨T, hT1, hT2, hMT⟩ := h.pre.1.1
    have hE₃N : E₃ ≤ Subgroup.normalizer (T : Set G) := hMT ▸ hE₃J.trans hJM
    have hle := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
      (by norm_num : 1 < 3) hT1 hT2 hE₃el hE₃N hE₃c
    have h3dvd : 3 ∣ Nat.card G := by
      have h1 : 3 ∣ Nat.card ↥E₃ := by
        rw [hE₃c]
        exact dvd_pow_self 3 (by omega)
      exact h1.trans (Subgroup.card_subgroup_dvd_card E₃)
    have hbeta : 3 ∈ GLABeta (m + 1) G := ⟨Nat.prime_three, by norm_num, h3dvd, by omega⟩
    exact h.standing.weakCoreLocal 3 hbeta
  have hstar : ∀ Q : Subgroup G, Q ≤ M → IsPGroup 3 ↥Q → 3 ≤ CFSG.Open.pRank 3 Q →
      Subgroup.normalizer (Q : Set G) ≤ M := by
    intro Q hQM hQp hQ3
    obtain ⟨P', hP', hQP'⟩ := Claims1110.exists_sylowIn_above'' hQM hQp
    obtain ⟨Pst, hP'P⟩ := hP'.2.1.exists_le_sylow
    have hS' : IsSylowIn 3 J (P' ⊓ J) := Claims1110d.isSylowIn_inf' hP' hJM hMJ
    have hS3 : 3 ≤ CFSG.Open.pRank 3 (P' ⊓ J) := le_trans (by omega) (hJ3.trans (pRank_le_of_isSylowIn hS'))
    have hJcore : J ≤ GLBCore 3 3 (P' ⊓ J) := hR3 G M hMK 𝒟 (fun L hL => hL) h2𝒟 _ hS'
    have hNS : Subgroup.normalizer ((P' ⊓ J : Subgroup G) : Set G) ≤ GLBCore 3 3 (P' ⊓ J) :=
      le_sSup ⟨_, le_rfl, hS3, rfl⟩
    have hcore : GLBCore 3 3 (P' ⊓ J) ≤ rankThreeAschCore 2 3 (Pst : Subgroup G) := by
      refine sSup_le ?_
      rintro _ ⟨X, hX, hX3, rfl⟩
      exact le_sSup ⟨X, hX.trans (inf_le_left.trans hP'P), by omega,
        hX3.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left), rfl⟩
    have hMcore : M ≤ rankThreeAschCore 2 3 (Pst : Subgroup G) :=
      (le_sup_normalizer_of_isSylowIn hMJ hS').trans (sup_le (hJcore.trans hcore) (hNS.trans hcore))
    obtain ⟨H, hH, hcoreH⟩ := hWC.2 Pst
    have hcoreH' : rankThreeAschCore 2 3 (Pst : Subgroup G) ≤ H := hcoreH
    have hHM : H = M := h.pre.1.2 H hH (hMcore.trans hcoreH')
    have hQcore : Subgroup.normalizer (Q : Set G) ≤ rankThreeAschCore 2 3 (Pst : Subgroup G) :=
      le_sSup ⟨Q, hQP'.trans hP'P, by omega,
        hQ3.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left), rfl⟩
    exact hQcore.trans (hHM ▸ hcoreH')
  obtain ⟨Q, hQ, -⟩ := Claims1110.exists_sylowIn_above'' (p := 3) (bot_le : ⊥ ≤ K ⊓ M) IsPGroup.of_bot
  have hK₁3 : 4 ≤ CFSG.Open.pRank 3 K₁ := by
    have h1 := hR1 G (M ⊓ Cg a) (hMK.of_le inf_le_left) {K₁} fun L hL => by
      rw [Set.mem_singleton_iff] at hL
      subst hL
      exact ⟨hK₁, hlieZ⟩
    simpa using h1
  have hQ3 : 4 ≤ CFSG.Open.pRank 3 Q :=
    hK₁3.trans ((CFSG.SectionRank.pRank_mono (by norm_num) hK₁le).trans (pRank_le_of_isSylowIn hQ))
  have hQN := hstar Q (hQ.1.trans inf_le_right) hQ.2.1 (by omega)
  have hQK : IsSylowIn 3 K Q := by
    refine ⟨hQ.1.trans inf_le_left, hQ.2.1, fun Q' hQ'K hQ'p hQQ' => ?_⟩
    by_contra hne
    obtain ⟨x, hxQ', hxQ, hxN⟩ := exists_mem_normalizer_of_lt_of_isPGroup hQ'p (lt_of_le_of_ne hQQ' (Ne.symm hne))
    have hle : Q ⊔ Subgroup.zpowers x ≤ K ⊓ M :=
      sup_le hQ.1 ((Subgroup.zpowers_le).2 ⟨hQ'K hxQ', hQN hxN⟩)
    have hp3 : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers x) :=
      hQ'p.to_le (sup_le hQQ' ((Subgroup.zpowers_le).2 hxQ'))
    have heq := hQ.2.2 _ hle hp3 le_sup_left
    exact hxQ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hv : (Nat.card ↥(K ⊓ M)).factorization 3 = (Nat.card ↥K).factorization 3 :=
    Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3))
      ((Claims1110.card_of_isSylowIn hQ).symm.trans (Claims1110.card_of_isSylowIn hQK))
  set π : ↥K →* ↥K ⧸ GLAPPrimeCore 5 ↥K := QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) with hπ
  set A₀' : Subgroup ↥K := (E ⊓ A).subgroupOf K with hA₀'
  have hA0K : E ⊓ A ≤ K := by rw [hA2]; exact inf_le_right
  have hOcop : Nat.Coprime 5 (Nat.card ↥(GLAPPrimeCore 5 ↥K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
  have hA₀'c : Nat.card ↥A₀' = 5 ^ 2 := by
    rw [hA₀', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0K).toEquiv, hA0c]
  have hPc : Nat.card ↥(A₀'.map π) = 5 ^ 2 := by
    have hinj : Function.Injective (π.comp A₀'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have hx5 : (x : ↥K) ^ 5 = 1 :=
        Subtype.ext (by simpa using hA0el.2 _ (Subgroup.mem_subgroupOf.1 x.2))
      exact Subgroup.mem_bot.2 (Subtype.ext (Claims1110.eq_one_of_dvd_coprime hOcop
        (orderOf_dvd_of_pow_eq_one hx5) (Subgroup.orderOf_dvd_natCard _ hx)))
    have h1 : (π.comp A₀'.subtype).range = A₀'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hA₀'c]
  have hlt := hR4 (barOf 5 K) hfi (A₀'.map π) (IsPGroup.of_card hPc) hPc
  set HK : Subgroup ↥K := (K ⊓ M).subgroupOf K with hHK
  have hker : HK ⊓ π.ker = π.ker := by
    refine inf_eq_right.2 fun o ho => ?_
    rw [hπ, QuotientGroup.ker_mk'] at ho
    have hoM : (o : G) ∈ M := hOK ((mem_gLAPPrimeCoreOf_iff 5 K o).2 ⟨o.2, ho⟩)
    exact Subgroup.mem_subgroupOf.2 ⟨o.2, hoM⟩
  have hcardKM : Nat.card ↥(K ⊓ M) =
      Nat.card ↥(Claims1110b.gammaK0 (A₀'.map π)) * Nat.card ↥(GLAPPrimeCore 5 ↥K) := by
    have h1 := Claims1110e.card_map_mul_card_inf_ker π HK
    have hkerπ : π.ker = GLAPPrimeCore 5 ↥K := QuotientGroup.ker_mk' _
    have hY' : HK.map π = Claims1110b.gammaK0 (A₀'.map π) := hY
    rw [hker, hkerπ, hY'] at h1
    rw [h1, hHK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hcardK : Nat.card ↥K = Nat.card (barOf 5 K) * Nat.card ↥(GLAPPrimeCore 5 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hO0 : Nat.card ↥(GLAPPrimeCore 5 ↥K) ≠ 0 := Nat.card_pos.ne'
  have hΓ0 : Nat.card ↥(Claims1110b.gammaK0 (A₀'.map π)) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card (barOf 5 K) ≠ 0 := Nat.card_pos.ne'
  have e1 : (Nat.card ↥(K ⊓ M)).factorization 3 =
      (Nat.card ↥(Claims1110b.gammaK0 (A₀'.map π))).factorization 3 +
        (Nat.card ↥(GLAPPrimeCore 5 ↥K)).factorization 3 := by
    rw [hcardKM, Nat.factorization_mul hΓ0 hO0, Finsupp.add_apply]
  have e2 : (Nat.card ↥K).factorization 3 =
      (Nat.card (barOf 5 K)).factorization 3 + (Nat.card ↥(GLAPPrimeCore 5 ↥K)).factorization 3 := by
    rw [hcardK, Nat.factorization_mul hK0 hO0, Finsupp.add_apply]
  have hlt' : (Nat.card ↥(Claims1110b.gammaK0 (A₀'.map π))).factorization 3 <
      (Nat.card (barOf 5 K)).factorization 3 := hlt
  omega

theorem step6K1Claim_of_inputs (h119 : Lemma119Statement)
    (h1834 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hres : InputD4UpRank)
    (hR1 : InputD4ThreeRank) (hR3 : InputD4LayerGen) (hR4 : InputFi22GammaThree) :
    Claims1110f.Step6K1Claim :=
  step6K1Claim_of_wreath h119 h1834 hres (step6WreathClaim_of_inputs h119 h112 hR1 hR3 hR4)

end Wreath

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110i
