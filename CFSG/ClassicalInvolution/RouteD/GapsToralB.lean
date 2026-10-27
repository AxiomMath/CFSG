module

public import CFSG.ClassicalInvolution.RouteD.GapsToralD
public import CFSG.ClassicalInvolution.RouteD.GapsPatternBLast
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.CurtisTits (rankOne)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

section Generation

theorem top_le_of_normal_of_not_le_center {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {N : Subgroup Y} (hN : N.Normal) (hnc : ¬ N ≤ Subgroup.center Y) : ⊤ ≤ N := by
  obtain ⟨hperf, hsimple⟩ := hY
  have hmapN : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have := hmapN
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Y))) with
    h | h
  · exfalso
    apply hnc
    intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center Y) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center Y)) := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact (QuotientGroup.eq_one_iff x).1 (by simpa using hx')
  · have hsup : ∀ g : Y, ∃ a ∈ N, ∃ z ∈ Subgroup.center Y, g = a * z := by
      intro g
      have : QuotientGroup.mk' (Subgroup.center Y) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center Y)) := by rw [h]; trivial
      obtain ⟨a, ha, hag⟩ := this
      exact ⟨a, ha, a⁻¹ * g, QuotientGroup.eq.1 hag, by group⟩
    have hcomm : ∀ a b : Y, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hsup a
      obtain ⟨b₁, hb₁, z₂, hz₂, rfl⟩ := hsup b
      rw [commutator_mul_central _ _ _ _ hz₁ hz₂]
      have : ⁅a₁, b₁⁆ = a₁ * (b₁ * a₁⁻¹ * b₁⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem ha₁ (hN.conj_mem _ (inv_mem ha₁) _)
    have hle : ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ N := Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    rw [← commutator_def, hperf] at hle
    exact hle

theorem top_le_iSup_fund_odd {m : ℕ} (hm : 3 ≤ m) (hadm : StatedLieAdmissible .POmegaOdd m p f)
    (hstd : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') :
    (⊤ : Subgroup (modelUniv .POmegaOdd m p f Fact.out).K) ≤
      ⨆ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D, R := by
  have hqs : CFSG.Open.IsQuasisimple (modelUniv .POmegaOdd m p f Fact.out).K :=
    (ModelFacts.modelClauseZero .POmegaOdd m p f Fact.out trivial hadm).1
  set S := ⨆ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D, R
    with hS
  have hnormal : S.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hmapS : S.map (MulAut.conj g).toMonoidHom ≤ S := by
      rw [hS, Subgroup.map_iSup]
      refine iSup_le fun R => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hR => ?_
      exact le_iSup₂_of_le (conjSub g R) (conjSub_mem_fundamentalSubgroups hR g) le_rfl
    exact hmapS ⟨x, hx, rfl⟩
  have hR₀ : rankOne (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (⟨0, by omega⟩ : Fin m) ∈
      fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D :=
    rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p f) hm (i := ⟨0, by omega⟩)
      (by show 0 + 1 < m; omega)
  obtain ⟨R', hR', W, hW⟩ := hstd _ hR₀
  refine top_le_of_normal_of_not_le_center hqs hnormal fun hle => ?_
  have hR₀S : rankOne (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (⟨0, by omega⟩ : Fin m) ≤
      Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K :=
    (le_iSup₂_of_le _ hR₀ le_rfl).trans hle
  refine not_commutes_of_linearBlockStandardPair hW fun a ha b _ => ?_
  exact (Subgroup.mem_center_iff.mp (hR₀S ha) b).symm

theorem range_le_iSup_fund_odd {m : ℕ} (hm : 3 ≤ m) (hadm : StatedLieAdmissible .POmegaOdd m p f)
    (hstd : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') {X : Type} [Group X]
    (ψ : (modelUniv .POmegaOdd m p f Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
      R.map ψ := by
  have h := Subgroup.map_mono (f := ψ) (top_le_iSup_fund_odd hm hadm hstd)
  rw [← MonoidHom.range_eq_map, Subgroup.map_iSup] at h
  refine h.trans (iSup_le fun R => ?_)
  rw [Subgroup.map_iSup]
  exact iSup_le fun hR => le_iSup₂_of_le R hR le_rfl

end Generation

section Wiring

@[expose] def TorusFixedB {m : ℕ} (c : TCtx p f .POmegaOdd m Ω K z) {t : G}
    (htz : t * z * t⁻¹ = z) : Prop :=
  ∃ (i₀ i₁ : Fin m) (_ : i₀ ≠ i₁) (γ₀ : Fin m → ℤ) (s₀ t₀ : Bool)
    (_ : toStdB m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (k : spinGroup (quadOdd m (GaloisField p f)))
    (T : Subgroup (spinGroup (quadOdd m (GaloisField p f)))),
    (∀ y ∈ (((oddDatum m (GaloisField p f)).rootGroup γ₀ ⊔
        (oddDatum m (GaloisField p f)).rootGroup (-γ₀)).map (MulAut.conj k).toMonoidHom),
      locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y) ∧
    (∀ (i j : Fin m) (hij : i ≠ j), i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → ∀ (t : Bool)
      (u : (GaloisField p f)ˣ), (oddFrame m (GaloisField p f)).longTorus hij true t u ∈ T) ∧
    (∀ x ∈ T, locAut c.hΩ.conjInvariant htz (c.d.ψ (k * x * k⁻¹)) = c.d.ψ (k * x * k⁻¹))

theorem toralNormalB_of_torusFixed {m : ℕ} (hm : 5 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    {t : G} (htz : t * z * t⁻¹ = z) (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hT : TorusFixedB c htz) : ToralNormalB c htz := by
  classical
  obtain ⟨i₀, i₁, h01, γ₀, s₀, t₀, hγ₀, k, T, H1, hTT, H2⟩ := hT
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hF : Nat.card (GaloisField p f) = p ^ f := c.card_eq
  have hq : 5 ≤ Nat.card (GaloisField p f) := by rw [hF]; exact c.hq
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf1, by omega, c.hp2⟩
  have hσ2 : ∀ y, locAut c.hΩ.conjInvariant htz (locAut c.hΩ.conjInvariant htz y) = y :=
    locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', locAut c.hΩ.conjInvariant htz (c.d.ψ k') ∈ c.d.ψ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  obtain ⟨k₀, v, hk₀⟩ := ModelFacts.OrthAut.toralNormal_odd_of_subgroups c.hp2 hf1 hF hq
    (by omega : 4 ≤ m) c.d.ψ c.d.ker_le (locAut c.hΩ.conjInvariant htz) hσ2 hσr h01 hγ₀ k H1 T
    hTT H2
  exact ⟨k₀, v, hk₀⟩

theorem PartnerPatternBPair.of_torusFixed {m : ℕ} (hm : 8 ≤ m) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaOdd m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : TorusFixedB c (partner_involution_commutes c.hp2 c.hz ht hKβ))
    (hres : ∀ k₀ v, ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
      LastLongExcluded (p := p) (f := f) m v) :
    PartnerPatternBPair p f m Ω K β t := by
  obtain ⟨W, hW⟩ := hKβ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact PartnerPatternBPair.of_toral_odd_short hm hMFZ c hsingle hshape hβ ht ⟨W, hW⟩ hfixM
    (toralNormalB_of_torusFixed (by omega) c _ h2t hKt hT) hres

end Wiring

end CFSG.ClassicalInvolution.RouteD.Gaps
