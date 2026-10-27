module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieNR
public import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieE
public import CFSG.ClassicalInvolution.Q3.TL4SecOrbit
public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS
public import CFSG.ClassicalInvolution.Q3.TL4Conn26S4B
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint
open scoped commutatorElement

@[expose] def SecIdE3MuZ2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    EdgelessMember3 R S t → MuZ2Member R → ¬ TightInO2 t →
      ((¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
        Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) →
      IsSimpleGroup ↥(genFittingFStar Y) ∧ (genFittingFStar Y).index ≤ 2 ∧
        ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
          ((Even f ∧ LieModel (FStarQuot Y) .PSL 2 p f) ∨ LieModel (FStarQuot Y) .PSL 3 p f ∨
            LieModel (FStarQuot Y) .PSU 3 p f)) ∨
          NativeSporadic.IsSporadic (FStarQuot Y) .M12)

@[expose] def SecIdNoRootAE5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → ¬ T3.DStarConnected Φ →
    Nonempty (TC.Thin.AEIdent Φ 5) →
      ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
        IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
          ∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
            (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x

@[expose] def SecIdE4GenAE5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → ¬ T3.DStarConnected Φ →
    Nonempty (TC.Thin.AEIdent Φ 5) →
      ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
        IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
          ∀ σ : MulAut X, σ * σ = 1 → σ x' = x' → (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
            (∀ k ∈ B, σ k ∈ B) → (¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) →
              Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
                {g | σ (x' * g * x'⁻¹) = g}) = ⊤

@[expose] def SecIdE2EdgelessBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → TightInO2 t → TightEdgeless R →
      (∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W) →
      tightCore R = ⊤

@[expose] def SecIdE2DStarBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → TightInO2 t → ¬ TightEdgeless R →
      ¬ T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) →
      Nonempty (TC.Thin.AEIdent (CoreAssembly.conjClass (tightCore R)) 5)

section Mu

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem muIsoZ2_forall_of_exists (hP : Q3CL.PartIHypG Ω) (hE : Disconnected.DEdgeless Ω)
    {W' : Subgroup G} (hW' : W' ∈ WSet Ω) (hZ : MuIsoZ2 Ω W') (hne : Ω.Nonempty) :
    ∀ W ∈ WSet Ω, MuIsoZ2 Ω W := by
  intro W hW
  by_cases hs : ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty
  · exfalso
    obtain ⟨e3⟩ := Q3T6.Mu.muIsoS3_of_shape hP hW' hE hs
    obtain ⟨e2⟩ := hZ
    have h1 := Nat.card_congr (e3.symm.trans e2).toEquiv
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin] at h1
    exact absurd h1 (by decide)
  · push Not at hs
    exact Q3T6.Mu.muIsoZ2_of_shape hP hW hne hs

end Mu

section Model

theorem exists_ne_comm_of_quat {Y : Type} [Group Y] {R : Subgroup Y} {S : Sylow 2 R}
    (e : ↥(S : Subgroup R) ≃* QuaternionGroup 2) : ∃ a b : Y, a * b ≠ b * a := by
  refine ⟨((e.symm (.a 1) : R) : Y), ((e.symm (.xa 0) : R) : Y), fun h => ?_⟩
  have h' : e.symm (.a 1) * e.symm (.xa 0) = e.symm (.xa 0) * e.symm (.a 1) :=
    Subtype.ext (Subtype.ext h)
  have h'' := congrArg e h'
  simp only [map_mul, MulEquiv.apply_symm_apply] at h''
  exact absurd h'' (by decide)

theorem index_dvd_six_of_le_two {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (h : H.index ≤ 2) : H.index ∣ 6 := by
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge H.index 2 with h1 | h1
  · rw [show H.index = 1 by omega]
    exact one_dvd 6
  · rw [show H.index = 2 by omega]
    norm_num

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem concl164_of_e3 (hM : Model164) (hT : MuZ2Table) (hE3 : SecIdE3MuZ2)
    (hm : EdgelessMember3 R S t) (hmu : MuZ2Member R) (hO2 : ¬ TightInO2 t)
    (hx : (¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) : Concl164 R t := by
  obtain ⟨hL2, -, hL3, hU3⟩ := hM
  obtain ⟨hFs, hi, hX⟩ := hE3 Y R S t hm hmu hO2 hx
  obtain ⟨hTL3, hTU3, -, -, hTM12⟩ := hT Y R S t hm hmu hFs (index_dvd_six_of_le_two hi)
  rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl⟩ | hl | hl⟩ | hm12
  · exact hL2 Y R S t hm hmu hFs hi p f hp hp2 hf hl
  · obtain ⟨hs, hl'⟩ := hTL3 p f hl
    exact hL3 Y R S t hm hmu hs p f hp hp2 hl'
  · obtain ⟨hs, hl', h4⟩ := hTU3 p f hl
    exact hU3 Y R S t hm hmu hs p f hp hp2 h4 hl'
  · exact absurd hm12 hTM12

theorem fstar_of_lieModel {Y : Type} [Group Y] [Finite Y] (hnab : ∃ a b : Y, a * b ≠ b * a)
    {t : Assembly.LowTwoRank.StatedLieTag} {k p f : ℕ} (h : LieModel Y t k p f) :
    IsSimpleGroup ↥(genFittingFStar Y) ∧ (genFittingFStar Y).index = 1 ∧
      LieModel (FStarQuot Y) t k p f := by
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple Y t k p f h
  have htop :=
    CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar Y) ≃* Y := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hFs : IsSimpleGroup ↥(genFittingFStar Y) := eF.isSimpleGroup
  have hZ : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar Y))
      with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : eF.symm a ∈ Subgroup.center ↥(genFittingFStar Y) := by
        rw [ht]
        exact Subgroup.mem_top _
      have hc := Subgroup.mem_center_iff.mp ha (eF.symm b)
      apply hab
      have := congrArg eF hc
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this.symm
  refine ⟨hFs, ?_, ?_⟩
  · rw [htop, Subgroup.index_top]
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eF).symm h

theorem concl164_of_lie (hM : Model164) (hT : MuZ2Table) (hm : EdgelessMember3 R S t)
    (hmu : MuZ2Member R) (hY : LieModel Y .PSL 3 3 1 ∨ LieModel Y .PSU 3 3 1 ∨
      LieModel Y .G2 0 3 1 ∨ LieModel Y .trialityD4 0 3 1 ∨ NativeSporadic.IsSporadic Y .M11) :
    Concl164 R t := by
  obtain ⟨-, hM11, hL3, -⟩ := hM
  obtain ⟨eQ⟩ : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := hm.cls.1
  have hnab := exists_ne_comm_of_quat eQ
  rcases hY with h | h | h | h | h
  · obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple Y _ _ _ _ h
    exact hL3 Y R S t hm hmu hs 3 1 Nat.prime_three (by norm_num) h
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    have h4 := ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.1 3 1 hF).2.2
    norm_num at h4
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact absurd hF ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.2.1 3 1)
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact absurd hF ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.2.2.1 3 1)
  · exact hM11 Y R S t hm hmu h

end Model

theorem exists_datum_of_not_dstarConnected {n : ℕ} (h4 : Thm4RBelow 3 n) {X : Type} [Group X]
    [Finite X]
    (hn : Nat.card X < n) {Φ : Set (Subgroup X)} (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hds : ¬ T3.DStarConnected Φ) {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') ∧ ∃ (S : Sylow 2 ↥A) (z : X),
      TightDatum A S z ∧ TightCls X A S z ∧ CoreAssembly.conjClass (tightCore A) = Φ ∧
        ¬ TightEdgeless A := by
  have htr := omegaTransitive_of_not_dstarConnected h4 h hO hn hA hds
  obtain ⟨S, z, hd, hc, hcl⟩ := exists_datum_of_omegaTransitive h hO hgen hA htr
  refine ⟨fun L hL L' hL' => ?_, S, z, hd, hc, hcl, fun hE => ?_⟩
  · obtain ⟨g, -, hg⟩ := htr L hL
    obtain ⟨g', -, hg'⟩ := htr L' hL'
    exact ⟨g' * g⁻¹, by rw [conjSub_mul, ← hg, conjSub_inv_conjSub, hg']⟩
  · have hE' : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore A)) := hE
    rw [hcl] at hE'
    exact hE' A hA B hB.1 (Or.inl hB)

section Cit3

variable {n : ℕ}

theorem secIdDStar_cases_below (hS : SecIdentDatum3 n) (hE2 : SecIdE2DStarBelow n)
    (hE4 : SecIdE4DStar) {Y : Type} [Group Y] [Finite Y] (hn : Nat.card Y < n) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (he : ¬ TightEdgeless R) (hds : ¬ T3.DStarConnected (CoreAssembly.conjClass (tightCore R))) :
    Nonempty (TC.Thin.AEIdent (CoreAssembly.conjClass (tightCore R)) 5) ∨ SecIdLie3 R t := by
  by_cases hO2 : TightInO2 t
  · exact Or.inl (hE2 Y hn R S t hd hc hO2 he hds)
  · rcases hS Y hn R S t hd hc with h2 | ⟨hE, -⟩ | ⟨hE, -⟩ | ⟨hZ, hm⟩ | hl
    · exact absurd h2 hO2
    · exact absurd hE he
    · exact absurd hE he
    · exact absurd (hE4 Y R S t hd hc hO2 hZ hm) hds
    · exact Or.inr hl

section Lift

theorem tightSecNoRootR_three_of_below (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n)
    (hCIT : Uniform.CITBelowT (.sl2 3 1) n) (hIH : Uniform.IH8T 3 1 n)
    (hE2 : SecIdE2DStarBelow n) (hE4 : SecIdE4DStar) (hM : SecIdNoRootAE5) :
    TightSecNoRootR 3 n := by
  intro X _ _ hn Φ h hO hgen hA hds A hAΦ B hB x x' hx hx' hxx'
  obtain ⟨htr, S, z, hd, hc, hcl, he⟩ :=
    exists_datum_of_not_dstarConnected h4 hn h hO hgen hds hAΦ hB
  rcases secIdDStar_cases_below hS hE2 hE4 hn hd hc he (by rw [hcl]; exact hds) with hAE | hl
  · rw [hcl] at hAE
    obtain ⟨I⟩ := hAE
    exact ⟨hM X Φ h hO hgen hA htr hds ⟨I⟩ A hAΦ B hB x x' hx hx' hxx',
      fun e heA heB _ P hP hPA hPB v hv g hg k hk =>
        AE5.ne_mul_inv_inv h hO hgen I hAΦ hB hx hx' hxx' heA heB hP hPA hPB hv hg hk⟩
  · subst hcl
    obtain ⟨h1, h2⟩ := hl.noRoot hCIT hIH hn hd hc h.noTwins hds A hAΦ B hB x x' hx hx' hxx'
    exact ⟨h1, fun e heA heB hee _ _ _ _ _ _ _ _ _ _ _ => absurd hee (h2 e heA heB)⟩

theorem tightE4SecGenR_three_of_below (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n)
    (hCIT : Uniform.CITBelowT (.sl2 3 1) n) (hIH : Uniform.IH8T 3 1 n)
    (hE2 : SecIdE2DStarBelow n) (hE4 : SecIdE4DStar) (hM : SecIdE4GenAE5) :
    TightE4SecGenR 3 n := by
  intro X _ _ hn Φ h hO hgen hA hds A hAΦ B hB x x' hx hx' hxx'
  obtain ⟨htr, S, z, hd, hc, hcl, he⟩ :=
    exists_datum_of_not_dstarConnected h4 hn h hO hgen hds hAΦ hB
  rcases secIdDStar_cases_below hS hE2 hE4 hn hd hc he (by rw [hcl]; exact hds) with hAE | hl
  · rw [hcl] at hAE
    exact hM X Φ h hO hgen hA htr hds hAE A hAΦ B hB x x' hx hx' hxx'
  · subst hcl
    exact hl.e4Gen hCIT hIH hn hd hc h.noTwins hds A hAΦ B hB x x' hx hx' hxx'

end Lift

theorem tightS26DichR_three_of_below (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n)
    (hE2 : SecIdE2EdgelessBelow n) (hE4 : SecIdE4Edge) (hLie : SecIdLieEdgeless3Below n)
    (hE3 : SecIdE3MuZ2) (hT : MuZ2Table) (hM : Model164) : TightS26DichR 3 n := by
  intro X _ _ hn Φ h hO hgen hA hE htop hmu' A hAΦ u hu m _ hou hP β hβu hβ
  have htr := omegaTransitive_of_dEdgeless h4 h hO hn hAΦ hE
  obtain ⟨S, z, hd, hc, hcl⟩ := exists_datum_of_omegaTransitive h hO hgen hAΦ htr
  have hcore : tightCore A = A := h.closure_twoElts hAΦ
  obtain ⟨P, hPs, hPc⟩ := hP
  obtain ⟨e⟩ : Nonempty (↥P ≃* QuaternionGroup 2) := h.quat A hAΦ P hPs
  have h8 : Nat.card ↥P = 2 ^ 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hm1 : m = 1 := by
    rw [h8] at hPc
    have := Nat.pow_right_injective le_rfl hPc
    omega
  subst hm1
  have hE' : TightEdgeless A := by
    show Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore A))
    rw [hcl]
    exact hE
  have hm : EdgelessMember3 A S z := ⟨hd, hc, hE'⟩
  have hmu : MuZ2Member A := by
    obtain ⟨W', hW', hZ⟩ := hmu'
    have hP' : Q3CL.PartIHypG Φ := hcl ▸ hd.partIHypG
    show ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore A)),
      MuIsoZ2 (CoreAssembly.conjClass (tightCore A)) W
    rw [hcl]
    exact muIsoZ2_forall_of_exists hP' hE hW' hZ ⟨A, hAΦ⟩
  have h164 : Concl164 A z := by
    by_cases hO2 : TightInO2 z
    · exfalso
      have hW : ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore A)),
          MuIsoZ2 (CoreAssembly.conjClass (tightCore A)) W := by
        rw [hcl]
        exact hmu'
      have hAt := hE2 X hn A S z hd hc hO2 hE' hW
      rw [hcore] at hAt
      exact htop (hAt ▸ hAΦ)
    · rcases hS X hn A S z hd hc with h2 | ⟨-, h3, hx⟩ | ⟨-, hx⟩ | ⟨hZ, hmod⟩ | hl
      · exact absurd h2 hO2
      · exact concl164_of_e3 hM hT hE3 hm hmu hO2 (Or.inl ⟨h3, hx⟩)
      · exact concl164_of_e3 hM hT hE3 hm hmu hO2 (Or.inr hx)
      · exact absurd hE' (hE4 X A S z hd hc hO2 hZ hmod)
      · exact concl164_of_lie hM hT hm hmu (hLie X hn A S z hd hc hl hE')
  have hz : IsUniqueInvolution A z := hcore ▸ hd.isUniqueInvolution_core
  have hu2 : u ^ 2 ^ 1 = z := by
    have hsq : u ^ 2 ^ 1 * u ^ 2 ^ 1 = 1 := by
      rw [← pow_add, show 2 ^ 1 + 2 ^ 1 = 2 ^ (1 + 1) by norm_num, ← hou, pow_orderOf_eq_one]
    rcases hz.unique _ (A.pow_mem hu _) hsq with h1 | h1
    · exfalso
      have hd' := orderOf_dvd_of_pow_eq_one h1
      rw [hou] at hd'
      norm_num at hd'
    · exact h1
  have hfix : ∀ x ∈ Subgroup.zpowers u, β x = x := by
    rintro x ⟨k, rfl⟩
    simp only [map_zpow, hβu]
  have hUc : Nat.card ↥(Subgroup.zpowers u) = 4 := by
    rw [Nat.card_zpowers, hou]
    norm_num
  have hβ2 : β ^ 2 ^ 1 * β ^ 2 ^ 1 = 1 := by
    rw [← pow_add, show 2 ^ 1 + 2 ^ 1 = 2 ^ (1 + 1) by norm_num]
    exact hβ
  rw [hu2]
  exact h164 (Subgroup.zpowers u) (Subgroup.zpowers_le.mpr hu) inferInstance hUc
    (β ^ 2 ^ 1) β hfix (by rw [pow_one, pow_two]) hβ2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
