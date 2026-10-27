module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownTwOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChev
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    1 ≤ m := by
  have h := Finite.one_lt_card (α := K)
  rw [hK] at h
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0, pow_zero] at h
    exact absurd h (lt_irrefl 1)
  · exact h0

theorem fixAlt_of_raw {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {f : MulAut R}
    {lab₀ : LargeEvenLabel} (hlab₀ : LargeEvenInLambda2 lab₀)
    (h : CFSG.Assembly.LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
      (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀) :
    FixAlt p I f :=
  Or.inl ⟨lab₀, hlab₀, Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ₀, hθ⟩ => ⟨hs, hna, θ₀, fixGeomP_of_ggFixGeom hθ⟩) h⟩

theorem geomBody_of_field {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag ≠ .triD4) {R : Type} [Group R]
    {I F : Set (MulAut R)} (h : IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ f ∈ F,
      orderOf f = p → FixAlt p I f) : GeomBody p lab R I F :=
  fun hs hna => ⟨fun _ f hf hord => Or.inl (h hs hna f hf hord), fun h' => absurd h' ht⟩

theorem dvd_two_pow_div_sub_one' {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (h : p ∣ 2 ^ n - 1) :
    p ∣ 2 ^ (n / p) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left k hp.pos]
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_sub Nat.one_le_two_pow] at h ⊢
  push_cast at h ⊢
  rw [mul_comm p k, pow_mul, ZMod.pow_card] at h
  exact h

section Families

variable {p : ℕ}

theorem cAll_geomBody_A (hp : p.Prime) (hp2 : p ≠ 2) {l n : ℕ} (hl : 2 ≤ l) :
    MI.CAll ⟨.A, l, n⟩ (GeomBody p ⟨.A, l, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have hn : 1 ≤ n := one_le_of_card_field hK
  have h := ggRawFieldFixStd_linear (l := l) hl hn hK (p := p) hS hna f hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.A, l, n / p⟩ := by
    refine ⟨one_le_of_card_field hK₀, ?_⟩
    dsimp only
    exact ⟨by omega, fun h => by omega⟩
  exact fixAlt_of_raw hlab₀ (ggRawFieldFixStd_linear (l := l) hl hn hK (p := p) hS hna f hf hord)

theorem cAll_geomBody_D3 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} :
    MI.CAll ⟨.D, 3, n⟩ (GeomBody p ⟨.D, 3, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have hn : 1 ≤ n := one_le_of_card_field hK
  have h := ggRawFieldFixStd_linear (l := 3) (by norm_num) hn hK (p := p) hS hna f hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.A, 3, n / p⟩ := by
    refine ⟨one_le_of_card_field hK₀, ?_⟩
    dsimp only
    exact ⟨by omega, fun h => by omega⟩
  exact fixAlt_of_raw hlab₀ (ggRawFieldFixStd_linear (l := 3) (by norm_num) hn hK (p := p) hS hna f
    hf hord)

theorem geomBody_sp (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    {l n : ℕ} (hl : 3 ≤ l) [NeZero l] (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    GeomBody p ⟨t, l, n⟩ (LargeEvenProj (LargeEvenSpGroup K l))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K l))) := by
  haveI : CharP K 2 := CFSG.ComponentClassification.RankTwoClassical.charP_two_of_card hK
  refine geomBody_of_field (by rcases ht with rfl | rfl <;> simp) fun hS hna f hf hord => ?_
  have hn : 1 ≤ n := one_le_of_card_field hK
  have h := FieldFixSp.exists_fixGeom hl hn hp hp2 hK hS hna hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨t, l, n / p⟩ := by
    refine ⟨one_le_of_card_field hK₀, ?_⟩
    rcases ht with rfl | rfl <;> dsimp only <;> exact ⟨by omega, fun h => by omega⟩
  have hraw : CFSG.Assembly.LargeEvenRawDatum ⟨t, l, n / p⟩ = LargeEvenRecipeSymplectic l (2 ^ (n / p)) false := by
    rcases ht with rfl | rfl <;> rfl
  refine fixAlt_of_raw hlab₀ ?_
  rw [hraw]
  exact FieldFixSp.exists_fixGeom hl hn hp hp2 hK hS hna hf hord

theorem cAll_geomBody_BC (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    {l n : ℕ} (hl : 3 ≤ l) : MI.CAll ⟨t, l, n⟩ (GeomBody p ⟨t, l, n⟩) := by
  haveI : NeZero l := ⟨by omega⟩
  intro Q hQ
  have hraw : ∀ Q', CFSG.Assembly.LargeEvenRawDatum ⟨t, l, n⟩ Q' =
      LargeEvenRecipeSymplectic l (2 ^ n) false Q' := by
    intro Q'
    rcases ht with rfl | rfl <;> rfl
  rw [hraw] at hQ ⊢
  exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => geomBody_sp hp hp2 ht hl K hK) hQ

theorem geomBody_of_fieldDeg {lab : LargeEvenLabel} (ht : lab.tag ≠ .triD4) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (h : IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ f ∈ F, orderOf f = p → p ∣ FP.fieldDeg lab →
      FixAlt p I f) : FP.FieldDegDvd lab R I F → GeomBody p lab R I F :=
  fun hdeg => geomBody_of_field ht fun hs hna f hf hord => h hs hna f hf hord (hord ▸ hdeg f hf)

theorem cAll_of_fieldDeg {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {P : LargeEvenRawCont}
    (h : MI.CAll lab fun R _ I F => FP.FieldDegDvd lab R I F → P R I F) : MI.CAll lab P :=
  MI.CAll.mono (fun _ _ _ _ hh => hh.2 hh.1) (MI.CAll.and (FP.canonFieldDeg hlab) h)

theorem cAll_geomBody_D (hp : p.Prime) (hp2 : p ≠ 2) {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) : MI.CAll ⟨.D, l, n⟩ (GeomBody p ⟨.D, l, n⟩) := by
  have hlab : LargeEvenInLambda2 ⟨.D, l, n⟩ := ⟨hn, show 3 ≤ l by omega⟩
  refine cAll_of_fieldDeg hlab ?_
  refine (MI.canonAll_iff_legacyAll hlab (by simp [MI.DerivedLab]) _).2 ?_
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl hl fun K _ _ _ hK => ?_
  refine geomBody_of_fieldDeg (by simp) fun hS hna f hf hord hpn => ?_
  have hpk : p ∣ 2 ^ (n / p) - 1 := dvd_two_pow_div_sub_one' hp hpn hpq
  have h := FieldFixOmegaPlus.exists_fixGeom hl hn hp hp2 hK hpk hS hna hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.D, l, n / p⟩ := ⟨one_le_of_card_field hK₀, show 3 ≤ l by omega⟩
  refine fixAlt_of_raw hlab₀ ?_
  have h3 : l ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact FieldFixOmegaPlus.exists_fixGeom hl hn hp hp2 hK hpk hS hna hf hord

theorem cAll_geomBody_twD (hp : p.Prime) (hp2 : p ≠ 2) {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) :
    MI.CAll ⟨.twD, l, n⟩ (GeomBody p ⟨.twD, l, n⟩) := by
  have hlab : LargeEvenInLambda2 ⟨.twD, l, n⟩ := ⟨hn, show 2 ≤ l by omega⟩
  refine (MI.canonAll_iff_legacyAll hlab (by simp [MI.DerivedLab]) _).2 ?_
  refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl hl fun K _ _ _ hK b c hirr => ?_
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have h := FieldFixTwOmega.exists_fixGeom hl hn hp hp2 hK hirr hS hna hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.twD, l, n / p⟩ := ⟨one_le_of_card_field hK₀, show 2 ≤ l by omega⟩
  refine fixAlt_of_raw hlab₀ ?_
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  simp only [h2, h3, ↓reduceIte]
  exact FieldFixTwOmega.exists_fixGeom hl hn hp hp2 hK hirr hS hna hf hord

theorem cAll_geomBody_derived (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    MI.CAll lab (GeomBody p lab) := by
  have ht : lab.tag ≠ .triD4 := by rcases hd with h | h | h <;> rw [h] <;> simp
  have hn1 : lab.n = 1 := by
    obtain ⟨t, l, n⟩ := lab
    rcases hd with h | h | h <;> dsimp only at h <;> subst h <;> exact hlab.2.2
  have hdeg : FP.fieldDeg lab = 1 := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at hn1
    rcases hd with h | h | h <;> dsimp only at h <;> subst h <;> simp [FP.fieldDeg, hn1]
  have key : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), FP.FieldDegDvd lab R I F →
      GeomBody p lab R I F := by
    intro R _ I F
    refine geomBody_of_fieldDeg ht fun _ _ f _ hord hpn => ?_
    rw [hdeg] at hpn
    exact absurd (Nat.le_of_dvd one_pos hpn) (by have := hp.two_le; omega)
  exact cAll_of_fieldDeg hlab fun Q hQ =>
    Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, key R I F⟩) hQ

end Families

section Exceptional


variable {p : ℕ}

theorem cAll_geomBody_chev (hp : p.Prime) (hp2 : p ≠ 2) {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {t : LargeEvenLieTag}
    (ht : (t = .F4 ∧ τ = .F4) ∨ (t = .E7 ∧ τ = .E7) ∨ (t = .E8 ∧ τ = .E8)) {n : ℕ} (hn : 1 ≤ n) :
    MI.CAll ⟨t, 0, n⟩ (GeomBody p ⟨t, 0, n⟩) := by
  have hraw : ∀ (k : ℕ) (Q : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨t, 0, k⟩ Q =
      LargeEvenRecipeChevalley τ.cartan (2 ^ k) false Q := by
    intro k Q
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have httr : t ≠ .triD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  intro Q hQ
  rw [hraw] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simpa using httr) fun _ _ f hf hord => ?_
  have h := chev_fixStd hτ hn hK hp.pos hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨t, 0, n / p⟩ := by
    refine ⟨one_le_of_card_field hK₀, ?_⟩
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  refine fixAlt_of_raw hlab₀ ?_
  rw [hraw]
  exact chev_fixStd hτ hn hK hp.pos hf hord

theorem cAll_geomBody_E6 (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ} (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) : MI.CAll ⟨.E6, 0, n⟩ (GeomBody p ⟨.E6, 0, n⟩) := by
  have hraw : ∀ (k : ℕ) (Q : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨.E6, 0, k⟩ Q =
      LargeEvenRecipeChevalley CFSG.Blueprint.Chevalley.Tag.E6.cartan (2 ^ k) false Q :=
    fun _ _ => rfl
  intro Q hQ
  rw [hraw] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simp) fun _ _ f hf hord => ?_
  have h := e6_fixStd hn hK hp hp2 hp3 hpq hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hlab₀ : LargeEvenInLambda2 ⟨.E6, 0, n / p⟩ := ⟨one_le_of_card_field hK₀, rfl⟩
  refine fixAlt_of_raw hlab₀ ?_
  rw [hraw]
  exact e6_fixStd hn hK hp hp2 hp3 hpq hf hord

theorem t156Geom_of_rest (h : T156Rest) : T156Geom := by
  intro p hp hp2 lab hlab
  by_cases hr : RestLabel p lab
  · exact h p hp hp2 lab hlab hr
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  unfold RestLabel at hr
  dsimp only at hr
  push Not at hr
  obtain ⟨htwA, hA1, hBC2, hD, htwD, hG2, hTD4, hB2, hF4, hE6, htwE6⟩ := hr
  cases t
  case A =>
    have hl : 1 ≤ l := hlab.2.1
    have hl1 : l ≠ 1 := hA1 rfl
    exact cAll_geomBody_A hp hp2 (by omega)
  case twA => exact absurd rfl htwA
  case B =>
    have hl : 2 ≤ l := hlab.2.1
    have hl2 : l ≠ 2 := hBC2 (Or.inl rfl)
    exact cAll_geomBody_BC hp hp2 (Or.inl rfl) (by omega)
  case C =>
    have hl : 2 ≤ l := hlab.2.1
    have hl2 : l ≠ 2 := hBC2 (Or.inr rfl)
    exact cAll_geomBody_BC hp hp2 (Or.inr rfl) (by omega)
  case B2der => exact cAll_geomBody_derived hp hlab (Or.inl rfl)
  case D =>
    have hl : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · obtain rfl : l = 3 := by omega
      exact cAll_geomBody_D3 hp hp2
    · exact cAll_geomBody_D hp hp2 h4 hn (hD rfl h4)
  case twD =>
    have hl : 4 ≤ l := htwD rfl
    exact cAll_geomBody_twD hp hp2 hl hn
  case G2 => exact absurd rfl hG2
  case G2der => exact cAll_geomBody_derived hp hlab (Or.inr (Or.inl rfl))
  case F4 =>
    obtain rfl : l = 0 := hlab.2
    exact cAll_geomBody_chev hp hp2 (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) hn
  case E6 =>
    obtain rfl : l = 0 := hlab.2
    obtain ⟨hp3, hpq⟩ := hE6 rfl
    exact cAll_geomBody_E6 hp hp2 hp3 hn hpq
  case E7 =>
    obtain rfl : l = 0 := hlab.2
    exact cAll_geomBody_chev hp hp2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hn
  case E8 =>
    obtain rfl : l = 0 := hlab.2
    exact cAll_geomBody_chev hp hp2 (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, rfl⟩)) hn
  case twE6 => exact absurd rfl htwE6
  case triD4 => exact absurd rfl hTD4
  case twB2 => exact absurd rfl hB2
  case twF4 => exact absurd rfl hF4
  case twF4der => exact cAll_geomBody_derived hp hlab (Or.inr (Or.inr rfl))

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA.T156

end
