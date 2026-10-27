module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Phi

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {n : ℕ} {K₁ K₂ V V' : Subgroup G} {s : G}

namespace L257

omit [Finite G] in
theorem conjugate_commutator' (A B : Subgroup G) (g : G) :
    CFSG.conjugate ⁅A, B⁆ g = ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ := by
  unfold CFSG.conjugate
  exact Subgroup.map_commutator _ _ _

omit [Finite G] in
theorem conjugate_iSup_le (P : Subgroup G → Prop) {Y : Subgroup G} (g : G)
    (h : ∀ E, P E → CFSG.conjugate E g ≤ Y) :
    CFSG.conjugate (⨆ (E : Subgroup G) (_ : P E), E) g ≤ Y := by
  unfold CFSG.conjugate
  rw [Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hE => h E hE

omit [Finite G] in
theorem comm_prod {w₁ w₂ r₁ r₂ : G} (hww : w₁ * w₂ = w₂ * w₁) (h12 : w₁ * r₂ = r₂ * w₁)
    (h21 : w₂ * r₁ = r₁ * w₂) :
    (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹ * (w₁ * r₁) * (w₂ * r₂) = (r₂ * r₁)⁻¹ * (r₁ * r₂) := by
  have e1 : (w₁ * r₁) * (w₂ * r₂) = (w₁ * w₂) * (r₁ * r₂) := by
    calc (w₁ * r₁) * (w₂ * r₂) = w₁ * (r₁ * w₂) * r₂ := by group
      _ = w₁ * (w₂ * r₁) * r₂ := by rw [h21]
      _ = (w₁ * w₂) * (r₁ * r₂) := by group
  have e2 : (w₂ * r₂) * (w₁ * r₁) = (w₁ * w₂) * (r₂ * r₁) := by
    calc (w₂ * r₂) * (w₁ * r₁) = w₂ * (r₂ * w₁) * r₁ := by group
      _ = w₂ * (w₁ * r₂) * r₁ := by rw [h12]
      _ = (w₂ * w₁) * (r₂ * r₁) := by group
      _ = (w₁ * w₂) * (r₂ * r₁) := by rw [hww]
  calc (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹ * (w₁ * r₁) * (w₂ * r₂)
      = ((w₂ * r₂) * (w₁ * r₁))⁻¹ * ((w₁ * r₁) * (w₂ * r₂)) := by group
    _ = ((w₁ * w₂) * (r₂ * r₁))⁻¹ * ((w₁ * w₂) * (r₁ * r₂)) := by rw [e1, e2]
    _ = (r₂ * r₁)⁻¹ * (r₁ * r₂) := by group

omit [Finite G] in
theorem isElemAbelian_of_le_sup {W R Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hWR : ∀ w ∈ W, ∀ r ∈ R, w * r = r * w) (hY : Y ≤ W ⊔ R) (hYR : Y ⊓ R = ⊥) :
    IsElemAbelian 2 Y := by
  have hcomm : ∀ a b : Y, (a : G) * b = b * a := by
    intro a b
    obtain ⟨w₁, hw₁, r₁, hr₁, h₁⟩ := mem_sup_of_commute hWR (hY a.2)
    obtain ⟨w₂, hw₂, r₂, hr₂, h₂⟩ := mem_sup_of_commute hWR (hY b.2)
    have hcm : (a : G)⁻¹ * (b : G)⁻¹ * (a : G) * (b : G) ∈ Y ⊓ R := by
      refine ⟨Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem a.2) (Y.inv_mem b.2)) a.2) b.2, ?_⟩
      rw [← h₁, ← h₂, comm_prod (B2F.isElemAbelian_comm hW hw₁ hw₂) (hWR _ hw₁ _ hr₂)
        (hWR _ hw₂ _ hr₁)]
      exact R.mul_mem (R.inv_mem (R.mul_mem hr₂ hr₁)) (R.mul_mem hr₁ hr₂)
    rw [hYR, Subgroup.mem_bot] at hcm
    have h3 : (a : G) * b = b * a := by
      have := congrArg (fun t => (b : G) * (a : G) * t) hcm
      simp only [mul_one] at this
      calc (a : G) * b = (b * a) * ((a : G)⁻¹ * (b : G)⁻¹ * a * b) := by group
        _ = b * a := by rw [hcm, mul_one]
    exact h3
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun y hy => ?_⟩
  obtain ⟨w, hw, r, hr, rfl⟩ := mem_sup_of_commute hWR (hY hy)
  have hsq : (w * r) ^ 2 = r ^ 2 := by
    have h1 : w * r = r * w := hWR w hw r hr
    have hw2 : w ^ 2 = 1 := hW.2 w hw
    calc (w * r) ^ 2 = w * r * (w * r) := pow_two _
      _ = w * (r * w) * r := by simp only [mul_assoc]
      _ = w * (w * r) * r := by rw [← h1]
      _ = (w * w) * (r * r) := by simp only [mul_assoc]
      _ = w ^ 2 * r ^ 2 := by rw [pow_two, pow_two]
      _ = r ^ 2 := by rw [hw2, one_mul]
  have hmem : (w * r) ^ 2 ∈ Y ⊓ R := by
    refine ⟨Y.pow_mem hy 2, ?_⟩
    rw [hsq]
    exact R.pow_mem hr 2
  rw [hYR, Subgroup.mem_bot] at hmem
  exact hmem

omit [Finite G] in
theorem conjugate_pCoreOf (g : G) (X : Subgroup G) :
    CFSG.conjugate (pCoreOf 2 X) g = pCoreOf 2 (CFSG.conjugate X g) := by
  unfold CFSG.conjugate
  exact (pCoreOf_map_equiv 2 (MulAut.conj g⁻¹) X).symm

end L257

namespace Conf257

variable (c : Conf257 N n K₁ K₂ V V' s)

include c in
theorem exists_not_conjugate_le (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥)
    {W : Subgroup G} (hW : W = V ∨ W = V') :
    ∃ E : Subgroup G, IsMaxElemAbelian N.SC E ∧
      ¬ CFSG.conjugate E N.x ≤ W ⊔ thompsonJ N.SC := by
  by_contra hno
  push Not at hno
  have hle : CFSG.conjugate (thompsonJ N.SC) N.x ≤ W ⊔ thompsonJ N.SC :=
    L257.conjugate_iSup_le (fun E => IsMaxElemAbelian N.SC E) N.x hno
  have hYR : CFSG.conjugate (thompsonJ N.SC) N.x ⊓ thompsonJ N.SC = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← hint]
    exact le_inf (inf_le_right.trans (thompsonJ_le_self _))
      (inf_le_left.trans (BenderBranch.conjugate_mono (thompsonJ_le_self _) _))
  have hY : IsElemAbelian 2 (CFSG.conjugate (thompsonJ N.SC) N.x) :=
    L257.isElemAbelian_of_le_sup (c.rad_elem hW)
      (fun w hw r hr => c.rad_comm hW hw (c.SC_le_centralizer (thompsonJ_le_self _ hr))) hle hYR
  have hback : thompsonJ N.SC =
      CFSG.conjugate (CFSG.conjugate (thompsonJ N.SC) N.x) N.x⁻¹ := by
    rw [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
  apply c.not_isElemAbelian_thompsonJ_SC
  rw [hback, L257.conjugate_eq_cjSub]
  exact isElemAbelian_cjSub hY

include c in
theorem conjugate_rad_le {W₁ W₂ E U : Subgroup G} (hW : (W₁ = V ∧ W₂ = V') ∨ (W₁ = V' ∧ W₂ = V))
    (hE : IsMaxElemAbelian N.SC E) (hnot : ¬ CFSG.conjugate E N.x ≤ W₁ ⊔ thompsonJ N.SC)
    (hU : U = V ∨ U = V') : CFSG.conjugate U N.x ≤ W₂ ⊔ thompsonJ N.SC := by
  have hxS : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  have hA := L257.isMaxElemAbelian_conjugate hxS (c.isMaxElemAbelian_of_exists hU hE)
  obtain ⟨E', hE', hcase⟩ := c.exists_of_isMaxElemAbelian hA
  have hE'le : E' ≤ thompsonJ N.SC := le_iSup₂_of_le E' hE' le_rfl
  have hsub : CFSG.conjugate E N.x ≤ CFSG.conjugate (U ⊔ E) N.x :=
    BenderBranch.conjugate_mono le_sup_right _
  have hsub' : CFSG.conjugate U N.x ≤ CFSG.conjugate (U ⊔ E) N.x :=
    BenderBranch.conjugate_mono le_sup_left _
  have hAle : CFSG.conjugate (U ⊔ E) N.x ≤ V ⊔ thompsonJ N.SC ∨
      CFSG.conjugate (U ⊔ E) N.x ≤ V' ⊔ thompsonJ N.SC := by
    rcases hcase with h | h
    · exact Or.inl (h ▸ sup_le_sup_left hE'le V)
    · exact Or.inr (h ▸ sup_le_sup_left hE'le V')
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hW
  · rcases hAle with h | h
    · exact absurd (hsub.trans h) hnot
    · exact hsub'.trans h
  · rcases hAle with h | h
    · exact hsub'.trans h
    · exact absurd (hsub.trans h) hnot

include c in
theorem sup_inf_sup_le :
    (V ⊔ thompsonJ N.SC) ⊓ (V' ⊔ thompsonJ N.SC) ≤ (V ⊓ V') ⊔ thompsonJ N.SC := by
  intro w hw
  obtain ⟨v, hv, r, hr, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => c.rad_comm (Or.inl rfl) ha (c.SC_le_centralizer (thompsonJ_le_self _ hb)))
    hw.1
  obtain ⟨v', hv', r', hr', h'⟩ := mem_sup_of_commute
    (fun a ha b hb => c.rad_comm (Or.inr rfl) ha (c.SC_le_centralizer (thompsonJ_le_self _ hb)))
    hw.2
  have h1 : v'⁻¹ * v = r' * r⁻¹ := by
    calc v'⁻¹ * v = v'⁻¹ * (v * r) * r⁻¹ := by group
      _ = v'⁻¹ * (v' * r') * r⁻¹ := by rw [h']
      _ = r' * r⁻¹ := by group
  have hZ : v'⁻¹ * v ∈ centerOf N.K := by
    refine ⟨N.K.mul_mem (N.K.inv_mem (c.V'_le_K hv')) (c.V_le_K hv), ?_⟩
    rw [h1]
    exact Subgroup.mul_mem _ (c.SC_le_centralizer (thompsonJ_le_self _ hr'))
      (Subgroup.inv_mem _ (c.SC_le_centralizer (thompsonJ_le_self _ hr)))
  have hvV' : v ∈ V' := by
    have := V'.mul_mem hv' (c.center_le_V' hZ)
    simpa using this
  exact Subgroup.mul_mem_sup ⟨hv, hvV'⟩ hr

include c in
theorem conjugate_rad_le_inf (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥) {U : Subgroup G}
    (hU : U = V ∨ U = V') :
    CFSG.conjugate U N.x ≤ (V ⊓ V') ⊔ thompsonJ N.SC := by
  obtain ⟨E₁, hE₁, hn₁⟩ := c.exists_not_conjugate_le hint (Or.inr rfl)
  obtain ⟨E₂, hE₂, hn₂⟩ := c.exists_not_conjugate_le hint (Or.inl rfl)
  have h1 := c.conjugate_rad_le (Or.inr ⟨rfl, rfl⟩) hE₁ hn₁ hU
  have h2 := c.conjugate_rad_le (Or.inl ⟨rfl, rfl⟩) hE₂ hn₂ hU
  exact (le_inf h1 h2).trans c.sup_inf_sup_le

include c in
theorem conjugate_commutator_le (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥) :
    CFSG.conjugate ⁅V, V'⁆ N.x ≤ thompsonJ N.SC := by
  rw [L257.conjugate_commutator']
  refine (Subgroup.commutator_mono (c.conjugate_rad_le_inf hint (Or.inl rfl))
    (c.conjugate_rad_le_inf hint (Or.inr rfl))).trans ?_
  have hD : ∀ a ∈ V ⊓ V', ∀ r ∈ thompsonJ N.SC, a * r = r * a := fun a ha r hr =>
    c.rad_comm (Or.inl rfl) ha.1 (c.SC_le_centralizer (thompsonJ_le_self _ hr))
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  obtain ⟨a, ha, r, hr, hgr⟩ := mem_sup_of_commute hD ((V ⊓ V' ⊔ thompsonJ N.SC).inv_mem hg)
  obtain ⟨a', ha', r', hr', hhr⟩ := mem_sup_of_commute hD ((V ⊓ V' ⊔ thompsonJ N.SC).inv_mem hh)
  have key := L257.comm_prod (B2F.isElemAbelian_comm c.geom.V_elem ha.1 ha'.1) (hD a ha r' hr')
    (hD a' ha' r hr)
  rw [hgr, hhr] at key
  simp only [inv_inv] at key
  rw [commutatorElement_def, key]
  exact (thompsonJ N.SC).mul_mem ((thompsonJ N.SC).inv_mem ((thompsonJ N.SC).mul_mem hr' hr))
    ((thompsonJ N.SC).mul_mem hr hr')

include c in
theorem conjugate_K_cases {g : G} (hg : g ∈ N.S) {X : Subgroup G} (hX : X = K₁ ∨ X = K₂) :
    CFSG.conjugate X g = K₁ ∨ CFSG.conjugate X g = K₂ := by
  have hgK : g ∈ Subgroup.normalizer (N.K : Set G) := c.S_le_normalizer_K hg
  have hgM : g ∈ M := L257.S_le_M N hg
  have hKg : CFSG.conjugate N.K g = N.K := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgK
  have hB : CFSG.conjugate (N.K ⊓ Subgroup.normalizer (N.SK : Set G)) g =
      N.K ⊓ Subgroup.normalizer (N.SK : Set G) := by
    rw [← c.setup.borel, BenderBranch.conjugate_inf, hKg]
    have hM : CFSG.conjugate M g = M :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hgM)
    rw [hM]
  have hlt₁ : N.K ⊓ Subgroup.normalizer (N.SK : Set G) < X := by
    rcases hX with h | h
    · exact h ▸ c.setup.pair.lt₁
    · exact h ▸ c.setup.pair.lt₂
  have hlt₂ : X < N.K := by
    rcases hX with h | h
    · exact h ▸ c.setup.pair.lt_K₁
    · exact h ▸ c.setup.pair.lt_K₂
  have h1 : CFSG.conjugate (N.K ⊓ Subgroup.normalizer (N.SK : Set G)) g < CFSG.conjugate X g :=
    lt_of_le_of_ne (BenderBranch.conjugate_mono hlt₁.le g)
      (fun e => hlt₁.ne (BenderBranch.conjugate_inj.mp e))
  rw [hB] at h1
  have h2 : CFSG.conjugate X g < N.K := by
    have h3 : CFSG.conjugate X g < CFSG.conjugate N.K g :=
      lt_of_le_of_ne (BenderBranch.conjugate_mono hlt₂.le g)
        (fun e => hlt₂.ne (BenderBranch.conjugate_inj.mp e))
    rwa [hKg] at h3
  exact c.setup.pair.only _ h1 h2

include c in
theorem conjugate_rad_cases {g : G} (hg : g ∈ N.S) {W : Subgroup G} (hW : W = V ∨ W = V') :
    CFSG.conjugate W g = V ∨ CFSG.conjugate W g = V' := by
  rcases hW with hW | hW
  · rw [hW]
    rcases c.conjugate_K_cases hg (Or.inl rfl) with h | h
    · left
      rw [c.setup.hV, L257.conjugate_pCoreOf, h]
    · right
      rw [c.setup.hV, c.setup.hV', L257.conjugate_pCoreOf, h]
  · rw [hW]
    rcases c.conjugate_K_cases hg (Or.inr rfl) with h | h
    · left
      rw [c.setup.hV, c.setup.hV', L257.conjugate_pCoreOf, h]
    · right
      rw [c.setup.hV', L257.conjugate_pCoreOf, h]

include c in
theorem S_le_normalizer_conjugate_D :
    N.S ≤ Subgroup.normalizer (CFSG.conjugate ⁅V, V'⁆ N.x : Set G) := by
  intro g hg
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  have hg'S : N.x * g * N.x⁻¹ ∈ N.S := L257.x_conj_S N hg
  have hxg : N.x * g = (N.x * g * N.x⁻¹) * N.x := by simp [mul_assoc]
  have hDg' : CFSG.conjugate ⁅V, V'⁆ (N.x * g * N.x⁻¹) = ⁅V, V'⁆ := by
    rw [L257.conjugate_commutator']
    have h1 := c.conjugate_rad_cases hg'S (Or.inl rfl)
    have h2 := c.conjugate_rad_cases hg'S (Or.inr rfl)
    have hne : CFSG.conjugate V (N.x * g * N.x⁻¹) ≠ CFSG.conjugate V' (N.x * g * N.x⁻¹) :=
      fun e => c.geom.V_ne (BenderBranch.conjugate_inj.mp e)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Subgroup.commutator_comm]
    · exact absurd (h1.trans h2.symm) hne
  rw [BenderBranch.conjugate_conjugate, hxg, ← BenderBranch.conjugate_conjugate, hDg']

include c in
theorem conjugate_commutator_ne_bot : CFSG.conjugate ⁅V, V'⁆ N.x ≠ ⊥ := by
  intro h
  have hD : ⁅V, V'⁆ ≠ ⊥ := by
    intro h0
    apply c.geom.noncomm
    rw [Subgroup.commutator_comm] at h0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
  apply hD
  apply Subgroup.eq_bot_of_card_eq
  have := BenderBranch.card_conjugate ⁅V, V'⁆ N.x
  rw [h, Subgroup.card_bot] at this
  exact this.symm

include c in
theorem exists_E (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥) :
    ∃ E : Subgroup G, E = CFSG.conjugate ⁅V, V'⁆ N.x ∧ E ≠ ⊥ ∧ E ≤ thompsonJ N.SC ∧
      E ≤ N.SC ∧ N.S ≤ Subgroup.normalizer (E : Set G) :=
  ⟨_, rfl, c.conjugate_commutator_ne_bot, c.conjugate_commutator_le hint,
    (c.conjugate_commutator_le hint).trans (thompsonJ_le_self _),
    c.S_le_normalizer_conjugate_D⟩

include c in
theorem S_le_normalizer_inf : N.S ≤ Subgroup.normalizer ((V ⊓ V' : Subgroup G) : Set G) := by
  intro g hg
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_inf]
  have hne : CFSG.conjugate V g ≠ CFSG.conjugate V' g := fun e =>
    c.geom.V_ne (BenderBranch.conjugate_inj.mp e)
  rcases c.conjugate_rad_cases hg (Or.inl rfl) with h1 | h1 <;>
    rcases c.conjugate_rad_cases hg (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2, inf_comm]
  · exact absurd (h1.trans h2.symm) hne

omit c in
theorem conjugate_inv_eq {Y : Subgroup G} (hY : N.S ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.conjugate Y N.x⁻¹ = CFSG.conjugate Y N.x := by
  have h2 : (N.x ^ 2)⁻¹ ∈ N.S := N.S.inv_mem N.x_sq
  have hY' : CFSG.conjugate Y (N.x ^ 2)⁻¹ = Y :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hY h2)
  have : N.x⁻¹ = (N.x ^ 2)⁻¹ * N.x := by group
  rw [this, ← BenderBranch.conjugate_conjugate, hY']

include c in
theorem SK_le_conjugate_sup (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥) :
    N.SK ≤ CFSG.conjugate (V ⊓ V') N.x ⊔ CFSG.conjugate (thompsonJ N.SC) N.x := by
  rw [c.geom.P_eq]
  have key : ∀ {U : Subgroup G}, (U = V ∨ U = V') →
      U ≤ CFSG.conjugate (V ⊓ V') N.x ⊔ CFSG.conjugate (thompsonJ N.SC) N.x := by
    intro U hU
    have h1 := BenderBranch.conjugate_mono (c.conjugate_rad_le_inf hint hU) N.x⁻¹
    have h2 : CFSG.conjugate (CFSG.conjugate U N.x) N.x⁻¹ = U := by
      rw [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
    rw [h2, L257.conjugate_sup', conjugate_inv_eq c.S_le_normalizer_inf,
      conjugate_inv_eq (S_le_normalizer_RC (N := N))] at h1
    exact h1
  exact sup_le (key (Or.inl rfl)) (key (Or.inr rfl))

include c in
theorem SK_inf_conjugate_le (hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥) :
    N.SK ⊓ CFSG.conjugate (V ⊓ V') N.x ≤ V ⊓ V' := by
  intro f hf
  have hfV : f ∈ CFSG.conjugate V N.x := BenderBranch.conjugate_mono inf_le_left N.x hf.2
  have hf2 := c.conjugate_rad_le_inf hint (Or.inl rfl) hfV
  obtain ⟨d, hd, r, hr, rfl⟩ := mem_sup_of_commute (A := V ⊓ V') (B := thompsonJ N.SC)
    (fun a ha b hb => c.rad_comm (Or.inl rfl) ha.1 (c.SC_le_centralizer (thompsonJ_le_self _ hb)))
    hf2
  have hrSK : r ∈ N.SK := by
    have := N.SK.mul_mem (N.SK.inv_mem (c.V_le_SK hd.1)) hf.1
    simpa using this
  have hrZ : r ∈ centerOf N.K := ⟨L257.SK_le_K N hrSK, c.SC_le_centralizer (thompsonJ_le_self _ hr)⟩
  exact (V ⊓ V').mul_mem hd ⟨c.center_le_V hrZ, c.center_le_V' hrZ⟩

end Conf257

end CFSG.QuasithinUnique
