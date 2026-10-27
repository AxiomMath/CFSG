module

public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.GH74.GLS.SP.Identify
public import CFSG.Timmesfeld.RankTwo.Presentation

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.Stage4.Hex

section Match

variable {n : ℕ} {Y : Type} [Group Y] (M : RankTwoSystem Y n)

@[expose] def UMatch {G : Type} [Group G] (D : RankTwoSystem G n) : Prop :=
  ∃ φ : D.U ≃* M.U, ∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U,
    (x : G) ∈ D.root i ↔ ((φ x : M.U) : Y) ∈ M.root i

@[expose] def RankTwoMatch (G : Type) [Group G] : Prop :=
  ∃ D : RankTwoSystem G n, UMatch M D

@[expose] def GlueMatch (G : Type) [Group G] : Prop :=
  ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
    (R : RGD2 n H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧
    ∃ φ : U ≃* M.U, ∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : U,
      (x : G) ∈ root i ↔ ((φ x : M.U) : Y) ∈ M.root i

variable {M}

theorem nonempty_mulEquiv_of_rankTwoMatch {G : Type} [Group G] [IsSimpleGroup G] [IsSimpleGroup Y]
    (h : RankTwoMatch M G) : Nonempty (G ≃* Y) := by
  obtain ⟨D, φ, hφ⟩ := h
  exact nonempty_mulEquiv_of_rankTwo D M φ (fun i h1 hn x => hφ i h1 (by exact_mod_cast hn) x)

theorem rankTwoMatch_of_uMatch {G : Type} [Group G] {D : RankTwoSystem G n} (h : UMatch M D) :
    RankTwoMatch M G :=
  ⟨D, h⟩

theorem rankTwoMatch_of_glueMatch {G : Type} [Group G] [IsSimpleGroup G] (h : GlueMatch M G) :
    RankTwoMatch M G := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  exact ⟨(R.toPre hgen).toSystemOfSimple, φ, hφ⟩

theorem nonempty_mulEquiv_of_glueMatch {G : Type} [Group G] [IsSimpleGroup G] [IsSimpleGroup Y]
    (h : GlueMatch M G) : Nonempty (G ≃* Y) :=
  nonempty_mulEquiv_of_rankTwoMatch (rankTwoMatch_of_glueMatch h)

theorem GlueMatch.of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : GlueMatch M G') : GlueMatch M G := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  have hker : (e.symm : G' →* G).ker ≤ H := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact bot_le
  have hU : U ⊓ (e.symm : G' →* G).ker = ⊥ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact inf_bot_eq U
  refine ⟨H.map (e.symm : G' →* G), (e.symm : G' →* G) r₁, (e.symm : G' →* G) r₂,
    U.map (e.symm : G' →* G), fun i => (root i).map (e.symm : G' →* G),
    R.map (e.symm : G' →* G) hker hU,
    R.map_gen (e.symm : G' →* G) e.symm.surjective hker hU hgen,
    (MulEquiv.subgroupMap e.symm U).symm.trans φ, ?_⟩
  intro i h1 hn x
  have hyx : (((MulEquiv.subgroupMap e.symm U).symm x : U) : G') = e (x : G) := by
    simp [MulEquiv.subgroupMap_symm_apply]
  have key := hφ i h1 hn ((MulEquiv.subgroupMap e.symm U).symm x)
  rw [hyx] at key
  have hx : (x : G) ∈ (root i).map (e.symm : G' →* G) ↔ e (x : G) ∈ root i := by
    have := Subgroup.mem_map_equiv (f := e.symm) (K := root i) (x := (x : G))
    simpa using this
  rw [hx]
  exact key

theorem rankTwoMatch_self : RankTwoMatch M Y :=
  ⟨M, MulEquiv.refl _, fun _ _ _ _ => Iff.rfl⟩

end Match

section G2

variable (F : Type) [Field F]

@[expose] def G2RankTwoData
    (G : Type) [Group G] (hF : 3 ≤ Nat.card F) : Prop :=
  RankTwoMatch (g2ModelSystem F hF) G

@[expose] def G2GlueData
    (G : Type) [Group G] (hF : 3 ≤ Nat.card F) : Prop :=
  GlueMatch (g2ModelSystem F hF) G

variable {F}

theorem g2_of_rankTwoData
    {G : Type} [Group G] [IsSimpleGroup G] {hF : 3 ≤ Nat.card F}
    (h : G2RankTwoData F G hF) : Nonempty (G ≃* AdjointQuotient .G2 F) :=
  haveI := isSimpleGroup_g2Model hF
  nonempty_mulEquiv_of_rankTwoMatch h

theorem g2RankTwoData_model
    (hF : 3 ≤ Nat.card F) : G2RankTwoData F (AdjointQuotient .G2 F) hF :=
  rankTwoMatch_self

theorem lieModel_g2_of_rankTwoData
    [Finite F] {G : Type} [Group G] [IsSimpleGroup G] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hq : 3 ≤ p ^ f) (hcard : Nat.card F = p ^ f)
    (h : G2RankTwoData F G (hcard ▸ hq)) : LieModel G .G2 0 p f := by
  obtain ⟨e⟩ := g2_of_rankTwoData h
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm
    (CFSG.Timmesfeld.lieModel_G2_quotient hp hf hq hcard)

theorem g2RankTwoData_of_glueData
    {G : Type} [Group G] [IsSimpleGroup G] {hF : 3 ≤ Nat.card F}
    (h : G2GlueData F G hF) : G2RankTwoData F G hF :=
  rankTwoMatch_of_glueMatch h

theorem g2_of_glueData
    {G : Type} [Group G] [IsSimpleGroup G] {hF : 3 ≤ Nat.card F}
    (h : G2GlueData F G hF) : Nonempty (G ≃* AdjointQuotient .G2 F) :=
  g2_of_rankTwoData (g2RankTwoData_of_glueData h)

theorem g2GlueData_model
    (hF : 3 ≤ Nat.card F) : G2GlueData F (AdjointQuotient .G2 F) hF := by
  have := isSimpleGroup_g2Model hF
  refine ⟨_, _, _, _, _, hexQuotRGD2 (g2Data F), hexQuotRGD2_gen (g2Data F),
    MulEquiv.subgroupCongr (g2ModelSystem_U hF).symm, ?_⟩
  intro i _ _ x
  rw [g2ModelSystem_root hF i]
  rfl

theorem g2GlueData_iff
    {G : Type} [Group G] [IsSimpleGroup G] (hF : 3 ≤ Nat.card F) :
    G2GlueData F G hF ↔ Nonempty (G ≃* AdjointQuotient .G2 F) :=
  ⟨fun h => g2_of_glueData h, fun ⟨e⟩ => GlueMatch.of_equiv e (g2GlueData_model hF)⟩

end G2

section D4

variable {K : Type} [Field K] [Finite K] (σ : K →+* K) {q : ℕ} (hq : 2 ≤ q)
  (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)

@[expose] def D4RankTwoData
    (G : Type) [Group G] : Prop :=
  RankTwoMatch (d4ModelSystem σ hq hK hσq) G

@[expose] def D4GlueData
    (G : Type) [Group G] : Prop :=
  GlueMatch (d4ModelSystem σ hq hK hσq) G

variable {σ hq hK hσq}

theorem d4_of_rankTwoData
    {G : Type} [Group G] [IsSimpleGroup G]
    (h : D4RankTwoData σ hq hK hσq G) :
    Nonempty (G ≃* twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) :=
  haveI := isSimpleGroup_d4Model σ hq hK hσq
  nonempty_mulEquiv_of_rankTwoMatch h

theorem d4RankTwoData_model :
    D4RankTwoData σ hq hK hσq (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) :=
  rankTwoMatch_self

theorem lieModel_d4_of_rankTwoData
    {G : Type} [Group G] [IsSimpleGroup G] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hqpf : q = p ^ f) (h : D4RankTwoData σ hq hK hσq G) :
    LieModel G .trialityD4 0 p f := by
  obtain ⟨e⟩ := d4_of_rankTwoData h
  subst hqpf
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm
    (CFSG.Timmesfeld.lieModel_twistedD4_quotient hp hf hK σ hσq)

theorem d4RankTwoData_of_glueData
    {G : Type} [Group G] [IsSimpleGroup G]
    (h : D4GlueData σ hq hK hσq G) : D4RankTwoData σ hq hK hσq G :=
  rankTwoMatch_of_glueMatch h

theorem d4_of_glueData
    {G : Type} [Group G] [IsSimpleGroup G] (h : D4GlueData σ hq hK hσq G) :
    Nonempty (G ≃* twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) :=
  d4_of_rankTwoData (d4RankTwoData_of_glueData h)

variable (σ hq hK hσq)

theorem d4GlueData_model :
    D4GlueData σ hq hK hσq (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) := by
  have := isSimpleGroup_d4Model σ hq hK hσq
  refine ⟨_, _, _, _, _, hexQuotRGD2 (twistedData σ (sigma_three_of_card hK hσq)),
    hexQuotRGD2_gen (twistedData σ (sigma_three_of_card hK hσq)),
    MulEquiv.subgroupCongr (d4ModelSystem_U σ hq hK hσq).symm, ?_⟩
  intro i _ _ x
  rw [d4ModelSystem_root σ hq hK hσq i]
  rfl

theorem d4GlueData_iff
    {G : Type} [Group G] [IsSimpleGroup G] :
    D4GlueData σ hq hK hσq G ↔
      Nonempty (G ≃* twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) :=
  ⟨fun h => d4_of_glueData h, fun ⟨e⟩ => GlueMatch.of_equiv e (d4GlueData_model σ hq hK hσq)⟩

end D4

end CFSG.GH74.GLS.Stage4.Hex
