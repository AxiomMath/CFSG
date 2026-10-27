module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2ModelDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

structure D4T2PlumbData (C Ĉ G : Type) [Group C] [Group Ĉ] [Group G] where
  cj : Ĉ →* MulAut C
  lf : Ĉ →* G
  ι : C →* G
  cj_inj : Function.Injective cj
  lf_inj : Function.Injective lf
  ι_inj : Function.Injective ι
  comp : ∀ (x : Ĉ) (y : C), ι (cj x y) = lf x * ι y * (lf x)⁻¹

namespace D4T2PlumbData

section OfBaseChange

variable {C Ĉ G : Type} [Group C] [Group Ĉ] [Group G]
  (cj : Ĉ →* MulAut C) (bc : Ĉ →* G) (bc' : C →* G) (ι : C →* G) (g0 : G)
  (hcj : Function.Injective cj) (hbc : Function.Injective bc) (hι' : Function.Injective ι)
  (hι : ∀ y, ι y = g0⁻¹ * bc' y * g0)
  (hcomp : ∀ (x : Ĉ) (y : C), bc' (cj x y) = bc x * bc' y * (bc x)⁻¹)

@[expose] def ofBaseChange : D4T2PlumbData C Ĉ G where
  cj := cj
  lf := (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  ι := ι
  cj_inj := hcj
  lf_inj := (MulAut.conj g0⁻¹).injective.comp hbc
  ι_inj := hι'
  comp := fun x y => by
    rw [hι, hι, hcomp]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem ofBaseChange_lf (x : Ĉ) :
    (ofBaseChange cj bc bc' ι g0 hcj hbc hι' hι hcomp).lf x = g0⁻¹ * bc x * g0 := by
  change (MulAut.conj g0⁻¹) (bc x) = _
  rw [MulAut.conj_apply, inv_inv]

end OfBaseChange

variable {C Ĉ G : Type} [Group C] [Group Ĉ] [Group G] (P : D4T2PlumbData C Ĉ G)

@[expose] def liftSub (F : Subgroup (MulAut C)) : Subgroup G :=
  (F.comap P.cj).map P.lf

theorem mem_liftSub {F : Subgroup (MulAut C)} {y : G} :
    y ∈ P.liftSub F ↔ ∃ x : Ĉ, P.cj x ∈ F ∧ P.lf x = y := by
  simp only [liftSub, Subgroup.mem_map, Subgroup.mem_comap]

theorem map_fixedPoints_eq {F : Subgroup (MulAut C)} (hF : F ≤ P.cj.range) :
    (fixedPoints F).map P.ι = P.ι.range ⊓ Subgroup.centralizer (P.liftSub F : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl⟩ := (P.mem_liftSub).1 hz
    have h1 := P.comp x c
    rw [mem_fixedPoints.1 hc _ hx] at h1
    calc P.lf x * P.ι c = (P.lf x * P.ι c * (P.lf x)⁻¹) * P.lf x := by group
      _ = P.ι c * P.lf x := by rw [← h1]
  · rintro ⟨⟨c, rfl⟩, hcomm⟩
    refine ⟨c, mem_fixedPoints.2 fun φ hφ => ?_, rfl⟩
    obtain ⟨x, rfl⟩ := hF hφ
    apply P.ι_inj
    rw [P.comp x c, hcomm (P.lf x) ((P.mem_liftSub).2 ⟨x, hφ, rfl⟩)]
    group

theorem relIndex_liftSub (F : Subgroup (MulAut C)) {E : Subgroup (MulAut C)}
    (hE : E ≤ P.cj.range) : (P.liftSub F).relIndex (P.liftSub E) = F.relIndex E := by
  unfold liftSub
  rw [Subgroup.relIndex_map_map_of_injective _ _ P.lf_inj, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self hE]

theorem card_liftSub {E : Subgroup (MulAut C)} (hE : E ≤ P.cj.range) :
    Nat.card (P.liftSub E) = Nat.card E := by
  unfold liftSub
  rw [Subgroup.card_map_of_injective P.lf_inj]
  conv_rhs => rw [← Subgroup.map_comap_eq_self hE]
  exact (Subgroup.card_map_of_injective P.cj_inj).symm

theorem isElemAbelian_liftSub {p : ℕ} {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) :
    IsElemAbelian p (P.liftSub E) :=
  (hE.comap P.cj_inj).map P.lf

theorem exists_liftSub_eq {E : Subgroup (MulAut C)} (hE : E ≤ P.cj.range) {F' : Subgroup G}
    (hF' : F' ≤ P.liftSub E) : ∃ F : Subgroup (MulAut C), F ≤ E ∧ P.liftSub F = F' := by
  refine ⟨(F'.comap P.lf ⊓ E.comap P.cj).map P.cj, ?_, ?_⟩
  · calc (F'.comap P.lf ⊓ E.comap P.cj).map P.cj ≤ (E.comap P.cj).map P.cj :=
          Subgroup.map_mono inf_le_right
      _ = E := Subgroup.map_comap_eq_self hE
  · unfold liftSub
    rw [Subgroup.comap_map_eq_self_of_injective P.cj_inj]
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hF' hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩

theorem inner_of_liftSub_le_range {E : Subgroup (MulAut C)} (hE : E ≤ P.cj.range)
    (h : P.liftSub E ≤ P.ι.range) : ∀ g ∈ E, g ∈ (MulAut.conj : C →* MulAut C).range := by
  intro g hg
  obtain ⟨x, rfl⟩ := hE hg
  obtain ⟨c, hc⟩ := h ((P.mem_liftSub).2 ⟨x, hg, rfl⟩)
  refine ⟨c, MulEquiv.ext fun y => P.ι_inj ?_⟩
  rw [P.comp x y, MulAut.conj_apply, map_mul, map_mul, map_inv, hc]

theorem exists_normalized_of_normalized {E : Subgroup (MulAut C)} (hE : E ≤ P.cj.range)
    {l : ℕ} {R : Subgroup G} (hRΓ : R ≤ P.ι.range) (hR1 : R ≠ ⊥) (hRp : IsPGroup l R)
    (hnorm : ∀ ε ∈ P.liftSub E, R.map (MulAut.conj ε).toMonoidHom = R) :
    ∃ R' : Subgroup C, R' ≠ ⊥ ∧ IsPGroup l R' ∧ ∀ g ∈ E, R'.map g.toMonoidHom = R' := by
  have hle : ∀ g ∈ E, (R.comap P.ι).map g.toMonoidHom ≤ R.comap P.ι := by
    intro g hg
    obtain ⟨x, rfl⟩ := hE hg
    rintro _ ⟨y, hy, rfl⟩
    have hε := hnorm (P.lf x) ((P.mem_liftSub).2 ⟨x, hg, rfl⟩)
    show P.ι (P.cj x y) ∈ R
    rw [P.comp x y]
    have : P.lf x * P.ι y * (P.lf x)⁻¹ ∈ R.map (MulAut.conj (P.lf x)).toMonoidHom :=
      ⟨P.ι y, hy, rfl⟩
    rwa [hε] at this
  refine ⟨R.comap P.ι, ?_, hRp.comap_of_injective P.ι P.ι_inj, fun g hg => ?_⟩
  · intro h
    apply hR1
    rw [← Subgroup.map_comap_eq_self hRΓ, h, Subgroup.map_bot]
  · refine le_antisymm (hle g hg) fun y hy => ?_
    exact ⟨(g⁻¹ : MulAut C) y, hle g⁻¹ (inv_mem hg) ⟨y, hy, rfl⟩, by simp⟩

end D4T2PlumbData

section Lang

set_option linter.unusedSectionVars false

open CFSG.RankThree.PartOne.KE


theorem d4t2pl_langSetup_conj_of_toral_datum {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L) (hDq : D.q = ℓ ^ f)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) {p : ℕ}
    (hfin : Finite D.model) {C : Type}
    [Group C] (ι₀ : C →* ModGL τ L) (hι₀ : Function.Injective ι₀)
    (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) (β : MulAut C) {u : ModGL τ L}
    (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      D.g0 * rootDiagUnit τ a * D.g0⁻¹ = u ∧ ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := by
  classical
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hyu'] at h
    have : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [this, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, fun c => ?_, ?_, hι⟩
  · exact ha ▸ hy
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hι, hβ c, ← ha, hyu']
    group
  · rw [← ha, hyu']
    group

theorem d4t2pl_langSetup_iota_of_inndiag_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∧
      (∃ (t : TwistTag) (ht : t.tag = .E6) (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
        (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 (AlgebraicClosure K) t ht * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 (AlgebraicClosure K) t ht)⁻¹) ∧
      (∀ c : ↥(twistedE6RootGroup K σ), ι c = S.D.g0⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) * S.D.g0) ∧
      (∀ x ∈ twistedE6InndiagGL K σ, S.D.g0⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) x :
          ModGL Tag.E6 (AlgebraicClosure K)) * S.D.g0 ∈ S.D.model) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, hh, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := huF.2
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL TwistTag.E6.tag K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι, hg0, hι⟩ :=
    d4t2pl_langSetup_conj_of_toral_datum hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  refine ⟨S, a, ι, hDq, hT, hap, h1, hinj, hrange, hconjι, hg0, ⟨TwistTag.E6, rfl,
    iterateFrobenius L ℓ f, fun c => ?_, fun g => ?_⟩, hι, fun x hx => ?_⟩
  · rw [hDq]
    exact hFr c
  · rw [hΦ]
    rfl
  · have key : S.D.g0⁻¹ * baseChangeGL ι₁ x * S.D.g0 ∈ S.D.model := by
      rw [model_eq_map_twistedFixedGroup S.D hΦ]
      refine ⟨baseChangeGL ι₁ x, ?_, ?_⟩
      · exact map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f)
          hFr ⟨x, hx, rfl⟩
      · change (MulAut.conj S.D.g0⁻¹) (baseChangeGL ι₁ x) = _
        rw [MulAut.conj_apply, inv_inv]
    exact key

structure TwE6LineLangIota (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (h : twistedE6InndiagGL K σ) extends TwE6LineLang K σ q h where
  hι : ∀ c : ↥(twistedE6RootGroup K σ), ι c = S.D.g0⁻¹ *
    (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) :
      ModGL Tag.E6 (AlgebraicClosure K)) * S.D.g0
  hlift : ∀ x ∈ twistedE6InndiagGL K σ, S.D.g0⁻¹ *
    (baseChangeGL (algebraMap K (AlgebraicClosure K)) x : ModGL Tag.E6 (AlgebraicClosure K)) *
      S.D.g0 ∈ S.D.model

theorem d4t2pl_nonempty_lineLangIota (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1) :
    Nonempty (TwE6LineLangIota K σ q h) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [← hqf]; exact hKq
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := by intro c; rw [← hqf]; exact hσ c
  have hpℓ : 3 ≠ ringChar K := fun h' => hK3 h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hconj, hg0, hS, hι, hlift⟩ :=
    d4t2pl_langSetup_iota_of_inndiag_twE6 hp hf hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI hchar : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  exact ⟨{
    e := f, he := hf, hqe := hqf, hℓ := hp, hK' := hK', hσ' := hσ', hL3 := hL3, hchar := hchar,
    p₀ := p₀, hp₀ := hp₀, hp₀ℓ := hp₀ℓ, hq₀ := hq₀, S := S, a := a, ι := ι, hSq := hSq,
    hT := hT, hap := hap, h1 := h1, hinj := hinj, hrange := hrange, hconj := hconj, hg0 := hg0,
    hS := hS, hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0,
    hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
      hap h1, hι := hι, hlift := hlift }⟩

theorem d4t2pl_exists_lineLangIota_of_cube {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1) {d : ℕ}
    (hd : TwE6LineDim K σ f d) :
    ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧ h ≠ 1 ∧ h ^ 3 = 1 ∧
      twE6MatFixDim K σ h = d ∧ Nonempty (TwE6LineLangIota K σ q h) := by
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hE.three_dvd
    omega
  obtain ⟨h, hh, hdim⟩ := hd
  have hinj := twE6_conj_injective K σ q hE.frob hE.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hE.elemAbelian.2 f hf
  exact ⟨h, hh, hh1, hh3, hdim,
    d4t2pl_nonempty_lineLangIota K σ q hE.char_ne_three hE.frob hE.card_field hq2 h hh1 hh3⟩

theorem twE6LineGenAt_of_model (hM : D4T2ModelGen)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hd : TwE6LineDim K σ f 30) : TwE6LineGenAt K σ E f := by
  classical
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hE.three_dvd
    omega
  obtain ⟨h, rfl, hh1, hh3, hdim, ⟨D⟩⟩ := d4t2pl_exists_lineLangIota_of_cube hE hf hf1 hd
  have hinj := twE6_conj_injective K σ q hE.frob hE.card_field hq2
  have hEcj : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hE.le_inndiag
  have hcomp0 : ∀ (x : ↥(twistedE6InndiagGL K σ)) (y : ↥(twistedE6RootGroup K σ)),
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((twistedE6InndiagConj K σ x y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K))⁻¹ := by
    intro x y
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  obtain ⟨P, hPcj, hPlf, hPι⟩ : ∃ P : D4T2PlumbData ↥(twistedE6RootGroup K σ)
      ↥(twistedE6InndiagGL K σ) (ModGL Tag.E6 (AlgebraicClosure K)),
      P.cj = twistedE6InndiagConj K σ ∧
      (∀ x : ↥(twistedE6InndiagGL K σ), P.lf x = D.S.D.g0⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) * D.S.D.g0) ∧ P.ι = D.ι :=
    ⟨D4T2PlumbData.ofBaseChange (twistedE6InndiagConj K σ)
      ((baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6InndiagGL K σ).subtype)
      ((baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6RootGroup K σ).subtype) D.ι D.S.D.g0 hinj
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _)) D.hinj D.hι hcomp0,
      rfl, fun x => D4T2PlumbData.ofBaseChange_lf .., rfl⟩
  have hlfh : P.lf h = rootDiagUnit Tag.E6 D.a := by
    have h2 : D.S.D.g0 * rootDiagUnit Tag.E6 D.a * D.S.D.g0⁻¹ =
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) := D.hg0
    rw [hPlf h, ← h2]
    group
  have hfmem : P.cj h ∈ E := by
    rw [hPcj]
    exact hf
  have hEcj' : E ≤ P.cj.range := by
    rw [hPcj]
    exact hEcj
  have hdE : rootDiagUnit Tag.E6 D.a ∈ P.liftSub E := (P.mem_liftSub).2 ⟨h, hfmem, hlfh⟩
  have hEh : P.liftSub E ≤ D.S.D.model := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (P.mem_liftSub).1 hy
    rw [hPlf x]
    exact D.hlift x x.2
  have hEab : IsElemAbelian 3 (P.liftSub E) := P.isElemAbelian_liftSub hE.elemAbelian
  have hEcard : Nat.card (P.liftSub E) = 3 ^ 3 := by
    rw [P.card_liftSub hEcj']
    exact hE.card_E
  have hEΓ : ¬ P.liftSub E ≤ D.S.Γ := by
    intro hle
    rw [← D.hrange, ← hPι] at hle
    exact hE.not_le_inn fun g hg => P.inner_of_liftSub_le_range hEcj' hle g hg
  have hnoR : ∀ R : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), R ≤ D.S.Γ → R ≠ ⊥ →
      IsPGroup (ringChar K) R → ∃ ε ∈ P.liftSub E, R.map (MulAut.conj ε).toMonoidHom ≠ R := by
    intro R hRΓ hR1 hRp
    by_contra hcon
    have hnorm : ∀ ε ∈ P.liftSub E, R.map (MulAut.conj ε).toMonoidHom = R := fun ε hε => by
      by_contra hne
      exact hcon ⟨ε, hε, hne⟩
    rw [← D.hrange, ← hPι] at hRΓ
    obtain ⟨R', hR'1, hR'p, hR'n⟩ := P.exists_normalized_of_normalized hEcj' hRΓ hR1 hRp hnorm
    exact hE.not_normalizesR ⟨R', hR'1, hR'p, hR'n⟩
  have hker : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  have h3dvd : 3 ∣ ringChar K ^ D.e + 1 := by
    rw [← D.hqe]
    exact hE.three_dvd
  have hAlg : D.S.IsAlgebraic :=
    D.S.isAlgebraic_of_algebraic K 2 (by rw [D.hSq, ← D.hqe]; exact hE.card_field)
  have key := hM D.S D.hS hAlg D.hℓ D.he D.hSq hE.char_ne_three D.hL3 h3dvd D.hT D.hap hker
    (P.liftSub E) hEh hEab hEcard hdE hEΓ hnoR
  have hmapfp := D.toTwE6LineLang.map_fixedPoints
  have hCd : D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} ≤ D.ι.range := fun x hx => by
    rw [D.hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hcomapfix : (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}).comap D.ι =
      fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) := by
    rw [← hmapfp]
    exact Subgroup.comap_map_eq_self_of_injective D.hinj _
  unfold TwE6LineGenAt
  refine (Subgroup.map_le_map_iff_of_injective D.hinj).1 ?_
  rw [hmapfp]
  refine key.trans (sup_le (sSup_le fun J hJ => ?_) (iSup₂_le fun F hF => ?_))
  ·
    have hJ' : CFSG.Open.IsComponentOf J
        (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}) := hJ
    have hJle : J ≤ D.ι.range := hJ'.1.trans hCd
    have hJc := isComponentOf_comap_of_injective D.ι D.hinj hJle hCd hJ'
    rw [hcomapfix] at hJc
    have hJY : J.comap D.ι ≤ sSup {J | CFSG.Open.IsComponentOf J
        (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))} := le_sSup hJc
    calc J = (J.comap D.ι).map D.ι := (Subgroup.map_comap_eq_self hJle).symm
      _ ≤ _ := Subgroup.map_mono (hJY.trans le_sup_left)
  ·
    obtain ⟨hFle, hFrel, hFd⟩ := hF
    obtain ⟨F', hF'E, rfl⟩ := P.exists_liftSub_eq hEcj' hFle
    have hrel : F'.relIndex E = 3 := by
      rw [← P.relIndex_liftSub F' hEcj']
      exact hFrel
    have hF'cj : F' ≤ P.cj.range := hF'E.trans hEcj'
    have hfF : twistedE6InndiagConj K σ h ∈ F' := by
      obtain ⟨x, hxF, hx⟩ := (P.mem_liftSub).1 hFd
      have hxh : x = h := P.lf_inj (hx.trans hlfh.symm)
      rw [hxh, hPcj] at hxF
      exact hxF
    have hmapF := P.map_fixedPoints_eq hF'cj
    rw [hPι, D.hrange] at hmapF
    rw [← hmapF]
    refine Subgroup.map_mono (le_trans ?_ le_sup_right)
    exact le_iSup₂_of_le F' ⟨hF'E, hrel, hfF⟩ le_rfl

end Lang

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
