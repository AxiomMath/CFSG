module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Untw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.RecipeExcLang CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

theorem lieCompsExport_of_congr_exc {q : ℕ} {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (h : LieCompsExport q (MulAut.congr e β)) : LieCompsExport q β := by
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : ∀ {K : Subgroup S}, IsComponentOf K (fixSubgroup β) →
      IsComponentOf (K.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := fun hK => by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β h.layer, fun K hK => ?_⟩
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps _ (hmapc hK)
  let g : ↥(K.map (e : S →* G)) ≃* ↥K :=
    (K.equivMapOfInjective (e : S →* G) e.injective).symm
  refine ⟨X, inferInstance, inferInstance, hX, (g : _ →* ↥K).comp f, g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

theorem congr_conj_exc {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem conj_symm_eq_of_congr_eq_conj {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} {g : G} (h : MulAut.congr e β = MulAut.conj g) :
    MulAut.conj (e.symm g) = β := by
  apply (MulAut.congr e).injective
  rw [h, congr_conj_exc, MulEquiv.apply_symm_apply]

theorem pow_mul_mem_of_normalizer {G : Type*} [Group G] (N : Subgroup G) {t c : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hc : c ∈ N) {m : ℕ} (htm : t ^ m = 1) :
    (t * c) ^ m ∈ N := by
  have key : ∀ n : ℕ, ∃ c' ∈ N, (t * c) ^ n = t ^ n * c' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨c', hc', hn⟩ := ih
      have h1 : t⁻¹ * c' * t ∈ N := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (N : Set G)).inv_mem ht) c').1 hc'
        simpa using this
      refine ⟨t⁻¹ * c' * t * c, mul_mem h1 hc, ?_⟩
      rw [pow_succ, hn, pow_succ]
      group
  obtain ⟨c', hc', hn⟩ := key m
  rw [hn, htm, one_mul]
  exact hc'

theorem mem_of_pow_eq_one_of_pow_mem {G : Type*} [Group G] (N : Subgroup G) {x : G} {p m : ℕ}
    (hcop : Nat.Coprime p m) (hxp : x ^ p = 1) (hxm : x ^ m ∈ N) : x ∈ N := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, h⟩
  have h1 : (x ^ p) ^ a * (x ^ m) ^ b = x := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [show (p : ℤ) * a + (m : ℤ) * b = 1 by linarith, zpow_one]
  rw [hxp, one_zpow, one_mul] at h1
  rw [← h1]
  exact zpow_mem hxm b

theorem coprime_card_sub_one {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : p ∣ n) :
    Nat.Coprime p (n - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ n - (n - 1) := Nat.dvd_sub hpn h
  have h2 : n - (n - 1) = 1 := by omega
  rw [h2] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

section Residual


@[expose] def TrialityFieldExportP (p : ℕ) : Prop :=
  ∀ (ℓ f : ℕ) [Fact ℓ.Prime], 1 ≤ f → ∀ (K₃ : Type) [Field K₃] [Finite K₃],
    Nat.card K₃ = (ℓ ^ f) ^ 3 → ∀ (Fr : K₃ ≃+* K₃), (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ p = 1 →
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range →
      LieCompsExport ℓ φ

end Residual

section Inn


theorem inndiagGroup_le_normalizer_adjointGroup {τ : Tag} {K : Type} [Field K] :
    inndiagGroup τ K ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => conj_mem_adjointGroup_of_mem_inndiag hw hh
  · intro hh
    have h1 := conj_mem_adjointGroup_of_mem_inndiag (inv_mem hw) hh
    simpa [mul_assoc] using h1

theorem mem_adjointGroup_of_pow_eq_one_of_dvd {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K) {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K)
    (hwp : w ^ p = 1) : w ∈ adjointGroup τ K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨b, j, hj, rfl⟩ := hw
  have hm : (rootDiagUnit τ b * j) ^ (Nat.card K - 1) ∈ adjointGroup τ K := by
    have hd : rootDiagUnit τ b ^ (Nat.card K - 1) = 1 := by
      refine rootDiagUnit_pow_eq_one_of_forall fun i => Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ (b i).ne_zero
    exact pow_mul_mem_of_normalizer (adjointGroup τ K)
      (inndiagGroup_le_normalizer_adjointGroup (rootDiagUnit_mem_inndiagGroup b)) hj hd
  exact mem_of_pow_eq_one_of_pow_mem (adjointGroup τ K)
    (coprime_card_sub_one hp Nat.card_pos hpK) hwp hm

theorem mem_twistedE6InndiagGL_decomp_copy (K : Type) [Field K] (σ : K ≃+* K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6InndiagGL K σ) :
    ∃ c ∈ twistedE6RootGroup K σ, ∃ t ∈ twistedE6DiagGL K σ, x = c * t := by
  have hN : twistedE6DiagGL K σ ≤ Subgroup.normalizer
      (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    (le_sup_right : twistedE6DiagGL K σ ≤ twistedE6InndiagGL K σ).trans
      (twistedE6InndiagGL_le_normalizer K σ)
  have key : ∀ y ∈ Subgroup.closure ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
      (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K))),
      ∃ c ∈ twistedE6RootGroup K σ, ∃ t ∈ twistedE6DiagGL K σ, y = c * t := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact ⟨z, hz, 1, one_mem _, (mul_one z).symm⟩
      · exact ⟨1, one_mem _, z, hz, (one_mul z).symm⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      obtain ⟨c', hc', t', ht', rfl⟩ := hb
      refine ⟨c * (t * c' * t⁻¹), mul_mem hc ?_, t * t', mul_mem ht ht', ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hN ht) c').1 hc'
      · group
    | inv a _ ha =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      refine ⟨t⁻¹ * c⁻¹ * t, ?_, t⁻¹, inv_mem ht, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem ht)) c⁻¹).1 (inv_mem hc)
        rwa [inv_inv] at h'
      · group
  exact key x (mem_twistedE6InndiagGL_iff.1 hx)

theorem mem_twistedE6RootGroup_of_pow_eq_one_of_dvd {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K)
    {w : ModGL TwistTag.E6.tag K} (hw : w ∈ twistedE6InndiagGL K σ) (hwp : w ^ p = 1) :
    w ∈ twistedE6RootGroup K σ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hc, t, ht, rfl⟩ := mem_twistedE6InndiagGL_decomp_copy K σ hw
  have htN : t ∈ Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    twistedE6InndiagGL_le_normalizer K σ
      ((le_sup_right : twistedE6DiagGL K σ ≤ twistedE6InndiagGL K σ) ht)
  have htm : t ^ (Nat.card K - 1) = 1 := by
    obtain ⟨u, rfl⟩ := ht
    refine rootDiagUnit_pow_eq_one_of_forall fun i => Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
  have hm : (c * t) ^ (Nat.card K - 1) ∈ twistedE6RootGroup K σ := by
    have h1 : c * t = t * (t⁻¹ * c * t) := by group
    have h2 : t⁻¹ * c * t ∈ twistedE6RootGroup K σ := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer
        (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K))).inv_mem htN) c).1 hc
      simpa using this
    rw [h1]
    exact pow_mul_mem_of_normalizer _ htN h2 htm
  exact mem_of_pow_eq_one_of_pow_mem (twistedE6RootGroup K σ)
    (coprime_card_sub_one hp Nat.card_pos hpK) hwp hm

end Inn

section Families


theorem lieCompsExport_untwP {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : ExcRationalLieTypesP p) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hG2 : ∀ (q : TauCeti.PrimePower), (c q).Valid → τ = .G2 → 3 ≤ q.card)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (c q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) (β : MulAut S) (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) (hq : q.p ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β)
    (hlayer : q.p ≠ p → PerfectInLayer β) : LieCompsExport q.p β := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, _, hKfin, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  have hℓ : ringChar K = q.p := ringChar.eq K q.p
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine lieCompsExport_of_congr_exc e' ?_
  have hG2K : τ = .G2 → 3 ≤ Nat.card K := fun h => hK ▸ hG2 q hv h
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e' β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
        ((MulAut.congr e' β) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ p = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact exists_field_or_inndiag_FG (Or.inr h) hG2K hp hp2 _ hβ' hβ1'
    · exact exists_field_or_inndiag_FG (Or.inl h) hG2K hp hp2 _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inl h) hp hp2 _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inl h)) hp hp2 _ hβ' hβ1'
    · exact exists_field_or_inndiag_E (Or.inr (Or.inr h)) hp hp2 _ hβ' hβ1'
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  · refine (lieCompExport_of_conj ψ _ ?_).toComps
    rw [hψ]
    exact lieCompExport_entrywiseAdjointAut_untw hB hchar hvalid hA6 hℓ σ
  · by_cases hqp : q.p = p
    · exfalso
      have hout : ∀ a : S, MulAut.conj a ≠ β := hq.resolve_left (not_not.2 hqp)
      have hpK : p ∣ Nat.card K := by
        rw [hK, TauCeti.PrimePower.card_def, ← hqp]
        exact dvd_pow_self _ q.exponent_pos.ne'
      have hmem := mem_adjointGroup_of_pow_eq_one_of_dvd hp hpK hh hp1
      refine hout (e'.symm ⟨h, hmem⟩) (conj_symm_eq_of_congr_eq_conj e' ?_)
      ext c : 1
      apply Subtype.ext
      rw [hβh c]
      rfl
    · have hpK : ¬ p ∣ Nat.card K := by
        rw [hK]
        exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp (Ne.symm hqp)
      exact lieCompsExport_inner_untwP hp hp5 hres hτ hG2K hpK _ h
        (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
        (perfectInLayer_congr_of e' (hlayer hqp)) hℓ

theorem lieCompsExport_twE6P {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : ExcRationalLieTypesP p)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (hmon : MonomialToralAt Tag.E6 p)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) (β : MulAut S) (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) (hq : q.p ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β)
    (hlayer : q.p ≠ p → PerfectInLayer β) : LieCompsExport q.p β := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine lieCompsExport_of_congr_exc e' ?_
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e' β) = 1
  · have hmem : MulAut.congr e' β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, hh⟩ := hmem
    have hp1 : h ^ p = 1 :=
      twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
        (by rw [map_pow, hh, hβ', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1' (by rw [← hh, h', map_one])
    by_cases hqp : q.p = p
    · exfalso
      have hout : ∀ a : S, MulAut.conj a ≠ β := hq.resolve_left (not_not.2 hqp)
      have hpK : p ∣ Nat.card K := by
        rw [hK, ← hqp]
        exact Dvd.dvd.pow (dvd_pow_self _ q.exponent_pos.ne') (by norm_num)
      have hmem := mem_twistedE6RootGroup_of_pow_eq_one_of_dvd σ hp hpK h.2
        (by rw [← Subgroup.coe_pow, hp1]; rfl)
      refine hout (e'.symm ⟨(h : ModGL TwistTag.E6.tag K), hmem⟩)
        (conj_symm_eq_of_congr_eq_conj e' (hh.symm.trans ?_))
      ext c : 1
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      rfl
    · have hlayer' := perfectInLayer_congr_of e' (hlayer hqp)
      rw [← hh] at hlayer' ⊢
      exact lieCompsExport_inner_twE6P hp hp2 hres q.prime_p q.exponent_pos hK σ hσ
        (Ne.symm hqp) hmon h hp1 hh1 hlayer'
  · exact (lieCompExport_twE6_field hA6 q.prime_p q.exponent_pos
      (by rw [hK, ← pow_mul, mul_comm]) σ hσ hp hp2 Θ hΘ _ hβ' hΘβ).toComps

theorem lieCompsExport_triD4P {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : ExcRationalLieTypesP p) (hD4 : TrialityFieldExportP p)
    (hmon : MonomialToralAt Tag.D4 p)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (β : MulAut S) (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) (hq : q.p ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β)
    (hlayer : q.p ≠ p → PerfectInLayer β) : LieCompsExport q.p β := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘker⟩, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  refine lieCompsExport_of_congr_exc e' ?_
  by_cases hΘβ : Θ (MulAut.congr e' β) = 1
  · have hmem : MulAut.congr e' β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hΘker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, hx⟩ := hmem
    by_cases hqp : q.p = p
    · exfalso
      have hout : ∀ a : S, MulAut.conj a ≠ β := hq.resolve_left (not_not.2 hqp)
      exact hout (e'.symm x) (conj_symm_eq_of_congr_eq_conj e' hx.symm)
    · have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
        center_graphFixedRootGroup_eq_bot σ.surjective
      have hxp : x ^ p = 1 :=
        mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hx, hβ', map_one])
      have hx1 : x ≠ 1 := fun h' => hβ1' (by rw [← hx, h', map_one])
      have hlayer' := perfectInLayer_congr_of e' (hlayer hqp)
      rw [← hx] at hlayer' ⊢
      exact lieCompsExport_inner_triD4P hp hp2 hres q.prime_p q.exponent_pos hK σ hσ
        (Ne.symm hqp) hmon x hxp hx1 hlayer'
  · have hout' : MulAut.congr e' β ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hΘker]; exact hmem)
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    exact hD4 q.p q.exponent q.exponent_pos K hK σ hσ _ hβ' hout'


end Families

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
