module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem congr_pow_ne_one_aux {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} {p : ℕ} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    MulAut.congr e β ^ p = 1 ∧ MulAut.congr e β ≠ 1 := by
  refine ⟨by rw [← map_pow, hβ, map_one], fun h => hβ1 ?_⟩
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)


section Untw

private theorem exists_inndiag_of_mem_inner {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (β : MulAut ↥(adjointGroup τ K))
    (hβinn : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  obtain ⟨g, rfl⟩ := hβinn
  have hgp : g ^ p = 1 := by
    have : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, hβp, map_one]
    exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
  refine ⟨(g : ModGL τ K), adjointGroup_le_inndiagGroup g.2, fun c => ?_, ?_, ?_⟩
  · simp [MulAut.conj_apply]
  · rw [← Subgroup.coe_pow, hgp]
    rfl
  · intro h1
    apply hβ1
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]


theorem exists_inndiag_of_mem_innAutDerived_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (β : MulAut ↥(adjointGroup τ K)) (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  rcases hτ with rfl | rfl | hE
  ·
    refine exists_inndiag_of_mem_inner β ?_ hβp hβ1
    by_cases h3 : ringChar K = 3
    · haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := by
        have : CharP K (ringChar K) := ringChar.charP K
        rw [h3] at this
        exact this
      have hK' : Nat.card K = 3 ^ (f : ℕ) := by rw [hK, h3]
      obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form f.pos K hK'
      have hle : innAutDerived ↥(adjointGroup .G2 K) ≤ Θ.ker := by
        refine sup_le ?_ (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ
          fun a b => mul_comm a b)
        rw [hker]
        exact le_rfl
      have := hle hβmem
      rw [hker] at this
      exact this
    · have hK4 : 4 ≤ Nat.card K := by
        by_contra h4
        have hK3' : Nat.card K = 3 := by have := hG2 rfl; omega
        apply h3
        have hdvd : ringChar K ∣ 3 := by
          rw [← hK3', hK]
          exact dvd_pow_self _ f.ne_zero
        exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd
      exact CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outg2_innAutDerived_le_inner h3 hK4 hβmem
  ·
    exact exists_inndiag_of_mem_inner β
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_innAutDerived_le_inner_F4 hℓ f.pos hK hβmem)
      hβp hβ1
  ·
    obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hE K
    have hcomm : ∀ x y : RingAut K × Multiplicative (ZMod (exactE τ)), x * y = y * x := by
      rintro ⟨x1, x2⟩ ⟨y1, y2⟩
      exact Prod.ext (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K x1 y1)
        (mul_comm x2 y2)
    have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup τ K) ≤
        Θ.ker := by
      rintro _ ⟨g, rfl⟩
      refine (hker _).2 ⟨g, 1, fun h => ?_⟩
      simp [rootDiagUnit_one, MulAut.conj_apply]
    have hle : innAutDerived ↥(adjointGroup τ K) ≤ Θ.ker :=
      sup_le hinner (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ hcomm)
    obtain ⟨g, a, hga⟩ := (hker β).1 (hle hβmem)
    have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
      mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
    have hβw : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
        ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
      intro c
      rw [hga c]
      group
    obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hE hp β hβp hw hβw
    refine ⟨h', hh', hβh', hh'p, ?_⟩
    rintro rfl
    apply hβ1
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hβh' c]
    simp


theorem compNormal_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (hE6 : τ = .E6 → p ≠ 3)
    (β : MulAut ↥(adjointGroup τ K)) (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) : CompNormal β := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_untw hτ hG2 hp β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := fun h' => hpK (by rw [hK, ← h']; exact dvd_pow_self p f.ne_zero)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (hG2 rfl)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ hp hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := by
    intro hτG2
    rw [hSq]
    by_cases hp5 : 5 ≤ p
    · exact Or.inl hp5
    · right
      have hp3 : p = 3 := by
        have h2 := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by norm_num)
      have h3 := hG2 hτG2
      by_contra h4
      have hK3 : Nat.card K = 3 := by omega
      exact hpK (by rw [hK3, hp3])
  have hTame := langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure hp hpK) hsmall hT
    hap h1
  have hW := rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2
    (by rcases hτ with h' | h' | h' | h' | h' <;> simp [h']) hE6 hap
  exact compNormal_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hW

private theorem compNormal_untw_cat {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid)
    (hG2 : τ = .G2 → 3 ≤ q.card) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hE6 : τ = .E6 → p ≠ 3) {T : Type} [Group T] (e : T ≃* (CFSGIndex.lie ⟨c q, hv⟩).Group)
    (x : MulAut T) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxmem : x ∈ innAutDerived T) :
    CompNormal x := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' := e.trans eK
  refine compNormal_of_congr e' x ?_
  obtain ⟨hxp', hx1'⟩ := congr_pow_ne_one_aux e' hxp hx1
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK, PrimePower.card_def]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  exact compNormal_adjointGroup hτ (fun h => hK ▸ hG2 h) hp hp2 hpK hE6 _
    ((mem_innAutDerived_congr e').2 hxmem) hxp' hx1'

end Untw

section Tw


theorem compNormal_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpℓ : p ≠ ℓ)
    (β : MulAut ↥(twistedE6RootGroup K σ))
    (hβmem : β ∈ innAutDerived ↥(twistedE6RootGroup K σ)) (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    CompNormal β := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hKf : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · exact CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ
        fun x y => hcyc.isMulCommutative.is_comm.comm x y
  have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβmem
  obtain ⟨h, rfl⟩ := hmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective hℓ hf hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀ hmon
      (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  have hTame := langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
    (fun h => absurd h (by decide)) hT hap h1
  have hW := rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2 (by simp)
    (fun _ => hp3) hap
  exact compNormal_of_langSetup S hp ι hinj hrange _ hconj hT hap h1 hTame hW

theorem compNormal_trialityD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβmem : β ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) : CompNormal β := by
  classical
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range hℓ hf
      hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : x ^ p = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβp, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hmon : MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hTame := langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
    (fun h => absurd h (by decide)) hT hap h1
  have hW := rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2 (by simp)
    (fun h => absurd h (by decide)) hap
  exact compNormal_of_langSetup S hp ι hinj hrange _ hconj hT hap h1 hTame hW

end Tw

section Cat


theorem genNormalExcInner_holds : GenNormalExcInner := by
  intro p T _ _ d h hcore hE6 x hxp hx1 hxmem
  obtain ⟨e⟩ := h.iso
  obtain ⟨d, hv⟩ := d
  have hpc : p ≠ d.characteristic := h.ne
  cases d with
  | E6 q =>
    exact compNormal_untw_cat (Or.inr (Or.inr (Or.inl rfl)))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv (fun h => absurd h (by decide)) h.prime
      h.odd ((LieTypeIndex.characteristic_E6 q) ▸ hpc) (fun _ hp3 => hE6 ⟨hp3, q, Or.inl rfl⟩)
      e x hxp hx1 hxmem
  | E7 q =>
    exact compNormal_untw_cat (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv (fun h => absurd h (by decide)) h.prime
      h.odd ((LieTypeIndex.characteristic_E7 q) ▸ hpc) (fun h => absurd h (by decide))
      e x hxp hx1 hxmem
  | E8 q =>
    exact compNormal_untw_cat (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv (fun h => absurd h (by decide)) h.prime
      h.odd ((LieTypeIndex.characteristic_E8 q) ▸ hpc) (fun h => absurd h (by decide))
      e x hxp hx1 hxmem
  | F4 q =>
    exact compNormal_untw_cat (Or.inr (Or.inl rfl))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv (fun h => absurd h (by decide)) h.prime
      h.odd ((LieTypeIndex.characteristic_F4 q) ▸ hpc) (fun h => absurd h (by decide))
      e x hxp hx1 hxmem
  | G2 q =>
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    exact compNormal_untw_cat (Or.inl rfl)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv (fun _ => hr) h.prime
      h.odd ((LieTypeIndex.characteristic_G2 q) ▸ hpc) (fun h => absurd h (by decide))
      e x hxp hx1 hxmem
  | twistedE6 q =>
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    haveI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
    let e' := e.trans eK
    refine compNormal_of_congr e' x ?_
    obtain ⟨hxp', hx1'⟩ := congr_pow_ne_one_aux e' hxp hx1
    exact compNormal_twistedE6 q.prime_p q.exponent_pos hK σ hσ h.prime h.odd
      (fun hp3 => hE6 ⟨hp3, q, Or.inr rfl⟩) ((LieTypeIndex.characteristic_twistedE6 q) ▸ hpc) _
      ((mem_innAutDerived_congr e').2 hxmem) hxp' hx1'
  | trialityD4 q =>
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
    let e' := e.trans eK
    refine compNormal_of_congr e' x ?_
    obtain ⟨hxp', hx1'⟩ := congr_pow_ne_one_aux e' hxp hx1
    exact compNormal_trialityD4 q.prime_p q.exponent_pos hK σ hσ h.prime h.odd
      ((LieTypeIndex.characteristic_trialityD4 q) ▸ hpc) _
      ((mem_innAutDerived_congr e').2 hxmem) hxp' hx1'
  | _ => simp [S2019.S2019ExcCoreIdx] at hcore

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
