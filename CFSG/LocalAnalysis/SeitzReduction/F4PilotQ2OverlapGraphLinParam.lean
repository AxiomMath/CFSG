module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphParamExists
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RootSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_graphLift_aut_nonsplit_F4_two {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ)
    (hN : t ∈ normalizer (centralizerPerfectCore (subgroupToG e X₀) : Set G)) :
    ∃ (S : Type) (_ : Group S) (ρ : centralizerPerfectCore (subgroupToG e X₀) →* S)
      (τ : MulAut S), Function.Surjective ρ ∧
        ρ.ker ≤ center (centralizerPerfectCore (subgroupToG e X₀)) ∧ Sp6KindType S 1 κ ∧
        (∀ y, ρ ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom ⟨t, hN⟩ y) =
          τ (ρ y)) ∧
        τ * τ = 1 ∧ τ ∉ (MulAut.conj : S →* MulAut S).range ∧
        LieModel (fixedSubgroup τ) .PSp 3 2 1 := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨htX, hk⟩ := hk
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, hcase⟩ := hk
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => hκ.2 h.1
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nonsplit hw.standard.standard htC hw.orderOf_eq hKt
    hw.card_eq e hXJ hcyc hX₀' hX htX hDe
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hOut : Group.IsSolvable (Outer Kb) :=
    isSolvable_outer_of_sp6KindType_graph hKbP hκ.1 hκ.2 hty
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) :=
    (inSubgroup_layer_inf_centralizer_nonsplit e hXJ hcyc hX₀').symm
  obtain ⟨hcen, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe, inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup]
  have hDH : D ≤ centralizer (X : Set G) := map_map_symm_le_centralizer e hX₀D
  have hDq : CFSG.IsQuasisimple D := isQuasisimple_map_C3Levi e
  let eD : C3Levi K ≃* D :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  have hZD : center D = ⊥ := center_eq_bot_congr eD center_C3Levi_eq_bot
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    SeitzQ2.inf_centralizer_le_of_le_sup hLX (le_centralizer_iff.1 hDH) hZD
  have hOutL : IsPGroup 2 (Outer L) := SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK2 e
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hw.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hw.standard.standard htC hw.orderOf_eq
  have hB : HasBLift Kb := SeitzQ2.hasBLift_of_isPGroup_outer hOutL htC hw.orderOf_eq htL hCN
    hKt htX hlayer hDq hXD (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ H := centralizerPerfectCore_le_centralizer X
  have hθ : ∀ y : centralizerPerfectCore X,
      qh ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
        Kb.normalizerMonoidHom ⟨_, hsN⟩ (qh y) := by
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y :
        centralizerPerfectCore X) : G), hle ((centralizerPerfectCore X).normalizerMonoidHom
          ⟨t, hN⟩ y).2⟩ : H) = t' * ⟨(y : G), hle y.2⟩ * t'⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  set τK := Kb.normalizerMonoidHom ⟨_, hsN⟩ with hτK
  have hτK2 : τK * τK = 1 := by
    rw [hτK, ← map_mul]
    convert map_one Kb.normalizerMonoidHom
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hs2, pow_orderOf_eq_one]; rfl)
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
  refine ⟨Kb ⧸ center Kb, inferInstance, (QuotientGroup.mk' (center Kb)).comp qh,
    centerQuotientAut τK, (QuotientGroup.mk'_surjective _).comp hqs, fun x hx => ?_, hty,
    fun y => ?_, ?_, fun hin => ?_, hov.2.2.2⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center qh hqker hx
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hθ, centerQuotientAut_mk]
  · rw [← centerQuotientAut_mul, hτK2, centerQuotientAut_one]
  · exact hov.1 (mem_range_conj_of_centerQuotientAut (MonoidHom.id Kb)
      Function.surjective_id (fun g => rfl) hin)

theorem exists_mulEquiv_centralizerPerfectCore_linear_two {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ = .linear6 ∨ κ = .linear7)
    (hk : TwoKindAt e t X₀ κ)
    (hN : t ∈ normalizer (centralizerPerfectCore (subgroupToG e X₀) : Set G)) :
    ∃ (r : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ((κ = .linear6 ∧ r = 6) ∨ (κ = .linear7 ∧ r = 7)) ∧
      ∃ ε : centralizerPerfectCore (subgroupToG e X₀) ≃* LinearFlag.projectiveSL r F,
        MulAut.congr ε ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom
            ⟨t, hN⟩) *
          MulAut.congr ε ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom
            ⟨t, hN⟩) = 1 ∧
        MulAut.congr ε ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom
            ⟨t, hN⟩) ∉ (MulAut.conj : LinearFlag.projectiveSL r F →* MulAut _).range ∧
        LieModel (fixedSubgroup (MulAut.congr ε
          ((centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom ⟨t, hN⟩)))
          .PSp 3 2 1 := by
  have hκg : κ.IsGraphKind := by rcases hκ with rfl | rfl <;> decide
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  obtain ⟨S, _, ρ, τ, hρ, hker, hty, hρθ, hττ, hout, hfix⟩ :=
    exists_graphLift_aut_nonsplit_F4_two hw e hXJ hcyc hX₀ hκg hk hN
  obtain ⟨r, hS, hr⟩ : ∃ r, LieModel S .PSL r 2 1 ∧
      ((κ = .linear6 ∧ r = 6) ∨ (κ = .linear7 ∧ r = 7)) := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hty, Or.inr ⟨rfl, rfl⟩⟩
  have hEperf : Group.IsPerfect E := isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by rcases hr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl⟩
  have hr5 : 4 ≤ r' := by rcases hr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨F', _, _, hF', Φ, hΦ, hΦk⟩ := exists_sl_cover_of_surjective hEperf hr5 hS ρ hρ hker
  have hF'2 : Nat.card F' = 2 := by rw [hF', pow_one]
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    exact LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hF'2 (hΦk hz)
  have hZ : center E = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨w, hw'⟩ : (z : G) ∈ Φ.range := by rw [hΦ]; exact z.2
    have hwc : w ∈ center (Matrix.SpecialLinearGroup (Fin (r' + 1)) F') := by
      rw [mem_center_iff]
      intro v
      apply hΦinj
      have hv : Φ v ∈ E := by rw [← hΦ]; exact ⟨v, rfl⟩
      have := congrArg Subtype.val (mem_center_iff.1 hz ⟨Φ v, hv⟩)
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_mul, hw']
      exact this
    have h1 := LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hF'2 hwc
    rw [h1, map_one] at hw'
    exact mem_bot.2 (Subtype.ext hw'.symm)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hadm := statedLieAdmissible_of_lieModel hS
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  set εS : S ≃* LinearFlag.projectiveSL (r' + 1) F :=
    eJ.trans (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv (r' + 1) F).symm
    with hεS
  set ρe : E ≃* S := MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩ with hρe
  have hcongr : MulAut.congr ρe (E.normalizerMonoidHom ⟨t, hN⟩) = τ := by
    ext z
    obtain ⟨y, rfl⟩ := hρ z
    change ρ (E.normalizerMonoidHom ⟨t, hN⟩ (ρe.symm (ρ y))) = τ (ρ y)
    have : ρe.symm (ρ y) = y := ρe.symm_apply_apply y
    rw [this, hρθ]
  have h1 : MulAut.congr (ρe.trans εS) (E.normalizerMonoidHom ⟨t, hN⟩) =
      MulAut.congr εS τ := by
    rw [← hcongr]
    ext z
    rfl
  refine ⟨r' + 1, F, inferInstance, inferInstance, by rw [hF, pow_one], hr, ρe.trans εS, ?_, ?_,
    ?_⟩
  · rw [h1, ← map_mul, hττ, map_one]
  · intro hin
    rw [h1] at hin
    exact hout ((FixedFourGroup.congr_mem_inner_iff εS τ).1 hin)
  · rw [h1]
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv εS τ) hfix

open CFSG.SeitzReduction.SymplecticPilot (spBlock blockComplEquiv q2Block planeCoordsQ2
  card_planeCoordsQ2 q2Embed q2Embed_mem_q2Block_iff spBlock_compl_singleton complSpEquiv) in
theorem exists_twoLinParam [Finite K] [CharP K 2] (hK : Nat.card K = 2) {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {ε : ℕ} {κ : Sp6Kind}
    (hκ : (κ = .linear6 ∧ ε = 0) ∨ (κ = .linear7 ∧ ε = 1)) (hk : TwoKindAt e t X₀ κ) :
    ∃ Φ : q2Block ε K ({3} : Finset (Fin 4)) ≃* centralizerPerfectCore (subgroupToG e X₀),
      IsTwoGraphParam e X₀ (twoLinIota ε hK) Φ := by
  have hε : ε ≤ 1 := by rcases hκ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK]
  have hXL : subgroupToG e X₀ ≤ L := map_subtype_le _
  have hN : t ∈ normalizer (centralizerPerfectCore (subgroupToG e X₀) : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore _
      (centralizer_le_normalizer _ (centralizer_le hXL hw.mem_centralizer))
  have hκ' : κ = .linear6 ∨ κ = .linear7 := by
    rcases hκ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨r, F, _, _, hF, hr, ε₀, hα2, hαo, hαfix⟩ :=
    exists_mulEquiv_centralizerPerfectCore_linear_two hw e hXJ hcyc hX₀ hκ' hk hN
  have hr' : r = 2 * 3 + ε := by
    rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · cases h1
    · cases h1
    · omega
  subst hr'
  set θ := (centralizerPerfectCore (subgroupToG e X₀)).normalizerMonoidHom ⟨t, hN⟩ with hθ
  have hcard : ((planeCoordsQ2 ε ({3} : Finset (Fin 4)))ᶜ).card = 2 * 3 + ε := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨χK⟩ : Nonempty (q2Block ε K ({3} : Finset (Fin 4)) ≃*
      LinearFlag.projectiveSL (2 * 3 + ε) K) := by
    have := CFSG.SeitzReduction.SymplecticPilot.nonempty_q2Block_mulEquiv (ε := ε) hK
      ({3} : Finset (Fin 4))
    rwa [hcard] at this
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  have hKF : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]
  set χ : q2Block ε K ({3} : Finset (Fin 4)) ≃* LinearFlag.projectiveSL (2 * 3 + ε) F :=
    χK.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
      (FiniteField.ringEquivOfCardEq hKF)) with hχ
  set ψ₀ : q2Block ε K ({3} : Finset (Fin 4)) ≃* centralizerPerfectCore (subgroupToG e X₀) :=
    χ.trans ε₀.symm with hψ₀
  set α : MulAut (q2Block ε K ({3} : Finset (Fin 4))) := MulAut.congr ψ₀.symm θ with hα
  have hαcongr : MulAut.congr χ α = MulAut.congr ε₀ θ := by
    ext z
    simp [hα, hψ₀, MulAut.congr_apply]
  have hαα : α * α = 1 := (MulAut.congr χ).injective (by
    rw [map_mul, hαcongr, hα2, map_one])
  have hαo' : α ∉ (MulAut.conj : q2Block ε K ({3} : Finset (Fin 4)) →* MulAut _).range :=
    fun h' => hαo (by rw [← hαcongr]; exact (FixedFourGroup.congr_mem_inner_iff χ α).2 h')
  have hαfix' : LieModel (fixedSubgroup α) .PSp 3 2 1 := by
    rw [← hαcongr] at hαfix
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv χ α).symm hαfix
  obtain ⟨β, hβ⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_eq_mul_q2GraphBlock_mul_inv hK hε
    (le_refl 3) (3 : Fin 4) hF χ hαα hαo' hαfix'
  set ψ₁ : q2Block ε K ({3} : Finset (Fin 4)) ≃* centralizerPerfectCore (subgroupToG e X₀) :=
    β.trans ψ₀ with hψ₁
  have hψ₁θ : ∀ x, θ (ψ₁ x) =
      ψ₁ (CFSG.SeitzReduction.SymplecticPilot.q2GraphBlock ε hK {3} x) := by
    intro x
    have h1 : ∀ y, θ (ψ₀ y) = ψ₀ (α y) := by
      intro y
      simp [hα, MulAut.congr_apply]
    change θ (ψ₀ (β x)) = ψ₀ (β (CFSG.SeitzReduction.SymplecticPilot.q2GraphBlock ε hK {3} x))
    rw [h1, hβ]
    simp
  obtain ⟨-, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hDH : subgroupToG e (C3Levi K) ≤ centralizer (subgroupToG e X₀ : Set G) :=
    map_map_symm_le_centralizer e hX₀D
  have hDperf : ⁅subgroupToG e (C3Levi K), subgroupToG e (C3Levi K)⁆ =
      subgroupToG e (C3Levi K) :=
    isPerfect_iff.mp (isQuasisimple_map_C3Levi e).1
  have hDM : subgroupToG e (C3Levi K) ≤ centralizerPerfectCore (subgroupToG e X₀) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  set ι₀ : spBlock K ({3} : Finset (Fin 4))ᶜ →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((c3LeviHom K).comp (blockComplEquiv K (3 : Fin 4)).toMonoidHom)) with hι₀
  have hι₀r : ι₀.range = subgroupToG e (C3Levi K) := by
    rw [hι₀, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulEquiv.surjective _), ← MonoidHom.range_eq_map,
      range_c3LeviHom]
    rfl
  have hι₀mem : ∀ y, ι₀ y ∈ centralizerPerfectCore (subgroupToG e X₀) :=
    fun y => hDM (hι₀r ▸ ⟨y, rfl⟩)
  set ι : spBlock K ({3} : Finset (Fin 4))ᶜ →* centralizerPerfectCore (subgroupToG e X₀) :=
    ι₀.codRestrict _ hι₀mem with hιdef
  have hιinj : Function.Injective ι := by
    intro y z hyz
    have h1 := congrArg (fun w : centralizerPerfectCore (subgroupToG e X₀) => (w : G)) hyz
    apply (blockComplEquiv K (3 : Fin 4)).injective
    apply c3LeviHom_injective (K := K)
    apply e.symm.injective
    exact Subtype.ext h1
  have hιr : ι.range = perfectCore (fixedSubgroup θ) := by
    apply Subgroup.map_injective (centralizerPerfectCore (subgroupToG e X₀)).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore]
    change _ = perfectCore ((MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).map
      (centralizerPerfectCore (subgroupToG e X₀)).subtype)
    rw [hθ, CFSG.SeitzReduction.SymplecticPilot.map_eqLocus_normalizerMonoidHom_eq hN,
      perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀',
      MonoidHom.map_range, ← hι₀r]
    rfl
  have haut := CFSG.SeitzReduction.SymplecticPilot.exists_eq_conj_of_mulAut_spBlock hK
    (le_refl 3) (3 : Fin 4)
  have hperf : Group.IsPerfect (spBlock K ({3} : Finset (Fin 4))ᶜ) := by
    have := CFSG.SeitzReduction.SymplecticPilot.isPerfect_statedSp_of_charTwo (k := K)
      (le_refl 3)
    exact Group.IsPerfect.ofSurjective (f := (blockComplEquiv K (3 : Fin 4)).symm.toMonoidHom)
      (MulEquiv.surjective _)
  obtain ⟨ψ', hψ'⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_eq_of_intertwine hK hε
    haut hperf ψ₁ hψ₁θ ι hιinj hιr
  refine ⟨ψ', fun g => ?_⟩
  have hy : (complSpEquiv (K := K) (3 : Fin 4) g : CFSG.Assembly.LowTwoRank.StatedSp 4 K) ∈
      spBlock K ({3} : Finset (Fin 4))ᶜ := by
    rw [spBlock_compl_singleton]
    exact (complSpEquiv (K := K) (3 : Fin 4) g).2
  have h2 : twoLinIota ε hK g = ⟨q2Embed ε hK (complSpEquiv (K := K) (3 : Fin 4) g :
      CFSG.Assembly.LowTwoRank.StatedSp 4 K), (q2Embed_mem_q2Block_iff hK).2 hy⟩ := rfl
  have h3 : blockComplEquiv K (3 : Fin 4) ⟨_, hy⟩ = g := by
    rw [CFSG.SeitzReduction.SymplecticPilot.blockComplEquiv, MulEquiv.trans_apply]
    exact (complSpEquiv (K := K) (3 : Fin 4)).symm_apply_apply g
  rw [h2, hψ' _ hy]
  change ((e.symm (c3LeviHom K (blockComplEquiv K (3 : Fin 4) ⟨_, hy⟩)) : L) : G) = _
  rw [h3]

theorem twoGraphModelInput_linear7 : TwoGraphModelInput .linear7 := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨Φ, hΦ⟩ := exists_twoLinParam hK hw e hXJ hcyc hX₀ (Or.inr ⟨rfl, rfl⟩) hk
  exact ⟨_, inferInstance, inferInstance, twoLinIota 1 hK, Φ, hΦ, twoGraphModelValues_linear7 hK⟩

theorem twoOverlapInvAt_linear7 : TwoOverlapInvAt .linear7 :=
  twoOverlapInvAt_of_modelInput twoGraphModelInput_linear7

theorem twoOverlapInvAt_linear6_of_values
    (hV : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
      TwoGraphModelValues .linear6 K
        (CFSG.SeitzReduction.SymplecticPilot.q2Block 0 K ({3} : Finset (Fin 4)))
        (twoLinIota 0 hK)) :
    TwoOverlapInvAt .linear6 := by
  refine twoOverlapInvAt_of_modelInput ?_
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨Φ, hΦ⟩ := exists_twoLinParam hK hw e hXJ hcyc hX₀ (Or.inl ⟨rfl, rfl⟩) hk
  exact ⟨_, inferInstance, inferInstance, twoLinIota 0 hK, Φ, hΦ, hV K hK⟩

end CFSG.SeitzReduction.F4Pilot
