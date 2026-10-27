module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitE7
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit {t : G} {f : ℕ}
    (hw : E8Work L K t f) (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)}
    (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) = D := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E8 hAJ hA hcyc
  have hDperf : ⁅D, D⁆ = D := by
    have hCp : ⁅e7Levi K, e7Levi K⁆ = e7Levi K := isPerfect_iff.mp isQuasisimple_e7Levi.1
    rw [hDe, ← map_commutator, ← map_commutator, hCp]
  have hDH : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact F4Pilot.map_map_symm_le_centralizer e hAD
  have hDE : D ≤ centralizerPerfectCore X := F4Pilot.le_centralizerPerfectCore hDperf hDH
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.2⟩⟩
  have hPL : P ≤ L := std_perfect_le hw.standard hOut htC hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans (F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  rw [hX, inf_centralizer_nonsplit_E8 e hAJ hA hcyc, ← hX, ← hDe] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDH
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e (F4Pilot.le_centralizer_self_of_isCyclic hcyc)
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

theorem nonempty_adjointGroupE7_mulEquiv_centralizerPerfectCore_nonsplit_two {t : G}
    (hw : E8Work L K t 1) (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)}
    (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hF : NeighbourOvergroupE7Field
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ 2 ∧
      Nonempty (adjointGroup .E7 F ≃* centralizerPerfectCore X) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq e
  have hset := hw.seitz
  have hA3 : Nat.card A = 3 := by rw [hA, hK2]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hA3
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, -, hlt, hsK, hsN, hov⟩ := hF
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E8_nonsplit hset.standardSetting.standard htC
    hw.orderOf_eq hKt hw.card_eq e hAJ hA hcyc hX htX hDe
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
    exists_mulEquiv_adjointQuotient_of_lieModel (.inr (.inr (.inl rfl))) hov.2.2.1
  have : CharP F 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hF
  have hF2 : Nat.card F = 2 ^ 2 := by rw [hF]
  have hF4 : 4 ≤ Nat.card F := by rw [hF2]; norm_num
  set ε : Kb ⧸ center Kb ≃* adjointGroup .E7 F :=
    eF.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E7 F) with hε
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  set η : Kb →* adjointGroup .E7 F := ε.toMonoidHom.comp (QuotientGroup.mk' (center Kb)) with hη
  have hηs : Function.Surjective η := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Kb := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hηinj := SeitzQ2.injective_of_surjective_of_le_center_E7_of_four_le hF4 η hηs hηker.le
  set eK : Kb ≃* adjointGroup .E7 F := MulEquiv.ofBijective η ⟨hηinj, hηs⟩ with heK
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eK).2.mpr
      ⟨⟨2, (exceptional_E_pinned_model_Schreier F).2.1⟩⟩
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hOutL : IsPGroup 2 (Outer L) := by
    have : Subsingleton (Outer L) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H α =>
        induction b using QuotientGroup.induction_on with
        | H β =>
          rw [QuotientGroup.eq]
          exact forall_mem_range_conj_of_mulEquiv_E8_two hK2 e _
    intro g
    exact ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim _ _⟩
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hset.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC hw.orderOf_eq
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, hDe]
    exact (inSubgroup_layer_inf_centralizer_nonsplit_E8 e hAJ hA hcyc).symm
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe]
    exact (inf_centralizer_nonsplit_E8 e hAJ hA hcyc).le
  obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E8 hAJ hA hcyc
  have hDH : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact F4Pilot.map_map_symm_le_centralizer e hAD
  have hDq : CFSG.IsQuasisimple D := by
    rw [hDe]
    exact isQuasisimple_map_e7Levi e
  let eD : e7Levi K ≃* D :=
    (((e7Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((e7Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective)).trans (MulEquiv.subgroupCongr hDe.symm)
  have hZD : center D = ⊥ := F4Pilot.center_eq_bot_congr eD center_e7Levi_eq_bot
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    SeitzQ2.inf_centralizer_le_of_le_sup hLX (le_centralizer_iff.1 hDH) hZD
  have hB : HasBLift Kb := SeitzQ2.hasBLift_of_isPGroup_outer hOutL htC hw.orderOf_eq htL hCN
    hKt htX hlayer hDq hXD (isPerfect_iff.mp hKbP) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, -⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  set η' : centralizerPerfectCore X →* adjointGroup .E7 F := eK.toMonoidHom.comp qh with hη'
  have hη's : Function.Surjective η' := eK.surjective.comp hqs
  have hη'ker : η'.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := SeitzQ2.injective_of_surjective_of_le_center_E7_of_four_le hF4 η' hη's
    (hη'ker ▸ hqker)
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF2,
    ⟨(MulEquiv.ofBijective η' ⟨hinj, hη's⟩).symm⟩⟩

theorem exists_normalized_nonsplit_two {t : G} (hw : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)}
    (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hF : NeighbourOvergroupE7Field
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 1)
    {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂)
    {σ : K₂ ≃+* K₂} (hσ : orderOf σ = 2) (hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι) :
    ∃ Φ : E8Neighbour.high.levi K₂ ≃* centralizerPerfectCore X,
      ∀ x : E8Neighbour.high.levi K,
        ((Φ (leviBaseChange ι .high x) : centralizerPerfectCore X) : G) =
          ((e.symm x : L) : G) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hA3 : Nat.card A = 3 := by rw [hA, hK2]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hA3
  obtain ⟨F, _, _, _, hF4, ⟨ψF⟩⟩ :=
    nonempty_adjointGroupE7_mulEquiv_centralizerPerfectCore_nonsplit_two hw e hAJ hA hX htX hDe hF
  have hfixD := perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit hw e hAJ hA hcyc hX hDe
  set E : Subgroup G := centralizerPerfectCore X with hEdef
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card K₂ = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₂, hF4]
  set ψ₀ : e7Levi K₂ ≃* E := (e7LeviEquiv K₂).trans
    ((adjointGroupE7RingEquiv (FiniteField.ringEquivOfCardEq hc)).trans ψF) with hψ₀
  have hN : t ∈ normalizer (E : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
      (centralizer_le_normalizer X htX)
  have ht : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hθθ : E.normalizerMonoidHom ⟨t, hN⟩ * E.normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (E : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext ht, map_one]
  have hDE : D ≤ E := by
    rw [← hfixD]
    exact (perfectCore_le _).trans inf_le_left
  set ε₀ : e7Levi K →* G := L.subtype.comp (e.symm.toMonoidHom.comp (e7Levi K).subtype)
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ E := fun g => hDE (by rw [hDe]; exact ⟨_, ⟨g, g.2, rfl⟩, rfl⟩)
  set ε : e7Levi K →* E := ε₀.codRestrict _ hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) h
  have hεrange : ε.range.map E.subtype = D := by
    rw [hDe]
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact ⟨_, ⟨g', g'.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨ε ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      (E.normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective E.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, F4Pilot.map_eqLocus_normalizerMonoidHom hN, hfixD,
      hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_e7LeviBaseChange_eq ι hσ hfix ψ₀ hθθ ε hεinj hεr
  refine ⟨(MulEquiv.subgroupCongr (E8Neighbour.levi_high K₂)).trans ψ', fun x => ?_⟩
  have hx : (x : adjointGroup .E8 K) ∈ e7Levi K := (E8Neighbour.levi_high K) ▸ x.2
  have h1 : MulEquiv.subgroupCongr (E8Neighbour.levi_high K₂) (leviBaseChange ι .high x) =
      e7LeviBaseChange ι ⟨x, hx⟩ :=
    Subtype.ext (Subtype.ext (by rw [coe_e7LeviBaseChange]; rfl))
  rw [MulEquiv.trans_apply, h1, hψ']
  rfl

end CFSG.SeitzReduction.E8Pilot
