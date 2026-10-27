module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore F4Work HasBLift)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_E6 {t : G} {f : ℕ}
    (hw : F4Work L K t f) (e : L ≃* adjointGroup .E6 K) {A : Subgroup (adjointGroup .E6 K)}
    (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) = D := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA hcyc
  have hDperf : ⁅D, D⁆ = D := by
    have hCp : ⁅a5Levi K, a5Levi K⁆ = a5Levi K := isPerfect_iff.mp isQuasisimple_a5Levi.1
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
  have hPL : P ≤ L := std_perfect_le hw.standard (isSolvable_outer_of_mulEquiv_E6 e) htC
    hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans (F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hLX : L ⊓ centralizer (X : Set G) = X ⊔ D := by
    rw [hX, hDe, F4Pilot.inf_centralizer_map_symm e A, hcent, Subgroup.map_sup, Subgroup.map_sup]
  have hXD : X ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDH
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e (F4Pilot.le_centralizer_self_of_isCyclic hcyc)
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅X ⊔ D, X ⊔ D⁆ := by
      rw [← hLX]
      exact commutator_mono (le_inf hPL hPX) (le_inf hPL hPX)
    _ ≤ D := commutator_sup_le_of_le_centralizer hXX hXD

theorem exists_surjective_centralizerPerfectCore_nonsplit_E6_two {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .E6 K) {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K)
    (hA : Nat.card A = 3) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = rootLeviG e)
    (hk : NeighbourOvergroupSLFieldKind
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 1)
    (K₂ : Type) [Field K₂] [Finite K₂] (hK₂ : Nat.card K₂ = 4) :
    ∃ p : centralizerPerfectCore X →* a5Levi K₂, Function.Surjective p ∧
      p.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card p.ker) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have : CharP K₂ 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hK₂]; norm_num)
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hA' : Nat.card A = Nat.card K + 1 := by rw [hA, hK2]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hA
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, -, hlt, hsK, hsN, hov, -, hmodel, -⟩ := hk
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (by
      rw [hDe] at hd
      exact map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E6_nonsplit_of_one_le hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq le_rfl hw.card_eq e hAJ hA' hcyc hX htX hDe
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := LinearPilot.exists_projectiveSL_equiv_of_lieModel_PSL hmodel
  have hOut : Group.IsSolvable (Outer Kb) :=
    LinearPilot.isSolvable_outer_of_mulEquiv (by norm_num) eF
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hB : HasBLift Kb := hasBLift_nonsplit_E6_two hw.standard hK2 e hw.orderOf_eq hw.inf_eq hAJ
    hA hX htX (isPerfect_iff.mp hKb.1.1) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ H := F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : qh.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore H := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  set φ : qh.ker →* oddCore H :=
    ((Subgroup.inclusion hle).comp qh.ker.subtype).codRestrict (oddCore H) hmemO with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : oddCore H => ((z : H) : G)) hab))
  have hkodd : Odd (Nat.card qh.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card F = Fintype.card K₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK₂]
    norm_num
  set η : Kb ≃* a5Levi K₂ := (eF.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
    (FiniteField.ringEquivOfCardEq hc))).trans (a5LeviProjEquiv K₂) with hη
  refine ⟨η.toMonoidHom.comp qh, η.surjective.comp hqs, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ qh.ker := by
      rw [MonoidHom.mem_ker] at hz ⊢
      exact η.injective (by rw [map_one]; exact hz)
    exact hqker hz'
  · have hker : (η.toMonoidHom.comp qh).ker = qh.ker := by
      ext z
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    rw [hker]
    exact hkodd

theorem exists_normalized_cover_nonsplit_E6_two {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    {σ : K₂ ≃+* K₂} (hq : F4Pilot.QuadraticFrobenius K₂ σ 1) {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {t : G} (hw : F4Work L (fixSubfield σ) t 1)
    {A : Subgroup (adjointGroup .E6 (fixSubfield σ))} (hAJ : A ≤ posJ (fixSubfield σ))
    (hA : Nat.card A = 3) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = rootLeviG e)
    (hk : NeighbourOvergroupSLFieldKind
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 1) :
    ∃ p : centralizerPerfectCore X →* E6Neighbour.high.levi K₂, Function.Surjective p ∧
      p.ker = center (centralizerPerfectCore X) ∧ Odd (Nat.card p.ker) ∧
      ∀ x : E6Neighbour.high.levi (fixSubfield σ), ∃ y : centralizerPerfectCore X,
        (y : G) = ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) ∧
          p y = leviInclusion σ .high x := by
  have hK2 : Nat.card (fixSubfield σ) = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hK₂ : Nat.card K₂ = 4 := by rw [hq.card_eq]; norm_num
  have hA' : Nat.card A = Nat.card (fixSubfield σ) + 1 := by rw [hA, hK2]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hA
  obtain ⟨p₀, hp₀s, hp₀ker, hp₀odd⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_E6_two hw e hAJ hA hX htX hDe hk K₂ hK₂
  set φ : a5Levi K₂ ≃* E6Neighbour.high.levi K₂ :=
    MulEquiv.subgroupCongr (E6Neighbour.levi_high K₂).symm with hφ
  set p : centralizerPerfectCore X →* E6Neighbour.high.levi K₂ := φ.toMonoidHom.comp p₀ with hp
  have hpker : p.ker = p₀.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
      (centralizer_le_normalizer X htX)
  have hfix : perfectCore (centralizerPerfectCore X ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E6Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E6 (fixSubfield σ)).subtype) := by
    rw [modelToG_map_subtype_levi_high]
    exact perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_E6 hw e hAJ hA' hcyc hX rfl
  exact exists_normalized_of_surjective hq.orderOf_eq .high hN hw.orderOf_eq hfix p
    (φ.surjective.comp hp₀s) (hpker ▸ hp₀ker) (hpker ▸ hp₀odd)

end CFSG.SeitzReduction.E6Pilot
