module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightPairJShape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive
import CFSG.Quasithin.SteinbergCDBestOffenderRestriction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.McLaughlin

theorem nonempty_quotient_center_mulEquiv {Q J : Type} [Group Q] [Group J] [IsSimpleGroup J]
    (hQ : CFSG.Open.IsQuasisimple Q) (hJ : ∃ a b : J, a * b ≠ b * a) (f : Q →* J)
    (hf : Function.Surjective f) : Nonempty (Q ⧸ Subgroup.center Q ≃* J) := by
  have hZJ : Subgroup.center J = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian inferInstance hJ
  have hZ : ∀ z ∈ Subgroup.center Q, f z = 1 := by
    intro z hz
    have : f z ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨q, rfl⟩ := hf y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz q]
    rwa [hZJ, Subgroup.mem_bot] at this
  have hK : f.ker ≤ Subgroup.center Q := by
    intro x hx
    haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
    have hN : (f.ker.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
      (MonoidHom.normal_ker f).map _ (QuotientGroup.mk'_surjective _)
    rcases Subgroup.Normal.eq_bot_or_eq_top (f.ker.map (QuotientGroup.mk' (Subgroup.center Q)))
      with h | h
    · have hx' : QuotientGroup.mk' (Subgroup.center Q) x ∈
          f.ker.map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨x, hx, rfl⟩
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    · exfalso
      have hf1 : ∀ q : Q, f q = 1 := by
        intro q
        have hq : QuotientGroup.mk' (Subgroup.center Q) q ∈
            f.ker.map (QuotientGroup.mk' (Subgroup.center Q)) := by
          rw [h]
          exact Subgroup.mem_top _
        obtain ⟨k, hk, hkq⟩ := hq
        have hz : k⁻¹ * q ∈ Subgroup.center Q := by
          rw [← QuotientGroup.eq]
          exact hkq
        have hq' : q = k * (k⁻¹ * q) := by group
        rw [hq', map_mul, MonoidHom.mem_ker.mp hk, one_mul]
        exact hZ _ hz
      obtain ⟨a, b, hab⟩ := hJ
      obtain ⟨qa, rfl⟩ := hf a
      obtain ⟨qb, rfl⟩ := hf b
      rw [hf1 qa, hf1 qb] at hab
      exact hab (by simp)
  have hker : Subgroup.center Q = f.ker :=
    le_antisymm (fun z hz => MonoidHom.mem_ker.mpr (hZ z hz)) hK
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem normal_le_ker_of_isPGroup_two {X : Type*} {J : Type} [Group X] [Group J] [Finite J]
    [IsSimpleGroup J] (hJ : ∃ a b : J, a * b ≠ b * a) (g : X →* J) (hg : Function.Surjective g)
    {N : Subgroup X} (hN : N.Normal) (hp : IsPGroup 2 N) : N ≤ g.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (N.map g).Normal := hN.map g hg
  have hNp : IsPGroup 2 (N.map g) := hp.map g
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map g) with h | h
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hx' : g x ∈ N.map g := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at hx'
  · exfalso
    have hJ2 : IsPGroup 2 J := by
      have h1 := hNp
      rw [h] at h1
      exact IsPGroup.of_equiv h1 Subgroup.topEquiv
    have hZ := hJ2.center_nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ
      (center_eq_bot_of_isSimpleGroup_of_nonabelian inferInstance hJ)

section Bar

variable {G : Type} [Group G] [Finite G]

theorem nonempty_barM_quotient_center_mulEquiv {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {J : Type} [Group J] [IsSimpleGroup J] (hJ : ∃ a b : J, a * b ≠ b * a) (g : ↥L →* J)
    (hg : Function.Surjective g) :
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* J) := by
  haveI : Finite J := Finite.of_surjective g hg
  have hp : IsPGroup 2 (WeakBlockModuleData.barMHom hL.le).ker := by
    intro x
    have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : L), hL.le (x : L).2⟩ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact this
    have hmem : (⟨(x : L), hL.le (x : L).2⟩ : ↥M) ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : CFSG.pCore 2 ↥M => ((z : ↥M) : G)) hk
    simpa using this
  have hker : (WeakBlockModuleData.barMHom hL.le).ker ≤ g.ker :=
    normal_le_ker_of_isPGroup_two hJ g hg (MonoidHom.normal_ker _) hp
  let gb : ↥(barM M L) →* J :=
    (WeakBlockModuleData.barMHom hL.le).liftOfSurjective
      (WeakBlockModuleData.barMHom_surjective hL.le) ⟨g, hker⟩
  have hgb : Function.Surjective gb := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨WeakBlockModuleData.barMHom hL.le x,
      (WeakBlockModuleData.barMHom hL.le).liftOfRightInverse_comp_apply _ _ ⟨g, hker⟩ x⟩
  exact nonempty_quotient_center_mulEquiv hL.component.2.2 hJ gb hgb

end Bar

theorem false_of_central_quotient_alternating {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q)
    (hA : ∀ N : ℕ, 6 ≤ N → IsEmpty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin N)))
    {N : ℕ} (hN : N ≠ 5) (φ : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin N)) : False := by
  haveI : Group.IsPerfect Q := ⟨hq.1⟩
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  have h5 := BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup φ
  exact (hA N (by omega)).false φ

theorem false_of_mulEquiv_alternating {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q)
    (hA : ∀ N : ℕ, 6 ≤ N → IsEmpty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin N)))
    {N : ℕ} (hN : N ≠ 5) (φ : Q ≃* alternatingGroup (Fin N)) : False := by
  haveI : Group.IsPerfect Q := ⟨hq.1⟩
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h5 := BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup φ
  have hnab : ∃ a b : Q, a * b ≠ b * a := by
    have h := Group.IsPerfect.not_isMulCommutative Q
    simpa only [isMulCommutative_iff, not_forall] using h
  have hZ := center_eq_bot_of_mulEquiv_alternating hnab φ
  exact (hA N (by omega)).false
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ)

section U42

variable {G : Type} [Group G] [Finite G]

theorem false_of_u42Facts {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hNL : ¬ (L.subgroupOf M).Normal) (hrk : CFSG.Open.pRank 3 M ≤ 3)
    (hU : U42Facts (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) : False := by
  obtain ⟨hE9, hZ⟩ := hU
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
    refine CFSG.Quasithin.SteinbergCD.odd_card_center_of_pCore_eq_bot ?_
    have h := TenThreeThree.pCoreOf_barM_eq_bot hL
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (barM M L).subtype_injective).mp h
  have hZbot : Subgroup.center ↥(barM M L) = ⊥ := hZ _ hq hodd ⟨MulEquiv.refl _⟩
  obtain ⟨E, hE, hEc⟩ := BlockCyc.hasE9_of_surjective
    (φ := QuotientGroup.mk' (Subgroup.center ↥(barM M L))) (QuotientGroup.mk'_surjective _) hE9
  obtain ⟨E₀, hE₀L, hE₀ab, hE₀c⟩ : ∃ E₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E₀ ≤ barM M L ∧
      IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 := by
    refine ⟨E.map (barM M L).subtype, Subgroup.map_subtype_le E,
      BlockCyc.isElemAbelian_map _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective (barM M L).subtype_injective, hEc]
  obtain ⟨m', hm', hne⟩ : ∃ m' ∈ M, L.map (MulAut.conj m').toMonoidHom ≠ L := by
    by_contra hcon
    push Not at hcon
    apply hNL
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hcon g g.2
    rw [← h]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m', hm'⟩)
  have hE₁L : E₀.map c.toMonoidHom ≤ barM M (L.map (MulAut.conj m').toMonoidHom) := by
    rw [barM_map_conj hm']
    exact Subgroup.map_mono hE₀L
  obtain ⟨E₁, hE₁L, hE₁ab, hE₁c⟩ : ∃ E₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E₁ ≤ barM M (L.map (MulAut.conj m').toMonoidHom) ∧ IsElemAbelian 3 E₁ ∧
        Nat.card E₁ = 3 ^ 2 := by
    refine ⟨E₀.map c.toMonoidHom, hE₁L, BlockCyc.isElemAbelian_map _ hE₀ab, ?_⟩
    rw [Subgroup.card_map_of_injective c.injective, hE₀c]
  have hE₁cent : E₁ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hE₁L.trans (TenTenClaim.barM_le_centralizer hL (hL.map_conj hm') (Ne.symm hne))
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hE₁cent hb) a (hE₀L ha)
  have hinf : E₀ ⊓ E₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, hx₁⟩
    rw [Subgroup.mem_bot]
    have hxL : x ∈ barM M L := hE₀L hx₀
    have hxc : (⟨x, hxL⟩ : ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hE₁cent hx₁) y y.2)
    rw [hZbot, Subgroup.mem_bot] at hxc
    exact congrArg Subtype.val hxc
  obtain ⟨hab, hcard⟩ := TenTenClaim.elemAbelian_sup_card hE₀ab hE₁ab hcomm hinf
  obtain ⟨E', hE'M, hE', hE'c⟩ := TenTenClaim.exists_elemAbelian_lift (M := M) (W := M) le_rfl
    hab (by rw [TenTenClaim.barM_self]; exact le_top)
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE'M hE' (k := 4)
      (by rw [hE'c, hcard, hE₀c, hE₁c]; norm_num)
  omega

end U42

section Excl

variable {G : Type} [Group G] [Finite G]

theorem false_of_pairJ (hJ : KFactThreeFourPairJShape) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (h984 : AGL81NineEightFour G)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hNL : ¬ (L.subgroupOf M).Normal) {m : G} {q : ℕ}
    {iK iJ : TauCeti.CFSGIndex} (hpair : TenThirteen.IsThreeFourPair q iK iJ)
    (f : ↥(L.map (MulAut.conj m).toMonoidHom) →* iJ.Group) (hf : Function.Surjective f) :
    False := by
  have hT := hd.toTwoLocalPhaseThree' hS h984
  have hK : CFSG.Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hLc.component.2.2
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hrk : CFSG.Open.pRank 3 M ≤ 3 := by
    have h := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M he.maxTwoLocal_M.1
    rw [hS.rank] at h
    exact h
  haveI : Finite iJ.Group := Finite.of_surjective f hf
  obtain ⟨⟨hJsimp, hJnab⟩, -⟩ := hJ q iK iJ hpair iJ.Group ⟨MulEquiv.refl _⟩
  haveI := hJsimp
  let e : ↥L ≃* ↥(L.map (MulAut.conj m).toMonoidHom) :=
    L.equivMapOfInjective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective
  obtain ⟨eQ⟩ := nonempty_barM_quotient_center_mulEquiv hLc hJnab (f.comp e.toMonoidHom)
    (hf.comp e.surjective)
  obtain ⟨-, hJalt, hJorth, hJcl⟩ := hJ q iK iJ hpair
    (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ⟨eQ⟩
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    haveI := hperf
    haveI : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2
    haveI : Nontrivial ↥(barM M L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
    have h := Group.IsPerfect.not_isMulCommutative ↥(barM M L)
    simpa only [isMulCommutative_iff, not_forall] using h
  have e₀ : Subgroup.center ↥(barM M L) = ⊥ →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* ↥(barM M L)) := fun hZ =>
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩
  have hSyl : ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L := hT.not_isSylowTwoOf_inf hK h85 hD2 hL
  have hX : ¬ NineThreeOne L := (hT.nineThree_not_one hK h85 hD2 hL).1
  have hU : U42Facts (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) → False :=
    false_of_u42Facts hLc hNL hrk
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    exact hX h1
  ·
    obtain ⟨hcl, T, J', hT', hle, hne, htop, -⟩ :=
      BlockCyc.nineThreeTwo_parabolic hT.asc81bHyp hL hSyl h2
    exact hU (hJcl hcl T J' hT' hle hne htop)
  ·
    obtain ⟨e⟩ := e₀ (center_eq_bot_of_isOrthogonalTwo hperf hnab h3.2.1)
    have hO := IsOrthogonalTwo.of_mulEquiv e h3.2.1
    rcases hJorth hO with he5 | hu
    · obtain ⟨e5⟩ := he5
      exact hX (WeakBlockModuleData.kFactNineThreeThreeFive_proved G M (pCoreOf 2 H) L hL h3
        ⟨e.symm.trans e5⟩)
    · exact hU hu
  ·
    obtain ⟨φ⟩ := h4.2.2.1
    exact (hJalt 6 le_rfl).false φ
  ·
    obtain ⟨φ⟩ := h5.2.1
    exact false_of_mulEquiv_alternating hq hJalt (by norm_num) φ
  ·
    obtain ⟨-, n, ⟨φ⟩, -⟩ := h6
    exact false_of_central_quotient_alternating hq hJalt (by omega) φ
  ·
    obtain ⟨-, n, ⟨φ⟩, -⟩ := h7
    exact false_of_mulEquiv_alternating hq hJalt (by omega) φ
  ·
    obtain ⟨-, N, r, ⟨k, hk⟩, -, -, -, -, ⟨φ⟩, -⟩ := h8
    exact false_of_mulEquiv_alternating hq hJalt (by omega) φ

end Excl

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
