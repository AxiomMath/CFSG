module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporCardRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgISimple
public import CFSG.RankThree.PartTwo.Sec12.Hering129SPSpor
public import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuKFact

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge sporOrd SporadicOrdersTable)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor (CardRow)

theorem a6Row_of_cardRow (hB : LieOrderBridge) {s : TauCeti.SporadicName} (h : CardRow 360 s) :
    A6Row s := fun S _ _ e β hβ hβ1 J hJ hT _ => h S e β hβ hβ1 J hJ (ClsRed.card_a6 hB hT)


theorem two_dvd_sporOrd
    (s : TauCeti.SporadicName) : 2 ∣ sporOrd s ∧ 2 < sporOrd s := by
  cases s <;> decide +kernel

theorem a6Row_of_elem
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {s : TauCeti.SporadicName} (hsM : s ≠ .M)
    (h : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
      ∀ x : S, orderOf x = 3 → A6Free x) : A6Row s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hT hZ
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group :=
    CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.sporadic_isSimple_of_ne_M s hsM
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr e).2 inferInstance
  have hcS : Nat.card S = sporOrd s := (Nat.card_congr e.toEquiv).trans (hOrd s)
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    refine CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ?_
    rw [hcS]
    intro hp
    obtain ⟨h2, h2lt⟩ := two_dvd_sporOrd s
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have heq : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set S) := by
    ext g
    rw [CFSG.LocalAnalysis.GLTheoremA.AltDown.mem_fixSubgroup_conj,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      first
        | exact h.eq
        | exact h.eq.symm
    · intro h
      first
        | exact h
        | exact h.symm
  rw [heq] at hJ
  exact h S ⟨e⟩ x hxo J hJ (ClsRed.card_a6 hB hT) hZ

theorem a6Row_of_not_dvd
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {s : TauCeti.SporadicName} (hsM : s ≠ .M) (hd : ¬ 1080 ∣ sporOrd s) : A6Row s := by
  refine a6Row_of_elem hB hOrd hOut hsM fun S _ _ ⟨e⟩ x hx => a6Free_of_not_dvd hx fun h => hd ?_
  rw [← (Nat.card_congr e.toEquiv).trans (hOrd s)]
  exact h.trans (Subgroup.card_subgroup_dvd_card _)

theorem a6Row_small
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    A6Row .M11 ∧ A6Row .J1 ∧ A6Row .M22 ∧ A6Row .M23 ∧ A6Row .HS :=
  ⟨a6Row_of_not_dvd hB hOrd hOut (by decide) (by decide +kernel),
    a6Row_of_not_dvd hB hOrd hOut (by decide) (by decide +kernel),
    a6Row_of_not_dvd hB hOrd hOut (by decide) (by decide +kernel),
    a6Row_of_not_dvd hB hOrd hOut (by decide) (by decide +kernel),
    a6Row_of_not_dvd hB hOrd hOut (by decide) (by decide +kernel)⟩

theorem a6Row_cardRows
    (hB : LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    A6Row .McL ∧ A6Row .Co3 ∧ A6Row .Co2 ∧ A6Row .Fi22 ∧ A6Row .Ly ∧ A6Row .Th ∧
      A6Row .Fi23 ∧ A6Row .Fi24Prime :=
  ⟨a6Row_of_cardRow hB (K14Spor.cardRow_mcl' hOut hbr 360),
    a6Row_of_cardRow hB (K14Spor.cardRow_co3' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_co2' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_fi22' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_ly' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_th' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_fi23' hOut hbr (by norm_num)),
    a6Row_of_cardRow hB (K14Spor.cardRow_fi24' hbr hOut (by norm_num) (by norm_num))⟩

theorem a6Row_HN
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) : A6Row .HN :=
  a6Row_of_elem hB hOrd hOut (by decide) fun S _ _ ⟨e⟩ x hx =>
    a6Free_of_noCardComp (H1431c.noCardComp_HN e x (by rw [← hx]; exact pow_orderOf_eq_one x))

theorem a6Row_Co1
    (hB : LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : A6Row .Co1 := by
  refine a6Row_of_cardRow hB ?_
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hbr
  have hC := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_centShapeRk_three_good
    (Good := fun T _ => Nat.card T ≠ 360)
    (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun T _ e hc => by
      have h1 : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans
        CFSG.LieType.Multipliers.U43.card_X₀
      rw [h1] at hc
      norm_num at hc)
    (by
      show Nat.card ↥(alternatingGroup (Fin 9)) ≠ 360
      rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.card_alt_nine]
      norm_num)
    (fun _ _ hc _ => by
      show _ ≠ 360
      rw [hc]
      norm_num)
    (hbr .Suz)
  exact @K14Spor.cardRow_of_centShapeRk 360 .Co1 _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)

theorem a6Free_of_quasisimple
    {Q : Type} [Group Q] [Finite Q] {k : Q} (hk : orderOf k = 3)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set Q))) : A6Free k := by
  intro I hI _ hZ
  have hI' := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.glaPComponent_eq_of_quasisimple
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hq) hI
  apply not_mem_of_center hk hI hZ
  rw [hI']
  exact Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem a6Free_of_threeCases
    {Q : Type} [Group Q] [Finite Q] {k : Q} (hk : orderOf k = 3)
    (h : (CFSG.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set Q)) ∧
        Nat.card (Subgroup.center ↥(Subgroup.centralizer ({k} : Set Q))) = 3) ∨
      Nat.card ↥(Subgroup.centralizer ({k} : Set Q)) = 504) : A6Free k := by
  rcases h with ⟨hq, -⟩ | h
  · exact a6Free_of_quasisimple hk hq
  · exact a6Free_of_not_dvd hk (by rw [h]; norm_num)

theorem a6Row_M24
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) : A6Row .M24 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  refine a6Row_of_elem hB hOrd hOut (by decide) fun S _ _ ⟨e⟩ x hx => ?_
  haveI : Finite CFSG.Blueprint.NativeSporadic.M24 := Finite.of_equiv _ (e.trans b.symm).toEquiv
  let φ : S ≃* CFSG.Blueprint.NativeSporadic.M24 := e.trans b.symm
  refine a6Free_of_mulEquiv_apply φ (a6Free_of_threeCases (by rwa [MulEquiv.orderOf_eq]) ?_)
  exact CFSG.RankThree.PartTwo.Sec12.Hering129SP.threeCases_M24 (φ x) (by rwa [MulEquiv.orderOf_eq])

theorem a6Row_He
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) : A6Row .He := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  refine a6Row_of_elem hB hOrd hOut (by decide) fun S _ _ ⟨e⟩ x hx => ?_
  exact a6Free_of_threeCases hx
    (CFSG.RankThree.PartTwo.Sec12.Hering129SP.threeCases_He (e.trans b.symm) x hx)

set_option maxRecDepth 100000 in
theorem a6Row_J4
    (hB : LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : A6Row .J4 := by
  obtain ⟨hfin, hJs, hnc, ⟨b⟩⟩ := CFSG.Sporadic.J4.j4_model hbr
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  refine @a6Row_of_model hB .J4 ↥CFSG.Sporadic.J4.J _ hfin hJs hOut b hnc fun k hk => ?_
  refine a6Free_of_noCardComp fun I hI hc => ?_
  obtain ⟨g⟩ := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.pSimple_of_glaPComponent_three
    Nat.prime_three hk hI
  rw [Nat.card_congr g.toEquiv, hM] at hc
  norm_num at hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem a6Row_M12
    (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) : A6Row .M12 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  refine a6Row_of_elem hB hOrd hOut (by decide) fun S _ _ ⟨e⟩ x hx => ?_
  haveI : Finite ↥CFSG.Blueprint.NativeSporadic.M12 := Finite.of_equiv _ (e.trans b.symm).toEquiv
  let φ : S ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e.trans b.symm
  have hx' : orderOf (φ x) = 3 := by rwa [MulEquiv.orderOf_eq]
  refine a6Free_of_mulEquiv_apply φ (a6Free_of_not_dvd hx' fun hd => ?_)
  have hx3 : orderOf ((φ x : ↥CFSG.Blueprint.NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 3 := by
    rw [Subgroup.orderOf_coe]; exact hx'
  have hlt : Nat.card ↥(Subgroup.centralizer ({((φ x : ↥CFSG.Blueprint.NativeSporadic.M12) :
        Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12))) ⊓ CFSG.Blueprint.NativeSporadic.M12) < 60 :=
    KDSpor.check_card_lt m12S3Data rep_m12A rep_m12B
      Certificates.certificate13511.2.1 (by decide) _ (φ x).2 hx3
  have hmapc := map_centralizer_subtype CFSG.Blueprint.NativeSporadic.M12 (φ x)
  have hc : Nat.card (Subgroup.centralizer ({φ x} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) =
      Nat.card ↥(Subgroup.centralizer ({((φ x : ↥CFSG.Blueprint.NativeSporadic.M12) :
        Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12))) ⊓ CFSG.Blueprint.NativeSporadic.M12) := by
    rw [← hmapc, Subgroup.card_map_of_injective CFSG.Blueprint.NativeSporadic.M12.subtype_injective]
  rw [hc] at hd
  have := Nat.le_of_dvd Nat.card_pos hd
  omega

theorem a6Free_of_index_two
    {Q : Type} [Group Q] [Finite Q] {k : Q} (hk : orderOf k = 3)
    {K : Subgroup Q} (hKC : K ≤ Subgroup.centralizer ({k} : Set Q))
    (hidx : (K.subgroupOf (Subgroup.centralizer ({k} : Set Q))).index = 2)
    (hq : CFSG.IsQuasisimple ↥K) (hkK : k ∈ K) : A6Free k := by
  intro I hI _ hZ
  set C := Subgroup.centralizer ({k} : Set Q) with hCdef
  have hIC : I ≤ C := hI.1
  have hIK : I ≤ K := by
    rw [← CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hI]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    set H := K.subgroupOf C
    have hmem : ∀ c d : C, c * d ∈ H ↔ (c ∈ H ↔ d ∈ H) := fun c d =>
      Subgroup.mul_mem_iff_of_index_two hidx
    have hinv : ∀ c : C, c⁻¹ ∈ H ↔ c ∈ H := fun c => H.inv_mem_iff
    set a' : C := ⟨a, hIC ha⟩
    set b' : C := ⟨b, hIC hb⟩
    have h : a' * b' * a'⁻¹ * b'⁻¹ ∈ H := by
      rw [hmem, hmem, hmem, hinv, hinv]
      tauto
    have := Subgroup.mem_subgroupOf.1 h
    simpa [a', b', commutatorElement_def] using this
  have hI' := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le Nat.prime_three hI hIK hKC
  have hIeq := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.glaPComponent_eq_of_quasisimple
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hq) hI'
  exact not_mem_of_center hk hI hZ (hIeq ▸ hkK)

open CFSG.Sporadic.RuSchreier CFSG.AGLEmbeddingD2.Wilson.Census219
  CFSG.AGLEmbeddingD2.Wilson.ThetaSpor in
theorem a6Row_Ru
    (hB : LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : A6Row .Ru := by
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := CFSG.Sporadic.RuSchreier.ruEquivP
  haveI hfin : Finite ↥ruP := Finite.of_equiv _ e.toEquiv
  haveI hs : IsSimpleGroup ↥ruP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e.symm
  have hc : Nat.card ↥ruP = 145926144000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hnc : ∃ a c : ↥ruP, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num)
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group := e.symm.trans (hbr .Ru).some
  refine a6Row_of_model hB hOut b hnc fun x hx => ?_
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
  obtain ⟨g, hg⟩ := exists_conj_ruXp x hx3 hx1
  have hw : orderOf ruXp = 3 := by
    rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hfree : A6Free ruXp := by
    refine a6Free_of_index_two hw ruKY_le ruKY_index ruKY_quasisimple ?_
    exact Subgroup.mem_subgroupOf.2 ruTc_spec.1
  have h := a6Free_conj hfree g⁻¹
  rwa [← hg, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

theorem factorization_three_27
    {m : ℕ} (hm : ¬ 3 ∣ m) (hm0 : m ≠ 0) : (3 ^ 3 * m).factorization 3 = 3 := by
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, Nat.Prime.factorization_pow
    Nat.prime_three, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm]

theorem exists_sylow_of_factorization
    {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 3)
    (hv : (Nat.card G).factorization 3 =
      (Nat.card (Subgroup.centralizer ({x} : Set G))).factorization 3) :
    ∃ P' : Sylow 3 G, x ∈ (P' : Subgroup G) ∧
      (P' : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨P0⟩ := (inferInstance : Nonempty (Sylow 3 ↥C))
  set H := (P0 : Subgroup ↥C).map C.subtype with hH
  have hHcard : Nat.card H = 3 ^ (Nat.card G).factorization 3 := by
    rw [hH, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hv]
  refine ⟨Sylow.ofCard H hHcard, ?_, Subgroup.map_subtype_le _⟩
  show x ∈ H
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set x' : ↥C := ⟨x, hxC⟩
  haveI hN : (Subgroup.zpowers x').Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcomm : g * x' = x' * g := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 g.2
      simp only [Subgroup.coe_mul, x']
      first
        | exact this.symm
        | exact this
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * x' ^ k * g⁻¹ = x' ^ k := by
      rw [show g * x' ^ k * g⁻¹ = (g * x' * g⁻¹) ^ k by
        rw [← conj_zpow], show g * x' * g⁻¹ = x' by rw [hcomm]; group]
    rw [this]
    exact Subgroup.zpow_mem_zpowers x' k
  have hp : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
  have hle := hp.le_sylow_of_normal P0
  exact ⟨x', hle (Subgroup.mem_zpowers x'), rfl⟩

theorem isQuasisimple_of_tripleCover
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    CFSG.IsQuasisimple X := by
  obtain ⟨-, ⟨φ⟩⟩ := h
  have h6 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h6
  haveI hs : IsSimpleGroup (X ⧸ Subgroup.center X) := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hc : Nat.card (X ⧸ Subgroup.center X) = 360 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; decide
  refine ⟨hperf, hs, ?_⟩
  exact CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem a6Row_J2 (hB : LieOrderBridge)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : A6Row .J2 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  have hA := CFSG.RankThree.Native.rep_of_validA hvA
  have hB' := CFSG.RankThree.Native.rep_of_validA hvB
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  obtain ⟨hcardP, hcls⟩ := check_card_order_sound j2S3Data hA hB' h
  set P := Subgroup.closure ({CFSG.Monster.B.Co2.permOfArr j2S3Data.n j2S3Data.A,
    CFSG.Monster.B.Co2.permOfArr j2S3Data.n j2S3Data.B} :
    Set (Equiv.Perm (Fin j2S3Data.n))) with hPdef
  have b : ↥P ≃* (TauCeti.CFSGIndex.sporadic .J2).Group := e.symm.trans (hbr .J2).some
  haveI hs : IsSimpleGroup ↥P := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm
  have hord : j2S3Data.ord = 604800 := rfl
  have hnc : ∃ a c : ↥P, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP, hord]; norm_num)
  have hcases : ∀ c < j2S3Data.cases.size,
      j2S3Data.cases[c]!.card = 1080 ∨ j2S3Data.cases[c]!.card = 36 := by decide +kernel
  refine a6Row_of_model hB hOut b hnc fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin j2S3Data.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  have hmapc := map_centralizer_subtype P x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥P)) = j2S3Data.cases[c]!.card := by
    rw [← hcc, ← hmapc, Subgroup.card_map_of_injective P.subtype_injective]
  rcases hcases c hc with h1080 | h36
  · have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
    have hv : (Nat.card ↥P).factorization 3 =
        (Nat.card (Subgroup.centralizer ({x} : Set ↥P))).factorization 3 := by
      rw [hcc', h1080, hcardP, hord, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
        show (1080 : ℕ) = 3 ^ 3 * 40 by norm_num, factorization_three_27 (by norm_num) (by norm_num),
        factorization_three_27 (by norm_num) (by norm_num)]
    have hz := exists_sylow_of_factorization hx hv
    have hX : Nonempty (↥P ≃* CFSG.Blueprint.NativeSporadic.J2) := ⟨e.symm⟩
    have h415 := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
    exact a6Free_of_quasisimple hx (isQuasisimple_of_tripleCover
      (CFSG.RankThree.PartTwo.KFacts.KS14.j2_centralizer_isPerfect h415 hX hx1 hz)
      (CFSG.RankThree.PartTwo.KFacts.KS14.j2_centralizer_isTripleCover h415 hX hx1 hz))
  · exact a6Free_of_not_dvd hx (by rw [hcc', h36]; norm_num)

theorem i1430SporS_of_BM
    (hBr : A6Row .B) (hMr : A6Row .M) : ClsRed.I1430SporS := by
  have hB := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  obtain ⟨hM11, hJ1, hM22, hM23, hHS⟩ := a6Row_small hB hOrd hOut
  obtain ⟨hMcL, hCo3, hCo2, hFi22, hLy, hTh, hFi23, hFi24⟩ := a6Row_cardRows hB hOut hbr
  have hM12 := a6Row_M12 hB hOrd hOut
  have hJ2 := a6Row_J2 hB hOut hbr
  have hM24 := a6Row_M24 hB hOrd hOut
  have hHe := a6Row_He hB hOrd hOut
  have hRu := a6Row_Ru hB hOut hbr
  have hHN := a6Row_HN hB hOrd hOut
  have hCo1 := a6Row_Co1 hB hOut hbr
  have hJ4 := a6Row_J4 hB hOut hbr
  refine i1430SporS_of_rows hB fun s h1 h2 h3 => ?_
  cases s
  all_goals first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact absurd rfl h3
    | assumption

theorem i1430Cls_of_BM_lie
    (hBr : A6Row .B) (hMr : A6Row .M) (hON : ClsRed.I1430ONCover)
    (hLie : ClsRed.I1430ClsLie) : I1430Cls :=
  ClsRed.i1430Cls_of_parts CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds (i1430SporS_of_BM hBr hMr) hON hLie

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

end
