module

public import CFSG.Quasithin.H13.U3S1349L
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1349Local
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1343
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347St
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1349A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V : Subgroup G}

theorem s134_sup_parabolics_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) :
    (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (l2Of S ⊔ T) = normalizer (L : Set G) := by
  obtain ⟨h1T, h2T, h12, h21⟩ := s134_parabolics S
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := (oTwoRes_le _).trans inf_le_left
  have hle : (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (l2Of S ⊔ T) ≤ normalizer (L : Set G) :=
    sup_le (sup_le (hL1L.trans le_normalizer) S.T_le_NL)
      (sup_le ((s134_L2_le_L S).trans le_normalizer) S.T_le_NL)
  rcases s134_overgroups_M_F4 h1222 S hp _ (le_sup_right.trans le_sup_left) hle with h | h | h | h
  · exact absurd (le_antisymm (le_sup_left.trans h.le) le_sup_right) h1T
  · exact absurd (le_sup_right.trans h.le) h21
  · exact absurd (le_sup_left.trans h.le) h12
  · exact h

theorem input1349Local_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h56 : AsB56) (h1345 : NQS134.Stmt13_4_5_F4) (h1347 : Stmt13_4_7L2_F4)
    (h1348 : Stmt13_4_8_F4) (hX1 : Sp62InvolutionsIntoCJ) (hX2 : Sp62TransvectionProduct) :
    A6.Input1349Local_F4 := by
  intro G _ _ T L V S z hz hzL hCz hsol
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (L : Set G) with hM
  set Gz := centralizer ({z} : Set G) with hGzdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set Z := quasithinOmegaOneCenter T with hZdef
  have hTsylG : quasithinIsSylowTwo T := S.h13.sylow
  have hT2 : IsPGroup 2 T := hTsylG.1
  have hTM : T ≤ M := S.T_le_NL
  have hTGz : T ≤ Gz := s134_T_le_Gz hz
  have hL1TGz : L₁ ⊔ T ≤ Gz := s134_L1T_le_Gz S hz
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1TM : L₁ ⊔ T ≤ M := sup_le (hL1L.trans le_normalizer) hTM
  have hL2TM : l2Of S ⊔ T ≤ M := sup_le ((s134_L2_le_L S).trans le_normalizer) hTM
  obtain ⟨h1T, h2T, h12, h21⟩ := s134_parabolics S
  have hTZ : T ≤ centralizer (Z : Set G) := fun t ht => mem_centralizer_iff.2 fun x hx =>
    (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 hx).2.1 t ht).symm
  have hCzV : centralizer ({S.zV} : Set G) = M := S.centralizer_zV_F4 h1222

  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hz.2).2.2
  have hO2Gz : pCoreOf 2 Gz ≠ ⊥ := by
    intro hbot
    have hzmem : z ∈ Gz := mem_centralizer_singleton_iff.mpr rfl
    have hle : zpowers z ≤ pCoreOf 2 Gz := by
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        (zpowers_le.mpr hzmem) ?_ ?_
      · refine (normal_subgroupOf_iff_le_normalizer (zpowers_le.mpr hzmem)).2 fun y hy => ?_
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hz2 hz1)
    rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
    exact hz1 hle
  have hInHGz : InH T Gz := ⟨hTGz, hO2Gz⟩
  have hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ M := ⟨Gz, hInHGz, hCz⟩
  have hsylGz : IsSylowTwoOf T Gz := A5.isSylowTwoOf_of_le hTsylG hTGz
  have hred : IsTwoReducedIn Gz (VZ T Gz) :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hInHGz) hsylGz
  have hZVH : V ⊓ centralizer (L : Set G) ≤ VZ T Gz := by
    intro x hx
    rcases S.mem_ZV_iff.1 hx with rfl | rfl
    · exact one_mem _
    · exact le_conjClosure _ _ (s134_zV_mem_Z S)

  obtain ⟨hA6, hIq, hW, hGzeq, hGzq, hstar, -⟩ :=
    h1348 G T L V S z hz hzL hCz Gz (VZ T Gz) ⟨⟨hL1TGz, hO2Gz⟩, le_rfl, hCz⟩ hsol hred hZVH
  set I := conjClosure (thompsonJ (r1Of T L V)) Gz with hIdef

  have hGzSL : quasithinO2QuotientIso Gz A6.SL22.K := by
    obtain ⟨φ, hφ, hker⟩ := hGzq
    let e : A6.SL22.K ≃* Perm (Fin 3) × Perm (Fin 3) :=
      MulEquiv.prodCongr CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
        CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
    refine ⟨e.symm.toMonoidHom.comp φ, e.symm.surjective.comp hφ, ?_⟩
    rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa using congrArg e h, fun h => by rw [h, map_one]⟩
  obtain ⟨P₀, X₁, X₂, hP, hP', hc, hX₁, hX₂, hX₁₂, hX₂₁⟩ := A6.modelData_SL22.exists_data
  obtain ⟨A₁, A₂, -, -, -, -, hA₁₂, hA₂₁, -, -, hclsGz⟩ :=
    A6.overgroups_transport hGzSL hsylGz hP hP' hc hX₁ hX₂ hX₁₂ hX₂₁

  have hMGz : M ⊓ Gz = L₁ ⊔ T :=
    (eq_of_overgroups hclsGz hA₁₂ hA₂₁ le_sup_right (le_inf hL1TM hL1TGz) inf_le_right h1T
      fun h => hCz (h.symm.le.trans inf_le_left)).symm
  have hMLT : M = L ⊔ T := by
    refine le_antisymm ((s134_normalizer_le_sup_F4 h1222 S hz hzL).trans (sup_le le_sup_left ?_))
      (sup_le le_normalizer hTM)
    rw [hMGz]
    exact sup_le (hL1L.trans le_sup_left) le_sup_right
  have hp : IsPGroup 2 ↥(M ⊓ centralizer (V : Set G)) := s134_isPGroup_CMV S hA6 hMLT
  have hCT : M ⊓ centralizer (V : Set G) ≤ T := s134_CMV_le_T_F4 S hp h1222
  have hMsup : (L₁ ⊔ T) ⊔ (l2Of S ⊔ T) = M := s134_sup_parabolics_F4 h1222 S hp
  have hclsM : ∀ Y : Subgroup G, T ≤ Y → Y ≤ M →
      Y = T ∨ Y = L₁ ⊔ T ∨ Y = l2Of S ⊔ T ∨ Y = M := s134_overgroups_M_F4 h1222 S hp

  have hIGz : I ≤ Gz := (le_sup_right.trans le_sup_left).trans hGzeq.symm.le
  have hGzI : Gz ≤ normalizer (I : Set G) := le_normalizer_conjClosure _ _
  have hTI : T ≤ normalizer (I : Set G) := hTGz.trans hGzI
  have hsylIT : IsSylowTwoOf T (I ⊔ T) := A5.isSylowTwoOf_of_le hTsylG le_sup_right
  obtain ⟨hITq, -⟩ := quot_S3_sup hTI hsylIT hIq
  have hITM : ¬ I ⊔ T ≤ M := hstar.2.1
  have hITGz : I ⊔ T ≤ Gz := sup_le hIGz hTGz
  have hITT : I ⊔ T ≠ T := fun h => hITM (h.le.trans hTM)
  have hIM : ¬ I ≤ M := fun h => hITM (sup_le h hTM)

  have hZcard := s134_card_Z_F4 h1332 hC58 h317 h56 S hHM
  have hindex₁ : Nat.card ↥Z = 2 * Nat.card ↥(cZ T (I ⊔ T)) := by
    rw [cZ_sup_eq T I]
    have hVab : ∀ a ∈ VZ T Gz, ∀ b ∈ VZ T Gz, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hV2 : ∀ v ∈ VZ T Gz, v * v = 1 := fun v hv => by
      rw [← pow_two]
      exact hred.2.2.1.2 v hv
    have hOI : pCoreOf 2 I ≤ centralizer (VZ T Gz : Set G) := by
      refine (pCoreOf_le_pCoreOf hIGz hGzI).trans ?_
      refine hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 Gz)
        (LieType.BorelTits.le_normalizer_pCoreOf 2 Gz) fun d hd => ?_
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Gz ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact one_mem _
    have hsylI : IsSylowTwoOf (I ⊓ T) I := by
      have := A4.isSylowTwoOf_inf_normal hsylIT le_sup_left (sup_le le_normalizer hTI)
      rwa [inf_comm] at this
    have hle := card_le_two_mul_inf_centralizer hVab hV2 (le_conjClosure _ _)
      (hIGz.trans hred.2.1) hIq hOI hsylI hTZ hW
    have hne : Z ⊓ centralizer (I : Set G) ≠ Z := by
      intro h
      apply hIM
      intro i hi
      have hmem : S.zV ∈ Z ⊓ centralizer (I : Set G) := by
        rw [h]
        exact s134_zV_mem_Z S
      rw [← hCzV, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (mem_inf.1 hmem).2 i hi
    obtain ⟨k, hk⟩ := card_dvd_of_le (inf_le_left : Z ⊓ centralizer (I : Set G) ≤ Z)
    have hpos : 0 < Nat.card ↥(Z ⊓ centralizer (I : Set G)) := Nat.card_pos
    have hk1 : k ≠ 1 := by
      intro h
      rw [h, mul_one] at hk
      exact hne (eq_of_le_of_card_ge inf_le_left hk.le)
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, mul_zero] at hk
      exact (Nat.card_pos (α := ↥Z)).ne' hk
    have hk2 : k ≤ 2 := by
      rw [hk, mul_comm 2] at hle
      exact Nat.le_of_mul_le_mul_left hle hpos
    have hk' : k = 2 := by omega
    rw [hk, hk', mul_comm]
  have hindex₂ : Nat.card ↥Z = 2 * Nat.card ↥(cZ T (l2Of S ⊔ T)) := by
    rw [s134_cZ_L2T S hZcard]
    exact hZcard

  have hVL2T : V ≤ pCoreOf 2 (l2Of S ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((s134_V_le_L2 S).trans le_sup_left)
      (sup_le ((s134_L2_le_L S).trans S.frame.L_le) S.frame.T_le) S.isPGroup_V
  have hInH₂ : InH T (l2Of S ⊔ T) :=
    ⟨le_sup_right, fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ hVL2T))⟩
  have hK2 : oTwoRes (l2Of S ⊔ T) = l2Of S := s134_oTwoRes_L2T S

  have hcent : InH T ((I ⊔ T) ⊔ (l2Of S ⊔ T)) →
      (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓ centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G) ≤
          normalizer (oTwoRes (I ⊔ T) : Set G) ∧
        ((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓ centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) ≤
          normalizer (oTwoRes (l2Of S ⊔ T) : Set G)) ∧
      (oTwoRes (I ⊔ T) = oThreePrimeResidual (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓
          centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G)) ∨
        oTwoRes (l2Of S ⊔ T) = oThreePrimeResidual (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓
          centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G))) := by
    intro hInH0
    set H₀ := (I ⊔ T) ⊔ (l2Of S ⊔ T) with hH₀
    have hMH0 : ¬ M ≤ H₀ := fun h =>
      hITM (le_sup_left.trans (s134_le_of_normalizer_le S hInH0.2 h))
    have hMH0eq : M ⊓ H₀ = l2Of S ⊔ T :=
      (eq_of_overgroups hclsM h12 h21 le_sup_right (le_inf hL2TM le_sup_right) inf_le_left h2T
        fun h => hMH0 (h.symm.le.trans inf_le_right)).symm
    have hGzH0 : Gz ⊓ H₀ = I ⊔ T := by
      refine (eq_of_overgroups hclsGz hA₁₂ hA₂₁ le_sup_right (le_inf hITGz le_sup_left)
        inf_le_left hITT fun h => hMH0 ?_).symm
      rw [← hMsup]
      exact sup_le (hL1TGz.trans (h.symm.le.trans inf_le_right)) le_sup_right
    have hzK1 : z ∈ cZ T (oTwoRes (I ⊔ T)) :=
      mem_inf.2 ⟨hz.2, mem_centralizer_of_le_centralizer ((oTwoRes_le _).trans hITGz)⟩
    have hzVK2 : S.zV ∈ cZ T (oTwoRes (l2Of S ⊔ T)) := by
      rw [hK2]
      refine mem_inf.2 ⟨s134_zV_mem_Z S, ?_⟩
      have hzVL : S.zV ∈ centralizer (L : Set G) := (S.mem_ZV_iff.2 (Or.inr rfl)).2
      exact centralizer_le (SetLike.coe_subset_coe.2 (s134_L2_le_L S)) hzVL
    have hC1 : centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G) ≤ Gz :=
      centralizer_le (Set.singleton_subset_iff.2 hzK1)
    have hC2 : centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) ≤ M := by
      rw [← hCzV]
      exact centralizer_le (Set.singleton_subset_iff.2 hzVK2)
    have hH0C2 : H₀ ⊓ centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) = l2Of S ⊔ T := by
      apply le_antisymm
      · intro x hx
        have : x ∈ M ⊓ H₀ := mem_inf.2 ⟨hC2 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
        rw [hMH0eq] at this
        exact this
      · refine le_inf le_sup_right ?_
        rw [hK2]
        refine sup_le (fun l hl => ?_) (fun t ht => ?_)
        · rw [mem_centralizer_iff]
          intro x hx
          exact (mem_centralizer_iff.1 (mem_inf.1 hx).2 l hl).symm
        · rw [mem_centralizer_iff]
          intro x hx
          exact (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1
            (mem_inf.1 hx).1).2.1 t ht).symm
    refine ⟨⟨fun x hx => ?_, ?_⟩, Or.inr ?_⟩
    · have : x ∈ Gz ⊓ H₀ := mem_inf.2 ⟨hC1 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
      rw [hGzH0] at this
      exact le_normalizer_oTwoRes _ this
    · rw [hH0C2, hK2]
      exact sup_le le_normalizer (s134_T_le_normalizer_L2 S)
    · rw [hH0C2, s134_oThree_L2T S hA6, hK2]

  have hyp : Hyp1347 T (I ⊔ T) (l2Of S ⊔ T) :=
    { inH₁ := hstar.1
      inH₂ := hInH₂
      ne := fun h => hITM (h.le.trans hL2TM)
      s3₁ := hITq
      s3₂ := s134_L2T_quot S hCT
      chief := Or.inr (by rw [hK2]; exact s134_chief_L2 S)
      index₁ := hindex₁
      index₂ := hindex₂
      cent := hcent }
  obtain ⟨⟨hInH0, hH0M, -, -, -, -, -, hcases⟩, h2', h3', hniv, hii2⟩ :=
    h1347 G T L V S _ _ hyp hK2
  set H₀ := (I ⊔ T) ⊔ (l2Of S ⊔ T) with hH₀
  have hii : Concl1347ii T (I ⊔ T) (l2Of S ⊔ T) := by
    rcases hcases with hi | hii | hiii | hiv
    · exfalso

      have hcomm := hi.2.1
      rw [hK2] at hcomm
      have hL2N : l2Of S ≤ normalizer (oTwoRes (I ⊔ T) : Set G) := by
        refine le_normalizer_of_conj_mem' fun l hl k hk => ?_
        have hlk : ⁅l, k⁆ ∈ ⁅oTwoRes (I ⊔ T), l2Of S⁆ := by
          rw [commutator_comm]
          exact commutator_mem_commutator hl hk
        have hc : ⁅l, k⁆ ∈ pCoreOf 2 (oTwoRes (I ⊔ T)) := (mem_inf.1 (hcomm hlk)).1
        have e : l * k * l⁻¹ = ⁅l, k⁆ * k := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (LieType.BorelTits.pCoreOf_le 2 _ hc) hk
      have hL1N : L₁ ≤ normalizer (oTwoRes (I ⊔ T) : Set G) := by
        rw [oTwoRes_sup_eq hT2 hTI]
        exact (le_sup_left.trans hL1TGz).trans (hGzI.trans (normalizer_le_normalizer_oTwoRes I))
      have hKV := s134_le_centralizer_V S hz hzL ((oTwoRes_le _).trans hITGz) hL1N hL2N
      have hCVM : centralizer (V : Set G) ≤ M := fun x hx =>
        A6.Setting134.normalizer_V_le S (Subgroup.centralizer_le_normalizer _ hx)
      exact hITM ((le_oTwoRes_sup_of_isSylowTwoOf hsylIT).trans (sup_le (hKV.trans hCVM) hTM))
    · exact hii
    · exact absurd hiii h3'
    · exact absurd hiv hniv
  obtain ⟨K₀, hH0K, hKc, -, -, hKq, hH0J, -⟩ := id hii

  have hK0H0 : K₀ ≤ H₀ := le_sup_left.trans hH0K.symm.le
  have hH0sol : ¬ Group.IsSolvable ↥H₀ := fun hs =>
    hKc.1 (eq_bot_of_perfect_of_le_solvable hs hKc.2.1 hK0H0)
  have hH0N : H₀ ≤ normalizer (K₀ : Set G) :=
    ((h1345 G T L V S H₀ hInH0 hH0M hH0sol).2 K₀ hKc).2.1
  have hTsylH0 : IsSylowTwoOf T H₀ :=
    A5.isSylowTwoOf_of_le hTsylG (le_sup_right.trans le_sup_left)
  have hK0H2 : ¬ K₀ ≤ l2Of S ⊔ T := fun h => hH0M (hH0K.le.trans (sup_le (h.trans hL2TM) hTM))
  have hH0q : quasithinO2QuotientIso H₀ A6.SL3.S :=
    quot_SL3_of_sup hTsylH0 hH0N hH0K hKq le_sup_right le_sup_right h2T hK0H2

  have hMH0 : ¬ M ≤ H₀ := fun h => hH0M (s134_le_of_normalizer_le S hInH0.2 h)
  have hMH0eq : M ⊓ H₀ = l2Of S ⊔ T :=
    (eq_of_overgroups hclsM h12 h21 le_sup_right (le_inf hL2TM le_sup_right) inf_le_left h2T
      fun h => hMH0 (h.symm.le.trans inf_le_right)).symm
  have hGzH0 : Gz ⊓ H₀ = I ⊔ T := by
    refine (eq_of_overgroups hclsGz hA₁₂ hA₂₁ le_sup_right (le_inf hITGz le_sup_left)
      inf_le_left hITT fun h => hMH0 ?_).symm
    rw [← hMsup]
    exact sup_le (hL1TGz.trans (h.symm.le.trans inf_le_right)) le_sup_right
  have hL1M : L₁ ⊔ T ≠ M := fun h => h21 (hL2TM.trans h.symm.le)
  have hL1H0 : (L₁ ⊔ T) ⊓ H₀ = T := by
    by_contra hne
    have heq := eq_of_overgroups hclsM h12 h21
      (le_inf le_sup_right (le_sup_right.trans le_sup_left)) inf_le_left hL1TM hne hL1M
    apply hMH0
    rw [← hMsup]
    exact sup_le (heq.symm.le.trans inf_le_right) le_sup_right
  refine ⟨H₀, by rw [hMGz]; exact hL1H0, s134_quot_M_F4 h1222 S hp, hGzSL, hH0q, hsylGz, hTsylH0,
    ⟨by rw [hMGz]; exact h1T, by rw [hMH0eq]; exact h2T, by rw [hGzH0]; exact hITT⟩,
    ⟨by rw [hMGz]; exact hL1M, by rw [hMH0eq]; exact fun h => h12 (hL1TM.trans h.symm.le),
      fun h => hCz (h.symm.le.trans inf_le_left), fun h => hMH0 (by
        rw [← hMsup]
        exact sup_le (hL1TGz.trans (h.symm.le.trans inf_le_right)) le_sup_right),
      fun h => hH0M (h.symm.le.trans inf_le_left), fun h => h21 (by
        rw [← hMGz]
        exact le_inf hL2TM ((le_sup_right.trans h.symm.le).trans inf_le_left))⟩,
    ⟨by rw [hMGz, hMH0eq]; exact fun h => h12 h.le, by
        rw [hMGz, hGzH0]; exact fun h => hITM (h.symm.le.trans hL1TM), by
        rw [hMH0eq, hGzH0]; exact fun h => hITM (h.symm.le.trans hL2TM)⟩, fun hE => ?_⟩

  obtain ⟨T', hT'⟩ := exists_sylow_of_quasithinIsSylowTwo hTsylG
  have hTE : (T' : Subgroup G) ≤ M ⊔ Gz ⊔ H₀ := by
    rw [hT']
    exact hTM.trans (le_sup_left.trans le_sup_left)
  have hNJ : normalizer (thompsonJ (T' : Subgroup G) : Set G) ≤ M ⊔ Gz ⊔ H₀ := by
    rw [hT']
    have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
    have hT1 : T ≠ ⊥ := fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ S.V_le_T))
    have hJ1 : thompsonJ T ≠ ⊥ := S1414.thompsonJ_ne_bot hT2 hT1
    have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
    set X := normalizer (thompsonJ T : Set G) with hX
    have hXO : pCoreOf 2 X ≠ ⊥ := fun h =>
      hJ1 (le_bot_iff.1 (h ▸ LieType.BorelTits.le_pCoreOf_normalizer 2 _ hJ2))
    have hTX : T ≤ X := (le_sup_right.trans le_sup_left).trans hH0J
    have hCZ : centralizer (Z : Set G) ≤ L₁ ⊔ T := by
      rw [← hMGz]
      refine le_inf ?_ ?_
      · rw [← hCzV]
        exact centralizer_le (Set.singleton_subset_iff.2 (s134_zV_mem_Z S))
      · exact centralizer_le (Set.singleton_subset_iff.2 hz.2)
    have hXL1 : X ⊓ (L₁ ⊔ T) = T := by
      by_contra hne
      have heq := eq_of_overgroups hclsM h12 h21 (le_inf hTX le_sup_right) inf_le_right hL1TM hne
        hL1M
      have hMX : M ≤ X := by
        rw [← hMsup]
        exact sup_le (heq.symm.le.trans inf_le_left) ((le_sup_right.trans hH0J))
      have h2X : IsTwoLocal X := ⟨_, hJ1, hJ2, rfl⟩
      exact hH0M (hH0J.trans (S.uniqueM.1.1.2 X h2X hMX).le)
    have hXCZ : X ⊓ centralizer (Z : Set G) = T := by
      refine le_antisymm ?_ (le_inf hTX hTZ)
      calc X ⊓ centralizer (Z : Set G) ≤ X ⊓ (L₁ ⊔ T) := inf_le_inf_left _ hCZ
        _ = T := hXL1
    have hXeq := h2' hii X ⟨hH0J, hXO⟩ hXCZ
    exact hXeq.le.trans le_sup_right
  have hdT : S.zV ∈ (T' : Subgroup G) := by
    rw [hT']
    exact S.V_le_T S.zV_mem_V
  have hdZ : S.zV ∈ centralizer ((T' : Subgroup G) : Set G) := by
    rw [hT']
    exact (mem_quasithinOmegaOneCenter_iff.1 (s134_zV_mem_Z S)).2.1
  have hCd : centralizer ({S.zV} : Set G) ≤ M ⊔ Gz ⊔ H₀ := by
    rw [hCzV]
    exact le_sup_left.trans le_sup_left
  have h5 : 5 ∣ Nat.card ↥(centralizer ({S.zV} : Set G)) := by
    rw [hCzV]
    exact five_dvd_card_of_quot (s134_quot_M_F4 h1222 S hp)
  exact fusion_of_sp62 hX1 hX2 S.h13.qtke.2.1 T' hE hTE hNJ S.orderOf_zV hdT hdZ hCd h5

end CFSG.Quasithin.H13.U3
