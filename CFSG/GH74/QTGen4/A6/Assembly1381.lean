module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.A6.Gen4Cuts
public import CFSG.Quasithin.H13.A6S1512
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1378

public section

namespace CFSG.GH74.QTGen4

open CFSG.GH74 CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6 CFSG.Open CFSG.Blueprint
  CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt13_3_2_At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      QT13Five (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (T ≤ Subgroup.normalizer (K : Set G) ∧ quasithinIsMaximalLocal T K ∧
        quasithinIsMaxTwoLocal (Subgroup.normalizer (K : Set G)) ∧
        ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → K ⊔ T ≤ M →
          M = Subgroup.normalizer (K : Set G)) ∧
      ((∃ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V) ∧
        ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
          V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧ FSU G T K V ∧
          ∃ _ : IsMulCommutative ↥V, Modules13_3_2 K V) ∧
      ((¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) ∨
          quasithinO2QuotientIso L (alternatingGroup (Fin 5))) → QTH13 G T K)

@[expose] def Stmt13_3_2_GH : Prop := ∀ (G : Type) [Group G] [Finite G], GHCtx G → Stmt13_3_2_At G

def Stmt13_3_6_At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V →
      ¬ g1 T V ≤ Subgroup.normalizer (L : Set G) ∨
        (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧ IsA6On L V ∧
          ∃ _ : IsMulCommutative ↥V, Nat.card V = 2 ^ 5 ∧
            FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥)

def Stmt13_3_6_GH : Prop := ∀ (G : Type) [Group G] [Finite G], GHCtx G → Stmt13_3_6_At G

def Stmt13_7_8_At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ LieModel G .PSU 4 3 1 → IsMulCommutative ↥(conjClosure V (g1 T V))

def Stmt13_7_8_GH : Prop := ∀ (G : Type) [Group G] [Finite G], GHCtx G → Stmt13_7_8_At G

@[expose] def Stmt13_5_12_six_At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → ¬ LieModel G .PSp 3 2 1 →
    ¬ IsMulCommutative ↥(conjClosure (v3 T L V) (g1 T V)) → LieModel G .PSU 4 3 1

@[expose] def Stmt13_5_12_six_GH : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GHCtx G → Stmt13_5_12_six_At G

def Input1379Six_At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → IsElemAbelian 2 (conjClosure V S.G1)

def Input1379Six_GH : Prop := ∀ (G : Type) [Group G] [Finite G], GHCtx G → Input1379Six_At G

theorem isA6On_of_modules_At {G : Type} [Group G] [Finite G]
    (h13316 : ∀ T L : Subgroup G, QTH13 G T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    {T L V : Subgroup G} (hH : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) [IsMulCommutative ↥V]
    (hmod : Modules13_3_2 L V) : IsA6On L V := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, -, hc⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
    obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLN
    exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  · exact nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h6
  · exact nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hc
  · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
  · exact (h13316 T L hH hu).elim

theorem exists_setting4_At {G : Type} [Group G] [Finite G] (h1332 : Stmt13_3_2_At G)
    (h13316 : ∀ T L : Subgroup G, QTH13 G T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    {T L V : Subgroup G} (h : QTH13 G T L)
    (hA6 : A6CentralQuotient L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
      obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLV
      exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
    · exact h6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
    · exact (h13316 T L h hu).elim
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
    centralQuot := hA6
    frame := F }⟩

theorem exists_setting134_At {G : Type} [Group G] [Finite G] (h1332 : Stmt13_3_2_At G)
    {T L V : Subgroup G} (h : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : Nonempty (Setting134 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hc : Nat.card V = 2 ^ 5 ∧
      FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥ := by
    rcases hmod with h1 | h2 | h3 | h4 | h5
    · exact absurd h1.2 hZV
    · exact absurd h2.2 hZV
    · exact ⟨h3.1, h3.2.2⟩
    · exact absurd h4.2.2 hZV
    · exact absurd h5.2.2 hZV
  obtain ⟨R⟩ := exists_rawData6 hLV hc.2
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 5) hc.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame5 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    frame := F }⟩

theorem a6CentralQuotient_of_isA6On_At {G : Type} [Group G] [Finite G]
    (h1332 : Stmt13_3_2_At G)
    (h13316 : ∀ T L : Subgroup G, QTH13 G T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    {T L V : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hA6V : IsA6On L V) :
    A6CentralQuotient L := by
  obtain ⟨hfive, -, -, -⟩ := h1332 T L hH L hH.faithful
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  obtain ⟨e⟩ := hA6V
  obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLN
  obtain ⟨φ₁, hφ₁⟩ := exists_surjective_quot_of_alt6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  have hle := Nat.card_le_card_of_surjective φ₁ hφ₁
  rw [card_alt6] at hle
  rcases hfive with hf | h32 | hf | hhat | hu
  · obtain ⟨f⟩ := hf
    rw [Nat.card_congr f.toEquiv, card_alt5] at hle
    omega
  · rw [card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h32)] at hle
    omega
  · obtain ⟨f⟩ := hf
    have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : f z ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
        map_center_le_center f.toMonoidHom f.surjective ⟨z, hz, rfl⟩
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact f.injective (h1.trans (map_one f).symm)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans f)⟩
  · exact hhat.2.2
  · exact (h13316 T L hH hu).elim

theorem stmt13_8_1_GH_of_inputs (h1332 : Stmt13_3_2_GH) (h13316 : Stmt13_3_16_GH)
    (h1336 : Stmt13_3_6_GH) (h1378 : Stmt13_7_8_GH) : Stmt13_8_1_GH := by
  intro G _ _ hc T L hH hA6
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hNS, hNU⟩ := hcon
  have h1332' := h1332 G hc
  have h13316' := h13316 G hc
  obtain ⟨-, -, ⟨⟨V, hV⟩, hall⟩, -⟩ := h1332' T L hH L hH.faithful
  obtain ⟨-, -, -, hcomm, hmod⟩ := hall V hV
  have hA6V : IsA6On L V := isA6On_of_modules_At h13316' hH hA6 hV hmod
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact false_of_setting134_gen4 hc.1 (exists_setting134_At h1332' hH hV h).some
  obtain ⟨S⟩ := exists_setting4_At h1332' h13316' hH hA6 hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hM : ¬ S.G1 ≤ Subgroup.normalizer (L : Set G) := by
    rcases h1336 G hc T L V hH hV with h | ⟨hne, -⟩
    · rwa [hg1] at h
    · exact absurd hZV hne
  have hab := h1378 G hc T L V hH hV hA6V hNS hNU
  rw [hg1] at hab
  exact false_of_abelian_gen4 hc.1 S hM hab

theorem stmt13_7_8_GH_of_inputs (h1332 : Stmt13_3_2_GH) (h13316 : Stmt13_3_16_GH)
    (h13512 : Stmt13_5_12_six_GH) (h1379 : Input1379Six_GH) : Stmt13_7_8_GH := by
  intro G _ _ hc T L V hH hV hA6V hNS hNU
  have h1332' := h1332 G hc
  have h13316' := h13316 G hc
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact false_of_setting134_gen4 hc.1 (exists_setting134_At h1332' hH hV h).some
  obtain ⟨S⟩ := exists_setting4_At h1332' h13316' hH
    (a6CentralQuotient_of_isA6On_At h1332' h13316' hH hV hA6V) hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hcomm : IsMulCommutative ↥(conjClosure S.V3 S.G1) := by
    by_contra hna
    apply hNU
    refine h13512 G hc T L V hH hV hA6V hNS ?_
    rw [S.v3_eq, hg1]
    exact hna
  have hab : IsElemAbelian 2 (conjClosure S.V3 S.G1) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall
      (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) fun k hk v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hcomm.is_comm.comm
      ⟨w, HypF91.conjSub_le_conjClosure hk hw⟩ ⟨v, le_conjClosure _ _ hv⟩)
  rw [hg1]
  by_cases hM : S.G1 ≤ Subgroup.normalizer (L : Set G)
  · have hle : conjClosure V S.G1 ≤ V :=
      conjClosure_le fun _ hg _ hv => S.conj_mem_V_of_le_M hM hg hv
    exact (F7.isElemAbelian_mono S.elemAbelian_V hle).1
  · exact (h1379 G hc T L V S hNS hNU (not_isHatA6_of_gen4 hc.1 hH) (S.G1_mem_Hz_of hM) hab).1

theorem stmt13_3_2_GH_of_F4 (h : CFSG.Quasithin.H13.Stmt13_3_2_F4) : Stmt13_3_2_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem stmt13_3_6_GH_of_F4 (h : CFSG.Quasithin.H13.A6.Stmt13_3_6_F4) : Stmt13_3_6_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem stmt13_5_12_six_GH_of_F4 (h : CFSG.Quasithin.H13.A6.Stmt13_5_12_six_F4) :
    Stmt13_5_12_six_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem input1379Six_GH_of_F4 (h : CFSG.Quasithin.H13.A6.Input1379Six_F4) : Input1379Six_GH :=
  fun G _ _ hc => by haveI := finite4_of_gen4 hc.1; exact h G

theorem stmt13_8_1_F4_of_inputs (h1332 : CFSG.Quasithin.H13.Stmt13_3_2_F4)
    (h13316 : CFSG.Quasithin.H13.Stmt13_3_16_F4) (h1336 : CFSG.Quasithin.H13.A6.Stmt13_3_6_F4)
    (h1378 : CFSG.Quasithin.H13.A6.Stmt13_7_8_F4) : CFSG.Quasithin.H13.Stmt13_8_1_F4 := by
  intro G _ _ T L hH hA6
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hNS, hNU⟩ := hcon
  have h1332' : Stmt13_3_2_At G := fun T L hH K hK => h1332 G T L hH K hK
  have h13316' : ∀ T L : Subgroup G, QTH13 G T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 :=
    fun T L hH => h13316 G T L hH
  obtain ⟨-, -, ⟨⟨V, hV⟩, hall⟩, -⟩ := h1332' T L hH L hH.faithful
  obtain ⟨-, -, -, hcomm, hmod⟩ := hall V hV
  have hA6V : IsA6On L V := isA6On_of_modules_At h13316' hH hA6 hV hmod
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact false_of_setting134_gen4 Finite4.gen4 (exists_setting134_At h1332' hH hV h).some
  obtain ⟨S⟩ := exists_setting4_At h1332' h13316' hH hA6 hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hM : ¬ S.G1 ≤ Subgroup.normalizer (L : Set G) := by
    rcases h1336 G T L V hH hV with h | ⟨hne, -⟩
    · rwa [hg1] at h
    · exact absurd hZV hne
  have hab := h1378 G T L V hH hV hA6V hNS hNU
  rw [hg1] at hab
  exact false_of_abelian_gen4 Finite4.gen4 S hM hab

theorem stmt13_7_8_F4_of_inputs (h1332 : CFSG.Quasithin.H13.Stmt13_3_2_F4)
    (h13316 : CFSG.Quasithin.H13.Stmt13_3_16_F4)
    (h13512 : CFSG.Quasithin.H13.A6.Stmt13_5_12_six_F4)
    (h1379 : CFSG.Quasithin.H13.A6.Input1379Six_F4) : CFSG.Quasithin.H13.A6.Stmt13_7_8_F4 := by
  intro G _ _ T L V hH hV hA6V hNS hNU
  have h1332' : Stmt13_3_2_At G := fun T L hH K hK => h1332 G T L hH K hK
  have h13316' : ∀ T L : Subgroup G, QTH13 G T L → ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 :=
    fun T L hH => h13316 G T L hH
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact false_of_setting134_gen4 Finite4.gen4 (exists_setting134_At h1332' hH hV h).some
  obtain ⟨S⟩ := exists_setting4_At h1332' h13316' hH
    (a6CentralQuotient_of_isA6On_At h1332' h13316' hH hV hA6V) hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hcomm : IsMulCommutative ↥(conjClosure S.V3 S.G1) := by
    by_contra hna
    apply hNU
    refine h13512 G T L V hH hV hA6V hNS ?_
    rw [S.v3_eq, hg1]
    exact hna
  have hab : IsElemAbelian 2 (conjClosure S.V3 S.G1) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall
      (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) fun k hk v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hcomm.is_comm.comm
      ⟨w, HypF91.conjSub_le_conjClosure hk hw⟩ ⟨v, le_conjClosure _ _ hv⟩)
  rw [hg1]
  by_cases hM : S.G1 ≤ Subgroup.normalizer (L : Set G)
  · have hle : conjClosure V S.G1 ≤ V :=
      conjClosure_le fun _ hg _ hv => S.conj_mem_V_of_le_M hM hg hv
    exact (F7.isElemAbelian_mono S.elemAbelian_V hle).1
  · exact (h1379 G T L V S hNS hNU (not_isHatA6_of_gen4 Finite4.gen4 hH) (S.G1_mem_Hz_of hM)
      hab).1

end CFSG.GH74.QTGen4
