module

public import CFSG.Quasithin.H13.A5W1622u
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622t
public import CFSG.Quasithin.Background.C124AsmStmt
public import CFSG.Quasithin.H13.A5W1622s

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_c124_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4)
    (hres : Lem13622Case4Z0_F4) (h124 : C124StatementSQTK (G := G)) (hA7 : Lem13622A7Block_F4)
    (hH : S.Hyp1367) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (h7 : IsAlt 7 ↥(S.plus K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hH.hF
  have hz := S.not_le_centralizer_z_of_inYz hYz hT
  have hKG := hYz.1
  have hK₀ := hYz.2.1
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK

  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hKG hT hLv
  have hqP := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  obtain ⟨e7⟩ := id h7
  have hs7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hsP : IsSimpleGroup ↥(S.plus K) := e7.isSimpleGroup
  have hZP := center_eq_bot_of_isSimple_of_isQuasisimple hsP hqP
  have hnt : Nontrivial ↥(S.plus K) := hsP.toNontrivial
  have hker := ker_le_center_of_isQuasisimple hq π hπ hnt
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  set Kb := ↥K ⧸ CFSG.pCore 2 ↥K with hKb
  let eA : Kb ⧸ Subgroup.center Kb ≃* ↥(alternatingGroup (Fin 7)) :=
    (centerQuotEquiv π hπ hker).trans ((quotCenterEquivOfEqBot hZP).trans e7)
  have hcardZ : Nat.card Kb = 2520 * Nat.card (Subgroup.center Kb) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Kb),
      Nat.card_congr eA.toEquiv, L246.C123.card_A7]

  have hAQ : IsAltQuotient K (oTwoZIn K) 7 := by
    let φ : ↥K →* ↥(alternatingGroup (Fin 7)) :=
      eA.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Kb)).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    refine ⟨φ, eA.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)), ?_⟩
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, oTwoZIn, preimageModTwoCore,
      show (k : G) = K.subtype k from rfl, Subgroup.mem_map_iff_mem K.subtype_injective,
      Subgroup.mem_comap]
    show eA (QuotientGroup.mk (QuotientGroup.mk k)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rfl

  set X := K ⊔ S.Tv with hXdef
  have hXG : X ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hKG S.Tv_le_Gv
  have hsylX : IsSylowTwoOf S.Tv X :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right hXG
  have hcharX : CharTwo X := C1GN.charTwo_of_le hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right hXG
  have hred : IsTwoReducedIn X (conjClosure S.V1 X) :=
    isTwoReducedIn_conjClosure_of_sylowIn hsylX.1 hsylX.2.1 hsylX.2.2 hcharX S.V1_le_omega_Tv
  have hset : ((X : Subgroup G) : Set G) = (K : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K S.Tv hT
  have hprod : ∀ x ∈ X, ∃ l ∈ K, ∃ t ∈ S.Tv, x = l * t := by
    intro x hx
    have hx' : x ∈ ((K : Set G) * (S.Tv : Set G)) := hset ▸ hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    exact ⟨l, hl, t, ht, rfl⟩
  have hcharK : CharTwo K :=
    A4.charTwo_of_normal le_sup_left (sup_le Subgroup.le_normalizer hT) hcharX
  have hVK : ⁅conjClosure S.V1 X, K⁆ ≠ ⊥ := by
    intro h
    apply hz
    intro k hk
    have hzV : S.z ∈ conjClosure S.V1 X := le_conjClosure _ _ (Subgroup.mem_zpowers _)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h hzV) k hk)
  rcases h124 X S.Tv (conjClosure S.V1 X) K S.Tv 7 hcharX (S.sqtkGroup_sup_Tv hKG) hred hsylX
      hprod hK₀ hcharK hVK hAQ (pCoreOf_le_of_isSylowTwoOf hsylX) le_rfl (Or.inr (Or.inl rfl))
    with ⟨C, hC1, hCB, hCc, hXC⟩ | ⟨hblk, hL2 | ⟨m, hmo, hm3, hAm⟩⟩ | ⟨hblk, hexc | hA6 | hHat⟩
  ·
    have hCT : (C.subgroupOf S.Tv).Characteristic :=
      C1GN.characteristic_subgroupOf_trans (C1GN.baum_le S.Tv) hCB (C1GN.characteristic_baum S.Tv)
        hCc
    exact S.not_le_normalizer_of_characteristic_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37
      h39 hKG hK₀ hT hz (hCB.trans (C1GN.baum_le S.Tv)) hC1 hCT (le_sup_left.trans hXC)
  ·
    obtain ⟨n, hn, F, _, _, hFn, α, hα, hαk, -⟩ := hL2
    let eS := kbarEquivOfSurj α hα hαk
    have hcS : Nat.card Kb = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr eS.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
        Nat.card_eq_fintype_card, hFn]
      norm_num
    have hZ2 : Nat.card (Subgroup.center Kb) ≤ 2 := by
      rw [Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
      exact card_center_sl2_le
    exact sl2_card_ne hn Nat.card_pos hZ2 (hcS.symm.trans hcardZ)
  ·
    obtain ⟨α, hα, hαk, -⟩ := id hAm
    let eS := kbarEquivOfSurj α hα hαk
    have hm5 : 5 ≤ m ∨ m = 3 := by
      obtain ⟨j, rfl⟩ := hmo
      omega
    have hm7 : m = 7 := by
      rcases hm5 with hm5 | rfl
      · have hsA : IsSimpleGroup (alternatingGroup (Fin m)) :=
          alternatingGroup.isSimpleGroup (by simpa using hm5)
        have hZ : Subgroup.center Kb = ⊥ :=
          center_eq_bot_of_isSimple_of_isQuasisimple eS.isSimpleGroup hq
        have h1 : Nat.card Kb = 2520 := by
          rw [hcardZ, hZ, Subgroup.card_bot, mul_one]
        have h2 := two_mul_card_alt (m := m) (by omega)
        rw [← Nat.card_congr eS.toEquiv, h1] at h2
        exact eq_seven_of_factorial h2.symm
      · exfalso
        have h2 := two_mul_card_alt (m := 3) (by norm_num)
        rw [← Nat.card_congr eS.toEquiv, hcardZ] at h2
        have : 0 < Nat.card (Subgroup.center Kb) := Nat.card_pos
        norm_num [Nat.factorial] at h2
        omega
    subst hm7
    obtain ⟨K₁, hK₁K, hK₁, hTK₁, hLvK₁, ⟨e6⟩⟩ := hA7 G T L V S hH K hK hYz hT hLvK h7 hblk hAm

    have hK₁G : K₁ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₁K.trans hKG
    have hz₁ : ¬ K₁ ≤ Subgroup.centralizer ({S.z} : Set G) := fun h =>
      S.not_Lv_le_centralizer_z (hLvK₁.trans h)
    have hchar₁ : CharTwo (K₁ ⊔ S.Tv) :=
      C1GN.charTwo_of_le hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hK₁G S.Tv_le_Gv)
    have hl6 : IsPSL 3 2 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨ IsAlt 6 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
        IsPSU 3 3 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := Or.inr (Or.inl ⟨e6⟩)
    have hRk₁ := SBc11.isRankTwoLie2Derived_of_list
      (isList_of_mulEquiv (quotCenterEquivOfEqBot (SBc11.center_eq_bot_of_list hl6)).symm hl6)
    have h64₁ : ¬ 64 ∣ Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
      rw [SBc11.card_of_isAlt_six ⟨e6⟩]
      norm_num
    exact S.false_of_msPair_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 h132 h134 hres hH
      ⟨hK₁G, hK₁, hTK₁, hz₁, hLvK₁, hchar₁⟩ hRk₁ h64₁
  · exact S.false_of_excA7Block_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hKG hK₀ hT hz
      hLvK (C1GN.charTwo_of_le hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right hXG) hexc
  ·
    obtain ⟨-, α, hα, hαk, -⟩ := hA6
    let eS := kbarEquivOfSurj α hα hαk
    have hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hZ : Subgroup.center Kb = ⊥ :=
      center_eq_bot_of_isSimple_of_isQuasisimple eS.isSimpleGroup hq
    have h1 : Nat.card Kb = 360 := by
      rw [Nat.card_congr eS.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩]
    rw [hcardZ, hZ, Subgroup.card_bot] at h1
    omega
  ·
    obtain ⟨-, ⟨-, -, ⟨e6⟩⟩, -, -⟩ := hHat
    have h1 := Nat.card_congr (eA.symm.trans e6).toEquiv
    rw [L246.C123.card_A7, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩] at h1
    omega

end Setting

end CFSG.Quasithin.H13.A5
