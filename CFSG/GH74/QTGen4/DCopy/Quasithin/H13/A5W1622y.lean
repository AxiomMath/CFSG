module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1620Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622v
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622x
public import CFSG.Quasithin.H13.A5W1620Ta

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_cases_L32_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    [hsP : IsSimpleGroup ↥(S.plus K)] (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a)
    (h168 : Nat.card ↥(S.plus K) = 168) :
    IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) ∨
      A36Case3 ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set X := modO2Image Gv K with hX
  obtain ⟨ρ, θ, hρs, hθs, hρ1, hθk⟩ := S.exists_rho_theta_F4 h1222 h517 hF hK hYz hT hna
  have hnt : Nontrivial ↥(S.plus K) := IsSimpleGroup.toNontrivial
  have hZP : Subgroup.center ↥(S.plus K) = ⊥ := by
    rcases hsP.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(S.plus K)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

  have hbot : θ.ker = ⊥ →
      IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
    intro h
    rintro ⟨k, hkK, hkC⟩
    have h1 : ρ ⟨k, hkK⟩ ∈ θ.ker := (hθk ⟨k, hkK⟩).mpr hkC
    rw [h, Subgroup.mem_bot] at h1
    obtain ⟨n, hn⟩ := hρ1 _ h1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

  have hcardX : Nat.card ↥X = Nat.card ↥θ.ker * 168 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv, h168, mul_comm]
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) hK
  rcases hA with ⟨-, hsimp, -⟩ | ⟨hcomp, h3, hlist⟩ | h3 | h4
  ·
    left
    refine hbot ?_
    rcases hsimp.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      obtain ⟨x, rfl⟩ := hθs a
      obtain ⟨y, rfl⟩ := hθs b
      have hx : θ x = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
      have hy : θ y = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y)
      exact hab (by rw [hx, hy])
  ·
    exfalso
    have hker1 : θ.ker ≤ Subgroup.center ↥X := ker_le_center_of_isQuasisimple hcomp.1 θ hθs hnt
    have hker2 : Subgroup.center ↥X ≤ θ.ker := by
      intro x hx
      have h1 : θ x ∈ Subgroup.center ↥(S.plus K) := Subgroup.map_center_le_center hθs ⟨x, hx, rfl⟩
      rw [hZP, Subgroup.mem_bot] at h1
      exact h1
    have hkerZ : θ.ker = Subgroup.center ↥X := le_antisymm hker1 hker2
    have h504 : Nat.card ↥X = 504 := by rw [hcardX, hkerZ, h3]
    have hQZ : Nat.card (↥X ⧸ Subgroup.center ↥X) = 168 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
      rw [h504, h3] at h1
      omega
    rcases hlist with ⟨s, p, e, hp, he, -, hSL⟩ | ⟨-, -, ⟨e6⟩⟩ | ⟨-, -, ⟨e7⟩⟩ | ⟨-, -, ⟨e22⟩⟩
    ·
      have hq2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := hp.two_le
          _ ≤ p ^ e := Nat.le_self_pow (by omega) p
      cases s
      · obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
        have h2 := card_statedSU_three_of hK'
        rw [← Nat.card_congr eK.toEquiv, h504] at h2
        exact (sl3_su3_card_ne hq2 (Or.inl rfl)).2 h2.symm
      · obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
        have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
        rw [← Nat.card_congr eK.toEquiv, h504, hK'] at h2
        exact (sl3_su3_card_ne hq2 (Or.inl rfl)).1 h2.symm
    · rw [Nat.card_congr e6.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩] at hQZ
      omega
    · have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      rw [Nat.card_congr e7.toEquiv, h2520] at hQZ
      omega
    · have h22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
        CFSG.Sporadic.Mathieu.card_M22
      rw [Nat.card_congr e22.toEquiv, h22] at hQZ
      omega
  · exact Or.inr h3
  ·
    exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥X) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥X))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥X := by
      ext x
      simp [ψ₄]
    have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq θ hθs hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rw [Nat.card_congr (quotCenterEquivOfEqBot hZP).toEquiv, h168] at hcard
    omega

theorem exists_reduced_L32_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) [hsP : IsSimpleGroup ↥(S.plus K)]
    (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a) (h168 : Nat.card ↥(S.plus K) = 168) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧ K₀ ∈ lFamily S.Tv ∧ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) ∧
      S.Lv ≤ Subgroup.normalizer (K₀ : Set G) ∧ autOn K₀ (S.WK K) = S.plus K ∧
      IsPGroup 2 ↥(K₀ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
  rcases S.kbar_cases_L32_F4 h1222 h517 hF h36 hK hYz hT hna h168 with h2 | h3
  · exact ⟨K, le_rfl, hYz.2.1, hT, S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK, rfl,
      h2⟩
  · exact S.exists_reduced_of_case3_F4 h1222 h517 hF h37 h38 hK hYz hT hna h168 h3

theorem false_of_L32_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4) (hres : Lem13622Case4Z0_F4)
    (hRed : Lemma13620L32Red_F4) (hH : S.Hyp1367) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF2 : Nat.card F = 2)
    (e : ↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hH.hF

  have : Fintype F := Fintype.ofFinite F
  have hcard2 : Fintype.card F = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hF2, ZMod.card]
  let ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard2
  have hL3 : ∀ {Y : Type} [Group Y], (Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) →
      IsPSL 3 2 1 Y := fun e' => Vol2Native.A312L.Seven.isPSL_three_two
    (e'.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.trans
      (slMulEquivOfRingEquiv ε 3)))
  have hlP : IsPSL 3 2 1 ↥(S.plus K) := hL3 e
  have hsP : IsSimpleGroup ↥(S.plus K) := SBc11.isSimpleGroup_of_list (Or.inl hlP)
  have h168 : Nat.card ↥(S.plus K) = 168 := SBc11.card_of_isPSL_three_two hlP
  have hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

  obtain ⟨K₀, hK₀K, hK₀, hTK₀, hLvN, hK₀im, hK₀2⟩ :=
    S.exists_reduced_L32_F4 h1222 h517 hF h36 h37 h38 hK hYz hT hna h168
  have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hYz.1
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hYz.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left : K ≤ S.HK K).trans hR.2.1
  have hTW : S.Tv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (S.Tv_le_HK K).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hz₀ : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) :=
    S.not_le_centralizer_z_of_plus_eq_F4 h1222 h517 hF hYz hT hK₀im
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hchar₀ : CharTwo (K₀ ⊔ S.Tv) :=
    C1GN.charTwo_of_le hF hsyl le_sup_right (sup_le hK₀G S.Tv_le_Gv)

  obtain ⟨α, hα⟩ := exists_isModO2Surj_of_autOn hK₀W hK₀im (by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨a, b, hab⟩) hK₀2 e
  have hl₀ : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) :=
    hL3 ((QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1))
  have hlist₀ : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨ IsAlt 6 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨
      IsPSU 3 3 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := Or.inl hl₀
  have hRk₀ := SBc11.isRankTwoLie2Derived_of_list
    (isList_of_mulEquiv (quotCenterEquivOfEqBot (SBc11.center_eq_bot_of_list hlist₀)).symm hlist₀)
  have h168₀ : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 168 := SBc11.card_of_isPSL_three_two hl₀

  have hMS := S.isMSPair_of_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀ hTK₀
    hz₀ hchar₀ hRk₀
  obtain ⟨hα', hi⟩ := S.c134_data_of_F4 h132 h134 hK₀ hTK₀ hMS h168₀

  have hWT : S.WK K ≤ S.Tv := (S.WK_le_Tv_F4 h1222 h517 hF hYz.1 hT).1
  have hWO : S.WK K ≤ pCoreOf 2 (K₀ ⊔ S.Tv) := by
    have h2 : IsPGroup 2 ↥(S.WK K) := by
      have hT2 : IsPGroup 2 ↥S.Tv := hsyl.2.1
      exact hT2.to_le hWT
    exact le_pCoreOf_of_normalizes (hWT.trans le_sup_right) (sup_le hK₀W hTW) h2
  have hsylX : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le hsyl le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hred : IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)) :=
    isTwoReducedIn_conjClosure_of_sylowIn hsylX.1 hsylX.2.1 hsylX.2.2 hchar₀ S.V1_le_omega_Tv

  have h1617 : ∀ g : G, (∀ t ∈ S.Tv,
      (g * S.z * g⁻¹) * t * (g * S.z * g⁻¹)⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12) →
      ¬ K₀ ≤ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G) := fun g haT =>
    S.not_le_centralizer_conj_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀ hTK₀
      hz₀ g haT
  have hLvK₀ : S.Lv ≤ K₀ := hRed G T L V S hH K hK hYz hT ⟨F, inferInstance, inferInstance, hF2,
    ⟨e⟩⟩ K₀ hK₀K hK₀ hTK₀ hK₀im hz₀ hchar₀ hMS hWO hred hLvN h1617 hα' hi
  exact S.false_of_msPair_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 h132 h134 hres hH
    ⟨hK₀G, hK₀, hTK₀, hz₀, hLvK₀, hchar₀⟩ hRk₀ (by rw [h168₀]; norm_num)

end Setting

end CFSG.Quasithin.H13.A5
