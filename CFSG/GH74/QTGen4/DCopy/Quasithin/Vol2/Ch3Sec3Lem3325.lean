module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3325

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

open Lem3325 Lem3331

theorem stmt3_3_25_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4) (h24 : Stmt3_3_24_F4)
    (hθ : Fact3_3_25Theta) (hXS3 : Fact3_3_25XS3) (hHat : Insp3_3_25Hat)
    (hThree : Insp3_3_25Three) : Stmt3_3_25_F4 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hodd : ∀ d ∈ D, Odd (orderOf d) := fun d hdD => by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVe : IsElemAbelian 2 (vPlus L T) := hred.2.1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hVT : vPlus L T ≤ T := hVQ.trans hQT
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hLTV
  have hCV : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hVne : vPlus L T ≠ ⊥ := by
    intro hb'
    apply h.not_L_le_centralizer h38 h39
    rw [hb']
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  set Z := quasithinOmegaOneCenter T with hZdef
  set X := oTwoUpper (L ⊓ Subgroup.centralizer (Z : Set G)) with hXdef
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hXL : X ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hTsyl : IsSylowTwoOf T (X ⊔ T) :=
    ⟨le_sup_right, hT2, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
  have hRT : R ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hRLT : R ≤ L ⊔ T :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_right hXL T)
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQR : qL L T ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hXTN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hX3 : (IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
      IsLnBlock L 3) → ∀ x ∈ L ⊓ Subgroup.centralizer (Z : Set G), Odd (orderOf x) →
      x ^ 3 = 1 := by
    intro hb x hx hxo
    obtain ⟨e⟩ := hXS3 G T M L D h hTL hb
    have hxX : x ∈ X := mem_oTwoUpper_of_odd hx hxo
    have hxXT : x ∈ X ⊔ T := Subgroup.mem_sup_left hxX
    have hS6 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide
    have h1 : e (QuotientGroup.mk ((⟨x, hxXT⟩ : ↥(X ⊔ T)) ^ 6)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hS6]
    have h2 : (⟨x, hxXT⟩ : ↥(X ⊔ T)) ^ 6 ∈ CFSG.pCore 2 ↥(X ⊔ T) := by
      rw [← QuotientGroup.eq_one_iff]
      exact e.injective (h1.trans (map_one e).symm)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(X ⊔ T))) ⟨_, h2⟩
    have hk' : x ^ (6 * 2 ^ k) = 1 := by
      have := congrArg (fun w => ((w : ↥(X ⊔ T)) : G)) (congrArg Subtype.val hk)
      simpa [pow_mul] using this
    have hdvd : orderOf x ∣ 3 * 2 ^ (k + 1) := by
      rw [show 3 * 2 ^ (k + 1) = 6 * 2 ^ k by rw [pow_succ]; ring]
      exact orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf x) (2 ^ (k + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (Nat.not_even_iff_odd.mpr hxo ∘ (even_iff_two_dvd.mpr))).symm
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)
  have part2 : tC L T ≠ ⊥ → ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      D ≤ Subgroup.normalizer (X : Set G) ∧ D ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) →
        ¬ D ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro hTC hPSL
    have hblock : IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L := by
      rcases h24 G T M L D h with hA | hH | hG | hL3
      · exact Or.inl hA
      · exact Or.inr (Or.inl hH)
      · exact Or.inr (Or.inr hG)
      · exact absurd (h.isPSL_of_isLnBlock h38 h39 hTL hL3) hPSL
    have hblock' : IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsLnBlock L 3 := by
      rcases hblock with hA | hH | hG
      · exact Or.inl hA
      · exact Or.inr (Or.inl hH)
      · exact Or.inr (Or.inr (Or.inl hG))
    obtain ⟨z, hzZ, hz1, hz2, hzL, hzT⟩ := h.exists_involution_tC hTL hTC
    have hCM : Subgroup.centralizer (Z : Set G) ≤ M := by
      have hle : Subgroup.centralizer (Z : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)
      refine hle.trans (h.toSetup331.le_of_pCoreOf_ne_bot h38 h39 ?_ ?_)
      · refine sup_le (fun l hl => ?_) (fun t ht => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hzL l hl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hzT t ht)
      · intro hbot
        have hzP : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
          refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
            (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_ ?_
          · intro y hy
            rw [Subgroup.mem_normalizer_iff]
            intro w
            have hyz : y * z = z * y := (Subgroup.mem_centralizer_singleton_iff.mp hy)
            have hc : ∀ n : ℤ, y * z ^ n * y⁻¹ = z ^ n := fun n => by
              rw [(Commute.zpow_right hyz n).eq]
              group
            constructor
            · rintro ⟨n, rfl⟩
              exact ⟨n, (hc n).symm⟩
            · rintro ⟨n, hn⟩
              have hn' : z ^ n = y * w * y⁻¹ := hn
              refine ⟨n, ?_⟩
              calc z ^ n = y⁻¹ * (y * z ^ n * y⁻¹) * y := by group
                _ = y⁻¹ * (y * w * y⁻¹) * y := by rw [hc n, hn']
                _ = w := by group
          · refine IsPGroup.of_card (n := 1) ?_
            rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
        rw [hbot] at hzP
        exact hz1 ((Subgroup.mem_bot).mp (hzP (Subgroup.mem_zpowers z)))
    have hθX : ∀ y ∈ Subgroup.centralizer (Z : Set G), y ^ 3 = 1 → y ∈ X := by
      intro y hy hy3
      by_cases hy1 : y = 1
      · rw [hy1]
        exact X.one_mem
      have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
      have hyL : y ∈ L := hθ G T M L h.toSetup331 hML hblock y (hCM hy) hyo
      exact mem_oTwoUpper_of_odd ⟨hyL, hy⟩ (by rw [hyo]; decide)
    have hDX' : ∀ d ∈ D, ∀ y ∈ X, d * y * d⁻¹ ∈ X := by
      intro d hdD y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        have hx3 := hX3 hblock' x hx.1 hx.2
        refine hθX _ (conj_mem_centralizer_omegaOneCenter (h.DN hdD) hx.1.2) ?_
        rw [conj_pow, hx3, mul_one, mul_inv_cancel]
      | one => simp
      | mul a b _ _ iha ihb => simpa [mul_assoc] using X.mul_mem iha ihb
      | inv a _ ih => simpa [mul_assoc] using X.inv_mem ih
    have hDX : D ≤ Subgroup.normalizer (X : Set G) := by
      intro d hdD
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨hDX' d hdD y, fun hy => ?_⟩
      have := hDX' d⁻¹ (D.inv_mem hdD) _ hy
      simpa [mul_assoc] using this
    have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
      intro d hdD
      have h1 : (X ⊔ T).map (MulAut.conj d).toMonoidHom = X ⊔ T := by
        rw [Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hDX hdD),
          A38.map_conj_eq_iff.mpr (h.DN hdD)]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X ⊔ T)
        (A38.map_conj_eq_iff.mp h1)
    refine ⟨hDX, hDR, fun R₀ hR₀ hR₀R hLT => ?_⟩
    exact h.not_le_normalizer h38 h39 hR₀ (hR₀R.trans hRLT) hLT
  have part1 : IsAltBlockType L 6 ∨ IsG2Block L ∨ IsLnBlock L 3 := by
    rcases h24 G T M L D h with hA | hH | hG | hL3
    · exact Or.inl hA
    · exfalso
      obtain ⟨ha, hb, hc⟩ := hHat G T M L D h hTL hH
      have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
        intro hP
        have h1 := h.card_autOn_dvd hTL
        rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP,
          Vol2.Ch11.SecA.card_of_isHat hH.2.1, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin] at h1
        revert h1
        decide
      have hTC : tC L T = ⊥ := by
        by_contra hTC
        obtain ⟨-, hDR, hno⟩ := part2 hTC hPSL
        have hAQ : ∀ A : Subgroup G, IsMaxElemAbelian R A ↔ IsMaxElemAbelian (qL L T) A := by
          intro A
          constructor
          · intro hA
            exact ⟨ha A hA, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans hQR) hBe⟩
          · intro hA
            refine ⟨hA.1.trans hQR, hA.2.1, fun B hB hBe => ?_⟩
            obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
            exact (hA₀.2.2 B hB hBe).trans (hA.2.2 A₀ (ha A₀ hA₀) hA₀.2.1)
        have hQ2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
        have hRne : R ≠ ⊥ := fun hb' => h.toSetup331.pCoreOf_ne_bot (le_bot_iff.mp (by
          rw [← hb']
          exact hQR))
        refine hno (thompsonJ R) (thompsonJ_ne_bot' hQ2 hRne)
          (iSup₂_le fun A hA => hA.1) (fun g hg => ?_) (fun d hdD => ?_)
        · refine mem_normalizer_thompsonJ fun A hA => ?_
          have h1 := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr ((hAQ A).mp hA)
          rw [A38.map_conj_eq_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg)] at h1
          exact (hAQ _).mpr h1
        · refine mem_normalizer_thompsonJ fun A hA => ?_
          have h1 := (isMaxElemAbelian_map_mulEquiv (MulAut.conj d)).mpr hA
          rwa [A38.map_conj_eq_iff.mpr (hDR hdD)] at h1
      have hVQ' := hb hTC
      obtain ⟨h1, h2, h3⟩ := hc hVQ'
      have hCV' : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = vPlus L T := by rw [hCV, hVQ']
      obtain ⟨hVmax, huniq⟩ := unique_of_offenders hVe hVT hTV hCV' h1 h2 h3
      have hDV : D ≤ Subgroup.normalizer (vPlus L T : Set G) := fun d hdD =>
        mem_normalizer_of_odd_of_unique hVmax huniq (h.DN hdD) (hodd d hdD)
      exact h.not_le_normalizer h38 h39 hVne (hVT.trans le_sup_right) hLTV hDV
    · exact Or.inr (Or.inl hG)
    · exact Or.inr (Or.inr hL3)
  have part3 : tC L T = ⊥ → vPlus L T = qL L T ∨ IsAltBlockType L 6 := by
    intro hTC
    by_contra hcon
    push Not at hcon
    obtain ⟨hVQne, hnA6⟩ := hcon
    have hblock : IsG2Block L ∨ IsLnBlock L 3 := by
      rcases part1 with hA | hG | hL3
      · exact absurd hA hnA6
      · exact Or.inl hG
      · exact Or.inr hL3
    have hshort : IsShort2 L := by
      rcases hblock with hG | hL3
      · exact hG.1
      · exact hL3.1
    obtain ⟨-, ha, hb, hc⟩ := hThree G T M L D h hTL hblock hTC hVQne
      (h.isFFModule h38 h39)
    have hFQ := h.frattini_qL_le_tC h38 h39 hshort hTL
    rw [hTC] at hFQ
    have hF : frattini ↥(qL L T) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (qL L T).subtype_injective).mp (le_bot_iff.mp hFQ)
    have hQe : IsElemAbelian 2 (qL L T) :=
      isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
    have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
      have := hQe.1
      exact setLike_mul_comm ha hb
    have hTQ : T ≤ Subgroup.normalizer (qL L T : Set G) :=
      le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hCQ : T ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
      refine le_antisymm (fun x hx => ?_) (le_inf hQT fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
      rw [← hCV]
      exact ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
    obtain ⟨hQmax, huniq⟩ := unique_of_offenders hQe hQT hTQ hCQ ha hb hc
    have hDQ : D ≤ Subgroup.normalizer (qL L T : Set G) := fun d hdD =>
      mem_normalizer_of_odd_of_unique hQmax huniq (h.DN hdD) (hodd d hdD)
    exact h.not_le_normalizer h38 h39 h.toSetup331.pCoreOf_ne_bot
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      hDQ
  exact ⟨part1, part2, part3⟩

end CFSG.Quasithin.H13
