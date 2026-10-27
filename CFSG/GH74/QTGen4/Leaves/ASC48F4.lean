module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverFin
public import CFSG.GH74.QTGen4.Leaves.J4Branch
public import CFSG.GH74.QTGen4.Leaves.RuBranch
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.C213NonQHolds
public import CFSG.Quasithin.Background.C22PfI
public import CFSG.Quasithin.Background.C31AsmPf
public import CFSG.Quasithin.Background.C35InspAll
public import CFSG.Quasithin.Background.C35Pf
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.Background.C48AsmLineStep
public import CFSG.Quasithin.Background.C48PfD
public import CFSG.Quasithin.Background.C48PfFourModPf
public import CFSG.Quasithin.Background.F918F3
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.H13.InspC33Holds
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Vol2.KGFactC31HS
public import CFSG.Quasithin.Vol2.KGFactC31He
public import CFSG.Quasithin.Vol2.KGFactC31J1
public import CFSG.Quasithin.Vol2.KGFactC31J2
public import CFSG.Quasithin.Vol2.KGFactC31M11
public import CFSG.Quasithin.Vol2.KGFactC31M12
public import CFSG.Quasithin.Vol2.KGFactC31M23
public import CFSG.Quasithin.Vol2.KGFactC31M24

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def InspC31SporadicAtJ_Gen4 (s : TauCeti.SporadicName) : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.GH74.Gen4 A → ∀ (S M₀ R M V : Subgroup A),
    S.Normal → IsSporadic s ↥S → Subgroup.centralizer (S : Set A) = ⊥ →
    M₀ ≤ S → ⁅M₀, M₀⁆ = M₀ → M₀ ≠ ⊥ → (∃ L ∈ cComp M, M₀ = conjClosure L M) →
    IsPGroup 2 ↥R → R ≤ M → M ≤ Subgroup.normalizer (M₀ : Set A) →
    M₀ ≤ Subgroup.normalizer (R : Set A) →
    IsSylowTwoOf R (centralizerSection M M₀ (pCoreOf 2 M₀)) →
    V ≤ M₀ → V ≠ ⊥ → IsElemAbelian 2 V → ⁅V, M₀⁆ = V →
    V ≤ centerOf (pCoreOf 2 (M₀ ⊔ R)) →
    Subgroup.normalizer (V : Set A) ⊓ Subgroup.normalizer (M₀ : Set A) ≤ M →
    Subgroup.normalizer (R : Set A) ≤ M → ¬ S ≤ M →
    (s = .J4 → Subgroup.normalizer (thompsonJ R : Set A) ≤ M ∧
      Subgroup.normalizer (centerOf R : Set A) ≤ M ∧
      Subgroup.normalizer (omegaOneCenterOf (thompsonJ R) : Set A) ≤ M) →
    (C31Case3 ⊤ R M M₀ V S ∨ C31Case4 ⊤ R M M₀ V S ∨ C31Case5 ⊤ R M M₀ V S ∨
        C31Case6 ⊤ R M M₀ V S ∨ C31Case7 ⊤ R M M₀ V S ∨ C31Case8 ⊤ R M M₀ V S ∨
        C31Case9 ⊤ R M M₀ V S) ∧
      (C48Case1 ⊤ R M M₀ V S ∨ C48Case2 ⊤ R M M₀ V S ∨ C48Case3 ⊤ R M M₀ V S ∨
        C48Case4 ⊤ R M M₀ V S ∨ C48Case5 ⊤ R M M₀ V S ∨ C48Case6 ⊤ R M M₀ V S ∨
        C48Case7 ⊤ R M M₀ V S) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
        IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2

@[expose] def InspC31SporadicGen4 : Prop :=
  ∀ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) →
    InspC31SporadicAtJ_Gen4 s

end CFSG.Quasithin

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem c48SporStep_core_G4 (hG : CFSG.GH74.Gen4 G) {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (h31 : C31Basic H R M L V K) (hL : L = conjClosure L M)
    {s : TauCeti.SporadicName} (hInsp : InspC31SporadicAtJ_Gen4 s)
    (hJ : s = .J4 → C31SporJ.J4Cond (img (sporN H K) R) (img (sporN H K) M))
    (hsK : IsSporadic s (↥K ⧸ Subgroup.center ↥K))
    (hZ : Subgroup.center ↥K = ⊥ ∨
      ((Nat.card (ModO2 (conjClosure L M)) ∣ 60 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 360 ∨
          Nat.card (ModO2 (conjClosure L M)) ∣ 168 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 6048) ∧
        (IsPSL 3 2 1 (ModO2 L) → V ⊓ centerOf K = ⊥))) :
    (C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
        C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
        C48Case7 H R M L V K) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 L) →
        IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2 := by
  have hKX := K_le_sporX (H := H) hK.1
  have hsimp := isSimpleGroup_kStar hK
  have hperf := commutator_kStar hK
  have hL0 : L = conjClosure L M := hL
  have hM0ne : img (sporN H K) (conjClosure L M) ≠ ⊥ := fun hb =>
    img_V_ne_bot h h31 (le_bot_iff.mp (hb ▸ img_mono h.V_le))
  obtain ⟨-, hC48, hbound⟩ := hInsp (↥(sporX H K) ⧸ sporN H K) (CFSG.GH74.Gen4.quotient (sporN H K) (CFSG.GH74.Gen4.subgroup (sporX H K) hG)) (img (sporN H K) K)
    (img (sporN H K) (conjClosure L M)) (img (sporN H K) R) (img (sporN H K) M)
    (img (sporN H K) V) (img_K_normal H K) (IsSporadic.of_mulEquiv (kStarEquiv hKX) hsK)
    (centralizer_kStar_eq_bot (commutator_eq_of_isComponentOf hK) hKX) (img_mono h31.1)
    (img_M0_perfect h h31) hM0ne (exists_cComp_img h h31) (isPGroup_img h.pgroup)
    (img_mono h.le_M) (img_le_normalizer (le_normalizer_conjClosure L M))
    (img_le_normalizer (c2_9_two h).1) (img_isSylowTwoOf h h31) (img_mono h.V_le)
    (img_V_ne_bot h h31) (isElemAbelian_img h.V_elem) (img_V_comm h h31) (img_V_le_center h h31)
    (normalizer_inf_le_img_M h h31) (normalizer_img_R_le h h31) (not_img_K_le h hK h31) hJ
  have hcard : Nat.card (ModO2 (conjClosure L M)) =
      Nat.card (ModO2 (img (sporN H K) (conjClosure L M))) :=
    Nat.card_congr (modO2EquivL h h31).toEquiv
  have hshape : ∀ t : ℕ, (t = 2520 ∨ t = 1080 ∨ t = 20160 ∨ t = 9999360) →
      Nat.card (ModO2 (img (sporN H K) (conjClosure L M))) = t → Subgroup.center ↥K = ⊥ := by
    intro t ht htc
    rcases hZ with hZ | ⟨hdiv, -⟩
    · exact hZ
    · exfalso
      rw [hcard, htc] at hdiv
      rcases ht with rfl | rfl | rfl | rfl <;> revert hdiv <;> decide
  refine ⟨?_, ?_⟩
  · rcases hC48 with c1 | c2 | c3 | c4 | c5 | c6 | c7
    ·
      left
      obtain ⟨n, hn, hmod | hmod | hthird⟩ := c1
      · exact c48Case1_of_img h h31 hL hn (Or.inl hmod)
      · exact c48Case1_of_img h h31 hL hn (Or.inr hmod)
      · exact absurd hthird.2.1 (not_isC134Case_two (img_K_normal H K) hperf)
    ·
      right; left
      have hVK : V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
        rcases hZ with hZ | ⟨hdiv, hcov⟩
        · exact inf_centralizer_eq_bot_of_center (V_le_K h h31) hZ
        · obtain ⟨m, hm, hpsl, -⟩ := c2
          rcases hm with rfl | rfl
          · have hp : IsPSL 3 2 1 (ModO2 L) := by
              rw [hL0]
              exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm hpsl
            have h1 := hcov hp
            rw [eq_bot_iff] at h1 ⊢
            rintro v ⟨hv, hvC⟩
            exact h1 ⟨hv, V_le_K h h31 hv, hvC⟩
          · exfalso
            rw [hcard, card_of_isPSL_four_two hpsl] at hdiv
            revert hdiv
            decide
      exact c48Case2_of_img h h31 hL hVK c2
    ·
      right; right; left
      obtain ⟨hspor, hblock⟩ := c3
      refine ⟨?_, ?_⟩
      · rcases hspor with hs | hs
        · exact Or.inl (IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs)
        · exact Or.inr (IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs)
      · rw [hL0]
        exact isAltBlockType_of_img h h31 hblock
    ·
      right; right; right; left
      obtain ⟨hM23, hexc⟩ := c4
      have hZ' := hshape 2520 (Or.inl rfl) (card_modO2_of_isExcA7Block hexc)
      refine ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hM23, ?_⟩
      rw [hL0]
      exact isExcA7Block_of_img h h31 hexc
    ·
      right; right; right; right; left
      obtain ⟨hspor, hhat⟩ := c5
      have hZ' := hshape 1080 (Or.inr (Or.inl rfl)) (card_modO2_of_isHatA6Block hhat)
      refine ⟨?_, ?_⟩
      · rcases hspor with hs | hs
        · exact Or.inl (IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hs)
        · exact Or.inr (IsSporadic.of_mulEquiv (kEquivKStar hK hZ').symm hs)
      · rw [hL0]
        exact isHatA6Block_of_img h h31 hZ' hhat
    ·
      right; right; right; right; right; left
      have hZ' : Subgroup.center ↥K = ⊥ := by
        rcases hZ with hZ | ⟨hdiv, -⟩
        · exact hZ
        · exfalso
          obtain ⟨-, -, ⟨h24, -⟩ | ⟨h5, -⟩⟩ := c6
          · have h23 := dvd_card_of_isSporadic_m24 h24
            rw [← hcard] at h23
            rcases hdiv with hd | hd | hd | hd <;> have := h23.trans hd <;> revert this <;> decide
          · rw [hcard, card_of_isPSL_five_two h5] at hdiv
            revert hdiv
            decide
      exact c48Case6_of_img h hK h31 hL hZ' c6
    ·
      right; right; right; right; right; right
      obtain ⟨hRu, hG2⟩ := c7
      refine ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hRu, ?_⟩
      rw [hL0]
      exact isG2Block_of_img h h31 hG2
  ·
    intro m k hm hpsl hsum
    have hm2 : 2 ≤ m := by omega
    obtain ⟨-, hsum'⟩ := sum_img h h31 hL hm2 hsum
    have hpsl' : IsPSL m 2 1 (ModO2 (img (sporN H K) (conjClosure L M))) := by
      rw [hL0] at hpsl
      exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31) hpsl
    exact hbound m k hm hpsl' hsum'


end CFSG.Quasithin.C48Spor

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem c48SporStep_of_G4
    (h22 : ASC22One G)
    (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hCov : C48SporCoverFact G) : C48SporStep G := by
  intro H R M L V K h hK h31 hcase
  have hZ2 := isPGroup_center_of h31.2.2.2.2.1
  have hcover : (C31Case3 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case9 H R M L V K) →
      Subgroup.center ↥K = ⊥ ∨
      ((Nat.card (ModO2 (conjClosure L M)) ∣ 60 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 360 ∨
          Nat.card (ModO2 (conjClosure L M)) ∣ 168 ∨ Nat.card (ModO2 (conjClosure L M)) ∣ 6048) ∧
        (IsPSL 3 2 1 (ModO2 L) → V ⊓ centerOf K = ⊥)) := fun hc =>
    Or.inr ⟨card_modO2_dvd_of_c31Case379 h31.basic hc, hCov H R M L V K h hK h31 hc⟩
  rcases hcase with c3 | c4 | c5 | c6 | c7 | c8 | c9
  · exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .M22 (by simp)) (fun h => nomatch h) c3.1
      (hcover (Or.inl c3))
  · obtain ⟨e⟩ := c4.1
    have hZ := center_eq_bot_m23 e hZ2
    exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .M23 (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c4.1 hZ) (Or.inl hZ)
  · obtain ⟨e⟩ := c5.1
    have hZ := center_eq_bot_m24 e hZ2
    exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .M24 (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c5.1 hZ) (Or.inl hZ)
  · have hZ := center_eq_bot_j4 c6.1 hK.2.2
    exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .J4 (by simp))
      (fun _ => C31SporJ.normalizer_img_le_of_j4 h22 h hK h31.basic c6.1)
      (isSporadic_quot_of_center c6.1 hZ) (Or.inl hZ)
  · exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .HS (by simp)) (fun h => nomatch h) c7.1
      (hcover (Or.inr (Or.inl c7)))
  · have hZ := center_eq_bot_he c8.1 hK.2.2
    exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .He (by simp)) (fun h => nomatch h)
      (isSporadic_quot_of_center c8.1 hZ) (Or.inl hZ)
  · exact c48SporStep_core_G4 hG h hK h31.basic h31.1 (hInsp .Ru (by simp)) (fun h => nomatch h) c9.1
      (hcover (Or.inr (Or.inr c9)))


end CFSG.Quasithin.C48Spor

namespace CFSG.Quasithin.C31Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin
open CFSG.Quasithin.C48Spor

variable {G : Type} [Group G] [Finite G]

theorem c31SporStep_of_G4
    (hA3 : A3Orbits G)
    (h22 : ASC22One G) (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hM23 : SchurMult2M23) (hM24 : SchurMult2M24)
    (hJ4 : SchurMult2J4) (hHe : SchurMult2He) : C31SporStep G := by
  intro H R M L V K h hK h31 s hsn hsK
  have hKX := K_le_sporX (H := H) hK.1
  have hM0ne : img (sporN H K) (conjClosure L M) ≠ ⊥ := fun hb =>
    img_V_ne_bot h h31 (le_bot_iff.mp (hb ▸ img_mono h.V_le))
  have hsK' : IsSporadic s ↥(img (sporN H K) K) := IsSporadic.of_mulEquiv (kStarEquiv hKX) hsK
  have hJ : s = .J4 → C31SporJ.J4Cond (img (sporN H K) R) (img (sporN H K) M) := by
    rintro rfl
    exact C31SporJ.normalizer_img_le_of_j4 h22 h hK h31
      (IsSporadic.of_mulEquiv (kEquivKStar hK (center_eq_bot_of_img hK h31 hJ4 hsK')).symm hsK')
  obtain ⟨hC31, -, -⟩ := hInsp s hsn (↥(sporX H K) ⧸ sporN H K) (CFSG.GH74.Gen4.quotient (sporN H K) (CFSG.GH74.Gen4.subgroup (sporX H K) hG)) (img (sporN H K) K)
    (img (sporN H K) (conjClosure L M)) (img (sporN H K) R) (img (sporN H K) M)
    (img (sporN H K) V) (img_K_normal H K) hsK'
    (centralizer_kStar_eq_bot (commutator_eq_of_isComponentOf hK) hKX) (img_mono h31.1)
    (img_M0_perfect h h31) hM0ne (exists_cComp_img h h31) (isPGroup_img h.pgroup)
    (img_mono h.le_M) (img_le_normalizer (le_normalizer_conjClosure L M))
    (img_le_normalizer (c2_9_two h).1) (img_isSylowTwoOf h h31) (img_mono h.V_le)
    (img_V_ne_bot h h31) (isElemAbelian_img h.V_elem) (img_V_comm h h31) (img_V_le_center h h31)
    (normalizer_inf_le_img_M h h31) (normalizer_img_R_le h h31) (not_img_K_le h hK h31) hJ
  rcases hC31 with c3 | c4 | c5 | c6 | c7 | c8 | c9
  · have c := c31Case3_of_img h hK h31 c3
    exact ⟨eq_of_c31Case3 hA3 h h31 c, Or.inl c⟩
  · have c := c31Case4_of_img h hK h31 hM23 c4
    exact ⟨eq_of_c31Case4 hA3 h c, Or.inr (Or.inl c)⟩
  · have c := c31Case5_of_img h hK h31 hM24 c5
    exact ⟨eq_of_c31Case5 hA3 h c, Or.inr (Or.inr (Or.inl c))⟩
  · have c := c31Case6_of_img h hK h31 hJ4 c6
    exact ⟨eq_of_c31Case6 hA3 h c, Or.inr (Or.inr (Or.inr (Or.inl c)))⟩
  · have c := c31Case7_of_img h hK h31 c7
    exact ⟨eq_of_c31Case7 hA3 h h31 c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))⟩
  · have c := c31Case8_of_img h hK h31 hHe c8
    exact ⟨eq_of_c31Case8 hA3 h c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))⟩
  · have c := c31Case9_of_img h hK h31 c9
    exact ⟨eq_of_c31Case9 hA3 h h31 c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c)))))⟩


end CFSG.Quasithin.C31Spor

namespace CFSG.Quasithin.C31

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc31Statement_of_inputs_G4
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp33 : InspC33) (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hLie : C31LieStep G) :
    ASC31Statement G :=
  asc31Statement_of (C31B.c31BasicStep_of h36 h38 hA3 hSch hInsp33)
    (C31Spor.c31SporStep_of_G4 hA3 (C22Pf.asc22One_of hA37) hG hInsp schurMult2M23_holds
      schurMult2M24_holds schurMult2J4_holds schurMult2He_holds)
    C31NL.c31NonLieStep_holds hLie fun _ _ _ _ _ _ h hK => sqtkSimpleList_of_isComponentOf h.sqtk hK


end CFSG.Quasithin.C31

namespace CFSG.Quasithin.C31

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc31Statement_of_open_G4
    (hC41 : ASC41Statement G) (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hInsp35 : InspC35) :
    ASC31Statement G :=
  have hA37 := H13.a3ForSQTK_holds.1
  have hA38 := H13.a3ForSQTK_holds.2.1
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := fun K hK hq => C41Pf.outSolvable_of_isSQTKIn K hK hq
  have h22 : ASC22Statement G := C22Pf.asc22Statement_holds hA37
  have hInsp33 : InspC33 := H13.InspC33P.inspC33_holds
  asc31Statement_of_inputs_G4 H13.VolI.a36ForSQTK_holds hA37 hA38 hA3 hSch hInsp33 hG hInsp
    (C35.c31LieStep_of hInsp35 hC41 h22.1 h22.2.1 h22.2.2.2 hA3 (H13.VolI.asc129Statement_holds G)
      (asc111Statement_holds G) (asc19Statement_holds G) H13.VolI.a36ForSQTK_holds hA38 hSch
      hInsp33 schurMult2Sp4_holds schurMult2L42_holds schurMult2L52_holds)


end CFSG.Quasithin.C31

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_inputs_G4
    (hC31 : ASC31Statement G) (hC41 : ASC41Statement G)
    (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (h27 : ASC27Statement G) (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of hC31 hC41 (C48Spor.c48SporStep_of_G4 (C22Pf.asc22One_of hA37) hG hInsp hCov)
    c48C41LineStep
    (C48Pf.c48C41FourStep_of (C22Pf.asc22Three_of hA37) h27 h51 hI16 hA8 C48Pf.fourModFact_holds)
    hC129 hC111 hC19 hA3 hStep h36 h38


end CFSG.Quasithin.C48

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_open_G4
    (hC41 : ASC41Statement G) (hStep : ASC213Step G) (h27 : ASC27Statement G)
    (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hInsp35 : InspC35) (hCov : C48SporCoverFact G) :
    ASC48Statement G :=
  have hA37 := H13.a3ForSQTK_holds.1
  have hA38 := H13.a3ForSQTK_holds.2.1
  asc48Statement_of_inputs_G4 (C31.asc31Statement_of_open_G4 hC41 hG hInsp hInsp35) hC41
    (H13.VolI.asc129Statement_holds G) (asc111Statement_holds G) (asc19Statement_holds G)
    (a3Orbits_of_a37_a38 hA37 hA38) hStep H13.VolI.a36ForSQTK_holds hA37 hA38 h27 B5.asB51_holds
    asI16Cover_of asI16CoverA8_of hG hInsp hCov


end CFSG.Quasithin.C48

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_open'_G4
    (hC41 : ASC41Statement G) (hStep : ASC213Step G) (h27 : ASC27Statement G)
    (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4) (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of_open_G4 hC41 hStep h27 hG hInsp C35Pf.inspC35_holds hCov


end CFSG.Quasithin.C48

namespace CFSG.Quasithin.C48

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin


variable {G : Type} [Group G] [Finite G]

theorem asc48Statement_of_open''_G4
    (hC41 : ASC41Statement G) (h27 : ASC27Statement G) (hG : CFSG.GH74.Gen4 G) (hInsp : InspC31SporadicGen4)
    (hCov : C48SporCoverFact G) : ASC48Statement G :=
  asc48Statement_of_open'_G4 hC41 (C213NonQ.asc213Step_holds G) h27 hG hInsp hCov


end CFSG.Quasithin.C48

namespace CFSG.GH74.QTGen4.Leaves.ASC48

open CFSG.Quasithin


theorem inspC31SporadicGen4_holds
    : InspC31SporadicGen4 := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun A _ _ _ => KGC31.inspC31SporadicAt_m11.toJ A
  · exact fun A _ _ _ => KGC31.inspC31SporadicAt_m12.toJ A
  · exact fun A _ _ _ => KGC31.M22.inspC31SporadicAt_m22.toJ A
  · exact fun A _ _ _ => KGC31.M23.inspC31SporadicAt_m23.toJ A
  · exact fun A _ _ _ => KGC31.M24.inspC31SporadicAt_m24.toJ A
  · exact fun A _ _ _ => KGC31.inspC31SporadicAt_j1.toJ A
  · exact fun A _ _ _ => KGC31.inspC31SporadicAt_j2.toJ A
  · exact fun A _ _ hA S _ _ _ _ _ hS =>
      (CFSG.GH74.QTGen4.Leaves.not_isSporadic_J4_of_gen4 hA S hS).elim
  · exact fun A _ _ _ => KGC31.HS.inspC31SporadicAt_hs.toJ A
  · exact fun A _ _ _ => KGC31.He.inspC31SporadicAt_he.toJ A
  · exact fun A _ _ hA S _ _ _ _ _ hS =>
      (CFSG.GH74.QTGen4.Leaves.not_isSporadic_Ru_of_gen4 hA S hS).elim

theorem asc48Statement_F4_of
    (hC41 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC41Statement G)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC48Statement G :=
  fun G _ _ => CFSG.Quasithin.C48.asc48Statement_of_open''_G4 (hC41 G) (hC27 G)
    CFSG.GH74.QTGen4.Finite4.gen4 inspC31SporadicGen4_holds C48Cover.c48SporCoverFact_holds

end CFSG.GH74.QTGen4.Leaves.ASC48
