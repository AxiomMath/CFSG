module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauThreeHallFixedCentralizer
import CFSG.FeitThompson.Local.Tau13CommutingPrimeFixedEquality
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.Local.CommonFixedActionsNormalHallFactor
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05 (centralizerIn_eq)
open CFSG.FeitThompson.Prep09 (centIn_def)

universe u

variable {G : Type*} [Group G]

theorem forall_conjOnNormalized_eq_iff {V K : Subgroup G} (hVN : K ≤ normalizer (V : Set G))
    (Y : Subgroup ↥K) (h : ↥V) :
    (∀ y ∈ Y, conjOnNormalized V hVN y h = h) ↔
      (h : G) ∈ centralizer ((Y.map K.subtype : Subgroup G) : Set G) := by
  constructor
  · intro hy
    refine mem_centralizer_iff.2 ?_
    rintro g hg
    obtain ⟨y, hyY, rfl⟩ := Subgroup.mem_map.1 hg
    have hcoe := congrArg Subtype.val (hy y hyY)
    rw [conjOnNormalized_apply_coe] at hcoe
    exact mul_inv_eq_iff_eq_mul.1 hcoe
  · intro hc y hyY
    refine Subtype.ext ?_
    rw [conjOnNormalized_apply_coe]
    exact mul_inv_eq_iff_eq_mul.2
      (mem_centralizer_iff.1 hc (y : G) (Subgroup.mem_map_of_mem K.subtype hyY))

theorem setOf_conjOnNormalized_eq_iff {V K : Subgroup G} (hVN : K ≤ normalizer (V : Set G))
    (Y Z : Subgroup ↥K) :
    ({h : ↥V | ∀ y ∈ Y, conjOnNormalized V hVN y h = h}
        = {h : ↥V | ∀ y ∈ Z, conjOnNormalized V hVN y h = h}) ↔
      V ⊓ centralizer ((Y.map K.subtype : Subgroup G) : Set G)
        = V ⊓ centralizer ((Z.map K.subtype : Subgroup G) : Set G) := by
  constructor
  · intro hset
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hzV, hzc⟩
      refine ⟨hzV, (forall_conjOnNormalized_eq_iff hVN Z ⟨z, hzV⟩).1 ?_⟩
      have hz : (⟨z, hzV⟩ : ↥V) ∈ {h : ↥V | ∀ y ∈ Y, conjOnNormalized V hVN y h = h} :=
        (forall_conjOnNormalized_eq_iff hVN Y ⟨z, hzV⟩).2 hzc
      rwa [hset] at hz
    · rintro ⟨hzV, hzc⟩
      refine ⟨hzV, (forall_conjOnNormalized_eq_iff hVN Y ⟨z, hzV⟩).1 ?_⟩
      have hz : (⟨z, hzV⟩ : ↥V) ∈ {h : ↥V | ∀ y ∈ Z, conjOnNormalized V hVN y h = h} :=
        (forall_conjOnNormalized_eq_iff hVN Z ⟨z, hzV⟩).2 hzc
      rwa [← hset] at hz
  · intro heq
    ext h
    simp only [Set.mem_ofPred_eq, forall_conjOnNormalized_eq_iff hVN]
    have hmem := SetLike.ext_iff.1 heq (h : G)
    simp only [Subgroup.mem_inf] at hmem
    exact ⟨fun hh => (hmem.1 ⟨h.2, hh⟩).2, fun hh => (hmem.2 ⟨h.2, hh⟩).2⟩

theorem inf_centralizer_eq_of_semidirect [Finite G] {V J D B : Subgroup G}
    (hJV : J ≤ normalizer (V : Set G)) (hJsolv : Group.IsSolvable ↥J)
    (hDJ : D ≤ J) (hBJ : B ≤ J) (hsup : D ⊔ B = J) (hinf : D ⊓ B = ⊥)
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥B)) (hDnorm : J ≤ normalizer (D : Set G))
    (hD : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ D →
      V ⊓ centralizer (Y : Set G) = V ⊓ centralizer (D : Set G))
    (hB : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ B →
      V ⊓ centralizer (Y : Set G) = V ⊓ centralizer (B : Set G))
    (hDB : V ⊓ centralizer (D : Set G) = V ⊓ centralizer (B : Set G))
    {X : Subgroup G} (hX : X ≠ ⊥) (hXJ : X ≤ J) :
    V ⊓ centralizer (X : Set G) = V ⊓ centralizer (J : Set G) := by
  have := hJsolv
  have : (D.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDnorm
  have hmapD : (D.subgroupOf J).map J.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDJ
  have hmapB : (B.subgroupOf J).map J.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBJ
  have hmapX : (X.subgroupOf J).map J.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXJ
  have hmapTop : (⊤ : Subgroup ↥J).map J.subtype = J := by
    rw [← Subgroup.subgroupOf_self J, Subgroup.map_subgroupOf_eq_of_le le_rfl]
  have hmapne : ∀ Y : Subgroup ↥J, Y ≠ ⊥ → (Y.map J.subtype : Subgroup G) ≠ ⊥ := fun Y hY h =>
    hY ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective J)).1 h)
  have hsup' : D.subgroupOf J ⊔ B.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := D) (A' := B) hDJ hBJ, hsup, Subgroup.subgroupOf_self]
  have hinf' : D.subgroupOf J ⊓ B.subgroupOf J = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hinf]
    simp
  have hcop' : (Nat.card ↥(D.subgroupOf J)).Coprime (Nat.card ↥(B.subgroupOf J)) := by
    rwa [natCard_subgroupOf hDJ, natCard_subgroupOf hBJ]
  have hmain := fixedPoints_eq_of_semidirect_mulAut_hom (ρ := conjOnNormalized V hJV)
    hsup' hinf' hcop'
    (fun Y hY hYD => (setOf_conjOnNormalized_eq_iff hJV Y (D.subgroupOf J)).2 (by
      rw [hmapD]
      exact hD _ (hmapne Y hY) (by rw [← hmapD]; exact Subgroup.map_mono hYD)))
    (fun Y hY hYB => (setOf_conjOnNormalized_eq_iff hJV Y (B.subgroupOf J)).2 (by
      rw [hmapB]
      exact hB _ (hmapne Y hY) (by rw [← hmapB]; exact Subgroup.map_mono hYB)))
    ((setOf_conjOnNormalized_eq_iff hJV (D.subgroupOf J) (B.subgroupOf J)).2 (by
      rw [hmapD, hmapB]; exact hDB))
    (X := X.subgroupOf J) (fun h => hX (by rw [← hmapX, h, Subgroup.map_bot]))
  have htop : {h : ↥V | ∀ j : ↥J, conjOnNormalized V hJV j h = h}
      = {h : ↥V | ∀ j ∈ (⊤ : Subgroup ↥J), conjOnNormalized V hJV j h = h} := by
    ext h; simp
  rw [htop] at hmain
  have hfin := (setOf_conjOnNormalized_eq_iff hJV (X.subgroupOf J) ⊤).1 hmain
  rwa [hmapX, hmapTop] at hfin

theorem FNI_tau13_nonfree_product_fixed_centralizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_product_fixed_centralizer.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hfac hb X hXJ hXne
  have hamb04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hM : IsCoatom M := hfac.isSigmaComplement.isCoatom
  have hsd := hfac.isSigmaComplement.semidirect
  have hEM : E ≤ M := hsd.right_le
  have hE₁E : E₁ ≤ E := hfac.le_E₁
  have hE₃E : E₃ ≤ E := hfac.le_E₃
  have hsigma04 : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  have hsplit04 : _root_.CFSG.FeitThompson.IsNormalizedTauHallSplitting M E E₁ E₂ E₃ :=
    { le_E₁ := hfac.le_E₁
      le_E₂ := hfac.le_E₂
      le_E₃ := hfac.le_E₃
      isHall_E₁ := hfac.hall_E₁
      isHall_E₂ := hfac.hall_E₂
      isHall_E₃ := hfac.hall_E₃
      outer := hfac.semidirect_E
      inner := hfac.semidirect_E₂₁
      isCyclic_E₁ := hfac.isCyclic_E₁
      isCyclic_E₃ := hfac.isCyclic_E₃
      le_commutator_E₃ := hfac.le_commutator_E₃
      normal_E₂_sup_E₃ := hfac.normalizes_E₂E₃
      centralizer_E₃ := by rw [← centralizerIn_eq]; exact hfac.centralizer_E₃ }
  have hkey1 : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ E₁ →
      sigmaCore M ⊓ centralizer (Y : Set G) = sigmaCore M ⊓ centralizer (E₁ : Set G) := by
    intro Y hY hYE₁
    have h := (FTS_tau_one_hall_fixed_centralizer h₁ h₅ h₆ G hamb09 M hM E hEM hsd E₁ hE₁E
      hfac.hall_E₁).2 Y hYE₁ hY
    rwa [centIn_def, centIn_def] at h
  have hkey3 : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ E₃ →
      sigmaCore M ⊓ centralizer (Y : Set G) = sigmaCore M ⊓ centralizer (E₃ : Set G) :=
    fun Y hY hYE₃ => FNI_tau_three_hall_fixed_centralizer h₆ G hamb04 M E E₁ E₂ E₃ hsigma04
      hsplit04 Y hYE₃ hY
  obtain ⟨b, hbE₁, hbne, hbcent⟩ := hb
  have hborder : orderOf b ≠ 1 := fun h => hbne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hborder
  have hpcard : p ∣ Nat.card ↥(zpowers b) := by rw [Nat.card_zpowers]; exact hpb
  obtain ⟨x, hxb, hx⟩ := exists_mem_orderOf_eq_of_dvd hp hpcard
  have hPcard : Nat.card ↥(zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hPb : (zpowers x : Subgroup G) ≤ zpowers b := zpowers_le.2 hxb
  have hPE₁ : (zpowers x : Subgroup G) ≤ E₁ := hPb.trans (zpowers_le.2 hbE₁)
  have hPne : (zpowers x : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hpτ : p ∈ tau1Primes M := by
    refine (isHallPiSubgroup_iff.1 hfac.hall_E₁).1 p ?_
    rw [natCard_subgroupOf hE₁E]
    exact Nat.mem_primeFactors.2
      ⟨hp, (hPcard ▸ Subgroup.card_dvd_of_le hPE₁ : p ∣ Nat.card ↥E₁), Nat.card_pos.ne'⟩
  have hcentne : (E₃ ⊓ centralizer ((zpowers x : Subgroup G) : Set G) : Subgroup G) ≠ ⊥ := by
    intro h
    refine hbcent (le_bot_iff.1 ?_)
    rw [centralizerIn_eq, ← h]
    exact inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hPb))
  obtain ⟨r, hr, hrdvd⟩ : ∃ r, r.Prime ∧
      r ∣ Nat.card ↥(E₃ ⊓ centralizer ((zpowers x : Subgroup G) : Set G) : Subgroup G) :=
    Nat.exists_prime_and_dvd fun hc => hcentne (Subgroup.card_eq_one.1 hc)
  obtain ⟨y, hyC, hy⟩ := exists_mem_orderOf_eq_of_dvd hr hrdvd
  have hRcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hy]
  have hRcent : (zpowers y : Subgroup G) ≤ E₃ ⊓ centralizer ((zpowers x : Subgroup G) : Set G) :=
    zpowers_le.2 hyC
  have hRE₃ : (zpowers y : Subgroup G) ≤ E₃ := hRcent.trans inf_le_left
  have hRne : (zpowers y : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    exact hr.ne_one hRcard.symm
  have hPR := FNI_tau13_commuting_prime_fixed_equality h₁ h₂ h₃ h₄ h₅ h₆ G hamb04 M E E₁ E₂ E₃
    hsigma04 hsplit04 p r (zpowers x) (zpowers y) hpτ hPE₁ hPcard hr hRcent hRcard
  have hDB : sigmaCore M ⊓ centralizer (E₃ : Set G) = sigmaCore M ⊓ centralizer (E₁ : Set G) := by
    rw [← hkey3 _ hRne hRE₃, ← hPR, hkey1 _ hPne hPE₁]
  have hJE : (E₃ ⊔ E₁ : Subgroup G) ≤ E := sup_le hE₃E hE₁E
  have hJM : (E₃ ⊔ E₁ : Subgroup G) ≤ M := hJE.trans hEM
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hJsolv : Group.IsSolvable ↥(E₃ ⊔ E₁ : Subgroup G) := @isSolvable_of_le _ _ _ _ hJM hMsolv
  have hJV : (E₃ ⊔ E₁ : Subgroup G) ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hJM.trans (le_normalizer_sigmaCore M)
  have hinf : (E₃ ⊓ E₁ : Subgroup G) = ⊥ :=
    le_bot_iff.1 (hfac.semidirect_E.inf_eq_bot ▸
      inf_le_inf_left _ (le_sup_right : E₁ ≤ E₂ ⊔ E₁))
  have hDnorm : (E₃ ⊔ E₁ : Subgroup G) ≤ normalizer (E₃ : Set G) :=
    hJE.trans hfac.semidirect_E.le_normalizer
  have hcop : (Nat.card ↥E₃).Coprime (Nat.card ↥E₁) := by
    refine Nat.coprime_of_dvd fun k hk hk3 hk1 => ?_
    have hk3' : k ∈ tau3Primes M := by
      refine (isHallPiSubgroup_iff.1 hfac.hall_E₃).1 k ?_
      rw [natCard_subgroupOf hE₃E]
      exact Nat.mem_primeFactors.2 ⟨hk, hk3, Nat.card_pos.ne'⟩
    have hk1' : k ∈ tau1Primes M := by
      refine (isHallPiSubgroup_iff.1 hfac.hall_E₁).1 k ?_
      rw [natCard_subgroupOf hE₁E]
      exact Nat.mem_primeFactors.2 ⟨hk, hk1, Nat.card_pos.ne'⟩
    exact Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M) hk1' hk3'
  rw [centralizerIn_eq, centralizerIn_eq]
  exact inf_centralizer_eq_of_semidirect hJV hJsolv le_sup_left le_sup_right rfl hinf hcop hDnorm
    (fun Y hY hYD => hkey3 Y hY hYD) (fun Y hY hYB => hkey1 Y hY hYB) hDB hXne hXJ

end

end CFSG.FeitThompson.Proofs
