module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf57Core
public import CFSG.ClassicalInvolution.Q3.Sec13L711Mu
public import CFSG.ClassicalInvolution.Q3.TL3T28
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf66Class
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c
open Classical in

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.W_le_clique_sup {η : Set (Subgroup G)}
    (hQ8 : Sec13.Q8Omega Ω) (hη : η ∈ etaG Ω) (hWη : W = ⨆ V ∈ η, V)
    (hclC : Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) :
    ∃ w ∈ W, W ≤ (⨆ i, (ρ i).K) ⊔ Subgroup.zpowers w ∧ w * w ∈ (⨆ i, (ρ i).K) := by
  classical
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) :=
      fun x hx => exists_rep_of_mem_muDelta hx
    have : Nonempty (Rep Ω W) := ⟨ρ 0⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  set x : Fin 4 → ↥(muGroup Ω W) := fun i => T7D.imgQ (ρ i) with hx
  have hxΔ : ∀ i, x i ∈ muDelta Ω W := fun i => T7D.imgQ_mem (ρ i)
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hcomm_of : ∀ σ σ' : Rep Ω W, σ'.K ∈ omegaNbr Ω σ.K →
      T7D.imgQ σ * T7D.imgQ σ' = T7D.imgQ σ' * T7D.imgQ σ := fun σ σ' h =>
    Subtype.ext (c.comm_of_omega σ σ' h)
  have hxne : ∀ i j, i ≠ j → x i ≠ x j := fun i j hij => hne_of _ _ (hne i j hij)
  have hxC : ∀ i, x i ∈ Star3T.cent (muDelta Ω W) (x 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (hxΔ 0)
    · exact ⟨hxΔ i, (hcomm_of (ρ 0) (ρ i) (hnbr 0 i (Ne.symm hi))).symm⟩
  have hxC' : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxne 0 1 (by decide), hxne 0 2 (by decide),
        hxne 0 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 1 2 (by decide), hxne 1 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 2 3 (by decide)]), Finset.card_singleton]
  have hC4 : (Star3T.cent (muDelta Ω W) (x 0)).ncard = 4 := by
    have hsub : (↑({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (x 0) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (x 0)).ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, hxC'] at this
    rcases thompsonClique G Ω hP W c.hW hnc (x 0) (hxΔ 0) with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := exists_not_conn_of_not_connected c.hΩ c.hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) (x 0) a := by
    by_cases h : Star3T.Conn (muDelta Ω W) (x 0) d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) (x 0) a := ⟨hTT, hS, hxΔ 0, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  have hn : n = 2 := by
    have h4 : 2 ^ n = 2 ^ 2 := by rw [← hcard, hC4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hB3 : B.card = 3 := by rw [hBn, hn]
  obtain ⟨P, hP', hPB⟩ : ∃ P ∈ Star3T.cent (muDelta Ω W) (x 0), P ∉ B := by
    by_contra hall
    push Not at hall
    have h1 : (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ B.card := by
      calc (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
            Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
        _ = B.card := Set.ncard_coe_finset B
    omega
  have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP' hPB
  obtain ⟨za, g, hza, hmem, hrel⟩ := c.clique_relation' rep hrep hcfg hBC hdB hgen hP' hPB hB3
  have hcardPB : (insert P B).card = 4 := by rw [Finset.card_insert_of_notMem hPB, hB3]
  have hSeq : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) = insert P B := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hxC', hcardPB])
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have hyC : y ∈ Star3T.cent (muDelta Ω W) (x 0) := by
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    by_cases hyP : y = P
    · rw [hyP]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub y hyC hyP)
  have hKeq : ∀ i, (rep (x i)).K = (ρ i).K := fun i =>
    c.K_eq_of_img_eq (rep (x i)) (ρ i) (hrep (x i) (hxΔ i))
  have hxmem : ∀ i, x i ∈ insert P B := fun i => by
    rw [← hSeq]
    fin_cases i <;> simp [hx]
  have hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W := fun x hx => (hBC hx).1
  have hconj := hcfg.tt.exists_conj_of_not_conn hcfg.mem_d hcfg.mem_a hcfg.not_conn
  have hWle : W ≤ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) := by
    refine hWη.le.trans (iSup₂_le fun U' hU' => ?_)
    obtain ⟨J, hJD, hUJ⟩ := hQ8.exists_mem_DSet_of_mem_eta hη hU'
    have hJD' : J ∈ DSet Ω W := by rw [hWη]; exact hJD
    have hJΩ : J ∈ Ω := (hQ8.mem_RSet_iff).mp hJD'.1
    let ρ' : Rep Ω W := Q3CL.T8.mkRep hP c.hW hJΩ hJD' (Sec13.Q8Omega.isSylow2In_self (hQ8.two J hJΩ))
    have hyΔ : T7D.imgQ ρ' ∈ muDelta Ω W := T7D.imgQ_mem ρ'
    have hKy : (rep (T7D.imgQ ρ')).K = J :=
      c.K_eq_of_img_eq (rep (T7D.imgQ ρ')) ρ' (hrep (T7D.imgQ ρ') hyΔ)
    have hU'W : U' ≤ W := by rw [hWη]; exact le_iSup₂_of_le U' hU' le_rfl
    have hU'4 : Nat.card ↥U' = 4 :=
      hQ8.natCard_of_mem_USet (hQ8.mem_USet_of_mem_eta hη hU')
    have hU4 : U' ≤ c.U4 (rep (T7D.imgQ ρ')) := by
      intro z hz
      refine ⟨hKy ▸ hUJ hz, hU'W hz, ?_⟩
      have h1 := pow_card_eq_one' (G := ↥U') (x := ⟨z, hz⟩)
      rw [hU'4] at h1
      exact congrArg Subtype.val h1
    exact hU4.trans (c.U4_le_UU_of_generates rep hrep hBΔ haΔ hdB hgen hconj hyΔ)
  obtain ⟨w, hwgen⟩ := exists_zpowers_eq_inf_W c.hΩ c.hW (rep a).hR
  obtain ⟨hRW, -, -, -, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW (rep a).hR (rep a).hK
    (rep a).hRK
  have hwgen' : Subgroup.zpowers w = (rep a).K ⊓ W := by rw [hwgen, hRW]
  have hwKW : w ∈ (rep a).K ⊓ W := hwgen' ▸ Subgroup.mem_zpowers w
  have hKaD : (rep a).K ≤ Subgroup.normalizer (W : Set G) := by
    have hR := (rep a).hR.2
    rw [← Sec13.Q8Omega.eq_of_isSylow2In (hQ8.two _ (rep a).hK) (rep a).hRK]
    exact hR
  have hKaη : (rep a).K ⊓ W ∈ η := by
    have := hQ8.inf_mem_eta_of_le_normalizer hη (rep a).hK (hWη ▸ hKaD)
    rwa [← hWη] at this
  have hKa4 : Nat.card ↥((rep a).K ⊓ W) = 4 :=
    hQ8.natCard_of_mem_USet (hQ8.mem_USet_of_mem_eta hη hKaη)
  have hw4 : orderOf w = 4 := by
    rw [← Nat.card_zpowers, hwgen', hKa4]
  have hwsq : w * w = za := sq_eq_involution_of_orderOf_four hza hwKW.1 hw4
  have hPK : ∀ i, (ρ i).K ≤ ⨆ j, (ρ j).K := fun i => le_iSup (fun j => (ρ j).K) i
  refine ⟨w, hwKW.2, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨x', hx', a₁, ha₁, rfl⟩ := c.exists_mul_of_mem_UU_insert rep (hWle hg')
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
    · rw [hwgen']
      exact ⟨hx'.1, c.W4_le hx'.2⟩
    · have hUUB : c.UU rep (↑B : Set ↥(muGroup Ω W)) ≤ ⨆ i, (ρ i).K := by
        change Subgroup.closure _ ≤ _
        rw [Subgroup.closure_le]
        rintro y ⟨s, hs, hy⟩
        have hsI : s ∈ insert P B := Finset.mem_insert_of_mem (Finset.mem_coe.mp hs)
        rw [← hSeq] at hsI
        simp only [Finset.mem_insert, Finset.mem_singleton] at hsI
        have hyK : y ∈ (rep s).K := hy.1
        rcases hsI with rfl | rfl | rfl | rfl
        · exact hPK 0 (hKeq 0 ▸ hyK)
        · exact hPK 1 (hKeq 1 ▸ hyK)
        · exact hPK 2 (hKeq 2 ▸ hyK)
        · exact hPK 3 (hKeq 3 ▸ hyK)
      exact hUUB ha₁
  · rw [hwsq]
    have hr := hrel (x 0) (x 1) (x 2) (x 3) (hxne 0 1 (by decide)) (hxne 0 2 (by decide))
      (hxne 0 3 (by decide)) (hxne 1 2 (by decide)) (hxne 1 3 (by decide))
      (hxne 2 3 (by decide)) hSeq
    rw [hr]
    have hgi : ∀ i, g (x i) ∈ ⨆ j, (ρ j).K := fun i => by
      have := (hmem (x i) (hxmem i)).1.1
      exact hPK i (hKeq i ▸ this)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgi 0) (hgi 1)) (hgi 2)) (hgi 3)

end Ctx
end Thompson
end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8


open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open scoped commutatorElement


namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

namespace Pf93


section A

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}

theorem wcore_exists_W (hΩ : HypOmegaGen Ω) (hQ8 : Sec13.Q8Omega Ω) {K : Subgroup Y} {t : Y}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K t) (hperp : KPerp Ω K = twinSet Ω K)
    (hPn : TC.IsNormalTwoIn (⨆ M ∈ twinSet Ω K, M) t)
    {U : Subgroup Y} (hU : U ∈ USet Ω) (hUC : U ≤ Subgroup.centralizer ({t} : Set Y))
    (hUP : ¬ ∃ P : Subgroup Y, P ≤ Subgroup.centralizer ({t} : Set Y) ∧
      (P.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 P ∧ U ≤ P) :
    ∃ (S₁ : Sylow 2 Y) (η : Set (Subgroup Y)), η ∈ etaSet Ω (S₁ : Subgroup Y) ∧
      (∀ s ∈ (S₁ : Subgroup Y), ∀ V ∈ η, conjSub s V ∈ η) ∧
      (⨆ M ∈ twinSet Ω K, M) ≤ (S₁ : Subgroup Y) ∧ t ∈ (⨆ V ∈ η, V : Subgroup Y) ∧
      U ≤ (⨆ V ∈ η, V : Subgroup Y) := by
  set P : Subgroup Y := ⨆ M ∈ twinSet Ω K, M with hPdef
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hU2 : IsPGroup 2 U := hQ8.isPGroup_of_mem_USet hU
  have hUN : U ≤ Subgroup.normalizer (P : Set Y) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hPn.2.2 u (hUC hu) x hx, fun hx => ?_⟩
    have := hPn.2.2 u⁻¹ (C.inv_mem (hUC hu)) _ hx
    simpa [mul_assoc] using this
  have hPU : IsPGroup 2 ↥(U ⊔ P) := hU2.to_sup_of_normal_right' hPn.2.1 hUN
  obtain ⟨S₁, hS₁⟩ := hPU.exists_le_sylow
  have hUS : U ≤ (S₁ : Subgroup Y) := le_sup_left.trans hS₁
  have hPS : P ≤ (S₁ : Subgroup Y) := le_sup_right.trans hS₁
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S₁
  have hηG : η ∈ etaG Ω := ⟨S₁, hη, hinv⟩
  set W : Subgroup Y := ⨆ V ∈ η, V with hWdef
  have hWS : W ≤ (S₁ : Subgroup Y) := iSup₂_le fun V hV => (hη.1 hV).2
  have hS₁2 : IsPGroup 2 ↥(S₁ : Subgroup Y) := S₁.isPGroup'
  have hW2 : IsPGroup 2 W := hS₁2.to_le hWS
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hQ8.W_comm hηG
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have htW : t ∈ W := by
    have hKP : K ≤ P := le_iSup₂_of_le K hKtw le_rfl
    have hcard : 2 < Nat.card ↥(K ⊓ (S₁ : Subgroup Y)) := by
      rw [inf_eq_left.mpr (hKP.trans hPS), hQ8.card K hK]
      norm_num
    have hmem := hQ8.inf_mem_eta hηG hS₁2 hWS hK hcard
    have hUS' : K ⊓ W ∈ USet Ω := hQ8.mem_USet_of_mem_eta hηG hmem
    have h4 : Nat.card ↥(K ⊓ W) = 4 := hQ8.natCard_of_mem_USet hUS'
    have h2 : IsPGroup 2 ↥(K ⊓ W) := hW2.to_inf_right
    exact (T3.mem_of_isPGroup hz inf_le_left h2 (by omega)).2
  obtain ⟨J, hJ, hUJ, hcardJ, h4U⟩ := TC.Thin.exists_member_card_of_mem_USet hΩ hQ8.two hU
  have hJnot : J ∉ twinSet Ω K := by
    intro hJt
    have hJP : J ≤ P := le_iSup₂_of_le J hJt le_rfl
    refine hUP ⟨P, hPn.1, ⟨fun a ha g => ?_⟩, hPn.2.1, hUJ.trans hJP⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hPn.2.2 g g.2 a ha
  have hJK : J ≠ K := fun h => hJnot (h ▸ hKtw)
  have hJC : ¬ J ≤ C := by
    intro hJC
    have hN : J ≤ Subgroup.normalizer (K : Set Y) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ (Ne.symm hJK) hz le_rfl (hQ8.two J hJ)
        (by rw [hQ8.card J hJ]; norm_num) hJC
    have hnb : J ∈ omegaNbr Ω K :=
      ⟨hJ, hJK, J, (hQ8.mem_RSet_iff).mpr hJ, le_rfl, hN⟩
    have : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnb
    rw [hperp] at this
    exact hJnot this
  have hJCU : J ⊓ C = U := by
    have hU4 : Nat.card U = 4 := hQ8.natCard_of_mem_USet hU
    have hJ8 : Nat.card ↥J = 8 := hQ8.card J hJ
    have hle : U ≤ J ⊓ C := le_inf hUJ hUC
    have hdvd1 : Nat.card ↥(J ⊓ C) ∣ Nat.card ↥J := Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥U ∣ Nat.card ↥(J ⊓ C) := Subgroup.card_dvd_of_le hle
    have hne : J ⊓ C ≠ J := fun h => hJC (h ▸ inf_le_right)
    have hlt : Nat.card ↥(J ⊓ C) < Nat.card ↥J := by
      rcases (Subgroup.card_le_of_le (inf_le_left : J ⊓ C ≤ J)).lt_or_eq with h | h
      · exact h
      · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left h.ge) hne
    have : Nat.card ↥(J ⊓ C) = 4 := by
      rw [hU4] at hdvd2
      rw [hJ8] at hdvd1 hlt
      have h8 : Nat.card ↥(J ⊓ C) ∣ 8 := hdvd1
      interval_cases h : Nat.card ↥(J ⊓ C) <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [this, hU4])).symm
  have hUW : U ≤ W := by
    have hcardJS : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup Y)) := by
      have h1 : Nat.card ↥U ≤ Nat.card ↥(J ⊓ (S₁ : Subgroup Y)) :=
        Subgroup.card_le_of_le (le_inf hUJ hUS)
      rw [hQ8.natCard_of_mem_USet hU] at h1
      omega
    have hmem := hQ8.inf_mem_eta hηG hS₁2 hWS hJ hcardJS
    have hmemU : J ⊓ W ∈ USet Ω := hQ8.mem_USet_of_mem_eta hηG hmem
    have h4 : Nat.card ↥(J ⊓ W) = 4 := hQ8.natCard_of_mem_USet hmemU
    have hle : J ⊓ W ≤ U := by
      rw [← hJCU]
      refine le_inf inf_le_left fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm x hx.2 t htW
    have hequal : J ⊓ W = U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hQ8.natCard_of_mem_USet hU])
    rw [← hequal]
    exact inf_le_right
  exact ⟨S₁, η, hη, hinv, hPS, htW, hUW⟩

end A


end Pf93


section Final


variable {n : ℕ}

theorem v3WCore_proved (n : ℕ) : V3WCore n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hVo hO U hU hUC hUP
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := hC.partIHypG
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := hC.hyp
  have hcard8 : ∀ L ∈ Ω, Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := q8_all_of_core hC L hL L (Sec13.Q8Omega.isSylow2In_self (h2g L hL))
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ8 : Sec13.Q8Omega Ω := ⟨hΩ, h2g, hcard8, hC.aEmpty_all⟩
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hPn := v3_P_normalTwo hStd h2g
  obtain ⟨S₁, η, hη, hinv, hPS, htW, hUW⟩ :=
    Pf93.wcore_exists_W hΩ hQ8 hd.mem hd.hz hperp hPn hU hUC hUP
  have hηG : η ∈ etaG Ω := ⟨S₁, hη, hinv⟩
  set W : Subgroup Y := ⨆ V ∈ η, V with hWdef
  have hWΩ : W ∈ WSet Ω := ⟨η, hηG, rfl⟩
  have hWS : W ≤ (S₁ : Subgroup Y) := iSup₂_le fun V hV => (hη.1 hV).2
  refine ⟨W, hWΩ, htW, hUW, ?_⟩
  set P : Subgroup Y := ⨆ M ∈ twinSet Ω K, M with hPdef
  have hK₄ := hF.1
  let Ks : Fin 4 → Subgroup Y := ![K, K', K₃, K₄]
  have hKs : ∀ i, Ks i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hd.mem hd.hz
    · exact hd.hK'
    · exact hd.hK₃
    · exact hK₄
  have hKsne : ∀ i j, i ≠ j → Ks i ≠ Ks j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | simp [Ks, hd.hne, hd.hK₃K, hd.hK₃K', hF.2.1, hF.2.2.1, hF.2.2.2.1, Ne.symm hd.hne,
          Ne.symm hd.hK₃K, Ne.symm hd.hK₃K', Ne.symm hF.2.1, Ne.symm hF.2.2.1, Ne.symm hF.2.2.2.1]
  have hKsD : ∀ i, Ks i ∈ DSet Ω W := by
    intro i
    have hKΩ : Ks i ∈ Ω := (hKs i).1
    refine ⟨(hQ8.mem_RSet_iff).mpr hKΩ, ?_⟩
    exact hQ8.le_normalizer_W_of_le hηG S₁.isPGroup' hWS hKΩ
      ((le_iSup₂_of_le (Ks i) (hKs i) le_rfl).trans hPS)
  let ρ : Fin 4 → Thompson.Rep Ω W := fun i =>
    Q3CL.T8.mkRep hP hWΩ (hKs i).1 (hKsD i)
      (Sec13.Q8Omega.isSylow2In_self (h2g _ (hKs i).1))
  have hρK : ∀ i, (ρ i).K = Ks i := fun i => rfl
  have hnc : ¬ DbarConnected Ω W :=
    not_dbarConnected_of_wyl' hP hd hperp hWΩ (ρ 0) rfl (hStd.wyl W hWΩ)
  obtain ⟨w, hwW, hWle, hw2⟩ :=
    Q3CL.Thompson.Ctx.W_le_clique_sup (Q3CL.T8.ctxOf hP hWΩ) hQ8 hηG rfl hP.cls hnc ρ
      (fun i j hij => hKsne i j hij)
      (fun i j hij => adj_of_twins' hd hperp (hKs i) (hKs j) (hKsne j i (Ne.symm hij)))
  have hP4 : (⨆ i, (ρ i).K) ≤ P := iSup_le fun i => le_iSup₂_of_le (Ks i) (hKs i) le_rfl
  exact ⟨w, hwW, hWle.trans (sup_le_sup_right hP4 _), hP4 hw2⟩

end Final


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
