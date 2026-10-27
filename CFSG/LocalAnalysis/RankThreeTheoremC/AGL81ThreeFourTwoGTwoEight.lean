module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSU

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.AGLEmbedding.KFactProofs.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (center_adjointGroup_eq_bot)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Generic

private theorem exists_pow_eq_one_g28 {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : IsPGroup p S) (hne : S ≠ ⊥) : ∃ x ∈ S, x ≠ 1 ∧ x ^ p = 1 := by
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  have hdvd : p ∣ Nat.card S := by
    rcases hS.card_eq_or_dvd with h | h
    · exact absurd h Finite.one_lt_card.ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨x, x.2, fun h => ?_, ?_⟩
  · have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  · have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    exact congrArg Subtype.val h1

private theorem eq_bot_of_perfect_le_zpowers_g28 {G : Type*} [Group G] {L : Subgroup G} {z : G}
    (hL : L ≤ Subgroup.zpowers z) (hp : ⁅L, L⁆ = L) : L = ⊥ := by
  have hc : ⁅Subgroup.zpowers z, Subgroup.zpowers z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self z j i).eq
  rw [← hp]
  exact le_bot_iff.mp ((Subgroup.commutator_mono hL hL).trans hc.le)

private theorem pullback_g28 {X Y : Type*} [Group X] [Group Y] {ι : X →* Y}
    (hι : Function.Injective ι) {K Y₀ J : Subgroup Y} (hrange : ι.range = K) (hJ : J ≤ K ⊓ Y₀)
    (hne : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J (K ⊓ Y₀)) :
    Nonempty (J.comap ι ≃* J) ∧ J.comap ι ≠ ⊥ ∧ ⁅J.comap ι, J.comap ι⁆ = J.comap ι ∧
      IsSubnormal (J.comap ι) (Y₀.comap ι) := by
  have hJK : J ≤ ι.range := hrange ▸ hJ.trans inf_le_left
  have hmap : (J.comap ι).map ι = J := Subgroup.map_comap_eq_self hJK
  have hKι : K.comap ι = ⊤ := by
    rw [← hrange, MonoidHom.comap_range_self]
  refine ⟨⟨(Subgroup.equivMapOfInjective (J.comap ι) ι hι).trans (MulEquiv.subgroupCongr hmap)⟩,
    ?_, ?_, ?_⟩
  · intro hbot
    apply hne
    rw [← hmap, hbot, Subgroup.map_bot]
  · apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmap, hJp]
  · have h := hJs.comap ι
    rwa [Subgroup.comap_inf, hKι, top_inf_eq] at h

private theorem mul_conj_mul_inv_g28 {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem eq_one_of_mem_centralizer_g28 {X Y : Type*} [Group X] [Group Y] {K : Subgroup Y}
    (e : K ≃* X) (hZ : Subgroup.center X = ⊥) {c : Y} (hcK : c ∈ K)
    (hcC : c ∈ Subgroup.centralizer (K : Set Y)) : c = 1 := by
  have hc : e ⟨c, hcK⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC k k.2)
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : (⟨c, hcK⟩ : K) = 1 := e.injective (hc.trans (map_one e).symm)
  exact congrArg Subtype.val h1

end Generic

section Model

attribute [local irreducible] txL tU tZ tO tzc gW


variable {F : Type} [Field F] [Finite F] [CharP F 2] (M : G28Model F)

private theorem txElt_inj_g28 {i j : ℕ} (hi : i < 243) (hj : j < 243)
    (h : txElt M i = txElt M j) : i = j := by
  have hc := (M.eq_iff_codes (valid_txL hi) (valid_txL hj) (rho_txElt M hi)
    (rho_txElt M hj)).1 h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact txL_spec.2.2.1 j hj i hlt hc.symm
  · exact txL_spec.2.2.1 i hi j hlt hc

private theorem aElt_eq_txElt_g28 {t : ℕ} (ht : t < 81) :
    aElt M t = txElt M (27 * (t / 9) + 3 * (t % 9)) := by
  have e1 : (27 * (t / 9) + 3 * (t % 9)) / 27 = t / 9 := by omega
  have e2 : (27 * (t / 9) + 3 * (t % 9)) / 3 % 9 = t % 9 := by omega
  have e3 : (27 * (t / 9) + 3 * (t % 9)) % 3 = 0 := by omega
  rw [aElt, txElt, e1, e2, e3, pow_zero, mul_one]

private theorem bE_notMem_Asub_g28 : bE M tB1 ∉ Asub M := by
  rintro ⟨t, ht, hbt⟩
  have h1 : txElt M tB1 = txElt M (27 * (t / 9) + 3 * (t % 9)) :=
    (eq_aElt_of_rho M ht hbt).trans (aElt_eq_txElt_g28 M ht)
  have h2 := txElt_inj_g28 M (by decide) (by omega) h1
  have h3 : tB1 = 55 := rfl
  omega

private theorem mem_zpowers_zE_of_central_g28 {x : adjointGroup .G2 F} (hx : x ∈ TX M)
    (hc : ∀ t ∈ TX M, x * t = t * x) (hx3 : x ^ 3 = 1) : x ∈ Subgroup.zpowers (zE M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : tzE M ^ 3 ∈ TX M := Subgroup.pow_mem _ (tzE_mem_TX M) 3
  have hxA : x ∈ Asub M := by
    by_contra hxA
    exact comp_TX M x hx hxA hx3 (hc _ (zE_mem_TX M)) (hc _ hz3)
  by_contra hxz
  have hb : bE M tB1 ∈ TX M := bE_mem_TX M (by decide)
  obtain ⟨hW, hWc⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (isElemAbelian_zpowers' (zE_pow_three M)) hxz hx3 (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (hc _ (Subgroup.zpow_mem _ (zE_mem_TX M) k)).symm)
  set W := Subgroup.zpowers (zE M) ⊔ Subgroup.zpowers x
  have hzA : zE M ∈ Asub M := by
    rw [zE_eq_aElt]
    exact aElt_mem M (by norm_num)
  have hWA : W ≤ Asub M := sup_le (Subgroup.zpowers_le.mpr hzA) (Subgroup.zpowers_le.mpr hxA)
  have hWS : (W : Set (adjointGroup .G2 F)) ⊆ (S9 M : Set (adjointGroup .G2 F)) := fun w hw =>
    omega_S9 M w (hWA hw) (hW.2 w hw)
  have hcardW : Nat.card W = 9 := by rw [hWc, Nat.card_zpowers, orderOf_zE]
  have hnc : Nat.card W = (W : Set (adjointGroup .G2 F)).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have hWeq : (W : Set (adjointGroup .G2 F)) = (S9 M : Set (adjointGroup .G2 F)) := by
    refine Set.eq_of_subset_of_ncard_le hWS ?_ (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, card_S9, ← hnc, hcardW]
  have htz : tzE M ^ 3 ∈ W := by
    have h : tzE M ^ 3 ∈ (W : Set (adjointGroup .G2 F)) := by
      rw [hWeq]
      exact tzE_pow_three_mem_S9 M
    exact h
  have hbW : W ≤ Subgroup.centralizer {bE M tB1} := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact zE_comm_bE M cert_q1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc _ hb
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hbW htz)
  exact comp_TX M _ hb (bE_notMem_Asub_g28 M) (bE_pow_three M cert_q1)
    (zE_comm_bE M cert_q1).symm h1.symm

private noncomputable def TXSylow_g28 (hF : Nat.card F = 8) : Sylow 3 (adjointGroup .G2 F) :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard (TX M) (by
    rw [card_TX M, factorization_eq_of_mul (card_X' hF) (by norm_num)]
    norm_num)

private theorem commutator_SX_le_VX_g28 : ⁅SX M, SX M⁆ ≤ VX M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [mem_VX_iff, commutatorElement_def]
  rcases cen_or_inv M ha with h1 | h1 <;> rcases cen_or_inv M hb with h2 | h2
  · exact ((h1.mul h2).mul h1.inv').mul h2.inv'
  · exact ((h1.mul_inv h2).mul_cen h1.inv').mul_inv h2.inv'
  · exact ((h1.mul_cen h2).mul_inv h1.inv').mul h2.inv'
  · exact ((h1.mul_inv h2).mul_inv h1.inv').mul_inv h2.inv'

private theorem le_or_eq_of_isSubnormal_VX_g28 (hSU : SUStruct M)
    {L : Subgroup (adjointGroup .G2 F)} (hL : IsSubnormal L (VX M)) :
    L ≤ Subgroup.zpowers (zE M) ∨ L = VX M := by
  generalize hV : VX M = V at hL
  induction hL with
  | refl H => exact Or.inr rfl
  | @step H N U hHN hn _ ih =>
    rcases ih hV with h | h
    · exact Or.inl (hHN.trans h)
    · subst h
      subst hV
      have hN : VX M ≤ Subgroup.normalizer (H : Set (adjointGroup .G2 F)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).1 hn
      rcases hSU.2.1 H hHN hN with h | h | h
      · exact Or.inl (h ▸ bot_le)
      · exact Or.inl h
      · exact Or.inr h

private theorem eq_VX_of_isSubnormal_SX_g28 (hSU : SUStruct M)
    {L : Subgroup (adjointGroup .G2 F)} (hL : IsSubnormal L (SX M)) (hne : L ≠ ⊥)
    (hp : ⁅L, L⁆ = L) : L = VX M := by
  have hLV : L ≤ VX M := by
    rw [← hp]
    exact (Subgroup.commutator_mono hL.le hL.le).trans (commutator_SX_le_VX_g28 M)
  have hsub : IsSubnormal L (VX M) := by
    have h := hL.inf_of_le (VX_le_SX M)
    rwa [inf_eq_left.mpr hLV] at h
  rcases le_or_eq_of_isSubnormal_VX_g28 M hSU hsub with h | h
  · exact absurd (eq_bot_of_perfect_le_zpowers_g28 h hp) hne
  · exact h


private theorem isSimpleGroup_X_g28 (hF : Nat.card F = 8) : IsSimpleGroup (adjointGroup .G2 F) :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := F)
      (by rw [hF]; norm_num))
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm

private theorem exists_ne_comm_X_g28 (hF : Nat.card F = 8) :
    ∃ a b : adjointGroup .G2 F, a * b ≠ b * a := by
  haveI := isSimpleGroup_X_g28 hF
  by_contra h
  push Not at h
  have htop : Subgroup.center (adjointGroup .G2 F) = ⊤ :=
    eq_top_iff.mpr fun a _ => Subgroup.mem_center_iff.mpr fun b => h b a
  rw [center_adjointGroup_eq_bot] at htop
  exact bot_ne_top htop

private theorem isSolvable_outer_X_g28 (hF : Nat.card F = 8) :
    Group.IsSolvable (Outer (adjointGroup .G2 F)) := by
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup .G2 F)) = Nat.card (adjointGroup .G2 F) :=
    Nat.card_range_of_injective conj_injective_X
  have hcard : Nat.card (Outer (adjointGroup .G2 F)) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 F))
    rw [card_aut hF, hinner] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (Outer (adjointGroup .G2 F)) := isCyclic_of_prime_card hcard
  infer_instance

end Model

section Action

private theorem mem_centralizer_of_actHom_eq_one_g28 {Y X : Type} [Group Y] [Group X]
    (K : Subgroup Y) [K.Normal] (e : K ≃* X) {y : Y} (hy : actHom K e y = 1) :
    y ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := actHom_apply K e y (e ⟨k, hk⟩)
  rw [hy] at h
  simp only [MulAut.one_apply, MulEquiv.symm_apply_apply] at h
  have h' : y * k * y⁻¹ = k := h.symm
  calc k * y = (y * k * y⁻¹) * y := by rw [h']
    _ = y * k := by group

private theorem actHom_trans_g28 {Y X : Type} [Group Y] [Group X] (K : Subgroup Y) [K.Normal]
    (e : K ≃* X) (α : MulAut X) (y : Y) :
    actHom K (e.trans α) y = α * actHom K e y * α⁻¹ := by
  ext x
  simp [actHom, MulAut.mul_apply, MulAut.inv_apply]

private theorem actHom_coe_g28 {Y X : Type} [Group Y] [Group X] (K : Subgroup Y) [K.Normal]
    (e : K ≃* X) (k : K) : actHom K e (k : Y) = MulAut.conj (e k) := by
  have h := actHom_inner K e (e k)
  rwa [MulEquiv.symm_apply_apply] at h

end Action

section Core

attribute [local irreducible] txL tU tZ tO tzc gW


variable {F : Type} [Field F] [Finite F] [CharP F 2] (M : G28Model F)

private theorem exists_equiv_map_TX_g28 (hF : Nat.card F = 8) {Y : Type} [Group Y] [Finite Y]
    {K : Subgroup Y} [K.Normal] (R : Sylow 3 Y) (e : K ≃* adjointGroup .G2 F) :
    ∃ ε : K ≃* adjointGroup .G2 F,
      (TX M).map (K.subtype.comp ε.symm.toMonoidHom) = (R : Subgroup Y) ⊓ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 F) (Sylow.mapSurjective hs T)
    (TXSylow_g28 M hF)
  set ε : K ≃* adjointGroup .G2 F := e.trans (MulAut.conj g) with hε
  have hεT : (T : Subgroup K).map ε.toMonoidHom = TX M := by
    have h1 := congrArg (fun P : Sylow 3 (adjointGroup .G2 F) =>
      (P : Subgroup (adjointGroup .G2 F))) hg
    have h2 : ((TXSylow_g28 M hF : Sylow 3 (adjointGroup .G2 F)) :
        Subgroup (adjointGroup .G2 F)) = TX M := rfl
    simp only [Sylow.coe_subgroup_smul, h2, Sylow.coe_mapSurjective] at h1
    rw [← h1]
    change Subgroup.map ε.toMonoidHom (T : Subgroup K) =
      Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map e.toMonoidHom (T : Subgroup K))
    rw [Subgroup.map_map]
    rfl
  refine ⟨ε, ?_⟩
  have h1 : ((T : Subgroup K).map ε.toMonoidHom).map ε.symm.toMonoidHom = T := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (T : Subgroup K)
    ext x
    simp
  rw [← hT, ← hεT, ← Subgroup.map_map, h1]

private theorem gElt_mem_of_witness_g28 {Y : Type} [Group Y] [Finite Y] {K Y₀ : Subgroup Y}
    (R : Sylow 3 Y) (ι : adjointGroup .G2 F →* Y) (hι : Function.Injective ι)
    (hιK : ι.range ≤ K) (hTR : (TX M).map ι ≤ R)
    (hcore : GLBWeakCore 3 (R : Subgroup Y) ≤ Y₀)
    (hw : ∀ j < 4, ∃ w ∈ (R : Subgroup Y), w ∉ K ∧ w ^ 3 = 1 ∧
      ∀ q ∈ QX M (bIdx j), w * ι q = ι q * w) :
    ∀ j < 4, ι (gElt M j) ∈ Y₀ := by
  intro j hj
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hwR, hwK, hw3, hwc⟩ := hw j hj
  have hq : qOK txL tzc (bIdx j) (if j < 2 then tY1 else tY2) = true := by
    unfold bIdx
    split_ifs
    exacts [cert_q1, cert_q2]
  obtain ⟨hQe, hQc⟩ := QX_spec M hq
  set Q : Subgroup Y := (QX M (bIdx j)).map ι
  have hQe' : IsElemAbelian 3 Q :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ι _ hQe
  have hQc' : Nat.card Q = 9 := by rw [Subgroup.card_map_of_injective hι, hQc]
  have hQR : Q ≤ R := (Subgroup.map_mono (QX_le_TX M hq (bIdx_lt j))).trans hTR
  have hQK : Q ≤ K := (Subgroup.map_le_range ι _).trans hιK
  have hcomm : ∀ a ∈ Q, a * w = w * a := by
    rintro _ ⟨q, hq', rfl⟩
    exact (hwc q hq').symm
  obtain ⟨hE, hEc⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hQe'
    (fun h => hwK (hQK h)) hw3 hcomm
  have hEle : Q ⊔ Subgroup.zpowers w ≤
      Q ⊔ ((R : Subgroup Y) ⊓ Subgroup.centralizer (Q : Set Y)) :=
    sup_le_sup_left (Subgroup.zpowers_le.mpr
      (Subgroup.mem_inf.mpr ⟨hwR, Subgroup.mem_centralizer_iff.mpr hcomm⟩)) Q
  have h3 : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ ((R : Subgroup Y) ⊓ Subgroup.centralizer (Q : Set Y))) :=
    three_le_pRank_of_card_27 hEle hE (by rw [hEc, hQc'])
  have h2 : 2 ≤ CFSG.Open.pRank 3 Q := two_le_pRank_of_card_9 le_rfl hQe' hQc'
  refine hcore (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 hQR h2 h3 ?_)
  exact Subgroup.le_normalizer_map ι
    (Subgroup.mem_map_of_mem ι (mem_normalizer_of_conj_le (gElt_normalizes_QX M hj)))

private theorem gElt_mem_of_centralizer_g28 (hF : Nat.card F = 8) {Y : Type} [Group Y]
    [Finite Y] {K Y₀ : Subgroup Y} [K.Normal] (e : K ≃* adjointGroup .G2 F) (R : Sylow 3 Y)
    (hcore : GLBWeakCore 3 (R : Subgroup Y) ≤ Y₀) {c : Y} (hcR : c ∈ (R : Subgroup Y))
    (hcC : c ∈ Subgroup.centralizer (K : Set Y)) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) :
    ∃ ε : K ≃* adjointGroup .G2 F, ∀ j < 4, ((ε.symm (gElt M j) : K) : Y) ∈ Y₀ := by
  obtain ⟨ε, hιT⟩ := exists_equiv_map_TX_g28 M hF R e
  have hcK : c ∉ K := fun h =>
    hc1 (eq_one_of_mem_centralizer_g28 e (center_adjointGroup_eq_bot (τ := .G2) (K := F)) h hcC)
  refine ⟨ε, gElt_mem_of_witness_g28 M R (K.subtype.comp ε.symm.toMonoidHom)
    (K.subtype_injective.comp ε.symm.injective) ?_ (hιT.le.trans inf_le_left) hcore
    fun j _ => ⟨c, hcR, hcK, hc3, fun q _ => ?_⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact (ε.symm x).2
  · exact (Subgroup.mem_centralizer_iff.mp hcC _ (ε.symm q).2).symm

private theorem gElt_mem_of_inf_eq_bot_g28 (hF : Nat.card F = 8) {Y : Type} [Group Y]
    [Finite Y] {K Y₀ : Subgroup Y} [K.Normal] (e : K ≃* adjointGroup .G2 F) (R : Sylow 3 Y)
    (hcore : GLBWeakCore 3 (R : Subgroup Y) ≤ Y₀)
    (hRC : (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    (h3 : 3 ≤ CFSG.Open.pRank 3 (R : Subgroup Y)) :
    ∃ ε : K ≃* adjointGroup .G2 F, ∀ j < 4, ((ε.symm (gElt M j) : K) : Y) ∈ Y₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c := actHom K e
  have hinjR : Function.Injective (c.comp (R : Subgroup Y).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have h1 : (r : Y) ∈ (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) :=
      ⟨r.2, mem_centralizer_of_actHom_eq_one_g28 K e hr⟩
    rw [hRC, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTcard : Nat.card T = 3 ^ 5 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      factorization_eq_of_mul (card_X' hF) (by norm_num)]
  have hRK : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = 3 ^ 5 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  have hcardA : Nat.card (MulAut (adjointGroup .G2 F)) = 3 ^ 6 * 17816092672 := by
    rw [card_aut hF, card_X' hF]
    ring
  have hRcard : Nat.card (R : Subgroup Y) = 3 ^ 6 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
    have hdvd : Nat.card (R : Subgroup Y) ∣ 3 ^ 6 * 17816092672 := by
      rw [← hcardA, ← Nat.card_range_of_injective hinjR]
      exact Subgroup.card_subgroup_dvd_card (c.comp (R : Subgroup Y).subtype).range
    rw [hn] at hdvd
    have hle : n ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
      ((Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 17816092672)).dvd_of_dvd_mul_right
        hdvd)
    have hge : 5 ≤ n := by
      have h1 : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) ∣ Nat.card (R : Subgroup Y) :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hRK, hn] at h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
    have hne5 : n ≠ 5 := by
      rintro rfl
      have hRle : (R : Subgroup Y) ≤ K := by
        have h1 : (R : Subgroup Y) ⊓ K = R :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hRK, hn])
        rw [← h1]
        exact inf_le_right
      obtain ⟨B, hBR, hB, hB27⟩ := exists_elemAbelian_27 h3
      have hBK : B ≤ K := hBR.trans hRle
      have hB' : IsElemAbelian 3 ((B.comap K.subtype).map e.toMonoidHom) :=
        CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
          (isElemAbelian_comap_injective K.subtype K.subtype_injective hB)
      have hB'c : Nat.card ((B.comap K.subtype).map e.toMonoidHom) = 27 := by
        have h1 : (B.comap K.subtype).map K.subtype = B :=
          Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hBK)
        have h2 : Nat.card ((B.comap K.subtype).map K.subtype) = Nat.card (B.comap K.subtype) :=
          Subgroup.card_map_of_injective K.subtype_injective
        rw [h1] at h2
        rw [Subgroup.card_map_of_injective e.injective, ← h2, hB27]
      exact no_elemAbelian_27_X M hF hB' hB'c
    rw [hn, show n = 6 by omega]
  have hRb : Nat.card (c.comp (R : Subgroup Y).subtype).range = 3 ^ 6 :=
    (Nat.card_range_of_injective hinjR).trans hRcard
  let P : Sylow 3 (MulAut (adjointGroup .G2 F)) :=
    Sylow.ofCard (c.comp (R : Subgroup Y).subtype).range
      (by rw [hRb, factorization_eq_of_mul hcardA (by norm_num)])
  obtain ⟨α, hα⟩ := MulAction.exists_smul_eq (MulAut (adjointGroup .G2 F)) P (T0Sylow M hF)
  set ε : K ≃* adjointGroup .G2 F := e.trans α with hεdef
  have hT0 : ∀ t, t ∈ T0 M hF ↔ ∃ r ∈ (R : Subgroup Y), actHom K ε r = t := by
    intro t
    have h1 := congrArg (fun P : Sylow 3 (MulAut (adjointGroup .G2 F)) =>
      (P : Subgroup (MulAut (adjointGroup .G2 F)))) hα
    simp only [Sylow.coe_subgroup_smul, coe_T0Sylow] at h1
    rw [← h1]
    change t ∈ Subgroup.map (MulAut.conj α).toMonoidHom (c.comp (R : Subgroup Y).subtype).range ↔
      _
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, r.2, by rw [hεdef, actHom_trans_g28]; rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨c r, ⟨⟨r, hr⟩, rfl⟩, by rw [hεdef, actHom_trans_g28]; rfl⟩
  have hmk0 : ∀ g : adjointGroup .G2 F,
      (MulAut.conj g : MulAut (adjointGroup .G2 F)) = KFactProofs.G28.mk g 0 := fun g => by
    simp [KFactProofs.G28.mk]
  have hεT : (T : Subgroup K).map ε.toMonoidHom = TX M := by
    have hle : (T : Subgroup K).map ε.toMonoidHom ≤ TX M := by
      rintro _ ⟨t, ht, rfl⟩
      have htR : (t : Y) ∈ (R : Subgroup Y) := by
        have h1 : (t : Y) ∈ (R : Subgroup Y) ⊓ K := hT ▸ Subgroup.mem_map_of_mem K.subtype ht
        exact h1.1
      obtain ⟨g, hg, i, hi, hgi⟩ := (mem_T0_iff M hF _).mp ((hT0 _).mpr ⟨t, htR, rfl⟩)
      rw [actHom_coe_g28, hmk0] at hgi
      have h2 := (mk_inj hF (by norm_num) hi hgi).1
      change ε t ∈ TX M
      rw [h2]
      exact hg
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_TX M, Subgroup.card_map_of_injective ε.injective, hTcard]
    norm_num
  set ι : adjointGroup .G2 F →* Y := K.subtype.comp ε.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hιT : (TX M).map ι = (R : Subgroup Y) ⊓ K := by
    have h1 : ((T : Subgroup K).map ε.toMonoidHom).map ε.symm.toMonoidHom = T := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (T : Subgroup K)
      ext x
      simp
    rw [← hT, ← hεT, hιdef, ← Subgroup.map_map, h1]
  refine ⟨ε, gElt_mem_of_witness_g28 M (K := K) R ι hι ?_ (hιT.le.trans inf_le_left) hcore ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (ε.symm x).2
  · intro j hj
    have hq : qOK txL tzc (bIdx j) (if j < 2 then tY1 else tY2) = true := by
      unfold bIdx
      split_ifs
      exacts [cert_q1, cert_q2]
    have hyi : (if j < 2 then tY1 else tY2) < 243 := by split_ifs <;> decide
    obtain ⟨r, hrR, hr⟩ := (hT0 _).mp (yA_mem_T0 M hF hyi)
    refine ⟨r, hrR, fun hrK => ?_, ?_, fun q hq' => ?_⟩
    ·
      have h1 := actHom_coe_g28 K ε ⟨r, hrK⟩
      rw [hr, hmk0, yA] at h1
      exact absurd (mk_inj hF (by norm_num) (by norm_num) h1).2 (by norm_num)
    ·
      have h1 : actHom K ε (r ^ 3) = 1 := by rw [map_pow, hr, yA_pow_three M hq hF]
      have h2 : r ^ 3 ∈ (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) :=
        ⟨Subgroup.pow_mem _ hrR 3, mem_centralizer_of_actHom_eq_one_g28 K ε h1⟩
      rw [hRC, Subgroup.mem_bot] at h2
      exact h2
    ·
      have h1 := yA_comm_QA M hq hF (MulAut.conj q) ⟨q, hq', rfl⟩
      have h2 : yA M (if j < 2 then tY1 else tY2) q = q := by
        apply conj_injective_X (K := F)
        rw [← mul_conj_mul_inv_g28, ← h1, mul_inv_cancel_right]
      have h3 := actHom_apply K ε r q
      rw [hr, h2] at h3
      change r * ((ε.symm q : K) : Y) = ((ε.symm q : K) : Y) * r
      calc r * ((ε.symm q : K) : Y) = (r * ((ε.symm q : K) : Y) * r⁻¹) * r := by group
        _ = ((ε.symm q : K) : Y) * r := by rw [← h3]

private theorem gElt_mem_of_not_three_le_g28 (hF : Nat.card F = 8) {Y : Type} [Group Y]
    [Finite Y] {K Y₀ E : Subgroup Y} [K.Normal] (e : K ≃* adjointGroup .G2 F) (R : Sylow 3 Y)
    (hER : E ≤ R) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hcore : GLBCore 3 1 E ≤ Y₀) (h3 : ¬ 3 ≤ CFSG.Open.pRank 3 (R : Subgroup Y)) :
    ∃ ε : K ≃* adjointGroup .G2 F, ∀ j < 4, ((ε.symm (gElt M j) : K) : Y) ∈ Y₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε, hιT⟩ := exists_equiv_map_TX_g28 M hF R e
  set ι : adjointGroup .G2 F →* Y := K.subtype.comp ε.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hιR : ∀ t ∈ TX M, ι t ∈ (R : Subgroup Y) ⊓ K := fun t ht =>
    hιT ▸ Subgroup.mem_map_of_mem ι ht
  have hne : K.subgroupOf (R : Subgroup Y) ≠ ⊥ := by
    intro hbot
    have hz : ι (zE M) ∈ (R : Subgroup Y) ⊓ K := hιR _ (zE_mem_TX M)
    have h1 : (⟨ι (zE M), hz.1⟩ : (R : Subgroup Y)) ∈ K.subgroupOf (R : Subgroup Y) := hz.2
    rw [hbot, Subgroup.mem_bot] at h1
    exact zE_ne_one M (hι ((congrArg Subtype.val h1).trans (map_one ι).symm))
  haveI : Group.IsNilpotent (R : Subgroup Y) := R.isPGroup'.isNilpotent
  have hS := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨x, hxS, hx1, hx3⟩ := exists_pow_eq_one_g28 (R.isPGroup'.to_subgroup _) hS
  set z₀ : Y := ((x : (R : Subgroup Y)) : Y) with hz₀
  have hz₀K : z₀ ∈ K := hxS.1
  have hz₀R : z₀ ∈ (R : Subgroup Y) := x.2
  have hz₀Z : ∀ r ∈ (R : Subgroup Y), z₀ * r = r * z₀ := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hxS.2 ⟨r, hr⟩).symm
  have hz₀3 : z₀ ^ 3 = 1 := by rw [hz₀, ← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hz₀1 : z₀ ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hz₀E : z₀ ∈ E := by
    by_contra hz
    obtain ⟨hB, hBc⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE hz hz₀3
      (fun a ha => (hz₀Z a (hER ha)).symm)
    exact h3 (three_le_pRank_of_card_27 (sup_le hER (Subgroup.zpowers_le.mpr hz₀R)) hB
      (by rw [hBc, hEc]))
  have hN : Subgroup.normalizer (Subgroup.zpowers z₀ : Set Y) ≤ Y₀ := by
    refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff 3 1 E Y₀).mp hcore _
      (Subgroup.zpowers_le.mpr hz₀E) ?_
    exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨_, le_rfl, isElemAbelian_zpowers' hz₀3,
        by rw [Nat.card_zpowers, orderOf_eq_prime hz₀3 hz₀1, pow_one]⟩
  set x₀ : adjointGroup .G2 F := ε ⟨z₀, hz₀K⟩ with hx₀
  have hx₀z : ι x₀ = z₀ := by simp [hιdef, hx₀]
  have hx₀T : x₀ ∈ TX M := by
    have h1 : z₀ ∈ (TX M).map ι := hιT ▸ ⟨hz₀R, hz₀K⟩
    obtain ⟨t, ht, hte⟩ := h1
    have h2 : t = x₀ := hι (hte.trans hx₀z.symm)
    exact h2 ▸ ht
  have hx₀c : ∀ t ∈ TX M, x₀ * t = t * x₀ := by
    intro t ht
    apply hι
    rw [map_mul, map_mul, hx₀z]
    exact hz₀Z _ (hιR t ht).1
  have hx₀3 : x₀ ^ 3 = 1 := hι (by rw [map_pow, hx₀z, hz₀3, map_one])
  have hx₀1 : x₀ ≠ 1 := fun h => hz₀1 (by rw [← hx₀z, h, map_one])
  have hzp : Subgroup.zpowers x₀ = Subgroup.zpowers (zE M) := by
    refine Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (mem_zpowers_zE_of_central_g28 M hx₀T hx₀c hx₀3)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_zE, orderOf_eq_prime hx₀3 hx₀1]
  have hmap : (Subgroup.zpowers (zE M)).map ι = Subgroup.zpowers z₀ := by
    rw [← hzp, MonoidHom.map_zpowers, hx₀z]
  refine ⟨ε, fun j hj => hN ?_⟩
  rw [← hmap]
  exact Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι (gElt_mem_SX M hj))

private theorem exists_equiv_gElt_mem_g28 (hF : Nat.card F = 8) {Y : Type} [Group Y]
    [Finite Y] {K Y₀ E : Subgroup Y} [K.Normal] (e : K ≃* adjointGroup .G2 F) (R : Sylow 3 Y)
    (hER : E ≤ R) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hcore : (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀) :
    ∃ ε : K ≃* adjointGroup .G2 F, ∀ j < 4, ((ε.symm (gElt M j) : K) : Y) ∈ Y₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h3 : 3 ≤ pRank 3 (R : Subgroup Y)
  · rw [if_pos h3] at hcore
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    by_cases hRC : (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) = ⊥
    · exact gElt_mem_of_inf_eq_bot_g28 M hF e R hcore hRC h3
    · obtain ⟨c, hc, hc1, hc3⟩ :=
        exists_pow_eq_one_g28 (R.isPGroup'.to_le inf_le_left) hRC
      exact gElt_mem_of_centralizer_g28 M hF e R hcore hc.1 hc.2 hc1 hc3
  · rw [if_neg h3] at hcore
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    exact gElt_mem_of_not_three_le_g28 M hF e R hER hE hEc hcore h3

private theorem comap_eq_SX_g28 (hF : Nat.card F = 8) {Y : Type}
    [Group Y] {K Y₀ : Subgroup Y} (ε : K ≃* adjointGroup .G2 F)
    (hY : ∀ j < 4, ((ε.symm (gElt M j) : K) : Y) ∈ Y₀) (hKY : ¬ K ≤ Y₀) :
    Y₀.comap (K.subtype.comp ε.symm.toMonoidHom) = SX M := by
  obtain ⟨hPS, -, hmax⟩ := omega_facts M hF
  have hle : SX M ≤ Y₀.comap (K.subtype.comp ε.symm.toMonoidHom) := by
    rw [← hPS]
    unfold PX
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hY j hj
  rcases hmax _ hle with h | h
  · exact h
  · exfalso
    apply hKY
    intro k hk
    have h1 : ε ⟨k, hk⟩ ∈ Y₀.comap (K.subtype.comp ε.symm.toMonoidHom) := h ▸ Subgroup.mem_top _
    simpa using h1

end Core

theorem threeFourTwoAt_g28 :
    ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 3 →
      d.1 = .G2 q → ThreeFourTwoAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  intro q d hqp hqe hd
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  obtain ⟨F, _, _, hF, ⟨e₁⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hqp
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)
  rw [hqp, hqe] at hF
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨M⟩ := exists_model (K := F) hF8
  let e₂ : (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group ≃* adjointGroup .G2 F :=
    e₁.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hSU : SUStruct M := su_struct M hF8 (suHyp M hF8)
  refine ThreeFourTwoAt.of_mulEquiv e₂.symm ?_
  refine threeFourTwoAt_of_forall (isSimpleGroup_X_g28 hF8) (exists_ne_comm_X_g28 hF8)
    (isSolvable_outer_X_g28 hF8) ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ hER hE hEc hcore _ hKY J hJ hne hJp hJs _
  haveI := hKn
  obtain ⟨e⟩ := hKX
  obtain ⟨ε, hε⟩ := exists_equiv_gElt_mem_g28 M hF8 e R hER hE (by rw [hEc]; norm_num) hcore
  set ι : adjointGroup .G2 F →* Y := K.subtype.comp ε.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hrange : ι.range = K := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (ε.symm x).2
    · intro hy
      exact ⟨ε ⟨y, hy⟩, by simp [hιdef]⟩
  obtain ⟨⟨θ⟩, hne', hJp', hJs'⟩ := pullback_g28 hι hrange hJ hne hJp hJs
  rw [comap_eq_SX_g28 M hF8 ε hε hKY] at hJs'
  have hJV := eq_VX_of_isSubnormal_SX_g28 M hSU hJs' hne' hJp'
  obtain ⟨d', ψ, ⟨q', hq'p, hq'e, hd'⟩, hψ⟩ := hSU.2.2.2.1
  have hqq : q' = q := TauCeti.PrimePower.ext (hq'p.trans hqp.symm) (hq'e.trans hqe.symm)
  let eJ : J ≃* VX M := θ.symm.trans (MulEquiv.subgroupCongr hJV)
  refine ⟨.lie ⟨.G2 q, hv⟩, .lie d', ?_, ⟨e.trans e₂.symm⟩, ψ.comp eJ.toMonoidHom,
    hψ.comp eJ.surjective⟩
  exact Or.inr (Or.inl ⟨rfl, q, hqp, hqe, ⟨.G2 q, hv⟩, d', rfl, hqq ▸ hd', rfl, rfl⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
