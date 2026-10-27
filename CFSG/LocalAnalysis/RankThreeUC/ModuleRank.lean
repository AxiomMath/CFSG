module

public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem exists_noncyclic_pGroup_le_of_map {F Q : Type*} [Group F] [Finite F] [Group Q]
    {p : ℕ} [Fact p.Prime] (ψ : F →* Q) {B E : Subgroup F}
    (hB : ∀ x : F, ∃ b ∈ B, ψ x = ψ b) (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card (E.map ψ)) :
    ∃ S : Subgroup F, S ≤ B ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  let B₂ : Subgroup F := B ⊓ (E.map ψ).comap ψ
  have hmem : ∀ b : B₂, ψ b ∈ E.map ψ := fun b => b.2.2
  let g : B₂ →* E.map ψ := (ψ.comp B₂.subtype).codRestrict (E.map ψ) hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, e, he, rfl⟩
    obtain ⟨b, hb, hb'⟩ := hB e
    refine ⟨⟨b, hb, ?_⟩, Subtype.ext hb'.symm⟩
    show ψ b ∈ E.map ψ
    rw [← hb']
    exact ⟨e, he, rfl⟩
  have hexp : ∀ y : E.map ψ, y ^ p = 1 := by
    rintro ⟨y, e, he, rfl⟩
    exact Subtype.ext (by show ψ e ^ p = 1; rw [← map_pow, hE e he, map_one])
  have hpg : IsPGroup p (E.map ψ) := fun y => ⟨1, by simpa using hexp y⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p B₂))
  have htop : (T : Subgroup B₂).map g = ⊤ := by
    have h := (T.mapSurjective hg).3 (hpg.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  refine ⟨(T : Subgroup B₂).map B₂.subtype, ?_, T.isPGroup'.map B₂.subtype, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact t.2.1
  · intro hcyc
    have hT : IsCyclic (T : Subgroup B₂) :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective (T : Subgroup B₂) B₂.subtype B₂.subtype_injective).symm
        (MulEquiv.surjective _)
    have hQ : IsCyclic (E.map ψ) := by
      refine isCyclic_of_surjective (g.comp (T : Subgroup B₂).subtype) fun y => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (htop ▸ Subgroup.mem_top y)
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨c, hc⟩ := hQ.exists_generator
    have h1 : orderOf c = Nat.card (E.map ψ) := orderOf_eq_card_of_forall_mem_zpowers hc
    have h2 : orderOf c ≤ p :=
      Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one (hexp c))
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith

omit [Finite G] in
private theorem card_subgroupOf_eq {K H : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

private theorem card_inf_le_of_pRank_le_one {p : ℕ} (hp : p.Prime) {A E : Subgroup G}
    (hE : IsElemAbelian p E) (hA : CFSG.Open.pRank p A ≤ 1) :
    Nat.card (A ⊓ E : Subgroup G) ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := ((elementary_isPGroup p E hE).to_le (inf_le_right : A ⊓ E ≤ E)).exists_card_eq
  have hAE : IsElemAbelian p (A ⊓ E : Subgroup G) := by
    refine ⟨isMulCommutative_iff.mpr fun x y => ?_, fun x hx => hE.2 x hx.2⟩
    apply Subtype.ext
    have := isMulCommutative_iff.mp hE.1 ⟨x, x.2.2⟩ ⟨y, y.2.2⟩
    exact congrArg (fun z : E => (z : G)) this
  have hjle : j ≤ CFSG.Open.pRank p A :=
    le_csSup (pRank_set_bddAbove p hp.one_lt A) ⟨A ⊓ E, inf_le_left, hAE, hj⟩
  rw [hj]
  calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

private theorem two_le_pRank_of_noncyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hnc : ¬ IsCyclic Q) : 2 ≤ CFSG.Open.pRank p Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB, hBc⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (hp.odd_of_ne_two hp2) hQp hnc
  have hBe : CFSG.IsElementaryAbelian p (B.map Q.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨B.map Q.subtype, map_subtype_le B,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hBe,
    by rw [card_map_of_injective Q.subtype_injective, hBc]⟩

theorem two_le_pRank_or_of_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X A B : Subgroup G}
    (hAX : A ≤ X) (hXA : X ≤ normalizer (A : Set G)) (hBX : B ≤ X) (hX : X ≤ A ⊔ B)
    (h3 : 3 ≤ pRank p X) : 2 ≤ pRank p A ∨ 2 ≤ pRank p B := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hA : 2 ≤ CFSG.Open.pRank p A
  · exact Or.inl hA
  by_cases hB : 2 ≤ CFSG.Open.pRank p B
  · exact Or.inr hB
  exfalso
  obtain ⟨E, hEX, hEe, hEcard⟩ := pRank_attained p X (by omega)
  have hEA : Nat.card (A ⊓ E : Subgroup G) ≤ p := card_inf_le_of_pRank_le_one hp hEe (by omega)
  have hN : (A.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hAX).mpr hXA
  let ψ : X →* X ⧸ A.subgroupOf X := QuotientGroup.mk' (A.subgroupOf X)
  have hBψ : ∀ x : X, ∃ b ∈ B.subgroupOf X, ψ x = ψ b := by
    intro x
    have hx : (x : G) ∈ ((A ⊔ B : Subgroup G) : Set G) := hX x.2
    rw [coe_mul_of_right_le_normalizer_left A B (hBX.trans hXA)] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    refine ⟨⟨b, hBX hb⟩, hb, ?_⟩
    have hxab : x = ⟨a, hAX ha⟩ * ⟨b, hBX hb⟩ := Subtype.ext hab.symm
    have h1 : ψ ⟨a, hAX ha⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [hxab, map_mul, h1, one_mul]
  have hEp : ∀ x ∈ E.subgroupOf X, x ^ p = 1 := fun x hx => Subtype.ext (hEe.2 x hx)
  have hcard : p ^ 2 ≤ Nat.card ((E.subgroupOf X).map ψ) := by
    have h1 := Subgroup.relIndex_ker (E.subgroupOf X) ψ
    have h2 := Subgroup.relIndex_mul_card ψ.ker (E.subgroupOf X)
    rw [h1, QuotientGroup.ker_mk'] at h2
    have hinf : (A.subgroupOf X ⊓ E.subgroupOf X) = (A ⊓ E).subgroupOf X :=
      Subgroup.ext fun _ => Iff.rfl
    rw [hinf, card_subgroupOf_eq (inf_le_left.trans hAX), card_subgroupOf_eq hEX, hEcard] at h2
    have h4 : p ^ 3 ≤ p ^ CFSG.Open.pRank p X := Nat.pow_le_pow_right hp.pos h3
    have h5 : p ^ 2 * p ≤ Nat.card ((E.subgroupOf X).map ψ) * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ ≤ p ^ CFSG.Open.pRank p X := h4
        _ = _ := h2.symm
        _ ≤ _ := Nat.mul_le_mul_left _ hEA
    exact Nat.le_of_mul_le_mul_right h5 hp.pos
  obtain ⟨S, hSB, hSp, hSnc⟩ := exists_noncyclic_pGroup_le_of_map ψ hBψ hEp hcard
  have hS₁B : S.map X.subtype ≤ B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSB hs
  have hS₁nc : ¬ IsCyclic (S.map X.subtype) := fun hc =>
    hSnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective S X.subtype X.subtype_injective).symm
      (Subgroup.equivMapOfInjective S X.subtype X.subtype_injective).symm.surjective)
  have h6 := two_le_pRank_of_noncyclic hp hp2 (hSp.map X.subtype) hS₁nc
  have h7 := pRank_mono p hp.one_lt hS₁B
  omega

omit [Finite G] in
private theorem le_normalizer_inf_centralizer {M V : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ c ∈ M ⊓ centralizer (V : Set G),
      m * c * m⁻¹ ∈ M ⊓ centralizer (V : Set G) := by
    rintro m hm c ⟨hcM, hcV⟩
    refine ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : m⁻¹ * v * m ∈ V := by
      simpa using (mem_normalizer_iff.mp (hMV (M.inv_mem hm)) v).mp hv
    have hcomm := mem_centralizer_iff.mp hcV _ hv'
    calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [hcomm]
      _ = m * c * m⁻¹ * v := by group
  intro m hm
  rw [mem_normalizer_iff]
  intro c
  exact ⟨key m hm c, fun h => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ h⟩

private theorem exists_mem_map_conj_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {A B Y : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf p A Y) (hB : CFSG.ABGLocalTools.IsSylowOf p B Y) :
    ∃ m ∈ Y, A.map (MulAut.conj m).toMonoidHom = B := by
  obtain ⟨QA, rfl⟩ := hA
  obtain ⟨QB, rfl⟩ := hB
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq Y QA QB
  refine ⟨m, m.2, ?_⟩
  rw [← hm, sylow_conjugate_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem le_sup_inf_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {H Y S : Subgroup G}
    (hYH : Y ≤ H) (hn : H ≤ normalizer (Y : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) : H ≤ Y ⊔ (H ⊓ normalizer (S : Set G)) := by
  intro x hx
  have hxY : x ∈ normalizer (Y : Set G) := hn hx
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (mem_normalizer_iff.1 hxY s).1 (hS.le hs)
    · rw [card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hkS⟩ := exists_mem_map_conj_eq_of_isSylowOf hS hS'
  have hkx : k⁻¹ * x ∈ normalizer (S : Set G) := by
    refine mem_normalizer_iff_map_conj_eq.mpr ?_
    show S.map (MulAut.conj (k⁻¹ * x)).toMonoidHom = S
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun g => by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
          MonoidHom.id_apply]
    rw [← conjugate_map_mul, ← hkS, conjugate_map_mul, inv_mul_cancel, h1, Subgroup.map_id]
  rw [show x = k * (k⁻¹ * x) by group]
  exact mul_mem_sup hk ⟨H.mul_mem (H.inv_mem (hYH hk)) hx, hkx⟩

theorem le_sup_normalizer_centralizer {M V T : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    M ≤ (M ⊓ centralizer (V : Set G)) ⊔
      (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) := by
  have hn := le_normalizer_inf_centralizer hMV
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ centralizer (V : Set G))
      (M ⊓ centralizer (V : Set G)) := by
    have h := hT.inf_of_le_normalizer (inf_le_left : M ⊓ centralizer (V : Set G) ≤ M) hn
    rwa [← inf_assoc, inf_eq_left.mpr hT.le] at h
  exact le_sup_inf_normalizer_of_isSylowOf inf_le_left hn hS

omit [Finite G] in
private theorem mem_normalizer_zpowers_of_comm {v c : G} (h : v * c = c * v) :
    c ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute v c from h) k).eq

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.two_le_pRank_normalizer_or_centralizer
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G) (hp : IsWitnessPrime p P)
    (hw : IsWitnessGen p P M) {V T : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    2 ≤ pRank p (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) ∨
      2 ≤ pRank p (M ⊓ centralizer (V : Set G)) :=
  (two_le_pRank_or_of_le_sup hp.prime hp.odd inf_le_left
    (le_normalizer_inf_centralizer hMV) inf_le_left (le_sup_normalizer_centralizer hMV hT)
    (hw.three_le_pRank hp)).symm

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.conj_eq_or_inf_eq_bot
    (hp : p.Prime) (hw : IsWitnessGen p P M)
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (hMV : M ≤ normalizer (V : Set G))
    (h2 : 2 ≤ pRank p (M ⊓ centralizer (V : Set G))) (g : G) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V := by
  by_cases hbot : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨hwV, v, hv, hvw⟩ := w.2
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hw1
    apply Subtype.ext
    simpa using hvw.symm
  have hne : (zpowers v : Subgroup G) ≠ ⊥ := by
    rwa [Ne, zpowers_eq_bot]
  have hloc : IsTwoLocal (normalizer ((zpowers v : Subgroup G) : Set G)) :=
    ⟨zpowers v, hne, hV2.to_le (zpowers_le.mpr hv), rfl⟩
  have hRN : M ⊓ centralizer (V : Set G) ≤ normalizer ((zpowers v : Subgroup G) : Set G) := by
    rintro c ⟨-, hc⟩
    exact mem_normalizer_zpowers_of_comm (mem_centralizer_iff.mp hc v hv)
  have hNM := hw.le_of_le_of_two_le_pRank hp inf_le_left h2 hloc hRN
  have hRg : M ⊓ centralizer (V : Set G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    rintro c ⟨-, hc⟩
    refine ⟨g⁻¹ * c * g, hNM (mem_normalizer_zpowers_of_comm ?_),
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have hwc := mem_centralizer_iff.mp hc _ hwV
    have hwv : (w : G) = g * v * g⁻¹ := hvw.symm
    rw [hwv] at hwc
    calc v * (g⁻¹ * c * g) = g⁻¹ * (g * v * g⁻¹ * c) * g := by group
      _ = g⁻¹ * (c * (g * v * g⁻¹)) * g := by rw [hwc]
      _ = (g⁻¹ * c * g) * v := by group
  have hMg : M.map (MulAut.conj g).toMonoidHom ≤ M :=
    hw.le_of_le_of_two_le_pRank hp inf_le_left h2
      (twoLocal_map_automorphism M hw.maxLocal.1 _) hRg
  have heq : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge hMg
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hgM : g ∈ M := by
    rw [← maxTwoLocal_self_normalizing M hw.maxLocal]
    exact mem_normalizer_iff_map_conj_eq.mpr heq
  exact mem_normalizer_iff_map_conj_eq.mp (hMV hgM)

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
