module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem relIndex_sup_dvd {A B P R : Subgroup X} (hAB : A ≤ centralizer (B : Set X))
    (hPA : P ≤ A) (hRB : R ≤ B) :
    (P ⊔ R).relIndex (A ⊔ B) ∣ P.relIndex A * R.relIndex B := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
  have hcommPR : ∀ p ∈ P, ∀ r ∈ R, p * r = r * p :=
    fun p hp r hr => hcomm p (hPA hp) r (hRB hr)
  let φ : ↥A × ↥B →* ↥(A ⊔ B) :=
    MonoidHom.noncommCoprod (Subgroup.inclusion le_sup_left) (Subgroup.inclusion le_sup_right)
      (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by
      simp only [φ, MonoidHom.noncommCoprod_apply, Subgroup.coe_inclusion]
      exact hab)⟩
  have hmap : ((P.subgroupOf A).prod (R.subgroupOf B)).map φ =
      (P ⊔ R).subgroupOf (A ⊔ B) := by
    ext x
    constructor
    · rintro ⟨⟨⟨p, hpA⟩, ⟨r, hrB⟩⟩, hk, hx⟩
      have hk1 : p ∈ P := hk.1
      have hk2 : r ∈ R := hk.2
      rw [← hx]
      rw [Subgroup.mem_subgroupOf]
      simp only [φ, MonoidHom.noncommCoprod_apply, Subgroup.coe_inclusion]
      exact Subgroup.mul_mem_sup hk1 hk2
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨p, hp, r, hr, hpr⟩ :=
        CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommPR hx
      refine ⟨(⟨p, hPA hp⟩, ⟨r, hRB hr⟩), ?_, ?_⟩
      · exact ⟨hp, hr⟩
      · exact Subtype.ext (by
          simp only [φ, MonoidHom.noncommCoprod_apply, Subgroup.coe_inclusion]
          exact hpr)
  calc (P ⊔ R).relIndex (A ⊔ B)
      = (((P.subgroupOf A).prod (R.subgroupOf B)).map φ).index := by
        rw [Subgroup.relIndex, hmap]
    _ ∣ ((P.subgroupOf A).prod (R.subgroupOf B)).index :=
        Subgroup.index_map_dvd _ hsurj
    _ = P.relIndex A * R.relIndex B := by
        rw [Subgroup.index_prod, Subgroup.relIndex, Subgroup.relIndex]

theorem isSylowOf_sup {p : ℕ} [Fact p.Prime] {A B P R : Subgroup X}
    (hAB : A ≤ centralizer (B : Set X)) (hP : CFSG.ABGLocalTools.IsSylowOf p P A)
    (hR : CFSG.ABGLocalTools.IsSylowOf p R B) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊔ R) (A ⊔ B) := by
  obtain ⟨hPA, hPp, hPdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP)
  obtain ⟨hRB, hRp, hRdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff.mp hR)
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sup_le_sup hPA hRB, ?_, ?_⟩
  · refine IsPGroup.to_sup_of_normal_right' hPp hRp ?_
    exact hPA.trans (hAB.trans ((Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hRB)).trans
      (Subgroup.centralizer_le_normalizer (R : Set X))))
  · intro hdvd
    have hdiv := hdvd.trans (relIndex_sup_dvd hAB hPA hRB)
    exact (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hdiv |>.elim hPdvd hRdvd

private theorem le_normalizer_iSup_fin_three {C : Fin 3 → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set X)) (i : Fin 3) :
    (⨆ j, C j) ≤ normalizer (C i : Set X) := by
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact le_normalizer
  · exact (hcomm j i hij).trans (Subgroup.centralizer_le_normalizer (C i : Set X))

private theorem isSylowOf_inf_of_commuting {p : ℕ} [Fact p.Prime] (C : Fin 3 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set X)) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T (⨆ i, C i)) (i : Fin 3) :
    CFSG.ABGLocalTools.IsSylowOf p (T ⊓ C i) (C i) :=
  hT.inf_of_le_normalizer (le_iSup C i) (le_normalizer_iSup_fin_three hcomm i)

private theorem isSylowOf_iSup_inf_of_commuting {p : ℕ} [Fact p.Prime] (C : Fin 3 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set X)) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T (⨆ i, C i)) :
    CFSG.ABGLocalTools.IsSylowOf p (⨆ i, T ⊓ C i) (⨆ i, C i) := by
  have hTi := isSylowOf_inf_of_commuting C hcomm hT
  simp only [iSup_fin_three]
  exact isSylowOf_sup (sup_le (hcomm 0 2 (by decide)) (hcomm 1 2 (by decide)))
    (isSylowOf_sup (hcomm 0 1 (by decide)) (hTi 0) (hTi 1)) (hTi 2)

theorem eq_iSup_inf_of_isSylowOf {p : ℕ} [Fact p.Prime] (C : Fin 3 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set X)) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T (⨆ i, C i)) : T = ⨆ i, T ⊓ C i :=
  (isSylowOf_iSup_inf_of_commuting C hcomm hT).eq_of_le
    (iSup_le fun _ => inf_le_left) hT.le hT.isPGroup

private theorem card_dvd_card_of_le {H K : Subgroup X} (h : H ≤ K) :
    Nat.card H ∣ Nat.card K := by
  have hc := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at hc

private theorem pRank_coe_eq_openPRank' (p : ℕ) (H : Subgroup X) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥H).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm

private theorem isCyclic_of_pRank_le_one' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L S : Subgroup X} (hSL : S ≤ L) (hS : IsPGroup p S) (hr : CFSG.pRank p ↥L ≤ 1) :
    IsCyclic S := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p S) := ⟨hS⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a (R := ↥S) hp2 hnc
  have hEab : IsElemAbelian p (E.map S.subtype) :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mpr
      (CFSG.IsElementaryAbelian.subgroup_map hEel S.subtype)
  have hEL : E.map S.subtype ≤ L := by
    rintro _ ⟨e, -, rfl⟩
    exact hSL e.2
  have hcard : Nat.card (E.map S.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hEcard]
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt hEL hEab hcard
  rw [pRank_coe_eq_openPRank' p L] at hr
  omega

theorem omegaOnePSub_structure {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (C : Fin 3 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set X))
    (hrank : ∀ i, CFSG.Open.pRank p (C i) = 1) (hZ : ∀ i, ¬ p ∣ Nat.card (center ↥(C i)))
    (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T (⨆ i, C i)) :
    (∀ a ∈ omegaOnePSub p T, ∀ b ∈ omegaOnePSub p T, a * b = b * a) ∧
      (∀ v ∈ omegaOnePSub p T, v ^ p = 1) ∧ Nat.card (omegaOnePSub p T) = p ^ 3 ∧
      (∀ i, Nat.card ↥(omegaOnePSub p T ⊓ C i) = p) ∧
      omegaOnePSub p T ≤ ⨆ i, omegaOnePSub p T ⊓ C i := by
  haveI : Fact p.Prime := ⟨hp⟩
  let V : Subgroup X := omegaOnePSub p T
  have hTi : ∀ i, CFSG.ABGLocalTools.IsSylowOf p (T ⊓ C i) (C i) :=
    isSylowOf_inf_of_commuting C hcomm hT
  have hTsplit : T = ⨆ i, T ⊓ C i := eq_iSup_inf_of_isSylowOf C hcomm hT
  have hTi_cyclic : ∀ i, IsCyclic ↥(T ⊓ C i) := by
    intro i
    refine isCyclic_of_pRank_le_one' hp hp2 inf_le_right (hTi i).isPGroup ?_
    rw [pRank_coe_eq_openPRank' p (C i), hrank i]
  have hT_comm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    have hle : T ≤ centralizer (T : Set X) := by
      rw [hTsplit]
      refine iSup_le fun i => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup_le fun j => ?_
      by_cases hij : j = i
      · rw [hij]
        haveI := hTi_cyclic i
        exact Subgroup.le_centralizer _
      · exact (inf_le_right.trans (hcomm j i hij)).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hpdvd : ∀ i, p ∣ Nat.card (C i) := by
    intro i
    obtain ⟨E, hE, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (C i)
    have hEcard' : Nat.card E = p := by rw [hEcard, hrank i, pow_one]
    rw [← hEcard']
    exact card_dvd_card_of_le hE
  have hz_exists : ∀ i, ∃ z : X, z ∈ T ⊓ C i ∧ orderOf z = p := by
    intro i
    have hfac : 1 ≤ (Nat.card (C i)).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp (Nat.card_pos.ne')).mp (hpdvd i)
    have hpdvd' : p ∣ Nat.card ↥(T ⊓ C i) := by
      rw [(hTi i).card_eq]
      exact dvd_pow_self p
        (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hfac))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd'
    exact ⟨(z : X), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩
  choose z hzmem hzord using hz_exists
  have hz_noncentral : ∀ i, ∃ c ∈ C i, z i * c ≠ c * z i := by
    intro i
    by_contra h
    push Not at h
    have hcent : (⟨z i, (hzmem i).2⟩ : ↥(C i)) ∈ center ↥(C i) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (h (y : X) y.2).symm
    have hdvd : p ∣ Nat.card (center ↥(C i)) := by
      have hcard : Nat.card (Subgroup.zpowers (⟨z i, (hzmem i).2⟩ : ↥(C i))) = p := by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hzord i]
      rw [← hcard]
      exact card_dvd_card_of_le (Subgroup.zpowers_le.mpr hcent)
    exact hZ i hdvd
  have hVT : V ≤ T := (Subgroup.closure_le _).mpr (fun x hx => hx.1)
  have hV_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    fun a ha b hb => hT_comm a (hVT ha) b (hVT hb)
  let W : Subgroup X :=
    { carrier := {x : X | x ∈ T ∧ x ^ p = 1}
      one_mem' := ⟨T.one_mem, one_pow p⟩
      mul_mem' := by
        rintro x y ⟨hxT, hx⟩ ⟨hyT, hy⟩
        exact ⟨T.mul_mem hxT hyT, by
          rw [Commute.mul_pow (hT_comm x hxT y hyT), hx, hy, mul_one]⟩
      inv_mem' := by
        rintro x ⟨hxT, hx⟩
        exact ⟨T.inv_mem hxT, by rw [inv_pow, hx, inv_one]⟩ }
  have hVW : V ≤ W := (Subgroup.closure_le _).mpr (fun x hx => ⟨hx.1, hx.2⟩)
  have hV_pow : ∀ v ∈ V, v ^ p = 1 := fun v hv => (hVW hv).2
  have hV_ab : IsElemAbelian p V :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hT_comm a (hVT a.2) b (hVT b.2))),
      hV_pow⟩
  let A₁ : Subgroup X := ⊥ ⊔ zpowers (z 0)
  let A₂ : Subgroup X := A₁ ⊔ zpowers (z 1)
  let A₃ : Subgroup X := A₂ ⊔ zpowers (z 2)
  have hA1 : IsElemAbelian p A₁ ∧ Nat.card A₁ = p ^ 1 := by
    have h := isElemAbelian_sup_zpowers (p := p) (A := (⊥ : Subgroup X)) (C := C 0)
      (e := z 0) (a := 0) hp (CFSG.SectionRank.isElemAbelian_bot p)
      (by rw [pow_zero]; exact Subgroup.card_bot) bot_le (hzmem 0).2 (hzord 0)
      (hz_noncentral 0)
    simpa [A₁] using h
  have hA2 : IsElemAbelian p A₂ ∧ Nat.card A₂ = p ^ 2 := by
    have hle : A₁ ≤ centralizer (C 1 : Set X) :=
      sup_le bot_le (Subgroup.zpowers_le.mpr ((hcomm 0 1 (by decide)) (hzmem 0).2))
    have h := isElemAbelian_sup_zpowers (p := p) (A := A₁) (C := C 1) (e := z 1) (a := 1)
      hp hA1.1 hA1.2 hle (hzmem 1).2 (hzord 1) (hz_noncentral 1)
    simpa [A₂] using h
  have hA3 : IsElemAbelian p A₃ ∧ Nat.card A₃ = p ^ 3 := by
    have hle : A₂ ≤ centralizer (C 2 : Set X) :=
      sup_le (sup_le bot_le (Subgroup.zpowers_le.mpr ((hcomm 0 2 (by decide)) (hzmem 0).2)))
        (Subgroup.zpowers_le.mpr ((hcomm 1 2 (by decide)) (hzmem 1).2))
    have h := isElemAbelian_sup_zpowers (p := p) (A := A₂) (C := C 2) (e := z 2) (a := 2)
      hp hA2.1 hA2.2 hle (hzmem 2).2 (hzord 2) (hz_noncentral 2)
    simpa [A₃] using h
  have hz_in_V : ∀ i, z i ∈ V := fun i =>
    Subgroup.subset_closure ⟨(hzmem i).1, by rw [← hzord i]; exact pow_orderOf_eq_one (z i)⟩
  have hzpow_le : ∀ i, zpowers (z i) ≤ V := fun i => Subgroup.zpowers_le.mpr (hz_in_V i)
  have hA_le_V : A₃ ≤ V :=
    sup_le (sup_le (sup_le bot_le (hzpow_le 0)) (hzpow_le 1)) (hzpow_le 2)
  have hA3card : Nat.card A₃ = p ^ 3 := hA3.2
  have hVp : IsPGroup p V := hT.isPGroup.to_le hVT
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hVp
  have hr3 : r ≤ 3 := by
    have h1 := CFSG.SectionRank.le_pRank hp.one_lt (H := (⊤ : Subgroup X)) le_top hV_ab hr
    omega
  have h3r : 3 ≤ r := by
    have h1 : Nat.card A₃ ≤ Nat.card V := Subgroup.card_le_of_le hA_le_V
    rw [hA3card, hr] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hV_card : Nat.card V = p ^ 3 := by
    rw [hr, le_antisymm hr3 h3r]
  have hVi_card : ∀ i, Nat.card ↥(V ⊓ C i) = p := by
    intro i
    have hVi_ab : IsElemAbelian p (V ⊓ C i) := CFSG.Open.IsElemAbelian.mono hV_ab inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hVi_ab)
    have hk1 : k ≤ 1 := by
      have h1 := CFSG.SectionRank.le_pRank hp.one_lt (H := C i) inf_le_right hVi_ab hk
      rwa [hrank i] at h1
    have hk0 : k ≠ 0 := by
      intro hk0
      have hzne : z i ≠ 1 := by
        intro h
        have hzi := hzord i
        rw [h, orderOf_one] at hzi
        exact hp.ne_one hzi.symm
      have hne_bot : V ⊓ C i ≠ ⊥ := by
        intro hbot
        have hzbot : z i ∈ (⊥ : Subgroup X) :=
          hbot ▸ (Subgroup.mem_inf.mpr ⟨hz_in_V i, (hzmem i).2⟩)
        exact hzne (Subgroup.mem_bot.mp hzbot)
      have hone : 1 < Nat.card ↥(V ⊓ C i) :=
        (Subgroup.one_lt_card_iff_ne_bot (V ⊓ C i)).mpr hne_bot
      rw [hk, hk0, pow_zero] at hone
      exact lt_irrefl 1 hone
    have hk_eq : k = 1 := by omega
    rw [hk, hk_eq, pow_one]
  have hA_le_iSup : A₃ ≤ ⨆ i, V ⊓ C i := by
    refine sup_le (sup_le (sup_le bot_le ?_) ?_) ?_
    · exact (Subgroup.zpowers_le.mpr
        (Subgroup.mem_inf.mpr ⟨hz_in_V 0, (hzmem 0).2⟩)).trans
        (le_iSup (fun i => V ⊓ C i) 0)
    · exact (Subgroup.zpowers_le.mpr
        (Subgroup.mem_inf.mpr ⟨hz_in_V 1, (hzmem 1).2⟩)).trans
        (le_iSup (fun i => V ⊓ C i) 1)
    · exact (Subgroup.zpowers_le.mpr
        (Subgroup.mem_inf.mpr ⟨hz_in_V 2, (hzmem 2).2⟩)).trans
        (le_iSup (fun i => V ⊓ C i) 2)
  have hV_eq_A : V = A₃ :=
    (Subgroup.eq_of_le_of_card_ge hA_le_V (by rw [hV_card, hA3card])).symm
  have hV_le_iSup : V ≤ ⨆ i, V ⊓ C i := by
    rw [← hV_eq_A] at hA_le_iSup
    exact hA_le_iSup
  exact ⟨hV_comm, hV_pow, hV_card, hVi_card, hV_le_iSup⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
