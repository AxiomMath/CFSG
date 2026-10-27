module

public import CFSG.LocalAnalysis.RankThreeUC.K518HDefs
import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YCover
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

private theorem mem_of_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ R : Sylow p G, IsCyclic R) {Q : Subgroup G} [Q.Normal] (hQ : p ∣ Nat.card Q)
    {w : G} (hw : orderOf w = p) : w ∈ Q := by
  obtain ⟨w₀', hw₀'⟩ := exists_prime_orderOf_dvd_card' p hQ
  have hw₀ : orderOf (w₀' : G) = p := by rw [Subgroup.orderOf_coe]; exact hw₀'
  have hpg : ∀ {v : G}, orderOf v = p → IsPGroup p (Subgroup.zpowers v) := by
    intro v hv
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv, pow_one]
  obtain ⟨R₁, hR₁⟩ := (hpg hw).exists_le_sylow
  obtain ⟨R₂, hR₂⟩ := (hpg hw₀).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R₁ R₂
  have h1 : g * w * g⁻¹ ∈ (R₂ : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul w (MulAut.conj g) (R₁ : Subgroup G)
      (hR₁ (Subgroup.mem_zpowers w))
    simpa [MulAut.conj_apply] using this
  have h2 : (w₀' : G) ∈ (R₂ : Subgroup G) := hR₂ (Subgroup.mem_zpowers _)
  have := hcyc R₂
  set a₁ : (R₂ : Subgroup G) := ⟨g * w * g⁻¹, h1⟩ with ha₁def
  set a₂ : (R₂ : Subgroup G) := ⟨(w₀' : G), h2⟩ with ha₂def
  have ha₁ : orderOf a₁ = p := by
    rw [← Subgroup.orderOf_coe a₁]
    simp only [ha₁def]
    rw [← hw]
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
  have ha₂ : orderOf a₂ = p := by
    rw [← Subgroup.orderOf_coe a₂]
    exact hw₀
  have heq : Subgroup.zpowers a₁ = Subgroup.zpowers a₂ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ha₁, ha₂]
  have hmem : a₁ ∈ Subgroup.zpowers a₂ := heq ▸ Subgroup.mem_zpowers a₁
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : (w₀' : G) ^ k = g * w * g⁻¹ := congrArg Subtype.val hk
  have hgw : g * w * g⁻¹ ∈ Q := by rw [← hk']; exact Q.zpow_mem w₀'.2 k
  have h3 := Subgroup.Normal.conj_mem ‹Q.Normal› _ hgw g⁻¹
  have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
  rwa [e] at h3

private theorem exists_mul_mem_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q S₀ : Subgroup G} [Q.Normal] (hS : S₀ ≤ Q) (hp : IsPGroup p S₀)
    (hidx : ¬ p ∣ S₀.relIndex Q) (g : G) :
    ∃ a ∈ Q, ∃ b ∈ Subgroup.normalizer (S₀ : Set G), g = a * b := by
  have hp' : IsPGroup p (S₀.subgroupOf Q) := hp.comap_subtype
  let P : Sylow p Q := hp'.toSylow hidx
  have h := Sylow.normalizer_sup_eq_top P
  have hmap : Subgroup.map Q.subtype (P : Subgroup Q) = S₀ := by
    rw [show (P : Subgroup Q) = S₀.subgroupOf Q from IsPGroup.toSylow_coe hp' hidx,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hS]
  rw [hmap, sup_comm] at h
  have hg : g ∈ (↑(Q ⊔ Subgroup.normalizer (S₀ : Set G)) : Set G) := by
    rw [h]
    exact Set.mem_univ g
  rw [Subgroup.normal_mul] at hg
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hg
  exact ⟨a, ha, b, hb, hab.symm⟩

private theorem exists_last_power {G : Type*} [Group G] {p : ℕ} {M : Subgroup G} {y : G}
    (hy : ∃ k, orderOf y = p ^ k) (hyM : y ∉ M) :
    ∃ j : ℕ, y ^ p ^ j ∉ M ∧ (y ^ p ^ j) ^ p ∈ M := by
  classical
  obtain ⟨k, hk⟩ := hy
  have hex : ∃ j : ℕ, y ^ p ^ j ∈ M := ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact M.one_mem⟩
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp only [pow_zero, pow_one] at hspec
    exact hyM hspec
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨j, Nat.find_min hex (by omega), ?_⟩
  have : (y ^ p ^ j) ^ p = y ^ p ^ (j + 1) := by rw [← pow_mul, ← pow_succ]
  rw [this]
  rw [hj] at hspec
  exact hspec

private theorem exists_pElement_not_mem {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M K H₀ : Subgroup G} [M.Normal] (hKM : K ≤ M)
    (hdec : ∀ g : G, ∃ a ∈ K, ∃ b ∈ H₀, g = a * b) {x : G}
    (hx : ∃ k, orderOf x = p ^ k) (hxM : x ∉ M) :
    ∃ y ∈ H₀, (∃ k, orderOf y = p ^ k) ∧ y ∉ M := by
  obtain ⟨a, haK, b, hbH, hab⟩ := hdec x
  obtain ⟨k, hk⟩ := hx
  obtain ⟨e, m, hm, hbe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos b).ne' p hp.ne_one
  have hmd : m ∣ orderOf b := ⟨p ^ e, by rw [hbe]; ring⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  refine ⟨b ^ m, H₀.pow_mem hbH m, ⟨e, ?_⟩, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 hmd, hbe, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · intro hbm
    have ha1 : QuotientGroup.mk' M a = 1 := (QuotientGroup.eq_one_iff a).2 (hKM haK)
    have hπx : QuotientGroup.mk' M x = QuotientGroup.mk' M b := by
      rw [hab, map_mul, ha1, one_mul]
    have hπb : (QuotientGroup.mk' M b) ^ m = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hbm
    have h1 : orderOf (QuotientGroup.mk' M x) ∣ p ^ k := hk ▸ orderOf_map_dvd _ x
    have h2 : orderOf (QuotientGroup.mk' M x) ∣ m := by
      rw [hπx]
      exact orderOf_dvd_of_pow_eq_one hπb
    have hcop : Nat.Coprime (p ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    have h3 : orderOf (QuotientGroup.mk' M x) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
    have h4 : QuotientGroup.mk' M x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    exact hxM ((QuotientGroup.eq_one_iff x).1 h4)

private theorem conj_mem_sup_centralizer {Y : Type*} [Group Y] {L : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (L : Set Y)) {z : Y}
    (hz : z ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    g * z * g⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
  have key : L ⊔ Subgroup.centralizer (L : Set Y) ≤
      (L ⊔ Subgroup.centralizer (L : Set Y)).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro l hl
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hg l).mp hl)
    · intro c hc
      refine Subgroup.mem_sup_right ?_
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : g⁻¹ * l * g ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * l * g)).mpr
        have e : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
        rw [e] at h
        exact h hl
      have h := (Subgroup.mem_centralizer_iff.mp hc) _ hl'
      show l * (g * c * g⁻¹) = g * c * g⁻¹ * l
      calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * l := by group
  exact key hz

private theorem mem_normalizer_of_subgroupOf {Y : Type*} [Group Y] {N S : Subgroup Y}
    (hSN : S ≤ N) {b : N}
    (hb : b ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup N) : Set N)) :
    (b : Y) ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro h
  constructor
  · intro hh
    exact (hb ⟨h, hSN hh⟩).mp hh
  · intro hh
    have hhN : h ∈ N := by
      have := N.mul_mem (N.mul_mem (N.inv_mem b.2) (hSN hh)) b.2
      simpa [mul_assoc] using this
    exact (hb ⟨h, hhN⟩).mpr hh

theorem kFact518Out_of_crit (hC : K518Crit) :
    CFSG.LocalAnalysis.RankThreeUC.S15.KFact518Out := by
  intro Y _ _ L N S P hL hcl hnr hNL hS hP hPN p hp hp2 hpZ hpNL hrk x hxN hxp
  have : Fact p.Prime := ⟨hp⟩
  by_contra hxM
  have hSL : S ≤ L := hS.1
  have hSP : S ≤ P := fun s hs =>
    hP.2.1.le (Subgroup.mem_inf.mpr ⟨hSL hs, Subgroup.le_normalizer hs⟩)
  have hSN : S ≤ N := by
    intro s hs
    refine hPN (Subgroup.subset_closure ⟨hSP hs, ?_⟩)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS.2.1 ⟨s, hs⟩
    exact ⟨k, (Subgroup.orderOf_coe (⟨s, hs⟩ : S)).trans hk⟩
  set M : Subgroup Y := L ⊔ Subgroup.centralizer (L : Set Y) with hMdef
  have hMconj : ∀ g ∈ N, ∀ z ∈ M, g * z * g⁻¹ ∈ M := fun g hg z hz =>
    conj_mem_sup_centralizer (hNL hg) hz
  have hcyc : ∀ R : Sylow p ↥N, IsCyclic ↥R := by
    intro R
    have h1 : IsCyclic ↥((R : Subgroup ↥N).map N.subtype) :=
      CFSG.all_pSubgroups_isCyclic_of_pRank_le_one hp hp2 hrk _ (Subgroup.map_subtype_le _)
        (R.isPGroup'.map N.subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (R : Subgroup ↥N) N.subtype
        N.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  have hQnorm : ((N ⊓ L).subgroupOf N).Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨hzN, hzL⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨(g * z * g⁻¹ : N).2, ?_⟩)
    exact (Subgroup.mem_normalizer_iff.mp (hNL g.2) z).mp hzL
  have hA : ∀ s ∈ N, orderOf s = p → s ∈ L := by
    intro s hs hos
    have := hQnorm
    have hcard : p ∣ Nat.card ((N ⊓ L).subgroupOf N) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ L ≤ N)).toEquiv]
      exact hpNL
    have h := mem_of_orderOf_eq_prime hcyc hcard (w := (⟨s, hs⟩ : N))
      ((Subgroup.orderOf_coe (⟨s, hs⟩ : N)).symm.trans hos)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
  obtain ⟨y, hyH, hyp, hyM⟩ : ∃ y : N, y ∈ (Subgroup.normalizer (S : Set Y)).subgroupOf N ∧
      (∃ k, orderOf y = p ^ k) ∧ y ∉ M.subgroupOf N := by
    have hSNL : S ≤ N ⊓ L := le_inf hSN hSL
    have hM'norm : (M.subgroupOf N).Normal := ⟨fun z hz g => hMconj g g.2 z hz⟩
    have := hM'norm
    have := hQnorm
    have hS₀Q : S.subgroupOf N ≤ (N ⊓ L).subgroupOf N := fun z hz => hSNL hz
    have hp₀ : IsPGroup 2 (S.subgroupOf N) := hS.2.1.comap_subtype
    have hidx : ¬ 2 ∣ (S.subgroupOf N).relIndex ((N ⊓ L).subgroupOf N) := by
      rw [Subgroup.relIndex_subgroupOf (inf_le_left : N ⊓ L ≤ N)]
      intro hd
      refine hS.2.2 (hd.trans ?_)
      exact ⟨(N ⊓ L).relIndex L,
        (Subgroup.relIndex_mul_relIndex S (N ⊓ L) L hSNL inf_le_right).symm⟩
    have hdec : ∀ g : N, ∃ a ∈ (N ⊓ L).subgroupOf N,
        ∃ b ∈ (Subgroup.normalizer (S : Set Y)).subgroupOf N, g = a * b := by
      intro g
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_mem_normalizer hS₀Q hp₀ hidx g
      exact ⟨a, ha, b, mem_normalizer_of_subgroupOf hSN hb, hab⟩
    have hKM : (N ⊓ L).subgroupOf N ≤ M.subgroupOf N := fun z hz =>
      Subgroup.mem_sup_left (Subgroup.mem_inf.mp hz).2
    refine exists_pElement_not_mem hp hKM hdec (x := ⟨x, hxN⟩) ?_ hxM
    obtain ⟨k, hk⟩ := hxp
    exact ⟨k, (Subgroup.orderOf_coe (⟨x, hxN⟩ : N)).symm.trans hk⟩
  obtain ⟨j, hj1, hj2⟩ := exists_last_power hyp hyM
  set r : Y := ((y ^ p ^ j : N) : Y) with hrdef
  have hrN : r ∈ N := (y ^ p ^ j).2
  have hrS : r ∈ Subgroup.normalizer (S : Set Y) := Subgroup.pow_mem _ hyH _
  have hrM : r ∉ M := hj1
  have hrpM : r ^ p ∈ M := hj2
  have hrp : ∃ k, orderOf r = p ^ k := by
    obtain ⟨k, hk⟩ := hyp
    have h1 : orderOf (y ^ p ^ j) ∣ p ^ k := hk ▸ orderOf_pow_dvd _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h1
    exact ⟨i, (Subgroup.orderOf_coe _).trans hi⟩
  have hrpC : r ^ p ∉ Subgroup.centralizer (L : Set Y) := by
    intro hrC
    obtain ⟨i, hi⟩ := hrp
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hrM (hi ▸ M.one_mem)
    have hsN : r ^ p ^ (i - 1) ∈ N := N.pow_mem hrN _
    have hs : orderOf (r ^ p ^ (i - 1)) = p := by
      have hdvd : p ^ (i - 1) ∣ orderOf r := by rw [hi]; exact pow_dvd_pow p (Nat.sub_le i 1)
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hi]
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simp [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
    have hsL : r ^ p ^ (i - 1) ∈ L := hA _ hsN hs
    by_cases hi1 : i = 1
    · subst hi1
      simp only [Nat.sub_self, pow_zero, pow_one] at hsL
      exact hrM (Subgroup.mem_sup_left hsL)
    · have hsC : r ^ p ^ (i - 1) ∈ Subgroup.centralizer (L : Set Y) := by
        have : r ^ p ^ (i - 1) = (r ^ p) ^ p ^ (i - 2) := by
          rw [← pow_mul, ← pow_succ']
          congr 2
          omega
        rw [this]
        exact Subgroup.pow_mem _ hrC _
      have hz : (⟨r ^ p ^ (i - 1), hsL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hsC) g g.2)
      apply hpZ
      have h1 := orderOf_dvd_natCard (⟨_, hz⟩ : ↥(Subgroup.center ↥L))
      rwa [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨r ^ p ^ (i - 1), hsL⟩ : ↥L), hs] at h1
  have hcrit := hC Y L S P hL hcl hnr hS hP p hp hp2 hpZ r (hNL hrN) hrS hrp hrM hrpM hrpC
  have hle : pElementSubgroup 2 P ⊔ Subgroup.zpowers r ≤ N :=
    sup_le hPN ((Subgroup.zpowers_le).mpr hrN)
  have h3 := CFSG.SectionRank.pRank_mono hp.one_lt hle
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
