module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Max
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Signal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Step0
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10h2_exists_hom_extension {Γ Λ Q : Type*} [Group Γ] [Group Λ] [Group Q]
    (D : Subgroup Γ) [D.Normal] (ι : Λ →* Γ) (ψ : Λ →* Q)
    (hdec : ∀ m : Γ, ∃ d ∈ D, ∃ n : Λ, m = d * ι n) (hψ : ∀ u : Λ, ι u ∈ D → ψ u = 1) :
    ∃ φ : Γ →* Q, ∀ n : Λ, φ (ι n) = ψ n := by
  let q : Λ →* Γ ⧸ D := (QuotientGroup.mk' D).comp ι
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨d, hd, n, rfl⟩ := hdec m
    refine ⟨n, ?_⟩
    have h1 : ((d : Γ) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff d).2 hd
    simp [q, QuotientGroup.mk_mul, h1]
  have hker : q.ker ≤ ψ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact hψ u ((QuotientGroup.eq_one_iff _).1 hu)
  refine ⟨(q.liftOfSurjective hq ⟨ψ, hker⟩).comp (QuotientGroup.mk' D), fun n => ?_⟩
  exact q.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hq) ⟨ψ, hker⟩ n

omit [Finite G] in
private theorem r10h2_comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
private theorem r10h2_isElemAbelian_of_le {p : ℕ} {S E : Subgroup G} (hSE : S ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p S := CFSG.Open.IsElemAbelian.mono hE hSE

omit [Finite G] in
private theorem r10h2_isPGroup {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

private theorem r10h2_coprime_six {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f) {E : Subgroup G}
    (hE : IsPGroup f E) : Nat.Coprime (Nat.card E) 6 := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  rw [hk]
  refine Nat.Coprime.pow_left k ?_
  have h2 : Nat.Coprime f 2 := (Nat.coprime_primes hf Nat.prime_two).2 (by omega)
  have h3 : Nat.Coprime f 3 := (Nat.coprime_primes hf Nat.prime_three).2 (by omega)
  simpa using Nat.Coprime.mul_right h2 h3

private theorem r10h2_not_mem_zpowers {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) : x ∉ zpowers z := by
  intro hx
  have hpl := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have hB : zpowers x ⊔ zpowers z = zpowers z := sup_eq_right.2 (zpowers_le.2 hx)
  have h1 := hpl.card_eq
  rw [hB, Nat.card_zpowers, orderOf_eq_prime h.central.pow_eq_one h.central.ne_one] at h1
  norm_num at h1

private theorem r10h2_normalizer_ne_top {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {F : Subgroup G} (hF1 : F ≠ ⊥) (hFM : F ≤ M) :
    normalizer (F : Set G) ≠ ⊤ := by
  intro htop
  have := h.setting.simple
  have hnormal : F.Normal := normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hbot | hF
  · exact hF1 hbot
  · exact CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.setting.nonab M
      h.situation.isCoreMaxLocal.1.1 (top_le_iff.mp (hF ▸ hFM))

private theorem r10h2_normalizer_le_of_le_elem {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {E S : Subgroup G} (hEM : E ≤ M) (hEa : IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hSE : S ≤ E) (hS1 : 1 ≤ CFSG.Open.pRank 3 S) :
    normalizer (S : Set G) ≤ M := by
  have hS3 : IsPGroup 3 S := (r10h2_isPGroup hEa).to_le hSE
  have hSa : IsElemAbelian 3 S := r10h2_isElemAbelian_of_le hSE hEa
  by_cases h2 : 2 ≤ CFSG.Open.pRank 3 S
  · exact normalizer_le_of_le_of_two_le_pRank h.setting h.u0 h.situation.mem_sigmaA
      h.situation.isCoreMaxLocal hS3 (hSE.trans hEM) h2
  · obtain ⟨k, hk⟩ := hS3.exists_card_eq
    have hk1 : k ≤ CFSG.Open.pRank 3 S :=
      le_pRank_of_isElemAbelian Nat.prime_three le_rfl hSa hk
    have hne : S ≠ ⊥ := by
      rintro rfl
      obtain ⟨A, hAS, -, hAc⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 ⊥ hS1
      rw [le_bot_iff.1 hAS, Subgroup.card_bot] at hAc
      have := Nat.pow_eq_one.1 hAc.symm
      omega
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hy3 : (y : G) ^ 3 = 1 := hSa.2 y y.2
    have hyne : (y : G) ≠ 1 := fun h' => hy1 (Subtype.ext h')
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq S (by simpa using hk))
    have hcard : Nat.card S = 3 := by
      rw [hk, show k = 1 by omega]
      norm_num
    have hzp : zpowers (y : G) = S := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 y.2) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hy3 hyne, hcard]
    rw [← hzp]
    exact normalizer_zpowers_le_of_isElemAbelian_le_centralizer h (hEM (hSE y.2)) hyne hy3 hEM
      hEa hE27 fun e he => mem_centralizer_singleton_iff.2
        (r10h2_comm_of_isElemAbelian hEa he (hSE y.2))

private theorem r10h2_kfact {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) (hK2 : KFactRankThreeStructure) {F Q : Subgroup G} (hF1 : F ≠ ⊥)
    (hFM : F ≤ M) (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M)
    (hrank : 3 ≤ CFSG.Open.pRank 3 (normalizer (F : Set G)))
    (hQH : Q ≤ normalizer (F : Set G)) (hQ : IsPGroup 3 Q)
    (hQidx : ¬ 3 ∣ (Q.subgroupOf (normalizer (F : Set G))).index)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q) :
    (∃ N : Subgroup G, N ≤ normalizer (F : Set G) ∧
        (N.subgroupOf (normalizer (F : Set G))).Normal ∧
        (N.subgroupOf (normalizer (F : Set G))).index = 3) ∧
      ∀ D : Subgroup G, D ≤ normalizer (F : Set G) → IsElemAbelian 3 D → Nat.card D = 9 →
        ∀ W : Subgroup G, W ≤ normalizer (F : Set G) → D ≤ normalizer (W : Set G) →
          Nat.Coprime (Nat.card W) 6 → W ≤ rankThreePrimeCore 3 (normalizer (F : Set G)) := by
  have hpl := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have hQM : Q ≤ M := le_of_isPGroup_of_plane_le h hQ hBQ
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hKgrp : CFSG.IsKGroup (normalizer (F : Set G)) :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 h.setting.kProper) _
      (r10h2_normalizer_ne_top h hF1 hFM)
  have hQrk : 3 ≤ CFSG.Open.pRank 3 Q := by
    rw [pRank_eq_of_sylow Nat.prime_three hQH hQ hQidx]
    exact hrank
  have hxex : ∃ y ∈ normalizer (F : Set G), orderOf y = 3 ∧
      CFSG.Open.pRank 3 (centralizer ({y} : Set G) ⊓ normalizer (F : Set G)) = 2 := by
    refine ⟨x, hBF hxB, orderOf_eq_prime h.point.pow_eq_one h.point.ne_one, le_antisymm ?_ ?_⟩
    · exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) inf_le_left).trans
        (pRank_centralizer_le_two_of_mem_plane h hxB (r10h2_not_mem_zpowers h))
    · have hBC : zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) := fun b hb =>
        mem_centralizer_singleton_iff.2 (r10h2_comm_of_isElemAbelian hpl.isElemAbelian hb hxB)
      exact le_pRank_of_isElemAbelian Nat.prime_three (le_inf hBC hBF) hpl.isElemAbelian
        hpl.card_eq
  have hS : ∀ S : Subgroup G, S ≤ Q → 2 ≤ CFSG.Open.pRank 3 S →
      normalizer (S : Set G) ⊓ normalizer (F : Set G) ≤ normalizer (F : Set G) ⊓ M := by
    intro S hSQ hS2 g hg
    exact ⟨hg.2, normalizer_le_of_le_of_two_le_pRank h.setting h.u0 h.situation.mem_sigmaA
      h.situation.isCoreMaxLocal (hQ.to_le hSQ) (hSQ.trans hQM) hS2 hg.1⟩
  have hE : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ S : Subgroup G, S ≤ E → 1 ≤ CFSG.Open.pRank 3 S →
        normalizer (S : Set G) ⊓ normalizer (F : Set G) ≤ normalizer (F : Set G) ⊓ M := by
    intro E hEQ hEa hE27 S hSE hS1 g hg
    exact ⟨hg.2, r10h2_normalizer_le_of_le_elem h (hEQ.trans hQM) hEa hE27 hSE hS1 hg.1⟩
  have hy : ∀ y ∈ Q, y ≠ 1 → y ^ 3 = 1 →
      3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set G) ⊓ Q) →
      centralizer ({y} : Set G) ⊓ normalizer (F : Set G) ≤ normalizer (F : Set G) ⊓ M := by
    intro y hyQ hy1 hy3 hyr g hg
    obtain ⟨E, hEle, hEa, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three hyr
    exact ⟨hg.2, centralizer_le_of_isElemAbelian_le_centralizer h (hQM hyQ) hy1 hy3
      ((hEle.trans inf_le_right).trans hQM) hEa (by rw [hEc]; norm_num)
      (hEle.trans inf_le_left) hg.1⟩
  exact hK2 G (normalizer (F : Set G)) (normalizer (F : Set G) ⊓ M) Q hKgrp hQH hQ hQidx hQrk
    hxex inf_le_left (fun heq => hHM (inf_eq_left.1 heq)) (le_inf hQH hQM) hS hE hy

private theorem r10h2_primeCore_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 3 Q)
    (hQidx : ¬ 3 ∣ (Q.subgroupOf H).index) (hrank : 3 ≤ CFSG.Open.pRank 3 H)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q) : rankThreePrimeCore 3 H ≤ M := by
  obtain ⟨-, hHO, hO3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 H
  have hQM : Q ≤ M := le_of_isPGroup_of_plane_le h hQ hBQ
  have hQrk : 3 ≤ CFSG.Open.pRank 3 Q := by
    rw [pRank_eq_of_sylow Nat.prime_three hQH hQ hQidx]
    exact hrank
  obtain ⟨E, hEQ, hEa, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three hQrk
  have hE27 : Nat.card E = 27 := by rw [hEc]; norm_num
  have hE3 : 3 ≤ CFSG.Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three le_rfl hEa hEc
  obtain ⟨U, hUE, hUa, hUc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three (k := 2)
    (by omega : 2 ≤ CFSG.Open.pRank 3 E)
  refine le_of_plane_centralizers_le hUa (by rw [hUc]; norm_num) ?_
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hO3) fun u hu hu1 => ?_
  · exact hUE.trans (hEQ.trans (hQH.trans hHO))
  · have huE : u ∈ E := hUE hu
    exact centralizer_le_of_isElemAbelian_le_centralizer h (hQM (hEQ huE)) hu1 (hUa.2 u hu)
      (hEQ.trans hQM) hEa hE27 fun e he =>
        mem_centralizer_singleton_iff.2 (r10h2_comm_of_isElemAbelian hEa he huE)

omit [Finite G] in
private theorem r10h2_mem_of_coprime {H N : Subgroup G} (hNn : (N.subgroupOf H).Normal)
    (hN3 : (N.subgroupOf H).index = 3) {g : G} (hgH : g ∈ H)
    (hg : Nat.Coprime 3 (orderOf g)) : g ∈ N := by
  have := hNn
  have hcard : Nat.card (H ⧸ N.subgroupOf H) = 3 := hN3
  have h1 : orderOf (QuotientGroup.mk' (N.subgroupOf H) ⟨g, hgH⟩) ∣ 3 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk' (N.subgroupOf H) ⟨g, hgH⟩) ∣ orderOf g := by
    have h2' : orderOf (⟨g, hgH⟩ : H) = orderOf g := (Subgroup.orderOf_coe (⟨g, hgH⟩ : H)).symm
    rw [← h2']
    exact orderOf_map_dvd _ _
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hg) h2
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3))

theorem false_of_normal_index_three {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {H N Q : Subgroup G}
    (hdec : ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore 3 M, ∃ n ∈ M ⊓ H, m = d * n)
    (hNn : (N.subgroupOf H).Normal) (hN3 : (N.subgroupOf H).index = 3) (hQH : Q ≤ H)
    (hQM : Q ≤ M) (hQidx : ¬ 3 ∣ (Q.subgroupOf H).index) : False := by
  obtain ⟨hDM, hMD, hD3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M
  have := hNn
  have hDn : ((rankThreePrimeCore 3 M).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDM).2 hMD
  let ψ : ↥(M ⊓ H) →* ↥H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion inf_le_right)
  let ι : ↥(M ⊓ H) →* ↥M := Subgroup.inclusion inf_le_left
  have hdec' : ∀ m : ↥M, ∃ d ∈ (rankThreePrimeCore 3 M).subgroupOf M, ∃ n : ↥(M ⊓ H),
      m = d * ι n := by
    intro m
    obtain ⟨d, hd, n, hn, hmdn⟩ := hdec m m.2
    exact ⟨⟨d, hDM hd⟩, mem_subgroupOf.2 hd, ⟨n, hn⟩, Subtype.ext hmdn⟩
  have hψ' : ∀ u : ↥(M ⊓ H), ι u ∈ (rankThreePrimeCore 3 M).subgroupOf M → ψ u = 1 := by
    intro u hu
    have huD : (u : G) ∈ rankThreePrimeCore 3 M := mem_subgroupOf.1 hu
    have huH : (u : G) ∈ H := u.2.2
    have hord : Nat.Coprime 3 (orderOf (u : G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ huD) hD3
    exact (QuotientGroup.eq_one_iff _).2
      (mem_subgroupOf.2 (r10h2_mem_of_coprime hNn hN3 huH hord))
  have hsurj : Function.Surjective ψ := by
    have hcard : Nat.card (↥H ⧸ N.subgroupOf H) = 3 := hN3
    have : Fact (Nat.Prime (Nat.card (↥H ⧸ N.subgroupOf H))) :=
      ⟨by rw [hcard]; exact Nat.prime_three⟩
    obtain ⟨q, hqQ, hqN⟩ : ∃ q ∈ Q, q ∉ N := by
      by_contra hcon
      push Not at hcon
      have hdvd := relIndex_dvd_of_le_left H (show Q ≤ N from hcon)
      have h3 : N.relIndex H = 3 := hN3
      rw [h3] at hdvd
      exact hQidx hdvd
    rcases eq_bot_or_eq_top_of_prime_card ψ.range with hbot | htop
    · exfalso
      have hmem : ψ ⟨q, hQM hqQ, hQH hqQ⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hbot, mem_bot] at hmem
      exact hqN (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmem))
    · exact MonoidHom.range_eq_top.1 htop
  obtain ⟨φ, hφ⟩ :=
    r10h2_exists_hom_extension ((rankThreePrimeCore 3 M).subgroupOf M) ι ψ hdec' hψ'
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := hsurj y
    exact ⟨ι n, hφ n⟩
  have hker : φ.ker.index = 3 := by
    rw [index_ker, MonoidHom.range_eq_top.2 hφsurj, card_top]
    exact hN3
  exact no_normal_index_three_of_situation h.setting h.u0 h.situation φ.ker φ.normal_ker hker

theorem no_normal_index_three_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {f : ℕ} (hf : f.Prime) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index) :
    ∀ N : Subgroup G, N ≤ M ⊓ normalizer (Fs : Set G) →
      ((N.subgroupOf (M ⊓ normalizer (Fs : Set G)))).Normal →
        (N.subgroupOf (M ⊓ normalizer (Fs : Set G))).index ≠ 3 := by
  intro N _ hNn hN3
  obtain ⟨Q, -, hQH, -, hQidx⟩ :=
    exists_sylow_le_of_isPGroup Nat.prime_three
      (bot_le : (⊥ : Subgroup G) ≤ M ⊓ normalizer (Fs : Set G)) IsPGroup.of_bot
  have hQM : Q ≤ M := hQH.trans inf_le_left
  have hMH : M ⊓ (M ⊓ normalizer (Fs : Set G)) = M ⊓ normalizer (Fs : Set G) :=
    inf_eq_right.2 (inf_le_left : M ⊓ normalizer (Fs : Set G) ≤ M)
  have hdec : ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore 3 M,
      ∃ n ∈ M ⊓ (M ⊓ normalizer (Fs : Set G)), m = d * n := by
    intro m hm
    obtain ⟨d, hd, n, hn, hmn⟩ := exists_mul_mem_normalizer h hf hFsD hFs hsyl m hm
    exact ⟨d, hd, n, by rw [hMH]; exact hn, hmn⟩
  exact false_of_normal_index_three h hdec hNn hN3 hQH hQM hQidx

set_option linter.unusedVariables false in
theorem rank_three_enlarge {P : Sylow 3 G} {M : Subgroup G} {x z : G} (h : Setup65A G P M x z)
    (hK2 : KFactRankThreeStructure) {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f) {F Fs : Subgroup G}
    (hF : IsPGroup f F) (hF1 : F ≠ ⊥) (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) (hFs : IsPGroup f Fs)
    (hFsD : Fs ≤ rankThreePrimeCore 3 M)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) (hFFs : F < Fs)
    (hrank : 3 ≤ CFSG.Open.pRank 3 (normalizer (F : Set G))) :
    ∃ E : Subgroup G, F < E ∧ IsPGroup f E ∧ zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) ∧
      E ≤ rankThreePrimeCore 3 (normalizer (F : Set G)) ∧
      rankThreePrimeCore 3 (normalizer (F : Set G)) ≤ M := by
  have : Fact f.Prime := ⟨hf⟩
  have hpl := SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hFM : F ≤ M :=
    hFFs.le.trans (hFsD.trans (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M).1)
  obtain ⟨Q, hBQ, hQH, hQ3, hQidx⟩ := exists_sylow_le_of_isPGroup Nat.prime_three hBF hB3
  obtain ⟨-, hβ⟩ := r10h2_kfact h hK2 hF1 hFM hBF hHM hrank hQH hQ3 hQidx hBQ
  have hEp : IsPGroup f (Fs ⊓ normalizer (F : Set G) : Subgroup G) := hFs.to_le inf_le_left
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) :
      Set G) := (le_inf hBFs (hBF.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  refine ⟨Fs ⊓ normalizer (F : Set G), ?_, hEp, hBE,
    hβ _ hBF hpl.isElemAbelian (by rw [hpl.card_eq]; norm_num) _ inf_le_right hBE
      (r10h2_coprime_six hf hf5 hEp), r10h2_primeCore_le h hQH hQ3 hQidx hrank hBQ⟩
  obtain ⟨y, hyFs, hyN, hyF⟩ := exists_mem_normalizer_not_mem_of_lt hFs hFFs
  refine lt_of_le_of_ne (le_inf hFFs.le le_normalizer) fun heq => hyF ?_
  rw [heq]
  exact ⟨hyFs, hyN⟩

theorem false_of_sylow_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) (hK2 : KFactRankThreeStructure) {f : ℕ} (hf : f.Prime)
    (hf5 : 5 ≤ f) {F : Subgroup G} (hF : IsPGroup f F) (hF1 : F ≠ ⊥)
    (hFD : F ≤ rankThreePrimeCore 3 M)
    (hsyl : ¬ f ∣ (F.subgroupOf (rankThreePrimeCore 3 M)).index)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) : False := by
  have hFM : F ≤ M := hFD.trans (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M).1
  obtain ⟨R, hBR, -, hRN, hR3, -, -, hRk⟩ :=
    exists_sylow_three_normalizing h hf (by omega) hFD hF hsyl hBF
  have hrank : 3 ≤ CFSG.Open.pRank 3 (normalizer (F : Set G)) :=
    hRk.symm.le.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hRN)
  obtain ⟨Q, hRQ, hQH, hQ3, hQidx⟩ := exists_sylow_le_of_isPGroup Nat.prime_three hRN hR3
  have hBQ := hBR.trans hRQ
  obtain ⟨⟨N, -, hNn, hN3⟩, -⟩ := r10h2_kfact h hK2 hF1 hFM hBF hHM hrank hQH hQ3 hQidx hBQ
  exact false_of_normal_index_three h (exists_mul_mem_normalizer h hf hFD hF hsyl) hNn hN3
    hQH (le_of_isPGroup_of_plane_le h hQ3 hBQ) hQidx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
