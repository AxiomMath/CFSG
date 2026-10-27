module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem p65r3_le_pRank (hp : p.Prime) {E H : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

private theorem p65r3_normalizer_zpowers_le (hS : Situation G p P M) {y : G} (hyM : y ∈ M)
    (hyo : orderOf y = p) {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hEy : E ≤ centralizer ({y} : Set G)) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hE3 : 3 ≤ Open.pRank p E := p65r3_le_pRank hprime le_rfl hE hEc
  have hCM : centralizer ({y} : Set G) ≤ M :=
    hS.centralizer_le_of_pRank hyM hyo
      (hE3.trans (CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf hEM hEy)))
  obtain ⟨S, hES, hSC, hSp, hSidx⟩ :=
    RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hEy (elementary_isPGroup p E hE)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer ({y} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hSC, hSp, hSidx⟩
  have hS3 : 3 ≤ Open.pRank p S := p65r3_le_pRank hprime hES hE hEc
  have hSM : normalizer (S : Set G) ≤ M := hS.normalizer_le hSp (hSC.trans hCM) (by omega)
  exact (RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
    (RankThreeTheoremC.normalizer_zpowers_le_normalizer_centralizer y) hSsyl).trans (sup_le hCM hSM)

private theorem p65r3_normalizer_le_of_le_elem (hS : Situation G p P M) {E S : Subgroup G}
    (hEM : E ≤ M) (hEa : IsElemAbelian p E) (hE3 : Nat.card E = p ^ 3) (hSE : S ≤ E)
    (hS1 : 1 ≤ Open.pRank p S) : normalizer (S : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hSp : IsPGroup p S := (elementary_isPGroup p E hEa).to_le hSE
  have hSa : IsElemAbelian p S := hEa.mono hSE
  by_cases h2 : 2 ≤ Open.pRank p S
  · exact hS.normalizer_le hSp (hSE.trans hEM) h2
  · obtain ⟨k, hk⟩ := hSp.exists_card_eq
    have hk1 : k ≤ Open.pRank p S := p65r3_le_pRank hprime le_rfl hSa hk
    have hne : S ≠ ⊥ := by
      rintro rfl
      obtain ⟨A, hAS, -, hAc⟩ := pRank_attained p ⊥ hS1
      rw [le_bot_iff.1 hAS, Subgroup.card_bot] at hAc
      have := Nat.pow_eq_one.1 hAc.symm
      have := hprime.two_le
      omega
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hyp : (y : G) ^ p = 1 := hSa.2 y y.2
    have hyne : (y : G) ≠ 1 := fun h' => hy1 (Subtype.ext h')
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq S (by simpa using hk))
    have hcard : Nat.card S = p := by
      rw [hk, show k = 1 by omega, pow_one]
    have hzp : zpowers (y : G) = S := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 y.2) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hyp hyne, hcard]
    rw [← hzp]
    exact p65r3_normalizer_zpowers_le hS (hEM (hSE y.2)) (orderOf_eq_prime hyp hyne) hEM hEa hE3
      fun e he => mem_centralizer_singleton_iff.2 (hEa.comm he (hSE y.2))

private theorem p65r3_exists_mem_normalizer_not_mem {q : ℕ} [Fact q.Prime] {Q R : Subgroup G}
    (hR : IsPGroup q R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem p65r3_coprime_two_mul {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p)
    (hp : p.Prime) {E : Subgroup G} (hE : IsPGroup f E) : Nat.Coprime (Nat.card E) (2 * p) := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
    ((Nat.coprime_primes hf Nat.prime_two).2 hf2) ((Nat.coprime_primes hf hp).2 hfp))

private theorem p65r3_normalizer_ne_top (hS : Situation G p P M) (hx : Point P M x)
    {W : Subgroup G} (hW1 : W ≠ ⊥) (hWM : W ≤ M) : normalizer (W : Set G) ≠ ⊤ := by
  intro htop
  haveI := hS.simple
  have hnormal : W.Normal := normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hbot | hW
  · exact hW1 hbot
  · have hMtop : M = ⊤ := top_le_iff.mp (hW ▸ hWM)
    exact hx.not_le (hMtop ▸ le_top)

set_option linter.unusedVariables false in
theorem p65_rankThree_apply (hK : KFactP65RankThree) (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {W : Subgroup G} (hW1 : W ≠ ⊥) (hWM : W ≤ M)
    (hBW : zpowers x ⊔ zpowers z ≤ normalizer (W : Set G))
    (hHM : ¬ normalizer (W : Set G) ≤ M) {Q : Subgroup G} (hQH : Q ≤ normalizer (W : Set G))
    (hQ : IsPGroup p Q) (hQidx : ¬ p ∣ (Q.subgroupOf (normalizer (W : Set G))).index)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q) (hrank : 3 ≤ Open.pRank p (normalizer (W : Set G))) :
    (∃ N : Subgroup G, N ≤ normalizer (W : Set G) ∧
      (N.subgroupOf (normalizer (W : Set G))).Normal ∧
      (N.subgroupOf (normalizer (W : Set G))).index = p) ∧
    (∀ W' : Subgroup G, W' ≤ normalizer (W : Set G) →
      zpowers x ⊔ zpowers z ≤ normalizer (W' : Set G) → Nat.Coprime (Nat.card W') (2 * p) →
      W' ≤ rankThreePrimeCore p (normalizer (W : Set G))) ∧
    ∃ Q₀ : Subgroup G, Q₀ ≤ Q ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
      ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
        ∃ g ∈ normalizer (W : Set G) ⊓ normalizer (Q₀ : Set G), g * a * g⁻¹ ∈ zpowers b := by
  have hprime := hS.prime
  have hpl := plane_of_central hS hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hQM : Q ≤ M := le_of_plane_le hS hBP (centralizer_plane_le hS hz) hQ hBQ
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hcat : CatalogSimpleSections ↥(normalizer (W : Set G)) :=
    catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper _
      (p65r3_normalizer_ne_top hS hx hW1 hWM)
  have hQrk : 3 ≤ Open.pRank p Q := by
    rw [RankThreeTheoremC.pRank_eq_of_sylow hprime hQH hQ hQidx]
    exact hrank
  refine hK G p (normalizer (W : Set G)) (normalizer (W : Set G) ⊓ M) Q (zpowers x ⊔ zpowers z) x
    hprime hS.p_ge hcat inf_le_left (fun h => hHM (le_inf_iff.1 h).2) hQH hQ hQidx hQrk
    (le_inf hQH hQM) hBQ hpl.isElemAbelian hpl.card_eq hxB (hx.ne_one hprime)
    hpl.mem_of_mem_centralizer
    ((CFSG.SectionRank.pRank_mono hprime.one_lt inf_le_left).trans (hx.pRank_centralizer_le hS))
    ?_ ?_
  · intro S hSQ hS2 g hg
    exact ⟨hg.2, hS.normalizer_le (hQ.to_le hSQ) (hSQ.trans hQM) hS2 hg.1⟩
  · intro E hEQ hEa hE3 S hSE hS1 g hg
    exact ⟨hg.2, p65r3_normalizer_le_of_le_elem hS (hEQ.trans hQM) hEa hE3 hSE hS1 hg.1⟩

set_option linter.unusedVariables false in
theorem p65_rank_three_enlarge (hK : KFactP65RankThree) (hS : Situation G p P M)
    (hx : Point P M x) (hz : Central P z) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p)
    {F Fs : Subgroup G} (hF : IsPGroup f F) (hF1 : F ≠ ⊥)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) (hFs : IsPGroup f Fs) (hFsM : Fs ≤ M)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) (hFFs : F < Fs)
    (hrank : 3 ≤ Open.pRank p (normalizer (F : Set G))) :
    ∃ E : Subgroup G, F < E ∧ IsPGroup f E ∧ zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) ∧
      E ≤ rankThreePrimeCore p (normalizer (F : Set G)) ∧
      rankThreePrimeCore p (normalizer (F : Set G)) ≤ M := by
  have hprime := hS.prime
  haveI : Fact f.Prime := ⟨hf⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hFM : F ≤ M := hFFs.le.trans hFsM
  obtain ⟨Q, hBQ, hQH, hQp, hQidx⟩ := RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hBF hB3
  obtain ⟨-, hβ, -⟩ := p65_rankThree_apply hK hS hx hz hF1 hFM hBF hHM hQH hQp hQidx hBQ hrank
  have hEp : IsPGroup f (Fs ⊓ normalizer (F : Set G) : Subgroup G) := hFs.to_le inf_le_left
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) :
      Set G) := (le_inf hBFs (hBF.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  refine ⟨Fs ⊓ normalizer (F : Set G), ?_, hEp, hBE,
    hβ _ inf_le_right hBE (p65r3_coprime_two_mul hf hf2 hfp hprime hEp),
    p65_primeCore_le_of_rank_three hS hx hz hQH hQp hQidx hrank hBQ⟩
  obtain ⟨y, hyFs, hyN, hyF⟩ := p65r3_exists_mem_normalizer_not_mem hFs hFFs
  refine lt_of_le_of_ne (le_inf hFFs.le le_normalizer) fun heq => hyF ?_
  rw [heq]
  exact ⟨hyFs, hyN⟩

private theorem p65r3_exists_hom_extension {Γ Λ Q : Type*} [Group Γ] [Group Λ] [Group Q]
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
private theorem p65r3_mem_of_coprime {H N : Subgroup G} (hNn : (N.subgroupOf H).Normal)
    (hNp : (N.subgroupOf H).index = p) {g : G} (hgH : g ∈ H)
    (hg : Nat.Coprime p (orderOf g)) : g ∈ N := by
  have := hNn
  have hcard : Nat.card (H ⧸ N.subgroupOf H) = p := hNp
  have h1 : orderOf (QuotientGroup.mk' (N.subgroupOf H) ⟨g, hgH⟩) ∣ p := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk' (N.subgroupOf H) ⟨g, hgH⟩) ∣ orderOf g := by
    have h2' : orderOf (⟨g, hgH⟩ : H) = orderOf g := (Subgroup.orderOf_coe (⟨g, hgH⟩ : H)).symm
    rw [← h2']
    exact orderOf_map_dvd _ _
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hg) h2
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3))

private theorem p65r3_false_of_normal_index (hS : Situation G p P M) {H N Q : Subgroup G}
    (hdec : ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ H, m = d * n)
    (hNn : (N.subgroupOf H).Normal) (hNp : (N.subgroupOf H).index = p) (hQH : Q ≤ H)
    (hQM : Q ≤ M) (hQidx : ¬ p ∣ (Q.subgroupOf H).index) : False := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDM, hMD, hDp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have := hNn
  have hDn : ((rankThreePrimeCore p M).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDM).2 hMD
  let ψ : ↥(M ⊓ H) →* ↥H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion inf_le_right)
  let ι : ↥(M ⊓ H) →* ↥M := Subgroup.inclusion inf_le_left
  have hdec' : ∀ m : ↥M, ∃ d ∈ (rankThreePrimeCore p M).subgroupOf M, ∃ n : ↥(M ⊓ H),
      m = d * ι n := by
    intro m
    obtain ⟨d, hd, n, hn, hmdn⟩ := hdec m m.2
    exact ⟨⟨d, hDM hd⟩, mem_subgroupOf.2 hd, ⟨n, hn⟩, Subtype.ext hmdn⟩
  have hψ' : ∀ u : ↥(M ⊓ H), ι u ∈ (rankThreePrimeCore p M).subgroupOf M → ψ u = 1 := by
    intro u hu
    have huD : (u : G) ∈ rankThreePrimeCore p M := mem_subgroupOf.1 hu
    have huH : (u : G) ∈ H := u.2.2
    have hord : Nat.Coprime p (orderOf (u : G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ huD) hDp
    exact (QuotientGroup.eq_one_iff _).2
      (mem_subgroupOf.2 (p65r3_mem_of_coprime hNn hNp huH hord))
  have hsurj : Function.Surjective ψ := by
    have hcard : Nat.card (↥H ⧸ N.subgroupOf H) = p := hNp
    have : Fact (Nat.Prime (Nat.card (↥H ⧸ N.subgroupOf H))) :=
      ⟨by rw [hcard]; exact hprime⟩
    obtain ⟨q, hqQ, hqN⟩ : ∃ q ∈ Q, q ∉ N := by
      by_contra hcon
      push Not at hcon
      have hdvd := relIndex_dvd_of_le_left H (show Q ≤ N from hcon)
      have h3 : N.relIndex H = p := hNp
      rw [h3] at hdvd
      exact hQidx hdvd
    rcases eq_bot_or_eq_top_of_prime_card ψ.range with hbot | htop
    · exfalso
      have hmem : ψ ⟨q, hQM hqQ, hQH hqQ⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hbot, mem_bot] at hmem
      exact hqN (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmem))
    · exact MonoidHom.range_eq_top.1 htop
  obtain ⟨φ, hφ⟩ := p65r3_exists_hom_extension ((rankThreePrimeCore p M).subgroupOf M) ι ψ hdec'
    hψ'
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := hsurj y
    exact ⟨ι n, hφ n⟩
  have hker : φ.ker.index = p := by
    rw [index_ker, MonoidHom.range_eq_top.2 hφsurj, card_top]
    exact hNp
  haveI := φ.normal_ker
  have hpq : IsPGroup p (↥M ⧸ φ.ker) := IsPGroup.of_card (n := 1) (by
    rw [← Subgroup.index, hker, pow_one])
  have htop := eq_top_of_isPGroup_quotient hS φ.ker hpq
  rw [htop, index_top] at hker
  exact hprime.one_lt.ne hker

set_option linter.unusedVariables false in
theorem p65_false_of_isMax (hK : KFactP65RankThree) (hS : Situation G p P M)
    (hx : Point P M x) (hz : Central P z) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p)
    {F : Subgroup G} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) (hF1 : F ≠ ⊥)
    (hHM : ¬ normalizer (F : Set G) ≤ M)
    (hM1 : Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)))
    (hM2 : (∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n) ∨
     (∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ p →
        ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧
          ∀ g ∈ M ⊓ normalizer (E : Set G), g * a * g⁻¹ ∉ zpowers b)) : False := by
  have hprime := hS.prime
  obtain ⟨⟨hFM, -, hBF⟩, -⟩ := hF
  have hpl := plane_of_central hS hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hrank : 3 ≤ Open.pRank p (normalizer (F : Set G)) := by
    have h4 := hS.four_le_pRank
    exact (by omega : 3 ≤ Open.pRank p (P : Subgroup G)).trans
      (hM1.trans (CFSG.SectionRank.pRank_mono hprime.one_lt inf_le_right))
  obtain ⟨Q, hBQ, hQH, hQp, hQidx⟩ := RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hBF hB3
  have hQM : Q ≤ M := le_of_plane_le hS hBP (centralizer_plane_le hS hz) hQp hBQ
  obtain ⟨hN, -, hQ0⟩ := p65_rankThree_apply hK hS hx hz hF1 hFM hBF hHM hQH hQp hQidx hBQ hrank
  rcases hM2 with hdec | hE
  · obtain ⟨N, -, hNn, hNp⟩ := hN
    exact p65r3_false_of_normal_index hS hdec hNn hNp hQH hQM hQidx
  · obtain ⟨Q₀, hQ0Q, hQ0a, hQ0c, hQ0g⟩ := hQ0
    obtain ⟨a, ha, ha1, b, hb, hb1, hab⟩ := hE Q₀ (hQ0Q.trans hQM) hQ0a hQ0c
    obtain ⟨g, hg, hga⟩ := hQ0g a ha ha1 b hb hb1
    have hQ0rk : 2 ≤ Open.pRank p Q₀ := by
      have := p65r3_le_pRank hprime le_rfl hQ0a hQ0c
      have := hS.p_ge
      omega
    have hQ0M : normalizer (Q₀ : Set G) ≤ M :=
      hS.normalizer_le (elementary_isPGroup p Q₀ hQ0a) (hQ0Q.trans hQM) hQ0rk
    exact hab g ⟨hQ0M hg.2, hg.2⟩ hga

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
