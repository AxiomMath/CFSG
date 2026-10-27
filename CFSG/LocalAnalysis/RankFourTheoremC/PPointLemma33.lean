module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.RankThree.PartOne.HNB.Tools
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator {A D : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hD : g ∈ normalizer (D : Set G)) : g ∈ normalizer ((⁅A, D⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hD ⊢
  rw [Subgroup.map_commutator, hA, hD]

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hA, hB]

omit [Finite G] in
theorem mem_normalizer_centralizer_of_le {L : Subgroup G} {g : G}
    (hg : g ∈ centralizer (L : Set G)) :
    g ∈ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) :=
  normalizer_le_normalizer_centralizer L (centralizer_le_normalizer L hg)

omit [Finite G] in
theorem le_normalizer_pCoreOf_two (H : Subgroup G) : H ≤ normalizer (pCoreOf 2 H : Set G) := by
  have hn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  exact le_normalizer_of_normal_subgroupOf
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H)

omit [Finite G] in
theorem commute_of_isElemAbelian {p : ℕ} {D : Subgroup G} (hD : IsElemAbelian p D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hD ha hb

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) : IsElemAbelian p (zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

omit [Finite G] in
theorem exists_conj_to_sylow {p : ℕ} [Fact p.Prime] [Finite G] {Q E L₀ : Subgroup G} {x : G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q (centralizer ({x} : Set G))) (hE : IsPGroup p E)
    (hEL : E ≤ centralizer (L₀ : Set G)) {g : G}
    (hg : L₀ = (zpowers x).map (MulAut.conj g).toMonoidHom) :
    ∃ k : G, E.map (MulAut.conj k).toMonoidHom ≤ Q ∧
      L₀.map (MulAut.conj k).toMonoidHom = zpowers x := by
  have hgx : g * x * g⁻¹ ∈ L₀ := hg ▸ ⟨x, mem_zpowers x, rfl⟩
  have hE₁C : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm : e * (g * x * g⁻¹) = (g * x * g⁻¹) * e :=
      (mem_centralizer_iff.mp (hEL he) _ hgx).symm
    change g⁻¹ * e * g⁻¹⁻¹ * x = x * (g⁻¹ * e * g⁻¹⁻¹)
    calc g⁻¹ * e * g⁻¹⁻¹ * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [hcomm]
      _ = x * (g⁻¹ * e * g⁻¹⁻¹) := by group
  obtain ⟨c, hcC, hcE⟩ := exists_conj_le_of_isSylowOf hQ hE₁C (hE.map _)
  refine ⟨c * g⁻¹, ?_, ?_⟩
  · have : (MulAut.conj (c * g⁻¹)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom :=
      MonoidHom.ext fun _ => by simp [mul_assoc]
    rw [this, ← Subgroup.map_map]
    exact hcE
  · have hcomp : (MulAut.conj (c * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj c).toMonoidHom :=
      MonoidHom.ext fun _ => by simp [mul_assoc]
    rw [hg, Subgroup.map_map, hcomp, MonoidHom.map_zpowers]
    have hcx : c * x * c⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_singleton_iff.mp hcC
    change zpowers (c * x * c⁻¹) = zpowers x
    rw [hcx]

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem false_of_bad_conj_line [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {D L₀ : Subgroup G} (hDQ : D ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hD : IsElemAbelian p D) (hL₀D : L₀ ≤ D)
    (hL₀bad : ⁅pCoreOf 2 M ⊓ centralizer (L₀ : Set G), D⁆ ≠ ⊥) {g : G}
    (hg : L₀ = (zpowers x).map (MulAut.conj g).toMonoidHom) : False := by
  have hp : p.Prime := Fact.out
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  have hQM : Q ≤ M := inf_le_left.trans hPM
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) := le_normalizer_pCoreOf_two M
  obtain ⟨y, hyQ, hyc, hyp, hyx⟩ := h.exists_central_of_not_mem_zpowers hp2 h243 hS hFC hloc
  have hxp : x ^ p = 1 := by rw [← h.elem.2.1]; exact pow_orderOf_eq_one x
  have hyp' : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hxQ : x ∈ Q := ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  set A₂ : Subgroup G := zpowers x ⊔ zpowers y with hA₂
  have hxy : x * y = y * x := hyc x hxQ
  have hA₂el : IsElemAbelian p A₂ := by
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p
      (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hyp') ?_
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun b hb => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq
  have hA₂Q : A₂ ≤ Q := sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr hyQ)
  have hA₂z : ∀ a ∈ A₂, ∀ q ∈ Q, a * q = q * a := by
    have : A₂ ≤ centralizer (Q : Set G) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_iff.mpr fun q hq => mem_centralizer_singleton_iff.mp hq.2
      · exact mem_centralizer_iff.mpr fun q hq => hyc q hq
    exact fun a ha q hq => (mem_centralizer_iff.mp (this ha) q hq).symm
  have hA₂card : Nat.card A₂ = p ^ 2 := by
    have hycomm : ∀ e ∈ zpowers x, e * y = y * e := fun e he => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
      exact (Commute.zpow_left (show Commute x y from hxy) k).eq
    have hyx' : y ∉ zpowers x := hyx
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers x) hyp' hyx' hycomm,
      Nat.card_zpowers, h.elem.2.1]
    ring
  obtain ⟨E₃, hE₃Q, hE₃el, hE₃card⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp Q
  have hE₃c : p ^ 3 ≤ Nat.card E₃ := hE₃card ▸ Nat.pow_le_pow_right hp.pos h.three_le
  obtain ⟨E, hDE, hEQ, hEel, hE3⟩ :=
    exists_elemAbelian_sup hp hD hDQ hA₂el hA₂card hA₂Q hA₂z hE₃el hE₃Q hE₃c
  have hDM : D ≤ M := (hDQ.trans inf_le_left).trans hPM
  have hEM : E ≤ M := hEQ.trans hQM
  have hEp : IsPGroup p E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hEel
  have hDp : IsPGroup p D := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p D hD
  set A : Subgroup G := T₀ ⊓ centralizer (L₀ : Set G) with hA
  set T : Subgroup G := ⁅A, D⁆ with hT
  have hEL : E ≤ centralizer (L₀ : Set G) := fun e he =>
    mem_centralizer_iff.mpr fun l hl => commute_of_isElemAbelian hEel (hDE (hL₀D hl)) he
  have hEA : E ≤ normalizer (A : Set G) := fun e he =>
    mem_normalizer_inf' (hMT₀ (hEM he)) (mem_normalizer_centralizer_of_le (hEL he))
  have hDA : D ≤ normalizer (A : Set G) := fun d hd => hEA (hDE hd)
  have hED : E ≤ normalizer (D : Set G) := fun e he => centralizer_le_normalizer D
    (mem_centralizer_iff.mpr fun d hd => commute_of_isElemAbelian hEel (hDE hd) he)
  have hA2 : IsPGroup 2 A := hT₀2.to_le inf_le_left
  have hTA : T ≤ A := Subgroup.commutator_le.mpr fun a ha d hd => by
    have h1 := (mem_normalizer_iff.mp (hDA hd) a⁻¹).mp (A.inv_mem ha)
    have h2 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact A.mul_mem ha h1
  have hTT : ⁅T, D⁆ = T := by
    have hcop : Nat.Coprime (Nat.card D) (Nat.card A) := by
      obtain ⟨a, ha⟩ := hDp.exists_card_eq
      obtain ⟨b, hb⟩ := hA2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent A := hA2.isNilpotent
    exact CFSG.RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable D A hDA hcop
      inferInstance
  have hT2 : IsPGroup 2 T := hA2.to_le hTA
  have hTL : T ≤ centralizer (L₀ : Set G) := hTA.trans inf_le_right
  have hET : E ≤ normalizer (T : Set G) := fun e he =>
    mem_normalizer_commutator (hEA he) (hED he)
  obtain ⟨k, hkE, hkL⟩ := exists_conj_to_sylow h.sylow hEp hEL hg
  set κ : G →* G := (MulAut.conj k).toMonoidHom with hκ
  have hκinj : Function.Injective κ := (MulAut.conj k).injective
  have hTsC : T.map κ ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    have hxL : x ∈ L₀.map κ := hkL ▸ mem_zpowers x
    obtain ⟨l, hl, hlx⟩ := hxL
    rw [mem_centralizer_singleton_iff, ← hlx]
    have hlt := mem_centralizer_iff.mp (hTL ht) l hl
    calc κ t * κ l = κ (t * l) := (map_mul κ t l).symm
      _ = κ (l * t) := congrArg κ hlt.symm
      _ = κ l * κ t := map_mul κ l t
  have hEsel : IsElemAbelian p (E.map κ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEel κ
  have hEs3 : p ^ 3 ≤ Nat.card (E.map κ) := by
    rw [Subgroup.card_map_of_injective hκinj]
    exact hE3
  have hTs2 : IsPGroup 2 (T.map κ) := hT2.map κ
  have hTsEs : E.map κ ≤ normalizer ((T.map κ : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map κ ⟨e, hET he, rfl⟩
  have hTscop : p.Coprime (Nat.card (T.map κ)) := by
    obtain ⟨b, hb⟩ := hTs2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hcomm := h.commutator_le_primeCore hp2 h243 h244 hsig hS hFC hloc hkE hEsel hEs3 hTsC
    hTscop hTsEs
  have hTsDs : ⁅T.map κ, D.map κ⁆ = T.map κ := by
    rw [← Subgroup.map_commutator, hTT]
  have hTsO : T.map κ ≤ GLBPrimeCore p C := by
    calc T.map κ = ⁅T.map κ, D.map κ⁆ := hTsDs.symm
      _ ≤ ⁅T.map κ, E.map κ⁆ := Subgroup.commutator_mono le_rfl (Subgroup.map_mono hDE)
      _ ≤ _ := hcomm
  have hTsne : T.map κ ≠ ⊥ := fun hb => hL₀bad
    ((Subgroup.map_eq_bot_iff_of_injective T hκinj).mp hb)
  obtain ⟨n, hn⟩ := hTs2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hTsne (Subgroup.card_eq_one.mp (by simpa using hn))
  have h2dvd : 2 ∣ Nat.card (T.map κ) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact h.not_two_dvd_card_primeCore hS hD1 hloc (h2dvd.trans (Subgroup.card_dvd_of_le hTsO))

theorem not_exists_conj_lines [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {D : Subgroup G} (hDQ : D ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) :
    ¬ ∃ S : Finset (Subgroup G), S.card = p ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = p ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  classical
  rintro ⟨S, hScard, hS'⟩
  have hp : p.Prime := Fact.out
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hDM : D ≤ M := (hDQ.trans inf_le_left).trans hPM
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) := le_normalizer_pCoreOf_two M
  have hcop : p.Coprime (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hC : ∀ d ∈ D, (∀ t ∈ T₀, d * t = t * d) → d = 1 := by
    intro d hd hdc
    have hdT : d ∈ T₀ := hS.charTwo M hloc.maxLocal.1
      ⟨hDM hd, mem_centralizer_iff.mpr fun t ht => (hdc t ht).symm⟩
    obtain ⟨k, hk⟩ := hT₀2 ⟨d, hdT⟩
    have h2 : orderOf d ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hp' : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one (hD.2 d hd)
    have hcoprime : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd hp' h2))
  obtain ⟨L₁, L₂, hne, ⟨hL₁D, hL₁c, hL₁b⟩, ⟨hL₂D, hL₂c, hL₂b⟩⟩ :=
    exists_two_bad_lines hp hD hDcard (fun d hd => hMT₀ (hDM hd)) hcop hC
  have hkey : ∀ L ∈ S, ⁅T₀ ⊓ centralizer (L : Set G), D⁆ ≠ ⊥ → False := fun L hL hbad => by
    obtain ⟨hLD, -, g, hg⟩ := hS' L hL
    exact h.false_of_bad_conj_line hp2 h243 h244 hsig hS hD1 hFC hloc hDQ hD hLD hbad hg
  by_cases h1 : L₁ ∈ S
  · exact hkey L₁ h1 hL₁b
  by_cases h2 : L₂ ∈ S
  · exact hkey L₂ h2 hL₂b
  have hcard : (insert L₁ (insert L₂ S)).card = p + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne, h1]), Finset.card_insert_of_notMem h2,
      hScard]
  have := card_lines_le hp hDcard (insert L₁ (insert L₂ S)) (by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact ⟨hL₁D, hL₁c⟩
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact ⟨hL₂D, hL₂c⟩
    obtain ⟨hLD, hLc, -⟩ := hS' L hL
    exact ⟨hLD, hLc⟩)
  omega

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
