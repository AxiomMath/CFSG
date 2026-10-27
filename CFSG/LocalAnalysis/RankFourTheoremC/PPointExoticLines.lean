module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp31
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma33
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.RankThree.PartOne.HNB.Tools
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

theorem card_le_mul_card_map_conjNormal {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} [K.Normal] (hDc : IsCyclic (centralizer (K : Set X))) {E : Subgroup X}
    (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card (E.map (MulAut.conjNormal : X →* MulAut K)) := by
  set D : Subgroup X := centralizer (K : Set X) with hD
  set φ : X →* MulAut K := MulAut.conjNormal with hφ
  have hker : ∀ g, g ∈ φ.ker ↔ g ∈ D := fun g => mem_ker_conjNormal
  set ψ : E →* MulAut K := φ.comp E.subtype with hψ
  have hker_card : Nat.card ψ.ker ≤ p := by
    let κ : ψ.ker →* D :=
      ((E.subtype.comp ψ.ker.subtype).codRestrict D fun x => (hker _).mp x.2)
    have hκ : Function.Injective κ := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : D → X) hxy))
    have : IsCyclic ψ.ker := isCyclic_of_injective κ hκ
    exact card_le_of_isCyclic_of_pow_eq_one hp.pos fun x =>
      Subtype.ext (Subtype.ext (hE.2 _ x.1.2))
  have hmap : E.map φ = ψ.range := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Subgroup.card_ker_mul_card_range ψ]
  exact Nat.mul_le_mul_right _ hker_card

theorem commute_of_coprime_of_card_at {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {i : TauCeti.CFSGIndex} (hsig : SignalizerAutAt p i) {K : Subgroup X} [K.Normal]
    (e : Nonempty (K ≃* i.Group)) (hDp : IsPGroup p (centralizer (K : Set X)))
    (hDc : IsCyclic (centralizer (K : Set X))) {E F : Subgroup X} (hE : IsElemAbelian p E)
    (hE3 : p ^ 3 ≤ Nat.card E)
    (hEin : GL83OuterType24 p i ∨ ∀ a ∈ E, a ∈ K ⊔ centralizer (K : Set X))
    (hF : p.Coprime (Nat.card F)) (hEF : E ≤ normalizer (F : Set X)) :
    ∀ a ∈ E, ∀ f ∈ F, a * f = f * a := by
  have hp : p.Prime := Fact.out
  set D : Subgroup X := centralizer (K : Set X) with hD
  set φ : X →* MulAut K := MulAut.conjNormal with hφ
  have hker : ∀ g, g ∈ φ.ker ↔ g ∈ D := fun g => mem_ker_conjNormal
  have hBel : IsElemAbelian p (E.map φ) := CFSG.Open.IsElemAbelian.map hE φ
  have hBcard : p ^ 2 ≤ Nat.card (E.map φ) := by
    have h := card_le_mul_card_map_conjNormal hp hDc hE
    by_contra hlt
    push Not at hlt
    have : Nat.card E < p ^ 3 := by
      calc Nat.card E ≤ p * Nat.card (E.map φ) := h
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
        _ = p ^ 3 := by ring
    omega
  intro a ha f hf
  have haB : φ a ∈ E.map φ := ⟨a, ha, rfl⟩
  obtain ⟨B₀, hB₀B, hB₀el, hB₀card, haB₀⟩ := exists_plane_of_mem hp hBel hBcard haB
  set Y : Subgroup (MulAut K) := F.map φ with hY
  have hYcop : p.Coprime (Nat.card Y) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd F φ) hF
  have hB₀N : B₀ ≤ normalizer (Y : Set (MulAut K)) := by
    intro b hb
    obtain ⟨a', ha', rfl⟩ := hB₀B hb
    exact Subgroup.le_normalizer_map φ ⟨a', hEF ha', rfl⟩
  have hinner : B₀ ≤ (MulAut.conj : K →* MulAut K).range ∨ GL83OuterType24 p i := by
    rcases hEin with hout | hin
    · exact Or.inr hout
    · refine Or.inl fun b hb => ?_
      obtain ⟨a', ha', rfl⟩ := hB₀B hb
      obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp (hin a' ha')
      refine ⟨⟨k, hk⟩, ?_⟩
      have hφc : φ c = 1 := MonoidHom.mem_ker.mp ((hker c).mpr hc)
      change MulAut.conj (⟨k, hk⟩ : K) = φ a'
      rw [← hkc, map_mul, hφc, mul_one, ← MulAut.conjNormal_val]
  have hcent : B₀ ≤ centralizer (Y : Set (MulAut K)) :=
    hsig K e B₀ Y hB₀el hB₀card hYcop hB₀N hinner
  have hcomm : φ a * φ f = φ f * φ a :=
    (mem_centralizer_iff.mp (hcent haB₀) (φ f) ⟨f, hf, rfl⟩).symm
  have hfa : a * f * a⁻¹ ∈ F := ((mem_normalizer_iff.mp (hEF ha)) f).mp hf
  have hcom : a * f * a⁻¹ * f⁻¹ ∈ F ⊓ D := by
    refine ⟨F.mul_mem hfa (F.inv_mem hf), (hker _).mp ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc φ a * φ f * (φ a)⁻¹ * (φ f)⁻¹ = φ f * φ a * (φ a)⁻¹ * (φ f)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  obtain ⟨n, hn⟩ := hDp.exists_card_eq
  have hbot : F ⊓ D = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [hn]; exact (Nat.Coprime.symm hF).pow_right n))
  rw [hbot, mem_bot] at hcom
  have := mul_inv_eq_one.mp hcom
  exact (mul_inv_eq_iff_eq_mul.mp this)

section Point

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

@[expose] noncomputable def redQ (p : ℕ) (P : Sylow p G) (x : G) : Subgroup (RedCent p x) :=
  (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))

structure Lemma32At (p : ℕ) (P : Sylow p G) (x : G) : Prop where
  central : ∃ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G),
    (∀ q ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), q * y = y * q) ∧ orderOf y = p ∧
      y ∉ zpowers x
  commutator : ∀ {E F : Subgroup G}, E ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
    IsElemAbelian p E → p ^ 3 ≤ Nat.card E → F ≤ centralizer ({x} : Set G) →
    p.Coprime (Nat.card F) → E ≤ normalizer (F : Set G) →
    ⁅F, E⁆ ≤ GLBPrimeCore p (centralizer ({x} : Set G))

namespace IsPPoint

theorem exists_central_of_not_mem_zpowers_of_facts [Fact p.Prime] (hp2 : p ≠ 2)
    (hloc : D1Local p P M) (h : IsPPoint p P M x) {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex} (hfacts : PPointFacts p M x R K i)
    (hReq : (R : Subgroup (RedCent p x)) = redQ p P x) :
    ∃ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G),
      (∀ q ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), q * y = y * q) ∧ orderOf y = p ∧
        y ∉ zpowers x := by
  have hp : p.Prime := Fact.out
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  obtain ⟨y, hyRK, hyp, hyc, hynz⟩ :=
    hfacts.red.exists_central_pair hp2 hfacts.center_eq_bot hzc hzp
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  have hReq' : (R : Subgroup (RedCent p x)) = (Q.subgroupOf C).map (QuotientGroup.mk' O) := hReq
  have hQp : IsPGroup p Q := P.isPGroup'.to_inf_left
  have hQ' : IsPGroup p (Q.subgroupOf C) := hQp.comap_subtype
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hyR : y ∈ (Q.subgroupOf C).map (QuotientGroup.mk' O) := hReq' ▸ hyRK.1
  obtain ⟨c, hcQ, hcy⟩ := hyR
  refine ⟨(c : G), hcQ, fun q hq => ?_, ?_, fun hmem => ?_⟩
  · have hqQ : (⟨q, hq.2⟩ : C) ∈ Q.subgroupOf C := hq
    have hcomm : QuotientGroup.mk' O ⟨q, hq.2⟩ * QuotientGroup.mk' O c =
        QuotientGroup.mk' O c * QuotientGroup.mk' O ⟨q, hq.2⟩ := by
      rw [hcy]
      exact hyc _ (hReq' ▸ ⟨_, hqQ, rfl⟩)
    exact congrArg Subtype.val (commute_of_mk_commute hp O hOc hQ' hqQ hcQ hcomm)
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_of_orderOf_mk_eq hp O hOc hQ' hcQ (by rw [hcy]; exact hyp)
  · obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    have hcj : c = (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : C) ^ j :=
      Subtype.ext (by rw [← hj]; simp)
    apply hynz
    rw [← hcy, hcj, map_zpow]
    exact zpow_mem_zpowers _ j

end IsPPoint

theorem commutator_le_primeCore_of_facts [Fact p.Prime] {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex} (hsig : SignalizerAutAt p i)
    (hfacts : PPointFacts p M x R K i) (hReq : (R : Subgroup (RedCent p x)) = redQ p P x)
    {E F : Subgroup G} (hEQ : E ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) (hFC' : F ≤ centralizer ({x} : Set G))
    (hF : p.Coprime (Nat.card F)) (hEF : E ≤ normalizer (F : Set G)) :
    ⁅F, E⁆ ≤ GLBPrimeCore p (centralizer ({x} : Set G)) := by
  have hp : p.Prime := Fact.out
  haveI := hfacts.red.normal
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set ρ := QuotientGroup.mk' O with hρ
  have hReq' : (R : Subgroup (RedCent p x)) = (((P : Subgroup G) ⊓ C).subgroupOf C).map ρ := hReq
  have hOc : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hEC : E ≤ C := hEQ.trans inf_le_right
  have hEp : IsPGroup p E := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE
  obtain ⟨φ, -⟩ := exists_mulEquiv_map_mk O hp hOc hEp hEC
  have hEbcard : Nat.card ((E.subgroupOf C).map ρ) = Nat.card E := (Nat.card_congr φ.toEquiv).symm
  have hEbR : (E.subgroupOf C).map ρ ≤ (R : Subgroup (RedCent p x)) := by
    rw [hReq']
    exact Subgroup.map_mono fun a ha => hEQ ha
  have hFb : p.Coprime (Nat.card ((F.subgroupOf C).map ρ)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (F.subgroupOf C) ρ) ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC').toEquiv]
  have hEbFb : (E.subgroupOf C).map ρ ≤
      normalizer (((F.subgroupOf C).map ρ : Subgroup _) : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.le_normalizer_map ρ ⟨a, mem_normalizer_iff.mpr fun g => ?_, rfl⟩
    exact (mem_normalizer_iff.mp (hEF ha)) (g : G)
  have hEb3 : p ^ 3 ≤ Nat.card ((E.subgroupOf C).map ρ) := by rw [hEbcard]; exact hE3
  have hEbel : IsElemAbelian p ((E.subgroupOf C).map ρ) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hE C) ρ
  have key := commute_of_coprime_of_card_at hsig hfacts.equiv hfacts.isPGroup hfacts.isCyclic
    hEbel hEb3 (hfacts.inner.imp_right fun h' a ha => h' a (hEbR ha) (hEbel.2 a ha)) hFb hEbFb
  refine Subgroup.commutator_le.mpr fun f hf a ha => ?_
  have hfC : f ∈ C := hFC' hf
  have haC : a ∈ C := hEC ha
  have hcomm := key (ρ ⟨a, haC⟩) ⟨⟨a, haC⟩, ha, rfl⟩ (ρ ⟨f, hfC⟩) ⟨⟨f, hfC⟩, hf, rfl⟩
  have hker : (⟨f, hfC⟩ * ⟨a, haC⟩ * (⟨f, hfC⟩ : C)⁻¹ * (⟨a, haC⟩ : C)⁻¹ : C) ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    change ρ _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc ρ ⟨f, hfC⟩ * ρ ⟨a, haC⟩ * (ρ ⟨f, hfC⟩)⁻¹ * (ρ ⟨a, haC⟩)⁻¹
        = ρ ⟨a, haC⟩ * ρ ⟨f, hfC⟩ * (ρ ⟨f, hfC⟩)⁻¹ * (ρ ⟨a, haC⟩)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hmem : (⟨f, hfC⟩ * ⟨a, haC⟩ * (⟨f, hfC⟩ : C)⁻¹ * (⟨a, haC⟩ : C)⁻¹ : C) ∈
      (GLBPrimeCore p C).subgroupOf C := by
    rw [glbPrimeCore_subgroupOf]
    exact hker
  exact hmem

theorem lemma32At_of_facts [Fact p.Prime] (hp2 : p ≠ 2) (hloc : D1Local p P M)
    (h : IsPPoint p P M x) {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    {i : TauCeti.CFSGIndex} (hsig : SignalizerAutAt p i) (hfacts : PPointFacts p M x R K i)
    (hReq : (R : Subgroup (RedCent p x)) = redQ p P x) : Lemma32At p P x :=
  ⟨h.exists_central_of_not_mem_zpowers_of_facts hp2 hloc hfacts hReq,
    fun hEQ hE hE3 hFC' hF hEF =>
      commutator_le_primeCore_of_facts hsig hfacts hReq hEQ hE hE3 hFC' hF hEF⟩

namespace IsPPoint

theorem false_of_bad_conj_line_of_lemma32At [Fact p.Prime] (hp2 : p ≠ 2) (hS : D1Global G)
    (hD1 : D1For G) (hloc : D1Local p P M) (h : IsPPoint p P M x) (h32 : Lemma32At p P x)
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
  obtain ⟨y, hyQ, hyc, hyp, hyx⟩ := h32.central
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
  have hcomm := h32.commutator hkE hEsel hEs3 hTsC hTscop hTsEs
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

theorem not_exists_conj_lines_of_lemma32At [Fact p.Prime] (hp2 : p ≠ 2) (hS : D1Global G)
    (hD1 : D1For G) (hloc : D1Local p P M) (h : IsPPoint p P M x) (h32 : Lemma32At p P x)
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
    exact h.false_of_bad_conj_line_of_lemma32At hp2 hS hD1 hloc h32 hDQ hD hLD hbad hg
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

end Point

end CFSG.LocalAnalysis.RankFourTheoremC
