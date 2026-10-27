module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThreeZ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmQuot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup

namespace P64Asm

variable {A : Type} [Group A] [Finite A] {p : ℕ}

abbrev XBar (p : ℕ) (X : Subgroup A) : Type := ↥X ⧸ primeComplementCore (G := ↥X) p

abbrev XBar.mk (p : ℕ) (X : Subgroup A) : ↥X →* XBar p X :=
  QuotientGroup.mk' (primeComplementCore (G := ↥X) p)

theorem XBar.coprime (p : ℕ) (X : Subgroup A) :
    Nat.Coprime p (Nat.card (primeComplementCore (G := ↥X) p)) :=
  primeComplementCore_coprime p

theorem XBar.not_top_le {X Y : Subgroup A} (hOY : rankThreePrimeCore p X ≤ Y) (hXY : ¬ X ≤ Y) :
    ¬ ⊤ ≤ (Y.subgroupOf X).map (XBar.mk p X) := by
  intro h
  apply hXY
  intro g hg
  obtain ⟨y', hy', hyπ⟩ := h (mem_top (XBar.mk p X ⟨g, hg⟩))
  have hker : y'⁻¹ * ⟨g, hg⟩ ∈ primeComplementCore (G := ↥X) p := by
    rw [← QuotientGroup.eq_one_iff]
    change XBar.mk p X (y'⁻¹ * ⟨g, hg⟩) = 1
    rw [map_mul, map_inv, hyπ, inv_mul_cancel]
  have hO' : (((y'⁻¹ * ⟨g, hg⟩ : ↥X)) : A) ∈ rankThreePrimeCore p X := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
    exact ⟨_, hker, rfl⟩
  have e : g = ((y' : ↥X) : A) * (((y'⁻¹ * ⟨g, hg⟩ : ↥X)) : A) := by simp
  rw [e]
  exact Y.mul_mem hy' (hOY hO')

theorem XBar.exists_sylow {X Q : Subgroup A} (hQp : IsPGroup p (Q.subgroupOf X))
    (hQs : ¬ p ∣ (Q.subgroupOf X).index) [Fact p.Prime] :
    ∃ Qb : Sylow p (XBar p X), (Qb : Subgroup (XBar p X)) =
      (Q.subgroupOf X).map (XBar.mk p X) := by
  refine ⟨(hQp.toSylow hQs).mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  simp [Sylow.coe_mapSurjective]

theorem XBar.rank_three (hp : p.Prime) {X Q : Subgroup A} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    (h3 : 3 ≤ Open.pRank p Q) :
    3 ≤ Open.pRank p ((Q.subgroupOf X).map (XBar.mk p X)) := by
  obtain ⟨E, hEQ, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp h3
  have hEX : E ≤ X := hEQ.trans hQX
  have hE'Q' : E.subgroupOf X ≤ Q.subgroupOf X := fun e he => hEQ he
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  have hE'p : IsPGroup p (E.subgroupOf X) := hQ'p.to_le hE'Q'
  have hE'el : IsElemAbelian p (E.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hE X
  have hE'c : Nat.card (E.subgroupOf X) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hEc]
  exact SU1.le_pRank hp.one_lt (Subgroup.map_mono hE'Q')
    (CFSG.Open.IsElemAbelian.map hE'el (XBar.mk p X)) (k := 3)
    (by rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp _ (XBar.coprime p X) hE'p, hE'c])

theorem XBar.gamma2 (hp : p.Prime) {X Y Q : Subgroup A} (hQp : IsPGroup p (Q.subgroupOf X))
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)
    {Sb : Subgroup (XBar p X)} (hSb : Sb ≤ (Q.subgroupOf X).map (XBar.mk p X))
    (hk : 2 ≤ Open.pRank p Sb) :
    normalizer (Sb : Set (XBar p X)) ≤ (Y.subgroupOf X).map (XBar.mk p X) := by
  refine normalizer_le_map_of_gamma hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hQp
    (k := 2) ?_ hSb hk
  intro S hSQ hS2
  refine normalizer_subgroupOf_le S (hΓ2 _ ?_ ?_)
  · rintro _ ⟨s, hs, rfl⟩
    exact hSQ hs
  · rw [pRank_map_subtype hp.one_lt]
    exact hS2

theorem XBar.gamma1 (hp : p.Prime) {X Y Q : Subgroup A} (hQp : IsPGroup p (Q.subgroupOf X))
    (hΓ1 : ∀ E : Subgroup A, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup A, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)
    {Eb : Subgroup (XBar p X)} (hEb : Eb ≤ (Q.subgroupOf X).map (XBar.mk p X))
    (hEbel : IsElemAbelian p Eb) (hEbc : Nat.card Eb = p ^ 3) {Sb : Subgroup (XBar p X)}
    (hSb : Sb ≤ Eb) (hk : 1 ≤ Open.pRank p Sb) :
    normalizer (Sb : Set (XBar p X)) ≤ (Y.subgroupOf X).map (XBar.mk p X) := by
  have hinj := injOn_mk_of_isPGroup hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hQp
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup ↥X, E = Eb.comap (XBar.mk p X) ⊓ Q.subgroupOf X := ⟨_, rfl⟩
  have hEQ' : E ≤ Q.subgroupOf X := by
    rw [hEdef]
    exact inf_le_right
  have hEmap : E.map (XBar.mk p X) = Eb := by
    rw [hEdef]
    exact CFSG.AGLEmbedding.map_comap_inf_eq _ hEb
  have hEp : IsPGroup p E := hQp.to_le hEQ'
  have hEel : IsElemAbelian p E :=
    isElemAbelian_of_injOn hinj hEQ' (by rw [hEmap]; exact hEbel)
  have hEc : Nat.card E = p ^ 3 := by
    rw [← CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp _ (XBar.coprime p X) hEp, hEmap, hEbc]
  have hEA : E.map X.subtype ≤ Q := by
    rintro _ ⟨e, he, rfl⟩
    exact hEQ' he
  have hEAel : IsElemAbelian p (E.map X.subtype) := CFSG.Open.IsElemAbelian.map hEel _
  have hEAc : Nat.card (E.map X.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hEc]
  refine normalizer_le_map_of_gamma hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hEp
    (k := 1) ?_ (hEmap ▸ hSb) hk
  intro S hSE hS1
  refine normalizer_subgroupOf_le S (hΓ1 _ hEA hEAel hEAc _ (Subgroup.map_mono hSE) ?_)
  rw [pRank_map_subtype hp.one_lt]
  exact hS1

theorem XBar.plane (hp : p.Prime) {X Q B : Subgroup A} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    (hBQ : B ≤ Q) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2) :
    (B.subgroupOf X).map (XBar.mk p X) ≤ (Q.subgroupOf X).map (XBar.mk p X) ∧
      IsElemAbelian p ((B.subgroupOf X).map (XBar.mk p X)) ∧
        Nat.card ((B.subgroupOf X).map (XBar.mk p X)) = p ^ 2 := by
  have hBX : B ≤ X := hBQ.trans hQX
  have hB'Q' : B.subgroupOf X ≤ Q.subgroupOf X := fun b hb => hBQ hb
  have hB'p : IsPGroup p (B.subgroupOf X) := hQp.comap_subtype.to_le hB'Q'
  refine ⟨Subgroup.map_mono hB'Q', CFSG.Open.IsElemAbelian.map
    (CFSG.Open.IsElemAbelian.subgroupOf hBel X) _, ?_⟩
  rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp _ (XBar.coprime p X) hB'p,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv, hBcard]

theorem XBar.element (hp : p.Prime) {X Q B : Subgroup A} (hQp : IsPGroup p Q) (hQX : Q ≤ X)
    (hBQ : B ≤ Q) {x : A} (hxB : x ∈ B) (hx1 : x ≠ 1) :
    XBar.mk p X ⟨x, (hBQ.trans hQX) hxB⟩ ∈ (B.subgroupOf X).map (XBar.mk p X) ∧
      XBar.mk p X ⟨x, (hBQ.trans hQX) hxB⟩ ≠ 1 := by
  have hB'Q' : B.subgroupOf X ≤ Q.subgroupOf X := fun b hb => hBQ hb
  have hinj := injOn_mk_of_isPGroup hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X)
    hQp.comap_subtype
  refine ⟨Subgroup.mem_map_of_mem _ hxB, fun h => hx1 ?_⟩
  have h1 : (⟨x, (hBQ.trans hQX) hxB⟩ : ↥X) = 1 :=
    hinj (hB'Q' hxB) (one_mem _) (by rw [map_one]; exact h)
  exact congrArg Subtype.val h1

theorem XBar.sc (hp : p.Prime) {X B : Subgroup A} (hBX : B ≤ X) (hBel : IsElemAbelian p B)
    (hsc : ∀ y ∈ centralizer (B : Set A), y ^ p = 1 → y ∈ B) :
    ∀ y ∈ centralizer (((B.subgroupOf X).map (XBar.mk p X) : Subgroup (XBar p X)) :
        Set (XBar p X)), y ^ p = 1 → y ∈ (B.subgroupOf X).map (XBar.mk p X) := by
  refine mem_map_of_mem_centralizer hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X)
    (CFSG.Open.IsElemAbelian.subgroupOf hBel X) ?_
  intro y hy hyp
  have hyc : (y : A) ∈ centralizer (B : Set A) := by
    rw [mem_centralizer_iff]
    intro b hb
    have := (mem_centralizer_iff.mp hy) ⟨b, hBX hb⟩ hb
    exact congrArg Subtype.val this
  have hyp' : (y : A) ^ p = 1 := by
    have := congrArg Subtype.val hyp
    simpa using this
  exact hsc _ hyc hyp'

theorem XBar.rank_centralizer (hp : p.Prime) {X : Subgroup A} {x : A} (hxX : x ∈ X)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hcx : Open.pRank p (centralizer ({x} : Set A) ⊓ X) ≤ 2) :
    Open.pRank p (centralizer ({XBar.mk p X ⟨x, hxX⟩} : Set (XBar p X))) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπsurj : Function.Surjective (XBar.mk p X) := QuotientGroup.mk'_surjective _
  have hx'p : (⟨x, hxX⟩ : ↥X) ^ p = 1 := by
    apply Subtype.ext
    simpa using hxp
  have hx'1 : (⟨x, hxX⟩ : ↥X) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hzp : IsPGroup p (zpowers (⟨x, hxX⟩ : ↥X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx'p hx'1, pow_one])
  have hsub : centralizer ({XBar.mk p X ⟨x, hxX⟩} : Set (XBar p X)) ≤
      (centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X)).map (XBar.mk p X) := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := hπsurj g
    have hg0 : g₀ ∈ (centralizer ((((zpowers (⟨x, hxX⟩ : ↥X)).map (XBar.mk p X)) :
        Subgroup (XBar p X)) : Set (XBar p X))).comap (XBar.mk p X) := by
      rw [Subgroup.mem_comap, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
      exact hg
    have hmem := CFSG.AGLEmbedding.comap_centralizer_map_le_sup hp
      (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hzp hg0
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hmem
    obtain ⟨o, ho, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨c, hc, ?_⟩
    have h1 : XBar.mk p X o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    change XBar.mk p X c = XBar.mk p X (o * c)
    rw [map_mul, h1, one_mul]
  have hcent : centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X) =
      (centralizer ({x} : Set A)).subgroupOf X := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hker : ¬ p ∣ Nat.card (XBar.mk p X).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (XBar.coprime p X)
  calc Open.pRank p (centralizer ({XBar.mk p X ⟨x, hxX⟩} : Set (XBar p X)))
      ≤ Open.pRank p ((centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X)).map (XBar.mk p X)) :=
        SU1.pRank_mono hp.one_lt hsub
    _ ≤ Open.pRank p (centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X)) :=
        CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp _ hker _
    _ = Open.pRank p (X ⊓ centralizer ({x} : Set A)) := by
        rw [hcent, pRank_subgroupOf_inf hp.one_lt]
    _ ≤ 2 := by
        rw [inf_comm]
        exact hcx

theorem XBar.lift_normal {X : Subgroup A} {Nb : Subgroup (XBar p X)} (hNbn : Nb.Normal)
    (hNbi : Nb.index = p) :
    ∃ N : Subgroup A, N ≤ X ∧ (N.subgroupOf X).Normal ∧ (N.subgroupOf X).index = p := by
  have hπsurj : Function.Surjective (XBar.mk p X) := QuotientGroup.mk'_surjective _
  have hN' : ((Nb.comap (XBar.mk p X)).map X.subtype).subgroupOf X = Nb.comap (XBar.mk p X) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  refine ⟨(Nb.comap (XBar.mk p X)).map X.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [hN']
    exact hNbn.comap _
  · rw [hN', Subgroup.index_comap_of_surjective _ hπsurj]
    exact hNbi

theorem XBar.lift_W {X B W : Subgroup A} (hBX : B ≤ X) (hWX : W ≤ X)
    (hBW : B ≤ normalizer (W : Set A)) (hcop : Nat.Coprime (Nat.card W) (2 * p))
    (hWb : ∀ W' : Subgroup (XBar p X),
      (B.subgroupOf X).map (XBar.mk p X) ≤ normalizer (W' : Set (XBar p X)) →
        Nat.Coprime (Nat.card W') (2 * p) → W' = ⊥) :
    W ≤ rankThreePrimeCore p X := by
  have hB'W' : B.subgroupOf X ≤ normalizer ((W.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro w
    exact (mem_normalizer_iff.mp (hBW hb)) (w : A)
  have hBW' : (B.subgroupOf X).map (XBar.mk p X) ≤
      normalizer (((W.subgroupOf X).map (XBar.mk p X) : Subgroup (XBar p X)) :
        Set (XBar p X)) :=
    (Subgroup.map_mono hB'W').trans (Subgroup.le_normalizer_map _)
  have hcopb : Nat.Coprime (Nat.card ((W.subgroupOf X).map (XBar.mk p X))) (2 * p) := by
    have hdvd : Nat.card ((W.subgroupOf X).map (XBar.mk p X)) ∣ Nat.card (W.subgroupOf X) :=
      Subgroup.card_map_dvd _ _
    have hW'c : Nat.card (W.subgroupOf X) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv
    rw [hW'c] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd hcop
  have h0 := hWb _ hBW' hcopb
  intro w hw
  have hwX : w ∈ X := hWX hw
  have hmem : XBar.mk p X ⟨w, hwX⟩ ∈ (W.subgroupOf X).map (XBar.mk p X) :=
    Subgroup.mem_map_of_mem _ (show (⟨w, hwX⟩ : ↥X) ∈ W.subgroupOf X from hw)
  rw [h0, Subgroup.mem_bot] at hmem
  have hwO : (⟨w, hwX⟩ : ↥X) ∈ primeComplementCore (G := ↥X) p :=
    (QuotientGroup.eq_one_iff _).mp hmem
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
  exact ⟨_, hwO, rfl⟩

theorem XBar.lift_Q0 (hp : p.Prime) {X Q : Subgroup A} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    {Q₀b : Subgroup (XBar p X)} (hQ₀bQ : Q₀b ≤ (Q.subgroupOf X).map (XBar.mk p X))
    (hel : IsElemAbelian p Q₀b) (hc : Nat.card Q₀b = p ^ p)
    (hT : ∀ a ∈ Q₀b, a ≠ 1 → ∀ b ∈ Q₀b, b ≠ 1 →
      ∃ g ∈ normalizer (Q₀b : Set (XBar p X)), g * a * g⁻¹ ∈ zpowers b) :
    ∃ Q₀ : Subgroup A, Q₀ ≤ Q ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
      ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
        ∃ g ∈ X ⊓ normalizer (Q₀ : Set A), g * a * g⁻¹ ∈ zpowers b := by
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  have hinj := injOn_mk_of_isPGroup hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hQ'p
  obtain ⟨Q₀', hQ₀'def⟩ : ∃ Q₀' : Subgroup ↥X,
      Q₀' = Q₀b.comap (XBar.mk p X) ⊓ Q.subgroupOf X := ⟨_, rfl⟩
  have hQ₀'Q' : Q₀' ≤ Q.subgroupOf X := by
    rw [hQ₀'def]
    exact inf_le_right
  have hQ₀map : Q₀'.map (XBar.mk p X) = Q₀b := by
    rw [hQ₀'def]
    exact CFSG.AGLEmbedding.map_comap_inf_eq _ hQ₀bQ
  have hQ₀'p : IsPGroup p Q₀' := hQ'p.to_le hQ₀'Q'
  have hQ₀'el : IsElemAbelian p Q₀' :=
    isElemAbelian_of_injOn hinj hQ₀'Q' (by rw [hQ₀map]; exact hel)
  have hQ₀'c : Nat.card Q₀' = p ^ p := by
    rw [← CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp _ (XBar.coprime p X) hQ₀'p, hQ₀map, hc]
  have hsubof : (Q₀'.map X.subtype).subgroupOf X = Q₀' :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  refine ⟨Q₀'.map X.subtype, ?_, CFSG.Open.IsElemAbelian.map hQ₀'el _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact hQ₀'Q' he
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hQ₀'c]
  · refine P64Free.exists_normalizer_conj_mem_zpowers_of_quotient hp
      (Subgroup.map_subtype_le _) (hQ₀'p.map _) ?_
    intro a b ha ha1 hb hb1
    have haQ : a ∈ Q₀' := by
      rw [← hsubof]
      exact ha
    have hbQ : b ∈ Q₀' := by
      rw [← hsubof]
      exact hb
    rw [hsubof, hQ₀map]
    refine hT (XBar.mk p X a) ?_ ?_ (XBar.mk p X b) ?_ ?_
    · rw [← hQ₀map]
      exact Subgroup.mem_map_of_mem _ haQ
    · intro h
      exact ha1 (hinj (hQ₀'Q' haQ) (one_mem _) (by rw [map_one]; exact h))
    · rw [← hQ₀map]
      exact Subgroup.mem_map_of_mem _ hbQ
    · intro h
      exact hb1 (hinj (hQ₀'Q' hbQ) (one_mem _) (by rw [map_one]; exact h))

end P64Asm

theorem kFactP65RankThree_of_kdata (hI291 : KDL64I291) (hI246 : KDL64I246)
    (hRank : KDL64TypeRank) (hI204 : KDL64I204L2) : KFactP65RankThree := by
  intro A _ _ p X Y Q B x hp hp5 hX hYX hXY hQX hQp hQs h3 hQY hBQ hBel hBcard hxB hx1 hsc hcx hΓ2
    hΓ1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBX : B ≤ X := hBQ.trans hQX
  have hxX : x ∈ X := hBX hxB
  have hOY : rankThreePrimeCore p X ≤ Y :=
    P64Free.rankThreePrimeCore_le_of_gammaOne_cube hp hQX h3 hΓ1
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  obtain ⟨Qb, hQb⟩ := P64Asm.XBar.exists_sylow hQ'p hQs
  have hpl := P64Asm.XBar.plane hp hQX hQp hBQ hBel hBcard
  have hel := P64Asm.XBar.element hp hQp hQX hBQ hxB hx1
  have hxp : x ^ p = 1 := hBel.2 x hxB
  obtain ⟨⟨Nb, hNbn, hNbi⟩, hWb, Q₀b, hQ₀bQ, hQ₀bel, hQ₀bc, hQ₀bT⟩ :=
    P64Asm.three_Z hI291 hI246 hRank hI204 hp hp5 (hX.quotient _)
      (primeComplementCore_quotient_eq_bot p) Qb ((Y.subgroupOf X).map (P64Asm.XBar.mk p X))
      ((B.subgroupOf X).map (P64Asm.XBar.mk p X)) (P64Asm.XBar.mk p X ⟨x, hxX⟩)
      (P64Asm.XBar.not_top_le hOY hXY)
      (by rw [hQb]; exact Subgroup.map_mono (fun q hq => hQY hq))
      (by rw [hQb]; exact P64Asm.XBar.rank_three hp hQX hQp h3)
      (fun S hS hk => P64Asm.XBar.gamma2 hp hQ'p hΓ2 (by rw [← hQb]; exact hS) hk)
      (fun Eb hEb hEbel hEbc S hS hk =>
        P64Asm.XBar.gamma1 hp hQ'p hΓ1 (by rw [← hQb]; exact hEb) hEbel hEbc hS hk)
      (by rw [hQb]; exact hpl.1) hpl.2.1 hpl.2.2 hel.1 hel.2
      (P64Asm.XBar.sc hp hBX hBel hsc) (P64Asm.XBar.rank_centralizer hp hxX hxp hx1 hcx)
  refine ⟨P64Asm.XBar.lift_normal hNbn hNbi, ?_,
    P64Asm.XBar.lift_Q0 hp hQX hQp (by rw [← hQb]; exact hQ₀bQ) hQ₀bel hQ₀bc hQ₀bT⟩
  intro W hWX hBW hcop
  exact P64Asm.XBar.lift_W hBX hWX hBW hcop hWb

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
