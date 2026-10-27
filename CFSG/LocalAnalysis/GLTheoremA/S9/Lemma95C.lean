module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95B

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l95c_coprime_two_group {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup G}
    (h2 : IsPGroup 2 S) : Nat.Coprime p (Nat.card S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

private theorem l95c_coprime_q_group {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) {S : Subgroup G}
    (hS : IsPGroup q S) : Nat.Coprime p (Nat.card S) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).2 hqp.symm)

private theorem l95c_le_glaPPrimeCoreOf {p : ℕ} {X N : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p X := by
  have hNn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact hcop
  have hle : N.subgroupOf X ≤ GLAPPrimeCore p ↥X := by
    have hmem : N.subgroupOf X ∈ {K : Subgroup ↥X | K.Normal ∧ Nat.Coprime p (Nat.card K)} :=
      ⟨hNn, hcop'⟩
    exact le_sSup hmem
  intro s hs
  exact Subgroup.mem_map.2 ⟨⟨s, hNX hs⟩, hle (Subgroup.mem_subgroupOf.2 hs), rfl⟩

theorem glaPComponent_centralizer {p : ℕ} (hp : p.Prime) {x : G} {L E J : Subgroup G}
    (hL : GLAPComponent p (cx x) L) (hxE : x ∈ E)
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J) :
    GLAPComponent p (Subgroup.centralizer (E : Set G)) J := by
  have hCE : Subgroup.centralizer (E : Set G) ≤ cx x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxE)
  have hsub := isSubnormal_inf hL.2.1 (Subgroup.centralizer (E : Set G))
  rw [inf_eq_right.2 hCE] at hsub
  exact glaPComponent_of_isSubnormal' hp hsub hJ

theorem pCoreOf_inf_centralizer_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (Y : Subgroup G) (a : G) :
    pCoreOf q Y ⊓ Subgroup.centralizer ({a} : Set G) ≤
      GLAPPrimeCoreOf p (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hNX : pCoreOf q Y ⊓ Subgroup.centralizer ({a} : Set G) ≤ Y ⊓ Subgroup.centralizer ({a} : Set G) :=
    inf_le_inf_right _ (CFSG.LieType.BorelTits.pCoreOf_le q Y)
  have hXN : Y ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((pCoreOf q Y ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf q Y (Subgroup.mem_inf.1 hg).1, Subgroup.le_normalizer (Subgroup.mem_inf.1 hg).2⟩
  have hNq : IsPGroup q (pCoreOf q Y ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup q Y).to_le inf_le_left
  exact l95c_le_glaPPrimeCoreOf hNX hXN (l95c_coprime_q_group hp hq hqp hNq)

theorem covers_of_normalizer_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {M C Q₂ : Subgroup G} (hQ₂C : Q₂ ≤ GLAPPrimeCoreOf p C) (hQ₂ : IsPGroup q Q₂)
    (hM : ∀ Q₃ : Subgroup G, Q₂ ≤ Q₃ → IsPGroup q Q₃ → Q₃ ≤ GLAPPrimeCoreOf p C →
      Subgroup.normalizer (Q₃ : Set G) ≤ M) : Covers p M C := by
  haveI : Fact q.Prime := ⟨hq⟩
  show (M ⊓ C) ⊔ GLAPPrimeCoreOf p C = C
  obtain ⟨O, hO⟩ : ∃ O : Subgroup G, O = GLAPPrimeCoreOf p C := ⟨_, rfl⟩
  rw [← hO]
  have hOC : O ≤ C := by
    rw [hO]
    exact Subgroup.map_subtype_le _
  have hCN : C ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact le_normalizer_glaPPrimeCoreOf p C
  have hQ₂O : Q₂ ≤ O := by
    rw [hO]
    exact hQ₂C
  have hQ₂C' : Q₂ ≤ C := hQ₂O.trans hOC
  set N : Subgroup C := O.subgroupOf C with hN
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOC).2 hCN
  set Q₂N : Subgroup N := (Q₂.subgroupOf C).subgroupOf N with hQ₂Ndef
  have hQ₂N : IsPGroup q Q₂N := by
    intro x
    have hxQ : ((x.1 : C) : G) ∈ Q₂ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 x.2)
    obtain ⟨n, hn⟩ := hQ₂ ⟨((x.1 : C) : G), hxQ⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hn
    simpa using h
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hQ₂N
  set P' : Subgroup C := (P : Subgroup N).map N.subtype with hP'def
  have hFr : Subgroup.normalizer ((P' : Subgroup C) : Set C) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  set Q₃ : Subgroup G := P'.map C.subtype with hQ₃def
  have hQ₃O : Q₃ ≤ O := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hw
    exact Subgroup.mem_subgroupOf.1 v.2
  have hQ₃q : IsPGroup q Q₃ :=
    (P.isPGroup'.map N.subtype).map C.subtype
  have hQ₂Q₃ : Q₂ ≤ Q₃ := by
    intro x hx
    have hxC : x ∈ C := hQ₂C' hx
    have hxN : (⟨x, hxC⟩ : C) ∈ N := Subgroup.mem_subgroupOf.2 (hQ₂O hx)
    have hmemQ : (⟨⟨x, hxC⟩, hxN⟩ : N) ∈ Q₂N := Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hx)
    have hmemP : (⟨⟨x, hxC⟩, hxN⟩ : N) ∈ (P : Subgroup N) := hP hmemQ
    exact Subgroup.mem_map.2 ⟨N.subtype ⟨⟨x, hxC⟩, hxN⟩,
      Subgroup.mem_map.2 ⟨⟨⟨x, hxC⟩, hxN⟩, hmemP, rfl⟩, rfl⟩
  have hd : ∀ y : C, y ∈ Subgroup.normalizer ((P' : Subgroup C) : Set C) →
      (y : G) ∈ Subgroup.normalizer ((Q₃ : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
      refine Subgroup.mem_map.2 ⟨y * w * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy w).1 hw, ?_⟩
      simp
    · intro hg
      obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hg
      refine Subgroup.mem_map.2 ⟨y⁻¹ * w * y⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) w).1 hw, ?_⟩
      have hval : (C.subtype (y⁻¹ * w * y⁻¹⁻¹) : G) = (y : G)⁻¹ * (C.subtype w) * (y : G) := by
        simp
      rw [hval, hwg]
      group
  apply le_antisymm
  · exact sup_le inf_le_right hOC
  · intro c hc
    have htopc : (⟨c, hc⟩ : C) ∈ Subgroup.normalizer ((P' : Subgroup C) : Set C) ⊔ N := by
      rw [hFr]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 htopc
    have hcG : c = (y : G) * (z : G) := by
      have h := congrArg Subtype.val hyz
      simpa using h.symm
    have hyM : (y : G) ∈ M := hM Q₃ hQ₂Q₃ hQ₃q (by rw [← hO]; exact hQ₃O) (hd y hy)
    have hyC : (y : G) ∈ C := y.2
    have hzO : (z : G) ∈ O := Subgroup.mem_subgroupOf.1 hz
    rw [hcG]
    exact Subgroup.mul_mem_sup ⟨hyM, hyC⟩ hzO

open scoped Pointwise in
theorem le_core_of_covers_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M C S : Subgroup G}
    (hcov : Covers p M C) (hS : S ≤ pCoreOf 2 M ⊓ C) : S ≤ GLAPPrimeCoreOf p C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov' : (M ⊓ C) ⊔ GLAPPrimeCoreOf p C = C := hcov
  obtain ⟨O, hO⟩ : ∃ O : Subgroup G, O = GLAPPrimeCoreOf p C := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = pCoreOf 2 M ⊓ C := ⟨_, rfl⟩
  rw [← hO] at hcov'
  have hOC : O ≤ C := by
    rw [hO]
    exact Subgroup.map_subtype_le _
  have hTC : T ≤ C := by
    rw [hT]
    exact inf_le_right
  have hCN : C ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact le_normalizer_glaPPrimeCoreOf p C
  have hTN : T ≤ Subgroup.normalizer (O : Set G) := hTC.trans hCN
  have hT2 : IsPGroup 2 T := by
    rw [hT]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = T ⊔ O := ⟨_, rfl⟩
  have hKset : (K : Set G) = (T : Set G) * (O : Set G) := by
    rw [hK]
    exact Subgroup.coe_mul_of_left_le_normalizer_right T O hTN
  have hKmem : ∀ x : G, x ∈ K ↔ ∃ t ∈ T, ∃ u ∈ O, t * u = x := by
    intro x
    have h := Set.ext_iff.1 hKset x
    rw [SetLike.mem_coe, Set.mem_mul] at h
    exact h
  have hTK : T ≤ K := by
    rw [hK]
    exact le_sup_left
  have hKC : K ≤ C := by
    rw [hK]
    exact sup_le hTC hOC
  have hOnorm : ∀ o ∈ O, ∀ k ∈ K, o * k * o⁻¹ ∈ K := by
    intro o ho k hk
    rw [hKmem] at hk ⊢
    obtain ⟨t, ht, u, hu, rfl⟩ := hk
    have hoC : o ∈ C := hOC ho
    have h1 : t⁻¹ * o * t ∈ O := by
      have h := (Subgroup.mem_normalizer_iff.1 (hCN (C.inv_mem (hTC ht))) o).1 ho
      rwa [inv_inv] at h
    have hu' : o * u * o⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hCN hoC) u).1 hu
    refine ⟨t, ht, (t⁻¹ * o * t) * o⁻¹ * (o * u * o⁻¹),
      O.mul_mem (O.mul_mem h1 (O.inv_mem ho)) hu', ?_⟩
    group
  have hMnorm : ∀ m ∈ M ⊓ C, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.1 hm
    rw [hKmem] at hk ⊢
    obtain ⟨t, ht, u, hu, rfl⟩ := hk
    have hTm : m * t * m⁻¹ ∈ T := by
      rw [hT] at ht ⊢
      obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.1 ht
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 M hmM) t).1 ht1
      · exact C.mul_mem (C.mul_mem hmC ht2) (C.inv_mem hmC)
    have huO : m * u * m⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hCN hmC) u).1 hu
    exact ⟨m * t * m⁻¹, hTm, m * u * m⁻¹, huO, by group⟩
  have hMN : M ⊓ C ≤ Subgroup.normalizer (K : Set G) := fun m hm => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hMnorm m hm k hk
    · intro hk
      have h := hMnorm m⁻¹ ((M ⊓ C).inv_mem hm) _ hk
      have e : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k := by group
      rwa [e] at h
  have hON : O ≤ Subgroup.normalizer (K : Set G) := fun o ho => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hOnorm o ho k hk
    · intro hk
      have h := hOnorm o⁻¹ (O.inv_mem ho) _ hk
      have e : o⁻¹ * (o * k * o⁻¹) * o⁻¹⁻¹ = k := by group
      rwa [e] at h
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hcov']
    exact sup_le hMN hON
  have hKnorm : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 hCK
  have hcard := card_sup_mul_card_inf_of_le_normalizer hTN
  have hKeq : K = O ⊔ T := by
    rw [hK, sup_comm]
  rw [← hKeq] at hcard
  have hOcop : Nat.Coprime p (Nat.card ↥O) := by
    rw [hO]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp C)
  have hTcop : Nat.Coprime p (Nat.card ↥T) := l95c_coprime_two_group hp hp2 hT2
  have hKcop : Nat.Coprime p (Nat.card ↥K) := by
    have hdvd : Nat.card ↥K ∣ Nat.card ↥O * Nat.card ↥T := ⟨Nat.card ↥(O ⊓ T), hcard.symm⟩
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hOcop hTcop)
  have hKc : Nat.Coprime p (Nat.card ↥(K.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
    exact hKcop
  have hle : K.subgroupOf C ≤ GLAPPrimeCore p ↥C := by
    have hmem : K.subgroupOf C ∈ {N : Subgroup ↥C | N.Normal ∧ Nat.Coprime p (Nat.card N)} :=
      ⟨hKnorm, hKc⟩
    exact le_sSup hmem
  have hST : S ≤ T := by
    rw [hT]
    exact hS
  intro s hs
  have hsK : s ∈ K := hTK (hST hs)
  have hsC : s ∈ C := hKC hsK
  exact Subgroup.mem_map.2 ⟨⟨s, hsC⟩, hle (Subgroup.mem_subgroupOf.2 hsK), rfl⟩

theorem exists_Gstar_component {p : ℕ} (hc : S9Ctx G p) (h183 : Input18_3_4) {B E J : Subgroup G} {a : G}
    (hB : IsElemAbelian p B) (hEB : E ≤ B) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    (haE : a ∈ E) (ha1 : a ≠ 1) (hJ : GLAPComponent p (Subgroup.centralizer (E : Set G)) J) :
    ∃ K₁ : Subgroup G, GLAPComponent p (cx a) K₁ ∧ J ≤ closureIn K₁ B ∧ IsGStar p B K₁ := by
  have hp : p.Prime := hc.ctx.prime
  have hKa : CFSG.Open.IsKGroup ↥(cx a) := S9.isKGroup_cx hc ha1
  have hCE : Subgroup.centralizer (E : Set G) ≤ cx a :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haE)
  have hJ' : GLAPComponent p (cx a ⊓ Subgroup.centralizer (E : Set G)) J := by
    rw [inf_eq_right.2 hCE]
    exact hJ
  obtain ⟨𝒞, h𝒞comp, h𝒞sup, -, h𝒞trans⟩ :=
    h183 G (cx a) hKa p hp E (isElemAbelian_le_centralizer hE haE) hE J hJ'
  have hJsup : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [h𝒞sup]
    refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq ?_)
    exact (gLBConj_one J).symm
  rcases Set.eq_empty_or_nonempty 𝒞 with hempty | ⟨K₁, hK₁⟩
  · exfalso
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := by
      rw [hempty]
      simp
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hJsup.trans hbot.le))
  · have hcl : ∀ L ∈ 𝒞, L ≤ closureIn K₁ B := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := h𝒞trans K₁ hK₁ L hL
      have hconj : GLBConj e K₁ = K₁.map (MulAut.conj e⁻¹).toMonoidHom := rfl
      rw [hconj]
      exact le_iSup₂_of_le (f := fun a (_ : a ∈ B) => K₁.map (MulAut.conj a).toMonoidHom) e⁻¹
        (B.inv_mem (hEB he)) le_rfl
    have hJcl : J ≤ closureIn K₁ B := hJsup.trans (iSup₂_le fun L hL => hcl L hL)
    refine ⟨K₁, h𝒞comp K₁ hK₁, hJcl, ?_⟩
    have hJH : GLAPComponent p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) J :=
      glaPComponent_of_le hp hJ (le_inf hJcl hJ.1) inf_le_right
    have hlayer : GLAPLayer p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
      intro h0
      apply glaPComponent_ne_bot' hJ
      have hJmem : J ∈ {L : Subgroup G |
          GLAPComponent p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) L} := hJH
      exact le_bot_iff.1 ((le_sSup hJmem).trans h0.le)
    unfold IsGStar
    exact ⟨E, hEB, hE, hEcard, hlayer⟩

theorem not_isPGroup_of_component {p r : ℕ} (hr : r.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : ¬ IsPGroup r J := by
  intro hrJ
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 (glaPComponent_ne_bot' hJ)
  haveI : Group.IsNilpotent ↥J := hrJ.isNilpotent
  have h1 : commutator ↥J = ⊤ := commutator_top_of_perfect (glaPComponent_perfect hJ)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J).ne h1

theorem eq_bot_of_two_group_odd {S : Subgroup G} (h2 : IsPGroup 2 S) (hodd : Odd (Nat.card S)) :
    S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at hodd
  have hn0 : n = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hn0] at hn
  exact Subgroup.eq_bot_of_card_eq S (by rw [hn]; rfl)

theorem coprime_card_of_two_group {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup G}
    (h2 : IsPGroup 2 S) : Nat.Coprime p (Nat.card S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem card_mul_of_index_eq {p : ℕ} {K E : Subgroup G} (hKE : K ≤ E)
    (hi : (K.subgroupOf E).index = p) : Nat.card K * p = Nat.card E := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf E)
  have h2 : Nat.card (K.subgroupOf E) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv
  rw [h2, hi] at h1
  exact h1

theorem Contra92.isPGroup_Q₁ {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}
    (hC : Contra92 p B x L q Q₁) : IsPGroup q Q₁ := fun g => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (hC.setup.exp g g.2)⟩

theorem Q₂_le_core_cx {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hc : S9Ctx G p) (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J)
    (hDE : D ≤ E) {a : G} (haD : a ∈ D) (ha1 : a ≠ 1) :
    (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (cx a) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have haE : a ∈ E := hDE haD
  have hKa : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_cx hc ha1
  have hxa : x ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hE.el hE.mem haE)
  have hJ' := glaPComponent_centralizer hp hC.h.comp hE.mem hE.comp
  have hEX : E ≤ cx a ⊓ cx x := le_inf (isElemAbelian_le_centralizer hE.el haE)
    (isElemAbelian_le_centralizer hE.el hE.mem)
  have hXK : CFSG.Open.IsKGroup ↥(cx a ⊓ cx x) := isKGroup_of_le_cx hc ha1 inf_le_left
  have hCE : Subgroup.centralizer (E : Set G) ≤ cx a ⊓ cx x :=
    le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haE))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hE.mem))
  have hJX : J ≤ GLAPLayer p (cx a ⊓ cx x) := by
    have h1 := hin.lbal (cx a ⊓ cx x) E hXK hEX (isPGroup_of_isElemAbelian hE.el)
    rw [inf_eq_right.2 hCE] at h1
    have h0 : J ≤ GLAPLayer p (Subgroup.centralizer (E : Set G)) := le_sSup hJ'
    exact h0.trans h1
  have hQ₂core : (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf p (cx a ⊓ cx x) := by
    intro g hg
    have hg' := Q₂_le_A hC hE hDE hg
    have h1 : g ∈ pCoreOf q (cx x) ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hC.le_pCoreOf_cx hg'.1, Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD) hg'.2⟩
    have h2 := pCoreOf_inf_centralizer_le (p := p) hp hC.setup.prime hC.setup.ne_p (cx x) a h1
    rwa [inf_comm] at h2
  have h145 := hin.i145 hp hp2 (cx a) (Subgroup.zpowers x) hKa (Subgroup.zpowers_le.2 hxa)
    (isPGroup_zpowers_of_mem hE.el hE.mem)
  rw [S3.centralizer_zpowers] at h145
  calc (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G)
      = ⁅⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆, J⁆ := (Q₂_comm_self hc hin hC hE hDE).symm
    _ ≤ ⁅GLAPPrimeCoreOf p (cx a ⊓ cx x), GLAPLayer p (cx a ⊓ cx x)⁆ :=
        Subgroup.commutator_mono hQ₂core hJX
    _ = ⁅GLAPLayer p (cx a ⊓ cx x), GLAPPrimeCoreOf p (cx a ⊓ cx x)⁆ := Subgroup.commutator_comm _ _
    _ ≤ GLAPPrimeCoreOf p (cx a) := h145


theorem covers_cx_of_closure {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D M : Subgroup G}
    (hc : S9Ctx G p) (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J)
    (hDE : D ≤ E)
    (hclosure : ∀ Q₃ : Subgroup G,
      (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤ Q₃ → IsPGroup q Q₃ →
        Q₃ ≤ M ∧ Subgroup.normalizer (Q₃ : Set G) ≤ M)
    {a : G} (haD : a ∈ D) (ha1 : a ≠ 1) : Covers p M (cx a) :=
  covers_of_normalizer_le hc.ctx.prime hC.setup.prime hC.setup.ne_p
    (Q₂_le_core_cx hc hin hC hE hDE haD ha1)
    (hC.isPGroup_Q₁.to_le ((Q₂_le_A hC hE hDE).trans inf_le_left))
    (fun Q₃ h1 h2 _ => (hclosure Q₃ h1 h2).2)

theorem exists_a_with_S {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D M : Subgroup G}
    (hc : S9Ctx G p) (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J) (hDE : D ≤ E)
    (hDcard : Nat.card D = p ^ 2) (hM : IsTwoLocal M) (hJM : J ≤ M) (hDM : D ≤ M) :
    ∃ a ∈ D, a ≠ 1 ∧
      (⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) ≠ ⊥ := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hDel : IsElemAbelian p D := isElemAbelian_mono hE.el hDE
  have hDne : D ≠ ⊥ := by
    intro hD0
    rw [hD0, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hJ' : J ≤ M ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf hJM (hE.le_centralizer.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE)))
  have hnot2 : ¬ IsPGroup 2 J := not_isPGroup_of_component Nat.prime_two hE.comp
  obtain ⟨A, hAD, hAidx, hne⟩ :=
    GL83.I_33_3_proved G hc.ctx.charTwo p hp hp2 M D J hM hDne hDel hDM hJ' hnot2
  have hAcard : Nat.card A = p := by
    have h1 := card_mul_of_index_eq hAD hAidx
    rw [hDcard] at h1
    have hp0 : 0 < p := hp.pos
    have h2 : Nat.card A * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 h2
  have hA1 : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne hAcard
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haD : a ∈ D := hAD haA
  have hord : orderOf a = p := orderOf_eq_prime (hDel.2 a haD) ha1'
  have hAz : Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA) ?_
    rw [Nat.card_zpowers, hord, hAcard]
  refine ⟨a, haD, ha1', ?_⟩
  rw [← hAz, S3.centralizer_zpowers] at hne
  exact hne

theorem lemma95 {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G p)
    (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁) :
    GLATwoLocalRank q G ≤ GLATwoLocalRank p G := by
  by_contra hgt
  push_neg at hgt
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hq : q.Prime := hC.setup.prime
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd : q ∣ Nat.card G := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hC.setup.ne_bot
    have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hord : orderOf g = q := orderOf_eq_prime (hC.setup.exp g hg) hg1'
    rw [← hord]
    exact orderOf_dvd_natCard g
  have hβ : q ∈ GLABeta (GLATwoLocalRank p G + 1) G := ⟨hq, hC.setup.ne_two, hqdvd, hgt⟩
  have hwc := hc.weakCore q hβ
  have h3Q₁ := three_le_pRank_Q₁ hc hin.i713 hC
  obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow (CFSG.LieType.BorelTits.pCoreOf_isPGroup q (cx x))
  obtain ⟨M, hM2, hWM⟩ := hwc.2 R
  have hQ₁R : Q₁ ≤ (R : Subgroup G) := hC.le_pCoreOf_cx.trans hR
  have h3core : 3 ≤ CFSG.Open.pRank q (pCoreOf q (cx x)) := h3Q₁.trans (pRank_mono hq hC.le_pCoreOf_cx)
  have hR3 : 3 ≤ CFSG.Open.pRank q (R : Subgroup G) := h3core.trans (pRank_mono hq hR)
  have hCxM : cx x ≤ M :=
    (le_normalizer_pCoreOf q (cx x)).trans ((normalizer_le_weakCore hq hR h3core).trans hWM)
  have hGB : IsGB p B L := lemma93 hc hin.l93 hC.h hM2 (covers_of_le hCxM)
  obtain ⟨E, J, hE⟩ := exists_EJ hc hin hC hGB
  obtain ⟨D, hDE, hDcard, hne⟩ := exists_D hc hC hE
  have h3Q₂ := three_le_pRank_Q₂ hc hin hC hGB hE hDE hne
  have hQ₂R : (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤ (R : Subgroup G) :=
    ((Q₂_le_A hC hE hDE).trans inf_le_left).trans hQ₁R
  have hclosure : ∀ Q₃ : Subgroup G,
      (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤ Q₃ → IsPGroup q Q₃ →
        Q₃ ≤ M ∧ Subgroup.normalizer (Q₃ : Set G) ≤ M :=
    fun Q₃ h1 h2 => weakCore_closure hq R hWM hR3 hQ₂R h3Q₂ h1 h2
  have hJM : J ≤ M := hE.le_L.trans (hC.h.comp.1.trans hCxM)
  have hDM : D ≤ M := hDE.trans (hE.le.trans (hC.h.le_cx.trans hCxM))
  obtain ⟨a, haD, ha1, hSne⟩ := exists_a_with_S hc hC hE hDE hDcard hM2 hJM hDM
  have hcov := covers_cx_of_closure hc hin hC hE hDE hclosure haD ha1
  have haE : a ∈ E := hDE haD
  have hJa : J ≤ cx a :=
    hE.le_centralizer.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haE))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2M : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hA'2 : IsPGroup 2 (pCoreOf 2 M ⊓ cx a : Subgroup G) := h2M.to_le inf_le_left
  have hJA' : J ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ cx a : Subgroup G) : Set G) :=
    fun j hj => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 M (hJM hj), Subgroup.le_normalizer (hJa hj)⟩
  have hcop2 := coprime_card_of_two_group hp hp2 hA'2
  have hSJ : (⁅⁅pCoreOf 2 M ⊓ cx a, J⁆, J⁆ : Subgroup G) = ⁅pCoreOf 2 M ⊓ cx a, J⁆ :=
    hin.i321 hp _ J hcop2 hJA' (residual_of_component hp hE.comp)
  have hSA' : (⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G) ≤ pCoreOf 2 M ⊓ cx a :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hJA'
  have hScov : (⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (cx a) :=
    le_core_of_covers_two hp hp2 hcov hSA'
  obtain ⟨K₁, hK₁, hJK, hGstar⟩ := exists_Gstar_component hc hin.l93.i183 hC.h.bmax.1 hE.le hE.el
    hE.card haE ha1 (glaPComponent_centralizer hp hC.h.comp hE.mem hE.comp)
  have hodd := hc.stage4.2.1 B a K₁ hC.h.bmax (hE.le haE) ha1 hK₁ hGstar
  have hle : (⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G) ≤
      ⁅closureIn K₁ B, GLAPPrimeCoreOf p (cx a)⁆ := by
    calc (⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G)
        = ⁅⁅pCoreOf 2 M ⊓ cx a, J⁆, J⁆ := hSJ.symm
      _ ≤ ⁅GLAPPrimeCoreOf p (cx a), closureIn K₁ B⁆ := Subgroup.commutator_mono hScov hJK
      _ = ⁅closureIn K₁ B, GLAPPrimeCoreOf p (cx a)⁆ := Subgroup.commutator_comm _ _
  have hodd' : Odd (Nat.card ↥(⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have h2S : IsPGroup 2 (⁅pCoreOf 2 M ⊓ cx a, J⁆ : Subgroup G) := hA'2.to_le hSA'
  have hSbot := eq_bot_of_two_group_odd h2S hodd'
  apply hSne
  rw [Subgroup.commutator_comm]
  exact hSbot

end CFSG.LocalAnalysis.GLTheoremA.S9
