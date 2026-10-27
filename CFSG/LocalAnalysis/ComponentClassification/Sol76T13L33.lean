module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props33C
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma316

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

omit [Finite G] in
theorem conjugate_conjugate_mul (H : Subgroup G) (a b : G) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    show a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ by group]

omit [Finite G] in
theorem conjClosure_le_of_le_self {T L : Subgroup G} (hTL : T ≤ L) : conjClosure T L ≤ L := by
  rw [conjClosure_eq_iSup]
  refine iSup₂_le fun l hl => ?_
  have h1 : L.map (MulAut.conj l⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hl))
  calc conjugate T l = T.map (MulAut.conj l⁻¹).toMonoidHom := rfl
    _ ≤ L.map (MulAut.conj l⁻¹).toMonoidHom := map_mono hTL
    _ = L := h1

omit [Finite G] in
theorem conjugate_one' (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem exists_orderOf_eq_two_of_isTwoComponentIn {X C : Subgroup G} (hX : IsTwoComponentIn X C) :
    ∃ b ∈ X, orderOf b = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) := isQuasisimple_quotient_of_isPComponent hX.1 hX.2
  by_contra hno
  push Not at hno
  have hodd : Odd (Nat.card ↥X) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have := Fintype.ofFinite ↥X
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥X) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    exact hno x x.2 (by rw [orderOf_coe]; exact hx)
  have htop : pPrimeCore 2 ↥X = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨inferInstance, by rw [card_top]; exact Nat.coprime_two_left.mpr hodd⟩)
  have hnt : Nontrivial (↥X ⧸ pPrimeCore 2 ↥X) := LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨y, z, hyz⟩ := hnt.exists_pair_ne
  induction y using QuotientGroup.induction_on with
  | H y =>
  induction z using QuotientGroup.induction_on with
  | H z =>
  apply hyz
  rw [QuotientGroup.eq, htop]
  exact mem_top _

theorem eq_or_eq_of_le_sup {C X P P' : Subgroup G} (hX : IsTwoComponentIn X C)
    (hP : IsTwoComponentIn P C) (hP' : IsTwoComponentIn P' C) (hle : X ≤ P ⊔ P') :
    X = P ∨ X = P' := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hPX : P ≤ coreActionKernel X := GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hP.1 hX.2 hP.2 h1
  have hP'X : P' ≤ coreActionKernel X :=
    GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hP'.1 hX.2 hP'.2 h2
  have hperf : ⁅X, X⁆ = X := UnbalancedCorr.commutator_eq_of_isPComponent hX.1 hX.2
  exact not_le_coreActionKernel_of_le le_rfl hperf (exists_orderOf_eq_two_of_isTwoComponentIn hX)
    (hle.trans (sup_le hPX hP'X))

theorem conjClosure_le_of_two_le_pRank (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K K' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K' ≠ K) {a : G} (ha : orderOf a = 2) (haK : K ≤ centralizer ({a} : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank 2 (K' ⊓ centralizer ({a} : Set G))) :
    conjClosure K (twoLayerIn (centralizer ({a} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set La := twoLayerIn Ca with hLa
  set S := conjClosure K La with hS
  have hKL : K ≤ La := by
    set U := zpowers a with hU
    have hCU : centralizer (U : Set G) = Ca := by rw [hU, zpowers_eq_closure, centralizer_closure]
    have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hUne : U ≠ ⊥ := fun h => by
      rw [hU, zpowers_eq_bot] at h
      rw [h, orderOf_one] at ha
      norm_num at ha
    have hUQ : U ≤ coreActionKernel K := by
      rw [hU, zpowers_le]
      exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
        mem_centralizer_singleton_iff.mp (haK hk)
    have h1 := lemma212Input G K U hK.2 hUne hU2 hUQ
    rw [hCU, inf_eq_left.mpr haK, twoLayerIn_eq_self_of_isTwoComponentIn hK.1] at h1
    exact h1.trans (solomonKStarOf_le_twoLayerIn Ca)
  have hKS : K ≤ S := le_conjClosure K La
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hKinv := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
  have hcomm := commutator_eq_bot_of_mem_kStarComponents h315a hG hN hK' hK hne
  have hstep : ∀ e ∈ K' ⊓ Ca, orderOf e = 2 →
      S ≤ oddCoreIn La ⊔ K ∨
        ∃ B : Subgroup G, IsTwoComponentIn B Ca ∧ S = B ⊔ conjugate B e ∧ conjugate B e ≠ B := by
    intro e he he2
    have hKCe : K ≤ centralizer ({e} : Set G) := fun k hk =>
      mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm he.1) k hk))
    have hKe := isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN hK' hK hne he.1 he2
    have hKC : K ≤ Ca ⊓ centralizer ({e} : Set G) := le_inf haK hKCe
    have hKpc : IsPComponent 2 (K.subgroupOf (Ca ⊓ centralizer ({e} : Set G))) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKC inf_le_right hKe.2
    obtain ⟨B, hBCa, hBpc, -, hcl, hcase⟩ := foote_lemma_2_1_iv_subgroup he.2 he2 hKC hKpc
    have hB : IsTwoComponentIn B Ca := ⟨hBCa, hBpc⟩
    rcases hcase with ⟨hBe, hBres, -⟩ | ⟨hBe, -, hiso⟩ | ⟨hBe, -, -⟩
    ·
      left
      have hSB : S = B := by rw [hS, hcl, hBe, sup_idem]
      intro x hx
      have hxKO : x ∈ oddCoreIn Ca ⊔ K := by
        have hxB : x ∈ B := hSB ▸ hx
        rw [hBres] at hxB
        rw [sup_comm]
        exact ((closure_le _).mpr fun _ hg => hg.1) hxB
      have hKO : K ≤ normalizer (oddCoreIn Ca : Set G) := haK.trans (le_normalizer_oddCoreIn Ca)
      obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup_normalizer hKO hxKO
      have hoL : o ∈ La := by
        have : o = o * k * k⁻¹ := by group
        rw [this]
        exact mul_mem (conjClosure_le_of_le_self hKL hx) (inv_mem (hKL hk))
      have hLO : La ≤ normalizer (oddCoreIn Ca : Set G) :=
        (map_subtype_le _).trans (le_normalizer_oddCoreIn Ca)
      have hoO : o ∈ oddCoreIn La :=
        inf_le_oddCoreIn (coprime_card_oddCoreIn Ca) hLO ⟨ho, hoL⟩
      exact mul_mem (mem_sup_left hoO) (mem_sup_right hk)
    ·
      exfalso
      have hSB : S = B := by rw [hS, hcl, hBe, sup_idem]
      have hKB : K ≤ B := hSB ▸ hKS
      have hKm : ¬ K ≤ coreActionKernel B := not_le_coreActionKernel_of_le hKB hKperf hKinv
      have hequiv := solomonEquiv_of_not_le_coreActionKernel ha hK.1 hK.2.1 haK hKL hB hKm
      obtain ⟨φ⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
      exact hiso.false φ
    · exact Or.inr ⟨B, hB, hcl, hBe⟩
  obtain ⟨E, hEK, hE, hEcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (K' ⊓ Ca)
  have := Fintype.ofFinite ↥E
  have h4 : 4 ≤ Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card, hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (K' ⊓ Ca) := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; omega) (1 : ↥E)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥E))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  have hsq : ∀ w : ↥E, (w : G) ^ 2 = 1 := fun w => hE.2 w w.2
  have hinv2 : ∀ w : ↥E, w ≠ 1 → orderOf (w : G) = 2 := fun w hw =>
    orderOf_eq_prime (hsq w) fun h => hw (Subtype.ext h)
  have huv : (u : G) * v = v * u := by
    have := hE.1.is_comm.comm u v
    exact congrArg Subtype.val this
  have huv1 : u * v ≠ 1 := by
    intro h
    apply hvu
    have huinv : ((u : G))⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hsq u]
    apply Subtype.ext
    exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val h)).trans huinv
  have hmem : ∀ w : ↥E, (w : G) ∈ K' ⊓ Ca := fun w => hEK w.2
  have hsq' : ∀ {x : G}, x ^ 2 = 1 → x * x = 1 := fun h => by rwa [← pow_two]
  rcases hstep (u : G) (hmem u) (hinv2 u hu) with h | ⟨B₁, hB₁, hS₁, hne₁⟩
  · exact h
  rcases hstep (v : G) (hmem v) (hinv2 v hv1) with h | ⟨B₂, hB₂, hS₂, hne₂⟩
  · exact h
  rcases hstep ((u * v : ↥E) : G) (hmem (u * v)) (hinv2 (u * v) huv1) with h | ⟨B₃, hB₃, hS₃, hne₃⟩
  · exact h
  exfalso
  set e₁ : G := (u : G) with he₁
  set e₂ : G := (v : G) with he₂
  have he₃ : ((u * v : ↥E) : G) = e₁ * e₂ := rfl
  rw [he₃] at hS₃ hne₃
  set P := B₁ with hP
  set P' := conjugate B₁ e₁ with hP'
  have hconjC : ∀ {B : Subgroup G} {e : G}, IsTwoComponentIn B Ca → e ∈ Ca →
      IsTwoComponentIn (conjugate B e) Ca := fun hB he =>
    isTwoComponentIn_map_conj hB (le_normalizer (inv_mem he))
  have hP'2 : IsTwoComponentIn P' Ca := hconjC hB₁ (hmem u).2
  have hpair : ∀ {X : Subgroup G}, IsTwoComponentIn X Ca → X ≤ S → X = P ∨ X = P' :=
    fun hX hXS => eq_or_eq_of_le_sup hX hB₁ hP'2 (hS₁ ▸ hXS)
  have hinvol : ∀ {B : Subgroup G} {e : G}, e * e = 1 → conjugate (conjugate B e) e = B := by
    intro B e he
    rw [conjugate_conjugate_mul, he, conjugate_one']
  have hS₂e : conjugate S e₂ = S := by
    rw [hS₂, conjugate, Subgroup.map_sup, ← conjugate, ← conjugate,
      hinvol (hsq' (hsq v)), sup_comm]
  have hPe₂ : conjugate P e₂ = P ∨ conjugate P e₂ = P' := by
    refine hpair (hconjC hB₁ (hmem v).2) ?_
    rw [← hS₂e]
    exact map_mono (hS₁ ▸ le_sup_left)
  have hcommE : e₁ * e₂ = e₂ * e₁ := huv
  rcases hPe₂ with hPP | hPP'
  ·
    have hP'e₂ : conjugate P' e₂ = P' := by
      rw [hP', conjugate_conjugate_mul, hcommE, ← conjugate_conjugate_mul, hPP]
    rcases hpair hB₂ (hS₂ ▸ le_sup_left) with h | h
    · exact hne₂ (by rw [h, hPP])
    · exact hne₂ (by rw [h, hP'e₂])
  ·
    have hPe₃ : conjugate P (e₁ * e₂) = P := by
      rw [← conjugate_conjugate_mul, ← hP', ← hPP', hinvol (hsq' (hsq v))]
    have hP'e₃ : conjugate P' (e₁ * e₂) = P' := by
      rw [hP', conjugate_conjugate_mul, ← mul_assoc, hsq' (hsq u), one_mul, hPP']
    rcases hpair hB₃ (hS₃ ▸ le_sup_left) with h | h
    · exact hne₃ (by rw [h, hPe₃])
    · exact hne₃ (by rw [h, hP'e₃])

theorem lemma33CentralInputFor_of_residue (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hres : Lemma33ResidueInputFor 𝒜) : Lemma33CentralInputFor 𝒜 := by
  intro G _ _ hG N hN K hK a haN ha haK
  by_cases h : ∀ K' ∈ kStarComponents N, K' ≠ K →
      CFSG.Open.pRank 2 (K' ⊓ centralizer ({a} : Set G)) ≤ 1
  · exact hres G hG N hN K hK a haN ha haK h
  · push Not at h
    obtain ⟨K', hK', hne, h2⟩ := h
    exact conjClosure_le_of_two_le_pRank h32 h315a h315c hG hN hK hK' hne ha haK (by omega)

end CFSG.ComponentClassification.Sol76T13
