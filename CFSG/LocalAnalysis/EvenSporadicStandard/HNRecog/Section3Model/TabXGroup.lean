module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem pCoreOf_two_le (L : Subgroup G) : CFSG.Open.pCoreOf 2 L ≤ L :=
  Subgroup.map_subtype_le _

theorem isPGroup_pCoreOf_two (L : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype

theorem le_pCoreOf_two_of_normalized {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQn : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (hQ : IsPGroup 2 Q) :
    Q ≤ CFSG.Open.pCoreOf 2 L := by
  have hPp : IsPGroup 2 (Q.subgroupOf L) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
  have hPnorm : (Q.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff hQL).mpr fun h k hh hk => hQn k hk h hh
  calc Q = (Q.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hQL).symm
    _ ≤ (CFSG.pCore 2 ↥L).map L.subtype := Subgroup.map_mono (le_sSup ⟨hPnorm, hPp⟩)
    _ = CFSG.Open.pCoreOf 2 L := rfl

theorem conj_mem_pCoreOf_two {L : Subgroup G} {c : G}
    (hL : L.map (MulAut.conj c).toMonoidHom = L) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 L) :
    c * x * c⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have h := pCoreOf_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective L
  rw [hL] at h
  rw [h]
  exact ⟨x, hx, rfl⟩

theorem map_conj_eq_of_normalized {X U : Subgroup G} {k : G} (hk : k ∈ X)
    (hU : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U) : U.map (MulAut.conj k).toMonoidHom = U := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hU k hk u hu
  · intro hy
    refine ⟨k⁻¹ * y * k, ?_, ?_⟩
    · simpa using hU k⁻¹ (X.inv_mem hk) y hy
    · show k * (k⁻¹ * y * k) * k⁻¹ = y
      group

theorem map_conj_stab {X : Subgroup G} {k : G} (hk : k ∈ X) (c : G) :
    (X ⊓ Gx c).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c * k⁻¹) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective,
    map_conj_eq_of_normalized hk (fun x hx u hu => X.mul_mem (X.mul_mem hx hu) (X.inv_mem hx)),
    TwoHSData.map_centralizer_singleton (MulAut.conj k) c]
  rfl

theorem quotShape_prime [Finite G] {M N : Subgroup G} {p : ℕ} [Fact p.Prime] (hNM : N ≤ M)
    (hnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hcard : Nat.card M = p * Nat.card N) :
    QuotShape M N (Z p) := by
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNM).mpr fun h m hh hm => hnorm m hm h hh
  refine ⟨hN, ?_⟩
  have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hq : Nat.card (↥M ⧸ N.subgroupOf M) = p := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)
    rw [hcardN, hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  haveI : IsCyclic (↥M ⧸ N.subgroupOf M) := isCyclic_of_prime_card hq
  have hZ : Nat.card (Z p) = p := by
    rw [Z, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  haveI : IsCyclic (Z p) := isCyclic_of_prime_card hZ
  exact ⟨mulEquivOfCyclicCardEq (hq.trans hZ.symm)⟩

theorem quotShape_elem2_two [Finite G] {X D : Subgroup G} (hDX : D ≤ X)
    (hnorm : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hcard : Nat.card X = 4 * Nat.card D)
    {g₁ g₂ : G} (h₁ : g₁ ∈ X) (h₂ : g₂ ∈ X) (hs₁ : g₁ * g₁ ∈ D) (hs₂ : g₂ * g₂ ∈ D)
    (hn₁ : g₁ ∉ D) (hn₂ : g₂ ∉ D) (hn₁₂ : g₁ * g₂⁻¹ ∉ D) : QuotShape X D (Elem2 2) := by
  classical
  have hN : (D.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hDX).mpr fun h m hh hm => hnorm m hm h hh
  refine ⟨hN, ?_⟩
  have hcardD : Nat.card ↥(D.subgroupOf X) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hq : Nat.card (↥X ⧸ D.subgroupOf X) = 2 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf X)
    rw [hcardD, hcard] at h
    have := (Nat.eq_of_mul_eq_mul_right hpos h).symm
    rw [this]
    norm_num
  set Q := ↥X ⧸ D.subgroupOf X with hQ
  let a : Q := QuotientGroup.mk ⟨g₁, h₁⟩
  let b : Q := QuotientGroup.mk ⟨g₂, h₂⟩
  have ha1 : a ≠ 1 := by
    intro h
    exact hn₁ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hb1 : b ≠ 1 := by
    intro h
    exact hn₂ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hab : a ≠ b := by
    intro h
    have h' := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_iff_div_mem).mp h)
    apply hn₁₂
    simpa [div_eq_mul_inv] using h'
  have ha2 : a * a = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hs₁
  have hb2 : b * b = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hs₂
  have hsq : ∀ q : Q, q * q = 1 := by
    intro q
    by_contra hq2
    have hdvd : orderOf q ∣ 4 := by simpa [hq] using orderOf_dvd_natCard q
    have hmem : orderOf q ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hord : orderOf q = 4 := by
      rcases hmem with h | h | h
      · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_mul]) hq2
      · exact absurd (by rw [← pow_two, ← h]; exact pow_orderOf_eq_one q) hq2
      · exact h
    haveI : IsCyclic Q := isCyclic_of_orderOf_eq_card q (by rw [hord, hq]; norm_num)
    haveI : Fintype Q := Fintype.ofFinite Q
    have hcount := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
    have hsub : ({1, a, b} : Finset Q) ⊆ Finset.univ.filter (fun x : Q => x ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl
      · exact one_pow 2
      · rw [pow_two]; exact ha2
      · rw [pow_two]; exact hb2
    have h3 : ({1, a, b} : Finset Q).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [ha1.symm, hb1.symm]),
        Finset.card_pair hab]
    have := Finset.card_le_card hsub
    omega
  exact TwoHSData.nonempty_mulEquiv_elem2 2 hsq hq

theorem pCoreOf_eq_of_hom_sym5 [Finite G] {Y N : Subgroup G} (hNY : N ≤ Y)
    (hY : Nat.card ↥Y = 30720) (hN : Nat.card ↥N = 256) (ψ : ↥Y →* Equiv.Perm (Fin 5))
    (hrange : Nat.card ↥ψ.range = 120) (hNker : ∀ (n : G) (h : n ∈ N), ψ ⟨n, hNY h⟩ = 1) :
    CFSG.Open.pCoreOf 2 Y = N := by
  have hkerCard : Nat.card ↥ψ.ker = 256 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, hY] at h
    omega
  have hle : N.subgroupOf Y ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    simpa using hNker (y : G) (Subgroup.mem_subgroupOf.mp hy)
  have hNcard : Nat.card ↥(N.subgroupOf Y) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv, hN]
  have hker : N.subgroupOf Y = ψ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hkerCard, hNcard])
  have hNnormal : (N.subgroupOf Y).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker ψ
  have hNp : IsPGroup 2 ↥(N.subgroupOf Y) := IsPGroup.of_card (n := 8) (by rw [hNcard]; norm_num)
  apply le_antisymm
  · have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have hrangeTop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, h120])
    have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrangeTop
    have hPmap : (CFSG.pCore 2 ↥Y).map ψ = ⊥ :=
      eq_bot_of_normal_isPGroup_sym_five _
        ((CFSG.pCore_normal (p := 2) (G := ↥Y)).map ψ hsurj)
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map ψ)
    have hPle : CFSG.pCore 2 ↥Y ≤ ψ.ker := by
      intro x hx
      have h1 : ψ x ∈ (CFSG.pCore 2 ↥Y).map ψ := ⟨x, hx, rfl⟩
      rw [hPmap] at h1
      simpa using h1
    calc CFSG.Open.pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := rfl
      _ ≤ (N.subgroupOf Y).map Y.subtype := Subgroup.map_mono (hker ▸ hPle)
      _ = N := Subgroup.map_subgroupOf_eq_of_le hNY
  · have h1 : N.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hNnormal, hNp⟩
    calc N = (N.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
      _ ≤ (CFSG.pCore 2 ↥Y).map Y.subtype := Subgroup.map_mono h1

theorem pCoreOf_two_normalized (X : Subgroup G) {x r : G} (hx : x ∈ X)
    (hr : r ∈ CFSG.Open.pCoreOf 2 X) : x * r * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
  conj_mem_pCoreOf_two (map_conj_eq_of_normalized hx
    fun y hy u hu => X.mul_mem (X.mul_mem hy hu) (X.inv_mem hy)) hr

theorem derivedOf_le_of_quotShape {X D : Subgroup G} (hDX : D ≤ X)
    (h : QuotShape X D (Elem2 2)) : derivedOf X ≤ D := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  let χ : ↥X →* Elem2 2 := e.toMonoidHom.comp (QuotientGroup.mk' (D.subgroupOf X))
  have hker : χ.ker ≤ D.subgroupOf X := by
    intro x hx
    have h1 : e (QuotientGroup.mk' (D.subgroupOf X) x) = 1 := hx
    have h2 : (QuotientGroup.mk' (D.subgroupOf X) x) = 1 := by
      apply e.injective
      rw [h1, map_one]
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hcomm : _root_.commutator ↥X ≤ D.subgroupOf X :=
    (Abelianization.commutator_subset_ker χ).trans hker
  calc derivedOf X = (_root_.commutator ↥X).map X.subtype := rfl
    _ ≤ (D.subgroupOf X).map X.subtype := Subgroup.map_mono hcomm
    _ = D := Subgroup.map_subgroupOf_eq_of_le hDX

theorem derivedOf_le_commutator (X : Subgroup G) : derivedOf X ≤ _root_.commutator G := by
  have h : (_root_.commutator ↥X).map X.subtype ≤ _root_.commutator G := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h

theorem map_conj_centerOf {D X : Subgroup G} {k : G} (hk : k ∈ X)
    (hD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) :
    (centerOf D).map (MulAut.conj k).toMonoidHom = centerOf D := by
  have h := centerOf_map_of_injective (f := (MulAut.conj k).toMonoidHom)
    (MulAut.conj k).injective D
  rw [map_conj_eq_of_normalized hk hD] at h
  exact h.symm

private lemma factorization_30720_three : (30720 : ℕ).factorization 3 = 1 := by
  have h : (30720 : ℕ) = 3 * 10240 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_of_orderOf_three [Finite G] {X : Subgroup G} (hX : Nat.card ↥X = 30720)
    {σ₀ t σ : G} (h₀ : σ₀ ∈ X) (h₀o : orderOf σ₀ = 3) (ht : t ∈ X)
    (htσ : t * σ₀ * t⁻¹ = σ₀⁻¹) (hσ : σ ∈ X) (hσo : orderOf σ = 3) :
    ∃ k ∈ X, k * σ₀ * k⁻¹ = σ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : Nat.card (zpowers σ₀) = 3 ^ (Nat.card X).factorization 3 := by
    rw [Nat.card_zpowers, h₀o, hX, factorization_30720_three, pow_one]
  obtain ⟨x, hxX, hx⟩ := TwoHSData.exists_conj_mem_of_orderOf_eq_prime (p := 3) (R := X)
    (S := zpowers σ₀) (Subgroup.zpowers_le.mpr h₀) hS hσ hσo
  rw [mem_zpowers_iff_mem_range_orderOf] at hx
  obtain ⟨m, hm, hmeq⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range, h₀o] at hm
  have hσeq : σ = x * σ₀ ^ m * x⁻¹ := by rw [hmeq]; group
  have hcube : σ₀ ^ 3 = 1 := h₀o ▸ pow_orderOf_eq_one σ₀
  interval_cases m
  · exfalso
    have h1 : σ = 1 := by rw [hσeq]; group
    rw [h1, orderOf_one] at hσo
    omega
  · exact ⟨x, hxX, by rw [hσeq]; group⟩
  · refine ⟨x * t, X.mul_mem hxX ht, ?_⟩
    have hinv : σ₀ ^ 2 = σ₀⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hcube
    calc x * t * σ₀ * (x * t)⁻¹ = x * (t * σ₀ * t⁻¹) * x⁻¹ := by group
      _ = x * σ₀ ^ 2 * x⁻¹ := by rw [htσ, hinv]
      _ = σ := hσeq.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
