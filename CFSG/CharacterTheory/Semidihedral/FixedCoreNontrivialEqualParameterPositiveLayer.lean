module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveTorus
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialOddComplement

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card exists_isSylowOf)
open _root_.CFSG.Semidihedral.FixedCoreNontrivial.Positive

namespace PositiveInputs

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem card_lt_sixteen (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hX4 : ∀ T : Subgroup G, T ≤ X → ¬ IsKleinFour T) : Nat.card X < 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := h.localData
  obtain ⟨T, hXT⟩ := hX.exists_le_sylow
  have hT := hI.card_sylow_two T
  have hle : Nat.card X ≤ 16 := hT ▸ Subgroup.card_le_of_le hXT
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hXT' : X = T := Subgroup.eq_of_le_of_card_ge hXT (by rw [hT, heq])
    obtain ⟨S, hVS, -⟩ := h.sylow_two
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
    have hmem : ∀ v ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀, g * v * g⁻¹ ∈ X := by
      intro v hv
      rw [hXT', ← hg, coe_smul_sylow, mem_map_conj_iff]
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rw [e]
      exact hVS hv
    obtain ⟨T4, hT4X, hT4⟩ := exists_kleinFour_le_of_conj hL.t_sq hL.t_ne_one hL.s_sq
      hL.s_ne_one hL.s_ne.symm hL.ts g
      (hmem t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)))
      (hmem s₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)))
    exact hX4 T4 hT4X hT4

theorem factorization_card_C (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) {r : ℕ}
    (hr : r.Prime) (hrb : r ∣ Nat.card ((N t).map (C t).subtype)) :
    (Nat.card (C t)).factorization r =
      (Nat.card ((N t).map (C t).subtype) ^ 2).factorization r := by
  obtain ⟨-, -, hbodd, -, -, hCcard⟩ := hI.numerics h he
  obtain ⟨hbw, -, hqb, -, -⟩ := hI.coprimes h he
  set b := Nat.card ((N t).map (C t).subtype)
  set w := Nat.card (torusW G t s₀)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr hrb)
  have hrc : ¬ r ∣ 16 * p ^ f * w := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with hdvd | hdvd
    · rcases (Nat.Prime.dvd_mul hr).mp hdvd with hdvd | hdvd
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 4 by norm_num; exact hdvd)))
      · exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hqb hdvd hrb)
    · exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hbw hrb hdvd)
  have hw0 : w ≠ 0 := Nat.card_pos.ne'
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
  rw [hCcard, show 16 * b ^ 2 * p ^ f * w = b ^ 2 * (16 * p ^ f * w) by ring,
    Nat.factorization_mul (pow_ne_zero 2 Nat.card_pos.ne') (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hrc, add_zero]

theorem layer_prime_step (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {M OM O : Subgroup G} (hno4 : ∀ T : Subgroup G, T ≤ M → ¬ IsKleinFour T) (htM : t ∈ M)
    (hOMM : OM ≤ M) (hOModd : Odd (Nat.card OM))
    (hXO : O ⊔ (N t).map (C t).subtype ≤ OM) (hXC : O ⊔ (N t).map (C t).subtype ≤ C t)
    (hXcard : Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G) =
      Nat.card ((N t).map (C t).subtype) ^ 2)
    (hXnorm : ∀ E : Subgroup G, E ≤ O ⊔ (N t).map (C t).subtype →
      ¬ E ≤ (N t).map (C t).subtype →
      ∀ c ∈ C t ⊓ Subgroup.normalizer (E : Set G), Odd (orderOf c) →
        c ∈ O ⊔ (N t).map (C t).subtype)
    {r : ℕ} (hr : r.Prime) (hrb : r ∣ Nat.card ((N t).map (C t).subtype)) :
    ∃ Or : Subgroup G, IsSylowOf r Or OM ∧ Or ≤ O ⊔ (N t).map (C t).subtype ∧
      OM ⊓ Subgroup.normalizer (Or : Set G) ≤ O ⊔ (N t).map (C t).subtype ∧
      Nat.card Or = r ^ (Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G)).factorization r := by
  have : Fact r.Prime := ⟨hr⟩
  have hL := h.localData
  set B := (N t).map (C t).subtype with hB
  set X := O ⊔ B with hX
  obtain ⟨Br⟩ : Nonempty (Sylow r B) := inferInstance
  have hBrX : (Br : Subgroup B).map B.subtype ≤ X := (Subgroup.map_subtype_le _).trans le_sup_right
  obtain ⟨Xr, hXr, hBrXr⟩ := exists_isSylowOf_le hBrX (Br.isPGroup'.map B.subtype)
  obtain ⟨Or, hOr, hXrOr⟩ := exists_isSylowOf_le (hXr.le.trans hXO) hXr.isPGroup
  obtain ⟨hOrC, -⟩ := hI.le_C_of_isPGroup hr hrb Br hOr.isPGroup (hBrXr.trans hXrOr)
  have hXrC : IsSylowOf r Xr (C t) := by
    apply isSylowOf_of_card (hXr.le.trans hXC)
    rw [hXr.card_eq, hXcard, hI.factorization_card_C h he hr hrb]
  have hOrXr : Or = Xr := hXrC.eq_of_le hXrOr hOrC hOr.isPGroup
  have hOrX : Or ≤ X := hOrXr ▸ hXr.le
  have hOrcard : Nat.card Or = r ^ (Nat.card X).factorization r := hOrXr ▸ hXr.card_eq
  have hOrB : ¬ Or ≤ B := by
    intro hle
    have hdvd : Nat.card Or ∣ Nat.card B := Subgroup.card_dvd_of_le hle
    rw [hOrcard, hXcard, Nat.factorization_pow] at hdvd
    have hk := hr.factorization_pos_of_dvd (Nat.card_pos (α := B)).ne' hrb
    apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := B)).ne' hr
    refine (Nat.pow_dvd_pow r ?_).trans hdvd
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega
  obtain ⟨u, huBr, hu1⟩ : ∃ u ∈ (Br : Subgroup B).map B.subtype, u ≠ 1 := by
    have hne : (Br : Subgroup B).map B.subtype ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, Subgroup.card_map_of_injective B.subtype_injective,
        Br.card_eq_multiplicity]
      exact Nat.one_lt_pow (hr.factorization_pos_of_dvd (Nat.card_pos (α := B)).ne' hrb).ne'
        hr.one_lt
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨u, hu, fun h' => hu1 (Subtype.ext h')⟩
  have huB : u ∈ B := (Subgroup.map_subtype_le _) huBr
  have huOr : u ∈ Or := hXrOr (hBrXr huBr)
  have hNC : M ⊓ Subgroup.normalizer (Or : Set G) ≤ C t := by
    rintro n ⟨hnM, hnN⟩
    have ht'M : n * t * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM htM) (M.inv_mem hnM)
    have ht'u : n * t * n⁻¹ * u = u * (n * t * n⁻¹) := by
      have hu' : n⁻¹ * u * n ∈ Or := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) u).mp huOr
        rwa [inv_inv] at this
      have hc : n⁻¹ * u * n * t = t * (n⁻¹ * u * n) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hOrC hu')
      calc n * t * n⁻¹ * u = n * (t * (n⁻¹ * u * n)) * n⁻¹ := by group
        _ = n * (n⁻¹ * u * n * t) * n⁻¹ := by rw [hc]
        _ = u * (n * t * n⁻¹) := by group
    have ht'C : n * t * n⁻¹ ∈ C t :=
      h.confine u huB hu1 (Subgroup.mem_centralizer_singleton_iff.mpr ht'u)
    by_contra hn
    have hne : t ≠ n * t * n⁻¹ := by
      intro htt
      apply hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [← htt]
    obtain ⟨T, hTM, hT⟩ := exists_kleinFour_le (a := t) (b := n * t * n⁻¹) hL.t_sq hL.t_ne_one
      (by rw [show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, hL.t_sq]; group)
      (by
        intro h1
        apply hL.t_ne_one
        calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
          _ = 1 := by rw [h1]; group)
      hne (Subgroup.mem_centralizer_singleton_iff.mp ht'C).symm htM ht'M
    exact hno4 T hTM hT
  refine ⟨Or, hOr, hOrX, ?_, hOrcard⟩
  rintro n ⟨hnO, hnN⟩
  exact hXnorm Or hOrX hOrB n (Subgroup.mem_inf.mpr ⟨hNC ⟨hOMM hnO, hnN⟩, hnN⟩)
    (odd_orderOf_of_mem hOModd hnO)

theorem layer_sylow_of_maximal (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {Q₁ Y O R : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t))
    (hY : Y ≤ C t ⊓ Subgroup.normalizer (Q₁ : Set G)) (hYcyc : IsCyclic Y)
    (hYcard : Nat.card Y = 2 * (p ^ f - 1)) (htY : t ∈ Y)
    (hYB : Disjoint Y ((N t).map (C t).subtype)) (hOY : O ≤ Y)
    (hOB : ∀ y ∈ O, ∀ x ∈ (N t).map (C t).subtype, y * x = x * y)
    (hXcard : Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G) =
      Nat.card ((N t).map (C t).subtype) ^ 2)
    (hXnorm : ∀ E : Subgroup G, E ≤ O ⊔ (N t).map (C t).subtype →
      ¬ E ≤ (N t).map (C t).subtype →
      ∀ c ∈ C t ⊓ Subgroup.normalizer (E : Set G), Odd (orderOf c) →
        c ∈ O ⊔ (N t).map (C t).subtype)
    (hQR : Q₁ ≤ R) (hR : IsPGroup p R)
    (hRinv : Y ⊔ (N t).map (C t).subtype ≤ Subgroup.normalizer (R : Set G))
    (hRmax : ∀ R' : Subgroup G, IsPGroup p R' →
      Y ⊔ (N t).map (C t).subtype ≤ Subgroup.normalizer (R' : Set G) → R ≤ R' → R' = R) :
    ∃ T : Sylow p G, (T : Subgroup G) = R := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, -, hbodd, -, -, -⟩ := hI.numerics h he
  obtain ⟨-, -, -, -, hpb⟩ := hI.coprimes h he
  have hL := h.localData
  set B := (N t).map (C t).subtype with hB
  set M := Subgroup.normalizer (R : Set G) with hM
  set OM := (CFSG.pPrimeCore 2 M).map M.subtype with hOM
  set X := O ⊔ B with hX
  have hYM : Y ≤ M := le_sup_left.trans hRinv
  have hBM : B ≤ M := le_sup_right.trans hRinv
  have htM : t ∈ M := hYM htY
  obtain ⟨hQ₁card, -⟩ := hI.sylow_C_facts hQ₁
  have hR1 : R ≠ ⊥ := by
    intro hRb
    have h1 : Nat.card Q₁ ≤ 1 := by
      calc Nat.card Q₁ ≤ Nat.card R := Subgroup.card_le_of_le hQR
        _ = 1 := by rw [hRb, Subgroup.card_bot]
    have h2 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
    omega
  have hno4 := hI.not_kleinFour_le_normalizer h he hR hR1
  obtain ⟨Y₂, hY₂⟩ := exists_isSylowOf 2 Y
  have hY₂card : Nat.card Y₂ = 8 := by
    have h8 : 2 * (p ^ f - 1) = 2 ^ 3 * Nat.card B := by omega
    have hb2 : ¬ 2 ∣ Nat.card B := fun h2 =>
      (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr h2)
    rw [hY₂.card_eq, hYcard, h8, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hb2, add_zero,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
    norm_num
  obtain ⟨SM, hSM, hY₂SM⟩ := exists_isSylowOf_le (hY₂.le.trans hYM) hY₂.isPGroup
  have hSMlt := hI.card_lt_sixteen h hSM.isPGroup (fun T hT => hno4 T (hT.trans hSM.le))
  have hSMeq : Y₂ = SM := by
    apply Subgroup.eq_of_le_of_card_ge hY₂SM
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hSM.isPGroup
    have h8 : 8 ∣ 2 ^ n := by
      rw [← hn, ← hY₂card]
      exact Subgroup.card_dvd_of_le hY₂SM
    rw [hY₂card, hn]
    rw [hn] at hSMlt
    have hn4 : n < 4 := by
      by_contra hc
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all
  have hSMcyc : IsCyclic SM := by
    have := hYcyc
    rw [← hSMeq]
    exact Subgroup.isCyclic_of_le hY₂.le
  obtain ⟨SM', hSM'⟩ := exists_sylow_isCyclic hSM hSMcyc
  obtain ⟨hM2, hModd⟩ := hI.odd_mem_pPrimeCore_of_isCyclic_sylow SM' hSM'
  have hOModd : Odd (Nat.card OM) := odd_card_map_pPrimeCore M
  have hOMM : OM ≤ M := Subgroup.map_subtype_le _
  have hle_OM : ∀ Z : Subgroup G, Z ≤ M → Odd (Nat.card Z) → Z ≤ OM :=
    fun Z hZM hZ x hx => hModd x (hZM hx) (odd_orderOf_of_mem hZ hx)
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact hbodd.pow
  have hXO : X ≤ OM := hle_OM X (sup_le (hOY.trans hYM) hBM) hXodd
  have hXC : X ≤ C t := sup_le (hOY.trans (hY.trans inf_le_left)) (Subgroup.map_subtype_le _)
  have hYcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    have := hYcyc
    intro x hx y hy
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := Y)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    comm_of_mem_sup (fun a ha b hb => hYcomm a (hOY ha) b (hOY hb)) hL.B_comm hOB hx hy
  have hstep := fun r (hr : r.Prime) (hrb : r ∣ Nat.card B) =>
    hI.layer_prime_step h he hno4 htM hOMM hOModd hXO hXC hXcard hXnorm hr hrb
  have hcomp : ∀ r ∈ (Nat.card (X.subgroupOf OM)).primeFactors, ∃ M' : Subgroup OM,
      M'.Normal ∧ ¬ r ∣ Nat.card (M' ⊓ X.subgroupOf OM : Subgroup OM) ∧
        M'.index ≤ r ^ (Nat.card (X.subgroupOf OM)).factorization r := by
    intro r hr
    have hcardX' : Nat.card (X.subgroupOf OM) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXO).toEquiv
    rw [hcardX'] at hr ⊢
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrX : r ∣ Nat.card X := Nat.dvd_of_mem_primeFactors hr
    have hrb : r ∣ Nat.card B := by
      rw [hXcard] at hrX
      exact hrp.dvd_of_dvd_pow hrX
    have : Fact r.Prime := ⟨hrp⟩
    obtain ⟨Or, ⟨S, hS⟩, hOrX, hNX, hOrcard⟩ := hstep r hrp hrb
    have hSc : Subgroup.normalizer (S : Set OM) ≤ Subgroup.centralizer (S : Set OM) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hnN : (n : G) ∈ Subgroup.normalizer (Or : Set G) := by
        apply mem_normalizer_of_conj_mem
        rw [← hS]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨n * s * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn s).mp hs, rfl⟩
      have hnX : (n : G) ∈ X := hNX (Subgroup.mem_inf.mpr ⟨n.2, hnN⟩)
      have hyX : (y : G) ∈ X := hOrX (hS ▸ ⟨y, hy, rfl⟩)
      exact Subtype.ext (hXcomm _ hyX _ hnX)
    obtain ⟨Mr, hMrn, hMrr, hMridx⟩ := exists_normal_pComplement S hSc
    refine ⟨Mr, hMrn, fun hdvd => hMrr (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left)), ?_⟩
    rw [hMridx]
    have hScard : Nat.card S = Nat.card Or := by
      rw [← hS, Subgroup.card_map_of_injective OM.subtype_injective]
    rw [hScard, hOrcard]
  obtain ⟨M', hM'n, hM'⟩ := exists_normal_isComplement'_of_primewise (X.subgroupOf OM) hcomp
  obtain ⟨V₀, hV₀O, hOV₀, -, -, hV₀card⟩ := exists_normal_complement_of_subgroupOf hXO hM'n hM'
  have hV₀cop : Nat.Coprime (Nat.card V₀) (Nat.card X) := by
    apply Nat.coprime_of_dvd
    intro r hr hrV hrX
    have hrb : r ∣ Nat.card B := by
      rw [hXcard] at hrX
      exact hr.dvd_of_dvd_pow hrX
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨Or, hOr, -, -, hOrcard⟩ := hstep r hr hrb
    have h1 := hOr.card_eq
    rw [hOrcard] at h1
    have h2 : (Nat.card X).factorization r = (Nat.card OM).factorization r :=
      Nat.pow_right_injective hr.two_le h1
    rw [← hV₀card, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply] at h2
    have hpos := hr.factorization_pos_of_dvd (Nat.card_pos (α := V₀)).ne' hrV
    omega
  have hV₀rel : V₀.relIndex OM = Nat.card X := by
    have h1 := Subgroup.relIndex_mul_card V₀ OM
    rw [inf_eq_left.mpr hV₀O, ← hV₀card] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := V₀))
    rw [h1]
    ring
  have hV₀cop' : Nat.Coprime (Nat.card V₀) (V₀.relIndex OM) := by
    rw [hV₀rel]
    exact hV₀cop
  have hMV₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem (conj_mem_of_coprime_relIndex hV₀O hOV₀ hV₀cop'
      (le_normalizer_map_pPrimeCore M hg))
  have hRO : R ≤ OM := hle_OM R Subgroup.le_normalizer (odd_card_of_isPGroup h.odd hR)
  have hpX : Nat.Coprime p (Nat.card X) := by
    rw [hXcard]
    exact Nat.Coprime.pow_right 2 hpb
  have hRV₀ : R ≤ V₀ := le_of_coprime_relIndex hV₀O hOV₀ hRO (by
    rw [hV₀rel]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    rw [hk]
    exact Nat.Coprime.pow_left k hpX)
  have hYN : Y ≤ Subgroup.normalizer (B : Set G) := fun y hy =>
    mem_normalizer_of_conj_mem (fun x hx => hL.B_conj y (hY hy).1 x hx)
  have hYBcard : Nat.card (Y ⊔ B : Subgroup G) = 2 ^ 3 * Nat.card B * Nat.card B := by
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B Y hYN
      hYB.symm, hYcard, show 2 * (p ^ f - 1) = 2 ^ 3 * Nat.card B by omega]
    ring
  have hV₀odd : Odd (Nat.card V₀) := Odd.of_dvd_nat hOModd (Subgroup.card_dvd_of_le hV₀O)
  have hcopA : Nat.Coprime (Nat.card (Y ⊔ B : Subgroup G)) (Nat.card V₀) := by
    rw [hYBcard]
    have hb : Nat.Coprime (Nat.card B) (Nat.card V₀) := by
      have h1 := hV₀cop.symm
      rw [hXcard] at h1
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self _ two_ne_zero) h1
    have h8 : Nat.Coprime (2 ^ 3) (Nat.card V₀) :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hV₀odd)
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨h8, hb⟩, hb⟩
  obtain ⟨R₀, hR₀, hRR₀, hAR₀⟩ := exists_isSylowOf_invariant ((sup_le hYM hBM).trans hMV₀)
    hV₀odd hcopA hRV₀ hR hRinv
  have hR₀R : R₀ = R := hRmax R₀ hR₀.isPGroup hAR₀ hRR₀
  rw [hR₀R] at hR₀
  have hRM : IsSylowOf p R M := by
    rw [isSylowOf_iff]
    refine ⟨Subgroup.le_normalizer, hR, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex R OM M hRO hOMM,
      ← Subgroup.relIndex_mul_relIndex R V₀ OM hRV₀ hV₀O, hV₀rel]
    intro hdvd
    rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with hdvd | hdvd
    · rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with hdvd | hdvd
      · exact (isSylowOf_iff.mp hR₀).2.2 hdvd
      · exact (Nat.Prime.coprime_iff_not_dvd h.prime).mp hpX hdvd
    · exact not_dvd_relIndex_map_pPrimeCore h.odd hM2 hdvd
  exact exists_sylow_eq_of_isSylowOf_normalizer hRM

theorem exists_layer_sylow (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) :
    ∃ R Q₁ Y O : Subgroup G, (∃ T : Sylow p G, (T : Subgroup G) = R) ∧
      IsSylowOf p Q₁ (C t) ∧ Q₁ ≤ R ∧ O ≤ Y ∧
      Y ⊔ (N t).map (C t).subtype ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G) =
        Nat.card ((N t).map (C t).subtype) ^ 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hL := h.localData
  obtain ⟨Q₁, hQ₁⟩ := exists_isSylowOf p (C t)
  obtain ⟨Y, O, hY, hYcyc, hYcard, htY, hYB, -, hOY, -, -, hOB, hXcard, hXnorm⟩ :=
    hI.exists_layer_torus he hQ₁
  obtain ⟨-, hQ₁J, -⟩ := hI.sylow_C_facts hQ₁
  have hBQ₁ : (N t).map (C t).subtype ≤ Subgroup.normalizer (Q₁ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem (fun y hy => by
      rw [← hL.JB_comm y (hQ₁J hy) x hx, mul_inv_cancel_right]
      exact hy)
  have hQ₁inv : Y ⊔ (N t).map (C t).subtype ≤ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le (hY.trans inf_le_right) hBQ₁
  obtain ⟨R, hQ₁R, hRmax⟩ := Finite.exists_le_maximal (α := Subgroup G)
    (p := fun R' => IsPGroup p R' ∧
      Y ⊔ (N t).map (C t).subtype ≤ Subgroup.normalizer (R' : Set G))
    ⟨hQ₁.isPGroup, hQ₁inv⟩
  obtain ⟨hR, hRinv⟩ := hRmax.prop
  exact ⟨R, Q₁, Y, O, hI.layer_sylow_of_maximal h he hQ₁ hY hYcyc hYcard htY hYB hOY hOB hXcard
    hXnorm hQ₁R hR hRinv (fun R' hR' hR'inv hRR' => (hRmax.eq_of_le ⟨hR', hR'inv⟩ hRR').symm),
    hQ₁, hQ₁R, hOY, hRinv, hXcard⟩

end PositiveInputs

end CFSG.Semidihedral.FixedCoreNontrivial
