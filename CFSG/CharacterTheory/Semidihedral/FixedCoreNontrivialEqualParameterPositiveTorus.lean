module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumBasic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff exists_isSylowOf)
open _root_.CFSG.Semidihedral.FixedCoreNontrivial.Positive

namespace Positive

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem clause_facts (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    torusW G t s₀ ≤ C t ∧ (N t).map (C t).subtype ≤ torusH G t s₀ ∧ d ∈ torusH G t s₀ ∧
      orderOf d = 4 ∧ d ^ 2 = t ∧ s₀ * d * s₀⁻¹ = d⁻¹ ∧
      ∃ P : Sylow 2 (torusH G t s₀),
        (P : Subgroup (torusH G t s₀)).map (torusH G t s₀).subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ := by
  obtain ⟨-, -, hVW, -, hBK, -, -, -, -, -, -, -, -, hd4, hd2, hds, hdW, -, hsylH, -⟩ :=
    h.clauses
  have hL := h.localData
  refine ⟨?_, hBK.trans (Subgroup.centralizer_le_normalizer _),
    LocalData.mem_normalizer_of_inv (W := torusW G t s₀) _ le_rfl hdW, hd4, hd2, ?_, hsylH⟩
  · intro w hw
    have hwD : w ∈ Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
      rw [← hVW]
      exact Subgroup.mem_sup_right hw
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))) hwD
  · have h4 : d ^ 4 = 1 := by
      rw [← hd4]
      exact pow_orderOf_eq_one d
    have hd3 : t * d = d⁻¹ := by
      rw [← hd2]
      apply eq_inv_of_mul_eq_one_left
      rw [← h4]
      group
    have hds' : d * s₀ = t * s₀ * d := by
      rw [← hds]
      group
    calc s₀ * d * s₀⁻¹ = s₀ * (d * s₀) := by rw [hL.s_inv_eq]; group
      _ = s₀ * (t * s₀ * d) := by rw [hds']
      _ = (s₀ * t) * s₀ * d := by group
      _ = t * (s₀ * s₀) * d := by rw [← hL.ts]; group
      _ = t * d := by rw [hL.s_sq, mul_one]
      _ = d⁻¹ := hd3

theorem card_dihedral_le (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) :
    Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≤ 8 := by
  obtain ⟨-, -, -, hd4, -, hsd, -⟩ := clause_facts h
  have hL := h.localData
  have hsN : Subgroup.zpowers s₀ ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsd]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers d)) k
  have hs2 : orderOf s₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hL.s_sq) hL.s_ne_one
  calc Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G)
      ≤ Nat.card (Subgroup.zpowers d) * Nat.card (Subgroup.zpowers s₀) :=
        card_sup_le_of_le_normalizer hsN
    _ = 8 := by rw [Nat.card_zpowers, Nat.card_zpowers, hd4, hs2]

end Positive

namespace PositiveInputs

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem not_kleinFour_le_normalizer (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) :
    ∀ T : Subgroup G, T ≤ Subgroup.normalizer (Q : Set G) → ¬ IsKleinFour T :=
  fun _ hT hT4 => hI.not_le_normalizer_of_isKleinFour h he hQ hQ1 hT4 hT

theorem torus_inv (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hWQ : torusW G t s₀ ≤ Subgroup.normalizer (Q : Set G))
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) :
    (∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) ∧ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hWC, -⟩ := clause_facts h
  have hQC : Q ⊓ C t = ⊥ := by
    apply (hI.eq_bot_of_mod_four_eq_one he).1 _ inf_le_right hQ.to_inf_left
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hWQ hw) y)
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hWC hw)) y)
  exact hI.conj_eq_inv_of_inf_centralizer_eq_bot (odd_card_of_isPGroup h.odd hQ)
    h.localData.t_sq htQ hQC

theorem sl2_neg_one_eq (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {F₀ : Type}
    [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = p ^ f)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F₀) : (e.symm (-1) : G) = t := by
  have hmem : (e.symm (-1) : G) ∈ J := (e.symm (-1)).2
  have hsq : (e.symm (-1) : G) * (e.symm (-1) : G) = 1 := by
    have : e.symm (-1) * e.symm (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    exact congrArg Subtype.val this
  rcases h.localData.J_inv _ hmem hsq with h1 | h1
  · exfalso
    have hodd : Odd (Nat.card F₀) := by
      rw [hF₀]
      exact h.odd.pow
    apply sl2_neg_one_ne_one hodd
    have h2 : e.symm (-1) = e.symm 1 := by
      rw [map_one]
      exact Subtype.ext h1
    exact e.symm.injective h2
  · exact h1

theorem torus_normalizer_two_complement (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥)
    (hWQ : torusW G t s₀ ≤ Subgroup.normalizer (Q : Set G))
    (hBQ : (N t).map (C t).subtype ≤ Subgroup.normalizer (Q : Set G))
    (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    (hinv : ∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    IsPGroup 2 (Subgroup.normalizer (Q : Set G) ⧸
        CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))) ∧
      ∀ x ∈ Subgroup.normalizer (Q : Set G), Odd (orderOf x) →
        x ∈ (CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWC, -, -, hd4, hd2, -, P₂, hP₂⟩ := clause_facts h
  have hL := h.localData
  set Fq := Subgroup.normalizer (Q : Set G) with hFq
  have hno4 := hI.not_kleinFour_le_normalizer h he hQ hQ1
  have htd : t ∈ Subgroup.zpowers d := by
    rw [← hd2]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) 2
  have htF : t ∈ Fq := (Subgroup.zpowers_le.mpr hdQ) htd
  have hdgrp : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hd4]; norm_num)
  obtain ⟨S, hS, hdS⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hdQ) hdgrp
  have hSt : S ≤ C t := hI.le_centralizer_of_isPGroup_two_of_no_kleinFour hS.isPGroup
    (fun T hT => hno4 T (hT.trans hS.le)) (hdS htd) hL.t_orderOf
  by_cases hcyc : IsCyclic S
  · obtain ⟨S', hS'⟩ := exists_sylow_isCyclic hS hcyc
    exact hI.odd_mem_pPrimeCore_of_isCyclic_sylow S' hS'
  · exfalso
    have hS8 : 8 ≤ Nat.card S := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.isPGroup
      have h4 : 4 ∣ 2 ^ n := by
        rw [← hn, ← hd4, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le hdS
      have hne : 2 ^ n ≠ 4 := by
        intro h4'
        apply hcyc
        have hcard : Nat.card S ≤ Nat.card (Subgroup.zpowers d) := by
          rw [hn, h4', Nat.card_zpowers, hd4]
        rw [← Subgroup.eq_of_le_of_card_ge hdS hcard]
        exact Subgroup.isCyclic_of_le le_rfl
      rw [hn]
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · interval_cases n <;> simp_all
      · calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have hnot : ¬ Fq ⊓ C t ≤ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) := by
      intro hle
      have hSH : S ≤ torusH G t s₀ := (le_inf hS.le hSt).trans hle
      obtain ⟨k, -, hSk⟩ := exists_le_conj_of_sylow P₂ hSH hS.isPGroup
      rw [hP₂] at hSk
      have hcard : Nat.card ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G).map
          (MulAut.conj k).toMonoidHom) ≤ Nat.card S := by
        rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
        exact (card_dihedral_le h).trans hS8
      have heq := Subgroup.eq_of_le_of_card_ge hSk hcard
      have hkt : k * t * k⁻¹ ∈ S := by
        rw [heq, mem_map_conj_iff]
        have : k⁻¹ * (k * t * k⁻¹) * k = t := by group
        rw [this, ← hd2]
        exact Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) 2
      have hks : k * s₀ * k⁻¹ ∈ S := by
        rw [heq, mem_map_conj_iff]
        have : k⁻¹ * (k * s₀ * k⁻¹) * k = s₀ := by group
        rw [this]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
      obtain ⟨T, hTS, hT⟩ := exists_kleinFour_le_of_conj hL.t_sq hL.t_ne_one hL.s_sq
        hL.s_ne_one hL.s_ne.symm hL.ts k hkt hks
      exact hno4 T (hTS.trans hS.le) hT
    have hJ : J ≤ Fq ⊓ C t := hI.layer_le_of_not_le_normalizer he inf_le_right
      (le_inf hWQ hWC) (le_inf hBQ (Subgroup.map_subtype_le _))
      ⟨htF, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ hnot
    obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := h.sl2
    have hsq := hI.sq_dvd_card_of_sl2_inverting h.prime h.odd h.one_le hF₀
      (by have := h.q_gt; omega) J Q e hQ hcomm (hJ.trans inf_le_left)
      (by rw [sl2_neg_one_eq h hF₀ e]; exact hinv) hQ1
    have hdisj : Disjoint Q J := by
      rw [Subgroup.disjoint_def]
      intro x hxQ hxJ
      have h1 : t * x * t⁻¹ = x := by rw [hL.t_comm_J x hxJ, mul_inv_cancel_right]
      have h2 : x * x = 1 := by
        have := hinv x hxQ
        rw [h1] at this
        calc x * x = x * x⁻¹ := by rw [← this]
          _ = 1 := mul_inv_cancel x
      exact eq_one_of_mul_self_eq_one_of_odd
        (odd_orderOf_of_mem (odd_card_of_isPGroup h.odd hQ) hxQ) h2
    have hcardQJ := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q J
      (hJ.trans inf_le_left) hdisj
    obtain ⟨Q₁, hQ₁⟩ := exists_isSylowOf p (C t)
    obtain ⟨hQ₁card, hQ₁J, -⟩ := hI.sylow_C_facts hQ₁
    have hqJ : p ^ f ∣ Nat.card J := hQ₁card ▸ Subgroup.card_dvd_of_le hQ₁J
    apply h.not_cube
    calc (p ^ f) ^ 3 = (p ^ f) ^ 2 * p ^ f := by ring
      _ ∣ Nat.card Q * Nat.card J := mul_dvd_mul hsq hqJ
      _ = Nat.card (Q ⊔ J : Subgroup G) := hcardQJ.symm
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _

theorem torus_sylow_of_maximal (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {P Q : Subgroup G} (hPH : IsSylowOf p P (torusH G t s₀)) (hPcard : Nat.card P = p ^ f)
    (hPWBcard : Nat.card (P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
      p ^ f * Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype))
    (hPWBmax : ∀ X : Subgroup G, X ≤ torusH G t s₀ → Odd (Nat.card X) →
      P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ≤ X →
        X = P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype)
    (hPQ : P ≤ Q) (hQ : IsPGroup p Q)
    (hQinv : torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤
      Subgroup.normalizer (Q : Set G))
    (hQmax : ∀ Q' : Subgroup G, IsPGroup p Q' →
      torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤
        Subgroup.normalizer (Q' : Set G) → Q ≤ Q' → Q' = Q) :
    (∃ T : Sylow p G, (T : Subgroup G) = Q) ∧
      (∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) ∧
      IsPGroup 2 (Subgroup.normalizer (Q : Set G) ⧸
        CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))) ∧
      (∀ x ∈ Subgroup.normalizer (Q : Set G), Odd (orderOf x) →
        x ∈ (CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype) ∧
      (N t).map (C t).subtype ≤ (CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype ∧
      Nat.Coprime (Nat.card ((N t).map (C t).subtype))
        (((N t).map (C t).subtype).relIndex
          ((CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, hwb, hbodd, -, -, -⟩ := hI.numerics h he
  obtain ⟨hbw, hqw, -, hpw, hpb⟩ := hI.coprimes h he
  obtain ⟨hWC, hBH, -, -, hd2, -, -⟩ := clause_facts h
  set W := torusW G t s₀ with hW
  set B := (N t).map (C t).subtype with hB
  set Fq := Subgroup.normalizer (Q : Set G) with hFq
  set OF := (CFSG.pPrimeCore 2 Fq).map Fq.subtype with hOF
  have hWQ : W ≤ Fq := le_sup_left.trans (le_sup_left.trans hQinv)
  have hBQ : B ≤ Fq := le_sup_right.trans (le_sup_left.trans hQinv)
  have hdQ : d ∈ Fq := (le_sup_right.trans hQinv) (Subgroup.mem_zpowers d)
  have htF : t ∈ Fq := by
    rw [← hd2]
    exact Subgroup.pow_mem _ hdQ 2
  have hQ1 : Q ≠ ⊥ := by
    intro hQb
    have h1 : Nat.card P ≤ 1 := by
      calc Nat.card P ≤ Nat.card Q := Subgroup.card_le_of_le hPQ
        _ = 1 := by rw [hQb, Subgroup.card_bot]
    have h2 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
    omega
  obtain ⟨hinv, hcomm⟩ := hI.torus_inv h he hQ hWQ htF
  obtain ⟨hF2, hFodd⟩ :=
    hI.torus_normalizer_two_complement h he hQ hQ1 hWQ hBQ hdQ hinv hcomm
  have hOFodd : Odd (Nat.card OF) := odd_card_map_pPrimeCore Fq
  have hOFF : OF ≤ Fq := Subgroup.map_subtype_le _
  have hle_OF : ∀ X : Subgroup G, X ≤ Fq → Odd (Nat.card X) → X ≤ OF :=
    fun X hXF hX x hx => hFodd x (hXF hx) (odd_orderOf_of_mem hX hx)
  have hWodd : Odd (Nat.card W) := by
    rw [hwb]
    exact odd_two_mul_add_one _
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact h.odd.pow
  have hPO : P ≤ OF := hle_OF P (hPQ.trans Subgroup.le_normalizer) hPodd
  have hWO : W ≤ OF := hle_OF W hWQ hWodd
  have hBO : B ≤ OF := hle_OF B hBQ hbodd
  have hQO : Q ≤ OF := hle_OF Q Subgroup.le_normalizer (odd_card_of_isPGroup h.odd hQ)
  have hWH : W ≤ torusH G t s₀ := Subgroup.le_normalizer
  have hOH : OF ⊓ torusH G t s₀ = P ⊔ W ⊔ B := hPWBmax _ inf_le_right
    (Odd.of_dvd_nat hOFodd (Subgroup.card_dvd_of_le inf_le_left))
    (le_inf (sup_le (sup_le hPO hWO) hBO) (sup_le (sup_le hPH.le hWH) hBH))
  have hHall : Nat.Coprime (Nat.card W) (W.relIndex (OF ⊓ torusH G t s₀)) := by
    rw [hOH]
    have h1 := Subgroup.relIndex_mul_card W (P ⊔ W ⊔ B)
    rw [inf_eq_left.mpr (le_sup_right.trans le_sup_left : W ≤ P ⊔ W ⊔ B), hPWBcard] at h1
    have h2 : W.relIndex (P ⊔ W ⊔ B) = p ^ f * Nat.card B := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := W))
      rw [h1]
      ring
    rw [h2]
    exact Nat.Coprime.mul_right hqw.symm hbw.symm
  obtain ⟨hWBcard, U, hUO, hOU, hUdisj, -, hUcard, hUcopW⟩ :=
    hI.exists_normal_complement_torus_core OF hOFodd hWO hBO hHall
  have hUodd : Odd (Nat.card U) := Odd.of_dvd_nat hOFodd (Subgroup.card_dvd_of_le hUO)
  have hUC : U ⊓ C t = ⊥ := by
    have hle := (hI.eq_bot_of_mod_four_eq_one he).2.2 (U ⊓ C t) inf_le_right
      (Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left))
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hUcopW)
      (by
        intro w hw
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf]
        exact and_congr (Subgroup.mem_normalizer_iff.mp (hOU (hWO hw)) y)
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hWC hw)) y))
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ U ⊓ (W ⊔ B) := Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_sup_right (hle hx)⟩
    rwa [hUdisj.eq_bot] at hx'
  have hUcopB : Nat.Coprime (Nat.card U) (Nat.card B) := by
    apply Nat.coprime_of_dvd
    intro r hr hrU hrB
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨Br⟩ : Nonempty (Sylow r B) := inferInstance
    obtain ⟨Vr, hVr, hBrV⟩ := exists_isSylowOf_le ((Subgroup.map_subtype_le _).trans hBO)
      (Br.isPGroup'.map B.subtype)
    obtain ⟨hVC, -⟩ := hI.le_C_of_isPGroup hr hrB Br hVr.isPGroup hBrV
    have hVU : IsSylowOf r (Vr ⊓ U) U := hVr.inf_of_le_normalizer hUO hOU
    have hbot : Vr ⊓ U = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ U ⊓ C t := Subgroup.mem_inf.mpr ⟨hx.2, hVC hx.1⟩
      rwa [hUC] at hx'
    have hcard := hVU.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos := hr.factorization_pos_of_dvd Nat.card_pos.ne' hrU
    have : 1 < r ^ (Nat.card U).factorization r := Nat.one_lt_pow hpos.ne' hr.one_lt
    omega
  have hOFcard : Nat.card OF = Nat.card U * (Nat.card W * Nat.card B) := by
    rw [← hUcard, hWBcard]
  have hUrel : U.relIndex OF = Nat.card W * Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card U OF
    rw [inf_eq_left.mpr hUO, hOFcard] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := U))
    rw [h1]
    ring
  have hBrel : B.relIndex OF = Nat.card U * Nat.card W := by
    have h1 := Subgroup.relIndex_mul_card B OF
    rw [inf_eq_left.mpr hBO, hOFcard] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B))
    rw [h1]
    ring
  have hUcop : Nat.Coprime (Nat.card U) (U.relIndex OF) := by
    rw [hUrel]
    exact Nat.Coprime.mul_right hUcopW hUcopB
  have hFU : Fq ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem (conj_mem_of_coprime_relIndex hUO hOU hUcop
      (le_normalizer_map_pPrimeCore Fq hg))
  obtain ⟨-, hUcomm⟩ :=
    hI.conj_eq_inv_of_inf_centralizer_eq_bot hUodd h.localData.t_sq (hFU htF) hUC
  have hQU : Q ≤ U := le_of_coprime_relIndex hUO hOU hQO (by
    rw [hUrel]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right hpw hpb))
  obtain ⟨Q₀, hQ₀, hQQ₀⟩ := exists_isSylowOf_le hQU hQ
  have hQ₀inv : W ⊔ B ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (Q₀ : Set G) := by
    have key : ∀ g ∈ Fq, g ∈ Subgroup.normalizer (Q₀ : Set G) := fun g hg =>
      mem_normalizer_of_isSylowOf_comm hUcomm hQ₀ (hFU hg)
    exact sup_le (sup_le (fun x hx => key x (hWQ hx)) (fun x hx => key x (hBQ hx)))
      (Subgroup.zpowers_le.mpr (key d hdQ))
  have hQ₀Q : Q₀ = Q := hQmax Q₀ hQ₀.isPGroup hQ₀inv hQQ₀
  rw [hQ₀Q] at hQ₀
  have hQF : IsSylowOf p Q Fq := by
    rw [isSylowOf_iff]
    refine ⟨Subgroup.le_normalizer, hQ, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q OF Fq hQO hOFF,
      ← Subgroup.relIndex_mul_relIndex Q U OF hQU hUO, hUrel]
    intro hdvd
    rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with hdvd | hdvd
    · rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with hdvd | hdvd
      · exact (isSylowOf_iff.mp hQ₀).2.2 hdvd
      · exact (Nat.Prime.coprime_iff_not_dvd h.prime).mp (Nat.Coprime.mul_right hpw hpb) hdvd
    · exact not_dvd_relIndex_map_pPrimeCore h.odd hF2 hdvd
  refine ⟨exists_sylow_eq_of_isSylowOf_normalizer hQF, hinv, hF2, hFodd, hBO, ?_⟩
  rw [hBrel]
  exact Nat.Coprime.mul_right hUcopB.symm hbw

theorem exists_torus_sylow (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) :
    ∃ Q : Subgroup G, (∃ T : Sylow p G, (T : Subgroup G) = Q) ∧
      (∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) ∧
      IsPGroup 2 (Subgroup.normalizer (Q : Set G) ⧸
        CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))) ∧
      (∀ x ∈ Subgroup.normalizer (Q : Set G), Odd (orderOf x) →
        x ∈ (CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype) ∧
      (N t).map (C t).subtype ≤ (CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype ∧
      Nat.Coprime (Nat.card ((N t).map (C t).subtype))
        (((N t).map (C t).subtype).relIndex
          ((CFSG.pPrimeCore 2 (Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPH, hBdP, -, -, -, hPWBcard, hPWBmax⟩ := hI.exists_split_torus_sylow he
  obtain ⟨hPcard, hPK, -⟩ := hI.sylow_H_facts hPH
  have hWP : torusW G t s₀ ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp hPK).trans (Subgroup.centralizer_le_normalizer _)
  have hPinv : torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤
      Subgroup.normalizer (P : Set G) :=
    sup_le (sup_le hWP (le_sup_left.trans hBdP)) (le_sup_right.trans hBdP)
  obtain ⟨Q, hPQ, hQmax⟩ := Finite.exists_le_maximal (α := Subgroup G)
    (p := fun Q' => IsPGroup p Q' ∧ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
      Subgroup.zpowers d ≤ Subgroup.normalizer (Q' : Set G))
    ⟨hPH.isPGroup, hPinv⟩
  obtain ⟨hQ, hQinv⟩ := hQmax.prop
  exact ⟨Q, hI.torus_sylow_of_maximal h he hPH hPcard hPWBcard hPWBmax hPQ hQ hQinv
    (fun Q' hQ' hQ'inv hQQ' => (hQmax.eq_of_le ⟨hQ', hQ'inv⟩ hQQ').symm)⟩

end PositiveInputs

end CFSG.Semidihedral.FixedCoreNontrivial
