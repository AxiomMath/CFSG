module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Transfer
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.BarAux
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ShortBlockCommutator

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM barM_mono odd_card_center_barM_sup)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomOf barMEquiv)

@[expose] def A7PerfectSylow : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (Λ : Subgroup B), CFSG.Open.IsQuasisimple ↥Λ →
    Odd (Nat.card (Subgroup.center ↥Λ)) →
    Nonempty (↥Λ ⧸ Subgroup.center ↥Λ ≃* alternatingGroup (Fin 7)) →
    ∀ P : Subgroup B, IsTwoRadicalIn Λ P →
      ∃ H : Subgroup B, H ≤ Λ ∧ ⁅H, H⁆ = H ∧ P ≤ H ∧
        ¬ 2 ∣ (P.subgroupOf H).index ∧
        (∀ T : Subgroup B, T ≤ H ⊓ Subgroup.normalizer (P : Set B) → IsPGroup 2 T → T ≤ P) ∧
        Odd (Nat.card (Subgroup.center ↥H)) ∧ CFSG.Open.IsQuasisimple ↥H

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem eq_bot_of_normal_isPGroup {B : Type*} [Group B] [Finite B] {H T : Subgroup B}
    (hHq : CFSG.Open.IsQuasisimple ↥H) (hodd : Odd (Nat.card (Subgroup.center ↥H)))
    (hH0 : H ≠ ⊥) (hTH : T ≤ H) (hTn : (T.subgroupOf H).Normal) (hT2 : IsPGroup 2 T) :
    T = ⊥ := by
  rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top hHq.1
    hHq.2 (T.subgroupOf H) hTn with hc | htop
  · rw [eq_bot_iff]
    intro t ht
    have hz : (⟨t, hTH ht⟩ : ↥H) ∈ Subgroup.center ↥H := hc (Subgroup.mem_subgroupOf.2 ht)
    obtain ⟨e, he⟩ := hT2 ⟨t, ht⟩
    have he0 : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have he' : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ e = 1 := Subtype.ext (by simpa using he0)
    have h1 : orderOf (⟨⟨t, hTH ht⟩, hz⟩ : Subgroup.center ↥H) ∣ Nat.card (Subgroup.center ↥H) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨⟨t, hTH ht⟩, hz⟩ : Subgroup.center ↥H) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using he'
    have h3 : Nat.Coprime (orderOf (⟨⟨t, hTH ht⟩, hz⟩ : Subgroup.center ↥H)) (2 ^ e) :=
      Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr (hodd.of_dvd_nat h1))
    have h4 := Nat.Coprime.eq_one_of_dvd h3 h2
    rw [orderOf_eq_one_iff] at h4
    have := congrArg (fun z : Subgroup.center ↥H => ((z : ↥H) : B)) h4
    simpa using this
  · exfalso
    apply hH0
    have hHT : H ≤ T := fun x hx => by
      have : (⟨x, hx⟩ : ↥H) ∈ T.subgroupOf H := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    have hH2 : IsPGroup 2 H := hT2.to_le hHT
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥H := hH2.isNilpotent
    have : Group.IsPerfect ↥H := ⟨hHq.1⟩
    have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
      (G := ↥H)
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥H) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h1

theorem exists_minimal_lift {M L : Subgroup G} (hLM : L ≤ M)
    (hQL : pCoreOf 2 M ≤ Subgroup.normalizer (L : Set G))
    {H : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hHΛ : H ≤ barM M L) (hHperf : ⁅H, H⁆ = H) :
    ∃ K : Subgroup G, K ≤ L ∧ pCoreOf 2 M ≤ Subgroup.normalizer (K : Set G) ∧ barM M K = H ∧
      ⁅K, K⁆ = K := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  set P₀ : Subgroup G → Prop := fun K => K ≤ L ∧ Q ≤ Subgroup.normalizer (K : Set G) ∧ barM M K = H
    with hP₀
  set K₀ : Subgroup G := (H.comap (barMHomOf hLM)).map L.subtype with hK₀
  have hK₀mem : ∀ x : G, x ∈ K₀ ↔ ∃ hx : x ∈ L, barMHomOf hLM ⟨x, hx⟩ ∈ H := by
    intro x
    simp only [hK₀, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, hl⟩
    · rintro ⟨hx, h⟩; exact ⟨⟨x, hx⟩, h, rfl⟩
  have hK₀L : K₀ ≤ L := fun x hx => ((hK₀mem x).1 hx).1
  have hK₀H : barM M K₀ = H := by
    apply le_antisymm
    · intro y hy
      obtain ⟨m, hm, rfl⟩ := (mem_barM y).1 hy
      obtain ⟨hmL, h⟩ := (hK₀mem m).1 hm
      exact h
    · intro y hy
      obtain ⟨m, hm, rfl⟩ := (mem_barM y).1 (hHΛ hy)
      refine (mem_barM _).2 ⟨m, (hK₀mem m).2 ⟨hm, hy⟩, rfl⟩
  have hK₀Q : Q ≤ Subgroup.normalizer (K₀ : Set G) := by
    have key : ∀ q ∈ Q, ∀ k ∈ K₀, q * k * q⁻¹ ∈ K₀ := by
      intro q hq k hk
      obtain ⟨hkL, hkH⟩ := (hK₀mem k).1 hk
      have hqk : q * k * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hQL hq) k).mp hkL
      refine (hK₀mem _).2 ⟨hqk, ?_⟩
      have hqM' : q ∈ M := hQM hq
      have h1 : (QuotientGroup.mk (⟨q, hqM'⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (mem_pCore_of_coe_mem hq)
      have : barMHomOf hLM ⟨q * k * q⁻¹, hqk⟩ = barMHomOf hLM ⟨k, hkL⟩ := by
        show (QuotientGroup.mk (⟨q * k * q⁻¹, _⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) = QuotientGroup.mk ⟨k, _⟩
        have e : (⟨q * k * q⁻¹, hLM hqk⟩ : ↥M) = ⟨q, hqM'⟩ * ⟨k, hLM hkL⟩ * ⟨q, hqM'⟩⁻¹ := rfl
        rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
        simp
      rw [this]; exact hkH
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨fun hk => key q hq k hk, fun hk => by
      have := key q⁻¹ (Q.inv_mem hq) _ hk
      simpa [mul_assoc] using this⟩
  obtain ⟨K, hK, hmin⟩ := exists_minimal_subgroup P₀ ⟨K₀, hK₀L, hK₀Q, hK₀H⟩
  obtain ⟨hKL, hKQ, hKH⟩ := hK
  refine ⟨K, hKL, hKQ, hKH, ?_⟩
  have hcc : ⁅K, K⁆ ≤ K := commutator_le_of_le (le_refl K) (le_refl K)
  refine le_antisymm hcc ?_
  have := hmin ⁅K, K⁆ ⟨hcc.trans hKL, le_normalizer_commutator' hKQ hKQ, by
    rw [barM_commutator (hKL.trans hLM) (hKL.trans hLM), hKH, hHperf]⟩ hcc
  exact this.ge

theorem pCoreOf_sup_pCoreOf_eq {M K : Subgroup G} (hKM : K ≤ M)
    {H : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hKH : barM M K = H)
    (hHq : CFSG.Open.IsQuasisimple ↥H) (hodd : Odd (Nat.card (Subgroup.center ↥H)))
    (hH0 : H ≠ ⊥) : pCoreOf 2 (K ⊔ pCoreOf 2 M) = pCoreOf 2 M := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set X₁ : Subgroup G := K ⊔ Q with hX₁
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQX₁ : Q ≤ X₁ := le_sup_right
  have hX₁M : X₁ ≤ M := sup_le hKM hQM
  have hKQ' : K ≤ Subgroup.normalizer (Q : Set G) := fun k hk => hMQ (hKM hk)
  have hbarX₁ : barM M X₁ = H := by
    rw [hX₁, barM_sup_pCoreOf hKQ']; exact hKH
  apply le_antisymm
  · set T : Subgroup G := pCoreOf 2 X₁ with hT
    have hTX₁ : T ≤ X₁ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X₁
    have hTM : T ≤ M := hTX₁.trans hX₁M
    have hTH : barM M T ≤ H := hbarX₁ ▸ barM_mono hTX₁
    have hT2 : IsPGroup 2 (barM M T) :=
      barM_isPGroup hTM (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X₁)
    have hTn : ((barM M T).subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : ((n : ↥H) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M T := Subgroup.mem_subgroupOf.mp hn
      obtain ⟨⟨t, htM⟩, ht, hnt⟩ := (mem_barM _).1 hn'
      have ht' : t ∈ T := ht
      have hg : ((g : ↥H) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M X₁ := hbarX₁ ▸ g.2
      obtain ⟨⟨x, hxM⟩, hx, hgx⟩ := (mem_barM _).1 hg
      have hx' : x ∈ X₁ := hx
      have hconj : (⟨x, hx'⟩ : ↥X₁) * ⟨t, hTX₁ ht'⟩ * (⟨x, hx'⟩ : ↥X₁)⁻¹ ∈
          T.subgroupOf X₁ :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 X₁).conj_mem ⟨t, hTX₁ ht'⟩ ht'
          ⟨x, hx'⟩
      have hc' : x * t * x⁻¹ ∈ T := Subgroup.mem_subgroupOf.mp hconj
      rw [Subgroup.mem_subgroupOf]
      show ((g : ↥H) : ↥M ⧸ CFSG.pCore 2 ↥M) * ((n : ↥H) : ↥M ⧸ CFSG.pCore 2 ↥M) *
        ((g : ↥H) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ ∈ barM M T
      rw [← hgx, ← hnt]
      refine (mem_barM _).2 ⟨⟨x, hxM⟩ * ⟨t, htM⟩ * ⟨x, hxM⟩⁻¹, hc', ?_⟩
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hT0 : barM M T = ⊥ := eq_bot_of_normal_isPGroup hHq hodd hH0 hTH hTn hT2
    intro t ht
    have htM : t ∈ M := hTM ht
    have h1 : (QuotientGroup.mk (⟨t, htM⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M T :=
      (mem_barM _).2 ⟨⟨t, htM⟩, ht, rfl⟩
    rw [hT0, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact coe_mem_pCoreOf h1
  · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q X₁ hQX₁
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQX₁).mpr (hX₁M.trans hMQ))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)

theorem exists_block_of_perfectSylow (hclass : A7PerfectSylow)
    (h85 : Asc81bEightFive) (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L)
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹)
    (he : Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin 7))) :
    ∃ L₁ : Subgroup G, L₁ ≤ L ∧ ⁅L₁, L₁⁆ = L₁ ∧
      pCoreOf 2 (L ⊔ S) ≤ Subgroup.normalizer (L₁ : Set G) ∧
      L₁ ⊓ pCoreOf 2 (L ⊔ S) = pCoreOf 2 L₁ ∧ IsShort2 L₁ ∧
      ¬ barM (L ⊔ S) L₁ ≤ (Subgroup.center ↥(barM (L ⊔ S) L)).map (barM (L ⊔ S) L).subtype := by
  classical
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  set M : Subgroup G := L ⊔ S with hM
  set Q : Subgroup G := pCoreOf 2 M with hQ
  have hLs : IsTwoPrimeComponent M L :=
    Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp M S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hLM : L ≤ M := le_sup_left
  have hSM : S ≤ M := le_sup_right
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hQS : Q ≤ S := hA'.twoCore_le
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) := hQS.trans hSL
  have hSQ : S ≤ L ⊔ Q := le_sup_pCoreOf_of_acts hX hA hL hact
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hrad := isTwoRadicalIn_barM hA' hSL hSQ hL.not_le_normalizer
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hLs.component.2.2
  have hoddZ : Odd (Nat.card (Subgroup.center ↥(barM M L))) := odd_card_center_barM_sup hA' hSL
  obtain ⟨H, hHΛ, hHperf, hPH, hodd1, hodd2, hoddH, hHq⟩ :=
    hclass _ (barM M L) hq hoddZ he (barM M S) hrad
  have hP0 : barM M S ≠ ⊥ := hrad.2.1
  have hH0 : H ≠ ⊥ := fun h => hP0 (le_bot_iff.mp (h ▸ hPH))
  obtain ⟨K, hKL, hKQ, hKH, hKperf⟩ := exists_minimal_lift hLM hQL hHΛ hHperf
  have hKM : K ≤ M := hKL.trans hLM
  have hKQ' : K ≤ Subgroup.normalizer (Q : Set G) := fun k hk => hMQ (hKM hk)
  set X₁ : Subgroup G := K ⊔ Q with hX₁
  have hQX₁ : Q ≤ X₁ := le_sup_right
  have hKX₁ : K ≤ X₁ := le_sup_left
  have hX₁M : X₁ ≤ M := sup_le hKM hQM
  have hX₁X : X₁ ≤ X := hX₁M.trans (sup_le hL.le hA.twoRadical.1)
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hKQ
  have hbarX₁ : barM M X₁ = H := by
    rw [hX₁, barM_sup_pCoreOf hKQ']; exact hKH
  have hpc : pCoreOf 2 X₁ = Q := pCoreOf_sup_pCoreOf_eq hKM hKH hHq hoddH hH0
  have hKG : CFSG.Open.IsKGroup ↥X₁ := hX.of_le hX₁X
  have hKn : (K.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX₁).mpr hX₁N
  have hbarKn : (barM X₁ K).Normal := normal_barM_of_le_normalizer hX₁N
  have hqK : CFSG.Open.IsQuasisimple ↥(barM X₁ K) :=
    Proving.isQuasisimple_of_mulEquiv'
      ((MulEquiv.subgroupCongr hKH.symm).trans
        (barMEquiv hKX₁ hKM (by rw [hpc])).symm) hHq
  have hTP : IsTwoPrimeComponent X₁ K :=
    { le := hKX₁
      subnormal := CFSG.Open.IsSubnormal.step hKX₁ hKn (CFSG.Open.IsSubnormal.refl _)
      perfect := hKperf
      component := ⟨le_top, CFSG.Open.IsSubnormal.step le_top
        (by have := hbarKn; exact inferInstance) (CFSG.Open.IsSubnormal.refl _), hqK⟩ }
  have hmemX₁ : ∀ s ∈ S, s ∈ X₁ := by
    intro s hs
    have h1 : (QuotientGroup.mk (⟨s, hSM hs⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M X₁ := by
      rw [hbarX₁]; exact hPH ((mem_barM _).2 ⟨⟨s, hSM hs⟩, hs, rfl⟩)
    obtain ⟨⟨x, hxM⟩, hx, hxs⟩ := (mem_barM _).1 h1
    have hker : (⟨x, hxM⟩ : ↥M)⁻¹ * ⟨s, hSM hs⟩ ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]; exact hxs
    have hq1 := coe_mem_pCoreOf hker
    have e : s = x * (((⟨x, hxM⟩ : ↥M)⁻¹ * ⟨s, hSM hs⟩ : ↥M) : G) := by simp
    rw [e]
    exact X₁.mul_mem hx (hQX₁ hq1)
  have hrad1 : IsTwoRadicalIn X₁ S := by
    refine isTwoRadicalIn_iff.mpr ⟨hmemX₁, hA'.twoRadical.2.1, hS2, fun T hT hT2 _ => ?_⟩
    have hTM : T ≤ M := (hT.trans inf_le_left).trans hX₁M
    have hTH : barM M T ≤ H := hbarX₁ ▸ barM_mono (hT.trans inf_le_left)
    have hTN : barM M T ≤ Subgroup.normalizer ((barM M S : Subgroup _) : Set _) := by
      intro y hy
      obtain ⟨⟨t, htM⟩, ht, rfl⟩ := (mem_barM y).1 hy
      exact mk_mem_normalizer_barM ⟨t, htM⟩ ((hT ht).2)
    have h1 : barM M T ≤ barM M S :=
      hodd2 _ (le_inf hTH hTN) (barM_isPGroup hTM hT2)
    intro t ht
    have htM : t ∈ M := hTM ht
    have h2 := h1 ((mem_barM _).2 ⟨⟨t, htM⟩, ht, rfl⟩)
    obtain ⟨⟨s, hsM⟩, hs, hst⟩ := (mem_barM _).1 h2
    have hker : (⟨s, hsM⟩ : ↥M)⁻¹ * ⟨t, htM⟩ ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]; exact hst
    have hq1 := coe_mem_pCoreOf hker
    have e : t = s * (((⟨s, hsM⟩ : ↥M)⁻¹ * ⟨t, htM⟩ : ↥M) : G) := by simp
    rw [e]
    exact S.mul_mem hs (hQS hq1)
  have hAhyp : Asc81bHyp X₁ S :=
    ⟨hrad1, charTwo_of_twoCore_le hA'.charTwo hQX₁ hX₁M, cgsIn_eq_of_le hA' hX₁M⟩
  have hSyl : IsSylowTwoOf (S ⊓ K) K := by
    refine ⟨inf_le_right, hS2.to_le inf_le_left, ?_⟩
    let φ₀ : ↥K →* ↥M ⧸ CFSG.pCore 2 ↥M := barMHomOf hKM
    have hφH : ∀ k : ↥K, φ₀ k ∈ H := fun k => hKH ▸ (mem_barM _).2 ⟨⟨k.1, hKM k.2⟩, k.2, rfl⟩
    let φ : ↥K →* ↥H := φ₀.codRestrict H hφH
    have hφsurj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨m, hm, rfl⟩ := (mem_barM y).1 (hKH ▸ hy)
      exact ⟨⟨m, hm⟩, Subtype.ext rfl⟩
    have heq : (S ⊓ K).subgroupOf K = (barM M S |>.subgroupOf H).comap φ := by
      ext k
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
      constructor
      · rintro ⟨hkS, -⟩
        exact (mem_barM _).2 ⟨⟨k.1, hKM k.2⟩, hkS, rfl⟩
      · intro h
        obtain ⟨⟨s, hsM⟩, hs, hsk⟩ := (mem_barM _).1 h
        have hker : (⟨s, hsM⟩ : ↥M)⁻¹ * ⟨k.1, hKM k.2⟩ ∈ CFSG.pCore 2 ↥M := by
          rw [← QuotientGroup.eq]; exact hsk
        have hq1 := coe_mem_pCoreOf hker
        have e : (k : G) = s * (((⟨s, hsM⟩ : ↥M)⁻¹ * ⟨k.1, hKM k.2⟩ : ↥M) : G) := by simp
        refine ⟨?_, k.2⟩
        rw [e]
        exact S.mul_mem hs (hQS hq1)
    rw [heq, Subgroup.index_comap_of_surjective _ hφsurj]
    exact hodd1
  have hshort : IsShort2 K := (h85 G X₁ S K hKG hAhyp hTP hSyl).1
  refine ⟨K, hKL, hKperf, hKQ, ?_, hshort, ?_⟩
  · have := hTP.inf_twoCore
    rwa [hpc] at this
  · intro hcen
    apply hH0
    have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
      intro a ha b hb
      have haK : a ∈ barM M K := hKH ▸ ha
      obtain ⟨z, hz, rfl⟩ := hcen haK
      have hbΛ : b ∈ barM M L := hHΛ hb
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hbΛ⟩)).symm
    rw [eq_bot_iff, ← hHperf, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, hcomm a ha b hb]
    simp

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
