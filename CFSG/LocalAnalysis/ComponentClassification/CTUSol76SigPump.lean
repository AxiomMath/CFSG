module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigTools
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315a

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_oddCoreIn_of_le_coreActionKernel {J S : Subgroup G}
    (hS : S ≤ coreActionKernel J) : ⁅J, S⁆ ≤ oddCoreIn J := by
  rw [commutator_le]
  intro j hj s hs
  have h := (mem_coreActionKernel.mp (hS (inv_mem hs))).2 j⁻¹ (inv_mem hj)
  rw [inv_inv, inv_inv] at h
  rwa [commutatorElement_def]

theorem commutator_sup_le_of_le {A B V O : Subgroup G} (hBA : B ≤ normalizer (A : Set G))
    (hAO : A ≤ normalizer (O : Set G)) (hBO : B ≤ normalizer (O : Set G))
    (hA : ⁅A, V⁆ ≤ O) (hB : ⁅B, V⁆ ≤ O) : ⁅A ⊔ B, V⁆ ≤ O := by
  rw [commutator_le]
  intro x hx v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_normalizer hBA hx
  have h1 : ⁅a, v⁆ ∈ O := hA (commutator_mem_commutator ha hv)
  have h2 : ⁅b, v⁆ ∈ O := hB (commutator_mem_commutator hb hv)
  have h3 : a * ⁅b, v⁆ * a⁻¹ ∈ O := (mem_normalizer_iff.mp (hAO ha) _).mp h2
  have : ⁅a * b, v⁆ = (a * ⁅b, v⁆ * a⁻¹) * ⁅a, v⁆ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem h3 h1

theorem odd_card_sup_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ normalizer (A : Set G)) (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup G)) := by
  rw [sup_comm]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hBA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hBA
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (B ⊔ A)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ B ⊔ A)).toEquiv]
  exact (Odd.of_dvd_nat hB (Subgroup.card_quotient_dvd_card _)).mul hA

variable [Finite G]

theorem oddCoreIn_le_of_le_normalizer {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) : oddCoreIn N ≤ oddCoreIn X := by
  have hX : X ≤ normalizer (oddCoreIn N : Set G) := fun x hx =>
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hXN hx))
  have h := inf_le_oddCoreIn (coprime_card_oddCoreIn N) hX
  have h1 : oddCoreIn N ≤ X := (map_subtype_le _).trans hNX
  rwa [inf_eq_left.mpr h1] at h

theorem oddCoreIn_le_of_isTwoComponentIn {M C : Subgroup G} (hM : IsTwoComponentIn M C) :
    oddCoreIn M ≤ oddCoreIn C :=
  GrSLit.Sol25.oddIn_le_of_isPComponent hM.1 hM.2

theorem le_normalizer_oddCoreIn_twoLayerIn (C : Subgroup G) :
    C ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) := fun _ hc =>
  mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer_twoLayerIn C hc))

section Pump

variable {N K : Subgroup G} {u : G}

theorem mem_pump_of_two (hK : K ∈ kStarComponents N) (huQ : u ∈ coreActionKernel K)
    (hu2 : orderOf u = 2) {x : G} (hx : x ∈ K ⊓ centralizer ({u} : Set G)) {k : ℕ}
    (hk : orderOf x = 2 ^ k) : x ∈ twoLayerIn (K ⊓ centralizer ({u} : Set G)) := by
  set Y := K ⊓ centralizer ({u} : Set G) with hY
  obtain ⟨hKu2, hsup, -⟩ := pump_facts hK huQ hu2
  have hKuK : twoLayerIn Y ≤ K := hKu2.1.trans inf_le_left
  have hKuO : twoLayerIn Y ≤ normalizer (oddCoreIn K : Set G) :=
    hKuK.trans (le_normalizer_oddCoreIn K)
  have hxK : x ∈ oddCoreIn K ⊔ twoLayerIn Y := by rw [sup_comm, hsup]; exact hx.1
  obtain ⟨o, ho, y, hy, rfl⟩ := exists_mul_of_mem_sup_normalizer hKuO hxK
  have hyC : y ∈ centralizer ({u} : Set G) := (hKu2.1 hy).2
  have hoC : o ∈ centralizer ({u} : Set G) := by
    have : o = (o * y) * y⁻¹ := by group
    rw [this]
    exact mul_mem hx.2 (inv_mem hyC)
  have hYW : oddCoreIn K ⊓ centralizer ({u} : Set G) ≤ normalizer (twoLayerIn Y : Set G) :=
    (le_inf (inf_le_left.trans (map_subtype_le _)) inf_le_right).trans
      (le_normalizer_twoLayerIn Y)
  have hodd : Nat.Coprime 2 (((oddCoreIn K ⊓ centralizer ({u} : Set G)) ⊓
      twoLayerIn Y).subgroupOf (oddCoreIn K ⊓ centralizer ({u} : Set G))).index := by
    have hdvd := Subgroup.index_dvd_card
      (((oddCoreIn K ⊓ centralizer ({u} : Set G)) ⊓ twoLayerIn Y).subgroupOf
        (oddCoreIn K ⊓ centralizer ({u} : Set G)))
    refine Nat.Coprime.coprime_dvd_right hdvd ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_oddCoreIn K)
  exact mem_of_mem_sup_of_coprime_index hYW hodd (mul_mem (mem_sup_right ⟨ho, hoC⟩)
    (mem_sup_left hy)) hk

theorem le_pump_of_isPGroup (hK : K ∈ kStarComponents N) (huQ : u ∈ coreActionKernel K)
    (hu2 : orderOf u = 2) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ K ⊓ centralizer ({u} : Set G)) :
    S ≤ twoLayerIn (K ⊓ centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  exact mem_pump_of_two hK huQ hu2 (hSK hx) hk

theorem le_coreActionKernel_pump {S : Subgroup G} (hSQ : S ≤ coreActionKernel K)
    (hSu : S ≤ centralizer ({u} : Set G)) :
    S ≤ coreActionKernel (twoLayerIn (K ⊓ centralizer ({u} : Set G))) := by
  set Y := K ⊓ centralizer ({u} : Set G) with hY
  intro s hs
  have hsK : s ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp (hSQ hs)).1
  have hsC : s ∈ normalizer (centralizer ({u} : Set G) : Set G) := le_normalizer (hSu hs)
  have hsY : s ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, mem_normalizer_iff.mp hsK, mem_normalizer_iff.mp hsC]
  have hsL : s ∈ normalizer (twoLayerIn Y : Set G) := by
    have h1 := map_twoLayerIn (MulAut.conj s) Y
    have hsY' : Y.map (MulAut.conj s).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp hsY
    rw [hsY'] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  refine mem_coreActionKernel.mpr ⟨hsL, fun j hj => ?_⟩
  have hjK : j ∈ K := ((map_subtype_le _ : twoLayerIn Y ≤ Y) hj).1
  have h1 := (mem_coreActionKernel.mp (hSQ hs)).2 j hjK
  have h2 : j⁻¹ * s⁻¹ * j * s ∈ twoLayerIn Y := by
    have h3 : s⁻¹ * j * s ∈ twoLayerIn Y := by
      have := (mem_normalizer_iff.mp (inv_mem hsL) j).mp hj
      rwa [inv_inv] at this
    rw [mul_assoc, mul_assoc]
    exact mul_mem (inv_mem hj) (by simpa [mul_assoc] using h3)
  have hLO : twoLayerIn Y ≤ normalizer (oddCoreIn K : Set G) :=
    ((map_subtype_le _ : twoLayerIn Y ≤ Y).trans inf_le_left).trans (le_normalizer_oddCoreIn K)
  exact inf_le_oddCoreIn (coprime_card_oddCoreIn K) hLO ⟨h1, h2⟩

end Pump

section Lemmas

variable {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

omit [Finite G] in
theorem centralizer_zpowers_eq (u : G) :
    centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem mem_cover_and_commutator_le_oddCoreIn_of_fixed_pump
    {K J V : Subgroup G} {w f : G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hwK : w ∈ coreActionKernel K) (hw2 : orderOf w = 2)
    (hVQ : V ≤ coreActionKernel K)
    (hVw : V ≤ centralizer ({w} : Set G))
    (hfK : f ∈ K) (hf2 : orderOf f = 2)
    (hfw : f ∈ centralizer ({w} : Set G))
    (hJ : IsTwoComponentIn J (centralizer ({w} : Set G)))
    (hcover : twoLayerIn (K ⊓ centralizer ({w} : Set G)) ⊔ oddCoreIn J = J) :
    f ∈ J ∧ ⁅J, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
  classical
  set Cw : Subgroup G := centralizer ({w} : Set G) with hCw
  set Y : Subgroup G := K ⊓ Cw with hY
  set P : Subgroup G := twoLayerIn Y with hP
  have hwP2 : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2, pow_one])
  have hwQ : zpowers w ≤ coreActionKernel K := zpowers_le.mpr hwK
  have hsup0 : (K ⊓ centralizer ((zpowers w : Subgroup G) : Set G)) ⊔ oddCoreIn K = K :=
    Sol76.inf_centralizer_sup_oddCoreIn_eq (L := K) (S := zpowers w) hwP2 hwQ
  have hsup : Y ⊔ oddCoreIn K = K := by
    rw [hY, hCw, ← centralizer_zpowers_eq]
    exact hsup0
  obtain ⟨-, hPeq, -, -⟩ := Sol76.cover_facts hKq inf_le_left hsup
  have hfCw : f ∈ Cw := hfw
  have hfY : f ∈ Y := by rw [hY]; exact ⟨hfK, hfCw⟩
  have hfP : f ∈ P := by
    rw [hP, hPeq]
    exact subset_closure ⟨hfY, 1, by simpa using hf2⟩
  have hcover' : P ⊔ oddCoreIn J = J := by rw [hP]; exact hcover
  have hPJ' : P ≤ J := (le_sup_left : P ≤ P ⊔ oddCoreIn J).trans hcover'.le
  have hfJ : f ∈ J := hPJ' hfP
  have hVP : V ≤ coreActionKernel P := by
    rw [hP]
    exact le_coreActionKernel_pump (K := K) (u := w) hVQ hVw
  have hPV : ⁅P, V⁆ ≤ oddCoreIn P :=
    commutator_le_oddCoreIn_of_le_coreActionKernel hVP
  have hPOJ : oddCoreIn P ≤ oddCoreIn J :=
    oddCoreIn_le_of_sup_eq hPJ' hcover'
  have hOJ : oddCoreIn J ≤ oddCoreIn Cw := oddCoreIn_le_of_isTwoComponentIn hJ
  have hPVO : ⁅P, V⁆ ≤ oddCoreIn Cw := hPV.trans (hPOJ.trans hOJ)
  have hVCw : V ≤ Cw := hVw
  have hCwN : Cw ≤ normalizer (oddCoreIn Cw : Set G) := Sol76.le_normalizer_oddCoreIn Cw
  have hVNorm : V ≤ normalizer (oddCoreIn Cw : Set G) := hVCw.trans hCwN
  have hOJ' : oddCoreIn J ≤ Cw := hOJ.trans (map_subtype_le _)
  have hA : ⁅oddCoreIn J, V⁆ ≤ oddCoreIn Cw := by
    have hcomm : ⁅oddCoreIn Cw, V⁆ ≤ oddCoreIn Cw :=
      (Subgroup.le_normalizer_iff_commutator_le_left).mp hVNorm
    exact (Subgroup.commutator_mono hOJ le_rfl).trans hcomm
  have hBA : P ≤ normalizer (oddCoreIn J : Set G) :=
    hPJ'.trans (Sol76.le_normalizer_oddCoreIn J)
  have hAO : oddCoreIn J ≤ normalizer (oddCoreIn Cw : Set G) := hOJ'.trans hCwN
  have hBO : P ≤ normalizer (oddCoreIn Cw : Set G) :=
    hPJ'.trans (hJ.1.trans hCwN)
  have hsum : ⁅oddCoreIn J ⊔ P, V⁆ ≤ oddCoreIn Cw :=
    commutator_sup_le_of_le hBA hAO hBO hA hPVO
  have hsupJO : oddCoreIn J ⊔ P = J := by rw [sup_comm]; exact hcover'
  refine ⟨hfJ, ?_⟩
  rwa [hsupJO] at hsum

omit [Finite G] in
theorem zpowers_ne_bot_of_orderOf_eq_two {u : G} (hu2 : orderOf u = 2) :
    zpowers u ≠ ⊥ := fun h => by
  rw [zpowers_eq_bot] at h
  rw [h, orderOf_one] at hu2
  norm_num at hu2

omit [Finite G] in
theorem sq_eq_one_of_orderOf_eq_two {u : G} (hu2 : orderOf u = 2) : u ^ 2 = 1 := by
  rw [← hu2, pow_orderOf_eq_one]

theorem le_oddCoreIn_of_component_dichotomy {u b : G}
    (hu2 : orderOf u = 2) (hb2 : orderOf b = 2) (hub : u * b = b * u)
    {V X : Subgroup G} (hVu : V ≤ centralizer ({u} : Set G))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({u} : Set G))
    (hXV : ⁅X, V⁆ = X)
    (hbranches : ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({u} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({u} : Set G))) :
    X ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  set Cu := centralizer ({u} : Set G) with hCu
  have hTe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hu2)
  have hSe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hb2)
  have hS1 := zpowers_ne_bot_of_orderOf_eq_two hb2
  have hT1 := zpowers_ne_bot_of_orderOf_eq_two hu2
  have hbu : b ∈ Cu := mem_centralizer_singleton_iff.mpr hub.symm
  have hST : zpowers b ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact zpowers_le.mpr hbu
  have h25 := sol25 hS1 hT1 hSe hTe hST
  rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h25
  have hX' : X ≤ oddCoreIn (centralizer ((zpowers b : Subgroup G) : Set G)) ⊓
      centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq, centralizer_zpowers_eq]; exact hX
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (hX.trans inf_le_left))
      (coprime_card_oddCoreIn _))
  refine le_oddCoreIn_of_commutator_le (hX.trans inf_le_right) hXodd
    ((Subgroup.commutator_mono le_rfl hX).trans h25.1) fun M hM => ?_
  have hM' : IsTwoComponentIn M (centralizer ((zpowers u : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers_eq]; exact hM
  rcases hbranches M hM with hbM | hMV
  · have h1 := commutator_le_oddCoreIn_of_not_moves hS1 hT1 hSe hTe hST hM' hX'
      (Or.inr ((Subgroup.commutator_mono le_rfl inf_le_left).trans
        (commutator_le_oddCoreIn_of_le_coreActionKernel hbM)))
    exact h1.trans (oddCoreIn_le_of_isTwoComponentIn hM)
  · have hXM : X ≤ normalizer (M : Set G) := hX.trans (h25.2 M hM).1
    have hCO : Cu ≤ normalizer (oddCoreIn Cu : Set G) := le_normalizer_oddCoreIn Cu
    exact commutator_le_of_eq_commutator hXM ((hX.trans inf_le_right).trans hCO)
      (hVu.trans hCO) (hM.1.trans hCO) hMV hXV

theorem inf_inf_le_oddCoreIn_of_component_dichotomy {u : G} (hu2 : orderOf u = 2)
    {S₁ S₂ : Subgroup G} (hS₁ : S₁ ≠ ⊥) (hS₁e : CFSG.Open.IsElemAbelian 2 S₁)
    (hS₁u : S₁ ≤ centralizer ({u} : Set G)) (hS₂ : S₂ ≠ ⊥)
    (hS₂e : CFSG.Open.IsElemAbelian 2 S₂) (hS₂u : S₂ ≤ centralizer ({u} : Set G))
    (hbranches : ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({u} : Set G)) →
        S₁ ≤ coreActionKernel M ∨
          ⁅M, S₂⁆ ≤ oddCoreIn (centralizer ({u} : Set G))) :
    oddCoreIn (centralizer (S₁ : Set G)) ⊓ oddCoreIn (centralizer (S₂ : Set G)) ⊓
        centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  set Cu := centralizer ({u} : Set G) with hCu
  set X := oddCoreIn (centralizer (S₁ : Set G)) ⊓ oddCoreIn (centralizer (S₂ : Set G)) ⊓ Cu
    with hXdef
  have hTe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hu2)
  have hT1 := zpowers_ne_bot_of_orderOf_eq_two hu2
  have hST₁ : S₁ ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact hS₁u
  have hST₂ : S₂ ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact hS₂u
  have h25 := sol25 hS₁ hT1 hS₁e hTe hST₁
  rw [centralizer_zpowers_eq] at h25
  have hX₁ : X ≤ oddCoreIn (centralizer (S₁ : Set G)) ⊓
      centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hX₂ : X ≤ oddCoreIn (centralizer (S₂ : Set G)) ⊓
      centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left : X ≤ _))
      (coprime_card_oddCoreIn _))
  refine le_oddCoreIn_of_commutator_le inf_le_right hXodd
    ((Subgroup.commutator_mono le_rfl
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).trans h25.1) fun M hM => ?_
  have hM' : IsTwoComponentIn M (centralizer ((zpowers u : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers_eq]; exact hM
  rcases hbranches M hM with hS₁Q | hMS₂
  · have h1 := commutator_le_oddCoreIn_of_not_moves hS₁ hT1 hS₁e hTe hST₁ hM' hX₁
      (Or.inr ((Subgroup.commutator_mono le_rfl inf_le_left).trans
        (commutator_le_oddCoreIn_of_le_coreActionKernel hS₁Q)))
    exact h1.trans (oddCoreIn_le_of_isTwoComponentIn hM)
  · have hmove : ⁅M, S₂ ⊓ normalizer (M : Set G)⁆ ≤ oddCoreIn M := by
      have h1 : ⁅M, S₂ ⊓ normalizer (M : Set G)⁆ ≤ M :=
        CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ inf_le_right
      have h2 : ⁅M, S₂ ⊓ normalizer (M : Set G)⁆ ≤ oddCoreIn Cu :=
        (Subgroup.commutator_mono le_rfl inf_le_left).trans hMS₂
      exact (le_inf h2 h1).trans
        (inf_le_oddCoreIn (coprime_card_oddCoreIn Cu) (hM.1.trans (le_normalizer_oddCoreIn Cu)))
    have h1 := commutator_le_oddCoreIn_of_not_moves hS₂ hT1 hS₂e hTe hST₂ hM' hX₂
      (Or.inr hmove)
    exact h1.trans (oddCoreIn_le_of_isTwoComponentIn hM)

theorem component_dichotomy_of_actual_hull_kernel {D J S V : Subgroup G}
    (hJ : IsTwoComponentIn J D)
    (hSJ : S ≤ coreActionKernel J)
    (hVJ : V ≤ J) :
    ∀ M : Subgroup G, IsTwoComponentIn M D →
      S ≤ coreActionKernel M ∨ ⁅M, V⁆ ≤ oddCoreIn D := by
  intro M hM
  by_cases hMJ : M = J
  · left
    simpa [hMJ] using hSJ
  · exact Or.inr ((Subgroup.commutator_mono le_rfl hVJ).trans
      (CFSG.ComponentClassification.FooteLit.commutator_le_oddCoreIn_of_ne hM hJ hMJ))

theorem component_dichotomy_of_actual_hulls {V : Subgroup G} {f : G}
    (hhulls : ∀ w ∈ V, w ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({w} : Set G)) ∧ f ∈ J ∧
        ⁅J, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G))) :
    ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers f ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
  intro w hw hw1 M hM
  obtain ⟨J, hJ, hfJ, hJV⟩ := hhulls w hw hw1
  by_cases hMJ : M = J
  · subst hMJ
    exact Or.inr hJV
  · refine Or.inl (zpowers_le.mpr ?_)
    exact CFSG.ComponentClassification.GSThmB.B5a.le_coreActionKernel_of_ne
      hM.1 hJ.1 hM.2 hJ.2 hMJ hfJ

theorem le_coreActionKernel_of_ne (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') : K' ≤ coreActionKernel K := fun _ hx =>
  mem_coreActionKernel_of_ne hK' hK hne.symm hx

theorem pump_moves (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {u : G}
    (huK' : u ∈ K') (hu2 : orderOf u = 2) {M : Subgroup G}
    (hM : IsTwoComponentIn M (centralizer ({u} : Set G))) :
    twoLayerIn (K ⊓ centralizer ({u} : Set G)) ≤ coreActionKernel M ∨
      M ≤ oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)) := by
  have huQ : u ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm huK'
  obtain ⟨-, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  have hKuL := hKuS.trans (solomonKStarOf_le_twoLayerIn _)
  by_cases h : twoLayerIn (K ⊓ centralizer ({u} : Set G)) ≤ coreActionKernel M
  · exact Or.inl h
  · exact Or.inr ((le_conjClosure_of_not_le_coreActionKernel hM hKuL h).trans
      (h32 G hG N hN K' hK' K hK hne.symm u huK' hu2))

theorem oddCoreIn_pump_le (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {u : G}
    (huK' : u ∈ K') (hu2 : orderOf u = 2) :
    oddCoreIn (twoLayerIn (K ⊓ centralizer ({u} : Set G))) ≤
      oddCoreIn (centralizer ({u} : Set G)) := by
  have huQ : u ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm huK'
  obtain ⟨-, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  exact oddCoreIn_le_of_conjClosure_le (hKuS.trans (solomonKStarOf_le_twoLayerIn _))
    (h32 G hG N hN K' hK' K hK hne.symm u huK' hu2)

theorem commutator_le_oddCoreIn_of_le_pump (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {u : G} (huK' : u ∈ K') (hu2 : orderOf u = 2) {S M : Subgroup G}
    (hSQ : S ≤ coreActionKernel K) (hSu : S ≤ centralizer ({u} : Set G))
    (hMP : M ≤ oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
      twoLayerIn (K ⊓ centralizer ({u} : Set G))) :
    ⁅M, S⁆ ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  set Cu := centralizer ({u} : Set G) with hCu
  have huQ : u ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm huK'
  obtain ⟨hKu2, -, -, hKuS, -⟩ := pump_facts hK huQ hu2
  have hKuL : twoLayerIn (K ⊓ Cu) ≤ twoLayerIn Cu :=
    hKuS.trans (solomonKStarOf_le_twoLayerIn _)
  have hKuC : twoLayerIn (K ⊓ Cu) ≤ Cu := hKu2.1.trans inf_le_right
  have hOLC : oddCoreIn (twoLayerIn Cu) ≤ Cu := (map_subtype_le _).trans (map_subtype_le _)
  have hCO : Cu ≤ normalizer (oddCoreIn Cu : Set G) := le_normalizer_oddCoreIn Cu
  refine (Subgroup.commutator_mono hMP le_rfl).trans ?_
  refine commutator_sup_le_of_le (hKuL.trans (le_normalizer_oddCoreIn _)) (hOLC.trans hCO)
    (hKuC.trans hCO) ?_ ?_
  · exact (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
      (hSu.trans (le_normalizer_oddCoreIn_twoLayerIn Cu))).trans (oddCoreIn_twoLayerIn_le Cu)
  · exact (commutator_le_oddCoreIn_of_le_coreActionKernel (le_coreActionKernel_pump hSQ hSu)).trans
      (oddCoreIn_pump_le h32 hG hN hK hK' hne huK' hu2)

theorem component_dichotomy_of_pump (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {u : G} (huK' : u ∈ K') (hu2 : orderOf u = 2) {S₁ S₂ : Subgroup G}
    (hS₁p : IsPGroup 2 S₁) (hS₁Ku : S₁ ≤ K ⊓ centralizer ({u} : Set G))
    (hS₂Q : S₂ ≤ coreActionKernel K) (hS₂u : S₂ ≤ centralizer ({u} : Set G)) :
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({u} : Set G)) →
      S₁ ≤ coreActionKernel M ∨
        ⁅M, S₂⁆ ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  intro M hM
  have huQ : u ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm huK'
  rcases pump_moves h32 hG hN hK hK' hne huK' hu2 hM with h | h
  · exact Or.inl ((le_pump_of_isPGroup hK huQ hu2 hS₁p hS₁Ku).trans h)
  · exact Or.inr (commutator_le_oddCoreIn_of_le_pump h32 hG hN hK hK' hne huK' hu2
      hS₂Q hS₂u h)

theorem le_oddCoreIn_of_pump (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {u b : G}
    (huK' : u ∈ K') (hu2 : orderOf u = 2) (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (hub : u * b = b * u) {V X : Subgroup G} (hVK' : V ≤ K')
    (hVu : V ≤ centralizer ({u} : Set G))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({u} : Set G))
    (_hVX : V ≤ normalizer (X : Set G)) (hXV : ⁅X, V⁆ = X) :
    X ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  have hbu : b ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hub.symm
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hSp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  exact le_oddCoreIn_of_component_dichotomy hu2 hb2 hub hVu hX hXV
    (component_dichotomy_of_pump h32 hG hN hK hK' hne huK' hu2
      (S₁ := zpowers b) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hbK) (zpowers_le.mpr hbu)) hVQ hVu)

theorem inf_inf_le_oddCoreIn (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {u : G}
    (huK' : u ∈ K') (hu2 : orderOf u = 2) {S₁ S₂ : Subgroup G} (hS₁ : S₁ ≠ ⊥)
    (hS₁e : CFSG.Open.IsElemAbelian 2 S₁) (hS₁K : S₁ ≤ K)
    (hS₁u : S₁ ≤ centralizer ({u} : Set G)) (hS₂ : S₂ ≠ ⊥)
    (hS₂e : CFSG.Open.IsElemAbelian 2 S₂) (hS₂Q : S₂ ≤ coreActionKernel K)
    (hS₂u : S₂ ≤ centralizer ({u} : Set G)) :
    oddCoreIn (centralizer (S₁ : Set G)) ⊓ oddCoreIn (centralizer (S₂ : Set G)) ⊓
        centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  exact inf_inf_le_oddCoreIn_of_component_dichotomy hu2 hS₁ hS₁e hS₁u hS₂ hS₂e hS₂u
    (component_dichotomy_of_pump h32 hG hN hK hK' hne huK' hu2
      (S₁ := S₁) (S₂ := S₂)
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 S₁ hS₁e)
      (le_inf hS₁K hS₁u) hS₂Q hS₂u)

end Lemmas

end CFSG.ComponentClassification.Sol76.Sig
