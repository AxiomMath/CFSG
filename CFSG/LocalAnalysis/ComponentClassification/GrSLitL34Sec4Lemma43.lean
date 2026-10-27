module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_le_self {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])

omit [Finite G] in
theorem mem_normalizer_of_forall_commute {E : Subgroup G} {p : G}
    (h : ∀ y ∈ E, p * y = y * p) : p ∈ normalizer (E : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rwa [show p * y * p⁻¹ = y by rw [h y hy]; group]
  · intro hy
    have h1 := h _ hy
    have h2 : p * y * p⁻¹ = y := by
      calc p * y * p⁻¹ = p⁻¹ * (p * (p * y * p⁻¹)) := by group
        _ = p⁻¹ * (p * y * p⁻¹ * p) := by rw [h1]
        _ = y := by group
    rwa [h2] at hy

theorem exists_center_involution_of_normal {S H : Subgroup G} (hS : IsPGroup 2 S) (hHS : H ≤ S)
    (hHn : S ≤ normalizer (H : Set G)) (hH : H ≠ ⊥) :
    ∃ t ∈ H, orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hS
  have hHn' : (H.subgroupOf S).Normal := ⟨fun h hh s => by
    rw [mem_subgroupOf] at hh ⊢
    exact (mem_normalizer_iff.mp (hHn s.2) h).mp hh⟩
  have hHne : H.subgroupOf S ≠ ⊥ := by
    intro h
    apply hH
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hHS hx⟩ : S) ∈ H.subgroupOf S := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at hx'
    exact (mem_bot).mpr (congrArg Subtype.val hx')
  set C := H.subgroupOf S ⊓ center ↥S with hC
  have hCne : C ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  have hC2 : IsPGroup 2 C := (hS.of_equiv (topEquiv).symm).to_le le_top
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hCne (card_eq_one.mp (by rw [hk, pow_zero]))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((w : ↥S) : G), (mem_subgroupOf.mp (mem_inf.mp w.2).1), ?_, fun s hs => ?_⟩
  · rw [← hw, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · have h := (mem_center_iff.mp (mem_inf.mp w.2).2) ⟨s, hs⟩
    exact congrArg Subtype.val h

theorem exists_sixteen_of_isThreeConnected {S₁ E F : Subgroup G} (h3 : IsThreeConnected S₁)
    (hES : E ≤ S₁) (hFS : F ≤ S₁) (hE : IsEightGroup E) (hF : IsEightGroup F) (hEF : E ≠ F) :
    ∃ D : Subgroup G, D ≤ S₁ ∧ IsElemTwo D ∧ 16 ≤ Nat.card D := by
  by_contra hno
  push Not at hno
  have hEr : IsAbelianTwoOfRank 3 E := hE.1.isAbelianTwoOfRank (by rw [hE.2])
  have hFr : IsAbelianTwoOfRank 3 F := hF.1.isAbelianTwoOfRank (by rw [hF.2])
  obtain ⟨-, -, hchain⟩ := h3 E F hES hFS hEr hFr
  have key : ∀ B : Subgroup G, Relation.ReflTransGen (fun A' B' : Subgroup G => B' ≤ S₁ ∧
      IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) E B →
      IsAbelianTwoOfRank 3 B ∧ ∀ y ∈ B, y * y = 1 → y ∈ E := by
    intro B hB
    induction hB with
    | refl => exact ⟨hEr, fun y hy _ => hy⟩
    | @tail B' C' _ hBC ih =>
      obtain ⟨hCS, hCr, hcomm⟩ := hBC
      obtain ⟨hBr, hBE⟩ := ih
      refine ⟨hCr, fun y hy hy2 => ?_⟩
      obtain ⟨F₀, hF₀B, hF₀, hF₀8⟩ := exists_isElemTwo_of_isAbelianTwoOfRank hBr
      have hF₀E : F₀ ≤ E := fun f hf => hBE f (hF₀B hf) (hF₀.2 f hf)
      have hEB : E ≤ B' := by
        have heq : F₀ = E := eq_of_le_of_card_ge hF₀E (by rw [hE.2]; exact hF₀8)
        rw [← heq]
        exact hF₀B
      by_contra hyE
      obtain ⟨hD, hDc⟩ := isElemTwo_sup_zpowers hE.1 hy2 hyE fun e he => hcomm e (hEB he) y hy
      have h16 := hno _ (sup_le hES (zpowers_le.mpr (hCS hy))) hD
      rw [hDc, hE.2] at h16
      omega
  obtain ⟨-, hFE⟩ := key F hchain
  exact hEF (eq_of_le_of_card_ge (fun f hf => hFE f hf (hF.1.2 f hf)) (by rw [hE.2, hF.2])).symm

theorem mem_normalizer_wGroup_of_eight {S₁ W B : Subgroup G}
    (hWB : ∀ B : Subgroup G, B ≤ S₁ → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hBS : B ≤ S₁) (hB : IsEightGroup B) {g : G}
    (hg : B.map (MulAut.conj g).toMonoidHom ≤ S₁) : g ∈ normalizer (W : Set G) := by
  have h8 : Nat.card ↥(B.map (MulAut.conj g).toMonoidHom) = 8 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hB.2]
  have h1 := hWB _ hg ((hB.1.map_conj g).isAbelianTwoOfRank (by rw [h8]))
  rw [wGroup_map_conj, hWB B hBS (hB.1.isAbelianTwoOfRank (by rw [hB.2]))] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr h1

omit [Finite G] in
theorem withKernel_le_normalizer (J : Subgroup G) : withKernel J ≤ normalizer (J : Set G) :=
  sup_le le_normalizer fun _ hc => (mem_coreActionKernel.mp hc).1

omit [Finite G] in
theorem map_conj_withKernel_le {J : Subgroup G} {c : G} (hc : c ∈ normalizer (J : Set G)) :
    (withKernel J).map (MulAut.conj c).toMonoidHom ≤ withKernel J := by
  unfold withKernel
  rw [Subgroup.map_sup]
  refine sup_le_sup (le_of_eq (mem_normalizer_iff_map_conj_eq.mp hc)) ?_
  rintro _ ⟨k, hk, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_mem_coreActionKernel hc hk

omit [Finite G] in
theorem inf_mem_normalizer {A B : Subgroup G} {s : G} (hA : s ∈ normalizer (A : Set G))
    (hB : s ∈ normalizer (B : Set G)) : s ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [mem_inf]
  exact ⟨fun h => ⟨(hA y).mp h.1, (hB y).mp h.2⟩, fun h => ⟨(hA y).mpr h.1, (hB y).mpr h.2⟩⟩

omit [Finite G] in
theorem oddIn_le_coreActionKernel (J : Subgroup G) : oddIn J ≤ coreActionKernel J := by
  intro o ho
  have hoJ : o ∈ J := (map_subtype_le _ : oddIn J ≤ J) ho
  refine mem_coreActionKernel.mpr ⟨le_normalizer hoJ, fun j hj => ?_⟩
  have h1 : j⁻¹ * o⁻¹ * j ∈ oddIn J := by
    have := conj_mem_oddIn (inv_mem hj) (inv_mem ho)
    rwa [inv_inv] at this
  exact mul_mem h1 ho

theorem exists_mul_centralizer_of_mem_coreActionKernel {J P : Subgroup G} (hP : IsSylowTwoIn P J)
    {c : G} (hc : c ∈ coreActionKernel J) :
    ∃ o ∈ oddIn J, ∃ c₁ ∈ coreActionKernel J, (∀ p ∈ P, c₁ * p = p * c₁) ∧ c = o * c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcN : c ∈ normalizer (J : Set G) := (mem_coreActionKernel.mp hc).1
  have hP2 : IsPGroup 2 P := isPGroup_of_isSylowTwoIn hP
  have hPJ : P ≤ J := hP.1
  set O : Subgroup G := oddIn J with hOdef
  have hJO : J ≤ normalizer (O : Set G) := fun j hj => mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => conj_mem_oddIn hj hy, fun hy => by
      have := conj_mem_oddIn (inv_mem hj) hy
      rwa [show j⁻¹ * (j * y * j⁻¹) * j⁻¹⁻¹ = y by group] at this⟩
  have hOodd : Odd (Nat.card O) := odd_card_map_pPrimeCore J
  have hPO : P ≤ normalizer (O : Set G) := hPJ.trans hJO
  have hSyl : IsSylowTwoIn P (P ⊔ O) := isSylowTwoIn_sup_odd hP2 hPO hOodd
  have hON : c ∈ normalizer (O : Set G) :=
    normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J) hcN
  have hcK : c ∈ normalizer ((P ⊔ O : Subgroup G) : Set G) := by
    refine mem_normalizer_of_map_le_self ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((le_of_eq (mem_normalizer_iff_map_conj_eq.mp hON)).trans le_sup_right)
    rintro _ ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 := (mem_coreActionKernel.mp (inv_mem hc)).2 p (hPJ hp)
    rw [inv_inv] at h1
    rw [show c * p * c⁻¹ = p * (p⁻¹ * c * p * c⁻¹) by group]
    exact mul_mem (mem_sup_left hp) (mem_sup_right h1)
  obtain ⟨m, hm, n, hnN, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hSyl hcK
  have hm' : m ∈ (P : Set G) * (O : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right P O hPO]
    exact hm
  obtain ⟨p, hp, o, ho, rfl⟩ := hm'
  have hpN : p ∈ normalizer (P : Set G) := le_normalizer hp
  have ho' : p * o * p⁻¹ ∈ O := conj_mem_oddIn (hPJ hp) ho
  refine ⟨p * o * p⁻¹, ho', p * n, ?_, ?_, by group⟩
  · have h1 : p * n = (p * o * p⁻¹)⁻¹ * (p * o * n) := by group
    rw [h1]
    exact mul_mem (inv_mem (oddIn_le_coreActionKernel J ho')) hc
  ·
    have hc₁N : p * n ∈ normalizer (P : Set G) := mul_mem hpN hnN
    have hc₁C : p * n ∈ coreActionKernel J := by
      have h1 : p * n = (p * o * p⁻¹)⁻¹ * (p * o * n) := by group
      rw [h1]
      exact mul_mem (inv_mem (oddIn_le_coreActionKernel J ho')) hc
    intro q hq
    set c₁ := p * n with hc₁
    have hcomm : q⁻¹ * c₁⁻¹ * q * c₁ ∈ O := (mem_coreActionKernel.mp hc₁C).2 q (hPJ hq)
    have hcP : q⁻¹ * c₁⁻¹ * q * c₁ ∈ P := by
      have h2 : c₁⁻¹ * q * c₁⁻¹⁻¹ ∈ P := (mem_normalizer_iff.mp (inv_mem hc₁N) q).mp hq
      rw [inv_inv] at h2
      rw [show q⁻¹ * c₁⁻¹ * q * c₁ = q⁻¹ * (c₁⁻¹ * q * c₁) by group]
      exact mul_mem (inv_mem hq) h2
    have h0 := eq_bot_of_le_two_group_of_le_odd hP2 hOodd (zpowers_le.mpr hcP)
      (zpowers_le.mpr hcomm)
    have h1 : q⁻¹ * c₁⁻¹ * q * c₁ = 1 := by
      have := mem_zpowers (q⁻¹ * c₁⁻¹ * q * c₁)
      rw [h0] at this
      exact this
    calc c₁ * q = c₁ * q * (q⁻¹ * c₁⁻¹ * q * c₁) := by rw [h1, mul_one]
      _ = q * c₁ := by group

theorem le_normalizer_of_withKernel {J P E : Subgroup G} (hP : IsSylowTwoIn P J) (hEP : E ≤ P)
    (hE : J ⊓ normalizer (P : Set G) ≤ normalizer (E : Set G)) :
    withKernel J ⊓ normalizer (P : Set G) ≤ normalizer (E : Set G) := by
  intro g hg
  obtain ⟨hgW, hgP⟩ := mem_inf.mp hg
  have hCJ : coreActionKernel J ≤ normalizer (J : Set G) := fun c hc =>
    (mem_coreActionKernel.mp hc).1
  have hg' : g ∈ (J : Set G) * (coreActionKernel J : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left J (coreActionKernel J) hCJ]
    exact hgW
  obtain ⟨j, hj, c, hc, rfl⟩ := hg'
  obtain ⟨o, ho, c₁, -, hc₁P, rfl⟩ := exists_mul_centralizer_of_mem_coreActionKernel hP hc
  have hc₁N : c₁ ∈ normalizer (P : Set G) := mem_normalizer_of_forall_commute hc₁P
  have hjo : j * o ∈ J ⊓ normalizer (P : Set G) := by
    refine mem_inf.mpr ⟨mul_mem hj ((map_subtype_le _ : oddIn J ≤ J) ho), ?_⟩
    have := mul_mem hgP (inv_mem hc₁N)
    rwa [show j * (o * c₁) * c₁⁻¹ = j * o by group] at this
  have hc₁E : c₁ ∈ normalizer (E : Set G) :=
    mem_normalizer_of_forall_commute fun y hy => hc₁P y (hEP hy)
  show j * (o * c₁) ∈ normalizer (E : Set G)
  rw [show j * (o * c₁) = (j * o) * c₁ by group]
  exact mul_mem (hE hjo) hc₁E

theorem not_isThreeConnected (hSol : SolomonCommutingCoreInput) (hKG : L34UnbalancedKGroupInput)
    (hTwo : L34TwoEightsFact) (hPar : L34ParabolicGenerationFact) (hEnd : L34Lemma43EndStep)
    {a x : G} {J S A : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (hZ : S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J)
    (hrun : L34Sec4Running J A) : ¬ IsThreeConnected (S ⊓ withKernel J) := by
  intro h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, -, hS, haS, hxS⟩ := id hset
  obtain ⟨hsimple, -, hK, -, -, hLB, -, -⟩ := hbase
  obtain ⟨hAW, hA8, hWA⟩ := hrun
  have : IsSimpleGroup G := hsimple
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  have ha2 : orderOf a = 2 := hU3.1
  have hx2 : orderOf x = 2 := hU3.2.1
  have hax : a * x = x * a := hU3.2.2.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set S₁ : Subgroup G := S ⊓ withKernel J with hS₁
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hPS₁ : P ≤ S₁ := le_inf inf_le_left (inf_le_right.trans le_sup_left)
  obtain ⟨E₁, E₂, hE₁P, hE₂P, hE₁, hE₂, hE₁₂⟩ := hTwo G J P hJper hL34 hP
  obtain ⟨D, hDS, hD, hD16⟩ := exists_sixteen_of_isThreeConnected h3 (hE₁P.trans hPS₁)
    (hE₂P.trans hPS₁) hE₁ hE₂ hE₁₂
  have hDr : IsAbelianTwoOfRank 3 D := hD.isAbelianTwoOfRank (by omega)
  set W : Subgroup G := wGroup D with hWdef
  have hWB : ∀ B : Subgroup G, B ≤ S₁ → IsAbelianTwoOfRank 3 B → wGroup B = W := fun B hBS hB =>
    wGroup_eq_of_abelianConnected hGW (h3 B D hBS hDS hB hDr).abelianConnected
  have hW : W ≠ ⊥ := by
    have hAN : A ≤ normalizer (J : Set G) := hAW.trans (withKernel_le_normalizer J)
    obtain ⟨c, hcN, hcA⟩ := hS.exists_conj_le hAN hA8.1.isPGroup
    set A' : Subgroup G := A.map (MulAut.conj c).toMonoidHom with hA'
    have hA'S : A' ≤ S₁ := by
      refine le_inf ?_ ((map_mono hAW).trans (map_conj_withKernel_le hcN))
      rintro _ ⟨y, hy, rfl⟩
      exact hcA y hy
    have hA'8 : Nat.card A' = 8 := by
      rw [hA', card_map_of_injective (MulAut.conj c).injective, hA8.2]
    have h1 := hWB A' hA'S ((hA8.1.map_conj c).isAbelianTwoOfRank (by rw [hA'8]))
    rw [hA', wGroup_map_conj] at h1
    intro hW0
    apply hWA
    rw [hW0] at h1
    exact (map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp h1
  have hWodd : Odd (Nat.card W) := by
    have h := (CFSG.ClassicalInvolution.Balance.isComplete_deltaCore hD.isElemAbelian hD16
      (twoBalancedWrt_of_gwTwoBalanced hGW hD)).1.1
    rw [hWdef, wGroup_eq_completion hD]
    exact Nat.coprime_two_left.mp h
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hOM : oddIn J ≤ M := by
    have hDN : D ≤ normalizer ((oddIn J : Subgroup G) : Set G) := fun d hd =>
      normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
        (withKernel_le_normalizer J (mem_inf.mp (hDS hd)).2)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
      Nat.prime_two D (oddIn J) hD.isElemAbelian (by norm_num; omega) hDN
      (by rw [oddIn, card_map_of_injective J.subtype_injective]; exact pPrimeCore_coprime_card)
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    have hFD : F ≤ D := hF.1
    have hFc : Nat.card F = 8 := by rw [hF.2]; norm_num
    refine inf_le_right.trans fun y hy => ?_
    refine mem_normalizer_wGroup_of_eight hWB (hFD.trans hDS) ⟨hD.mono hFD, hFc⟩ ?_
    rintro _ ⟨f, hf, rfl⟩
    have hfy := (mem_centralizer_iff.mp hy) f hf
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hfy, mul_inv_cancel_right]
    exact hDS (hFD hf)
  obtain ⟨T₁, T₂, hT₁P, hT₂P, ⟨F₁, hF₁T, hF₁⟩, ⟨F₂, hF₂T, hF₂⟩, hJgen⟩ :=
    hPar G J P hJper hL34 hP
  have hNT : ∀ T F : Subgroup G, T ≤ P → F ≤ T → IsEightGroup F →
      J ⊓ normalizer (T : Set G) ≤ M := by
    intro T F hTP hFT hF g hg
    refine mem_normalizer_wGroup_of_eight hWB ((hFT.trans hTP).trans hPS₁) hF ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hPS₁ (hTP ((mem_normalizer_iff.mp (mem_inf.mp hg).2 f).mp (hFT hf)))
  have hJM : J ≤ M := hJgen.trans
    (sup_le (sup_le hOM (hNT T₁ F₁ hT₁P hF₁T hF₁)) (hNT T₂ F₂ hT₂P hF₂T hF₂))
  have hNJ : normalizer (J : Set G) ≤ M := by
    intro n hn
    obtain ⟨m, hmJ, k, hkN, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hP hn
    refine mul_mem (hJM hmJ) (mem_normalizer_wGroup_of_eight hWB (hE₁P.trans hPS₁) hE₁ ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact hPS₁ ((mem_normalizer_iff.mp hkN f).mp (hE₁P hf))
  have hMtop : M ≠ ⊤ := by
    intro hMt
    have hWn : W.Normal := by
      constructor
      intro w hw g
      have hg : g ∈ M := by rw [hMt]; exact mem_top g
      exact (mem_normalizer_iff.mp hg w).mp hw
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW h
    · have h2 : 2 ∣ Nat.card W := by
        rw [h, card_top, ← ha2]
        exact orderOf_dvd_natCard a
      exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  have hDxN := oddIn_inf_le_normalizer hSol hx2 ha2 hax.symm hJa hJc
  obtain ⟨K, hKM, hKc, hcase⟩ := exists_component_of_unbalancedKGroup hKG hSol hK hMtop hU3 hL34
    (hNJ (hSN haS)) (hNJ (hSN hxS)) hJM (hDxN.trans hNJ)
  exact hEnd G a x J S A hset hcent hZ ⟨hAW, hA8, hWA⟩ h3 W hW hWodd hWB hNJ K hKM hKc hcase

theorem exponent_eq_four (hExp : L34CenterExponentFact) (hEl : L34ElementaryCenterFact)
    {a x : G} {J S : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (h3 : ¬ IsThreeConnected (S ⊓ withKernel J)) : Monoid.exponent ↥(S ⊓ zStarIn J) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := hset
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  set Z : Subgroup G := S ⊓ zStarIn J with hZdef
  have hZP : P ⊓ zStarIn J = Z := by
    have hZJ : zStarIn J ≤ J := map_subtype_le _
    rw [hPdef, hZdef, inf_assoc, inf_eq_right.mpr hZJ]
  have h4 : ∀ z ∈ Z, z ^ 4 = 1 := fun z hz => hExp G J P hJper hL34 hP z (hZP ▸ hz)
  have hsq : ∃ z ∈ Z, z * z ≠ 1 := by
    by_contra hno
    push Not at hno
    apply h3
    obtain ⟨E, -, hEP, hE, hEc, hEN⟩ :=
      hEl G J P hJper hL34 hP fun z hz => hno z (hZP ▸ hz)
    rw [hZP] at hEc
    set S₁ : Subgroup G := S ⊓ withKernel J with hS₁
    have hPS₁ : P ≤ S₁ := le_inf inf_le_left (inf_le_right.trans le_sup_left)
    have hS₁2 : IsPGroup 2 S₁ := hS2.to_le inf_le_left
    have hS₁N : S₁ ≤ normalizer (E : Set G) := fun s hs =>
      le_normalizer_of_withKernel hP hEP hEN (mem_inf.mpr ⟨(mem_inf.mp hs).2,
        inf_mem_normalizer (le_normalizer (mem_inf.mp hs).1) (hSN (mem_inf.mp hs).1)⟩)
    set C : Subgroup G := S ⊓ coreActionKernel J with hCdef
    have hCS₁ : C ≤ S₁ := inf_le_inf_left S le_sup_right
    have hCn : S₁ ≤ normalizer (C : Set G) := by
      intro s hs
      refine mem_normalizer_of_map_le_self ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_inf.mpr ⟨mul_mem (mul_mem (mem_inf.mp hs).1 (mem_inf.mp hy).1)
        (inv_mem (mem_inf.mp hs).1), conj_mem_coreActionKernel (hSN (mem_inf.mp hs).1)
          (mem_inf.mp hy).2⟩
    have haC : a ∈ C := mem_inf.mpr ⟨haS, mem_coreActionKernel_of_le_centralizer hJa⟩
    have hCne : C ≠ ⊥ := by
      intro h
      rw [h, mem_bot] at haC
      rw [haC, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
    obtain ⟨t, htC, ht2, htZ⟩ := exists_center_involution_of_normal hS₁2 hCS₁ hCn hCne
    have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have htne : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    by_cases htE : t ∈ E
    ·
      have htZ' : t ∈ Z := by
        refine mem_inf.mpr ⟨(mem_inf.mp htC).1, ?_⟩
        rw [zStarIn, GSThmB.map_fusionZStar_eq J]
        exact mem_inf.mpr ⟨(mem_inf.mp (hEP htE)).2, (mem_inf.mp htC).2⟩
      have hZ2 : 1 < Nat.card Z := by
        rw [one_lt_card_iff_ne_bot]
        intro h
        rw [h, mem_bot] at htZ'
        exact htne htZ'
      exact isThreeConnected_of_normal hS₁2 (hEP.trans hPS₁) hS₁N hE (by omega)
    · obtain ⟨hD, hDc⟩ := isElemTwo_sup_zpowers hE ht1 htE fun e he =>
        htZ e (hPS₁ (hEP he))
      refine isThreeConnected_of_normal hS₁2
        (sup_le (hEP.trans hPS₁) (zpowers_le.mpr (hCS₁ htC))) ?_ hD (by omega)
      intro s hs
      refine mem_normalizer_of_map_le_self ?_
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le_sup (le_of_eq (mem_normalizer_iff_map_conj_eq.mp (hS₁N hs))) (le_of_eq ?_)
      congr 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [htZ s hs, mul_inv_cancel_right]
  obtain ⟨z, hzZ, hz2⟩ := hsq
  have hdvd : Monoid.exponent ↥Z ∣ 4 := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
    Subtype.ext (by simpa using h4 y y.2)
  have hndvd : ¬ Monoid.exponent ↥Z ∣ 2 := by
    intro h
    have h1 : orderOf (⟨z, hzZ⟩ : ↥Z) ∣ 2 := (Monoid.order_dvd_exponent _).trans h
    have h2 : (⟨z, hzZ⟩ : ↥Z) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    apply hz2
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Monoid.exponent ↥Z ∣ 2 ^ 2 from hdvd)
  interval_cases i
  · exact absurd (he ▸ one_dvd 2) hndvd
  · exact absurd (he ▸ dvd_refl 2) hndvd
  · rw [he]
    norm_num

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open GrS4

theorem l34Lemma43_of_inputs (hSol : SolomonCommutingCoreInput) (hKG : L34UnbalancedKGroupInput)
    (hTwo : L34TwoEightsFact) (hPar : L34ParabolicGenerationFact) (hExp : L34CenterExponentFact)
    (hEl : L34ElementaryCenterFact) (hEnd : L34Lemma43EndStep) : L34Lemma43 := by
  intro G _ _ a x J S A hset hcent hZ hrun
  have h3 := not_isThreeConnected hSol hKG hTwo hPar hEnd hset hcent hZ hrun
  exact ⟨h3, exponent_eq_four hExp hEl hset h3⟩

end CFSG.ComponentClassification.GrSLit
