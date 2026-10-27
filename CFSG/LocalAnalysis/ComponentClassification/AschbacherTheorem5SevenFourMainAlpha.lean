module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveStrong
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainFactors
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainInner
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveApply

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem oddCore_factor_le_core (hC : Counterexample G D 2 Abar) (i : Fin 2) :
    (CFSG.oddCore (aschbacherThm5Preimage D (Abar i))).map
        (aschbacherThm5Preimage D (Abar i)).subtype ≤ aschbacherThm5Core D := by
  set A := aschbacherThm5Preimage D (Abar i)
  have hDA : D ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
      (canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen i)
  have : (CFSG.oddCore A).Characteristic := CFSG.ComponentClassification.OddCore.characteristic A
  refine SectionSix.Strong.le_core_of_odd ((Subgroup.map_subtype_le _).trans (preimage_le D _))
    (fun d hd => AschbacherTheorem3.mem_normalizer_map_of_characteristic (CFSG.oddCore A)
      (hDA hd)) ?_
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact AschbacherTheorem3.odd_card_oddCore A

namespace FieldHyps

variable {t g : G}

theorem exists_large_centralizer (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {j m : Fin 2} (hjm : j ≠ m)
    (hnd' : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g m))
    {T₀ : Subgroup G} (hT₀2 : IsPGroup 2 T₀) (htT₀ : t ∈ T₀)
    (hT₀L : T₀ ≤ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    (hT₀A : T₀ ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    ∃ C : Subgroup G, C ≤ aschbacherThm5Preimage D (Abar i) ⊓
        Subgroup.centralizer (T₀ : Set G) ∧ IsPGroup 2 C ∧ Nat.card T₀ ≤ Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set B := rightConjugate D g with hBdef
  set K := Subgroup.normalizer ((B : Subgroup G) : Set G) with hKdef
  set Lm := aschbacherThm5Preimage B (conjFactors D Abar g m) with hLm
  set Lj := aschbacherThm5Preimage B (conjFactors D Abar g j) with hLj
  have hC' := hC.conj g
  have htm : t ∈ Lm := hT₀L htT₀
  have hBL : ∀ k : Fin 2, B ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage B (conjFactors D Abar g k) : Subgroup G) : Set G) := fun k =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le B _)).mp
      (canonical_preimage_normal B _ hC'.hyp.hcomm hC'.hyp.hgen k)
  have htwoT : ∀ u ∈ T₀, ∃ e : ℕ, u ^ (2 ^ e) = 1 := by
    intro u hu
    obtain ⟨e, he⟩ := hT₀2 ⟨u, hu⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hcentj : ∀ x ∈ Lm, aschbacherThm5Centralizes (aschbacherThm5Core B) Lj x := fun x hx =>
    cross_factor_centralizes B (conjFactors D Abar g) hC'.hyp.hcomm j m hjm x hx
  have hframe : AschbacherTheorem3.Frame A T₀ := by
    refine ⟨hT₀A, ?_, hT₀2⟩
    rw [eq_bot_iff]
    rintro u ⟨huT, huA⟩
    rw [Subgroup.mem_bot]
    by_contra hu1
    exact hF.not_centralizes_conj hin hC (l := j) huA (htwoT u huT) hu1 (hcentj u (hT₀L huT))
  obtain ⟨S, hS, hTS, -⟩ := exists_sylow_normalizer (le_sup_right : T₀ ≤ A ⊔ T₀) hT₀2
  have hnwc : ∃ a ∈ A, rightConjugate T₀ a ≤ S ∧ rightConjugate T₀ a ≠ T₀ := by
    by_contra hcon
    push Not at hcon
    have h42 := AschbacherTheorem3.lemma_4_2_oddCore
      (⟨hframe, hS, hTS, hcon⟩ : AschbacherTheorem3.Hyp42 A T₀ S)
    apply hF.false_of_centralizes_inv_mul hin hC hii' hnd (a := 1) A.one_mem
    intro a ha
    rw [inv_one, one_mul]
    have hmem : ⁅t⁻¹, a⁻¹⁆ ∈ ⁅A, T₀⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (T₀.inv_mem htT₀) (A.inv_mem ha)
    have h1 := oddCore_factor_le_core hC i (h42 hmem)
    rw [commutatorElement_def, inv_inv, inv_inv] at h1
    exact h1
  obtain ⟨a, -, haS, hane⟩ := hnwc
  obtain ⟨y, hyS, hyne⟩ := exists_conj_le_normalizer hS.isPGroup hTS haS hane
  obtain ⟨hNeq, hTC, hTCc⟩ := AschbacherTheorem3.lemma_4_1 hframe hS.le hTS
  set C := S ⊓ Subgroup.normalizer (T₀ : Set G) ⊓ A with hCdef
  have hcomm : ∀ x ∈ T₀, ∀ c ∈ C, x * c = c * x := by
    intro x hx c hc
    have h1 := Subgroup.commutator_mem_commutator hx hc
    rw [hTCc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hCle : C ≤ A ⊓ Subgroup.centralizer (T₀ : Set G) := by
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨hc.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx c hc
  have hC2 : IsPGroup 2 C := hS.isPGroup.to_le (inf_le_left.trans inf_le_left)
  refine ⟨C, hCle, hC2, ?_⟩
  have hcardy : Nat.card (rightConjugate T₀ y) = Nat.card T₀ :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  have hCN : C ≤ Subgroup.normalizer (T₀ : Set G) := inf_le_left.trans inf_le_right
  have hcardC : Nat.card (T₀ ⊔ C : Subgroup G) = Nat.card T₀ * Nat.card C :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T₀ C hCN
      (disjoint_iff.mpr hTC)
  by_cases hdis : T₀ ⊓ rightConjugate T₀ y = ⊥
  · have hyN : rightConjugate T₀ y ≤ Subgroup.normalizer (T₀ : Set G) := hyS.trans inf_le_right
    have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T₀
      (rightConjugate T₀ y) hyN (disjoint_iff.mpr hdis)
    have h2 : Nat.card (T₀ ⊔ rightConjugate T₀ y : Subgroup G) ≤
        Nat.card (T₀ ⊔ C : Subgroup G) := by
      apply Subgroup.card_le_of_le
      rw [← hNeq]
      exact sup_le (le_inf hTS Subgroup.le_normalizer) hyS
    rw [h1, hcardC, hcardy] at h2
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  exfalso
  obtain ⟨⟨u, huT, huy⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hdis
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hyu : y * u * y⁻¹ ∈ T₀ := (mem_rightConjugate_iff T₀ y u).mp huy
  have hyK : y⁻¹ ∈ K := by
    refine hC'.hyp.hi j j u y⁻¹ (htwoT u huT) ?_ (hcentj u (hT₀L huT)) ?_
    · rw [hC.center, Subgroup.mem_bot]
      exact hu1'
    · rw [inv_inv]
      exact hcentj _ (hT₀L hyu)
  obtain ⟨k, hk⟩ := hC'.hyp.hperm y⁻¹ hyK m
  have hTy : rightConjugate T₀ y ≤ aschbacherThm5Preimage B (conjFactors D Abar g k) := by
    rw [← hk]
    exact Subgroup.map_mono hT₀L
  have hnle : ¬ rightConjugate T₀ y ≤ T₀ := fun hle =>
    hyne (Subgroup.eq_of_le_of_card_ge hle hcardy.symm.le)
  obtain ⟨s', hs'y, hs'T⟩ := Set.not_subset.mp hnle
  have hs'N : s' ∈ T₀ ⊔ C := by
    rw [← hNeq]
    exact hyS hs'y
  have hframe' : AschbacherTheorem3.Frame C T₀ := by
    refine ⟨?_, hTC, hT₀2⟩
    intro x hx
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcomm x hx c hc).symm
  rw [sup_comm] at hs'N
  obtain ⟨s, hsT, c, hcC, rfl⟩ := hframe'.mem_sup_iff.mp hs'N
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hs'T
    exact hs'T hsT
  have hcA : c ∈ A := hcC.2
  have hsc : s * c = c * s := hcomm s hsT c hcC
  have hctwo : ∃ e : ℕ, c ^ (2 ^ e) = 1 := by
    obtain ⟨e, he⟩ := hC2 ⟨c, hcC⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  rcases fin_two_cases hjm k with hkj | hkm
  ·
    rw [hkj] at hTy
    have hscj : s * c ∈ Lj := hTy hs'y
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hC2) ⟨c, hcC⟩
    rw [Subgroup.orderOf_mk] at he
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at he
      exact hc1 he
    have hdvd : 2 ∣ orderOf c := by
      rw [he]
      exact dvd_pow_self 2 he0
    set N := orderOf c / 2 with hNdef
    set c₀ := c ^ N with hc₀def
    have hc₀2 : orderOf c₀ = 2 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hdvd
    have hc₀A : c₀ ∈ A := A.pow_mem hcA N
    have hct : c₀ * t = t * c₀ := by
      have h1 : Commute c t := (hcomm t htT₀ c hcC).symm
      exact (h1.pow_left N).eq
    have hc₀eq : c₀ = (s ^ N)⁻¹ * (s * c) ^ N := by
      rw [(Commute.mul_pow hsc N), inv_mul_cancel_left]
    have hsN : (s ^ N)⁻¹ ∈ Lm := Lm.inv_mem (Lm.pow_mem (hT₀L hsT) N)
    have hscN : (s * c) ^ N ∈ Lj := Lj.pow_mem hscj N
    have hc₀B : c₀ ∈ B := by
      rw [hc₀eq]
      exact B.mul_mem (preimage_le B _ hsN) (preimage_le B _ hscN)
    have hcnorm : ∀ k' : Fin 2, (aschbacherThm5Preimage B (conjFactors D Abar g k')).map
        (MulAut.conj c₀).toMonoidHom = aschbacherThm5Preimage B (conjFactors D Abar g k') :=
      fun k' => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBL k' hc₀B)
    have hF' := hF.mirror hC hii' hc₀A hc₀2 hct hcnorm
    apply hF'.false_of_centralizes_inv_mul hin hC' hjm.symm hnd' hsN
    rw [inv_inv, hc₀eq, mul_inv_cancel_left]
    exact cross_factor_centralizes B (conjFactors D Abar g) hC'.hyp.hcomm m j hjm.symm _ hscN
  ·
    rw [hkm] at hTy
    have hcLm : c ∈ Lm := by
      have h1 := Lm.mul_mem (Lm.inv_mem (hT₀L hsT)) (hTy hs'y)
      rwa [inv_mul_cancel_left] at h1
    exact hF.not_centralizes_conj hin hC (l := j) hcA hctwo hc1 (hcentj c hcLm)

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
