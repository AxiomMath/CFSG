module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeComp
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveGoldCore
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.Goldschmidt.Steps.G37Core

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools

variable {C : Type} [Group C] [Finite C]

theorem eq_top_of_eleven
    (hGold : Asc76X.GoldschmidtTheoremA) (T : Sylow 2 C) {E : Subgroup C}
    (hET : E ≤ T) (hE2 : ∀ e ∈ E, e * e = 1) (hEc : Nat.card E = 2 ^ 11)
    (hcl : fusionStronglyClosed (E : Set C) (T : Subgroup C)) {x u : C}
    (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hx11 : ∀ e ∈ E, x ^ 11 * e * (x ^ 11)⁻¹ = e)
    (huE : u ∈ E) (hu : ∀ e ∈ E, x * e * x⁻¹ = e ↔ e = 1 ∨ e = u) {ea eb : C}
    (hea : ea ∈ E) (heb : eb ∈ E) (ha1 : ea * (x * ea * x⁻¹) ≠ 1)
    (hb1 : eb * (x * eb * x⁻¹) ≠ 1) (hab : ¬ IsConj (ea * (x * ea * x⁻¹)) (eb * (x * eb * x⁻¹)))
    (habu : ¬ IsConj (ea * (x * ea * x⁻¹)) (eb * (x * eb * x⁻¹) * u)) {H : Subgroup C}
    (hEH : E ≤ H) (hNH : normalizer (E : Set C) ≤ H) {f₁ f₂ : C} (hf₁ : f₁ ∈ E) (hf₂ : f₂ ∈ E)
    (hf₁1 : f₁ ≠ 1) (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₁ ≠ f₂)
    (hF : ∀ f, f = f₁ ∨ f = f₂ ∨ f = f₁ * f₂ → centralizer ({f} : Set C) ≤ H) :
    H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE2 a ha)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE2 b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hE2 _ (E.mul_mem ha hb))).symm
      _ = b * a := by rw [mul_inv_rev, hai, hbi]
  have hQab : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEab _ a.2 _ b.2)⟩⟩
  have hIH : IH (Nat.card C + 1) := fun Z _ _ _ =>
    coreStatement_iff.mp (RankTwoAltFive.coreStatement_of_goldschmidtTheoremA hGold) Z
  have hTsyl : fusionIsSylowIn 2 (T : Subgroup C) ⊤ :=
    ⟨le_top, T.isPGroup', fun P' _ hP' hTP => T.is_maximal' hP' hTP⟩
  obtain ⟨hConc, hC1, -, hC3, hC4⟩ := N16_of N1 _ hIH C T E ⊤ T hET hQab hcl hET hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup C := normalClosureIn ⊤ E with hMdef
  have hMeq : M = normalClosure (E : Set C) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact mem_subgroupOf.1 hy'
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hEM : E ≤ M := by
    rw [hMeq]
    exact le_normalClosure
  suffices hgoal : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ by
    obtain ⟨hMO, -⟩ := hC4 hgoal
    have hOH : oddCoreOf M ≤ H := by
      have hf₁2 : f₁ ^ 2 = 1 := by rw [sq]; exact hE2 _ hf₁
      have hf₂2 : f₂ ^ 2 = 1 := by rw [sq]; exact hE2 _ hf₂
      have hFN : zpowers f₂ ≤ normalizer (zpowers f₁ : Set C) :=
        zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => by
          rcases G37.eq_one_or_eq_of_mem_zpowers hf₁2 hy with rfl | rfl
          · rw [one_mul, mul_one]
          · exact hEab _ hf₁ _ hf₂))
      have hFE : zpowers f₁ ⊔ zpowers f₂ ≤ E := sup_le (zpowers_le.mpr hf₁) (zpowers_le.mpr hf₂)
      have hFel : IsElemAbelian 2 (zpowers f₁ ⊔ zpowers f₂) :=
        ⟨⟨⟨fun a b => Subtype.ext (hEab _ (hFE a.2) _ (hFE b.2))⟩⟩, fun a ha => by
          rw [sq]
          exact hE2 _ (hFE ha)⟩
      have hdisj : zpowers f₁ ⊓ zpowers f₂ = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hy₁, hy₂⟩
        rcases G37.eq_one_or_eq_of_mem_zpowers hf₁2 hy₁ with rfl | rfl
        · exact one_mem _
        · rcases G37.eq_one_or_eq_of_mem_zpowers hf₂2 hy₂ with h | h
          · exact absurd h hf₁1
          · exact absurd h hf₁₂
      have hF4 : 2 ^ 2 ≤ Nat.card (zpowers f₁ ⊔ zpowers f₂ : Subgroup C) := by
        rw [AS76b.card_sup_eq_mul hFN hdisj, Nat.card_zpowers, Nat.card_zpowers,
          orderOf_eq_prime hf₁2 hf₁1, orderOf_eq_prime hf₂2 hf₂1]
        norm_num
      have hON : zpowers f₁ ⊔ zpowers f₂ ≤ normalizer ((oddCoreOf M : Subgroup C) : Set C) :=
        hFE.trans (hEM.trans (AS76b.le_normalizer_map_subtype_of_normal M _))
      have hOodd : Nat.Coprime 2 (Nat.card (oddCoreOf M)) := by
        rw [oddCoreOf, card_map_of_injective M.subtype_injective]
        exact Nat.coprime_two_left.mpr (odd_card_goldschmidtOddCore ↥M)
      rw [← CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hFel
        hF4 hON hOodd]
      refine iSup_le fun f => iSup_le fun hf => iSup_le fun hf1 => inf_le_right.trans (hF f ?_)
      obtain ⟨a, ha, b, hb, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hFN hf
      rcases G37.eq_one_or_eq_of_mem_zpowers hf₁2 ha with rfl | rfl <;>
        rcases G37.eq_one_or_eq_of_mem_zpowers hf₂2 hb with rfl | rfl
      · exact absurd (one_mul (1 : C)) hf1
      · exact Or.inr (Or.inl (one_mul _))
      · exact Or.inl (mul_one _)
      · exact Or.inr (Or.inr rfl)
    rw [eq_top_iff, ← hC1]
    exact sup_le ((le_of_eq hMO).trans (sup_le hOH hEH)) (inf_le_right.trans hNH)
  set π := QuotientGroup.mk' (goldschmidtOddCore ↥M) with hπ
  have hOM := odd_card_goldschmidtOddCore ↥M
  have hπE : ∀ m₁ m₂ : M, (m₁ : C) ∈ E → (m₂ : C) ∈ E → π m₁ = π m₂ → m₁ = m₂ := by
    intro m₁ m₂ h₁ h₂ he
    have hk : m₁⁻¹ * m₂ ∈ goldschmidtOddCore ↥M := by
      rw [← QuotientGroup.ker_mk' (goldschmidtOddCore ↥M), MonoidHom.mem_ker, map_mul, map_inv,
        he, inv_mul_cancel]
    have hE' : ((m₁⁻¹ * m₂ : M) : C) ∈ E := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact E.mul_mem (E.inv_mem h₁) h₂
    have h2 : (m₁⁻¹ * m₂) * (m₁⁻¹ * m₂) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hE2 _ hE')
    have hodd : Odd (orderOf (m₁⁻¹ * m₂)) := hOM.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
    have hdvd : orderOf (m₁⁻¹ * m₂) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (T : Subgroup C).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hPM, subgroupOf_map_subtype]
  have hEPM : E.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun y hy => mem_subgroupOf.2 (hET (mem_subgroupOf.1 hy))
  have hclM := stronglyClosed_subgroupOf T hcl hEM PM hEPM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (E.subgroupOf M) (goldschmidtOddCore M) hEPM hclM
  set Ab := (E.subgroupOf M).map π with hAb
  have hASbar : Ab ≤ Sbar := by
    rw [hSbar]
    exact map_mono hEPM
  have hAab : IsMulCommutative Ab := isMulCommutative_map (isMulCommutative_subgroupOf hQab M) π
  have hO' : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot M
  have hSbarT : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) = barOf M T := by
    rw [hSbar, hPMeq]
    rfl
  have hopen : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), IsComponentOf K.1 ⊤ :=
    fun K => (CFSG.isComponent_iff_open K.1).mp K.2
  have htype : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M),
      goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K => hConc.2.2 K.1 (hopen K)
  have hind : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), InducesOmega1 Ab K.1 Sbar :=
    fun K => by
      rw [hSbarT]
      exact hC3 K.1 (hopen K)
  have hcover : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), ∀ a ∈ Ab, ∃ y ∈ Ab ⊓ K.1,
      ∀ w ∈ K.1, a⁻¹ * w * a = y⁻¹ * w * y :=
    fun K => N17_of N11b _ Sbar Ab K.1 hASbar hAab hclbar hO' (hopen K) (htype K) (hind K)
  have hA2 : ∀ a ∈ Ab, a * a = 1 := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_one π]
    congr 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hE2 _ (mem_subgroupOf.mp hq))
  have hAc : Nat.card Ab = 2 ^ 11 := by
    have hinj : Function.Injective (π.comp (E.subgroupOf M).subtype) := fun a b hab =>
      Subtype.ext (hπE _ _ (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2) hab)
    have h1 : Ab = (π.comp (E.subgroupOf M).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv, hEc]
  set σ := Asc76X.conjQuot hMn x with hσ
  have hσmk : ∀ m : M, σ (π m) = π ⟨x * m * x⁻¹, hMn.conj_mem m m.2 x⟩ := fun m =>
    Asc76X.conjQuot_mk hMn x m
  have hσpow : ∀ n : ℕ, σ ^ n = Asc76X.conjQuot hMn (x ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Asc76X.conjQuot_one]
    | succ n ih => rw [pow_succ, pow_succ, ih, Asc76X.conjQuot_mul]
  have hσA : ∀ y ∈ Ab, σ y ∈ Ab := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hσmk]
    exact ⟨_, mem_subgroupOf.mpr (hxE _ (mem_subgroupOf.mp hq)), rfl⟩
  have hσ11 : ∀ y ∈ Ab, (σ ^ 11) y = y := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hσpow, Asc76X.conjQuot_mk]
    congr 1
    exact Subtype.ext (hx11 _ (mem_subgroupOf.mp hq))
  have huM : u ∈ M := hEM huE
  have hu' : ∀ y ∈ Ab, σ y = y ↔ y = 1 ∨ y = π ⟨u, huM⟩ := by
    rintro _ ⟨q, hq, rfl⟩
    have hqE : (q : C) ∈ E := mem_subgroupOf.mp hq
    rw [hσmk]
    constructor
    · intro h
      have h1 := hπE _ _ (hxE _ hqE) hqE h
      rcases (hu _ hqE).mp (congrArg Subtype.val h1) with h3 | h3
      · left
        rw [show q = 1 from Subtype.ext h3, map_one]
      · right
        congr 1
        exact Subtype.ext h3
    · rintro (h | h)
      · obtain rfl : q = 1 := hπE q 1 hqE E.one_mem (by rw [h, map_one])
        congr 1
        exact Subtype.ext (by simp)
      · obtain rfl : q = ⟨u, huM⟩ := hπE _ _ hqE huE h
        congr 1
        exact Subtype.ext ((hu u huE).mpr (Or.inr rfl))
  have hwmk : ∀ (e : C) (he : e ∈ E), π ⟨e, hEM he⟩ * σ (π ⟨e, hEM he⟩) =
      π ⟨e * (x * e * x⁻¹), hEM (E.mul_mem he (hxE e he))⟩ := fun e he => by
    rw [hσmk, ← map_mul]
    rfl
  have hmemA : ∀ (e : C) (he : e ∈ E), π ⟨e, hEM he⟩ ∈ Ab := fun e he =>
    ⟨⟨e, hEM he⟩, mem_subgroupOf.mpr he, rfl⟩
  have hne : ∀ (e : C) (he : e ∈ E), e * (x * e * x⁻¹) ≠ 1 →
      π ⟨e, hEM he⟩ * σ (π ⟨e, hEM he⟩) ≠ 1 := fun e he h1 h => by
    rw [hwmk e he, ← map_one π] at h
    exact h1 (congrArg Subtype.val (hπE _ 1 (E.mul_mem he (hxE e he)) E.one_mem h))
  have hlift : ∀ s t : M, s * s = 1 → t * t = 1 → IsConj (π s) (π t) → IsConj (s : C) t := by
    intro s t hs ht h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M) c
    have hk : m * s * m⁻¹ * t ∈ goldschmidtOddCore ↥M := by
      rw [← QuotientGroup.ker_mk' (goldschmidtOddCore ↥M), MonoidHom.mem_ker, map_mul, map_mul,
        map_mul, map_inv, hc, ← map_mul, ht, map_one]
    have hs' : m * s * m⁻¹ * (m * s * m⁻¹) = 1 := by
      rw [show m * s * m⁻¹ * (m * s * m⁻¹) = m * (s * s) * m⁻¹ by group, hs, mul_one,
        mul_inv_cancel]
    have h1 : IsConj s t := (isConj_iff.mpr ⟨m, rfl⟩).trans
      (CFSG.ShultStronglyClosedTI.InvolutionCounting.isConj_of_odd_orderOf_mul hs' ht
        (hOM.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)))
    obtain ⟨c', hc'⟩ := isConj_iff.mp h1
    exact isConj_iff.mpr ⟨(c' : C), congrArg Subtype.val hc'⟩
  have hsq : ∀ (e : C) (he : e ∈ E), (⟨e, hEM he⟩ : M) * ⟨e, hEM he⟩ = 1 := fun e he =>
    Subtype.ext (hE2 e he)
  have hab' : ¬ IsConj (π ⟨ea, hEM hea⟩ * σ (π ⟨ea, hEM hea⟩))
      (π ⟨eb, hEM heb⟩ * σ (π ⟨eb, hEM heb⟩)) := by
    rw [hwmk ea hea, hwmk eb heb]
    have hwa : ea * (x * ea * x⁻¹) ∈ E := E.mul_mem hea (hxE ea hea)
    have hwb : eb * (x * eb * x⁻¹) ∈ E := E.mul_mem heb (hxE eb heb)
    exact fun h => hab (hlift _ _ (hsq _ hwa) (hsq _ hwb) h)
  have habu' : ¬ IsConj (π ⟨ea, hEM hea⟩ * σ (π ⟨ea, hEM hea⟩))
      (π ⟨eb, hEM heb⟩ * σ (π ⟨eb, hEM heb⟩) * π ⟨u, huM⟩) := by
    rw [hwmk ea hea, hwmk eb heb, ← map_mul]
    have hwa : ea * (x * ea * x⁻¹) ∈ E := E.mul_mem hea (hxE ea hea)
    have hbu : eb * (x * eb * x⁻¹) * u ∈ E := E.mul_mem (E.mul_mem heb (hxE eb heb)) huE
    exact fun h => habu (hlift _ (⟨_, hEM hbu⟩ : M) (hsq _ hwa) (hsq _ hbu) h)
  have hempty := isEmpty_componentIndex_of_eleven Sbar hO' hASbar hA2 hAc hclbar htype hind hcover
    σ hσA hσ11 hu' (hmemA ea hea) (hmemA eb heb) (hne ea hea ha1) (hne eb heb hb1) hab' habu'
  rw [goldschmidtLayer, sSup_eq_bot]
  intro K hK
  exact (hempty.false ⟨K, (CFSG.isComponent_iff_open K).mpr hK⟩).elim

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
