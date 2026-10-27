module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeFusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoCData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoCGold
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoCLift
import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1TwoCDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

theorem co1TwoCControl
    : Co1TwoCControl := by
  intro X _ _ L ψ hψ hZ hCL z hz hz2 hzc huniq u hu hu2 hcu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Co1TwoCSetting L ψ z := ⟨hψ, hCL, hz, hz2, hzc, huniq⟩
  set N := normalizer (L : Set X) with hNdef
  set K := centralizer ({u} : Set X) with hKdef
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have hdata := co1_twoC_data (AS81.orderOf_actionHom hψ hCL (r := ⟨u, le_normalizer hu⟩) hu2)
    hcu
  obtain ⟨E₀, p₀, ea₀, eb₀, ef₀, hvE₀, hE₀2, hE₀c, hE₀card, hE₀n, hp₀v, hp₀11, hp₀fix, hea₀,
    heb₀, hef₀, hwb₀1, hcls⟩ := hdata
  obtain ⟨ha₀, hf₀, haf₀, hb₀, hbu₀⟩ := hcls _ (AS81.orderOf_actionHom hψ hCL hz2) hzc
  obtain ⟨E, x, ea, eb, ef, hEL, huE, hE2, hEcard, hEn, hxL, hxu, hxE, hx11, hfix, hea, heb, hef,
    ⟨la, hla, hwa⟩, ⟨lf, hlf, hwf⟩, ⟨laf, hlaf, hwaf⟩, hwb1, hnb, hnbu⟩ :=
    twoC_lift hψ hZ hz hzz huniq hu huu hvE₀ hE₀2 hE₀c hE₀card hE₀n hp₀v
      (by rw [← hp₀11, pow_orderOf_eq_one]) hp₀fix hea₀ heb₀ hef₀ hwb₀1 ha₀ hf₀ haf₀ hb₀ hbu₀
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE2 a ha)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE2 b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hE2 _ (E.mul_mem ha hb))).symm
      _ = b * a := by rw [mul_inv_rev, hai, hbi]
  have hEK : E ≤ K := fun e he => mem_centralizer_singleton_iff.mpr (hEab _ he _ huE)
  have hE2g : IsPGroup 2 E := IsPGroup.of_card (n := 11) (hEcard.trans (by norm_num))
  have hEnorm : ∀ c ∈ N, c * u = u * c → c ∈ normalizer (E : Set X) := by
    intro c hc hcu
    rw [mem_normalizer_iff]
    intro e
    refine ⟨hEn c hc hcu e, fun he => ?_⟩
    have hci : c⁻¹ * u = u * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcu, mul_inv_cancel_right]
    have h1 := hEn c⁻¹ (inv_mem hc) hci _ he
    rwa [show c⁻¹ * (c * e * c⁻¹) * c⁻¹⁻¹ = e by group] at h1
  obtain ⟨T₀, hT₀⟩ := exists_isSylowOf 2 (N ⊓ K)
  have hT₀K := h.isSylowOf_centralizer hu hu2 hT₀
  have hET₀ : E ≤ T₀ := by
    have hT₀N : T₀ ≤ normalizer (E : Set X) := fun t ht => by
      obtain ⟨htN, htK⟩ := mem_inf.mp (hT₀.le ht)
      exact hEnorm t htN (mem_centralizer_singleton_iff.mp htK)
    have heq := hT₀.eq_of_le le_sup_right
      (sup_le (le_inf (hEL.trans le_normalizer) hEK) hT₀.le)
      (IsPGroup.to_sup_of_normal_left' hE2g hT₀.isPGroup hT₀N)
    rw [← heq]
    exact le_sup_left
  have hT₀L : T₀ ≤ L := h.le_of_isPGroup (hT₀.le.trans inf_le_left) hT₀.isPGroup
  have hclX : ∀ e ∈ E, ∀ k ∈ K, k⁻¹ * e * k ∈ T₀ → k⁻¹ * e * k ∈ E := by
    intro e he k hk hke
    have hku : k * u = u * k := mem_centralizer_singleton_iff.mp hk
    have hPE : zpowers e ⊔ zpowers u ≤ E := sup_le (zpowers_le.mpr he) (zpowers_le.mpr huE)
    have hku' : k⁻¹ * u * k = u := by
      rw [mul_assoc, ← hku, inv_mul_cancel_left]
    obtain ⟨c, hcN, hc⟩ := h.exists_realize (hPE.trans hEL) (hE2g.to_le hPE) (g := k) (by
      rw [map_le_iff_le_comap]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · show (MulAut.conj k⁻¹) e ∈ L
        rw [MulAut.conj_apply, inv_inv]
        exact hT₀L hke
      · show (MulAut.conj k⁻¹) u ∈ L
        rw [MulAut.conj_apply, inv_inv, hku']
        exact hu)
    have hcu : c⁻¹ * u * c = u := by
      rw [hc u (mem_sup_right (mem_zpowers u)), hku']
    have hcu' : c⁻¹ * u = u * c⁻¹ := by
      calc c⁻¹ * u = c⁻¹ * u * c * c⁻¹ := by group
        _ = u * c⁻¹ := by rw [hcu]
    have h1 := hEn c⁻¹ (inv_mem hcN) hcu' e he
    rw [inv_inv, hc e (mem_sup_left (mem_zpowers e))] at h1
    exact h1
  obtain ⟨T, hT⟩ := hT₀K
  have hmemT : ∀ y : K, y ∈ (T : Subgroup K) ↔ (y : X) ∈ T₀ := by
    intro y
    constructor
    · intro hy
      rw [← hT]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hT] at hy
      obtain ⟨y', hy', he⟩ := hy
      rwa [← Subtype.ext he]
  have hxK : x ∈ K := mem_centralizer_singleton_iff.mpr hxu
  have hmemE : ∀ y : K, y ∈ E.subgroupOf K ↔ (y : X) ∈ E := fun y => mem_subgroupOf
  have hconjz : ∀ {w l : X}, l ∈ L → w = l * z * l⁻¹ → w ≠ 1 := by
    rintro w l - rfl h1
    have hz1 : z ≠ 1 := fun h2 => by
      rw [h2, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    apply hz1
    calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
      _ = 1 := by rw [h1]; group
  have hwaE : ea * (x * ea * x⁻¹) ∈ E := E.mul_mem hea (hxE ea hea)
  have hwfE : ef * (x * ef * x⁻¹) ∈ E := E.mul_mem hef (hxE ef hef)
  have hNK : normalizer (E : Set X) ≤ N := h.normalizer_le_of_conj_mem hEL (g := la) (by
    rw [← hwa]
    exact hwaE)
  have hCN : ∀ {w l : X}, l ∈ L → w = l * z * l⁻¹ → centralizer ({w} : Set X) ≤ N := by
    rintro w l hl rfl
    exact h.centralizer_conj_le (L.mul_mem (L.mul_mem hl hz) (L.inv_mem hl))
  have key := eq_top_of_eleven Asc76X.goldschmidtTheoremA T (E := E.subgroupOf K)
    (fun y hy => (hmemT y).mpr (hET₀ ((hmemE y).mp hy)))
    (fun y hy => Subtype.ext (hE2 _ ((hmemE y).mp hy)))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]; exact hEcard)
    (fun y hy g hg => (hmemE _).mpr (hclX _ ((hmemE y).mp hy) _ g.2 ((hmemT _).mp hg)))
    (x := ⟨x, hxK⟩) (u := ⟨u, mem_centralizer_singleton_iff.mpr rfl⟩)
    (fun y hy => (hmemE _).mpr (hxE _ ((hmemE y).mp hy)))
    (fun y hy => Subtype.ext (hx11 _ ((hmemE y).mp hy)))
    ((hmemE _).mpr huE)
    (fun y hy => by
      have h1 := hfix _ ((hmemE y).mp hy)
      constructor
      · intro h2
        rcases h1.mp (congrArg Subtype.val h2) with h3 | h3
        · exact Or.inl (Subtype.ext h3)
        · exact Or.inr (Subtype.ext h3)
      · intro h2
        apply Subtype.ext
        exact h1.mpr (h2.imp (congrArg Subtype.val) (congrArg Subtype.val)))
    (ea := ⟨ea, hEK hea⟩) (eb := ⟨eb, hEK heb⟩) ((hmemE _).mpr hea) ((hmemE _).mpr heb)
    (fun h1 => hconjz hla hwa (congrArg Subtype.val h1))
    (fun h1 => hwb1 (congrArg Subtype.val h1))
    (fun h1 => hnb ((isConj_iff.mpr ⟨la, hwa.symm⟩).trans (by
      obtain ⟨c, hc⟩ := isConj_iff.mp h1
      exact isConj_iff.mpr ⟨(c : X), congrArg Subtype.val hc⟩)))
    (fun h1 => hnbu ((isConj_iff.mpr ⟨la, hwa.symm⟩).trans (by
      obtain ⟨c, hc⟩ := isConj_iff.mp h1
      exact isConj_iff.mpr ⟨(c : X), congrArg Subtype.val hc⟩)))
    (H := N.subgroupOf K)
    (fun y hy => mem_subgroupOf.mpr (le_normalizer (hEL ((hmemE y).mp hy))))
    (fun g hg => by
      refine mem_subgroupOf.mpr (hNK ?_)
      rw [mem_normalizer_iff]
      intro e
      constructor
      · intro he
        have h1 := (mem_normalizer_iff.mp hg ⟨e, hEK he⟩).mp ((hmemE _).mpr he)
        exact (hmemE _).mp h1
      · intro he
        have heK : e ∈ K := by
          have h2 : (g : X)⁻¹ * ((g : X) * e * (g : X)⁻¹) * g ∈ K :=
            K.mul_mem (K.mul_mem (K.inv_mem g.2) (hEK he)) g.2
          rwa [show (g : X)⁻¹ * ((g : X) * e * (g : X)⁻¹) * g = e by group] at h2
        have h1 := (mem_normalizer_iff.mp hg ⟨e, heK⟩).mpr ((hmemE _).mpr he)
        exact (hmemE _).mp h1)
    (f₁ := ⟨_, hEK hwaE⟩) (f₂ := ⟨_, hEK hwfE⟩) ((hmemE _).mpr hwaE) ((hmemE _).mpr hwfE)
    (fun h1 => hconjz hla hwa (congrArg Subtype.val h1))
    (fun h1 => hconjz hlf hwf (congrArg Subtype.val h1))
    (fun h1 => hconjz hlaf hwaf (by
      have h2 : ea * (x * ea * x⁻¹) = ef * (x * ef * x⁻¹) := congrArg Subtype.val h1
      rw [h2]
      exact hE2 _ hwfE))
    (fun f hf g hg => by
      refine mem_subgroupOf.mpr ?_
      have hgf : (g : X) ∈ centralizer ({(f : X)} : Set X) :=
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (mem_centralizer_singleton_iff.mp hg))
      rcases hf with rfl | rfl | rfl
      · exact hCN hla hwa hgf
      · exact hCN hlf hwf hgf
      · exact hCN hlaf hwaf hgf)
  intro g hg
  have hg' : (⟨g, hg⟩ : K) ∈ N.subgroupOf K := by
    rw [key]
    exact mem_top _
  exact mem_subgroupOf.mp hg'

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
