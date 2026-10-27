module

public import CFSG.GH74.Generic.BProg.B3.S1Split
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp
public import CFSG.GH74.Generic.BProg.B3.KG531Red

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Lemma283b

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement MatrixGroups

section SL2

variable {F : Type*} [Field F] [Finite F] {P : Type*} [Group P]

theorem center_cases_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F)) {s z : P}
    (hs : orderOf s = 2) (hz : z ∈ center P) : z = 1 ∨ z = s := by
  have h1 : s = e.symm (-1) :=
    (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e s).1 hs
  have h2 := (CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e z).1 hz
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff (e z)).1 h2 with h | h
  · left
    exact e.injective (by rw [h, map_one])
  · right
    rw [h1]
    exact e.eq_symm_apply.2 h

theorem mem_center_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F)) {s : P}
    (hs : orderOf s = 2) : s ∈ center P := by
  have h1 : s = e.symm (-1) :=
    (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e s).1 hs
  rw [CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e s, h1, MulEquiv.apply_symm_apply]
  exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).2 (Or.inr rfl)

end SL2

section Bar

variable {G : Type} [Group G] [Finite G]

theorem exists_equiv_bar {a : G} {H : Subgroup G} (hHY : H ≤ centralizer ({a} : Set G))
    (hO : pPrimeCoreOf 2 H ≤ pPrimeCoreOf 2 (centralizer ({a} : Set G))) :
    Nonempty ((↥H ⧸ pPrimeCore 2 ↥H) ≃* ↥(PumpCalc.bar a H)) := by
  classical
  let f : ↥H →* ↥(PumpCalc.bar a H) :=
    ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hHY)).codRestrict
      (PumpCalc.bar a H) (fun h => ⟨⟨(h : G), hHY h.2⟩, Subgroup.mem_subgroupOf.2 h.2, rfl⟩)
  have hfs : Function.Surjective f := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩
  have hker : f.ker = pPrimeCore 2 ↥H := by
    have h0 : f.ker = ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hHY)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [h0]
    apply le_antisymm
    · exact S1Split.ker_fK_le a hHY
    · intro o ho
      have hoG : ((o : ↥H) : G) ∈ pPrimeCoreOf 2 H := ⟨o, ho, rfl⟩
      obtain ⟨y, hy, hyo⟩ := hO hoG
      rw [MonoidHom.mem_ker]
      have hy' : Subgroup.inclusion hHY o = y := Subtype.ext hyo.symm
      show barMk ↥(centralizer ({a} : Set G)) (Subgroup.inclusion hHY o) = 1
      rw [hy']
      exact (QuotientGroup.eq_one_iff y).2 hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

theorem ne_of_s1SplitMod {x a : G} {K A J₁ J₂ : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hS : S1SplitMod K A x a J₁ J₂) : a ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hax
  have hKC : K ≤ centralizer ({a} : Set G) := hax ▸ hK.1
  have hK' : IsPCompIn 2 (centralizer ({a} : Set G)) K := hax ▸ hK
  have hinf : K ⊓ centralizer ({a} : Set G) = K := inf_eq_left.2 hKC
  have hsub : (K.subgroupOf (centralizer ({a} : Set G))).IsSubnormal :=
    B1.isSubnormal_of_isPCompIn hK'
  have h₁ : IsPCompIn 2 K J₁ := by
    have h := hS.comp₁
    rwa [hinf] at h
  have h₂ : IsPCompIn 2 K J₂ := by
    have h := hS.comp₂
    rwa [hinf] at h
  have e₁ := FalseCtxS45Comp.eq_of_le (B1.isPCompIn_of_isSubnormal 2 hKC hsub h₁) hK' h₁.1
  have e₂ := FalseCtxS45Comp.eq_of_le (B1.isPCompIn_of_isSubnormal 2 hKC hsub h₂) hK' h₂.1
  exact hS.ne (e₁.trans e₂.symm)

end Bar

end S1Lemma283b

section Lemma283bTable

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup S1Lemma283b
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_lemma283b_of_table (hT : KG531Table) (hc : Ctx21 G x K A a D J)
    {J₁ J₂ : Subgroup G} (hS : S1SplitMod K A x a J₁ J₂) (hJ₂ : J₂ ≤ J)
    (hO₁ : pPrimeCoreOf 2 J₁ ≤ pPrimeCoreOf 2 (centralizer ({a} : Set G)))
    (hO₂ : pPrimeCoreOf 2 J₂ ≤ pPrimeCoreOf 2 (centralizer ({a} : Set G))) : ¬ J₁ ≤ J := by
  classical
  intro hJ₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J := hc.obs.comp
  have ha : orderOf a = 2 := hc.obs.y_ord
  have hax : a ∈ centralizer ({x} : Set G) := hc.src.1 hc.a_mem
  have hxY : x ∈ centralizer ({a} : Set G) := TwoThin.mem_centralizer_symm hax
  have haY : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hane : a ≠ x := ne_of_s1SplitMod hK hS
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hxa_comm : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hxY
  have hxaY : x * a ∈ centralizer ({a} : Set G) := Subgroup.mul_mem _ hxY haY
  have hxa1 : x * a ≠ 1 := by
    intro h
    apply hane
    calc a = x * x * a := by rw [hxx, one_mul]
      _ = x * (x * a) := mul_assoc _ _ _
      _ = x := by rw [h, mul_one]
  have hxa2 : orderOf (x * a) = 2 := by
    refine orderOf_eq_prime ?_ hxa1
    calc (x * a) ^ 2 = x * (a * x) * a := by rw [pow_two]; group
      _ = x * (x * a) * a := by rw [hxa_comm]
      _ = (x * x) * (a * a) := by group
      _ = 1 := by rw [hxx, haa, one_mul]
  have hprod : barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ =
      barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ * barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ :=
    map_mul (barMk ↥(centralizer ({a} : Set G))) ⟨x, hxY⟩ ⟨a, haY⟩
  have hab_cen : ∀ g : barQ ↥(centralizer ({a} : Set G)),
      g * barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ =
        barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ * g := by
    intro g
    obtain ⟨y, rfl⟩ := barMk_surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hab2 : orderOf (barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩) = 2 :=
    TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer haY ha)
  have hxb2 : orderOf (barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩) = 2 :=
    TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hxY hx)
  have ht2 : orderOf (barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩) = 2 :=
    TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hxaY hxa2)
  have hMc : CFSG.IsComponent (PumpCalc.bar a J) := FalseCtxS45Comp.isComponent_bar hJ
  have hGH : GHList (↥(PumpCalc.bar a J) ⧸ center ↥(PumpCalc.bar a J)) :=
    ghList_of_quasisimple hc.hyp.simple hc.hyp.nonab hc.hyp.kgh ha hMc.1
  obtain ⟨F, _, _, hodd, hF5, ⟨q₁⟩, ⟨q₂⟩⟩ := hS.sl2
  have hoddN : Odd (Nat.card F) := by rwa [Nat.card_eq_fintype_card]
  have h4 : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card]; omega
  have hJ₁Y : J₁ ≤ centralizer ({a} : Set G) := hS.comp₁.1.trans inf_le_right
  have hJ₂Y : J₂ ≤ centralizer ({a} : Set G) := hS.comp₂.1.trans inf_le_right
  obtain ⟨b₁⟩ := exists_equiv_bar hJ₁Y hO₁
  obtain ⟨b₂⟩ := exists_equiv_bar hJ₂Y hO₂
  have e₁ : ↥(PumpCalc.bar a J₁) ≃* SL(2, F) := b₁.symm.trans q₁
  have e₂ : ↥(PumpCalc.bar a J₂) ≃* SL(2, F) := b₂.symm.trans q₂
  have haL₁ : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ ∈ PumpCalc.bar a J₁ :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.2 hS.u_mem, rfl⟩
  have haM : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ ∈ PumpCalc.bar a J :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.2 (hJ₁ hS.u_mem), rfl⟩
  have htL₂ : barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ ∈ PumpCalc.bar a J₂ :=
    ⟨⟨x * a, hxaY⟩, Subgroup.mem_subgroupOf.2 hS.xu_mem, rfl⟩
  have htM : barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ ∈ PumpCalc.bar a J :=
    ⟨⟨x * a, hxaY⟩, Subgroup.mem_subgroupOf.2 (hJ₂ hS.xu_mem), rfl⟩
  have hcen₁ : ∀ z ∈ center ↥(PumpCalc.bar a J₁),
      (z : barQ ↥(centralizer ({a} : Set G))) = 1 ∨
        (z : barQ ↥(centralizer ({a} : Set G))) = barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ := by
    intro z hz
    have hs : orderOf (⟨_, haL₁⟩ : ↥(PumpCalc.bar a J₁)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hab2
    rcases center_cases_of_equiv_sl2 hoddN e₁ hs hz with h | h
    · left; simpa using congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  have hs₂ : orderOf (⟨_, htL₂⟩ : ↥(PumpCalc.bar a J₂)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht2
  have hcen₂ : ∀ z ∈ center ↥(PumpCalc.bar a J₂),
      (z : barQ ↥(centralizer ({a} : Set G))) = 1 ∨
        (z : barQ ↥(centralizer ({a} : Set G))) =
          barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ := by
    intro z hz
    rcases center_cases_of_equiv_sl2 hoddN e₂ hs₂ hz with h | h
    · left; simpa using congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  have htZ : (⟨_, htL₂⟩ : ↥(PumpCalc.bar a J₂)) ∈ center ↥(PumpCalc.bar a J₂) :=
    mem_center_of_equiv_sl2 hoddN e₂ hs₂
  have hcomm : ∀ g ∈ PumpCalc.bar a J₁, ∀ h ∈ PumpCalc.bar a J₂, g * h = h * g := by
    rintro _ ⟨j₁, hj₁, rfl⟩ _ ⟨j₂, hj₂, rfl⟩
    have hmem := hS.commute (j₁ : G) (Subgroup.mem_subgroupOf.1 hj₁) (j₂ : G)
      (Subgroup.mem_subgroupOf.1 hj₂)
    obtain ⟨y, hy, hye⟩ := hO₁ hmem.1
    have hyc : y = ⁅j₁, j₂⁆ := Subtype.ext hye
    have h1 : barMk ↥(centralizer ({a} : Set G)) ⁅j₁, j₂⁆ = 1 := by
      rw [← hyc]
      exact (QuotientGroup.eq_one_iff y).2 hy
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hdisj : PumpCalc.bar a J₁ ⊓ PumpCalc.bar a J₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg₁, hg₂⟩
    rw [Subgroup.mem_bot]
    have hz₁ : (⟨g, hg₁⟩ : ↥(PumpCalc.bar a J₁)) ∈ center ↥(PumpCalc.bar a J₁) := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcomm l l.2 g hg₂)
    have hz₂ : (⟨g, hg₂⟩ : ↥(PumpCalc.bar a J₂)) ∈ center ↥(PumpCalc.bar a J₂) := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcomm g hg₁ l l.2).symm
    rcases hcen₁ _ hz₁ with h | h
    · exact h
    · exfalso
      rcases hcen₂ _ hz₂ with h' | h'
      · have h3 : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ = 1 := h.symm.trans h'
        rw [h3, orderOf_one] at hab2
        omega
      · have h3 : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ =
            barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ := h.symm.trans h'
        have h4' : barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ = 1 :=
          mul_right_cancel (b := barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩)
            (by rw [one_mul, ← hprod, ← h3])
        rw [h4', orderOf_one] at hxb2
        omega
  have hZ : (center ↥(PumpCalc.bar a J₁)).map (PumpCalc.bar a J₁).subtype ≤
      (center ↥(PumpCalc.bar a J)).map (PumpCalc.bar a J).subtype := by
    rintro _ ⟨z, hz, rfl⟩
    show (z : barQ ↥(centralizer ({a} : Set G))) ∈ _
    rcases hcen₁ z hz with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact ⟨⟨_, haM⟩, Subgroup.mem_center_iff.2 fun m =>
        Subtype.ext (hab_cen (m : barQ ↥(centralizer ({a} : Set G)))), rfl⟩
  have hLC : ∀ {Ji : Subgroup G}, Ji ≤ K ⊓ centralizer ({a} : Set G) → Ji ≤ J →
      PumpCalc.bar a Ji ≤ centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩} :
        Set (barQ ↥(centralizer ({a} : Set G)))) ⊓ PumpCalc.bar a J := by
    intro Ji hJiK hJiJ
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      ⟨j, Subgroup.mem_subgroupOf.2 (hJiJ (Subgroup.mem_subgroupOf.1 hj)), rfl⟩⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hjK : (j : G) ∈ K := (hJiK (Subgroup.mem_subgroupOf.1 hj)).1
    have hjx : (j : G) * x = x * (j : G) := Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hjK)
    have hja : (j : G) * a = a * (j : G) := Subgroup.mem_centralizer_singleton_iff.1 j.2
    show (j : G) * (x * a) = x * a * (j : G)
    calc (j : G) * (x * a) = ((j : G) * x) * a := (mul_assoc _ _ _).symm
      _ = (x * (j : G)) * a := by rw [hjx]
      _ = x * ((j : G) * a) := mul_assoc _ _ _
      _ = x * (a * (j : G)) := by rw [hja]
      _ = x * a * (j : G) := (mul_assoc _ _ _).symm
  have hL₁C := hLC hS.comp₁.1 hJ₁
  have hL₂C := hLC hS.comp₂.1 hJ₂
  have hCt : centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩} :
        Set (barQ ↥(centralizer ({a} : Set G)))) ⊓ PumpCalc.bar a J ≤
      centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩} :
        Set (barQ ↥(centralizer ({a} : Set G)))) := by
    intro g hg
    have hg1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1
    rw [hprod] at hg1
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply mul_right_cancel (b := barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩)
    calc g * barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ *
          barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩
        = g * (barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ *
          barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩) := mul_assoc _ _ _
      _ = barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ *
          barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ * g := hg1
      _ = barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ *
          (barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ * g) := mul_assoc _ _ _
      _ = barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ *
          (g * barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩) := by rw [hab_cen g]
      _ = barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ * g *
          barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ := (mul_assoc _ _ _).symm
  have hsub : ∀ {Ji : Subgroup G}, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) Ji →
      ((PumpCalc.bar a Ji).subgroupOf
        (centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩} :
          Set (barQ ↥(centralizer ({a} : Set G)))))).IsSubnormal := by
    intro Ji hJi
    have hsubK : ((K ⊓ centralizer ({a} : Set G)).subgroupOf
        (centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G))).IsSubnormal :=
      B1.isSubnormal_subgroupOf_inf (S := centralizer ({a} : Set G)) (B1.isSubnormal_of_isPCompIn hK)
    have hW : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G)) Ji :=
      B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsubK hJi
    have hT₁ := TwoThin.isTwoComponent_map_barMk (TwoThin.orderOf_mk_centralizer hxY hx)
      (TwoThin.le_centralizer_mk hW.1 hxY) (TwoThin.isTwoComponent_centralizer_mk hW hxY)
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hT₁.1
      Subgroup.IsSubnormal.top
  have hsub₁ := CFSG.ComponentClassification.CatalogueBPrimeJoin.subgroupOf_isSubnormal_of_le hCt
    (hsub hS.comp₁)
  have hsub₂ := CFSG.ComponentClassification.CatalogueBPrimeJoin.subgroupOf_isSubnormal_of_le hCt
    (hsub hS.comp₂)
  have hq₁ := B1.PilotS3.isQuasisimple_of_equiv_sl2 h4 ((Subgroup.subgroupOfEquivOfLe hL₁C).trans e₁)
  have hq₂ := B1.PilotS3.isQuasisimple_of_equiv_sl2 h4 ((Subgroup.subgroupOfEquivOfLe hL₂C).trans e₂)
  exact kg_531a_of_table hT hMc.1 hGH ht2 htM hL₁C hL₂C ⟨hq₁, hsub₁⟩ ⟨hq₂, hsub₂⟩
    ⟨⟨_, htL₂⟩, htZ, rfl⟩ hcomm hdisj hodd hF5 ⟨e₁⟩ ⟨e₂⟩ hZ

end Lemma283bTable

end CFSG.GH74.Generic.BProg.B3
