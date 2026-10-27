module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma283bCore

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup S1Lemma283b
open scoped commutatorElement MatrixGroups

@[expose] def KG531BCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), CFSG.IsQuasisimple ↥M →
    GHList (↥M ⧸ center ↥M) → pPrimeCore 2 ↥M = ⊥ → ∀ t ∈ M, orderOf t = 2 →
    ∀ L : Subgroup X, IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L →
    ∀ (F : Type) [Field F] [Fintype F], Odd (Fintype.card F) → 5 ≤ Fintype.card F →
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) → pPrimeCoreOf 2 L = ⊥

@[expose] def KG531BPair : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), CFSG.IsQuasisimple ↥M →
    GHList (↥M ⧸ center ↥M) → pPrimeCore 2 ↥M = ⊥ → ∀ t ∈ M, orderOf t = 2 →
    ∀ L₁ L₂ : Subgroup X, IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₁ →
    IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₂ →
    ∀ s ∈ L₁, orderOf s = 2 → s ∈ (center ↥M).map M.subtype → t ∈ L₂ →
    ∀ (F : Type) [Field F] [Fintype F], Odd (Fintype.card F) → 5 ≤ Fintype.card F →
    Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, F)) →
    Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, F)) →
    pPrimeCoreOf 2 L₁ = ⊥ ∧ pPrimeCoreOf 2 L₂ = ⊥

section Bridge

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem bar_data (hc : Ctx21 G x K A a D J) {Ji : Subgroup G}
    (hJi : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) Ji) (hJiJ : Ji ≤ J)
    (hxaY : x * a ∈ centralizer ({a} : Set G))
    {F : Type} [Field F] [Fintype F] (eq : ↥Ji ⧸ pPrimeCore 2 ↥Ji ≃* SL(2, F)) :
    IsPCompIn 2 (centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩} :
        Set (barQ ↥(centralizer ({a} : Set G)))) ⊓ PumpCalc.bar a J) (PumpCalc.bar a Ji) ∧
      Nonempty (↥(PumpCalc.bar a Ji) ⧸ pPrimeCore 2 ↥(PumpCalc.bar a Ji) ≃* SL(2, F)) ∧
      (pPrimeCoreOf 2 (PumpCalc.bar a Ji) = ⊥ →
        pPrimeCoreOf 2 Ji ≤ pPrimeCoreOf 2 (centralizer ({a} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hax : a ∈ centralizer ({x} : Set G) := hc.src.1 hc.a_mem
  have hxY : x ∈ centralizer ({a} : Set G) := TwoThin.mem_centralizer_symm hax
  have haY : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
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
  have hJiY : Ji ≤ centralizer ({a} : Set G) := hJi.1.trans inf_le_right
  have hLC : PumpCalc.bar a Ji ≤
      centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩} :
        Set (barQ ↥(centralizer ({a} : Set G)))) ⊓ PumpCalc.bar a J := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      ⟨j, Subgroup.mem_subgroupOf.2 (hJiJ (Subgroup.mem_subgroupOf.1 hj)), rfl⟩⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hjK : (j : G) ∈ K := (hJi.1 (Subgroup.mem_subgroupOf.1 hj)).1
    have hjx : (j : G) * x = x * (j : G) := Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hjK)
    have hja : (j : G) * a = a * (j : G) := Subgroup.mem_centralizer_singleton_iff.1 j.2
    show (j : G) * (x * a) = x * a * (j : G)
    calc (j : G) * (x * a) = ((j : G) * x) * a := (mul_assoc _ _ _).symm
      _ = (x * (j : G)) * a := by rw [hjx]
      _ = x * ((j : G) * a) := mul_assoc _ _ _
      _ = x * (a * (j : G)) := by rw [hja]
      _ = x * a * (j : G) := (mul_assoc _ _ _).symm
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
  have hsubK : ((K ⊓ centralizer ({a} : Set G)).subgroupOf
      (centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G))).IsSubnormal :=
    B1.isSubnormal_subgroupOf_inf (S := centralizer ({a} : Set G)) (B1.isSubnormal_of_isPCompIn hK)
  have hW : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G)) Ji :=
    B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsubK hJi
  have hT₁ := TwoThin.isTwoComponent_map_barMk (TwoThin.orderOf_mk_centralizer hxY hx)
    (TwoThin.le_centralizer_mk hW.1 hxY) (TwoThin.isTwoComponent_centralizer_mk hW hxY)
  have hP := (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).2 hT₁
  have hLP : IsPCompIn 2 (centralizer ({barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩} :
      Set (barQ ↥(centralizer ({a} : Set G)))) ⊓ PumpCalc.bar a J) (PumpCalc.bar a Ji) :=
    ⟨hLC, CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hLC hCt hP⟩
  let f : ↥Ji →* ↥(PumpCalc.bar a Ji) :=
    ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hJiY)).codRestrict
      (PumpCalc.bar a Ji) (fun h => ⟨⟨(h : G), hJiY h.2⟩, Subgroup.mem_subgroupOf.2 h.2, rfl⟩)
  have hfs : Function.Surjective f := by
    rintro ⟨_, ⟨c, hc', rfl⟩⟩
    exact ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc'⟩, Subtype.ext rfl⟩
  have hfker : f.ker ≤ pPrimeCore 2 ↥Ji := by
    have h0 : f.ker = ((barMk ↥(centralizer ({a} : Set G))).comp (Subgroup.inclusion hJiY)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [h0]
    exact S1Split.ker_fK_le a hJiY
  have hker2 : ¬ 2 ∣ Nat.card f.ker := by
    intro h2
    have hcop : Nat.Coprime 2 (Nat.card f.ker) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hfker) pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop h2
  obtain ⟨hcomap, -⟩ := CFSG.prime_complement_kernel_core_preimage f hfs hker2
  let ψ : ↥Ji →* ↥(PumpCalc.bar a Ji) ⧸ pPrimeCore 2 ↥(PumpCalc.bar a Ji) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(PumpCalc.bar a Ji))).comp f
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hfs
  have hψk : ψ.ker = pPrimeCore 2 ↥Ji := by
    rw [← hcomap]
    ext o
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff (f o)
  refine ⟨hLP, ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hψk).trans eq)⟩, fun hLO => ?_⟩
  have hLO' : pPrimeCore 2 ↥(PumpCalc.bar a Ji) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (PumpCalc.bar a Ji).subtype_injective).1 hLO
  rintro _ ⟨o, ho, rfl⟩
  have ho' : o ∈ (pPrimeCore 2 ↥(PumpCalc.bar a Ji)).comap f := by rw [hcomap]; exact ho
  rw [hLO'] at ho'
  have hfo : f o = 1 := Subgroup.mem_bot.1 (Subgroup.mem_comap.1 ho')
  have h1 : barMk ↥(centralizer ({a} : Set G)) ⟨(o : G), hJiY o.2⟩ = 1 := congrArg Subtype.val hfo
  exact ⟨⟨(o : G), hJiY o.2⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem s1_lemma283b_of_pair_table (hT : KG531Table) (hB : KG531BPair)
    (hc : Ctx21 G x K A a D J) {J₁ J₂ : Subgroup G} (hS : S1SplitMod K A x a J₁ J₂)
    (hJ₂ : J₂ ≤ J) : ¬ J₁ ≤ J := by
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
  have ht2 : orderOf (barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩) = 2 :=
    TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hxaY hxa2)
  have hMc : CFSG.IsComponent (PumpCalc.bar a J) := FalseCtxS45Comp.isComponent_bar hJ
  have hGH : GHList (↥(PumpCalc.bar a J) ⧸ center ↥(PumpCalc.bar a J)) :=
    ghList_of_quasisimple hc.hyp.simple hc.hyp.nonab hc.hyp.kgh ha hMc.1
  have hMO : pPrimeCore 2 ↥(PumpCalc.bar a J) = ⊥ := by
    have h := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal 2 hMc.2
    rw [CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (PumpCalc.bar a J).subtype_injective).1
      (le_bot_iff.1 h)
  have htM : barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ ∈ PumpCalc.bar a J :=
    ⟨⟨x * a, hxaY⟩, Subgroup.mem_subgroupOf.2 (hJ₂ hS.xu_mem), rfl⟩
  have haM : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ ∈ PumpCalc.bar a J :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.2 (hJ₁ hS.u_mem), rfl⟩
  have haZ : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ ∈
      (center ↥(PumpCalc.bar a J)).map (PumpCalc.bar a J).subtype :=
    ⟨⟨_, haM⟩, Subgroup.mem_center_iff.2 fun m =>
      Subtype.ext (hab_cen (m : barQ ↥(centralizer ({a} : Set G)))), rfl⟩
  have haL₁ : barMk ↥(centralizer ({a} : Set G)) ⟨a, haY⟩ ∈ PumpCalc.bar a J₁ :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.2 hS.u_mem, rfl⟩
  have htL₂ : barMk ↥(centralizer ({a} : Set G)) ⟨x * a, hxaY⟩ ∈ PumpCalc.bar a J₂ :=
    ⟨⟨x * a, hxaY⟩, Subgroup.mem_subgroupOf.2 hS.xu_mem, rfl⟩
  obtain ⟨F, _, _, hodd, hF5, ⟨q₁⟩, ⟨q₂⟩⟩ := hS.sl2
  obtain ⟨hP₁, he₁, hO₁⟩ := bar_data hc hS.comp₁ hJ₁ hxaY q₁
  obtain ⟨hP₂, he₂, hO₂⟩ := bar_data hc hS.comp₂ hJ₂ hxaY q₂
  obtain ⟨hL₁, hL₂⟩ := hB _ _ hMc.1 hGH hMO _ htM ht2 _ _ hP₁ hP₂ _ haL₁ hab2 haZ htL₂ F hodd hF5
    he₁ he₂
  exact s1_lemma283b_of_table hT hc hS hJ₂ (hO₁ hL₁) (hO₂ hL₂) hJ₁

end Bridge

end CFSG.GH74.Generic.BProg.B3
