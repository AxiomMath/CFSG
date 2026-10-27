module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PUnipB
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PNorm
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Sp44Main
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PUnipA

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank CFSG.Open Subgroup
open scoped commutatorElement

theorem frobSylow_antiSp {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4) :
    FrobSylow (frobHom K) (antiUnipotent K) where
  card := by rw [card_antiUnipotent, hK]; norm_num
  stable u hu := frobHom_mem_antiUnipotent hu
  class_two x hx y hy z hz := antiUnipotent_class_two hx hy hz
  nonabelian := antiUnipotent_nonabelian
  elem_abelian := by
    obtain ⟨E, hE, hc, hab, hexp⟩ := exists_elemAbelian (K := K)
    exact ⟨E, hE, by rw [hc, hK]; norm_num, hab, hexp⟩
  big_abelian x hx hx2 := by
    obtain ⟨R, hR, hxR, hab, hc⟩ := exists_abelian_of_involution hx hx2
    exact ⟨R, hR, hxR, hab, by rw [hc, hK]; norm_num⟩
  cocycle u hu h := antiUnipotent_cocycle_four hK hu h
  card_fix := card_antiUnipotent_inf_fixed hK

theorem frobSylow_statedSp {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4)
    {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) :
    FrobSylow (frobSp K Fr) ((antiUnipotent K).map (antiSpEquiv K).toMonoidHom) :=
  (frobSylow_antiSp hK).map_equiv (antiSpEquiv K) (fun a => antiSpEquiv_frobHom hFr a)

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {t : X}

section Conj

variable {h : X}

theorem conj_mul_self (ht2 : t * t = 1) : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
  calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
    _ = 1 := by rw [ht2]; group

theorem conj_ne_one (ht1 : t ≠ 1) : h⁻¹ * t * h ≠ 1 := by
  intro e
  apply ht1
  have : t = h * (h⁻¹ * t * h) * h⁻¹ := by group
  rw [this, e]; group

theorem conj_normalizes (hh : h ∈ Y) (htn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) :
    ∀ y ∈ Y, (h⁻¹ * t * h) * y * (h⁻¹ * t * h)⁻¹ ∈ Y := by
  intro y hy
  have h1 : t * (h * y * h⁻¹) * t⁻¹ ∈ Y := htn _ (Y.mul_mem (Y.mul_mem hh hy) (Y.inv_mem hh))
  have h2 : h⁻¹ * (t * (h * y * h⁻¹) * t⁻¹) * h ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.inv_mem hh) h1) hh
  have e : (h⁻¹ * t * h) * y * (h⁻¹ * t * h)⁻¹ = h⁻¹ * (t * (h * y * h⁻¹) * t⁻¹) * h := by
    group
  rw [e]
  exact h2

theorem conj_outer (hh : h ∈ Y) (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹) :
    ¬ ∃ y ∈ Y, ∀ z ∈ Y, (h⁻¹ * t * h) * z * (h⁻¹ * t * h)⁻¹ = y * z * y⁻¹ := by
  rintro ⟨y, hy, hyz⟩
  apply hout
  refine ⟨h * y * h⁻¹, Y.mul_mem (Y.mul_mem hh hy) (Y.inv_mem hh), fun w hw => ?_⟩
  have hz : h⁻¹ * w * h ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hh) hw) hh
  have := hyz _ hz
  calc t * w * t⁻¹ = h * ((h⁻¹ * t * h) * (h⁻¹ * w * h) * (h⁻¹ * t * h)⁻¹) * h⁻¹ := by group
    _ = h * (y * (h⁻¹ * w * h) * y⁻¹) * h⁻¹ := by rw [this]
    _ = (h * y * h⁻¹) * w * (h * y * h⁻¹)⁻¹ := by group

theorem conj_centralizer (hh : h ∈ Y) (ht2 : t * t = 1)
    (hcent : centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t) :
    centralizer ({h⁻¹ * t * h} : Set X) =
      (Y ⊓ centralizer ({h⁻¹ * t * h} : Set X)) ⊔ zpowers (h⁻¹ * t * h) := by
  have ht2' : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := conj_mul_self ht2
  have hKt : ∀ k ∈ Y ⊓ centralizer ({t} : Set X), k * t = t * k := fun k hk =>
    mem_centralizer_singleton_iff.mp hk.2
  have hKt' : ∀ k ∈ Y ⊓ centralizer ({h⁻¹ * t * h} : Set X), k * (h⁻¹ * t * h) = (h⁻¹ * t * h) * k :=
    fun k hk => mem_centralizer_singleton_iff.mp hk.2
  apply le_antisymm
  · intro x hx
    have hx1 : h * x * h⁻¹ ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp hx
      calc h * x * h⁻¹ * t = h * (x * (h⁻¹ * t * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * t * h) * x) * h⁻¹ := by rw [this]
        _ = t * (h * x * h⁻¹) := by group
    obtain ⟨k, hk, hxk | hxk⟩ := (mem_sup_zpowers_iff ht2 hKt).mp (hcent ▸ hx1)
    · refine (mem_sup_zpowers_iff ht2' hKt').mpr ⟨h⁻¹ * k * h, ⟨?_, ?_⟩, Or.inl ?_⟩
      · exact Y.mul_mem (Y.mul_mem (Y.inv_mem hh) hk.1) hh
      · refine mem_centralizer_singleton_iff.mpr ?_
        have := hKt k hk
        calc h⁻¹ * k * h * (h⁻¹ * t * h) = h⁻¹ * (k * t) * h := by group
          _ = h⁻¹ * (t * k) * h := by rw [this]
          _ = (h⁻¹ * t * h) * (h⁻¹ * k * h) := by group
      · calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
          _ = h⁻¹ * k * h := by rw [hxk]
    · refine (mem_sup_zpowers_iff ht2' hKt').mpr ⟨h⁻¹ * k * h, ⟨?_, ?_⟩, Or.inr ?_⟩
      · exact Y.mul_mem (Y.mul_mem (Y.inv_mem hh) hk.1) hh
      · refine mem_centralizer_singleton_iff.mpr ?_
        have := hKt k hk
        calc h⁻¹ * k * h * (h⁻¹ * t * h) = h⁻¹ * (k * t) * h := by group
          _ = h⁻¹ * (t * k) * h := by rw [this]
          _ = (h⁻¹ * t * h) * (h⁻¹ * k * h) := by group
      · calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
          _ = h⁻¹ * (k * t) * h := by rw [hxk]
          _ = h⁻¹ * k * h * (h⁻¹ * t * h) := by group
  · refine sup_le inf_le_right ?_
    rw [zpowers_le, mem_centralizer_singleton_iff]

end Conj

theorem gomi1P_facts (hO : standardComponentOddCore X = ⊥) (ht : orderOf t = 2)
    (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) (htn : t ∈ normalizer (Y : Set X))
    (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹)
    (hcent : centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t) :
    Gomi1PFacts Y (CFSG.Open.genFittingLayer X) := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have htn' : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy => (mem_normalizer_iff.mp htn y).mp hy
  obtain ⟨M⟩ := nonempty_frobModel hY ht2 htn' hout
  letI := M.field
  haveI := M.fin
  haveI := M.charP
  have ht2₁ := conj_mul_self (t := t) (h := M.h) ht2
  have ht1₁ := conj_ne_one (t := t) (h := M.h) ht1
  have htn₁ := conj_normalizes M.h_mem htn'
  have hout₁ := conj_outer M.h_mem hout
  have hcent₁ := conj_centralizer M.h_mem ht2 hcent
  haveI hYs : IsSimpleGroup Y :=
    (CFSG.LieType.Simplicity.fam_classical_converse ↥Y
      ⟨.PSp, 2, 2, 2, CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hY⟩).2.2
  have hYcard : Nat.card Y = 979200 :=
    CFSG.ComponentClassification.GSThmB.CF23I.card_of_lieModel_Sp44 hY
  have htY₁ : M.h⁻¹ * t * M.h ∉ Y := fun h => hout₁ ⟨_, h, fun z _ => rfl⟩
  have hact : ∀ a : StatedSp 2 M.K,
      (M.h⁻¹ * t * M.h) * (M.ψ a : X) * (M.h⁻¹ * t * M.h)⁻¹ =
        (M.ψ (frobSp M.K M.Fr a) : X) := M.act
  have hF := frobSylow_statedSp M.card M.hFr
  have hD := sylowData_of_frobSylow M.ψ (frobSp M.K M.Fr) hF ht2₁ htY₁ hact
  have hKcard : Nat.card (Y ⊓ centralizer ({M.h⁻¹ * t * M.h} : Set X) : Subgroup X) = 720 := by
    rw [card_inf_centralizer_eq M.ψ (frobSp M.K M.Fr) hact]
    exact card_eqLocus_fieldSp M.card M.hFr
  have hKZ := center_inf_centralizer_eq_bot M.ψ (frobSp M.K M.Fr) hact
    (center_eqLocus_fieldSp (Fr := M.Fr))
  have h1 := gomi1P_facts_of_data (X := X) (Y := Y) (t := M.h⁻¹ * t * M.h) hO ht2₁ ht1₁ hYcard
    htn₁ hout₁ hcent₁ hKcard hKZ hD
  rw [CFSG.Adapters.genFittingLayer_eq_foundations]
  exact h1

theorem gomi1P_of_ident (hO : standardComponentOddCore X = ⊥) (ht : orderOf t = 2)
    (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) (htn : t ∈ normalizer (Y : Set X))
    (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹)
    (hcent : centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t)
    (hid : Gomi1PIdent Y (CFSG.Open.genFittingLayer X)) :
    CFSG.Blueprint.LieModel (CFSG.Open.genFittingLayer X) .PSp 2 2 2 ∧
      centralizer (CFSG.Open.genFittingLayer X : Set X) = standardComponentOddCore X := by
  have hfacts := gomi1P_facts hO ht hY htn hout hcent
  have hL : CFSG.Open.genFittingLayer X = Y := hid hfacts
  refine ⟨CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hL.symm) hY, ?_⟩
  rw [hfacts.centralizer_eq_bot, hO]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
