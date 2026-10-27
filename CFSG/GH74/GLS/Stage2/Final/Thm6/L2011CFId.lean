module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFAux
public import CFSG.GH74.GLS.Stage1.Main.BrPairModel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

structure Data411 {K : Type} [Group K] (x : K) (q : ℕ) (I₁ I₂ : Subgroup K) : Prop where
  sup : Ez x = I₁ ⊔ I₂
  sl₁ : HasSL2Model ↥I₁ (fun r => r = q)
  sl₂ : HasSL2Model ↥I₂ (fun r => r = q)
  comm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a
  inf : I₁ ⊓ I₂ = zpowers x
  derived : ∀ a ∈ centralizer ({x} : Set K), ∀ b ∈ centralizer ({x} : Set K),
    ⁅a, b⁆ ∈ (generalizedFitting ↥(centralizer ({x} : Set K))).map (centralizer ({x} : Set K)).subtype
  Fs : (generalizedFitting ↥(centralizer ({x} : Set K))).map (centralizer ({x} : Set K)).subtype =
    Ez x ⊔ (centralizer ({x} : Set K) ⊓ centralizer (Ez x : Set K))
  Zabel : ∀ a ∈ centralizer ({x} : Set K) ⊓ centralizer (Ez x : Set K),
    ∀ b ∈ centralizer ({x} : Set K) ⊓ centralizer (Ez x : Set K), a * b = b * a

section Id

variable {K : Type} [Group K] [Finite K] {x : K} {q : ℕ} {I₁ I₂ : Subgroup K}

omit [Finite K] in
theorem perfect_of_pCompIn' {H E : Subgroup K} (hEH : E ≤ H) (h : IsPComponent 2 (E.subgroupOf H)) :
    ⁅E, E⁆ = E := by
  have hp : Group.IsPerfect (E.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect h
  have hp' : Group.IsPerfect E := by
    have e := Subgroup.subgroupOfEquivOfLe hEH
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

omit [Finite K] in
theorem ne_bot_of_pCompIn' {H E : Subgroup K} (h : IsPComponent 2 (E.subgroupOf H)) : E ≠ ⊥ := by
  intro hE
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial h
  rw [hE, Subgroup.bot_subgroupOf] at this
  exact not_nontrivial_iff_subsingleton.2 inferInstance this

omit [Finite K] in
theorem le_cent_of_data (hd : Data411 x q I₁ I₂) :
    I₁ ≤ centralizer ({x} : Set K) ∧ I₂ ≤ centralizer ({x} : Set K) := by
  have hEzC : Ez x ≤ centralizer ({x} : Set K) := Subgroup.map_subtype_le _
  exact ⟨(hd.sup ▸ le_sup_left : I₁ ≤ Ez x).trans hEzC, (hd.sup ▸ le_sup_right : I₂ ≤ Ez x).trans hEzC⟩

omit [Finite K] in
theorem isComponent_I (hq5 : 5 ≤ q) (hd : Data411 x q I₁ I₂) :
    CFSG.IsComponent (I₁.subgroupOf (centralizer ({x} : Set K))) ∧
      CFSG.IsComponent (I₂.subgroupOf (centralizer ({x} : Set K))) := by
  set C : Subgroup K := centralizer ({x} : Set K) with hC
  obtain ⟨hI₁C, hI₂C⟩ := le_cent_of_data hd
  have hlayer : layer ↥C = I₁.subgroupOf C ⊔ I₂.subgroupOf C := by
    rw [← Subgroup.subgroupOf_sup hI₁C hI₂C, ← hd.sup]
    unfold Ez
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hlc : (layer ↥C).Characteristic := CFSG.LocalCores.layer_characteristic
  have hln : (layer ↥C).Normal := inferInstance
  have hcommY : ∀ a ∈ I₁.subgroupOf C, ∀ b ∈ I₂.subgroupOf C, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hd.comm a ha b hb)
  have hcommY' : ∀ a ∈ I₂.subgroupOf C, ∀ b ∈ I₁.subgroupOf C, a * b = b * a := fun a ha b hb =>
    (hcommY b hb a ha).symm
  have hq₁ := CFSG.GH74.GLS.Stage1.Main.quasi_of_hasSL2 hq5 hd.sl₁
  have hq₂ := CFSG.GH74.GLS.Stage1.Main.quasi_of_hasSL2 hq5 hd.sl₂
  refine ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hI₁C).symm hq₁, ?_⟩,
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hI₂C).symm hq₂, ?_⟩⟩
  · refine Subgroup.IsSubnormal.step _ (layer ↥C) (hlayer ▸ le_sup_left) hln.isSubnormal ⟨fun n hn g => ?_⟩
    have hg : (g : ↥C) ∈ I₂.subgroupOf C ⊔ I₁.subgroupOf C := by
      rw [sup_comm, ← hlayer]; exact g.2
    have hn' : (n : ↥C) ∈ I₁.subgroupOf C := hn
    exact ConjComponent.conj_mem_of_mem_sup hcommY' hg hn'
  · refine Subgroup.IsSubnormal.step _ (layer ↥C) (hlayer ▸ le_sup_right) hln.isSubnormal ⟨fun n hn g => ?_⟩
    have hg : (g : ↥C) ∈ I₁.subgroupOf C ⊔ I₂.subgroupOf C := by
      rw [← hlayer]; exact g.2
    have hn' : (n : ↥C) ∈ I₂.subgroupOf C := hn
    exact ConjComponent.conj_mem_of_mem_sup hcommY hg hn'

theorem pComp_eq (hq5 : 5 ≤ q) (hqodd : Odd q) (hx2 : orderOf x = 2) (hd : Data411 x q I₁ I₂)
    {E : Subgroup K} (hE : IsPCompIn 2 (centralizer ({x} : Set K)) E)
    (hEsl : HasSL2Model (↥E ⧸ pPrimeCore 2 ↥E) (fun r => r = q)) : E = I₁ ∨ E = I₂ := by
  set C : Subgroup K := centralizer ({x} : Set K) with hC
  obtain ⟨hEC, hEpc⟩ := hE
  obtain ⟨hI₁C, hI₂C⟩ := le_cent_of_data hd
  obtain ⟨hc₁, hc₂⟩ := isComponent_I hq5 hd
  have hperfE : ⁅E, E⁆ = E := perfect_of_pCompIn' hEC hEpc
  have hEsub : (E.subgroupOf C).IsSubnormal := by
    obtain ⟨_, _, hs, _⟩ := hEpc
    exact hs
  have hEne : E ≠ ⊥ := ne_bot_of_pCompIn' hEpc
  have hEF : E ≤ (generalizedFitting ↥C).map C.subtype := by
    calc E = ⁅E, E⁆ := hperfE.symm
      _ ≤ _ := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        exact hd.derived g₁ (hEC hg₁) g₂ (hEC hg₂)
  have hEEz : E ≤ Ez x := by
    calc E = ⁅E, E⁆ := hperfE.symm
      _ ≤ Ez x := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have h1 := hEF hg₁
        have h2 := hEF hg₂
        rw [hd.Fs] at h1 h2
        have hZc : ∀ u ∈ Ez x, ∀ z ∈ C ⊓ centralizer (Ez x : Set K), u * z = z * u := fun u hu z hz =>
          Subgroup.mem_centralizer_iff.1 hz.2 u hu
        obtain ⟨u₁, hu₁, z₁, hz₁, rfl⟩ := ConjComponent.exists_mul_of_mem_sup hZc h1
        obtain ⟨u₂, hu₂, z₂, hz₂, rfl⟩ := ConjComponent.exists_mul_of_mem_sup hZc h2
        rw [hZc u₁ hu₁ z₁ hz₁, hZc u₂ hu₂ z₂ hz₂,
          ConjComponent.commutatorElement_mul_mul (hZc u₁ hu₁ z₁ hz₁).symm (hZc u₂ hu₂ z₁ hz₁).symm
            (hd.Zabel z₁ hz₁ z₂ hz₂) (hZc u₁ hu₁ z₂ hz₂).symm (hZc u₂ hu₂ z₂ hz₂).symm]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu₁ hu₂) (Subgroup.inv_mem _ hu₁))
          (Subgroup.inv_mem _ hu₂)
  have hEcard : ∃ m : ℕ, Odd m ∧ Nat.card ↥(E.subgroupOf C) = q * (q ^ 2 - 1) * m := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥E)
    have h2 : Nat.card (↥E ⧸ pPrimeCore 2 ↥E) = q * (q ^ 2 - 1) := card_of_hasSL2Model hEsl
    have h3 : Odd (Nat.card ↥(pPrimeCore 2 ↥E)) :=
      Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥E))
    refine ⟨Nat.card ↥(pPrimeCore 2 ↥E), h3, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, h1, h2]
  have hcommY : ∀ a ∈ I₁.subgroupOf C, ∀ b ∈ I₂.subgroupOf C, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hd.comm a ha b hb)
  have hEle : E.subgroupOf C ≤ I₁.subgroupOf C ⊔ I₂.subgroupOf C := by
    rw [← Subgroup.subgroupOf_sup hI₁C hI₂C, ← hd.sup]
    intro g hg
    exact hEEz hg
  have hinf : Nat.card ↥(I₁.subgroupOf C ⊓ I₂.subgroupOf C) = 2 := by
    have : I₁.subgroupOf C ⊓ I₂.subgroupOf C = (zpowers x).subgroupOf C := by
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, ← hd.inf]
    rw [this]
    have hxC : zpowers x ≤ C := by
      rw [zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxC).toEquiv, Nat.card_zpowers, hx2]
  have hcard₁ : Nat.card ↥(I₁.subgroupOf C) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI₁C).toEquiv]; exact card_of_hasSL2Model hd.sl₁
  have hcard₂ : Nat.card ↥(I₂.subgroupOf C) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI₂C).toEquiv]; exact card_of_hasSL2Model hd.sl₂
  have hperf' : ⁅E.subgroupOf C, E.subgroupOf C⁆ = E.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEC, hperfE]
  have hne' : E.subgroupOf C ≠ ⊥ := by
    intro h
    apply hEne
    have := congrArg (Subgroup.map C.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hEC, Subgroup.map_bot] at this
  have key := eq_or_eq_of_perfect_subnormal hqodd hc₁ hc₂ hcommY hinf hcard₁ hcard₂ hEle hEsub hperf'
    hne' hEcard
  rcases key with h | h
  · left
    have := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_eq_left.2 hEC, inf_eq_left.2 hI₁C] at this
  · right
    have := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_eq_left.2 hEC, inf_eq_left.2 hI₂C] at this

theorem pair_eq (hqodd : Odd q) {E₁ E₂ : Subgroup K} (hcfg : Ivk93Cfg x q E₁ E₂)
    (hd : Data411 x q I₁ I₂) : (E₁ = I₁ ∧ E₂ = I₂) ∨ (E₁ = I₂ ∧ E₂ = I₁) := by
  have h1 := pComp_eq hcfg.five hqodd hcfg.ord hd hcfg.comp₁ hcfg.sl₁
  have h2 := pComp_eq hcfg.five hqodd hcfg.ord hd hcfg.comp₂ hcfg.sl₂
  have hne := hcfg.ne
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Id

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
