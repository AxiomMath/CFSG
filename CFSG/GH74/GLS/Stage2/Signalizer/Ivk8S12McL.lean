module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12TwoSpec
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltYCore
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Ord
public import Certificates.Certificate5249

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.GroupTheory.TwoWeights CFSG.ComponentClassification.J2Cover
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification

theorem eq_one_or_of_mem_zpowers_two {G : Type*} [Group G] {x g : G} (hx : orderOf x = 2)
    (hg : g ∈ zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  have h := zpow_mod_orderOf x k
  rw [hx] at h
  push_cast at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h, h0]
    simp
  · right
    rw [← h, h1]
    simp

theorem alt8_step_of_hom {X : Type*} [Group X] {τ : X} (hτ2 : orderOf τ = 2)
    (ρ : ↥(centralizer ({τ} : Set X)) →* Equiv.Perm (Fin 8))
    (hρA : ∀ g, ρ g ∈ alternatingGroup (Fin 8))
    (hρτ : ρ ⟨τ, mem_centralizer_singleton_iff.2 rfl⟩ = 1)
    (hρ1 : ∀ g, ρ g = 1 → g = 1 ∨ g = ⟨τ, mem_centralizer_singleton_iff.2 rfl⟩)
    {T₀ : Subgroup X} (hτT : τ ∈ T₀) (hTC : T₀ ≤ centralizer ({τ} : Set X))
    (hT₀card : Nat.card ↥T₀ = 2 ^ 7) {E : Subgroup X} (hE3 : IsPGroup 3 ↥E) (hEne : E ≠ ⊥)
    (hEC : E ≤ centralizer ({τ} : Set X)) (hN : T₀ ≤ normalizer (E : Set X)) : False := by
  classical
  have hτsq : τ ^ 2 = 1 := by rw [← hτ2]; exact pow_orderOf_eq_one τ
  have hτCval : ((⟨τ, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({τ} : Set X))) :
    X) = τ := rfl
  generalize (⟨τ, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({τ} : Set X))) = τC
    at hρτ hρ1 hτCval
  have hτ2C : orderOf τC = 2 := by
    rw [← Subgroup.orderOf_coe τC, hτCval, hτ2]
  set TC : Subgroup ↥(centralizer ({τ} : Set X)) := T₀.subgroupOf (centralizer ({τ} : Set X))
    with hTCdef
  set EC : Subgroup ↥(centralizer ({τ} : Set X)) := E.subgroupOf (centralizer ({τ} : Set X))
    with hECdef
  set P : Subgroup (Equiv.Perm (Fin 8)) := TC.map ρ with hP
  set W : Subgroup (Equiv.Perm (Fin 8)) := EC.map ρ with hW
  have hPA : P ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨g, -, rfl⟩
    exact hρA g
  have hτTC : τC ∈ TC := by
    show (τC : X) ∈ T₀
    rw [hτCval]
    exact hτT
  set ρT : ↥TC →* Equiv.Perm (Fin 8) := ρ.comp TC.subtype with hρT
  have hker : ρT.ker = zpowers (⟨τC, hτTC⟩ : ↥TC) := by
    apply le_antisymm
    · intro g hg
      rw [MonoidHom.mem_ker] at hg
      rcases hρ1 g.1 hg with h | h
      · have : g = 1 := Subtype.ext h
        rw [this]
        exact one_mem _
      · have : g = ⟨τC, hτTC⟩ := Subtype.ext h
        rw [this]
        exact mem_zpowers _
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact hρτ
  have hkc : Nat.card ρT.ker = 2 := by
    rw [hker, Nat.card_zpowers, ← hτ2C, ← Subgroup.orderOf_coe (⟨τC, hτTC⟩ : ↥TC)]
  have hTCcard : Nat.card ↥TC = 2 ^ 7 := by
    rw [← hT₀card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  have hPcard : Nat.card ↥P = 2 ^ 6 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρT.ker
    have h2 : Nat.card (↥TC ⧸ ρT.ker) = Nat.card ρT.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρT).toEquiv
    have h3 : ρT.range = P := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [hTCcard, h2, h3, hkc] at h1
    norm_num at h1 ⊢
    omega
  have hW3 : IsPGroup 3 ↥W := by
    intro w
    obtain ⟨g, hg, hgw⟩ := w.2
    obtain ⟨k, hk⟩ := hE3 ⟨(g : X), hg⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hgk : g ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have : ((w : Equiv.Perm (Fin 8)) ^ 3 ^ k) = 1 := by
      rw [← hgw, ← map_pow, hgk, map_one]
    simpa using this
  have hWne : W ≠ ⊥ := by
    intro hWb
    apply hEne
    rw [eq_bot_iff]
    intro e he
    have heC : e ∈ centralizer ({τ} : Set X) := hEC he
    have hmem : ρ ⟨e, heC⟩ ∈ W := ⟨⟨e, heC⟩, he, rfl⟩
    rw [hWb, Subgroup.mem_bot] at hmem
    rcases hρ1 _ hmem with h | h
    · have := congrArg Subtype.val h
      simpa using this
    · exfalso
      have he' : e = τ := (congrArg Subtype.val h).trans hτCval
      obtain ⟨k, hk⟩ := hE3 ⟨e, he⟩
      have hk' : e ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf τ ∣ 3 ^ k := by
        rw [← he']
        exact orderOf_dvd_of_pow_eq_one hk'
      rw [hτ2] at h1
      have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h1
      omega
  have hconj : ∀ g : ↥(centralizer ({τ} : Set X)), (g : X) ∈ T₀ → ∀ h ∈ W,
      ρ g * h * (ρ g)⁻¹ ∈ W := by
    intro g hg h hh
    obtain ⟨k, hk, rfl⟩ := hh
    refine ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN hg) (k : X)).1 hk
    exact h1
  have hN' : P ≤ normalizer (W : Set (Equiv.Perm (Fin 8))) := by
    rintro _ ⟨g, hgT, rfl⟩
    have hg : (g : X) ∈ T₀ := hgT
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj g hg h, fun hh => ?_⟩
    have hg' : ((g⁻¹ : ↥(centralizer ({τ} : Set X))) : X) ∈ T₀ := by
      rw [Subgroup.coe_inv]
      exact T₀.inv_mem hg
    have := hconj g⁻¹ hg' _ hh
    simpa [map_inv, mul_assoc] using this
  have hWbot := AltY.three_group_trivial (n := 8) (e := 6) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hPA
    hPcard hW3 hN'
  exact hWne hWbot

theorem alt8_step {X : Type*} [Group X] {τ : X} (hτ2 : orderOf τ = 2)
    (φ : ↥(centralizer ({τ} : Set X)) ⧸
      zpowers (⟨τ, CFSG.Sporadic.Recognition.McLCentralizer.self_mem_centralizer τ⟩ :
        ↥(centralizer ({τ} : Set X))) ≃* alternatingGroup (Fin 8))
    {T₀ : Subgroup X} (hτT : τ ∈ T₀) (hTC : T₀ ≤ centralizer ({τ} : Set X))
    (hT₀card : Nat.card ↥T₀ = 2 ^ 7) {E : Subgroup X} (hE3 : IsPGroup 3 ↥E) (hEne : E ≠ ⊥)
    (hEC : E ≤ centralizer ({τ} : Set X)) (hN : T₀ ≤ normalizer (E : Set X)) : False := by
  classical
  set τC : ↥(centralizer ({τ} : Set X)) := ⟨τ, mem_centralizer_singleton_iff.2 rfl⟩ with hτC
  have hτ2C : orderOf τC = 2 := by
    rw [← hτ2, ← Subgroup.orderOf_coe τC]
  let ρ : ↥(centralizer ({τ} : Set X)) →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))
  refine alt8_step_of_hom hτ2 ρ (fun g => (φ (QuotientGroup.mk' _ g)).2) ?_ ?_ hτT hTC hT₀card
    hE3 hEne hEC hN
  · have h2 : QuotientGroup.mk' (zpowers τC) τC = 1 :=
      (QuotientGroup.eq_one_iff τC).2 (mem_zpowers _)
    show ((φ (QuotientGroup.mk' (zpowers τC) τC) : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)) = 1
    rw [h2, map_one]
    rfl
  · intro g hg
    have h1 : φ (QuotientGroup.mk' (zpowers τC) g) = 1 := Subtype.ext hg
    have h2 : QuotientGroup.mk' (zpowers τC) g = 1 := φ.injective (by rw [h1, map_one])
    exact eq_one_or_of_mem_zpowers_two hτ2C ((QuotientGroup.eq_one_iff g).1 h2)

theorem not_threeCfg_mclP :
    ¬ ThreeCfg (⊤ : Subgroup ↥mclP) := by
  classical
  have hn : (275 : ℕ) < 2 ^ 32 := by norm_num
  have hgT : List.Forall₂ (Rep 275) Certificates.Ivk8Two.McL.gensT [mclGen 0, mclGen 1] :=
    .cons (rep_arrTable hn (rep_mclStrongPerm (by norm_num : 0 < 13)))
      (.cons (rep_arrTable hn (rep_mclStrongPerm (by norm_num : 1 < 13))) .nil)
  have hgN : ∀ g ∈ [mclGen 0, mclGen 1], g ∈ mclP := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact mclGen_mem_P 0 (by norm_num)
    · exact mclGen_mem_P 1 (by norm_num)
  obtain ⟨a, u₁, u₂, u₃, x, y, ha, h₁, h₂, h₃, hx, hy, hane, -, D, hcard⟩ :=
    two_spec hn hgT hgN Certificates.certificate5249
  set B : Subgroup (Equiv.Perm (Fin 275)) := closure {u₁, u₂, u₃, a, x, y} with hB
  have hBle : B ≤ mclP := by
    rw [hB, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hB2 : IsPGroup 2 ↥B := D.isPGroup_closure
  set T₀ : Subgroup ↥mclP := B.subgroupOf mclP with hT₀
  have hT₀2 : IsPGroup 2 ↥T₀ := hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBle).symm
  have hT₀card' : 2 ^ 7 ≤ Nat.card ↥T₀ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv]
    exact hcard
  have hX : Nat.card ↥mclP = 898128000 := card_mclP
  have hX2 : ¬ 2 ^ (7 + 1) ∣ Nat.card ↥mclP := by rw [hX]; norm_num
  have hX3 : ¬ 3 ^ 8 ∣ Nat.card ↥mclP := by rw [hX]; norm_num
  have hT₀card : Nat.card ↥T₀ = 2 ^ 7 := card_eq_two_pow hT₀2 hT₀card' hX2
  have D' := data_of_mem mclP D ha h₁ h₂ h₃ hx hy
  have hcen : ∀ t ∈ T₀, t * (⟨a, ha⟩ : ↥mclP) = ⟨a, ha⟩ * t := by
    intro t ht
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (D.closure_le_centralizer ht))
  have hτT : (⟨a, ha⟩ : ↥mclP) ∈ T₀ := Subgroup.subset_closure (by simp)
  have hTC : T₀ ≤ centralizer ({(⟨a, ha⟩ : ↥mclP)} : Set ↥mclP) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcen t ht)
  refine not_threeCfg_of_data D' hT₀2 hcen hτT (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hT₀card' hX2 hX3 ?_
  intro E hE3 hEne hEC hN
  have hτ2 : orderOf (⟨a, ha⟩ : ↥mclP) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [sq] using D.a_a)
    · intro h
      exact hane (congrArg Subtype.val h)
  obtain ⟨-, -, ⟨φ⟩⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
      (T := ↥mclP) ⟨mclPermEquiv.symm⟩ hτ2
  exact alt8_step hτ2 φ hτT hTC hT₀card hE3 hEne hEC hN

theorem center_eq_bot_of_equiv_mcl
    {Y : Type} [Group Y]
    (e : Y ≃* NativeSporadic.McL) : center Y = ⊥ := by
  have hs : IsSimpleGroup Y :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [Nat.card_congr (e.trans mclPermEquiv).toEquiv, card_mclP] at hp
    exact absurd hp (by norm_num)

theorem not_sylCfgOf_McL
    {Y : Type} [Group Y] (hY : NativeSporadic.IsSporadic Y .McL) :
    ¬ SylCfgOf Y := by
  obtain ⟨e⟩ := hY
  have e₀ : Y ≃* NativeSporadic.McL := e
  have e' : Y ≃* mclP := e₀.trans mclPermEquiv
  have : Finite Y := Finite.of_equiv ↥mclP e'.symm.toEquiv
  have hc : center Y = ⊥ := center_eq_bot_of_equiv_mcl e₀
  have hout : Nat.card (OuterAutomorphisms.Outer Y) ≤ 2 :=
    outer_card_le_of_equiv McL_outer_card_le_two.1 e₀
  have hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := card_mulAut_le_of_outer hout
  intro h
  have h1 := threeCfg_of_sylCfgOf_inner hc hcard h
  have h2 := threeCfg_map e' h1
  rw [Subgroup.map_top_of_surjective _ e'.surjective] at h2
  exact not_threeCfg_mclP h2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
