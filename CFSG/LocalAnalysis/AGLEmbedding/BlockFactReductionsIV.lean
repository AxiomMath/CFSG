module

import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Transfer

variable {X : Type*} [Group X] [Finite X] {Lb P : Subgroup X}

theorem card_le_three_of_sylow_subgroupOf (hPL : P ≤ Lb)
    (h : ∀ Q : Sylow 3 ↥(P.subgroupOf Lb), IsCyclic (Q : Subgroup ↥(P.subgroupOf Lb)) →
      Nat.card Q ≤ 3)
    (Q : Sylow 3 ↥P) (hQ : IsCyclic (Q : Subgroup ↥P)) : Nat.card Q ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e : ↥P ≃* ↥(P.subgroupOf Lb) := (Subgroup.subgroupOfEquivOfLe hPL).symm
  set Q' : Sylow 3 ↥(P.subgroupOf Lb) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ' : (Q' : Subgroup ↥(P.subgroupOf Lb)) = (Q : Subgroup ↥P).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  set φ : ↥(Q : Subgroup ↥P) ≃* ↥(Q' : Subgroup ↥(P.subgroupOf Lb)) :=
    ((Q : Subgroup ↥P).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hQ'.symm)
  have hcyc : IsCyclic (Q' : Subgroup ↥(P.subgroupOf Lb)) :=
    isCyclic_of_injective φ.symm.toMonoidHom φ.symm.injective
  have h1 := h Q' hcyc
  rwa [← Nat.card_congr φ.toEquiv] at h1

omit [Finite X] in
theorem not_zpowers_inf_eq_bot_of_subgroupOf (hPL : P ≤ Lb)
    (h : ∀ u ∈ P.subgroupOf Lb, ∀ v ∈ P.subgroupOf Lb, orderOf u = 9 → orderOf v = 9 →
      Commute u v → Subgroup.zpowers u ⊓ Subgroup.zpowers v ≠ ⊥)
    {u v : X} (hu : u ∈ P) (hv : v ∈ P) (hu9 : orderOf u = 9) (hv9 : orderOf v = 9)
    (huv : u * v = v * u) : ¬ Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  intro hbot
  refine h ⟨u, hPL hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨v, hPL hv⟩
    (Subgroup.mem_subgroupOf.mpr hv) (by rw [Subgroup.orderOf_mk, hu9])
    (by rw [Subgroup.orderOf_mk, hv9]) (Subtype.ext huv) ?_
  rw [eq_bot_iff]
  intro x hx
  have h1 := Subgroup.mem_map_of_mem Lb.subtype hx.1
  have h2 := Subgroup.mem_map_of_mem Lb.subtype hx.2
  rw [MonoidHom.map_zpowers] at h1 h2
  have h3 : (x : X) ∈ (⊥ : Subgroup X) := hbot ▸ ⟨h1, h2⟩
  exact (Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h3)))

omit [Finite X] in
theorem mul_comm_of_subgroupOf (hPL : P ≤ Lb)
    (h : ∀ N B : Subgroup ↥Lb, N ≤ B → B ≤ P.subgroupOf Lb →
      P.subgroupOf Lb ≤ Subgroup.normalizer (N : Set ↥Lb) →
      P.subgroupOf Lb ≤ Subgroup.normalizer (B : Set ↥Lb) → Nat.Coprime 3 (Nat.card N) →
      (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N) → (∀ j ∈ P.subgroupOf Lb, ∃ e : ℕ, j ^ 2 ^ e ∈ B) →
      ∀ U : Subgroup ↥Lb, U ≤ P.subgroupOf Lb → IsPGroup 3 U → ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    {N B : Subgroup X} (hNB : N ≤ B) (hBP : B ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set X))
    (hPB : P ≤ Subgroup.normalizer (B : Set X)) (hN : Nat.Coprime 3 (Nat.card N))
    (h3 : ∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N) (h2 : ∀ j ∈ P, ∃ e : ℕ, j ^ 2 ^ e ∈ B)
    {U : Subgroup X} (hUP : U ≤ P) (hU : IsPGroup 3 U) {a b : X} (ha : a ∈ U) (hb : b ∈ U) :
    a * b = b * a := by
  have hnorm : ∀ {W : Subgroup X}, P ≤ Subgroup.normalizer (W : Set X) →
      P.subgroupOf Lb ≤ Subgroup.normalizer (W.subgroupOf Lb : Set ↥Lb) := by
    intro W hW z hz
    refine Subgroup.mem_normalizer_iff.mpr fun n => ?_
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hW (Subgroup.mem_subgroupOf.mp hz)) n
  have hcard : Nat.card (N.subgroupOf Lb) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNB.trans (hBP.trans hPL))).toEquiv
  have key := h (N.subgroupOf Lb) (B.subgroupOf Lb) (fun x hx => hNB hx) (fun x hx => hBP hx)
    (hnorm hPN) (hnorm hPB) (hcard ▸ hN)
    (fun x hx => by
      obtain ⟨e, he⟩ := h3 x hx
      exact ⟨e, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact he⟩)
    (fun x hx => by
      obtain ⟨e, he⟩ := h2 x hx
      exact ⟨e, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact he⟩)
    (U.subgroupOf Lb) (fun x hx => hUP hx) hU.comap_subtype ⟨a, hPL (hUP ha)⟩ ha
    ⟨b, hPL (hUP hb)⟩ hb
  exact congrArg Subtype.val key

theorem isMulCommutative_pCore_subgroupOf (hPL : P ≤ Lb)
    (h : IsMulCommutative ↥(CFSG.pCore 3 (↥P ⧸ primeComplementCore (G := ↥P) 3))) :
    IsMulCommutative ↥(CFSG.pCore 3
      (↥(P.subgroupOf Lb) ⧸ primeComplementCore (G := ↥(P.subgroupOf Lb)) 3)) := by
  set e : ↥(P.subgroupOf Lb) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPL
  set f := QuotientGroup.congr (primeComplementCore (G := ↥(P.subgroupOf Lb)) 3)
    (primeComplementCore (G := ↥P) 3) e (primeComplementCore_map_mulEquiv 3 e)
  set ψ := ((CFSG.pCore 3 (↥(P.subgroupOf Lb) ⧸
      primeComplementCore (G := ↥(P.subgroupOf Lb)) 3)).equivMapOfInjective f.toMonoidHom
      f.injective).trans (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 3 f))
  refine ⟨⟨fun a b => ψ.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact h.is_comm.comm _ _

omit [Finite X] in
theorem isElemAbelian_of_subgroupOf (hPL : P ≤ Lb)
    (h : ∀ U : Subgroup ↥Lb, U ≤ P.subgroupOf Lb → IsPGroup 3 U → IsElemAbelian 3 U)
    {U : Subgroup X} (hUP : U ≤ P) (hU : IsPGroup 3 U) : IsElemAbelian 3 U := by
  obtain ⟨hc, hx3⟩ := h (U.subgroupOf Lb) (fun x hx => hUP hx) hU.comap_subtype
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := congrArg (fun z : ↥(U.subgroupOf Lb) => ((z : ↥Lb) : X))
      (hc.is_comm.comm ⟨⟨a, hPL (hUP a.2)⟩, a.2⟩ ⟨⟨b, hPL (hUP b.2)⟩, b.2⟩)
    simpa using h1
  · have h1 := congrArg Subtype.val (hx3 ⟨x, hPL (hUP hx)⟩ hx)
    simpa using h1

theorem le_pRank_of_elemAbelian_le {p : ℕ} (hp : 1 < p) {H E : Subgroup X} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp hEH hE hk

theorem pRank_three_subgroupOf_le : Open.pRank 3 (P.subgroupOf Lb) ≤ Open.pRank 3 P := by
  refine csSup_le' ?_
  rintro k ⟨E, hEP, hE, hk⟩
  refine le_pRank_of_elemAbelian_le (by norm_num) (E := E.map Lb.subtype) ?_
    (isElemAbelian_map_of_isElemAbelian _ hE)
    (by rw [Subgroup.card_map_of_injective Lb.subtype_injective, hk])
  rintro _ ⟨x, hx, rfl⟩
  exact hEP hx

end Transfer

section Bar

variable {G : Type} [Group G] [Finite G]

theorem exists_parabolic_three_of_nineThreeTwo {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (h2 : NineThreeTwo M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W)) :
    ∃ T₁ : Subgroup ↥(barM M L), IsSylowTwoOf T₁ ⊤ ∧
      Subgroup.normalizer (T₁ : Set ↥(barM M L)) ≤ (blockPL M S L).subgroupOf (barM M L) ∧
      (blockPL M S L).subgroupOf (barM M L) ≠ Subgroup.normalizer (T₁ : Set ↥(barM M L)) ∧
      ∀ U : Subgroup ↥(barM M L), U ≤ (blockPL M S L).subgroupOf (barM M L) → ⁅U, U⁆ = U →
        Nat.Coprime 3 (Nat.card U) := by
  have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
    hS (isSylowTwoOf_inf_of_barM hL.le hA.twoCore_le hA.twoRadical.isPGroup hsyl)
  obtain ⟨T₁, hT₁, hN, hne⟩ := exists_sylowTwo_parabolic_of_nineThreeTwo h2 hns
  refine ⟨T₁, hT₁, hN, hne, fun W hW hWp => ?_⟩
  have h1 := hperf (W.map (barM M L).subtype) (fun x hx => by
      obtain ⟨u, hu, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mp (hW hu))
    (by rw [← Subgroup.map_commutator, hWp])
  rwa [Subgroup.card_map_of_injective (barM M L).subtype_injective] at h1

end Bar

end CFSG.AGLEmbedding
