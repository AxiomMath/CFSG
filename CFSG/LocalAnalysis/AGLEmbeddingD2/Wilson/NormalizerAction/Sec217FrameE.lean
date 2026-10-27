module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3AutTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3OuterKey
public import CFSG.RankThree.PartTwo.KFacts.K426RestMcL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic CFSG.Blueprint
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem false_of_pure3B {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ3 : Nat.card (center ↥L) = 3)
    (ψ : ↥L ⧸ center ↥L ≃* ↥j3P) {E U : Subgroup G} (hEL : E ≤ L)
    (hZE : ∀ z ∈ center ↥L, (z : G) ∈ E) (hE27 : Nat.card E = 27)
    (hE3 : ∀ x : ↥L, (x : G) ∈ E → x ^ 3 ∈ center ↥L)
    (hEB : ∀ x : ↥L, (x : G) ∈ E → x ∉ center ↥L →
      Nat.card (centralizer ({(x : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) = 243)
    (hUN : U ≤ normalizer (L : Set G)) (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hEU : ∀ x ∈ E, ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hLU : ⁅L, U⁆ = L) : False := by
  obtain ⟨T, hTR, hTinj, hTconj⟩ := exists_toR hq.1 ψ
  set Φ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6156) := T.comp L.normalizerMonoidHom with hΦ
  have hΦapp : ∀ (n : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L),
      (((L.normalizerMonoidHom n) x : ↥L) : G) = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hmemN : ∀ x : ↥L, (x : G) ∈ (Subgroup.normalizer (L : Set G)) := fun x => Subgroup.le_normalizer x.2
  have hΦL : ∀ x : ↥L, Φ ⟨(x : G), hmemN x⟩ =
      ((ψ (x : ↥L ⧸ center ↥L) : ↥j3P) : Equiv.Perm (Fin 6156)) := by
    intro x
    have : L.normalizerMonoidHom ⟨(x : G), hmemN x⟩ = MulAut.conj x :=
      MulEquiv.ext fun y => Subtype.ext (by rw [hΦapp]; simp [MulAut.conj_apply])
    show T (L.normalizerMonoidHom ⟨(x : G), hmemN x⟩) = _
    rw [this, hTconj]
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥L →* Equiv.Perm (Fin 6156), ∀ x : ↥L,
      θ x = ((ψ (x : ↥L ⧸ center ↥L) : ↥j3P) : Equiv.Perm (Fin 6156)) :=
    ⟨(j3P.subtype).comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))), fun x => rfl⟩
  have hθker : θ.ker = center ↥L := by
    ext x
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro h
      have h1 : ψ (x : ↥L ⧸ center ↥L) = 1 := Subtype.ext h
      rw [← QuotientGroup.eq_one_iff]
      exact (map_eq_one_iff _ ψ.injective).1 h1
    · intro h
      have : (x : ↥L ⧸ center ↥L) = 1 := (QuotientGroup.eq_one_iff x).2 h
      rw [this, map_one]; rfl
  set EX : Subgroup ↥L := E.subgroupOf L with hEX
  have hEXmem : ∀ x : ↥L, x ∈ EX ↔ (x : G) ∈ E := fun x => Subgroup.mem_subgroupOf
  have hEXcard : Nat.card EX = 27 := by
    rw [hEX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE27]
  have hZEX : center ↥L ≤ EX := fun z hz => (hEXmem z).2 (hZE z hz)
  set E' : Subgroup (Equiv.Perm (Fin 6156)) := EX.map θ with hE'
  have hE'card : Nat.card E' * 3 = 27 := by
    have := card_map_mul_ker θ EX (hθker.le.trans hZEX)
    rw [hθker, hZ3, hEXcard] at this
    exact this.symm
  set W : Subgroup (Equiv.Perm (Fin 6156)) := (U.subgroupOf (Subgroup.normalizer (L : Set G))).map Φ with hW
  have hUsub : Nat.card (U.subgroupOf (Subgroup.normalizer (L : Set G))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv, hU4]
  have hWle : W ≤ j3R := by
    rintro _ ⟨n, -, rfl⟩
    exact hTR _
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_pow]
    have : n ^ 2 = 1 := Subtype.ext (by simpa using hU2 n (Subgroup.mem_subgroupOf.1 hn))
    rw [this, map_one]
  have hW4 : Nat.card W ≤ 4 := by
    rw [← hUsub]
    exact Nat.card_le_card_of_surjective (Φ.subgroupMap (U.subgroupOf (Subgroup.normalizer (L : Set G))))
      (Φ.subgroupMap_surjective _)
  have hE'P : E' ≤ j3P := by
    rintro _ ⟨x, -, rfl⟩
    rw [hθ]; exact (ψ _).2
  have hE'3 : ∀ b ∈ E', b ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : θ (x ^ 3) = 1 := by
      rw [← MonoidHom.mem_ker, hθker]
      exact hE3 x ((hEXmem x).1 hx)
    exact this
  have hE'9 : 9 ≤ Nat.card E' := by omega
  have hodd : ∀ b ∈ E', b ≠ 1 →
      Odd (Nat.card (centralizer ({b} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156)))) := by
    rintro _ ⟨x, hx, rfl⟩ hb1
    have hxc : x ∉ center ↥L := by
      intro hxc
      apply hb1
      rw [← MonoidHom.mem_ker, hθker]
      exact hxc
    rw [hθ, ← CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ,
      hEB x ((hEXmem x).1 hx) hxc]
    exact ⟨121, by norm_num⟩
  have hNW : ∀ b ∈ E', ∀ w ∈ W, b * w * b⁻¹ ∈ W := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨n, hn, rfl⟩
    have hxE : (x : G) ∈ E := (hEXmem x).1 hx
    have hnU : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
    have hconj : (⟨(x : G), hmemN x⟩ : ↥(Subgroup.normalizer (L : Set G))) * n * (⟨(x : G), hmemN x⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ ∈
        U.subgroupOf (Subgroup.normalizer (L : Set G)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hEU _ hxE _ hnU
    have := Subgroup.mem_map_of_mem Φ hconj
    rw [map_mul, map_mul, map_inv, hΦL] at this
    rw [hθ]
    exact this
  have hW0 : W = ⊥ := R_key hWle hW2 hW4 hE'P hE'3 hE'9 hodd hNW
  have hUc : ∀ u ∈ U, ∀ x ∈ L, u * x * u⁻¹ = x := by
    intro u hu x hx
    have hΦu : Φ ⟨u, hUN hu⟩ = 1 := by
      have : Φ ⟨u, hUN hu⟩ ∈ W := Subgroup.mem_map_of_mem Φ (Subgroup.mem_subgroupOf.2 hu)
      rw [hW0] at this
      exact Subgroup.mem_bot.1 this
    have hσ : L.normalizerMonoidHom ⟨u, hUN hu⟩ = 1 := hTinj _ hΦu
    have := congrArg (fun σ : MulAut ↥L => ((σ ⟨x, hx⟩ : ↥L) : G)) hσ
    simpa [hΦapp] using this
  have hcomm : ⁅L, U⁆ = ⊥ := by
    rw [Subgroup.commutator_def, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    show ⁅l, u⁆ = 1
    rw [commutatorElement_def]
    have h1 := hUc u hu l hl
    have hc : u * l = l * u := by
      calc u * l = (u * l * u⁻¹) * u := by group
        _ = l * u := by rw [h1]
    rw [← hc]; group
  have hL0 : L = ⊥ := by rw [← hLU, hcomm]
  haveI : Subsingleton ↥L := ⟨fun a b => Subtype.ext
    ((Subgroup.mem_bot.1 (hL0 ▸ a.2)).trans (Subgroup.mem_bot.1 (hL0 ▸ b.2)).symm)⟩
  have : Nat.card (center ↥L) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨⟨1, one_mem _⟩⟩⟩
  omega

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
