module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfg
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def ThreeCfg {G : Type*} [Group G] (I : Subgroup G) : Prop :=
  ∃ P W : Subgroup G, IsSylowOf 2 P I ∧ IsPGroup 3 ↥W ∧ W ≠ ⊥ ∧ P ≤ normalizer (W : Set G)

section Sylow

theorem isSylowOf_map_iff {K G : Type*} [Group K] [Group G] [Finite K] [Finite G] {p : ℕ}
    [Fact p.Prime] (f : K →* G) (hf : Function.Injective f) {P X : Subgroup K} :
    IsSylowOf p (P.map f) (X.map f) ↔ IsSylowOf p P X := by
  rw [isSylowOf_iff, isSylowOf_iff, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.map_le_map_iff_of_injective hf]
  have : IsPGroup p ↥(P.map f) ↔ IsPGroup p ↥P := by
    constructor
    · intro h
      exact h.of_equiv (P.equivMapOfInjective f hf).symm
    · intro h
      exact h.of_equiv (P.equivMapOfInjective f hf)
  rw [this]

theorem threeCfg_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] (Θ : G ≃* G')
    {I : Subgroup G} (h : ThreeCfg I) : ThreeCfg (I.map Θ.toMonoidHom) := by
  obtain ⟨P, W, hP, hW3, hWne, hPW⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨P.map Θ.toMonoidHom, W.map Θ.toMonoidHom,
    (isSylowOf_map_iff Θ.toMonoidHom Θ.injective).2 hP, ?_, ?_, ?_⟩
  · exact hW3.of_equiv (W.equivMapOfInjective Θ.toMonoidHom Θ.injective)
  · intro hb
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective W Θ.injective).1 hb)
  · exact (Subgroup.map_mono hPW).trans (Subgroup.le_normalizer_map Θ.toMonoidHom)

end Sylow

section Aut

theorem finite_mulAut' (Y : Type*) [Group Y] [Finite Y] : Finite (MulAut Y) :=
  Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)

instance normal_innSub' (Y : Type) [Group Y] : (innSub Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem conj_injective_of_center_bot {Y : Type*} [Group Y] (hc : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut Y => φ z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc z * g = g * z * g⁻¹ * g := by rw [hz]
      _ = g * z := by group
  rw [hc] at this
  exact this

theorem threeCfg_of_sylCfgOf_inner {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (h : SylCfgOf Y) :
    ThreeCfg (⊤ : Subgroup Y) := by
  obtain ⟨T, W, hcfg⟩ := h
  obtain ⟨P, hPT, hPinn, hPsyl⟩ := hcfg.syl
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c : Y →* MulAut Y := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective_of_center_bot hc
  have hrange : innSub Y = c.range := rfl
  have hcardI : Nat.card ↥(innSub Y) = Nat.card Y := by
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hWI : W ≤ innSub Y := by
    refine CFSG.Sporadic.SmallOddCore.odd_card_map_le_of_index_le_two (innSub Y) ?_ ?_
    · rw [hcardI]
      exact hcard
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcfg.w3
      rw [hn]
      exact Odd.pow (by decide)
  have hPc : P ≤ c.range := hPinn
  have hWc : W ≤ c.range := hWI
  refine ⟨P.comap c, W.comap c, ?_, ?_, ?_, ?_⟩
  · have h1 : (P.comap c).map c = P := Subgroup.map_comap_eq_self hPc
    have h2 : (⊤ : Subgroup Y).map c = innSub Y := (MonoidHom.range_eq_map c).symm
    have h3 : IsSylowOf 2 ((P.comap c).map c) ((⊤ : Subgroup Y).map c) := by
      rw [h1, h2]
      exact hPsyl
    exact (isSylowOf_map_iff c hinj).1 h3
  · refine IsPGroup.comap_of_ker_isPGroup hcfg.w3 c ?_
    rw [(MonoidHom.ker_eq_bot_iff c).2 hinj]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup Y) = 3 ^ 0)
  · intro hb
    apply hcfg.w_ne
    rw [← Subgroup.map_comap_eq_self hWc, hb, Subgroup.map_bot]
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyT : c y ∈ T := hPT hy
    have := Subgroup.mem_normalizer_iff.mp (hcfg.t_norm hyT) (c z)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this

theorem threeCfg_of_sylCfgOf_aut {Y : Type} [Group Y] [Finite Y] {G : Type*} [Group G] [Finite G]
    (Θ : G ≃* MulAut Y) {I : Subgroup G} (hI : I.map Θ.toMonoidHom = innSub Y)
    (h : SylCfgOf Y) : ThreeCfg I := by
  obtain ⟨T, W, hcfg⟩ := h
  obtain ⟨P, hPT, hPinn, hPsyl⟩ := hcfg.syl
  have hfin : Finite (MulAut Y) := finite_mulAut' Y
  have h0 : ThreeCfg (innSub Y) :=
    ⟨P, W, hPsyl, hcfg.w3, hcfg.w_ne, hPT.trans hcfg.t_norm⟩
  have h1 := threeCfg_map Θ.symm h0
  have h2 : (innSub Y).map Θ.symm.toMonoidHom = I := by
    rw [← hI, Subgroup.map_map]
    have : Θ.symm.toMonoidHom.comp Θ.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rwa [h2] at h1

end Aut

section Criterion

theorem isPGroup_two_closure_of_comm {G : Type*} [Group G] (s : Set G) (h2 : ∀ x ∈ s, x * x = 1)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsPGroup 2 ↥(closure s) := by
  have hpair : s.Pairwise Commute := fun x hx y hy _ => hc x hx y hy
  have := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ g₁ ∈ closure s, ∀ g₂ ∈ closure s, g₁ * g₂ = g₂ * g₁ := by
    intro g₁ h₁ g₂ h₂
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨g₁, h₁⟩ : closure s) ⟨g₂, h₂⟩)
  have hsq : ∀ g ∈ closure s, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact h2 x hx
    | one => exact mul_one 1
    | mul x y hx hy hx1 hy1 =>
      have hxy := hcomm x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx1, hy1, one_mul]
    | inv x hx hx1 =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx1, inv_one]
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg2 : (g : G) ^ 2 = 1 := by rw [sq]; exact hsq g g.2
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hg2))
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

end Criterion

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
