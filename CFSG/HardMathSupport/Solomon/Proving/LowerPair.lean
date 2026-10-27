module

public import CFSG.HardMathSupport.Solomon.Proving.LowerFixed
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance.Alt
open Subgroup

theorem mem_sup_decomp {M : Type*} [Group M] {A B : Subgroup M}
    (h : A ≤ centralizer (B : Set M)) {g : M} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  have hcomm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
    (h m.2 n n.2).symm
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨u.1.1, u.1.2, u.2.1, u.2.2, by
    rw [MonoidHom.noncommCoprod_apply]
    rfl⟩

theorem eq_one_of_mem_inf_center {M : Type*} [Group M] {E : Subgroup M}
    (hEZ : E ⊓ center M = ⊥) {e : M} (he : e ∈ E) (hc : ∀ y : M, e * y = y * e) : e = 1 := by
  have hm : e ∈ E ⊓ center M := ⟨he, Subgroup.mem_center_iff.2 fun y => (hc y).symm⟩
  rw [hEZ] at hm
  exact Subgroup.mem_bot.1 hm

theorem inf_sup_eq_bot_of_comm {Y K₁ K₂ : Type*} [Group Y] [Group K₁] [Group K₂]
    (θ₁ : K₁ →* Y) (θ₂ : K₂ →* Y) (hθ₁ : Function.Injective θ₁) (hθ₂ : Function.Injective θ₂)
    {Cbar : Subgroup Y} {E₁ : Subgroup K₁} {E₂ : Subgroup K₂}
    (hE₁Z : E₁ ⊓ center K₁ = ⊥) (hE₂Z : E₂ ⊓ center K₂ = ⊥)
    (hC1 : ∀ g ∈ Cbar, ∀ y : K₁, Commute g (θ₁ y))
    (hC2 : ∀ g ∈ Cbar, ∀ y : K₂, Commute g (θ₂ y))
    (hE2 : ∀ g ∈ E₂.map θ₂, ∀ y : K₁, Commute g (θ₁ y)) :
    (Cbar ⊔ E₁.map θ₁) ⊓ E₂.map θ₂ = ⊥ := by
  have hCE : Cbar ≤ centralizer ((E₁.map θ₁ : Subgroup Y) : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hh
    exact (hC1 c hc e).eq.symm
  rw [eq_bot_iff]
  rintro g ⟨hgA, hgE⟩
  obtain ⟨c, hc, x, hx, rfl⟩ := mem_sup_decomp hCE hgA
  have hcomm_x : ∀ y : K₁, Commute x (θ₁ y) := by
    intro y
    have h := ((hC1 c hc y).inv_left).mul_left (hE2 (c * x) hgE y)
    rwa [inv_mul_cancel_left] at h
  obtain ⟨e₁, he₁, rfl⟩ := Subgroup.mem_map.1 hx
  have hz₁ : ∀ y : K₁, e₁ * y = y * e₁ := fun y => by
    apply hθ₁
    rw [map_mul, map_mul]
    exact (hcomm_x y).eq
  have he1 : e₁ = 1 := eq_one_of_mem_inf_center hE₁Z he₁ hz₁
  rw [he1, map_one, mul_one] at hgE ⊢
  obtain ⟨e₂, he₂, he₂eq⟩ := Subgroup.mem_map.1 hgE
  have hz₂ : ∀ y : K₂, e₂ * y = y * e₂ := fun y => by
    apply hθ₂
    rw [map_mul, map_mul, he₂eq]
    exact (hC2 c hc y).eq
  have he2 : e₂ = 1 := eq_one_of_mem_inf_center hE₂Z he₂ hz₂
  rw [he2, map_one] at he₂eq
  rw [Subgroup.mem_bot, ← he₂eq]

theorem commute_theta_of_centB {G : Type*} [Group G] [Finite G] {p : ℕ} {B X L : Subgroup G}
    (hL : GLAPComponent p X L) {c : G} (hc : c ∈ centB p B L) (hcX : c ∈ X) (y : barOf p L) :
    Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨c, hcX⟩) (barTheta p hL.1 hL.2.1 y) := by
  induction y using QuotientGroup.induction_on with
  | H ℓ =>
    rw [barTheta_mk]
    exact centB_comm_theta hL hc hcX ℓ

theorem exists_twoLocal_lower_pair {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X B L₁ L₂ : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B)
    (hL₁ : GLAPComponent p X L₁) (hL₂ : GLAPComponent p X L₂)
    (hne : barX p X L₁ ≠ barX p X L₂) (C : Subgroup G)
    (hC₁ : C ≤ centB p B L₁) (hC₂ : C ≤ centB p B L₂)
    (E₁ U : Subgroup (barOf p L₁)) (E₂ : Subgroup (barOf p L₂))
    (hE₁ : IsElemAbelian p E₁) (hE₁Z : E₁ ⊓ Subgroup.center (barOf p L₁) = ⊥)
    (hU : U ≠ ⊥ ∧ IsPGroup 2 U)
    (hEU : E₁ ≤ Subgroup.centralizer (U : Set (barOf p L₁)))
    (hE₂ : IsElemAbelian p E₂) (hE₂Z : E₂ ⊓ Subgroup.center (barOf p L₂) = ⊥) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card C * Nat.card E₁ * Nat.card E₂ ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set ↥X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hCB : C ≤ B := hC₁.trans (centB_le p B L₁)
  have hCX : C ≤ X := hCB.trans hBX
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) :=
    coprime_card_gLAPPrimeCore_aux p ↥X
  set O := GLAPPrimeCore p ↥X with hOdef
  set θ₁ := barTheta p hL₁.1 hL₁.2.1 with hθ₁def
  set θ₂ := barTheta p hL₂.1 hL₂.2.1 with hθ₂def
  have hθ₁inj : Function.Injective θ₁ := barTheta_injective p hL₁.1 hL₁.2.1
  have hθ₂inj : Function.Injective θ₂ := barTheta_injective p hL₂.1 hL₂.2.1
  have hpowB : ∀ z ∈ C, z ^ p = 1 := fun z hz => hB.2 z (hCB hz)
  have hCxmem : ∀ y : ↥(C.subgroupOf X), ((y : ↥X) : G) ∈ C :=
    fun y => Subgroup.mem_subgroupOf.1 y.2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(C.subgroupOf X) →* ↥X ⧸ O,
      ∀ y, ψ y = QuotientGroup.mk (y : ↥X) :=
    ⟨(QuotientGroup.mk' O).comp (C.subgroupOf X).subtype, fun y => rfl⟩
  have hkerC : ∀ z : ↥X, z ∈ O → (z : G) ∈ C → z = 1 := by
    intro z hzO hzC
    apply eq_one_of_mem_coprime hp O hO hzO
    apply Subtype.ext
    simpa using hpowB _ hzC
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hψ] at hy
    have hyO : (y : ↥X) ∈ O := (QuotientGroup.eq_one_iff _).1 hy
    exact Subtype.ext (by simpa using hkerC (y : ↥X) hyO (hCxmem y))
  have hCxcomm : IsMulCommutative ↥(C.subgroupOf X) :=
    ⟨⟨fun y z => Subtype.ext (Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact hB.1.is_comm.comm ⟨_, hCB (hCxmem y)⟩ ⟨_, hCB (hCxmem z)⟩ |> congrArg Subtype.val))⟩⟩
  have hCxpow : ∀ y : ↥(C.subgroupOf X), y ^ p = 1 := fun y =>
    Subtype.ext (Subtype.ext (by simpa using hpowB _ (hCxmem y)))
  set Cbar := ψ.range with hCbar
  set E₁b := E₁.map θ₁ with hE₁b
  set E₂b := E₂.map θ₂ with hE₂b
  set Tbar := U.map θ₁ with hTbar
  have hmemC : ∀ g ∈ Cbar, ∃ x : ↥X, (x : G) ∈ C ∧ g = QuotientGroup.mk x := by
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hg
    exact ⟨(y : ↥X), hCxmem y, hψ y⟩
  have hCbar_el : IsElemAbelian p Cbar := isElemAbelian_range' ψ hCxcomm hCxpow
  have hE₁b_el : IsElemAbelian p E₁b := isElemAbelian_map' θ₁ hE₁
  have hE₂b_el : IsElemAbelian p E₂b := isElemAbelian_map' θ₂ hE₂
  have hCardC : Nat.card Cbar = Nat.card C := by
    show Nat.card ψ.range = Nat.card C
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv)
  have hCardE₁ : Nat.card E₁b = Nat.card E₁ := Subgroup.card_map_of_injective hθ₁inj
  have hCardE₂ : Nat.card E₂b = Nat.card E₂ := Subgroup.card_map_of_injective hθ₂inj
  have hC1 : ∀ g ∈ Cbar, ∀ y : barOf p L₁, Commute g (θ₁ y) := by
    intro g hg y
    obtain ⟨x, hx, rfl⟩ := hmemC g hg
    exact commute_theta_of_centB hL₁ (hC₁ hx) x.2 y
  have hC2 : ∀ g ∈ Cbar, ∀ y : barOf p L₂, Commute g (θ₂ y) := by
    intro g hg y
    obtain ⟨x, hx, rfl⟩ := hmemC g hg
    exact commute_theta_of_centB hL₂ (hC₂ hx) x.2 y
  have hE2 : ∀ g ∈ E₂b, ∀ y : barOf p L₁, Commute g (θ₁ y) := by
    intro g hg y
    obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hg
    have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL₁.2.2.1 hL₂.2.2.1 hne)
    have hy : θ₁ y ∈ barX p X L₁ := by
      rw [← barTheta_range p hL₁.1 hL₁.2.1]
      exact ⟨y, rfl⟩
    have hg2 : θ₂ e ∈ barX p X L₂ := by
      rw [← barTheta_range p hL₂.1 hL₂.2.1]
      exact ⟨e, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcomm hy) (θ₂ e) hg2
  have hdisj1 : Cbar ⊓ E₁b = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgC, hgE⟩
    obtain ⟨e, he, hgeq⟩ := Subgroup.mem_map.1 hgE
    have hz : ∀ y : barOf p L₁, e * y = y * e := fun y => by
      apply hθ₁inj
      rw [map_mul, map_mul, hgeq]
      exact (hC1 g hgC y).eq
    have he1 : e = 1 := eq_one_of_mem_inf_center hE₁Z he hz
    rw [Subgroup.mem_bot, ← hgeq, he1, map_one]
  have hCE1 : Cbar ≤ centralizer (E₁b : Set (↥X ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hh
    exact (hC1 g hg e).eq.symm
  obtain ⟨hAel, hAcard⟩ := isElemAbelian_sup_card hCE1 hdisj1 hCbar_el hE₁b_el
  have hAE2 : Cbar ⊔ E₁b ≤ Subgroup.centralizer (E₂b : Set (↥X ⧸ O)) := by
    refine sup_le ?_ ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hh
      exact (hC2 g hg e).eq.symm
    · intro g hg
      obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hE2 h hh e).eq
  have hdisjA : (Cbar ⊔ E₁b) ⊓ E₂b = ⊥ :=
    inf_sup_eq_bot_of_comm θ₁ θ₂ hθ₁inj hθ₂inj hE₁Z hE₂Z hC1 hC2 hE2
  obtain ⟨hJc, hJcard⟩ := isElemAbelian_sup_card hAE2 hdisjA hAel hE₂b_el
  have hTne : Tbar ≠ ⊥ := by
    intro hbot
    apply hU.1
    rw [eq_bot_iff]
    intro u hu
    have hmem : θ₁ u ∈ Tbar := Subgroup.mem_map_of_mem θ₁ hu
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact hθ₁inj (by rw [hmem, map_one])
  have hTp : IsPGroup 2 Tbar := hU.2.map θ₁
  have hPcent : (Cbar ⊔ E₁b) ⊔ E₂b ≤ Subgroup.centralizer ((Tbar : Subgroup (↥X ⧸ O)) : Set (↥X ⧸ O)) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.1 hh
      exact (hC1 g hg u).eq.symm
    · intro g hg
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hh
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_iff.1 (hEU he) u hu
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.1 hh
      exact (hE2 g hg u).eq.symm
  have hPnorm := hPcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨P, S, hPc, hPp, hPcard, hS1, hS2, hPS⟩ :=
    exists_lift_twoLocal_of_le_normalizer hp hp2 O hO ((Cbar ⊔ E₁b) ⊔ E₂b) Tbar hJc
      ⟨hTne, hTp⟩ hPnorm
  refine ⟨P, S, hPc, hPp, ?_, hS1, hS2, hPS⟩
  rw [hPcard, hJcard, hAcard, hCardC, hCardE₁, hCardE₂]

end CFSG.HardMathSupport.Solomon.Proving
