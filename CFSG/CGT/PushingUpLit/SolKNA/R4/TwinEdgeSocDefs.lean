module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Asc77
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def SocleInvConj (F : Type) [Group F] : Prop :=
  ∀ s t : F, orderOf s = 2 → orderOf t = 2 → ∃ x : F, x * s * x⁻¹ = t

@[expose] def SocleCyc4 (F : Type) [Group F] : Prop :=
  ∀ z : F, orderOf z = 2 → ∀ N₁ N₂ P₁ P₂ : Subgroup F,
    N₁ ≤ Subgroup.centralizer {z} → N₂ ≤ Subgroup.centralizer {z} →
    Subgroup.centralizer {z} ≤ Subgroup.normalizer (N₁ : Set F) →
    Subgroup.centralizer {z} ≤ Subgroup.normalizer (N₂ : Set F) →
    IsSylow2In P₁ N₁ → IsSylow2In P₂ N₂ → IsCyclic P₁ → IsCyclic P₂ →
    4 ≤ Nat.card P₁ → 4 ≤ Nat.card P₂ → ∃ u ∈ P₁ ⊓ P₂, orderOf u = 4

@[expose] def SocleComm2 (F : Type) [Group F] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X), N.Normal → Nonempty (↥N ≃* F) →
    Subgroup.centralizer (N : Set X) = ⊥ → ∀ P : Subgroup X, IsPGroup 2 P → ⁅P, P⁆ ≤ N

@[expose] def SocleOutAbelian (F : Type) [Group F] : Prop :=
  ∀ P : Subgroup (Outer F), IsPGroup 2 P → IsMulCommutative P

structure SocleFactsR (F : Type) [Group F] : Prop where
  inv_conj : SocleInvConj F
  cyc4 : SocleCyc4 F
  comm2 : SocleComm2 F

theorem SocleOutAbelian.of_mulEquiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F')
    (h : SocleOutAbelian F') : SocleOutAbelian F := by
  intro P hP
  let ε : Outer F ≃* Outer F' := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  have hP' : IsPGroup 2 (P.map ε.toMonoidHom) := hP.map _
  have hc := h _ hP'
  let φ : P →* P.map ε.toMonoidHom :=
    (Subgroup.equivMapOfInjective P ε.toMonoidHom ε.injective).toMonoidHom
  have hφ : Function.Injective φ :=
    (Subgroup.equivMapOfInjective P ε.toMonoidHom ε.injective).injective
  refine ⟨⟨fun a b => ?_⟩⟩
  apply hφ
  rw [map_mul, map_mul]
  exact hc.is_comm.comm (φ a) (φ b)

theorem SocleOutAbelian.comm2 {F : Type} [Group F] (h : SocleOutAbelian F) : SocleComm2 F := by
  intro X _ _ N _ ⟨e⟩ hC P hP
  have hN : SocleOutAbelian ↥N := SocleOutAbelian.of_mulEquiv e h
  let Ψ : X →* Outer N :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner N)).comp
      (MulAut.conjNormal : X →* MulAut N)
  have hker : ∀ g : X, Ψ g = 1 → g ∈ N := by
    intro g hg
    have h2 : (MulAut.conjNormal g : MulAut N) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner N :=
      (QuotientGroup.eq_one_iff _).mp hg
    obtain ⟨f, hf⟩ := h2
    have hg' : g⁻¹ * (f : X) ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have key := congrArg (fun α : MulAut N => ((α ⟨y, hy⟩ : N) : X)) hf
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at key
      calc y * (g⁻¹ * (f : X)) = g⁻¹ * (g * y * g⁻¹) * f := by group
        _ = g⁻¹ * ((f : X) * y * (f : X)⁻¹) * f := by rw [key]
        _ = g⁻¹ * f * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hg'
    rw [hg']
    exact f.2
  have hPc : IsMulCommutative ↥(P.map Ψ) := hN _ (hP.map Ψ)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  apply hker
  rw [map_commutatorElement]
  have hcomm : Ψ a * Ψ b = Ψ b * Ψ a :=
    congrArg Subtype.val (hPc.is_comm.comm (⟨Ψ a, Subgroup.mem_map_of_mem Ψ ha⟩ : P.map Ψ)
      ⟨Ψ b, Subgroup.mem_map_of_mem Ψ hb⟩)
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem SocleFactsR.of_parts {F : Type} [Group F] (h1 : SocleInvConj F) (h2 : SocleCyc4 F)
    (h3 : SocleOutAbelian F) : SocleFactsR F :=
  ⟨h1, h2, h3.comm2⟩

theorem SocleInvConj.of_mulEquiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F')
    (h : SocleInvConj F') : SocleInvConj F := by
  intro s t hs ht
  obtain ⟨x, hx⟩ := h (e s) (e t) (by rw [MulEquiv.orderOf_eq]; exact hs)
    (by rw [MulEquiv.orderOf_eq]; exact ht)
  refine ⟨e.symm x, e.injective ?_⟩
  simpa using hx

theorem soc_exists_orderOf_four_of_cyclic {F : Type} [Group F] {P : Subgroup F} [Finite P]
    (hP : IsPGroup 2 P) (hc : IsCyclic P) (h4 : 4 ≤ Nat.card P) : ∃ u ∈ P, orderOf u = 4 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hP)
  rw [ha] at h4
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : a ≤ 1 := by omega
    have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  refine ⟨((g ^ (2 ^ (a - 2)) : P) : F), (g ^ (2 ^ (a - 2))).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow' _ (by positivity), hg, ha, Nat.gcd_eq_right
    (pow_dvd_pow 2 (by omega))]
  have : 2 ^ a = 2 ^ (a - 2) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [this, Nat.mul_div_cancel_left _ (by positivity)]

theorem soc_exists_common_orderOf_four {F : Type} [Group F] [Finite F] {A P₁ P₂ : Subgroup F}
    (hA : IsCyclic A) (h₁ : P₁ ≤ A) (h₂ : P₂ ≤ A) (hp₁ : IsPGroup 2 P₁) (hp₂ : IsPGroup 2 P₂)
    (hc₁ : IsCyclic P₁) (hc₂ : IsCyclic P₂) (hn₁ : 4 ≤ Nat.card P₁) (hn₂ : 4 ≤ Nat.card P₂) :
    ∃ u ∈ P₁ ⊓ P₂, orderOf u = 4 := by
  obtain ⟨u₁, hu₁, ho₁⟩ := soc_exists_orderOf_four_of_cyclic hp₁ hc₁ hn₁
  obtain ⟨u₂, hu₂, ho₂⟩ := soc_exists_orderOf_four_of_cyclic hp₂ hc₂ hn₂
  have hz : ∀ {u : F} (hu : u ∈ A) (ho : orderOf u = 4),
      Nat.card ((Subgroup.zpowers u).subgroupOf A) = 4 := by
    intro u hu ho
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hu)).toEquiv,
      Nat.card_zpowers, ho]
  have hq : (Subgroup.zpowers u₁).subgroupOf A = (Subgroup.zpowers u₂).subgroupOf A :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr
      (by rw [hz (h₁ hu₁) ho₁, hz (h₂ hu₂) ho₂])
  have hmem : u₂ ∈ Subgroup.zpowers u₁ := by
    have : (⟨u₂, h₂ hu₂⟩ : A) ∈ (Subgroup.zpowers u₂).subgroupOf A :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u₂)
    rw [← hq] at this
    exact Subgroup.mem_subgroupOf.mp this
  exact ⟨u₂, Subgroup.mem_inf.mpr ⟨(Subgroup.zpowers_le.mpr hu₁) hmem, hu₂⟩, ho₂⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
