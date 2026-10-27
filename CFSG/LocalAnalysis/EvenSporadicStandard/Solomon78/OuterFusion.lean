module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

@[expose] def AutCenterCond (Y : Type) [Group Y] : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν →
    (∀ y : Y, ν y = y → σ y = y) → σ = 1 ∨ σ = ν

@[expose] def AutCenterCondExc (Y : Type) [Group Y] (Exc : MulAut Y → Prop) : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν →
    (∀ y : Y, ν y = y → σ y = y) → σ = 1 ∨ σ = ν ∨ Exc ν

theorem AutCenterCond.toExc {Y : Type} [Group Y] (h : AutCenterCond Y) :
    AutCenterCondExc Y (fun _ => False) := fun ν σ hν hσ hνσ hfix =>
  (h ν σ hν hσ hνσ hfix).imp id Or.inl

theorem AutCenterCondExc.toCond {Y : Type} [Group Y] (h : AutCenterCondExc Y (fun _ => False)) :
    AutCenterCond Y := fun ν σ hν hσ hνσ hfix =>
  (h ν σ hν hσ hνσ hfix).elim Or.inl fun h' => h'.elim Or.inr False.elim

theorem AutCenterCond.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : AutCenterCond Y) : AutCenterCond Y' := by
  intro ν σ hν hσ hνσ hfix
  let φ : MulAut Y' → MulAut Y := fun a => (e.trans a).trans e.symm
  have hφ : ∀ (a : MulAut Y') (y : Y), φ a y = e.symm (a (e y)) := fun a y => rfl
  have hmul : ∀ a b : MulAut Y', φ (a * b) = φ a * φ b := fun a b => MulEquiv.ext fun y => by
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, MulEquiv.apply_symm_apply]
  have hone : φ 1 = 1 := MulEquiv.ext fun y => by
    rw [hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  have h1 := h (φ ν) (φ σ) (by rw [← hmul, hν, hone]) (by rw [← hmul, hσ, hone])
    (by rw [← hmul, ← hmul, hνσ]) (by
      intro y hy
      rw [hφ] at hy ⊢
      have h2 : ν (e y) = e y := by
        have := congrArg e hy
        rwa [MulEquiv.apply_symm_apply] at this
      rw [hfix _ h2, MulEquiv.symm_apply_apply])
  have h3 : ∀ a b : MulAut Y', φ a = φ b → a = b := fun a b hab => MulEquiv.ext fun y' => by
    have := congrArg (fun f : MulAut Y => e (f (e.symm y'))) hab
    simpa [hφ] using this
  rcases h1 with h1 | h1
  · exact Or.inl (h3 _ _ (h1.trans hone.symm))
  · exact Or.inr (h3 _ _ h1)


@[expose] def fixSubgroup {Y : Type} [Group Y] (ν : MulAut Y) : Subgroup Y where
  carrier := {y | ν y = y}
  mul_mem' := fun {a b} (ha : ν a = a) (hb : ν b = b) => by
    show ν (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one ν
  inv_mem' := fun {a} (ha : ν a = a) => by
    show ν a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem AutCenterCondExc.of_mulEquiv_card {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    {c : ℕ} (h : AutCenterCondExc Y (fun α => Nat.card (fixSubgroup α) = c)) :
    AutCenterCondExc Y' (fun α => Nat.card (fixSubgroup α) = c) := by
  intro ν σ hν hσ hνσ hfix
  let φ : MulAut Y' → MulAut Y := fun a => (e.trans a).trans e.symm
  have hφ : ∀ (a : MulAut Y') (y : Y), φ a y = e.symm (a (e y)) := fun a y => rfl
  have hmul : ∀ a b : MulAut Y', φ (a * b) = φ a * φ b := fun a b => MulEquiv.ext fun y => by
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, MulEquiv.apply_symm_apply]
  have hone : φ 1 = 1 := MulEquiv.ext fun y => by
    rw [hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  have h1 := h (φ ν) (φ σ) (by rw [← hmul, hν, hone]) (by rw [← hmul, hσ, hone])
    (by rw [← hmul, ← hmul, hνσ]) (by
      intro y hy
      rw [hφ] at hy ⊢
      have h2 : ν (e y) = e y := by
        have := congrArg e hy
        rwa [MulEquiv.apply_symm_apply] at this
      rw [hfix _ h2, MulEquiv.symm_apply_apply])
  have h3 : ∀ a b : MulAut Y', φ a = φ b → a = b := fun a b hab => MulEquiv.ext fun y' => by
    have := congrArg (fun f : MulAut Y => e (f (e.symm y'))) hab
    simpa [hφ] using this
  rcases h1 with h1 | h1 | h1
  · exact Or.inl (h3 _ _ (h1.trans hone.symm))
  · exact Or.inr (Or.inl (h3 _ _ h1))
  · refine Or.inr (Or.inr ?_)
    rw [← h1]
    refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun y' => ?_)
    show ν y' = y' ↔ φ ν (e.symm y') = e.symm y'
    rw [hφ, MulEquiv.apply_symm_apply]
    constructor
    · intro h'
      rw [h']
    · intro h'
      exact e.symm.injective h'

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem normalizerMonoidHom_coe {g : G} (hg : g ∈ normalizer (L : Set G)) (x : L) :
    ((L.normalizerMonoidHom ⟨g, hg⟩ x : L) : G) = g * x * g⁻¹ := rfl

theorem exists_fusion_pair (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) {t' : G} (ht' : t' ∈ fusedSet u t) {c : G}
    (hc : c * t * c⁻¹ = t') :
    ∃ (u₁ : G) (hN : u₁ ∈ normalizer (L : Set G)) (ν σ : MulAut L),
      u₁ = c⁻¹ * u * c ∧ u₁ * u₁ = 1 ∧ u₁ * t = t * u₁ ∧
      ν = L.normalizerMonoidHom ⟨u₁, hN⟩ ∧
      (∀ y : L, ((σ y : L) : G) = (c⁻¹ * t * c) * y * (c⁻¹ * t * c)⁻¹) ∧
      ν * ν = 1 ∧ σ * σ = 1 ∧ ν * σ = σ * ν ∧ (∀ y : L, ν y = y → σ y = y) ∧
      (σ = 1 → t' = t) ∧ (σ = ν → t' = u * t) := by
  obtain ⟨-, hcu, hct⟩ := ht'
  have := h.simpleL
  have ht2 := h.t_order
  have htt := mul_self_eq_one_of_orderOf_eq_two ht2
  have huu := mul_self_eq_one_of_orderOf_eq_two h.u_order
  have hZ : center L = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have htL : t ∉ L := not_mem_of_center_eq_bot h.t_mem ht2 hZ
  have hCt := centralizer_eq_zpowers_of_hyp38 hStd hS h
  have hCu := centralizer_u_le_centralizer_t hStd hS h
  have hMN := hStd.centralizer_le_normalizer h.t_mem ht2
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = c⁻¹ * u * c := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, t₂ = c⁻¹ * t * c := ⟨_, rfl⟩
  have hu₁t : u₁ * t = t * u₁ := by
    have h1 : c * t * c⁻¹ * u = u * (c * t * c⁻¹) := by rw [hc]; exact hcu
    calc u₁ * t = c⁻¹ * (u * (c * t * c⁻¹)) * c := by rw [hu₁]; group
      _ = c⁻¹ * (c * t * c⁻¹ * u) * c := by rw [h1]
      _ = t * u₁ := by rw [hu₁]; group
  have ht₂t : t₂ * t = t * t₂ := by
    have h2 : c * t * c⁻¹ * t = t * (c * t * c⁻¹) := by rw [hc]; exact hct
    calc t₂ * t = c⁻¹ * (t * (c * t * c⁻¹)) * c := by rw [ht₂]; group
      _ = c⁻¹ * (c * t * c⁻¹ * t) * c := by rw [h2]
      _ = t * t₂ := by rw [ht₂]; group
  have ht₂u₁ : t₂ * u₁ = u₁ * t₂ := by
    calc t₂ * u₁ = c⁻¹ * (t * u) * c := by rw [ht₂, hu₁]; group
      _ = c⁻¹ * (u * t) * c := by rw [h.u_comm_t.symm]
      _ = u₁ * t₂ := by rw [ht₂, hu₁]; group
  have hu₁₂ : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = c⁻¹ * (u * u) * c := by rw [hu₁]; group
      _ = 1 := by rw [huu]; group
  have ht₂₂ : t₂ * t₂ = 1 := by
    calc t₂ * t₂ = c⁻¹ * (t * t) * c := by rw [ht₂]; group
      _ = 1 := by rw [htt]; group
  have hcent : ∀ x : G, x * u₁ = u₁ * x → x * t₂ = t₂ * x := by
    intro x hxu
    have hx'u : c * x * c⁻¹ ∈ centralizer ({u} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      show c * x * c⁻¹ * u = u * (c * x * c⁻¹)
      rw [hu₁] at hxu
      calc c * x * c⁻¹ * u = c * (x * (c⁻¹ * u * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * u * c * x) * c⁻¹ := by rw [hxu]
        _ = u * (c * x * c⁻¹) := by group
    have hx't : c * x * c⁻¹ * t = t * (c * x * c⁻¹) := mem_centralizer_singleton_iff.1 (hCu hx'u)
    calc x * t₂ = c⁻¹ * (c * x * c⁻¹ * t) * c := by rw [ht₂]; group
      _ = c⁻¹ * (t * (c * x * c⁻¹)) * c := by rw [hx't]
      _ = t₂ * x := by rw [ht₂]; group
  have hu₁N : u₁ ∈ normalizer (L : Set G) := hMN (mem_centralizer_singleton_iff.2 hu₁t)
  have ht₂N : t₂ ∈ normalizer (L : Set G) := hMN (mem_centralizer_singleton_iff.2 ht₂t)
  set ν : MulAut L := L.normalizerMonoidHom ⟨u₁, hu₁N⟩ with hν
  set σ : MulAut L := L.normalizerMonoidHom ⟨t₂, ht₂N⟩ with hσ
  have hνν : ν * ν = 1 := by
    rw [hν, ← map_mul, ← map_one L.normalizerMonoidHom]
    congr 1
    exact Subtype.ext hu₁₂
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul, ← map_one L.normalizerMonoidHom]
    congr 1
    exact Subtype.ext ht₂₂
  have hνσ : ν * σ = σ * ν := by
    rw [hν, hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ht₂u₁.symm
  have hfix : ∀ y : L, ν y = y → σ y = y := by
    intro y hy
    have h1 : u₁ * (y : G) * u₁⁻¹ = y := by
      have := congrArg Subtype.val hy
      rwa [hν, normalizerMonoidHom_coe] at this
    have h2 : (y : G) * u₁ = u₁ * y := by
      calc (y : G) * u₁ = (u₁ * y * u₁⁻¹) * u₁ := by rw [h1]
        _ = u₁ * y := by group
    have h3 := hcent y h2
    apply Subtype.ext
    rw [hσ, normalizerMonoidHom_coe]
    calc t₂ * (y : G) * t₂⁻¹ = (y : G) * t₂ * t₂⁻¹ := by rw [h3]
      _ = y := by group
  have hmemC : ∀ g : G, (∀ y : L, g * (y : G) * g⁻¹ = (y : G)) → g ∈ centralizer (L : Set G) := by
    intro g hg
    refine mem_centralizer_iff.2 fun y hy => ?_
    have := hg ⟨y, hy⟩
    calc y * g = (g * y * g⁻¹) * g := by rw [this]
      _ = g * y := by group
  have hnotone : t₂ ≠ 1 := by
    intro e
    apply ne_one_of_orderOf_eq_two ht2
    have h1 : c⁻¹ * t * c = 1 := ht₂.symm.trans e
    have h2 : t = c * (c⁻¹ * t * c) * c⁻¹ := by group
    rw [h2, h1]
    group
  refine ⟨u₁, hu₁N, ν, σ, hu₁, hu₁₂, hu₁t, rfl, fun y => ?_, hνν, hσσ, hνσ, hfix, ?_, ?_⟩
  · rw [hσ, normalizerMonoidHom_coe, ht₂]
  · intro h1
    have h2 : t₂ ∈ centralizer (L : Set G) := by
      refine hmemC t₂ fun y => ?_
      have e1 : ((σ y : L) : G) = (((1 : MulAut L) y : L) : G) := by rw [h1]
      rw [hσ, normalizerMonoidHom_coe] at e1
      exact e1
    rw [hCt] at h2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
    rcases zpow_eq_one_or_self_of_orderOf_eq_two ht2 k with h3 | h3
    · exact absurd (hk.symm.trans h3) hnotone
    · have h4 : c⁻¹ * t * c = t := ht₂.symm.trans (hk.symm.trans h3)
      have h5 : c * t = t * c := by
        calc c * t = c * (c⁻¹ * t * c) := by rw [h4]
          _ = t * c := by group
      rw [← hc, h5]
      group
  · intro h1
    have h2 : u₁⁻¹ * t₂ ∈ centralizer (L : Set G) := by
      refine hmemC _ fun y => ?_
      have e1 : ((σ y : L) : G) = ((ν y : L) : G) := by rw [h1]
      rw [hσ, hν, normalizerMonoidHom_coe, normalizerMonoidHom_coe] at e1
      calc u₁⁻¹ * t₂ * (y : G) * (u₁⁻¹ * t₂)⁻¹ = u₁⁻¹ * (t₂ * (y : G) * t₂⁻¹) * u₁ := by group
        _ = u₁⁻¹ * (u₁ * (y : G) * u₁⁻¹) * u₁ := by rw [e1]
        _ = y := by group
    rw [hCt] at h2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
    rcases zpow_eq_one_or_self_of_orderOf_eq_two ht2 k with h3 | h3
    · exfalso
      have h4 : u₁⁻¹ * t₂ = 1 := hk.symm.trans h3
      have h5 : u₁ = t₂ := by
        have := congrArg (fun x => u₁ * x) h4
        simpa using this.symm
      rw [hu₁, ht₂] at h5
      have h6 : u = t := by
        have := mul_right_cancel h5
        exact mul_left_cancel this
      exact htL (h6 ▸ h.u_mem)
    · have h4 : u₁⁻¹ * t₂ = t := hk.symm.trans h3
      have h5 : t₂ = u₁ * t := by
        calc t₂ = u₁ * (u₁⁻¹ * t₂) := by group
          _ = u₁ * t := by rw [h4]
      have h6 : t = u * t' := by
        calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
          _ = c * (u₁ * t) * c⁻¹ := by rw [← ht₂, h5]
          _ = c * (c⁻¹ * u * c * t) * c⁻¹ := by rw [hu₁]
          _ = u * (c * t * c⁻¹) := by group
          _ = u * t' := by rw [hc]
      calc t' = u * (u * t') := by rw [← mul_assoc, huu, one_mul]
        _ = u * t := by rw [← h6]

theorem sol78Fusion_of_autCenterExc (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) {Exc : MulAut L → Prop} (hacc : AutCenterCondExc L Exc)
    (hExc : ∀ u₁ (hN : u₁ ∈ normalizer (L : Set G)), u₁ * u₁ = 1 → u₁ * t = t * u₁ →
      IsConj u u₁ → ¬ Exc (L.normalizerMonoidHom ⟨u₁, hN⟩)) : Sol78Fusion u t := by
  intro t' ht'
  by_cases hne : t' = t
  · exact Or.inl hne
  right
  obtain ⟨c, hc⟩ := isConj_iff.1 ht'.1
  obtain ⟨u₁, hN, ν, σ, hu₁, hu₁₂, hu₁t, hν, -, hνν, hσσ, hνσ, hfix, h1, h2⟩ :=
    exists_fusion_pair hStd hS h ht' hc
  rcases hacc ν σ hνν hσσ hνσ hfix with h3 | h3 | h3
  · exact absurd (h1 h3) hne
  · exact h2 h3
  · rw [hν] at h3
    exact absurd h3 (hExc u₁ hN hu₁₂ hu₁t (isConj_iff.2 ⟨c⁻¹, by rw [hu₁]; group⟩))

theorem sol78Fusion_of_autCenter (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) (hacc : AutCenterCond L) : Sol78Fusion u t :=
  sol78Fusion_of_autCenterExc hStd hS h (Exc := fun _ => False) hacc.toExc
    fun _ _ _ _ _ h' => h'

end CFSG.EvenSporadicStandard.Solomon78
