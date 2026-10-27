module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Shape
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Y

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section Gen

variable {G : Type*} [Group G]

theorem nd11s_sq_mem_closure {S : Set G} {T : Subgroup G}
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a)
    (hS : ∀ s ∈ S, s * s ∈ T) : ∀ x ∈ Subgroup.closure S, x * x ∈ T := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y hx hy hx' hy' =>
    have e : x * y * (x * y) = (x * x) * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
    rw [e]
    exact mul_mem hx' hy'
  | inv x hx hx' =>
    have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [e]
    exact inv_mem hx'

end Gen

section Structure

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem nd11s_K0_comm_F : ∀ k ∈ K0 d z₀, ∀ f ∈ d.F, k * f = f * k := fun _ hk _ hf =>
  (comm_of_conj_eq (s56_P_conj_F d (mem_K0_iff.1 hk).1.2 hf)).symm

theorem nd11s_sq_K0F (hd : d.Hyp) {T : Subgroup G} (hk : ∀ k ∈ K0 d z₀, k * k ∈ T) {x : G}
    (hx : x ∈ K0 d z₀ ⊔ d.F) : x * x ∈ T := by
  have hc := nd11s_K0_comm_F (d := d) (z₀ := z₀)
  have hx' : x ∈ ((K0 d z₀ ⊔ d.F : Subgroup G) : Set G) := hx
  rw [S56.coe_sup_eq_mul_of_comm hc] at hx'
  obtain ⟨k, hk', f, hf, rfl⟩ := hx'
  have hfk : f * k = k * f := (hc k hk' f hf).symm
  have e : k * f * (k * f) = (k * k) * (f * f) := by
    calc k * f * (k * f) = k * (f * k) * f := by group
      _ = k * (k * f) * f := by rw [hfk]
      _ = (k * k) * (f * f) := by group
  rw [e, hd.s56_F_sq hf, mul_one]
  exact hk k hk'

theorem nd11s_sq_mem_P1 (hd : d.Hyp) (hab : ∀ a ∈ P1 d, ∀ b ∈ P1 d, a * b = b * a)
    (hPe10 : Pe10 d ≤ K0 d z₀ ⊔ d.F) {y v : G} (hv : v ∈ K0 d z₀)
    (hgenv : P1 d = Pe10 d ⊔ Subgroup.closure ({v, y * v * y⁻¹} : Set G))
    {T T' : Subgroup G} (hk : ∀ k ∈ K0 d z₀, k * k ∈ T) (hT : T ≤ T')
    (hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T') : ∀ x ∈ P1 d, x * x ∈ T' := by
  have hcl : P1 d = Subgroup.closure ((Pe10 d : Set G) ∪ ({v, y * v * y⁻¹} : Set G)) := by
    rw [hgenv, Subgroup.closure_union, Subgroup.closure_eq]
  rw [hcl] at hab ⊢
  refine nd11s_sq_mem_closure hab ?_
  rintro s (hs | rfl | hs)
  · exact hT (nd11s_sq_K0F hd hk (hPe10 hs))
  · exact hT (hk s hv)
  · rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have e : y * v * y⁻¹ * (y * v * y⁻¹) = y * (v * v) * y⁻¹ := by group
    rw [e]
    exact hyT _ (hk v hv)

theorem P1_structure (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀)
    (hcard : Nat.card (P1 d) = 2 ^ 10)
    (hab : ∀ a ∈ P1 d, ∀ b ∈ P1 d, a * b = b * a)
    (hPe10 : Pe10 d ≤ K0 d z₀ ⊔ d.F)
    (hgen : ∀ y, IsY d y → ∃ v ∈ K0 d z₀,
      P1 d = Pe10 d ⊔ Subgroup.closure ({v, y * v * y⁻¹} : Set G)) :
    (IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10) ∨
      (d.ρ.range = ⊤ ∧
        Nonempty (↥(P1 d) ≃* (Multiplicative (Fin 6 → ZMod 2)) ×
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
        (frattini ↥(P1 d)).map (P1 d).subtype = d.s56U11) := by
  have _ := h08
  obtain ⟨y, hy⟩ := h07.1
  obtain ⟨hyN, hy3, hy1⟩ := hy.facts
  obtain ⟨v, hvK, hgenv⟩ := hgen y hy
  have hz0 : z₀ * z₀ = 1 := z0_sq hz h10
  have hzU : d.z ∈ d.s56U11 := s56_z_mem_U11 d
  obtain ⟨-, hCsq, hCD⟩ := C2_facts h49 hd hz h09 h10
  have hKsq : ∀ k ∈ K0 d z₀, k * k ∈ zpowers d.z := fun k hk =>
    hCsq k (mem_K0_iff.1 hk).1.1 (mem_K0_iff.1 hk).2
  have hP1sq : ∀ x ∈ P1 d, x * x ∈ d.s56U11 :=
    nd11s_sq_mem_P1 hd hab hPe10 hvK hgenv hKsq (zpowers_le.2 hzU)
      (fun t ht => hd.s56_N_conj_U11 h49 hyN (zpowers_le.2 hzU ht))
  by_cases hall : ∀ x ∈ P1 d, x * x = 1
  · exact Or.inl ⟨P2b.elemAb_of hab hall, hcard⟩
  right
  obtain ⟨x₀, hx₀⟩ := not_forall.1 hall
  obtain ⟨hx₀P, hx₀1⟩ := not_imp.1 hx₀
  have hρ : d.ρ.range = ⊤ := by
    rcases hd.centralizer_A with ⟨hr, -⟩ | ⟨hr, -⟩
    · exfalso
      have h1 : ∀ x ∈ P1 d, x * x ∈ (⊥ : Subgroup G) :=
        nd11s_sq_mem_P1 hd hab hPe10 hvK hgenv (T := ⊥) (T' := ⊥)
          (fun k hk => by
            rw [mem_bot]
            exact hCD hr k (mem_K0_iff.1 hk).1.1 (mem_K0_iff.1 hk).2)
          le_rfl (fun t ht => by rw [mem_bot.1 ht]; simp)
      exact hx₀1 (mem_bot.1 (h1 x₀ hx₀P))
    · exact hr
  have hsq_mul : ∀ a b : G, (∃ x ∈ P1 d, x * x = a) → (∃ x ∈ P1 d, x * x = b) →
      ∃ x ∈ P1 d, x * x = a * b := by
    rintro a b ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    refine ⟨x * x', mul_mem hx hx', ?_⟩
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hab x' hx' x hx]
      _ = x * x * (x' * x') := by group
  have hsq_conj : ∀ a : G, (∃ x ∈ P1 d, x * x = a) → ∃ x ∈ P1 d, x * x = y * a * y⁻¹ := by
    rintro a ⟨x, hx, rfl⟩
    refine ⟨y * x * y⁻¹, P1_inv h49 hd hz hz0 hy hyN hx, ?_⟩
    group
  obtain ⟨ha₁U, -, -, hya₁, hallU⟩ := hd.s56_y_orbit h49 hyN hy3 hy1
  have hzF : d.z ∈ d.F := s56_U11_le_F d hzU
  have ha₁F : y * d.z * y⁻¹ ∈ d.F := s56_U11_le_F d ha₁U
  have hcomm₁ : (y * d.z * y⁻¹) * d.z = d.z * (y * d.z * y⁻¹) := hd.s56_F_comm ha₁F hzF
  have hsq₁ : (y * d.z * y⁻¹) * (y * d.z * y⁻¹) = 1 := hd.s56_F_sq ha₁F
  have hz_sq : ∃ x ∈ P1 d, x * x = d.z := by
    have hs₀ : ∃ x ∈ P1 d, x * x = x₀ * x₀ := ⟨x₀, hx₀P, rfl⟩
    rcases hallU (x₀ * x₀) (hP1sq x₀ hx₀P) with h | h | h | h
    · exact absurd h hx₀1
    · rwa [h] at hs₀
    · rw [h] at hs₀
      have h1 := hsq_conj _ hs₀
      rw [hya₁] at h1
      have h2 := hsq_mul _ _ h1 hs₀
      have e : d.z * (y * d.z * y⁻¹) * (y * d.z * y⁻¹) = d.z := by
        calc d.z * (y * d.z * y⁻¹) * (y * d.z * y⁻¹)
            = d.z * ((y * d.z * y⁻¹) * (y * d.z * y⁻¹)) := by group
          _ = d.z := by rw [hsq₁, mul_one]
      rwa [e] at h2
    · rw [h] at hs₀
      have h1 := hsq_conj _ hs₀
      have e : y * (d.z * (y * d.z * y⁻¹)) * y⁻¹ = d.z := by
        calc y * (d.z * (y * d.z * y⁻¹)) * y⁻¹
            = (y * d.z * y⁻¹) * (y * (y * d.z * y⁻¹) * y⁻¹) := by group
          _ = (y * d.z * y⁻¹) * (d.z * (y * d.z * y⁻¹)) := by rw [hya₁]
          _ = ((y * d.z * y⁻¹) * d.z) * (y * d.z * y⁻¹) := by group
          _ = (d.z * (y * d.z * y⁻¹)) * (y * d.z * y⁻¹) := by rw [hcomm₁]
          _ = d.z * ((y * d.z * y⁻¹) * (y * d.z * y⁻¹)) := by group
          _ = d.z := by rw [hsq₁, mul_one]
      rwa [e] at h1
  have hU_sq : ∀ a ∈ d.s56U11, ∃ x ∈ P1 d, x * x = a := by
    have h1 : ∃ x ∈ P1 d, x * x = y * d.z * y⁻¹ := hsq_conj _ hz_sq
    intro a ha
    rcases hallU a ha with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, by simp⟩
    · exact hz_sq
    · exact h1
    · exact hsq_mul _ _ hz_sq h1
  have hU11le : d.s56U11 ≤ P1 d := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := hU_sq a ha
    exact mul_mem hx hx
  haveI : IsMulCommutative ↥(P1 d) := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  let S : Subgroup ↥(P1 d) := d.s56U11.subgroupOf (P1 d)
  have hS4 : Nat.card S = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU11le).toEquiv]
    exact s56_card_U11 d
  have hsqΓ : ∀ x : ↥(P1 d), x * x ∈ S := fun x => hP1sq x x.2
  have hsqΓ' : ∀ s ∈ S, ∃ x : ↥(P1 d), x * x = s := by
    intro s hs
    obtain ⟨x, hx, hxs⟩ := hU_sq (s : G) (Subgroup.mem_subgroupOf.1 hs)
    exact ⟨⟨x, hx⟩, Subtype.ext hxs⟩
  have hexΓ : ∀ x : ↥(P1 d), x ^ 4 = 1 := by
    intro x
    refine Subtype.ext ?_
    have h1 : ((x : G) * x) * ((x : G) * x) = 1 :=
      hd.s56_F_sq (s56_U11_le_F d (hP1sq x x.2))
    calc ((x ^ 4 : ↥(P1 d)) : G) = ((x : G) * x) * ((x : G) * x) := by simp [pow_succ, mul_assoc]
      _ = 1 := h1
  have hPgp : IsPGroup 2 ↥(P1 d) := IsPGroup.of_card hcard
  refine ⟨hρ, abelian_shape hcard S hS4 hsqΓ hsqΓ' hexΓ, ?_⟩
  rw [frattini_eq_squares hPgp S hsqΓ hsqΓ']
  exact Subgroup.map_subgroupOf_eq_of_le hU11le

end Structure

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
