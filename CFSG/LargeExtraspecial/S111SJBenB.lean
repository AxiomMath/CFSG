module

public import CFSG.LargeExtraspecial.S111SJBenA
public import CFSG.LargeExtraspecial.S111SJMin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_le_two_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (H : Subgroup G)
    (hH : ∀ h ∈ H, h * h = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hcard : Nat.card H = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]; exact Subtype.ext (hH g g.2))
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem conj_injective_of_center {Q : Type*} [Group Q] (hQ : center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ center Q := mem_center_iff.mpr fun y => by
    have := congrArg (fun σ : MulAut Q => σ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = (g * y * g⁻¹) * g := by rw [this]
      _ = g * y := by group
  rw [hQ, mem_bot] at this
  exact this

theorem mul_conj_mul_inv {Q : Type*} [Group Q] (σ : MulAut Q) (g : Q) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem card_le_two_mul_inf_inner {Q : Type*} [Group Q] [IsCyclic (Outer Q)]
    (Λ : Subgroup (MulAut Q)) (hΛ : ∀ l ∈ Λ, l * l = 1) :
    Nat.card Λ ≤ 2 * Nat.card (Λ ⊓ inner Q : Subgroup (MulAut Q)) := by
  set π : MulAut Q →* Outer Q := QuotientGroup.mk' (inner Q) with hπ
  set ψ := π.comp Λ.subtype with hψ
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Λ := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card ψ.range ≤ 2 := card_le_two_of_isCyclic _ (by
    rintro _ ⟨l, rfl⟩
    rw [← map_mul]
    have : l * l = 1 := Subtype.ext (hΛ l l.2)
    rw [this, map_one])
  have h3 : Nat.card ψ.ker = Nat.card (Λ ⊓ inner Q : Subgroup (MulAut Q)) := by
    refine Nat.card_congr ⟨fun x => ⟨x.1, x.1.2, ?_⟩, fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩, ?_, ?_⟩
    · have h := x.2
      change π ((x : Λ) : MulAut Q) = 1 at h
      exact (QuotientGroup.eq_one_iff _).mp h
    · change π (x : MulAut Q) = 1
      exact (QuotientGroup.eq_one_iff _).mpr x.2.2
    · intro x
      rfl
    · intro x
      rfl
  rw [← h1, h3]
  nlinarith [Nat.zero_le (Nat.card (Λ ⊓ inner Q : Subgroup (MulAut Q)))]

namespace LayerCfg

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem center_eq_bot (C : LayerCfg E O L w ρ a) : center (E ⧸ center E) = ⊥ := by
  have := C.perfect
  exact Group.IsPerfect.center_quotient_center_eq_bot E

theorem exists_mul_of_barAct_eq_conj [E.Normal] (C : LayerCfg E O L w ρ a) {x : X}
    {q : E ⧸ center E} (hx : barAct E x = MulAut.conj q) :
    ∃ e : E, (QuotientGroup.mk e : E ⧸ center E) = q ∧
      ∀ e' ∈ E, (e : X)⁻¹ * x * e' = e' * ((e : X)⁻¹ * x) := by
  have := C.perfect
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨e, rfl, fun e' he' => ?_⟩
  have h1 : barAct E ((e : X)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, barAct_of_mem, hx, inv_mul_cancel]
  exact commute_of_barAct_eq_one h1 e' he'

theorem commute_of_mem_O [Finite X] [E.Normal] [hO : O.Normal] (C : LayerCfg E O L w ρ a)
    {o : X} (ho : o ∈ O) {e : X} (he : e ∈ E) : e * o = o * e := by
  have := C.perfect
  have hN : ((E ⊓ O).subgroupOf E).Normal := Subgroup.normal_subgroupOf
  have hcen : (E ⊓ O).subgroupOf E ≤ center E := by
    rcases Quasisimple.normal_le_center_or_eq_top C.quasi ((E ⊓ O).subgroupOf E) with h | h
    · exact h
    · exfalso
      have hle : E ≤ O := fun x hx => by
        have : (⟨x, hx⟩ : E) ∈ (E ⊓ O).subgroupOf E := by rw [h]; trivial
        exact (mem_subgroupOf.mp this).2
      have h2 := CFSG.LargeExtraspecial.S5.two_dvd_card_of_isQuasisimple C.quasi
      have h3 : Nat.card E ∣ 3 := (Subgroup.card_dvd_of_le hle).trans C.card_O
      exact absurd (h2.trans h3) (by norm_num)
  have h1 : barAct E o = 1 := by
    ext y
    obtain ⟨e', rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAct_mk, MulAut.one_apply, QuotientGroup.eq]
    apply hcen
    rw [mem_subgroupOf]
    simp only [coe_mul, coe_inv, MulAut.conjNormal_apply]
    refine ⟨E.mul_mem (E.inv_mem (‹E.Normal›.conj_mem _ e'.2 o)) e'.2, ?_⟩
    have h2 : (o * (e' : X) * o⁻¹)⁻¹ * e' = o * ((e' : X)⁻¹ * o⁻¹ * (e' : X)⁻¹⁻¹) := by group
    rw [h2]
    exact O.mul_mem ho (hO.conj_mem _ (O.inv_mem ho) _)
  exact (commute_of_barAct_eq_one h1 e he).symm

theorem eq_four_of_field [Finite X] [FiniteDimensional (ZMod 2) V]
    [E.Normal] (C : LayerCfg E O L w ρ a) {f : ℕ}
    (hB : BenderType (E ⧸ center E) f 1 1) {l : MulAut (E ⧸ center E)}
    (hl : l ∈ L.map (barAct E)) (hout : ¬ ∃ g, ∀ x, l x = g * x * g⁻¹) : w = 4 ∧ f = 4 := by
  have hperf := C.perfect
  obtain ⟨m, hfm, ⟨eφ⟩, -⟩ := hB.fixed_linear l (C.lam_sq hl) hout
  have hconj := conj_injective_of_center C.center_eq_bot
  set Λ := L.map (barAct E) with hΛdef
  set A₀ : Subgroup (E ⧸ center E) := Λ.comap MulAut.conj with hA₀
  have hA₀fix : A₀ ≤ autFixed l := by
    intro q hq
    have h1 := C.lam_comm hl hq
    have h2 : MulAut.conj (l q) = MulAut.conj q := by
      rw [← mul_conj_mul_inv, h1, mul_inv_cancel_right]
    exact hconj h2
  have hA₀sq : ∀ q ∈ A₀, q * q = 1 := fun q hq => hconj (by
    rw [map_mul, map_one]; exact C.lam_sq hq)
  have hm1 : 1 ≤ m := by
    have := hB.two_le
    omega
  have hA₀card : Nat.card A₀ ≤ 2 ^ m := by
    set B : Subgroup (CFSG.Theory.Comparator.PSL2Model m) :=
      (A₀.subgroupOf (autFixed l)).map eφ.toMonoidHom with hB'
    have hBsq : ∀ x ∈ B, x * x = 1 := by
      rintro _ ⟨q, hq, rfl⟩
      rw [← map_mul]
      have : q * q = 1 := Subtype.ext (hA₀sq q (mem_subgroupOf.mp hq))
      rw [this, map_one]
    have h1 := card_le_of_sq_eq_one_psl2 hm1 B hBsq
    rw [hB', Subgroup.card_map_of_injective eφ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hA₀fix).toEquiv] at h1
    exact h1
  have hcyc : IsCyclic (Outer (E ⧸ center E)) := hB.outer_linear.1
  have hΛ2 := card_le_two_mul_inf_inner Λ fun l hl => C.lam_sq hl
  have hinf : Nat.card (Λ ⊓ inner (E ⧸ center E) : Subgroup _) = Nat.card A₀ := by
    have : (Λ ⊓ inner (E ⧸ center E) : Subgroup _) = A₀.map MulAut.conj := by
      ext σ
      constructor
      · rintro ⟨hσ, q, rfl⟩
        exact ⟨q, hσ, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨hq, q, rfl⟩
    rw [this, Subgroup.card_map_of_injective hconj]
  rw [hinf, C.card_lam] at hΛ2
  have hD' := two_mul_le_finrank_of_benderType (ρ.comp E.subtype)
    (C.rho_inj.comp Subtype.val_injective) hB (by omega)
  rw [C.finrank_eq] at hD'
  have h6 := C.four_le
  have h3 : 2 ^ (w - 1) ≤ 2 ^ (m + 1) := by
    calc 2 ^ (w - 1) ≤ 2 * 2 ^ m := hΛ2.trans (Nat.mul_le_mul_left 2 hA₀card)
      _ = 2 ^ (m + 1) := by ring
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

theorem false_of_field [Finite X] [FiniteDimensional (ZMod 2) V]
    [E.Normal] (C : LayerCfg E O L w ρ a) (h6 : 6 ≤ w) {f : ℕ}
    (hB : BenderType (E ⧸ center E) f 1 1) {l : MulAut (E ⧸ center E)}
    (hl : l ∈ L.map (barAct E)) (hout : ¬ ∃ g, ∀ x, l x = g * x * g⁻¹) : False := by
  have := C.eq_four_of_field hB hl hout
  omega

end LayerCfg

end CFSG.LargeExtraspecial.S11
