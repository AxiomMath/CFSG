module

public import CFSG.LargeExtraspecial.A2ModPL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions OrthoF2

theorem A2Action.eq_add_or_eq_add_add {X : Type} [Group X] {D : Set X} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)} (hA : A2Action D Q ρ) {d e : X}
    (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) {p x y z : V}
    (hx : commSpace (ρ d) = Submodule.span (ZMod 2) {p, x})
    (hy : commSpace (ρ e) = Submodule.span (ZMod 2) {p, y}) (hz : z ∈ commSpace (ρ (d * e)))
    (hz0 : z ≠ 0) (hzp : z ≠ p) : z = x + y ∨ z = p + (x + y) := by
  rw [(hA.commSpace_mul_eq_span_add hd he hde hx hy).1] at hz
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
  · simp at hz0
  · left
    simp
  · simp at hzp
  · right
    simp

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

@[expose] def IsPointCentreMap (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V))
    (c : (Fin n → ZMod 2) → V) : Prop :=
  c 0 = 0 ∧ ∀ v, v ≠ 0 → IsPointCentre ρ v (c v)

@[expose] def IsHyperplaneCentreMap
    (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)) (d : (Fin n → ZMod 2) → V) :
    Prop :=
  d 0 = 0 ∧ ∀ φ, φ ≠ 0 → IsHyperplaneCentre ρ φ (d φ)

theorem exists_isPointCentreMap
    (h : ∀ v : Fin n → ZMod 2, v ≠ 0 → ∃ p : V, IsPointCentre ρ v p) :
    ∃ c, IsPointCentreMap ρ c := by
  classical
  refine ⟨fun v => if hv : v = 0 then 0 else (h v hv).choose, by simp, fun v hv => ?_⟩
  simp only [hv, ↓reduceDIte]
  exact (h v hv).choose_spec

theorem exists_isHyperplaneCentreMap
    (h : ∀ φ : Fin n → ZMod 2, φ ≠ 0 → ∃ p : V, IsHyperplaneCentre ρ φ p) :
    ∃ d, IsHyperplaneCentreMap ρ d := by
  classical
  refine ⟨fun φ => if hφ : φ = 0 then 0 else (h φ hφ).choose, by simp, fun φ hφ => ?_⟩
  simp only [hφ, ↓reduceDIte]
  exact (h φ hφ).choose_spec

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {c d : (Fin n → ZMod 2) → V}

theorem false_of_forall_mem_commSpace_tv (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 2 ≤ n) {p : V} (hp : p ≠ 0)
    (h : ∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 → p ∈ commSpace (ρ (tv v φ))) :
    False := by
  refine hA.false_of_common_point closure_transvectionSet (not_isPGroup_two hn) hp fun t ht => ?_
  obtain ⟨v, φ, hv, hφ, hvφ, rfl⟩ := mem_transvectionSet.mp ht
  exact h v φ hv hφ hvφ

namespace IsPointCentreMap

theorem map_mulVec (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hc : IsPointCentreMap ρ c) (g : SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    c ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) = ρ g (c v) := by
  by_cases hv : v = 0
  · rw [hv, mulVec_zero, hc.1, map_zero]
  have hgv : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ≠ 0 :=
    fun h => hv ((sl_mulVec_eq_zero_iff g).mp h)
  exact IsPointCentre.unique hA hn hgv (hc.2 _ hgv) ((hc.2 v hv).apply g)

theorem false_of_const (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 2 ≤ n)
    (hc : IsPointCentreMap ρ c) {v₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    (hconst : ∀ v, v ≠ 0 → c v = c v₀) : False := by
  refine false_of_forall_mem_commSpace_tv hA hn (hc.2 v₀ hv₀).1 fun v φ hv hφ hvφ => ?_
  rw [← hconst v hv]
  exact (hc.2 v hv).2 φ hφ hvφ

end IsPointCentreMap

namespace IsHyperplaneCentreMap

theorem map_contra (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hd : IsHyperplaneCentreMap ρ d) (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (φ : Fin n → ZMod 2) : d (contra g φ) = ρ g (d φ) := by
  by_cases hφ : φ = 0
  · rw [hφ, contra_zero, hd.1, map_zero]
  have hgφ : contra g φ ≠ 0 := fun h => hφ ((contra_eq_zero_iff g).mp h)
  exact IsHyperplaneCentre.unique hA hn hgφ (hd.2 _ hgφ) ((hd.2 φ hφ).apply g)

theorem false_of_const (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 2 ≤ n)
    (hd : IsHyperplaneCentreMap ρ d) {φ₀ : Fin n → ZMod 2} (hφ₀ : φ₀ ≠ 0)
    (hconst : ∀ φ, φ ≠ 0 → d φ = d φ₀) : False := by
  refine false_of_forall_mem_commSpace_tv hA hn (hd.2 φ₀ hφ₀).1 fun v φ hv hφ hvφ => ?_
  rw [← hconst φ hφ]
  exact (hd.2 φ hφ).2 v hv hvφ

theorem injective (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hd : IsHyperplaneCentreMap ρ d) : Function.Injective d := by
  intro φ ψ hφψ
  by_contra hne
  have hφ : φ ≠ 0 := by
    rintro rfl
    rw [hd.1] at hφψ
    exact (hd.2 ψ (Ne.symm hne)).1 hφψ.symm
  have hψ : ψ ≠ 0 := by
    rintro rfl
    rw [hd.1] at hφψ
    exact (hd.2 φ hne).1 hφψ
  refine hd.false_of_const hA (by omega) hφ fun χ hχ => ?_
  by_cases hχφ : χ = φ
  · rw [hχφ]
  obtain ⟨g, hgφ, hgψ⟩ := exists_contra_eq_of_contra_eq hψ (Ne.symm hne) hχ hχφ
  rw [← hgψ, hd.map_contra hA hn, ← hφψ, ← hd.map_contra hA hn, hgφ]

end IsHyperplaneCentreMap

namespace IsPointCentreMap

theorem injective (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hc : IsPointCentreMap ρ c) : Function.Injective c := by
  intro v w hvw
  by_contra hne
  have hv : v ≠ 0 := by
    rintro rfl
    rw [hc.1] at hvw
    exact (hc.2 w (Ne.symm hne)).1 hvw.symm
  have hw : w ≠ 0 := by
    rintro rfl
    rw [hc.1] at hvw
    exact (hc.2 v hne).1 hvw
  refine hc.false_of_const hA (by omega) hv fun u hu => ?_
  by_cases huv : u = v
  · rw [huv]
  obtain ⟨g, hgv, hgw⟩ := exists_mulVec_eq_of_mulVec_eq hw (Ne.symm hne) hu huv
  rw [← hgw, hc.map_mulVec hA hn, ← hvw, ← hc.map_mulVec hA hn, hgv]

theorem ne (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) {v φ : Fin n → ZMod 2}
    (hv : v ≠ 0) (hφ : φ ≠ 0) (hvφ : φ ⬝ᵥ v = 0) : c v ≠ d φ := by
  intro heq
  have hall : ∀ w ψ : Fin n → ZMod 2, w ≠ 0 → ψ ≠ 0 → ψ ⬝ᵥ w = 0 → c w = d ψ := by
    intro w ψ hw hψ hwψ
    obtain ⟨g, hgv, hgφ⟩ := exists_mulVec_eq_contra_eq hv hφ hvφ hw hψ hwψ
    rw [← hgv, ← hgφ, hc.map_mulVec hA hn, hd.map_contra hA hn, heq]
  refine hc.false_of_const hA (by omega) hv fun w hw => ?_
  obtain ⟨ψ, hψ, hψv, hψw⟩ := exists_ne_zero_dotProduct_eq_zero_two hn v w
  rw [hall w ψ hw hψ hψw, hall v ψ hv hψ hψv]

end IsPointCentreMap

theorem commSpace_tv_eq_span (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) {v φ : Fin n → ZMod 2}
    (hv : v ≠ 0) (hφ : φ ≠ 0) (hvφ : φ ⬝ᵥ v = 0) :
    commSpace (ρ (tv v φ)) = Submodule.span (ZMod 2) {c v, d φ} := by
  have hli : LinearIndependent (ZMod 2) ![c v, d φ] :=
    linearIndependent_pair_iff.mpr ⟨(hc.2 v hv).1, (hd.2 φ hφ).1, hc.ne hA hn hd hv hφ hvφ⟩
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact (hc.2 v hv).2 φ hφ hvφ
    · exact (hd.2 φ hφ).2 v hv hvφ
  · rw [finrank_span_pair hli, (hA.isTypeA (tv_mem_transvectionSet hv hφ hvφ)).2.2.2.1]

theorem vec_add_ne_zero_of_ne {v w : Fin n → ZMod 2} (h : v ≠ w) : v + w ≠ 0 := fun h0 =>
  h (by rwa [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h0)

namespace IsPointCentreMap

theorem map_add_of_ne (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 4 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) {v w : Fin n → ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) : c (v + w) = c v + c w := by
  have hn3 : 3 ≤ n := by omega
  have hvw0 := vec_add_ne_zero_of_ne hvw
  have key : ∀ χ : Fin n → ZMod 2, χ ≠ 0 → χ ⬝ᵥ v = 0 → χ ⬝ᵥ w = 0 →
      c (v + w) = c v + c w ∨ c (v + w) = d χ + (c v + c w) := by
    intro χ hχ hχv hχw
    have hχvw : χ ⬝ᵥ (v + w) = 0 := by rw [dotProduct_add, hχv, hχw, add_zero]
    have hne : tv v χ ≠ tv w χ := fun h => hvw ((tv_eq_tv_iff hv hχ hχv hχw).mp h).1
    have hx : commSpace (ρ (tv v χ)) = Submodule.span (ZMod 2) {d χ, c v} := by
      rw [commSpace_tv_eq_span hA hn3 hc hd hv hχ hχv, Set.pair_comm]
    have hy : commSpace (ρ (tv w χ)) = Submodule.span (ZMod 2) {d χ, c w} := by
      rw [commSpace_tv_eq_span hA hn3 hc hd hw hχ hχw, Set.pair_comm]
    have hz : c (v + w) ∈ commSpace (ρ (tv v χ * tv w χ)) := by
      rw [tv_mul_tv_right hχv hχw]
      exact (hc.2 _ hvw0).2 χ hχ hχvw
    exact hA.eq_add_or_eq_add_add (tv_mem_transvectionSet hv hχ hχv)
      (tv_mem_transvectionSet hw hχ hχw) hne hx hy hz (hc.2 _ hvw0).1
      (hc.ne hA hn3 hd hvw0 hχ hχvw)
  obtain ⟨χ, χ', hχ, hχ', hχχ', hχv, hχw, hχ'v, hχ'w⟩ :=
    exists_two_ne_zero_dotProduct_eq_zero hn v w
  rcases key χ hχ hχv hχw with h | h
  · exact h
  rcases key χ' hχ' hχ'v hχ'w with h' | h'
  · exact h'
  exfalso
  refine hχχ' (hd.injective hA hn3 ?_)
  rw [h] at h'
  exact add_right_cancel h'

theorem map_add (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 4 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) (v w : Fin n → ZMod 2) :
    c (v + w) = c v + c w := by
  by_cases hv : v = 0
  · rw [hv, zero_add, hc.1, zero_add]
  by_cases hw : w = 0
  · rw [hw, add_zero, hc.1, add_zero]
  by_cases hvw : v = w
  · rw [hvw, ZModModule.add_self, ZModModule.add_self, hc.1]
  exact hc.map_add_of_ne hA hn hd hv hw hvw

end IsPointCentreMap

namespace IsHyperplaneCentreMap

theorem map_add_of_ne (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 4 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) {φ ψ : Fin n → ZMod 2}
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (hφψ : φ ≠ ψ) : d (φ + ψ) = d φ + d ψ := by
  have hn3 : 3 ≤ n := by omega
  have hφψ0 := vec_add_ne_zero_of_ne hφψ
  have key : ∀ x : Fin n → ZMod 2, x ≠ 0 → φ ⬝ᵥ x = 0 → ψ ⬝ᵥ x = 0 →
      d (φ + ψ) = d φ + d ψ ∨ d (φ + ψ) = c x + (d φ + d ψ) := by
    intro x hx hφx hψx
    have hφψx : (φ + ψ) ⬝ᵥ x = 0 := by rw [add_dotProduct, hφx, hψx, add_zero]
    have hne : tv x φ ≠ tv x ψ := fun h => hφψ ((tv_eq_tv_iff hx hφ hφx hψx).mp h).2
    have hX := commSpace_tv_eq_span hA hn3 hc hd hx hφ hφx
    have hY := commSpace_tv_eq_span hA hn3 hc hd hx hψ hψx
    have hz : d (φ + ψ) ∈ commSpace (ρ (tv x φ * tv x ψ)) := by
      rw [tv_mul_tv_left hφx hψx]
      exact (hd.2 _ hφψ0).2 x hx hφψx
    exact hA.eq_add_or_eq_add_add (tv_mem_transvectionSet hx hφ hφx)
      (tv_mem_transvectionSet hx hψ hψx) hne hX hY hz (hd.2 _ hφψ0).1
      (Ne.symm (hc.ne hA hn3 hd hx hφψ0 hφψx))
  obtain ⟨x, x', hx, hx', hxx', hxφ, hxψ, hx'φ, hx'ψ⟩ :=
    exists_two_ne_zero_dotProduct_eq_zero hn φ ψ
  rw [dotProduct_comm] at hxφ hxψ hx'φ hx'ψ
  rcases key x hx hxφ hxψ with h | h
  · exact h
  rcases key x' hx' hx'φ hx'ψ with h' | h'
  · exact h'
  exfalso
  refine hxx' (hc.injective hA hn3 ?_)
  rw [h] at h'
  exact add_right_cancel h'

theorem map_add (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 4 ≤ n)
    (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) (φ ψ : Fin n → ZMod 2) :
    d (φ + ψ) = d φ + d ψ := by
  by_cases hφ : φ = 0
  · rw [hφ, zero_add, hd.1, zero_add]
  by_cases hψ : ψ = 0
  · rw [hψ, add_zero, hd.1, add_zero]
  by_cases hφψ : φ = ψ
  · rw [hφψ, ZModModule.add_self, ZModModule.add_self, hd.1]
  exact hd.map_add_of_ne hA hn hc hφ hψ hφψ

end IsHyperplaneCentreMap

end CFSG.LargeExtraspecial.A2Mod
