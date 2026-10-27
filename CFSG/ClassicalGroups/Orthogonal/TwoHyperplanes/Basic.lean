module

public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem PolarNondegOn.inf_ker (h2 : (2 : K) ≠ 0) {S : Submodule K V} (hS : PolarNondegOn Q S)
    {u : V} (hu : u ∈ S) (hQu : Q u ≠ 0) :
    PolarNondegOn Q (S ⊓ LinearMap.ker (polarBilin Q u)) := by
  intro x hx hxW
  rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
  apply hS x hx.1
  intro y hy
  have huu : polar Q u u ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQu
  set c : K := polar Q u y / polar Q u u with hc
  have hy' : y - c • u ∈ S ⊓ LinearMap.ker (polarBilin Q u) := by
    refine ⟨S.sub_mem hy (S.smul_mem c hu), ?_⟩
    have hmem : y - c • u ∈ LinearMap.ker (polarBilin Q u) := by
      rw [LinearMap.mem_ker, polarBilin_apply_apply, polar_sub_right, polar_smul_right_eq, hc,
        div_mul_cancel₀ _ huu, sub_self]
    exact hmem
  have hxker : polar Q u x = 0 := by
    rw [← polarBilin_apply_apply]
    exact hx.2
  have hxpos : polar Q x u = 0 := by rw [polar_comm]; exact hxker
  have hx' := hxW (y - c • u) hy'
  calc
    polar Q x y = polar Q x (c • u + (y - c • u)) := by
      rw [show c • u + (y - c • u) = y by abel]
    _ = polar Q x (c • u) + polar Q x (y - c • u) := by rw [polar_add_right]
    _ = c * polar Q x u + polar Q x (y - c • u) := by rw [polar_smul_right_eq]
    _ = 0 := by rw [hxpos, hx', mul_zero, add_zero]

theorem finrank_inf_ker_polarBilin_add_one [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} {u : V} (hu : u ∈ S) (hQu : Q u ≠ 0) :
    Module.finrank K ↥(S ⊓ LinearMap.ker (polarBilin Q u)) + 1 = Module.finrank K S := by
  set f : V →ₗ[K] K := polarBilin Q u with hf
  have hfu : f u ≠ 0 := by
    rw [hf, polarBilin_apply_apply, polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQu
  have hsup : S ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxmem : x - (f x / f u) • u ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu, sub_self]
    have hxeq : x = (f x / f u) • u + (x - (f x / f u) • u) := by abel
    rw [hxeq]
    exact Submodule.add_mem_sup (S.smul_mem _ hu) hxmem
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨(c / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu]
  have hker : Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, Module.finrank_self] at h
    omega
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker f)
  rw [hsup, finrank_top] at hmod
  omega

private def perpFinset_th2a (Q : QuadraticForm K V) (s : Finset V) : Submodule K V :=
  s.inf fun u => LinearMap.ker (polarBilin Q u)

private theorem mem_perpFinset_th2a {s : Finset V} {x : V} :
    x ∈ perpFinset_th2a Q s ↔ ∀ u ∈ s, polar Q u x = 0 := by
  classical
  simp [perpFinset_th2a, Submodule.mem_finsetInf, LinearMap.mem_ker, polarBilin_apply_apply]

private theorem polarNondegOn_perpFinset_th2a [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {s : Finset V} (hs : ∀ u ∈ s, Q u ≠ 0)
    (hs' : (s : Set V).Pairwise fun u w => polar Q u w = 0) :
    PolarNondegOn Q (perpFinset_th2a Q s) ∧
      Module.finrank K (perpFinset_th2a Q s) + s.card = Module.finrank K V := by
  classical
  have main : ∀ t : Finset V, (∀ u ∈ t, Q u ≠ 0) →
      ((t : Set V).Pairwise fun u w => polar Q u w = 0) →
      PolarNondegOn Q (perpFinset_th2a Q t) ∧
        Module.finrank K (perpFinset_th2a Q t) + t.card = Module.finrank K V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _ _
        constructor
        · rw [show perpFinset_th2a Q (∅ : Finset V) = ⊤ by simp [perpFinset_th2a]]
          exact polarNondegOn_top hQ
        · have htop : perpFinset_th2a Q (∅ : Finset V) = ⊤ := by simp [perpFinset_th2a]
          rw [htop, finrank_top]
          simp
    | insert a s ha ih =>
        intro hs hs'
        have hs_s : ∀ u ∈ s, Q u ≠ 0 := fun u hu => hs u (Finset.mem_insert_of_mem hu)
        have hs'_s : (s : Set V).Pairwise fun u w => polar Q u w = 0 := by
          intro u hu w hw huv
          exact hs' (Finset.mem_insert_of_mem hu) (Finset.mem_insert_of_mem hw) huv
        obtain ⟨hnd, hfr⟩ := ih hs_s hs'_s
        have hQa : Q a ≠ 0 := hs a (Finset.mem_insert_self a s)
        have ha_mem : a ∈ perpFinset_th2a Q s := by
          rw [mem_perpFinset_th2a]
          intro u hu
          have hua : u ≠ a := fun h => ha (h ▸ hu)
          have h : polar Q a u = 0 := hs' (Finset.mem_insert_self a s)
            (Finset.mem_insert_of_mem hu) (fun h' => hua h'.symm)
          rwa [polar_comm] at h
        have hinf : perpFinset_th2a Q (insert a s) =
            perpFinset_th2a Q s ⊓ LinearMap.ker (polarBilin Q a) := by
          rw [perpFinset_th2a, Finset.inf_insert, inf_comm, perpFinset_th2a]
        constructor
        · rw [hinf]
          exact hnd.inf_ker h2 ha_mem hQa
        · rw [hinf, Finset.card_insert_of_notMem ha]
          have hstep := finrank_inf_ker_polarBilin_add_one h2 ha_mem hQa
          omega
  exact main s hs hs'

theorem exists_forall_polar_eq_zero_ne_zero [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {s : Finset V} (hs : ∀ u ∈ s, Q u ≠ 0)
    (hs' : (s : Set V).Pairwise fun u w => polar Q u w = 0)
    (hdim : s.card + 1 ≤ Module.finrank K V) :
    ∃ x, (∀ u ∈ s, polar Q u x = 0) ∧ Q x ≠ 0 := by
  obtain ⟨hnd, hfr⟩ := polarNondegOn_perpFinset_th2a h2 hQ hs hs'
  have hpos : 0 < Module.finrank K (perpFinset_th2a Q s) := by omega
  have hne : perpFinset_th2a Q s ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨x, hx, hQx⟩ := hnd.exists_map_ne_zero hne
  exact ⟨x, mem_perpFinset_th2a.mp hx, hQx⟩

theorem exists_forall_polar_eq_zero_map_eq [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {s : Finset V}
    (hs : ∀ u ∈ s, Q u ≠ 0) (hs' : (s : Set V).Pairwise fun u w => polar Q u w = 0)
    (hdim : s.card + 2 ≤ Module.finrank K V) (c : K) :
    ∃ x, (∀ u ∈ s, polar Q u x = 0) ∧ Q x = c := by
  obtain ⟨hnd, hfr⟩ := polarNondegOn_perpFinset_th2a h2 hQ hs hs'
  have hdim' : 2 ≤ Module.finrank K (perpFinset_th2a Q s) := by omega
  obtain ⟨x, hx, hxQ⟩ := hnd.exists_map_eq h2 hdim' c
  exact ⟨x, mem_perpFinset_th2a.mp hx, hxQ⟩

theorem exists_polar_eq_zero_polar_eq_zero_map_eq [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0) (hef : polar Q e f = 0) (c : K) :
    ∃ x, polar Q e x = 0 ∧ polar Q f x = 0 ∧ Q x = c := by
  classical
  have hs : ∀ u ∈ ({e, f} : Finset V), Q u ≠ 0 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact he
    · exact hf
  have hs' : ((({e, f} : Finset V) : Set V)).Pairwise fun u w => polar Q u w = 0 := by
    intro u hu w hw huw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · exact hef
    · rwa [polar_comm]
    · exact absurd rfl huw
  have hcard : ({e, f} : Finset V).card + 2 ≤ Module.finrank K V :=
    (Nat.add_le_add_right Finset.card_le_two 2).trans hdim
  obtain ⟨x, hx, hQx⟩ := exists_forall_polar_eq_zero_map_eq h2 hQ hs hs' hcard c
  exact ⟨x, hx e (by simp), hx f (by simp), hQx⟩

private theorem exists_reflect_mul_reflect_apply_eq_of_map_sub_ne_zero_th2a [Finite K]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) {e w w' : V} (he : Q e ≠ 0)
    (hw : polar Q e w = 0) (hw' : polar Q e w' = 0) (hQw : Q w = Q w')
    (hw0 : Q w ≠ 0) (hb0 : Q (w - w') ≠ 0) :
    ∃ a b, polar Q e a = 0 ∧ polar Q e b = 0 ∧ Q a = Q b ∧
      (reflect Q a * reflect Q b) w = w' := by
  classical
  set b : V := w - w' with hb
  have hQb : Q b ≠ 0 := by rw [hb]; exact hb0
  have hQw' : Q w' ≠ 0 := by rw [← hQw]; exact hw0
  have hsub : Q (w - w') = Q w + Q w' - polar Q w w' := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
    ring
  have hbb : polar Q b w = Q b := by
    rw [hb, polar_sub_left, polar_self_eq_two_mul, polar_comm Q w' w, hsub, ← hQw]
    ring
  have hrb : reflect Q b w = w' := by
    rw [reflect_apply hQb, hbb, div_self hQb, one_smul, hb]
    abel
  obtain ⟨a, hae, haw', haQ⟩ :=
    exists_polar_eq_zero_polar_eq_zero_map_eq h2 hQ hdim he hQw' hw' (Q b)
  have haw : polar Q a w' = 0 := by rwa [polar_comm] at haw'
  have hra : reflect Q a w' = w' := reflect_apply_of_polar_eq_zero haw
  have heb : polar Q e b = 0 := by
    rw [hb, polar_sub_right, hw, hw', sub_self]
  exact ⟨a, b, hae, heb, haQ, by rw [LinearEquiv.mul_apply, hrb, hra]⟩

private theorem exists_reflect_mul_reflect_apply_eq_of_map_sub_eq_zero_th2a
    (h2 : (2 : K) ≠ 0) {e w w' : V}
    (hw : polar Q e w = 0) (hw' : polar Q e w' = 0) (hQw : Q w = Q w')
    (hw0 : Q w ≠ 0) (hb0 : Q (w - w') = 0) :
    ∃ a b, polar Q e a = 0 ∧ polar Q e b = 0 ∧ Q a = Q b ∧
      (reflect Q a * reflect Q b) w = w' := by
  classical
  have hQw' : Q w' ≠ 0 := by rw [← hQw]; exact hw0
  have hpol : polar Q w w' = 2 * Q w := by
    have h : Q (w - w') = Q w + Q w' - polar Q w w' := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
      ring
    rw [hb0, ← hQw] at h
    have h' : Q w + Q w - polar Q w w' = 0 := by rw [← h]
    rw [(sub_eq_zero.mp h').symm]
    ring
  have hcoef : ((2 : K)⁻¹) ^ 2 * (4 : K) = 1 := by
    calc ((2 : K)⁻¹) ^ 2 * (4 : K) = ((2 : K)⁻¹ * 2) * ((2 : K)⁻¹ * 2) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ h2, one_mul]
  set b : V := (2 : K)⁻¹ • (w + w') with hb
  have hsumQ : Q (w + w') = 4 * Q w := by
    rw [QuadraticMap.map_add Q, ← hQw, hpol]
    ring
  have hQb : Q b = Q w := by
    rw [hb, map_smul_eq_sq, hsumQ, ← mul_assoc, hcoef, one_mul]
  have hQb_ne : Q b ≠ 0 := by rw [hQb]; exact hw0
  have hbw : polar Q b w = 2 * Q w := by
    rw [hb, polar_smul_left_eq, polar_add_left, polar_self_eq_two_mul, polar_comm Q w' w,
      hpol, show (2 : K) * Q w + 2 * Q w = 2 * (2 * Q w) by ring, ← mul_assoc,
      inv_mul_cancel₀ h2, one_mul]
  have hrb : reflect Q b w = -w' := by
    rw [reflect_apply hQb_ne, hbw, hQb, mul_div_cancel_right₀ _ hw0, hb, smul_smul,
      mul_inv_cancel₀ h2, one_smul]
    abel
  set a : V := w' with ha
  have hra : reflect Q a (-w') = w' := by
    rw [ha, reflect_apply hQw', polar_neg_right, polar_self_eq_two_mul, neg_div,
      mul_div_cancel_right₀ _ hQw', neg_smul, sub_neg_eq_add, two_smul]
    abel
  have hae : polar Q e a = 0 := by rw [ha]; exact hw'
  have heb : polar Q e b = 0 := by
    rw [hb, polar_smul_right_eq, polar_add_right, hw, hw', add_zero, mul_zero]
  refine ⟨a, b, hae, heb, ?_, ?_⟩
  · rw [ha, hQb, hQw]
  · rw [LinearEquiv.mul_apply, hrb, hra]

theorem exists_reflect_mul_reflect_apply_eq [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    {e w w' : V} (he : Q e ≠ 0) (hw : polar Q e w = 0) (hw' : polar Q e w' = 0)
    (hQw : Q w = Q w') (hw0 : Q w ≠ 0) :
    ∃ a b, polar Q e a = 0 ∧ polar Q e b = 0 ∧ Q a = Q b ∧
      (reflect Q a * reflect Q b) w = w' := by
  by_cases h : Q (w - w') = 0
  · exact exists_reflect_mul_reflect_apply_eq_of_map_sub_eq_zero_th2a h2 hw hw' hQw hw0 h
  · exact exists_reflect_mul_reflect_apply_eq_of_map_sub_ne_zero_th2a h2 hQ hdim he hw hw' hQw
      hw0 h

end CFSG.ClassicalGroups.Orthogonal

end
