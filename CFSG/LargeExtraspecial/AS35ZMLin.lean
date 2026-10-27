module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LargeExtraspecial.AS35ZM

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_V (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  simp [show (2 : ZMod 2) = 0 from rfl]

theorem neg_V (v : V) : -v = v := neg_eq_of_add_eq_zero_left (add_self_V v)

theorem eq_of_add_eq_zero_V {a b : V} (h : a + b = 0) : a = b := by
  rw [← neg_V b]
  exact eq_neg_of_add_eq_zero_left h

theorem sub_eq_add_V (v w : V) : v - w = v + w := by
  rw [sub_eq_add_neg, neg_V]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem commSpace_apply_mem {g : V ≃ₗ[ZMod 2] V} {w : V} (hw : w ∈ commSpace g) :
    g w ∈ commSpace g := by
  obtain ⟨v, rfl⟩ := mem_commSpace.1 hw
  rw [map_sub]
  exact sub_mem_commSpace g _

theorem commSpace_mem_of_commute {g u : V ≃ₗ[ZMod 2] V} (hug : ∀ v, u (g v) = g (u v))
    {w : V} (hw : w ∈ commSpace g) : u w ∈ commSpace g := by
  obtain ⟨v, rfl⟩ := mem_commSpace.1 hw
  rw [map_sub, hug]
  exact sub_mem_commSpace g _

theorem cube_on_commSpace {g : V ≃ₗ[ZMod 2] V} (h3 : ∀ v, g (g (g v)) = v) {w : V}
    (hw : w ∈ commSpace g) : g (g w) + g w + w = 0 := by
  obtain ⟨v, rfl⟩ := mem_commSpace.1 hw
  simp only [sub_eq_add_V, map_add, h3]
  calc v + g (g v) + (g (g v) + g v) + (g v + v)
      = (g (g v) + g (g v)) + (g v + g v) + (v + v) := by abel
    _ = 0 := by simp [add_self_V]

section Four

variable {J : V ≃ₗ[ZMod 2] V}

theorem J_injective_zero {v : V} (h : J v = 0) : v = 0 := by
  rw [← map_zero J] at h
  exact J.injective h

theorem eq_on_span_pair {u : V ≃ₗ[ZMod 2] V} (hu : ∀ x, u (J x) = J (u x))
    (T : V →ₗ[ZMod 2] V) (hTJ : ∀ x, T (J x) = J (T x)) {v : V} (hv : u v = T v) :
    ∀ w ∈ Submodule.span (ZMod 2) {v, J v}, u w = T w := by
  intro w hw
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
  rw [map_add, map_smul, map_smul, hu, hv, map_add, map_smul, map_smul, hTJ]

theorem pow_apply_mod_three {P : Submodule (ZMod 2) V} {u : V ≃ₗ[ZMod 2] V}
    (h3 : ∀ w ∈ P, u (u (u w)) = w) (n : ℕ) : ∀ w ∈ P, (u ^ n) w = (u ^ (n % 3)) w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    by_cases hn : n < 3
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [pow_add, LinearEquiv.mul_apply, show u ^ 3 = u * u * u by rw [pow_three, mul_assoc],
        LinearEquiv.mul_apply, LinearEquiv.mul_apply, h3 w hw, ih m (by omega) w hw,
        Nat.add_mod_right]

variable (hJ : ∀ v, J (J v) + J v + v = 0)
include hJ

theorem J_J (v : V) : J (J v) = J v + v :=
  eq_of_add_eq_zero_V (by rw [← add_assoc]; exact hJ v)

theorem J_J_add (v : V) : J (J v) + J v = v := by
  rw [J_J hJ, add_comm (J v) v, add_assoc, add_self_V, add_zero]

theorem eq_zero_of_J_eq (v : V) (h : J v = v) : v = 0 := by
  have := hJ v
  rw [h, h, add_self_V, zero_add] at this
  exact this

theorem J_J_J (v : V) : J (J (J v)) = v := by
  rw [J_J hJ, J_J hJ, add_comm (J v) v, add_assoc, add_self_V, add_zero]

theorem two_le_finrank_of_J [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hPJ : ∀ v ∈ P, J v ∈ P) (hP : P ≠ ⊥) : 2 ≤ finrank (ZMod 2) P := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hle : Submodule.span (ZMod 2) {v} ≤ P := (Submodule.span_singleton_le_iff_mem v P).2 hvP
  have hfr : finrank (ZMod 2) P ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) := by
    rw [finrank_span_singleton hv0]
    omega
  have heq := Submodule.eq_of_le_of_finrank_le hle hfr
  have hJv : J v ∈ Submodule.span (ZMod 2) {v} := heq ▸ hPJ v hvP
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hJv
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul] at ha
    exact hv0 (J_injective_zero ha.symm)
  · rw [one_smul] at ha
    exact hv0 (eq_zero_of_J_eq hJ v ha.symm)

theorem point_cases [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hP2 : finrank (ZMod 2) P ≤ 2) (hPJ : ∀ v ∈ P, J v ∈ P) {u : V ≃ₗ[ZMod 2] V}
    (hu : ∀ v, u (J v) = J (u v)) (huP : ∀ v ∈ P, u v ∈ P) :
    (∀ w ∈ P, u w = w) ∨ (∀ w ∈ P, u w = J w) ∨ (∀ w ∈ P, u w = J (J w)) := by
  by_cases hP : P = ⊥
  · left
    intro w hw
    rw [hP, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  set Q := Submodule.span (ZMod 2) {v, J v} with hQ
  have hQP : Q ≤ P := by
    rw [hQ, Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hvP
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hPJ v hvP
  have hQJ : ∀ w ∈ Q, J w ∈ Q := by
    intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine Submodule.mem_span_pair.2 ⟨d, c + d, ?_⟩
    rw [map_add, map_smul, map_smul, J_J hJ, smul_add, add_smul]
    abel
  have hvQ : v ∈ Q := Submodule.subset_span (Set.mem_insert v _)
  have h2 := two_le_finrank_of_J hJ hQJ (fun h => hv0 (by rw [h] at hvQ; exact hvQ))
  have heq : Q = P := Submodule.eq_of_le_of_finrank_le hQP (by omega)
  have huv : u v ∈ Q := heq ▸ huP v hvP
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 huv
  rw [← heq]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · exfalso
    rw [zero_smul, zero_smul, add_zero] at hab
    exact hv0 (u.injective (by rw [← hab, map_zero]))
  · right; left
    exact eq_on_span_pair hu J.toLinearMap (fun x => rfl)
      (by rw [← hab, zero_smul, zero_add, one_smul]; rfl)
  · left
    exact eq_on_span_pair hu LinearMap.id (fun x => rfl)
      (by rw [← hab, zero_smul, add_zero, one_smul]; rfl)
  · right; right
    exact eq_on_span_pair hu (J.toLinearMap ∘ₗ J.toLinearMap) (fun x => rfl)
      (by rw [← hab, one_smul, one_smul, LinearMap.comp_apply]; simp [J_J hJ, add_comm])

theorem point_cube [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hP2 : finrank (ZMod 2) P ≤ 2) (hPJ : ∀ v ∈ P, J v ∈ P) {u : V ≃ₗ[ZMod 2] V}
    (hu : ∀ v, u (J v) = J (u v)) (huP : ∀ v ∈ P, u v ∈ P) :
    ∀ w ∈ P, u (u (u w)) = w := by
  intro w hw
  rcases point_cases hJ hP2 hPJ hu huP with h | h | h
  · rw [h w hw, h w hw, h w hw]
  · rw [h w hw, h _ (hPJ w hw), h _ (hPJ _ (hPJ w hw)), J_J_J hJ]
  · rw [h w hw, h _ (hPJ _ (hPJ w hw)), h _ (hPJ _ (hPJ _ (hPJ _ (hPJ w hw)))),
      J_J_J hJ, J_J_J hJ]

theorem point_two_elt [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hP2 : finrank (ZMod 2) P ≤ 2) (hPJ : ∀ v ∈ P, J v ∈ P) {u : V ≃ₗ[ZMod 2] V}
    (hu : ∀ v, u (J v) = J (u v)) (huP : ∀ v ∈ P, u v ∈ P) {a : ℕ} (ha : u ^ (2 ^ a) = 1) :
    ∀ w ∈ P, u w = w := by
  have h3 := point_cube hJ hP2 hPJ hu huP
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by
    have : 2 ^ a % 3 ≠ 0 := by
      intro h0
      have h3d : 3 ∣ 2 ^ a := Nat.dvd_of_mod_eq_zero h0
      exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)) (by norm_num)
    omega
  have key : ∀ w ∈ P, w = (u ^ (2 ^ a % 3)) w := by
    intro w hw
    rw [← pow_apply_mod_three h3 _ w hw, ha]; rfl
  have hP0 : ∀ w ∈ P, u w = J w ∨ u w = J (J w) → (u (u w) = J (J w) ∨ u (u w) = J w) →
      w = 0 := by
    intro w hw h1 h2
    rcases hmod with hm | hm
    · have e := key w hw
      rw [hm, pow_one] at e
      rcases h1 with h1 | h1
      · exact eq_zero_of_J_eq hJ w (h1 ▸ e).symm
      · have : J (J (J w)) = J w := by rw [← h1, ← e]
        rw [J_J_J hJ] at this
        exact eq_zero_of_J_eq hJ w this.symm
    · have e := key w hw
      rw [hm, sq, LinearEquiv.mul_apply] at e
      rcases h2 with h2 | h2
      · have : J (J (J w)) = J w := by rw [← h2, ← e]
        rw [J_J_J hJ] at this
        exact eq_zero_of_J_eq hJ w this.symm
      · exact eq_zero_of_J_eq hJ w (h2 ▸ e).symm
  intro w hw
  rcases point_cases hJ hP2 hPJ hu huP with h | h | h
  · exact h w hw
  · have := hP0 w hw (Or.inl (h w hw)) (Or.inl (by rw [h w hw, h _ (hPJ w hw)]))
    rw [this, map_zero]
  · have := hP0 w hw (Or.inr (h w hw)) (Or.inr (by
      rw [h w hw, h _ (hPJ _ (hPJ w hw)), J_J_J hJ]))
    rw [this, map_zero]

end Four

abbrev eigOne (J g : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  commSpace g ⊓ LinearMap.ker (g.toLinearMap - J.toLinearMap)

abbrev eigTwo (J g : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  commSpace g ⊓ LinearMap.ker (g.toLinearMap - J.toLinearMap ∘ₗ J.toLinearMap)

theorem mem_eigOne {J g : V ≃ₗ[ZMod 2] V} {w : V} :
    w ∈ eigOne J g ↔ w ∈ commSpace g ∧ g w = J w := by
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

theorem mem_eigTwo {J g : V ≃ₗ[ZMod 2] V} {w : V} :
    w ∈ eigTwo J g ↔ w ∈ commSpace g ∧ g w = J (J w) := by
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

section Torus

variable {J g : V ≃ₗ[ZMod 2] V} (hgJ : ∀ v, g (J v) = J (g v))
include hgJ

theorem J_mem_commSpace {w : V} (hw : w ∈ commSpace g) : J w ∈ commSpace g :=
  commSpace_mem_of_commute (fun v => (hgJ v).symm) hw

theorem eigOne_J_mem {w : V} (hw : w ∈ eigOne J g) : J w ∈ eigOne J g := by
  rw [mem_eigOne] at hw ⊢
  exact ⟨J_mem_commSpace hgJ hw.1, by rw [hgJ, hw.2]⟩

theorem eigTwo_J_mem {w : V} (hw : w ∈ eigTwo J g) : J w ∈ eigTwo J g := by
  rw [mem_eigTwo] at hw ⊢
  exact ⟨J_mem_commSpace hgJ hw.1, by rw [hgJ, hw.2]⟩

omit hgJ in
theorem eigOne_u_mem {u : V ≃ₗ[ZMod 2] V} (hu : ∀ v, u (J v) = J (u v))
    (hug : ∀ v, u (g v) = g (u v)) {w : V} (hw : w ∈ eigOne J g) : u w ∈ eigOne J g := by
  rw [mem_eigOne] at hw ⊢
  exact ⟨commSpace_mem_of_commute hug hw.1, by rw [← hug, hw.2, hu]⟩

omit hgJ in
theorem eigTwo_u_mem {u : V ≃ₗ[ZMod 2] V} (hu : ∀ v, u (J v) = J (u v))
    (hug : ∀ v, u (g v) = g (u v)) {w : V} (hw : w ∈ eigTwo J g) : u w ∈ eigTwo J g := by
  rw [mem_eigTwo] at hw ⊢
  exact ⟨commSpace_mem_of_commute hug hw.1, by rw [← hug, hw.2, hu, hu]⟩

variable (hJ : ∀ v, J (J v) + J v + v = 0) (h3 : ∀ v, g (g (g v)) = v)
include hJ h3

theorem decomp_one_mem {w : V} (hw : w ∈ commSpace g) : g w + J (J w) ∈ eigOne J g := by
  rw [mem_eigOne]
  refine ⟨Submodule.add_mem _ (commSpace_apply_mem hw)
    (J_mem_commSpace hgJ (J_mem_commSpace hgJ hw)), ?_⟩
  have hc := cube_on_commSpace h3 hw
  have hy := J_J_add hJ (g w)
  rw [map_add, map_add, hgJ, hgJ, J_J_J hJ]
  apply eq_of_add_eq_zero_V
  calc g (g w) + J (J (g w)) + (J (g w) + w) = g (g w) + (J (J (g w)) + J (g w)) + w := by
        abel
    _ = 0 := by rw [hy, ← hc]

theorem decomp_two_mem {w : V} (hw : w ∈ commSpace g) : g w + J w ∈ eigTwo J g := by
  rw [mem_eigTwo]
  refine ⟨Submodule.add_mem _ (commSpace_apply_mem hw) (J_mem_commSpace hgJ hw), ?_⟩
  have hc := cube_on_commSpace h3 hw
  rw [map_add, map_add, map_add, hgJ, J_J hJ (g w), J_J hJ (J w), J_J hJ w]
  apply eq_of_add_eq_zero_V
  calc g (g w) + J (g w) + (J (g w) + g w + (J w + w + J w))
      = (g (g w) + g w + w) + (J (g w) + J (g w)) + (J w + J w) := by abel
    _ = 0 := by rw [hc]; simp only [add_self_V]

omit hgJ h3 in
theorem decomp_sum (w : V) : (g w + J (J w)) + (g w + J w) = w := by
  calc g w + J (J w) + (g w + J w) = (g w + g w) + (J (J w) + J w) := by abel
    _ = w := by rw [add_self_V, J_J_add hJ w, zero_add]

end Torus

section Swap

variable {J g a : V ≃ₗ[ZMod 2] V} (haa : ∀ v, a (a v) = v) (hag : ∀ v, g (a v) = a (g (g v)))
include haa hag

theorem a_commSpace_mem {w : V} (hw : w ∈ commSpace g) : a w ∈ commSpace g := by
  have hag2 : ∀ y, a (g y) = g (g (a y)) := by
    intro y
    have := hag (a y)
    rw [haa] at this
    rw [this, haa]
  obtain ⟨v, rfl⟩ := mem_commSpace.1 hw
  rw [map_sub, hag2]
  have e : g (g (a v)) - a v = (g (g (a v)) - g (a v)) + (g (a v) - a v) := by abel
  rw [e]
  exact Submodule.add_mem _ (sub_mem_commSpace g _) (sub_mem_commSpace g _)

variable (hgJ : ∀ v, g (J v) = J (g v)) (haJ : ∀ v, a (J v) = J (a v))
include hgJ haJ

theorem a_eigOne {w : V} (hw : w ∈ eigOne J g) : a w ∈ eigTwo J g := by
  rw [mem_eigOne] at hw
  rw [mem_eigTwo]
  refine ⟨a_commSpace_mem haa hag hw.1, ?_⟩
  rw [hag, hw.2, hgJ, hw.2, haJ, haJ]

theorem a_eigTwo (hJ : ∀ v, J (J v) + J v + v = 0) {w : V} (hw : w ∈ eigTwo J g) :
    a w ∈ eigOne J g := by
  rw [mem_eigTwo] at hw
  rw [mem_eigOne]
  refine ⟨a_commSpace_mem haa hag hw.1, ?_⟩
  rw [hag, hw.2, hgJ, hgJ, hw.2, J_J_J hJ, haJ]

theorem finrank_eig_le [FiniteDimensional (ZMod 2) V] (hJ : ∀ v, J (J v) + J v + v = 0)
    (hW : finrank (ZMod 2) (commSpace g) ≤ 4) :
    finrank (ZMod 2) (eigOne J g) ≤ 2 ∧ finrank (ZMod 2) (eigTwo J g) ≤ 2 := by
  have h12 : finrank (ZMod 2) (eigOne J g) ≤ finrank (ZMod 2) (eigTwo J g) := by
    rw [← LinearEquiv.finrank_map_eq a (eigOne J g)]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact a_eigOne haa hag hgJ haJ hw
  have h21 : finrank (ZMod 2) (eigTwo J g) ≤ finrank (ZMod 2) (eigOne J g) := by
    rw [← LinearEquiv.finrank_map_eq a (eigTwo J g)]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact a_eigTwo haa hag hgJ haJ hJ hw
  have hinf : eigOne J g ⊓ eigTwo J g = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf, mem_eigOne, mem_eigTwo] at hw
    have h1 : J w = J (J w) := hw.1.2.symm.trans hw.2.2
    rw [Submodule.mem_bot]
    exact eq_zero_of_J_eq hJ w (J.injective h1).symm
  have hsup : eigOne J g ⊔ eigTwo J g ≤ commSpace g := sup_le inf_le_left inf_le_left
  have h := Submodule.finrank_sup_add_finrank_inf_eq (eigOne J g) (eigTwo J g)
  rw [hinf, finrank_bot] at h
  have := Submodule.finrank_mono hsup
  omega

variable [FiniteDimensional (ZMod 2) V] (hJ : ∀ v, J (J v) + J v + v = 0)
  (h3 : ∀ v, g (g (g v)) = v) (hW : finrank (ZMod 2) (commSpace g) ≤ 4)
  {u : V ≃ₗ[ZMod 2] V} (hu : ∀ v, u (J v) = J (u v)) (hug : ∀ v, u (g v) = g (u v))
include hJ h3 hW hu hug

theorem torus_cube : ∀ w ∈ commSpace g, u (u (u w)) = w := by
  obtain ⟨h1, h2⟩ := finrank_eig_le haa hag hgJ haJ hJ hW
  intro w hw
  have e1 := point_cube hJ h1 (fun v hv => eigOne_J_mem hgJ hv) hu
    (fun v hv => eigOne_u_mem hu hug hv) _ (decomp_one_mem hgJ hJ h3 hw)
  have e2 := point_cube hJ h2 (fun v hv => eigTwo_J_mem hgJ hv) hu
    (fun v hv => eigTwo_u_mem hu hug hv) _ (decomp_two_mem hgJ hJ h3 hw)
  conv_lhs => rw [← decomp_sum (g := g) hJ w]
  rw [map_add, map_add, map_add, e1, e2, decomp_sum hJ w]

theorem torus_two_elt {k : ℕ} (hk : u ^ (2 ^ k) = 1) : ∀ w ∈ commSpace g, u w = w := by
  obtain ⟨h1, h2⟩ := finrank_eig_le haa hag hgJ haJ hJ hW
  intro w hw
  have e1 := point_two_elt hJ h1 (fun v hv => eigOne_J_mem hgJ hv) hu
    (fun v hv => eigOne_u_mem hu hug hv) hk _ (decomp_one_mem hgJ hJ h3 hw)
  have e2 := point_two_elt hJ h2 (fun v hv => eigTwo_J_mem hgJ hv) hu
    (fun v hv => eigTwo_u_mem hu hug hv) hk _ (decomp_two_mem hgJ hJ h3 hw)
  conv_lhs => rw [← decomp_sum (g := g) hJ w]
  rw [map_add, e1, e2, decomp_sum hJ w]

end Swap

end CFSG.LargeExtraspecial.AS35ZM
