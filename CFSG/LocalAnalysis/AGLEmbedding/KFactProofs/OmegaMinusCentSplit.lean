module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

def fixSpace (x : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V where
  carrier := {v | x v = v}
  add_mem' := fun {a b} (ha : x a = a) (hb : x b = b) => by
    change x (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := map_zero x
  smul_mem' := fun c v (hv : x v = v) => by
    change x (c • v) = c • v
    rw [map_smul, hv]

def moveSpace (x : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V where
  carrier := {v | x (x v) + x v + v = 0}
  add_mem' := fun {a b} (ha : x (x a) + x a + a = 0) (hb : x (x b) + x b + b = 0) => by
    change x (x (a + b)) + x (a + b) + (a + b) = 0
    calc x (x (a + b)) + x (a + b) + (a + b)
        = (x (x a) + x a + a) + (x (x b) + x b + b) := by simp only [map_add]; abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c v (hv : x (x v) + x v + v = 0) => by
    change x (x (c • v)) + x (c • v) + c • v = 0
    calc x (x (c • v)) + x (c • v) + c • v = c • (x (x v) + x v + v) := by
          simp only [map_smul, smul_add]
      _ = 0 := by rw [hv, smul_zero]

theorem mem_fixSpace {x : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixSpace x ↔ x v = v := Iff.rfl

theorem mem_moveSpace {x : V ≃ₗ[ZMod 2] V} {v : V} :
    v ∈ moveSpace x ↔ x (x v) + x v + v = 0 := Iff.rfl

variable {x : V ≃ₗ[ZMod 2] V}

theorem fix_inf_move : fixSpace x ⊓ moveSpace x = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  rw [mem_fixSpace] at h1
  rw [mem_moveSpace, h1, h1] at h2
  rw [Submodule.mem_bot]
  have := add_self_eq_zero' v
  rw [add_assoc, this, add_zero] at h2
  exact h2

theorem exists_fix_move (hx3 : ∀ v, x (x (x v)) = v) (v : V) :
    ∃ c ∈ fixSpace x, ∃ m ∈ moveSpace x, v = c + m := by
  have h1 := add_self_eq_zero' v
  have h2 := add_self_eq_zero' (x v)
  have h3 := add_self_eq_zero' (x (x v))
  refine ⟨v + x v + x (x v), ?_, x v + x (x v), ?_, ?_⟩
  · rw [mem_fixSpace, map_add, map_add, hx3]
    abel
  · rw [mem_moveSpace]
    simp only [map_add, hx3]
    calc v + x v + (x (x v) + v) + (x v + x (x v))
        = (v + v) + (x v + x v) + (x (x v) + x (x v)) := by abel
      _ = 0 := by rw [h1, h2, h3]; simp
  · calc v = v + (x v + x v) + (x (x v) + x (x v)) := by rw [h2, h3]; simp
      _ = v + x v + x (x v) + (x v + x (x v)) := by abel

theorem fix_sup_move (hx3 : ∀ v, x (x (x v)) = v) : fixSpace x ⊔ moveSpace x = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨c, hc, m, hm, rfl⟩ := exists_fix_move hx3 v
  exact Submodule.add_mem_sup hc hm

theorem isCompl_fix_move (hx3 : ∀ v, x (x (x v)) = v) : IsCompl (fixSpace x) (moveSpace x) :=
  IsCompl.of_eq fix_inf_move (fix_sup_move hx3)

theorem apply_mem_moveSpace (hx3 : ∀ v, x (x (x v)) = v) {m : V} (hm : m ∈ moveSpace x) :
    x m ∈ moveSpace x := by
  rw [mem_moveSpace] at hm ⊢
  rw [hx3]
  calc m + x (x m) + x m = x (x m) + x m + m := by abel
    _ = 0 := hm

theorem polar_fix_move (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c m : V}
    (hc : c ∈ fixSpace x) (hm : m ∈ moveSpace x) : polar Q c m = 0 := by
  rw [mem_fixSpace] at hc
  rw [mem_moveSpace] at hm
  have hm' : m = x (x m) + x m := (eq_of_add_eq_zero' hm).symm
  have h1 : polar Q c (x (x m)) = polar Q c (x m) := by
    have := polar_map_of_mem hx c (x m)
    rwa [hc] at this
  calc polar Q c m = polar Q c (x (x m)) + polar Q c (x m) := by
        conv_lhs => rw [hm']
        rw [polar_add_right]
    _ = 0 := by rw [h1]; exact add_self_eq_zero'' _

theorem polarNondegOn_fix (hQ : (polarBilin Q).Nondegenerate)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) :
    PolarNondegOn Q (fixSpace x) := by
  intro c hc hc0
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  obtain ⟨c', hc', m', hm', rfl⟩ := exists_fix_move hx3 y
  rw [polar_add_right, hc0 c' hc', polar_fix_move hx hc hm', add_zero]

theorem polarNondegOn_move (hQ : (polarBilin Q).Nondegenerate)
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) :
    PolarNondegOn Q (moveSpace x) := by
  intro m hm hm0
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  obtain ⟨c', hc', m', hm', rfl⟩ := exists_fix_move hx3 y
  rw [polar_add_right, polar_comm Q m c', polar_fix_move hx hc' hm, hm0 m' hm', add_zero]

theorem exists_aniso_pairs_move [FiniteDimensional (ZMod 2) V]
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : ∀ v, x (x (x v)) = v) :
    ∀ (n : ℕ) (W : Submodule (ZMod 2) V), finrank (ZMod 2) W = n → W ≤ moveSpace x →
      (∀ w ∈ W, x w ∈ W) → PolarNondegOn Q W →
      ∃ Ps : List (AnisoPair Q), Ps.Pairwise AnisoPair.Orth ∧
        (∀ P ∈ Ps, P.a ∈ W ∧ P.b = x P.a) ∧ finrank (ZMod 2) W = 2 * Ps.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWM hWx hWnd
  by_cases hW0 : W = ⊥
  · refine ⟨[], List.Pairwise.nil, by simp, ?_⟩
    rw [hW0, finrank_bot]
    simp
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hQ1 : ∃ v ∈ W, Q v = 1 := by
    by_contra hcon
    push Not at hcon
    have hQ0 : ∀ w ∈ W, Q w = 0 := fun w hw => by
      rcases zmod_two_cases (Q w) with h | h
      · exact h
      · exact absurd h (hcon w hw)
    apply hv0
    apply hWnd v hvW
    intro y hy
    simp only [polar, hQ0 _ (W.add_mem hvW hy), hQ0 v hvW, hQ0 y hy, sub_zero]
  obtain ⟨v₁, hv₁W, hv₁Q⟩ := hQ1
  have hv₁M := hWM hv₁W
  rw [mem_moveSpace] at hv₁M
  have hxx : x (x v₁) = x v₁ + v₁ := eq_of_add_eq_zero' (by rw [← add_assoc]; exact hv₁M)
  have hQb : Q (x v₁) = 1 := by rw [map_of_mem hx]; exact hv₁Q
  have hpol : polar Q v₁ (x v₁) = 1 := by
    have h := QuadraticMap.map_add Q v₁ (x v₁)
    have h2 : Q (v₁ + x v₁) = 1 := by
      rw [add_comm, ← hxx, map_of_mem hx, map_of_mem hx, hv₁Q]
    rw [h2, hv₁Q, hQb] at h
    revert h
    generalize polar Q v₁ (x v₁) = p
    revert p
    decide
  let P : AnisoPair Q := ⟨v₁, x v₁, hv₁Q, hQb, hpol⟩
  have hbW : P.b ∈ W := hWx v₁ hv₁W
  have hfin := finrank_inf_perp P hv₁W hbW
  have hW'x : ∀ u ∈ W ⊓ P.perp, x u ∈ W ⊓ P.perp := by
    intro u hu
    obtain ⟨huW, hu2⟩ := Submodule.mem_inf.1 hu
    have hu2' := (AnisoPair.mem_perp P).1 hu2
    refine Submodule.mem_inf.2 ⟨hWx u huW, (AnisoPair.mem_perp P).2 ⟨?_, ?_⟩⟩
    · change polar Q v₁ (x u) = 0
      have e1 : polar Q v₁ (x u) = polar Q (x v₁) (x (x u)) := (polar_map_of_mem hx v₁ (x u)).symm
      have e2 : polar Q (x v₁) (x (x u)) = polar Q (x (x v₁)) (x (x (x u))) :=
        (polar_map_of_mem hx (x v₁) (x (x u))).symm
      rw [hx3 u] at e2
      rw [e1, e2, hxx, polar_add_left, hu2'.2, hu2'.1, add_zero]
    · change polar Q (x v₁) (x u) = 0
      rw [polar_map_of_mem hx]
      exact hu2'.1
  have hW'nd := PolarNondegOn.inf_perp_aniso hWnd P hv₁W hbW
  have hW'M : W ⊓ P.perp ≤ moveSpace x := inf_le_left.trans hWM
  have hlt : finrank (ZMod 2) ↥(W ⊓ P.perp) < n := by omega
  obtain ⟨Ps', hpw, hmem, hfr⟩ := ih _ hlt (W ⊓ P.perp) rfl hW'M hW'x hW'nd
  refine ⟨P :: Ps', ?_, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨fun P' hP' => ?_, hpw⟩
    obtain ⟨ha', hb'⟩ := hmem P' hP'
    have ha1 := (AnisoPair.mem_perp P).1 (Submodule.mem_inf.1 ha').2
    have hb1 := (AnisoPair.mem_perp P).1
      (Submodule.mem_inf.1 (hb' ▸ hW'x _ ha')).2
    exact ⟨ha1.1, hb1.1, ha1.2, hb1.2⟩
  · intro P' hP'
    rcases List.mem_cons.1 hP' with rfl | hP''
    · exact ⟨hv₁W, rfl⟩
    · obtain ⟨ha', hb'⟩ := hmem P' hP''
      exact ⟨(Submodule.mem_inf.1 ha').1, hb'⟩
  · simp only [List.length_cons]
    omega

end CFSG.AGLEmbedding.OmegaMinusCent
