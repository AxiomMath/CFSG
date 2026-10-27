module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentQuad
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentStab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {Bb : Subgroup ↥(orthDerived Q)}

section Plane

variable {x : V ≃ₗ[F] V} {t : F} {v : V}

theorem eq_zero_of_apply_eq_of_mem_quadKer (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {w : V}
    (hw : w ∈ quadKer x t) (hxw : x w = w) : w = 0 := by
  have h0 := mem_quadKer_iff.1 hw
  rw [hxw, hxw] at h0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht 1 (by simpa [one_add_one_eq_two] using h2)
  have h3 : w + w = 0 := by rw [← two_smul F w, h2, zero_smul]
  have h4 : t • w = (w + t • w + w) - (w + w) := by abel
  rw [h0, h3, sub_zero] at h4
  exact (smul_eq_zero.1 h4).resolve_left ht0

theorem planeData_of_quad (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) (hv : x (x v) + t • x v + v = 0) (hQv : Q v ≠ 0) :
    PlaneData Q x v t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht 1 (by simpa [one_add_one_eq_two] using (CharTwo.two_eq_zero : (2 : F) = 0))
  have hxx : x (x v) = t • x v + v := by
    have h5 : x (x v) + (t • x v + v) = 0 := by rw [← add_assoc]; exact hv
    rw [eq_neg_of_add_eq_zero_left h5]
    exact neg_eq_self_vec F _
  have hQw : Q (x v) = Q v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx v
  have hQxw : Q (x (x v)) = Q v := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx (x v), hQw]
  refine ⟨ht0, hQv, hxx, hQw, ?_, fun s => by have h := ht s; rwa [← pow_two] at h⟩
  have h1 := hQxw
  rw [hxx, QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    hQw] at h1
  simp only [smul_eq_mul] at h1
  have hwv : polar Q (x v) v = polar Q v (x v) := QuadraticMap.polar_comm _ _ _
  have h2 : t * (t * Q v + polar Q v (x v)) = 0 := by
    rw [← hwv]
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_left ht0
  rw [CharTwo.add_eq_zero] at h3
  exact h3.symm

theorem not_isPlusType_plane_of_planeData {c : F} (hd : PlaneData Q x v c) :
    ¬ IsPlusType (Q.comp (plane x v).subtype) := by
  rintro ⟨W, hW, hWs⟩
  have h1 : Module.finrank F W = 1 := by
    have := hd.finrank_plane
    omega
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (by rintro rfl; simp at h1 : W ≠ ⊥)
  have h2 := hWs w hwW
  rw [QuadraticMap.comp_apply] at h2
  exact hw0 (Subtype.ext (hd.plane_aniso w.2 h2))

end Plane

private theorem exists_adapted_plane_aux1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hBb : IsElemAbelian p Bb) {N : Submodule F V}
    (hN : RegOn Q N) (hinv : ∀ b ∈ Bb, ∀ y ∈ N, (b : V ≃ₗ[F] V) y ∈ N)
    (hmov : ∃ b ∈ Bb, ∃ y ∈ N, (b : V ≃ₗ[F] V) y ≠ y) :
    ∃ (g : ↥(orthDerived Q)) (t : F) (v : V), g ∈ Bb ∧ v ∈ N ∧
      v ∈ quadKer (g : V ≃ₗ[F] V) t ∧ Q v ≠ 0 ∧ (∀ c : F, c * c + t * c + 1 ≠ 0) ∧
      PlaneData Q (g : V ≃ₗ[F] V) v t ∧ (g : V ≃ₗ[F] V) v ∈ N ∧
      (∀ b ∈ Bb, ∃ m : ℕ, ∀ y ∈ plane (g : V ≃ₗ[F] V) v,
        (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m) y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgB, v₀, hv₀N, hv₀⟩ := hmov
  have hord : orderOf g = p := orderOf_eq_prime (hBb.2 g hgB) (by rintro rfl; exact hv₀ rfl)
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ g hord
  obtain ⟨t, ht, v₁, hv₁N, hv₁, hQv₁⟩ :=
    exists_nonsingular_of_moved hx hp hp2 hpq hN (hinv g hgB) ⟨v₀, hv₀N, hv₀⟩
  obtain ⟨v, ⟨hvN, hvS⟩, hQv, hgen⟩ := exists_stab_max_vector hp hp2 hBb hgB ht hinv
    ⟨v₁, ⟨hv₁N, mem_quadKer_iff.2 hv₁⟩, hQv₁⟩
  have hv := mem_quadKer_iff.1 hvS
  have hiso : ∀ w, Q ((g : V ≃ₗ[F] V) w) = Q w := fun w =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (orthDerived_le_orthogonalGroup g.2) w
  have hv0 : v ≠ 0 := fun h0 => hQv (by rw [h0, QuadraticMap.map_zero])
  have hd : PlaneData Q (g : V ≃ₗ[F] V) v t := planeData_of_quad
    (orthDerived_le_orthogonalGroup g.2) ht hv hQv
  have hgvN : (g : V ≃ₗ[F] V) v ∈ N := hinv g hgB v hvN
  have hpow : ∀ b ∈ Bb, ∃ m : ℕ, ∀ y ∈ plane (g : V ≃ₗ[F] V) v,
      (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m) y := by
    intro b hb
    obtain ⟨m, hm⟩ := hgen b hb
    refine ⟨m, fun y hy => ?_⟩
    obtain ⟨s, t', rfl⟩ := mem_plane.1 hy
    have hc : ((g : V ≃ₗ[F] V) ^ m) ((g : V ≃ₗ[F] V) v) =
        (g : V ≃ₗ[F] V) (((g : V ≃ₗ[F] V) ^ m) v) :=
      congrArg (fun z : V ≃ₗ[F] V => z v)
        ((pow_succ (g : V ≃ₗ[F] V) m).symm.trans (pow_succ' (g : V ≃ₗ[F] V) m))
    rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hm,
      apply_comm_of_isElemAbelian hBb hb hgB v, hm, hc]
  exact ⟨g, t, v, hgB, hvN, hvS, hQv, ht, hd, hgvN, hpow⟩

private theorem exists_adapted_plane_aux2 {x : V ≃ₗ[F] V} {t : F} {v : V}
    (hv : v ∈ quadKer x t) : plane x v ≤ quadKer x t := by
  have hxv : x v ∈ quadKer x t := by
    refine mem_quadKer_iff.2 ?_
    have := congrArg (fun w => x w) (mem_quadKer_iff.1 hv)
    simpa [map_add, map_smul] using this
  intro y hy
  obtain ⟨s, t', rfl⟩ := mem_plane.1 hy
  exact Submodule.add_mem _ (Submodule.smul_mem _ s hv) (Submodule.smul_mem _ t' hxv)

private theorem exists_adapted_plane_aux3 {x : V ≃ₗ[F] V} {t : F} {v : V}
    (hd : PlaneData Q x v t)
    (hpow : ∀ b ∈ Bb, ∃ m : ℕ, ∀ y ∈ plane x v, (b : V ≃ₗ[F] V) y = (x ^ m) y) :
    ∀ b ∈ Bb, ∀ y ∈ plane x v, (b : V ≃ₗ[F] V) y ∈ plane x v := by
  intro b hb y hy
  obtain ⟨m, hm⟩ := hpow b hb
  rw [hm y hy]
  clear hm
  induction m generalizing y with
  | zero => simpa using hy
  | succ m ih => rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hd.plane_invariant hy)

theorem exists_adapted_plane (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hBb : IsElemAbelian p Bb) {N : Submodule F V}
    (hN : RegOn Q N) (hinv : ∀ b ∈ Bb, ∀ y ∈ N, (b : V ≃ₗ[F] V) y ∈ N)
    (hmov : ∃ b ∈ Bb, ∃ y ∈ N, (b : V ≃ₗ[F] V) y ≠ y) :
    ∃ (P : Submodule F V) (g : ↥(orthDerived Q)), g ∈ Bb ∧ P ≤ N ∧ Module.finrank F P = 2 ∧
      RegOn Q P ∧ ¬ IsPlusType (Q.comp P.subtype) ∧
      (∀ b ∈ Bb, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P) ∧
      (∀ y ∈ P, (g : V ≃ₗ[F] V) y = y → y = 0) ∧
      ∀ b ∈ Bb, ∃ m : ℕ, ∀ y ∈ P, (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m) y := by
  obtain ⟨g, t, v, hgB, hvN, hvS, _, ht, hd, hgvN, hpow⟩ :=
    exists_adapted_plane_aux1 hQ hp hp2 hpq hBb hN hinv hmov
  refine ⟨plane (g : V ≃ₗ[F] V) v, g, hgB, plane_le hvN hgvN, hd.finrank_plane, hd.plane_reg,
    not_isPlusType_plane_of_planeData hd, exists_adapted_plane_aux3 hd hpow, ?_, hpow⟩
  intro y hy hgy
  exact eq_zero_of_apply_eq_of_mem_quadKer ht (exists_adapted_plane_aux2 hvS hy) hgy

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
