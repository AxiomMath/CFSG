module

public import CFSG.Certificates.Kernel.Ivk8NormPSound
public import CFSG.Certificates.Kernel.Ivk8NormSound

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.PK Subgroup

variable {n : ℕ}

theorem pkp_mem_closure_of_subprods :
    ∀ (S : List (VP n)), ∀ g ∈ subprodsV S, pkp g ∈ closure {x | x ∈ S.map pkp}
  | [], g, hg => by
    simp only [subprodsV, List.mem_singleton] at hg
    rw [hg, pkp_oneV]
    exact one_mem _
  | s :: S, g, hg => by
    have hle : closure {x | x ∈ S.map pkp} ≤ closure {x | x ∈ (s :: S).map pkp} :=
      closure_mono fun x hx => List.mem_cons_of_mem _ hx
    simp only [subprodsV, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hle (pkp_mem_closure_of_subprods S g hg)
    · rw [pkp_mulV]
      exact mul_mem (subset_closure (List.mem_cons_self ..))
        (hle (pkp_mem_closure_of_subprods S g' hg'))

theorem comm_of_mem_closure {M : Type*} [Group M] {S : Set M}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
  have h1 : closure S ≤ centralizer S := closure_le _ |>.2 fun x hx =>
    mem_centralizer_iff.2 fun y hy => hcomm y hy x hx
  have h2 : closure S ≤ centralizer (closure S : Set M) := closure_le _ |>.2 fun x hx =>
    mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (h1 hy) x hx).symm
  intro x hx y hy
  exact mem_centralizer_iff.1 (h2 hy) x hx

theorem isPGroup_two_closure {M : Type*} [Group M] {S : Set M} (hinv : ∀ x ∈ S, x * x = 1)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : IsPGroup 2 (closure S) := by
  have hsq : ∀ g ∈ closure S, g * g = 1 := by
    intro g hg
    induction hg using closure_induction with
    | mem x hx => exact hinv x hx
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [comm_of_mem_closure hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, sq]
  exact Subtype.ext (hsq g g.2)

theorem hN_of_chkP (hn : n < 16777216) (hw : n + 1 < 2 ^ wd n) {p : ℕ} (hp : p.Prime) {H : Subgroup (Equiv.Perm (Fin n))}
    {xs : List (VP n)} (hxs : ∀ x ∈ xs, pkp x ∈ H) (c : VP n) {L : List (VP n)}
    (h : chkP n (wd n) p ((subprodsV (xs.map (conjV (invV c)))).tail.map Subtype.val)
      (L.map fun y => y.1.1) = true) :
    ∀ y ∈ L, orderOf (pkp y) = p → ∃ g ∈ H, g ∉ normalizer
      (zpowers (pkp c * pkp y * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n))) := by
  intro y hy hyo
  obtain ⟨g, hg, hgN⟩ := chkP_spec (by omega) hn hw hp h y hy hyo
  have hgS : g ∈ subprodsV (xs.map (conjV (invV c))) := List.mem_of_mem_tail hg
  have hgcl := pkp_mem_closure_of_subprods _ g hgS
  have hcl : closure {x | x ∈ (xs.map (conjV (invV c))).map pkp} ≤
      H.comap (MulAut.conj (pkp c)).toMonoidHom := by
    rw [closure_le]
    intro z hz
    simp only [Set.mem_setOf_eq, List.map_map, List.mem_map, Function.comp] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [SetLike.mem_coe, mem_comap, pkp_conjV, pkp_invV, inv_inv]
    simpa [mul_assoc] using hxs x hx
  refine ⟨pkp c * pkp g * (pkp c)⁻¹, by simpa using hcl hgcl, fun hN => hgN ?_⟩
  rw [mem_normalizer_iff] at hN ⊢
  intro z
  have hmap : (zpowers (pkp y)).map (MulAut.conj (pkp c)).toMonoidHom =
      zpowers (pkp c * pkp y * (pkp c)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hconj : ∀ u, pkp c * u * (pkp c)⁻¹ ∈ zpowers (pkp c * pkp y * (pkp c)⁻¹) ↔
      u ∈ zpowers (pkp y) := by
    intro u
    rw [← hmap]
    exact mem_map_iff_mem (MulAut.conj (pkp c)).injective
  have e2 := hN (pkp c * z * (pkp c)⁻¹)
  have e3 : pkp c * pkp g * (pkp c)⁻¹ * (pkp c * z * (pkp c)⁻¹) *
      (pkp c * pkp g * (pkp c)⁻¹)⁻¹ = pkp c * (pkp g * z * (pkp g)⁻¹) * (pkp c)⁻¹ := by group
  rw [e3, hconj, hconj] at e2
  exact e2

end CFSG.KS.Ivk8NormP

end
