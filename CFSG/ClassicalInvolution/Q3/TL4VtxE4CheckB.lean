module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Check
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic CFSG.Sporadic.Schreier CFSG.ClassicalInvolution.Asc77

variable {n : ℕ}

theorem orderOf_eq_four {u : Equiv.Perm (Fin n)} (h2 : ¬ u ^ 2 = 1) (h4 : u ^ 4 = 1) :
    orderOf u = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)

theorem starRel_of_treeStep {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L)
    {H : Subgroup (Equiv.Perm (Fin n))} {u gp gk : Equiv.Perm (Fin n)} {d : Bool}
    (hgp : gp ∈ H) (hgk : gk ∈ H) (huL : u ∈ L) (hu4 : orderOf u = 4)
    (hc : treeStep L i j u gp gk d = true) :
    Vtx.StarRel H (Subgroup.closure ({i, j} : Set _))
      (conjSub gp (Subgroup.closure ({i, j} : Set _)))
      (conjSub gk (Subgroup.closure ({i, j} : Set _))) := by
  set K := Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) with hK
  simp only [treeStep, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hne, hd⟩ := hc
  have huK : u ∈ K := (hiff u).mpr huL
  refine ⟨⟨gp, hgp, rfl⟩, ⟨gk, hgk, rfl⟩, fun e => ?_, ?_⟩
  · have h1 : conjSub (gp⁻¹ * gk) K = K := by
      rw [conjSub_mul, ← e, conjSub_inv_conjSub]
    rw [norms_of_conjSub_eq hiff h1] at hne
    exact Bool.noConfusion hne
  · have hord : ∀ g : Equiv.Perm (Fin n), orderOf (g * u * g⁻¹) = 4 := fun g => by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu4]
    cases d with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hd
      left
      refine ⟨gk * u * gk⁻¹, conj_mem_conjSub huK, hord gk, ?_⟩
      rw [mem_normalizer_iff_conjSub_eq]
      have h1 := conjSub_eq_of_norms hiff hd
      calc conjSub (gk * u * gk⁻¹) (conjSub gp K) =
          conjSub gp (conjSub (gp⁻¹ * (gk * u * gk⁻¹) * gp) K) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub gp K := by rw [h1]
    | true =>
      simp only [↓reduceIte] at hd
      right
      refine ⟨gp * u * gp⁻¹, conj_mem_conjSub huK, hord gp, ?_⟩
      rw [mem_normalizer_iff_conjSub_eq]
      have h1 := conjSub_eq_of_norms hiff hd
      calc conjSub (gp * u * gp⁻¹) (conjSub gk K) =
          conjSub gk (conjSub (gk⁻¹ * (gp * u * gp⁻¹) * gk) K) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub gk K := by rw [h1]

theorem reflTransGen_of_treeCheck {L U : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L)
    {H : Subgroup (Equiv.Perm (Fin n))} {ws : List (Equiv.Perm (Fin n))}
    {tree : List (ℕ × Bool × ℕ)} (hws : ∀ k < ws.length, ws.getD k 1 ∈ H)
    (h0 : ws.getD 0 1 = 1) (hc : treeCheck L U i j ws tree = true) :
    ∀ k < ws.length, Relation.ReflTransGen (Vtx.StarRel H (Subgroup.closure ({i, j} : Set _)))
      (Subgroup.closure ({i, j} : Set _))
        (conjSub (ws.getD k 1) (Subgroup.closure ({i, j} : Set _))) := by
  simp only [treeCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at hc
  obtain ⟨hU, hc⟩ := hc
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hc k hk with rfl | ⟨⟨hp, hU'⟩, hstep⟩
    · rw [h0, conjSub_one]
    · have hmemU : U.getD (tree.getD k (0, false, 0)).2.2 1 ∈ U := by
        rw [List.getD_eq_getElem _ _ hU']
        exact List.getElem_mem hU'
      have huL := hU _ hmemU
      exact (ih _ hp (hp.trans hk)).tail (starRel_of_treeStep hiff (hws _ (hp.trans hk))
        (hws k hk) huL.1.1 (orderOf_eq_four huL.1.2 huL.2) hstep)

theorem conjSub_le_normalizer_of_norms {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L) {g : Equiv.Perm (Fin n)}
    (h1 : norms L i j (g * i * g⁻¹) = true) (h2 : norms L i j (g * j * g⁻¹) = true) :
    conjSub g (Subgroup.closure ({i, j} : Set _)) ≤
      Subgroup.normalizer ((Subgroup.closure ({i, j} : Set _) : Subgroup _) : Set _) := by
  unfold conjSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_normalizer_iff_conjSub_eq]
  rcases hy with rfl | rfl
  · exact conjSub_eq_of_norms hiff h1
  · exact conjSub_eq_of_norms hiff h2

theorem norms_of_conjSub_le {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L) {g : Equiv.Perm (Fin n)}
    (hle : conjSub g (Subgroup.closure ({i, j} : Set _)) ≤
      Subgroup.normalizer ((Subgroup.closure ({i, j} : Set _) : Subgroup _) : Set _)) :
    norms L i j (g * i * g⁻¹) = true ∧ norms L i j (g * j * g⁻¹) = true := by
  have hi := hle (conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert i {j})))
  have hj := hle (conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert_of_mem i rfl)))
  rw [mem_normalizer_iff_conjSub_eq] at hi hj
  exact ⟨norms_of_conjSub_eq hiff hi, norms_of_conjSub_eq hiff hj⟩

theorem not_le_normalizer_of_nbrCheck {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L)
    {ws : List (Equiv.Perm (Fin n))} {allowed : List ℕ} (hc : nbrCheck L i j ws allowed = true)
    {k : ℕ} (hk : k < ws.length) (hka : k ∉ allowed) :
    ¬ conjSub (ws.getD k 1) (Subgroup.closure ({i, j} : Set _)) ≤
      Subgroup.normalizer ((Subgroup.closure ({i, j} : Set _) : Subgroup _) : Set _) := by
  intro hle
  simp only [nbrCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨h1, h2⟩ := norms_of_conjSub_le hiff hle
  rcases hc k hk with h | h
  · exact hka h
  · rw [h1, h2] at h
    exact Bool.noConfusion h

theorem edge_of_edgeCheck {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L) {g : Equiv.Perm (Fin n)}
    (hc : edgeCheck L i j g = true) :
    conjSub g (Subgroup.closure ({i, j} : Set _)) ≠ Subgroup.closure ({i, j} : Set _) ∧
      conjSub g (Subgroup.closure ({i, j} : Set _)) ≤
        Subgroup.normalizer ((Subgroup.closure ({i, j} : Set _) : Subgroup _) : Set _) := by
  simp only [edgeCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hne, h1⟩, h2⟩ := hc
  refine ⟨fun e => ?_, conjSub_le_normalizer_of_norms hiff h1 h2⟩
  rw [norms_of_conjSub_eq hiff e] at hne
  exact Bool.noConfusion hne

end CFSG.ClassicalInvolution.Q3.TL4.E4C
