module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b7

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem closure_pair_mul {a b : G} (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) :
    Subgroup.closure ({a, a * b} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp hx]
      have key : a * (a * b) ∈ Subgroup.closure ({a, a * b} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      rwa [← mul_assoc, haa, one_mul] at key

private theorem exists_fixed_of_involution {t u y : G} (htt : t * t = 1) (huu : u * u = 1)
    (hcomm : t * u = u * t) (hyy : y * y = 1)
    (hyt : y * t * y⁻¹ ∈ ({t, u, t * u} : Set G)) :
    ∃ a, (a = t ∨ a = u ∨ a = t * u) ∧ y * a = a * y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  rw [hyi] at hyt
  have fix : ∀ w : G, y * w * y = w → y * w = w * y := fun w hw => by
    calc y * w = y * w * (y * y) := by rw [hyy, mul_one]
      _ = (y * w * y) * y := by group
      _ = w * y := by rw [hw]
  rcases hyt with e | e | e
  · exact ⟨t, Or.inl rfl, fix t e⟩
  · have hyuy : y * u * y = t := by
      calc y * u * y = y * (y * t * y) * y := by rw [e]
        _ = (y * y) * t * (y * y) := by group
        _ = t := by rw [hyy, one_mul, mul_one]
    refine ⟨t * u, Or.inr (Or.inr rfl), fix _ ?_⟩
    calc y * (t * u) * y = y * t * (y * y) * u * y := by rw [hyy]; group
      _ = (y * t * y) * (y * u * y) := by group
      _ = t * u := by rw [e, hyuy, hcomm]
  · have h1 : y * (t * u) * y = t := by
      calc y * (t * u) * y = y * (y * t * y) * y := by rw [e]
        _ = (y * y) * t * (y * y) := by group
        _ = t := by rw [hyy, one_mul, mul_one]
    have h2 : (t * u) * (y * u * y) = (t * u) * u := by
      calc (t * u) * (y * u * y) = (y * t * y) * (y * u * y) := by rw [e]
        _ = y * (t * u) * y := by
          calc (y * t * y) * (y * u * y) = y * t * (y * y) * u * y := by group
            _ = y * (t * u) * y := by rw [hyy]; group
        _ = t := h1
        _ = (t * u) * u := by rw [mul_assoc, huu, mul_one]
    exact ⟨u, Or.inr (Or.inl rfl), fix u (mul_left_cancel h2)⟩

namespace Tri

variable {K J M : Subgroup G} {t u : G}

theorem counterfree (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S : Sylow 2 G} {P T T' : Subgroup G} (hs : SylowTri Ω S K J M P T T' t u) {L : Subgroup G}
    (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y) (hyS : y ∈ (S : Subgroup G))
    (hyt : y * t = t * y) : y ∈ Subgroup.closure ({t, u} : Set G) := by
  by_contra hyE
  have hΩ := h.fam.hyp
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hs.syl_P.1 hs.syl_P.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hs.syl_P)
    omega)
  have huT : u ∈ T := T3.mem_of_isPGroup h.inv_J hs.syl_T.1 hs.syl_T.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hs.mem_J hs.syl_T)
    omega)
  have htS : t ∈ (S : Subgroup G) := hs.le_P htP
  have huS : u ∈ (S : Subgroup G) := hs.le_T huT
  have hX2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) :=
    S.isPGroup'.to_le inf_le_left
  have hnadj : L ∉ omegaNbr Ω K := fun hLK =>
    hyE (h.mem_E_of_adj (Or.inl rfl) h.inv_K hLK hy hX2 inf_le_right
      (Subgroup.mem_inf.mpr ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
      (Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr h.comm_tu.symm⟩)
      (Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩))
  obtain ⟨-, hyu⟩ := hs.perm_inv hΩ.conjInvariant hyS
  rcases hyu with e | e | e
  · have hu' : u = t := by
      calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
        _ = y⁻¹ * t * y := by rw [e]
        _ = t := by rw [mul_assoc, ← hyt, ← mul_assoc, inv_mul_cancel, one_mul]
    exact absurd hu'.symm h.ne_tu
  · exact no_type2_central hQ h hr hs hL hy hyS hyt (mul_inv_eq_iff_eq_mul.mp e) hyE
  · exact no_type2_swap hQ h hr hs hL hy hyS hyt e hyE

theorem counterfree_all (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S : Sylow 2 G} {P T T' : Subgroup G} (hs : SylowTri Ω S K J M P T T' t u) {a : G}
    (ha : a = t ∨ a = u ∨ a = t * u) {L : Subgroup G} (hL : L ∈ Ω) {y : G}
    (hy : IsUniqueInvolution L y) (hyS : y ∈ (S : Subgroup G)) (hya : y * a = a * y) :
    y ∈ Subgroup.closure ({t, u} : Set G) := by
  have hcomm := h.comm_tu
  rcases ha with ha | ha | ha
  · rw [ha] at hya
    exact counterfree hQ h hr hs hL hy hyS hya
  · rw [ha] at hya
    have hr' : RigidEdge J M u (t * u) := h.rigid_of_adj hr h.adj_J.1 h.adj_MJ h.inv_J h.inv_M
    have := counterfree hQ h.rot hr' hs.rot hL hy hyS hya
    rwa [hcomm, closure_pair_mul h.inv_J.sq h.inv_K.sq hcomm.symm, Set.pair_comm] at this
  · rw [ha] at hya
    have hr' : RigidEdge M K (t * u) (u * (t * u)) :=
      h.rigid_of_adj hr h.adj_M.1 h.rot.rot.adj_J h.inv_M h.rot.rot.inv_J
    have := counterfree hQ h.rot.rot hr' hs.rot.rot hL hy hyS hya
    have e : u * (t * u) = t := by rw [← mul_assoc, ← hcomm, mul_assoc, h.inv_J.sq, mul_one]
    rwa [e, Set.pair_comm, closure_pair_mul h.inv_K.sq h.inv_J.sq hcomm] at this

theorem stronglyClosed (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u) :
    ∃ S : Sylow 2 G, Subgroup.closure ({t, u} : Set G) ≤ (S : Subgroup G) ∧
      fusionStronglyClosed ((Subgroup.closure ({t, u} : Set G) : Subgroup G) : Set G)
        (S : Subgroup G) := by
  obtain ⟨S, P, T, T', hs, -⟩ := h.exists_std_sylowTri
  have hΩ := h.fam.hyp
  have hcomm := h.comm_tu
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hs.syl_P.1 hs.syl_P.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hs.syl_P)
    omega)
  have huT : u ∈ T := T3.mem_of_isPGroup h.inv_J hs.syl_T.1 hs.syl_T.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hs.mem_J hs.syl_T)
    omega)
  have hEle : Subgroup.closure ({t, u} : Set G) ≤ (S : Subgroup G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hs.le_P htP
    · rw [Set.mem_singleton_iff.mp hx]; exact hs.le_T huT
  refine ⟨S, hEle, fun x hx g hxg => ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _
  have hx' : x = t ∨ x = u ∨ x = t * u := by
    rcases TypeCSetup.mem_closure_pair h.inv_K.sq h.inv_J.sq hcomm hx with e | e | e | e
    · exact absurd e hx1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  obtain ⟨c, hc⟩ := h.edge_conj x hx'
  have hyd : g⁻¹ * x * g = (g⁻¹ * c) * t * (g⁻¹ * c)⁻¹ := by rw [hc]; group
  have hy : IsUniqueInvolution (conjSub (g⁻¹ * c) K) (g⁻¹ * x * g) := by
    rw [hyd]; exact h.inv_K.conj (g⁻¹ * c)
  have hL : conjSub (g⁻¹ * c) K ∈ Ω := hΩ.conjInvariant (g⁻¹ * c) K h.mem
  obtain ⟨hyt, -⟩ := hs.perm_inv hΩ.conjInvariant hxg
  obtain ⟨a, ha, hya⟩ := exists_fixed_of_involution h.inv_K.sq h.inv_J.sq hcomm hy.sq hyt
  exact counterfree_all hQ h hr hs ha hL hy hxg hya

end Tri

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
