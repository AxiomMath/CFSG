module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fam
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec121_exists_V0 (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    ∃ V0 : Subgroup G, V0 ≤ E ∧ secB S L ≤ V0 ∧
      (∀ y ∈ secM t S L ⊓ L, ∀ x ∈ V0, y * x * y⁻¹ ∈ V0) ∧
      (∀ e ∈ E, ∃ x ∈ V0, ∃ a ∈ secA t S L, e = x * a) ∧ t ∉ V0 := by
  obtain ⟨φ, hperm⟩ := sec121_exists_perm F
  obtain ⟨u, hu, hfu, hequi⟩ := sec121_exists_family F hE hperm
  let V0 : Subgroup G :=
    Subgroup.closure ((secB S L : Set G) ∪ {z | ∃ i j, z = u i * u j})
  have hV0def : V0 = Subgroup.closure
      ((secB S L : Set G) ∪ {z | ∃ i j, z = u i * u j}) := rfl
  have hB_le_E : secB S L ≤ E := le_sup_left.trans (sec120_A_le_E F hE)
  have hV0_le_E : V0 ≤ E := by
    rw [hV0def, Subgroup.closure_le]
    intro z hz
    rcases hz with hzB | ⟨i, j, rfl⟩
    · exact hB_le_E hzB
    · exact E.mul_mem (hu i) (hu j)
  have hB_le_V0 : secB S L ≤ V0 := by
    rw [hV0def]
    intro b hb
    exact Subgroup.subset_closure (Or.inl hb)
  have hInv : ∀ y ∈ secM t S L ⊓ L, ∀ x ∈ V0, y * x * y⁻¹ ∈ V0 := by
    intro y hy x hx
    rw [hV0def] at hx
    obtain ⟨σ, -, hσact⟩ := hperm.2.2.2.1 y hy
    let c : Fin 5 → G := fun i => (u (σ i))⁻¹ * (y * u i * y⁻¹)
    have hc : ∀ i, c i ∈ secB S L := fun i => hequi y hy σ hσact i
    have hcu : ∀ i, y * u i * y⁻¹ = u (σ i) * c i := by
      intro i
      change y * u i * y⁻¹ = u (σ i) * ((u (σ i))⁻¹ * (y * u i * y⁻¹))
      group
    have hcomm : ∀ i j, c i * u (σ j) = u (σ j) * c i := by
      intro i j
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (hE.1 (hu (σ j)))).2) (c i) (hc i)
    refine Subgroup.closure_induction (p := fun z _ => y * z * y⁻¹ ∈ V0)
      ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases hz with hzB | ⟨i, j, rfl⟩
      · exact hB_le_V0 (F.normB y hy.1 z hzB)
      · have hstep : y * (u i * u j) * y⁻¹ =
            (u (σ i) * u (σ j)) * (c i * c j) := by
          calc y * (u i * u j) * y⁻¹
              = (y * u i * y⁻¹) * (y * u j * y⁻¹) := by group
            _ = (u (σ i) * c i) * (u (σ j) * c j) := by rw [hcu i, hcu j]
            _ = u (σ i) * (c i * u (σ j)) * c j := by group
            _ = u (σ i) * (u (σ j) * c i) * c j := by rw [hcomm i j]
            _ = (u (σ i) * u (σ j)) * (c i * c j) := by group
        rw [hstep]
        exact V0.mul_mem (Subgroup.subset_closure (Or.inr ⟨σ i, σ j, rfl⟩))
          (hB_le_V0 ((secB S L).mul_mem (hc i) (hc j)))
    · simpa using V0.one_mem
    · intro a b _ _ iha ihb
      rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
      exact V0.mul_mem iha ihb
    · intro a _ iha
      rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
      exact V0.inv_mem iha
  have hEA : ∀ e ∈ E, ∃ x ∈ V0, ∃ a ∈ secA t S L, e = x * a := by
    intro e he
    obtain ⟨v, hv, hve⟩ :=
      (hperm.2.2.1 (sec12f t e)).1 (sec12E_f_mem F (hE.1 he))
    obtain ⟨a, b, c, d, hvw⟩ := even_eq_four_wvec hv
    let x : G := (u a * u b) * (u c * u d)
    have hxV : x ∈ V0 := by
      refine V0.mul_mem ?_ ?_
      · exact Subgroup.subset_closure (Or.inr ⟨a, b, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr ⟨c, d, rfl⟩)
    have hxE : x ∈ E := hV0_le_E hxV
    have hf_pair : ∀ i j, sec12f t (u i * u j) = φ (wvec i + wvec j) := by
      intro i j
      rw [sec12E_f_mul F (hE.1 (hu i)) (hE.1 (hu j)), hfu i, hfu j,
        ← hperm.1 (wvec i) (wvec j) (wvec_even i) (wvec_even j)]
    have hfx : sec12f t x = φ v := by
      change sec12f t ((u a * u b) * (u c * u d)) = φ v
      rw [sec12E_f_mul F (hE.1 (E.mul_mem (hu a) (hu b)))
          (hE.1 (E.mul_mem (hu c) (hu d))), hf_pair a b, hf_pair c d,
        ← hperm.1 (wvec a + wvec b) (wvec c + wvec d)
          (wvec_add_even a b) (wvec_add_even c d), hvw]
    refine ⟨x, hxV, x⁻¹ * e, ?_, by group⟩
    exact sec120_inv_mul_mem_A F hE hxE he (hfx.trans hve)
  have ht_not_mem : t ∉ V0 := by
    intro ht
    rw [hV0def] at ht
    have hf1 : sec12f t t = 1 := by
      rw [sec12f, sec12E_t_sq F, one_mul, ← mul_inv_rev, sec12E_t_sq F, inv_one]
    exact sec120_t_not_mem_L F
      (F.bdata.1 (sec121_closure_ker F hE hperm hu hfu t ht hf1))
  exact ⟨V0, hV0_le_E, hB_le_V0, hInv, hEA, ht_not_mem⟩

end CFSG.OddStandard.SmallF3.Omega
