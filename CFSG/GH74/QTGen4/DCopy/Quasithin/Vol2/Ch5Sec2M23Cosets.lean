module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Cosets
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Setting

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

variable {G : Type} [Group G]

theorem stmt5_2_22_of_F4 (h519 : Stmt5_2_19_F4) : Stmt5_2_22_F4 := by
  intro G _ _ T M L V H B D L₂ n M2 π t hyp hM23 hS htI hsw
  obtain ⟨hGxM2, hH⟩ := h519 G T M L V H B D L₂ n M2 π hyp hM23 hS
  have hA : m23Gx T M L H B D ⊓ M2 = setStabIn M2 π {5, 6} := hGxM2.trans hH
  set J := m23I M2 π ⊓ stabilizer G ({((1 : G) : G ⧸ m23Gx T M L H B D),
      ((t : G) : G ⧸ m23Gx T M L H B D)} : Set (G ⧸ m23Gx T M L H B D)) ⊔
    m23I M2 π ⊓ m23Gx T M L H B D with hJ
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hIM2 : m23I M2 π ≤ M2 := setStabIn_le M2 π _
  have hJI : J ≤ m23I M2 π := sup_le inf_le_left inf_le_left
  have hlift : ∀ ρ ∈ alternatingGroup (Fin 7), ∃ (r : G) (hr : r ∈ M2), π ⟨r, hr⟩ = ρ := by
    intro ρ hρ
    have : ρ ∈ π.range := by rw [hS.range_eq]; exact hρ
    obtain ⟨r, hr⟩ := this
    exact ⟨r, r.2, hr⟩
  have hΛ : ∀ ρ : Equiv.Perm (Fin 7), (∀ x : Fin 7, x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 →
      ρ x = 3 ∨ ρ x = 4 ∨ ρ x = 5 ∨ ρ x = 6) →
      ρ • ({3, 4, 5, 6} : Set (Fin 7)) = {3, 4, 5, 6} := by
    intro ρ h
    refine perm_smul_set_eq_of_mapsTo fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    exact h x hx

  set Q : Subgroup (Equiv.Perm (Fin 7)) := (J.subgroupOf M2).map π with hQ
  have memQ : ∀ (r : G) (hr : r ∈ M2), r ∈ J → π ⟨r, hr⟩ ∈ Q := fun r hr hrJ =>
    ⟨⟨r, hr⟩, hrJ, rfl⟩
  have hx : ∀ ρ ∈ alternatingGroup (Fin 7), ρ • ({3, 4, 5, 6} : Set (Fin 7)) = {3, 4, 5, 6} →
      ρ • ({5, 6} : Set (Fin 7)) = {5, 6} → ρ ∈ Q := by
    intro ρ hρ h1 h2
    obtain ⟨r, hr, e⟩ := hlift ρ hρ
    rw [← e]
    refine memQ r hr (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨mem_setStabIn.mpr ⟨hr, ?_⟩,
      (mem_iff_of_inf_eq_setStabIn hA hr).mpr ?_⟩))
    · rw [e]; exact h1
    · rw [e]; exact h2
  have h1 : m23Rho1 ∈ Q := by
    refine hx _ ?_ (hΛ _ (by decide)) (by rw [smul_pair_set_eq_iff]; decide)
    rw [Equiv.Perm.mem_alternatingGroup, m23Rho1, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have h2 : m23Rho2 ∈ Q := by
    refine hx _ ?_ (hΛ _ (by decide)) (by rw [smul_pair_set_eq_iff]; decide)
    rw [Equiv.Perm.mem_alternatingGroup, m23Rho2, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have h3 : m23Rho3 ∈ Q := by
    obtain ⟨r, hr, e⟩ := hlift m23Rho3 (by
      rw [Equiv.Perm.mem_alternatingGroup, m23Rho3, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide)
    rw [← e]
    refine memQ r hr (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨mem_setStabIn.mpr ⟨hr, ?_⟩,
      (mem_stabilizer_pair_iff_of_inf_eq_setStabIn hA hsw hr).mpr (Or.inr ⟨?_, ?_⟩)⟩))
    · rw [e]; exact hΛ _ (by decide)
    · rw [e, smul_pair_set_eq_iff]; decide
    · rw [e, smul_pair_set_eq_iff]; decide

  intro g hg
  obtain ⟨hgM2, hgΛ⟩ := mem_setStabIn.mp hg
  have hmem : ∀ x : Fin 7, x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 →
      π ⟨g, hgM2⟩ x = 3 ∨ π ⟨g, hgM2⟩ x = 4 ∨ π ⟨g, hgM2⟩ x = 5 ∨ π ⟨g, hgM2⟩ x = 6 := by
    intro x hx'
    have : π ⟨g, hgM2⟩ • x ∈ π ⟨g, hgM2⟩ • ({3, 4, 5, 6} : Set (Fin 7)) :=
      Set.smul_mem_smul_set (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hx')
    rw [hgΛ] at this
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Equiv.Perm.smul_def] using this
  obtain ⟨i, hi⟩ := exists_m23Word _ _ (hmem 5 (by decide)) (hmem 6 (by decide))
    (fun h => absurd ((π ⟨g, hgM2⟩).injective h) (by decide))
  have hiQ : m23Word i ∈ Q := m23Word_mem h1 h2 h3 i
  obtain ⟨h', hh'J, hh'⟩ := Subgroup.mem_map.mp hiQ
  have hh'J' : (h' : G) ∈ J := hh'J
  have hpair : m23Word i • ({5, 6} : Set (Fin 7)) = π ⟨g, hgM2⟩ • ({5, 6} : Set (Fin 7)) := by
    have e : π ⟨g, hgM2⟩ • ({5, 6} : Set (Fin 7)) = {π ⟨g, hgM2⟩ 5, π ⟨g, hgM2⟩ 6} := by
      rw [Set.smul_set_insert, Set.smul_set_singleton]
      rfl
    rw [e, smul_pair_set_eq_iff]
    exact hi
  have hk : (h' : G)⁻¹ * g ∈ m23I M2 π ⊓ m23Gx T M L H B D := by
    have hkM2 : (h' : G)⁻¹ * g ∈ M2 := M2.mul_mem (M2.inv_mem h'.2) hgM2
    refine Subgroup.mem_inf.mpr ⟨(m23I M2 π).mul_mem ((m23I M2 π).inv_mem (hJI hh'J')) hg,
      (mem_iff_of_inf_eq_setStabIn hA hkM2).mpr ?_⟩
    rw [show (⟨(h' : G)⁻¹ * g, hkM2⟩ : ↥M2) = h'⁻¹ * ⟨g, hgM2⟩ from rfl, map_mul, map_inv,
      mul_smul, ← hpair, hh', inv_smul_smul]
  have := J.mul_mem hh'J' (Subgroup.mem_sup_right hk)
  rwa [mul_inv_cancel_left] at this

theorem stmt5_2_10_of_lemmas_F4
    (hset : Stmt5_2_10_setting_F4) (h520 : Stmt5_2_17_20_F4)
    (h519 : Stmt5_2_19_F4) (h521 : Stmt5_2_21_F4) (haut : Stmt5_2_10_aut_F4) : Stmt5_2_10_F4 :=
  stmt5_2_10_of_F4 (stmt5_2_11_22_of_F4 hset h520 h519 h521 (stmt5_2_22_of_F4 h519) haut)

end CFSG.Quasithin.H13
