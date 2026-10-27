module

public import CFSG.ClassicalInvolution.Q3.TL3T2

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

@[expose] def invs (Ω : Set (Subgroup G)) (M : Subgroup G) : Set G :=
  {x | ∃ L : Subgroup G, MaxAdj (nbrAdj Ω) M L ∧ IsUniqueInvolution L x}

@[expose] def vM (Ω : Set (Subgroup G)) (M : Subgroup G) : Subgroup G :=
  Subgroup.closure (invs Ω M)

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

omit [Finite G] in
theorem ThinStd.eq_of_uniqueInvolution {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) {u : G}
    (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u) : L = L' := by
  obtain ⟨a, rfl⟩ := hS.trans L hL
  obtain ⟨b, rfl⟩ := hS.trans L' hL'
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hS.mem
  have ha := (hzK.conj a).eq hu
  have hb := (hzK.conj b).eq hu'
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
    refine hS.tight K hS.mem zK hzK (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc b⁻¹ * a * zK = b⁻¹ * (a * zK * a⁻¹) * a := by group
      _ = b⁻¹ * (b * zK * b⁻¹) * a := by rw [ha, hb]
      _ = zK * (b⁻¹ * a) := by group
  calc conjSub a K = conjSub b (conjSub (b⁻¹ * a) K) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b K := by rw [conjSub_eq_of_mem_normalizer hn]

variable {M : Subgroup G} (hth : ThinAtM Ω M) (hind : Indep Ω M) {z : G}
  (hz : IsUniqueInvolution M z)
include hth hind hz

theorem ThinStd.invs_comm : ∀ x ∈ invs Ω M, ∀ y ∈ invs Ω M, x * y = y * x := by
  rintro x ⟨L, hL, hx⟩ y ⟨L', hL', hy⟩
  exact hS.commute_inv hth hind hL hL' hz hx hy

theorem ThinStd.mem_vM_iff {x : G} : x ∈ vM Ω M ↔ x = 1 ∨ x ∈ invs Ω M := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Or.inr hx
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | hx
      · rw [one_mul]; exact hy
      rcases hy with rfl | hy
      · rw [mul_one]; exact Or.inr hx
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨L, -, hu⟩ := hx
        exact Or.inl hu.sq
      · right
        obtain ⟨L, hL, hu⟩ := hx
        obtain ⟨L', hL', hu'⟩ := hy
        have hne : L ≠ L' := by
          rintro rfl
          exact hxy (hu.eq hu')
        obtain ⟨g, -, hg, hgu⟩ := hS.exists_third hth hind hL hL' hne hz hu hu'
        exact ⟨_, hg, hgu⟩
    | inv x _ hx =>
      rcases hx with rfl | hx
      · exact Or.inl inv_one
      · obtain ⟨L, hL, hu⟩ := hx
        have : x⁻¹ = x := inv_eq_of_mul_eq_one_right hu.sq
        rw [this]
        exact Or.inr ⟨L, hL, hu⟩
  · rintro (rfl | hx)
    · exact (vM Ω M).one_mem
    · exact Subgroup.subset_closure hx

theorem ThinStd.vM_comm : ∀ x ∈ vM Ω M, ∀ y ∈ vM Ω M, x * y = y * x := by
  intro x hx y hy
  rcases (hS.mem_vM_iff hth hind hz).mp hx with rfl | hx'
  · simp
  rcases (hS.mem_vM_iff hth hind hz).mp hy with rfl | hy'
  · simp
  exact hS.invs_comm hth hind hz x hx' y hy'

omit [Finite G] hS hind in
theorem vM_le_Qz : vM Ω M ≤ Qz z := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨L, hL, hu⟩
  exact mem_Qz_of_maxAdj hth hL hz hu

theorem ThinStd.comm_vM {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) {u : G}
    (hu : IsUniqueInvolution L u) {v : G} (hv : v ∈ vM Ω M) {l : G} (hl : l ∈ L) :
    l * v * l⁻¹ * v⁻¹ = 1 ∨ l * v * l⁻¹ * v⁻¹ = u := by
  have huV : u ∈ vM Ω M := Subgroup.subset_closure ⟨L, hL, hu⟩
  exact hS.comm_mem_of_mem_Qz hth hL hz hu (vM_le_Qz hth hz hv)
    (hS.vM_comm hth hind hz v hv u huV) hl

theorem ThinStd.eq_of_centralizes {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) {u : G}
    (hu : IsUniqueInvolution L u) {v : G} (hv : v ∈ vM Ω M)
    (hc : ∀ l ∈ L, l * v = v * l) : v = 1 ∨ v = u := by
  rcases (hS.mem_vM_iff hth hind hz).mp hv with rfl | ⟨L', hL', hv'⟩
  · exact Or.inl rfl
  · by_cases hLL : L = L'
    · subst hLL
      exact Or.inr (hv'.eq hu)
    · exact absurd hc (hS.not_centralizes hind hL hL' hLL hv')

omit hth hind in
theorem ThinStd.conjSub_vM {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c (vM Ω M) = vM Ω M := by
  have key : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c (vM Ω M) ≤ vM Ω M := by
    intro c hc
    unfold vM
    rw [conjSub, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨L, hL, hu⟩, rfl⟩
    exact ⟨conjSub c L, hS.maxAdj_conj_of_mem hL hz hc, hu.conj c⟩
  apply le_antisymm (key c hc)
  have h1 := conjSub_mono (n := c) (key c⁻¹ ((Subgroup.centralizer ({z} : Set G)).inv_mem hc))
  rwa [conjSub_conjSub_inv] at h1

end CFSG.ClassicalInvolution.Q3.TC.Thin
