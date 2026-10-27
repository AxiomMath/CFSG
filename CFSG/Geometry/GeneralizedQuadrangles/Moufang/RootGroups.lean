module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic
public import CFSG.Quasithin.Recognition.Stroth.RootGroupRegular

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
open scoped Pointwise

universe u v

section BasicIdentities

variable {V : Type u} {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V]

theorem rootGroup_comm (a b c : V) :
    rootGroup H Γ a b c = rootGroup H Γ c b a := by
  ext g
  simp only [mem_rootGroup]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h3, h2, h1⟩

variable [GraphAction H Γ]

theorem rootGroup_map_conj (g : H) (a b c : V) :
    (rootGroup H Γ a b c).map (MulAut.conj g).toMonoidHom =
      rootGroup H Γ (g • a) (g • b) (g • c) := by
  have hsmul : ∀ x : V, g • Γ.neighborSet x = Γ.neighborSet (g • x) := by
    intro x
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_neighborSet, mem_neighborSet]
    constructor
    · intro hw
      simpa using (GraphAction.adj_smul g x (g⁻¹ • w)).mpr hw
    · intro hw
      exact (GraphAction.adj_smul g x (g⁻¹ • w)).mp (by simpa using hw)
  have hA : (fixingSubgroup H (Γ.neighborSet a)).map (MulAut.conj g).toMonoidHom =
      fixingSubgroup H (Γ.neighborSet (g • a)) := by
    rw [← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
      (g := g) (s := Γ.neighborSet a), hsmul a]
  have hB : (fixingSubgroup H (Γ.neighborSet b)).map (MulAut.conj g).toMonoidHom =
      fixingSubgroup H (Γ.neighborSet (g • b)) := by
    rw [← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
      (g := g) (s := Γ.neighborSet b), hsmul b]
  have hC : (fixingSubgroup H (Γ.neighborSet c)).map (MulAut.conj g).toMonoidHom =
      fixingSubgroup H (Γ.neighborSet (g • c)) := by
    rw [← SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
      (g := g) (s := Γ.neighborSet c), hsmul c]
  rw [rootGroup, rootGroup,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hA, hB, hC]

end BasicIdentities

section PathBridge

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]

theorem rootGroup_eq_pathRootGroup (p : GPath Γ 4) :
    rootGroup H Γ (p 1) (p 2) (p 3) = pathRootGroup H Γ p := by
  ext g
  rw [mem_rootGroup, mem_pathRootGroup]
  constructor
  · rintro ⟨h1, h2, h3⟩ i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact (mem_fixingSubgroup_iff H).mp h1 v hv
    · exact (mem_fixingSubgroup_iff H).mp h2 v hv
    · exact (mem_fixingSubgroup_iff H).mp h3 v hv
  · intro h
    exact ⟨(mem_fixingSubgroup_iff H).mpr (fun v hv => h 1 (by omega) (by omega) v hv),
      (mem_fixingSubgroup_iff H).mpr (fun v hv => h 2 (by omega) (by omega) v hv),
      (mem_fixingSubgroup_iff H).mpr (fun v hv => h 3 (by omega) (by omega) v hv)⟩

end PathBridge

section Rigidity

variable {V : Type u} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {H : Type v} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem eq_one_of_mem_rootGroup_of_fix_opposite (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (p : GPath Γ 4) (hp : p.NoBack)
    {g : H} (hg : g ∈ rootGroup H Γ (p 1) (p 2) (p 3)) {w : V}
    (hw : Γ.dist (p 2) w = 4) (hgw : g • w = w) : g = 1 := by
  classical
  have hw3 : Γ.dist w (p 3) = 3 := by
    have hadj : Γ.Adj (p 3) (p 2) := (p.adj 2 (by omega)).symm
    have h42 : Γ.dist w (p 2) = 4 := by rw [SimpleGraph.dist_comm]; exact hw
    rcases hP.dist_adj hadj w with h | h
    · omega
    · have := hP.dist_le (by norm_num) w (p 3)
      omega
  let b := proj hP hw3
  have hb_adj : Γ.Adj (p 3) b := proj_adj hP hw3
  have hb_dist : Γ.dist w b = 2 := proj_dist hP hw3
  have hb_ne : b ≠ p 2 := by
    intro h
    rw [h, SimpleGraph.dist_comm, hw] at hb_dist
    omega
  let q : GPath Γ 4 := (p.take 3 (by omega)).snoc b (by simpa using hb_adj)
  have hq3 : q 3 = p 3 := by simp [q]
  have hq4 : q 4 = b := by simp [q]
  have hq : q.NoBack := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simpa [q] using hp 0 (by omega)
    · simpa [q] using hp 1 (by omega)
    · rw [hq4]
      simpa [q] using hb_ne.symm
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hg).1
  have hg2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hg).2.1
  have hg3 : g ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := ((mem_rootGroup H).mp hg).2.2
  have hfix : ∀ i, 1 ≤ i → i ≤ 3 → ∀ v, Γ.Adj (q i) v → g • v = v := by
    intro i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact (mem_fixingSubgroup_iff H).mp hg1 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg2 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg3 v (by simpa [q] using hv)
  have hbw : Γ.dist b w = 2 := by rw [SimpleGraph.dist_comm]; exact hb_dist
  let c := commonNeighbor hP hbw
  have hcb : Γ.Adj b c := commonNeighbor_adj_left hP hbw
  have hcw : Γ.Adj w c := commonNeighbor_adj_right hP hbw
  have hgb : g • b = b := (mem_fixingSubgroup_iff H).mp hg3 b hb_adj
  have hgc : g • c = c := by
    have h1 : Γ.Adj b (g • c) := by
      have h' := (GraphAction.adj_smul g b c).mpr hcb
      rwa [hgb] at h'
    have h2 : Γ.Adj w (g • c) := by
      have h' := (GraphAction.adj_smul g w c).mpr hcw
      rwa [hgw] at h'
    have h' := eq_commonNeighbor hP hbw h1 h2
    simpa [c] using h'
  have hc_ne : c ≠ p 3 := by
    intro hc3
    have h1 : Γ.Adj w (p 3) := hc3 ▸ hcw
    have h2 : Γ.dist w (p 3) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
    omega
  have hpg : IsGenPolygon Γ 4 := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hTh : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hall : ∀ v : V, g • v = v :=
    hpg.smul_eq_of_fix_root (by omega) hTh q hq hfix (by simpa [hq4] using hcb)
      (by simpa [hq3] using hc_ne) hgc
  refine eq_of_smul_eq_smul (m₁ := g) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  exact hall v

theorem eq_one_of_mem_rootGroup_of_fix_opposite_end (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (p : GPath Γ 4) (hp : p.NoBack)
    {g : H} (hg : g ∈ rootGroup H Γ (p 1) (p 2) (p 3)) {w : V}
    (hw : Γ.dist (p 1) w = 4) (hgw : g • w = w) : g = 1 := by
  classical
  have hw0 : Γ.dist w (p 0) = 3 := by
    have hadj : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
    have h41 : Γ.dist w (p 1) = 4 := by rw [SimpleGraph.dist_comm]; exact hw
    rcases hP.dist_adj hadj w with h | h
    · omega
    · have := hP.dist_le (by norm_num) w (p 0)
      omega
  let c := proj hP hw0
  have hc_adj : Γ.Adj (p 0) c := proj_adj hP hw0
  have hc_dist : Γ.dist w c = 2 := proj_dist hP hw0
  have hc_ne : c ≠ p 1 := by
    intro h
    rw [h, SimpleGraph.dist_comm, hw] at hc_dist
    omega
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hg).1
  have hg2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hg).2.1
  have hg3 : g ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := ((mem_rootGroup H).mp hg).2.2
  have hgp0 : g • p 0 = p 0 :=
    (mem_fixingSubgroup_iff H).mp hg1 (p 0) (by simpa using (p.adj 0 (by omega)).symm)
  have hgc : g • c = c := by
    have h1 : Γ.Adj (p 0) (g • c) := by
      have h' := (GraphAction.adj_smul g (p 0) c).mpr hc_adj
      rwa [hgp0] at h'
    have h2 : Γ.dist w (g • c) = 2 := by
      rw [← hgw, GPath.dist_smul hP.connected g w c]
      exact hc_dist
    have h' := eq_proj hP hw0 h1 h2
    simpa [c] using h'
  let q : GPath Γ 4 := p.rev
  have hq3 : q 3 = p 1 := by simp [q]
  have hq4 : q 4 = p 0 := by simp [q]
  have hq : q.NoBack := hp.rev
  have hfix : ∀ i, 1 ≤ i → i ≤ 3 → ∀ v, Γ.Adj (q i) v → g • v = v := by
    intro i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact (mem_fixingSubgroup_iff H).mp hg3 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg2 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg1 v (by simpa [q] using hv)
  have hpg : IsGenPolygon Γ 4 := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hTh : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hall : ∀ v : V, g • v = v :=
    hpg.smul_eq_of_fix_root (by omega) hTh q hq hfix (by simpa [hq4] using hc_adj)
      (by simpa [hq3] using hc_ne) hgc
  refine eq_of_smul_eq_smul (m₁ := g) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  exact hall v

end Rigidity

section Card

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem card_rootGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (p : GPath Γ 4) (hp : p.NoBack) :
    Nat.card (rootGroup H Γ (p 1) (p 2) (p 3)) = Γ.degree (p 4) - 1 := by
  rw [rootGroup_eq_pathRootGroup (H := H) p]
  have h := card_pathRootGroup_add_one (D := H) (n := 4) (by omega) hP hT hM p hp
  omega

end Card

section Consecutive

variable {V : Type u} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {H : Type v} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem commute_of_mem_rootGroup_consecutive (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (p : GPath Γ 3) (hp : p.NoBack)
    {g h : H} (hg : g ∈ rootGroup H Γ (p 0) (p 1) (p 2))
    (hh : h ∈ rootGroup H Γ (p 1) (p 2) (p 3)) : Commute g h := by
  classical
  have hg0 : g ∈ fixingSubgroup H (Γ.neighborSet (p 0)) := ((mem_rootGroup H).mp hg).1
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hg).2.1
  have hg2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hg).2.2
  have hh1 : h ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hh).1
  have hh2 : h ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hh).2.1
  have hh3 : h ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := ((mem_rootGroup H).mp hh).2.2
  have hhp0 : h • p 0 = p 0 :=
    (mem_fixingSubgroup_iff H).mp hh1 (p 0) (by simpa using (p.adj 0 (by omega)).symm)
  have hhp1 : h • p 1 = p 1 :=
    (mem_fixingSubgroup_iff H).mp hh2 (p 1) (by simpa using (p.adj 1 (by omega)).symm)
  have hhp2 : h • p 2 = p 2 :=
    (mem_fixingSubgroup_iff H).mp hh1 (p 2) (by simpa using p.adj 1 (by omega))
  have hgp1 : g • p 1 = p 1 :=
    (mem_fixingSubgroup_iff H).mp hg0 (p 1) (by simpa using p.adj 0 (by omega))
  have hgp2 : g • p 2 = p 2 :=
    (mem_fixingSubgroup_iff H).mp hg1 (p 2) (by simpa using p.adj 1 (by omega))
  have hgp3 : g • p 3 = p 3 :=
    (mem_fixingSubgroup_iff H).mp hg2 (p 3) (by simpa using p.adj 2 (by omega))
  have hmap1 : (rootGroup H Γ (p 0) (p 1) (p 2)).map (MulAut.conj h).toMonoidHom =
      rootGroup H Γ (p 0) (p 1) (p 2) := by
    rw [rootGroup_map_conj, hhp0, hhp1, hhp2]
  have hmap2 : (rootGroup H Γ (p 1) (p 2) (p 3)).map (MulAut.conj g).toMonoidHom =
      rootGroup H Γ (p 1) (p 2) (p 3) := by
    rw [rootGroup_map_conj, hgp1, hgp2, hgp3]
  have hk1 : g * h * g⁻¹ * h⁻¹ ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
    have hmem : MulAut.conj h (g⁻¹) ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
      rw [← hmap1]
      exact Subgroup.mem_map.mpr ⟨g⁻¹, Subgroup.inv_mem _ hg, rfl⟩
    have hconj : h * g⁻¹ * h⁻¹ ∈ rootGroup H Γ (p 0) (p 1) (p 2) := by
      simpa [MulAut.conj_apply] using hmem
    simpa only [mul_assoc] using Subgroup.mul_mem _ hg hconj
  have hk2 : g * h * g⁻¹ * h⁻¹ ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
    have hmem : MulAut.conj g h ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
      rw [← hmap2]
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hconj : g * h * g⁻¹ ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
      simpa [MulAut.conj_apply] using hmem
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hh)
  have hkfix1 := (mem_rootGroup H).mp hk1
  have hkfix2 := (mem_rootGroup H).mp hk2
  have hfix0 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) := hkfix1.1
  have hfix1 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 1)) :=
    hkfix1.2.1
  have hfix2 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 2)) :=
    hkfix1.2.2
  have hfix3 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) :=
    hkfix2.2.2
  have hex : ∀ v w : V, Γ.Adj v w → ∃ c : V, Γ.Adj v c ∧ c ≠ w := by
    intro v w hv
    have h3 : 3 ≤ (Γ.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hT v
    have hmem : w ∈ Γ.neighborFinset v := by simpa using hv
    have h2 : 2 ≤ ((Γ.neighborFinset v).erase w).card := by
      rw [Finset.card_erase_of_mem hmem]
      omega
    obtain ⟨c, hc⟩ :=
      Finset.card_pos.mp (by omega : 0 < ((Γ.neighborFinset v).erase w).card)
    exact ⟨c, by simpa using Finset.mem_of_mem_erase hc, Finset.ne_of_mem_erase hc⟩
  obtain ⟨z, hz, hzne⟩ := hex (p 0) (p 1) (p.adj 0 (by omega))
  obtain ⟨y, hy, hyne⟩ := hex (p 3) (p 2) ((p.adj 2 (by omega)).symm)
  let q : GPath Γ 4 := GPath.cons z p hz.symm
  have hq : q.NoBack := GPath.noBack_cons z p hz.symm hp hzne
  have hq3 : q 3 = p 2 := by simp [q]
  have hq4 : q 4 = p 3 := by simp [q]
  have hky : (g * h * g⁻¹ * h⁻¹) • y = y :=
    (mem_fixingSubgroup_iff H).mp hfix3 y hy
  have hpg : IsGenPolygon Γ 4 := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hTh : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hfixΓ : ∀ i, 1 ≤ i → i ≤ 4 - 1 → ∀ v, Γ.Adj (q i) v →
      (g * h * g⁻¹ * h⁻¹) • v = v := by
    intro i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact (mem_fixingSubgroup_iff H).mp hfix0 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hfix1 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hfix2 v (by simpa [q] using hv)
  have hall : ∀ v : V, (g * h * g⁻¹ * h⁻¹) • v = v :=
    hpg.smul_eq_of_fix_root (by omega) hTh q hq hfixΓ (by simpa [hq4] using hy)
      (by simpa [hq3] using hyne) hky
  have hk : g * h * g⁻¹ * h⁻¹ = 1 := by
    refine eq_of_smul_eq_smul (m₁ := g * h * g⁻¹ * h⁻¹) (m₂ := 1) (fun v : V => ?_)
    rw [one_smul]
    exact hall v
  rw [commute_iff_eq]
  calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
    _ = h * g := by rw [hk, one_mul]

end Consecutive

section Commutator

variable {V : Type u} {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V]
  [GraphAction H Γ]

theorem commutatorElement_mem_rootGroup (p : GPath Γ 4) {g h : H}
    (hg : g ∈ rootGroup H Γ (p 0) (p 1) (p 2))
    (hh : h ∈ rootGroup H Γ (p 2) (p 3) (p 4)) :
    g * h * g⁻¹ * h⁻¹ ∈ rootGroup H Γ (p 1) (p 2) (p 3) := by
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hg).2.1
  have hg2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hg).2.2
  have hh2 : h ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hh).1
  have hh3 : h ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := ((mem_rootGroup H).mp hh).2.1
  have hhp1 : h • p 1 = p 1 :=
    (mem_fixingSubgroup_iff H).mp hh2 (p 1) (by simpa using (p.adj 1 (by omega)).symm)
  have hgp3 : g • p 3 = p 3 :=
    (mem_fixingSubgroup_iff H).mp hg2 (p 3) (by simpa using p.adj 2 (by omega))
  have hstab1 : h • Γ.neighborSet (p 1) = Γ.neighborSet (p 1) := by
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_neighborSet, mem_neighborSet]
    constructor
    · intro hw
      simpa [hhp1] using (GraphAction.adj_smul h (p 1) (h⁻¹ • w)).mpr hw
    · intro hw
      exact (GraphAction.adj_smul h (p 1) (h⁻¹ • w)).mp (by simpa [hhp1] using hw)
  have hstab3 : g • Γ.neighborSet (p 3) = Γ.neighborSet (p 3) := by
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_neighborSet, mem_neighborSet]
    constructor
    · intro hw
      simpa [hgp3] using (GraphAction.adj_smul g (p 3) (g⁻¹ • w)).mpr hw
    · intro hw
      exact (GraphAction.adj_smul g (p 3) (g⁻¹ • w)).mp (by simpa [hgp3] using hw)
  have hk1 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := by
    have hmem : MulAut.conj h (g⁻¹) ∈ fixingSubgroup H (Γ.neighborSet (p 1)) :=
      Set.conj_mem_fixingSubgroup hstab1 (Subgroup.inv_mem _ hg1)
    have hconj : h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := by
      simpa [MulAut.conj_apply] using hmem
    simpa only [mul_assoc] using Subgroup.mul_mem _ hg1 hconj
  have hk2 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg2 hh2)
      (Subgroup.inv_mem _ hg2)) (Subgroup.inv_mem _ hh2)
  have hk3 : g * h * g⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
    have hmem : MulAut.conj g h ∈ fixingSubgroup H (Γ.neighborSet (p 3)) :=
      Set.conj_mem_fixingSubgroup hstab3 hh3
    have hconj : g * h * g⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
      simpa [MulAut.conj_apply] using hmem
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hh3)
  exact (mem_rootGroup H).mpr ⟨hk1, hk2, hk3⟩

end Commutator

end CFSG.Geometry.GeneralizedQuadrangles
