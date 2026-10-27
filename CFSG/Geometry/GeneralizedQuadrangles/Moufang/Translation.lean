module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Symmetries
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Transitive
public import CFSG.Geometry.GeneralizedQuadrangles.LinearSpace

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin
open CFSG.Quasithin.Stroth

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [FaithfulSMul H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

@[expose] def translationGroup (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    (p : V) : Subgroup H :=
  Subgroup.closure {g | ∃ L, Γ.Adj p L ∧ g ∈ symmetryGroup H Γ L}

@[expose] def translationGroupMinus (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    (p L₀ : V) : Subgroup H :=
  Subgroup.closure {g | ∃ L, Γ.Adj p L ∧ L ≠ L₀ ∧ g ∈ symmetryGroup H Γ L}

theorem symmetryGroup_le_translationGroup {p L : V} (hpL : Γ.Adj p L) :
    symmetryGroup H Γ L ≤ translationGroup H Γ p := by
  intro g hg
  exact Subgroup.subset_closure ⟨L, hpL, hg⟩

theorem symmetryGroup_le_translationGroupMinus {p L₀ L : V} (hpL : Γ.Adj p L)
    (hL : L ≠ L₀) : symmetryGroup H Γ L ≤ translationGroupMinus H Γ p L₀ := by
  intro g hg
  exact Subgroup.subset_closure ⟨L, hpL, hL, hg⟩

theorem translationGroupMinus_le_translationGroup (p L₀ : V) :
    translationGroupMinus H Γ p L₀ ≤ translationGroup H Γ p := by
  refine (Subgroup.closure_le (translationGroup H Γ p)).mpr ?_
  rintro g ⟨L, hpL, -, hg⟩
  exact Subgroup.subset_closure ⟨L, hpL, hg⟩

theorem symmetryGroup_le_whorlGroup_of_adj (hP : IsGeneralizedPolygon Γ 4) {p L : V}
    (hpL : Γ.Adj p L) : symmetryGroup H Γ L ≤ whorlGroup H Γ p := by
  intro g hg
  rw [mem_whorlGroup, mem_fixingSubgroup_iff]
  intro M hpM
  rw [mem_symmetryGroup, mem_fixingSubgroup_iff] at hg
  refine hg M ?_
  rw [mem_perpSet]
  by_cases hML : M = L
  · rw [hML]
    simp
  · exact Nat.le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hpL.symm hpM (Ne.symm hML))

theorem translationGroup_le_whorlGroup (hP : IsGeneralizedPolygon Γ 4) (p : V) :
    translationGroup H Γ p ≤ whorlGroup H Γ p := by
  refine (Subgroup.closure_le (whorlGroup H Γ p)).mpr ?_
  rintro g ⟨L, hpL, hg⟩
  exact symmetryGroup_le_whorlGroup_of_adj hP hpL hg

theorem commute_of_mem_symmetryGroup_of_adj (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {p L M : V} (hpL : Γ.Adj p L) (hpM : Γ.Adj p M) (hLM : L ≠ M)
    {g h : H} (hg : g ∈ symmetryGroup H Γ L) (hh : h ∈ symmetryGroup H Γ M) :
    Commute g h :=
  commute_of_mem_symmetryGroup hP hT
    (dist_eq_two_of_adj_of_adj_of_ne hP hpL.symm hpM hLM) hg hh

theorem commute_of_mem_symmetryGroup_of_mem_translationGroupMinus
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {p L₀ : V} (hpL₀ : Γ.Adj p L₀)
    {g h : H} (hg : g ∈ symmetryGroup H Γ L₀)
    (hh : h ∈ translationGroupMinus H Γ p L₀) : Commute g h := by
  classical
  refine Subgroup.closure_induction (p := fun x _ => Commute g x) ?_ ?_ ?_ ?_ hh
  · rintro x ⟨L, hpL, hL₀, hx⟩
    exact commute_of_mem_symmetryGroup_of_adj hP hT hpL₀ hpL (Ne.symm hL₀) hg hx
  · exact Commute.one_right g
  · intro x y _ _ hx hy
    exact hx.mul_right hy
  · intro x _ hx
    exact hx.inv_right

theorem generator_set_eq_union (p L₀ : V) (hpL₀ : Γ.Adj p L₀) :
    {g : H | ∃ L, Γ.Adj p L ∧ g ∈ symmetryGroup H Γ L} =
      {g : H | ∃ L, Γ.Adj p L ∧ L ≠ L₀ ∧ g ∈ symmetryGroup H Γ L} ∪
        (symmetryGroup H Γ L₀ : Set H) := by
  ext g
  constructor
  · rintro ⟨L, hpL, hg⟩
    by_cases hL : L = L₀
    · right
      rwa [hL] at hg
    · left
      exact ⟨L, hpL, hL, hg⟩
  · rintro (⟨L, hpL, -, hg⟩ | hg)
    · exact ⟨L, hpL, hg⟩
    · exact ⟨L₀, hpL₀, hg⟩

theorem translationGroup_eq_sup (p L₀ : V) (hpL₀ : Γ.Adj p L₀) :
    translationGroup H Γ p = symmetryGroup H Γ L₀ ⊔ translationGroupMinus H Γ p L₀ := by
  rw [translationGroup, translationGroupMinus, generator_set_eq_union p L₀ hpL₀]
  simp only [Subgroup.closure_union, Subgroup.closure_eq]
  exact sup_comm _ _

theorem exists_smul_eq_of_mem_symmetryGroup_of_adj (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (hM : MoufangCondition H Γ 4) {a L N : V}
    (hL : IsRegularVertex Γ L) (haL : Γ.Adj L a)
    (haN : Γ.Adj N a) (hLN : L ≠ N) {x x' : V} (hxN : Γ.Adj N x)
    (hx'N : Γ.Adj N x') (hxa : x ≠ a) (hx'a : x' ≠ a) :
    ∃ g : H, g ∈ symmetryGroup H Γ L ∧ g • x = x' := by
  classical
  obtain ⟨b, hLb, hba, -⟩ := exists_adj_ne_two hT L a a
  obtain ⟨q₀, hbq₀, hq₀L, -⟩ := exists_adj_ne_two hT b L L
  have hsym : rootGroup H Γ b L a = symmetryGroup H Γ L :=
    rootGroup_eq_symmetryGroup hP hT hL hLb haL hba
  let r : GPath Γ 4 :=
    { toFun := fun i => if i = 0 then q₀ else if i = 1 then b else if i = 2 then L
        else if i = 3 then a else N
      adj := fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
        · simpa using hbq₀.symm
        · simpa using hLb.symm
        · simpa using haL
        · simpa using haN.symm
      tail := fun i hi => by
        have h0 : i ≠ 0 := by omega
        have h1 : i ≠ 1 := by omega
        have h2 : i ≠ 2 := by omega
        have h3 : i ≠ 3 := by omega
        simp [h0, h1, h2, h3, hq₀L, hba, hLN] }
  have hr0 : r 0 = q₀ := by simp [r]
  have hr1 : r 1 = b := by simp [r]
  have hr2 : r 2 = L := by simp [r]
  have hr3 : r 3 = a := by simp [r]
  have hr4 : r 4 = N := by simp [r]
  have hr : r.NoBack := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [hr0, hr2]; exact hq₀L
    · rw [hr1, hr3]; exact hba
    · rw [hr2, hr4]; exact hLN
  obtain ⟨g, hfix, hgx⟩ := hM r hr x x' (by simpa [hr4] using hxN)
    (by simpa [hr4] using hx'N) (by simpa [hr3] using hxa)
    (by simpa [hr3] using hx'a)
  have hg : g ∈ rootGroup H Γ b L a := by
    rw [mem_rootGroup]
    exact ⟨(mem_fixingSubgroup_iff H).mpr (fun w hw => hfix 1 (by omega) (by omega) w
        (by simpa [hr1] using hw)),
      (mem_fixingSubgroup_iff H).mpr (fun w hw => hfix 2 (by omega) (by omega) w
        (by simpa [hr2] using hw)),
      (mem_fixingSubgroup_iff H).mpr (fun w hw => hfix 3 (by omega) (by omega) w
        (by simpa [hr3] using hw))⟩
  exact ⟨g, by rwa [← hsym], hgx⟩

theorem exists_smul_eq_of_mem_symmetryGroup_of_meet (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (hM : MoufangCondition H Γ 4) {c : Γ.Coloring (Fin 2)}
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L) {p L N a y u : V}
    (hp : c p = 0) (hpL : Γ.Adj p L) (haL : Γ.Adj L a) (haN : Γ.Adj N a)
    (hyN : Γ.Adj N y) (huN : Γ.Adj N u) (hy : Γ.dist p y = 4)
    (hu : Γ.dist p u = 4) :
    ∃ g : H, g ∈ symmetryGroup H Γ L ∧ g • y = u := by
  classical
  have hcL : c L = 1 := by
    have hne := c.valid hpL
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c L) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hLN : L ≠ N := by
    intro h
    have hyL : Γ.Adj y L := h.symm ▸ hyN.symm
    have h3 := dist_eq_three_of_adj_of_dist_eq_four hP hy hpL
    have h1 : Γ.dist y L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyL
    omega
  have ha_ne_p : a ≠ p := by
    intro h
    have hpN : Γ.Adj N p := h ▸ haN
    have hle : Γ.dist p y ≤ 2 := by
      have h1 : Γ.dist p N = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpN.symm
      have h2 : Γ.dist N y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyN
      have htri := hP.connected.dist_triangle (u := p) (v := N) (w := y)
      omega
    omega
  have hpa : Γ.dist p a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL haL (Ne.symm ha_ne_p)
  have hya : y ≠ a := by
    intro h
    rw [h] at hy
    omega
  have hua : u ≠ a := by
    intro h
    rw [h] at hu
    omega
  exact exists_smul_eq_of_mem_symmetryGroup_of_adj hP hT hM (hreg L hcL) haL haN hLN hyN huN
    hya hua

theorem dist_eq_four_of_not_mem_perpSet (hP : IsGeneralizedPolygon Γ 4) {p y u : V}
    (hy : Γ.dist p y = 4) (hyu : Γ.dist y u = 2) (hu : u ∉ perpSet Γ p) :
    Γ.dist p u = 4 := by
  obtain ⟨c⟩ := hP.isBipartite
  have hle : Γ.dist p u ≤ 4 := hP.dist_le (by norm_num) p u
  have hgt : 2 < Γ.dist p u := by
    by_contra h
    exact hu (by rw [mem_perpSet]; omega)
  have hcu : c u = c y := ((hP.eq_iff_even_dist c y u).2 (by rw [hyu]; norm_num)).symm
  have hcy : c y = c p := ((hP.eq_iff_even_dist c p y).2 (by rw [hy]; norm_num)).symm
  have heven : Even (Γ.dist p u) := (hP.eq_iff_even_dist c p u).1 (by rw [← hcy, ← hcu])
  obtain ⟨k, hk⟩ := heven
  omega

theorem not_exists_adj_projectionLine_of_mem_trace (hP : IsGeneralizedPolygon Γ 4)
    {p L₀ x y y' u : V} (hpL₀ : Γ.Adj p L₀) (hxL₀ : Γ.Adj L₀ x) (hxp : x ≠ p)
    (hy : Γ.dist p y = 4) (hx : Γ.dist y x = 2) (hx' : Γ.dist y' x = 2)
    (hMM' : commonNeighbor hP hx ≠ commonNeighbor hP hx')
    (hyu : Γ.dist y u = 2) (hy'u : Γ.dist y' u = 2) (hu : u ∉ perpSet Γ p) :
    ¬ ∃ a, Γ.Adj L₀ a ∧ Γ.Adj (commonNeighbor hP hyu) a := by
  classical
  rintro ⟨a, haL₀, haN⟩
  let N : V := commonNeighbor hP hyu
  have hyN : Γ.Adj y N := commonNeighbor_adj_left hP hyu
  have huN : Γ.Adj u N := commonNeighbor_adj_right hP hyu
  have hyL₀ : Γ.dist y L₀ = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy hpL₀
  have ha_ne_y : a ≠ y := by
    intro hay
    rw [hay] at haL₀
    have h1 : Γ.dist y L₀ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haL₀.symm
    omega
  have hya : Γ.dist y a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyN haN (Ne.symm ha_ne_y)
  have hax : a = x :=
    (eq_proj hP hyL₀ haL₀ hya).trans (eq_proj hP hyL₀ hxL₀ hx).symm
  have hxN : Γ.Adj x N := by
    rw [← hax]
    exact haN.symm
  have hN_eq : N = commonNeighbor hP hx :=
    eq_commonNeighbor hP hx hyN hxN
  have hMne : ¬ Γ.Adj y' N := by
    intro hy'N
    have hN' : N = commonNeighbor hP hx' := eq_commonNeighbor hP hx' hy'N hxN
    exact hMM' (hN_eq.symm.trans hN')
  obtain ⟨c⟩ := hP.isBipartite
  have hcy'x : c y' = c x := (hP.eq_iff_even_dist c y' x).2 (by rw [hx']; norm_num)
  have hcxM : c x ≠ c N := c.valid hxN
  have hcol : c y' ≠ c N := by
    rw [hcy'x]
    exact hcxM
  have hdist : Γ.dist y' N = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hMne hcol
  have hux : u = x :=
    (eq_proj hP hdist huN.symm hy'u).trans
      (eq_proj hP hdist hxN.symm hx').symm
  have hxperp : x ∈ perpSet Γ p := by
    rw [mem_perpSet]
    exact Nat.le_of_eq
      (dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm hxp))
  exact hu (hux ▸ hxperp)

theorem exists_smul_mem_translationGroupMinus_of_trace
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L₀ x y₁ y₂ u : V} (hp : c p = 0) (hpL₀ : Γ.Adj p L₀)
    (hxL₀ : Γ.Adj L₀ x) (hxp : x ≠ p)
    (hy₁ : Γ.dist p y₁ = 4) (hy₂ : Γ.dist p y₂ = 4)
    (hx₁ : Γ.dist y₁ x = 2) (hx₂ : Γ.dist y₂ x = 2)
    (hM₁₂ : commonNeighbor hP hx₁ ≠ commonNeighbor hP hx₂)
    (hu₁ : Γ.dist y₁ u = 2) (hu₂ : Γ.dist y₂ u = 2) (hu : u ∉ perpSet Γ p) :
    ∃ g ∈ translationGroupMinus H Γ p L₀, g • y₁ = y₂ := by
  classical
  have hcolor : ∀ {L : V}, Γ.Adj p L → c L = 1 := by
    intro L hpL
    have hne := c.valid hpL
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c L) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hu4 : Γ.dist p u = 4 := dist_eq_four_of_not_mem_perpSet hP hy₁ hu₁ hu
  let N₁ : V := commonNeighbor hP hu₁
  have hy₁N₁ : Γ.Adj y₁ N₁ := commonNeighbor_adj_left hP hu₁
  have huN₁ : Γ.Adj u N₁ := commonNeighbor_adj_right hP hu₁
  have hpN₁ : Γ.dist p N₁ = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hy₁) hy₁N₁
  let a₁ : V := proj hP hpN₁
  have ha₁N₁ : Γ.Adj N₁ a₁ := proj_adj hP hpN₁
  have hpa₁ : Γ.dist p a₁ = 2 := proj_dist hP hpN₁
  let L₁ : V := commonNeighbor hP hpa₁
  have hpL₁ : Γ.Adj p L₁ := commonNeighbor_adj_left hP hpa₁
  have ha₁L₁ : Γ.Adj L₁ a₁ := (commonNeighbor_adj_right hP hpa₁).symm
  have hL₁ne : L₁ ≠ L₀ := by
    intro h
    exact not_exists_adj_projectionLine_of_mem_trace hP hpL₀ hxL₀ hxp hy₁ hx₁ hx₂ hM₁₂
      hu₁ hu₂ hu ⟨a₁, h ▸ ha₁L₁, ha₁N₁⟩
  have hy₁a₁ : y₁ ≠ a₁ := by
    intro h
    rw [h] at hy₁
    omega
  have hua₁ : u ≠ a₁ := by
    intro h
    exact hu (by rw [h, mem_perpSet]; omega)
  obtain ⟨g₁, hg₁S, hg₁⟩ :=
    exists_smul_eq_of_mem_symmetryGroup_of_meet hP hT hM hreg hp hpL₁ ha₁L₁ ha₁N₁
      hy₁N₁.symm huN₁.symm hy₁ hu4
  let N₂ : V := commonNeighbor hP hu₂
  have hy₂N₂ : Γ.Adj y₂ N₂ := commonNeighbor_adj_left hP hu₂
  have huN₂ : Γ.Adj u N₂ := commonNeighbor_adj_right hP hu₂
  have hpN₂ : Γ.dist p N₂ = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hy₂) hy₂N₂
  let a₂ : V := proj hP hpN₂
  have ha₂N₂ : Γ.Adj N₂ a₂ := proj_adj hP hpN₂
  have hpa₂ : Γ.dist p a₂ = 2 := proj_dist hP hpN₂
  let L₂ : V := commonNeighbor hP hpa₂
  have hpL₂ : Γ.Adj p L₂ := commonNeighbor_adj_left hP hpa₂
  have ha₂L₂ : Γ.Adj L₂ a₂ := (commonNeighbor_adj_right hP hpa₂).symm
  have hL₂ne : L₂ ≠ L₀ := by
    intro h
    exact not_exists_adj_projectionLine_of_mem_trace hP hpL₀ hxL₀ hxp hy₂ hx₂ hx₁
      (Ne.symm hM₁₂) hu₂ hu₁ hu ⟨a₂, h ▸ ha₂L₂, ha₂N₂⟩
  have hy₂a₂ : y₂ ≠ a₂ := by
    intro h
    rw [h] at hy₂
    omega
  have hua₂ : u ≠ a₂ := by
    intro h
    exact hu (by rw [h, mem_perpSet]; omega)
  obtain ⟨g₂, hg₂S, hg₂⟩ :=
    exists_smul_eq_of_mem_symmetryGroup_of_meet hP hT hM hreg hp hpL₂ ha₂L₂ ha₂N₂
      hy₂N₂.symm huN₂.symm hy₂ hu4
  have hg₁G : g₁ ∈ translationGroupMinus H Γ p L₀ :=
    symmetryGroup_le_translationGroupMinus hpL₁ hL₁ne hg₁S
  have hg₂G : g₂ ∈ translationGroupMinus H Γ p L₀ :=
    symmetryGroup_le_translationGroupMinus hpL₂ hL₂ne hg₂S
  refine ⟨g₂⁻¹ * g₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₂G) hg₁G, ?_⟩
  calc
    (g₂⁻¹ * g₁) • y₁ = g₂⁻¹ • (g₁ • y₁) := mul_smul g₂⁻¹ g₁ y₁
    _ = g₂⁻¹ • u := by rw [hg₁]
    _ = y₂ := by rw [← hg₂]; exact inv_smul_smul g₂ y₂

theorem exists_mem_traceSet_not_mem_perpSet (hP : IsGeneralizedPolygon Γ 4)
    {p y z : V} (hy : Γ.dist p y = 4) (hz : Γ.dist p z = 4) (hyz : Γ.dist y z = 4)
    (hzspan : z ∉ spanSet Γ p y) :
    ∃ u, u ∈ traceSet Γ y z ∧ u ∉ perpSet Γ p := by
  classical
  by_contra h
  push Not at h
  have hsub : traceSet Γ y z ⊆ traceSet Γ p y := by
    intro u hu
    refine ⟨?_, hu.1⟩
    have hup : u ∈ perpSet Γ p := h u hu
    rw [mem_perpSet] at hup
    obtain ⟨c⟩ := hP.isBipartite
    have hcu : c u = c y :=
      ((hP.eq_iff_even_dist c y u).2 (by rw [hu.1]; norm_num)).symm
    have hcy : c y = c p := ((hP.eq_iff_even_dist c p y).2 (by rw [hy]; norm_num)).symm
    have heven : Even (Γ.dist p u) := (hP.eq_iff_even_dist c p u).1 (by rw [← hcy, ← hcu])
    have hne0 : Γ.dist p u ≠ 0 := by
      intro h0
      have h0' : Γ.dist u p = 0 := by rwa [SimpleGraph.dist_comm]
      have hup' : u = p := (hP.connected.dist_eq_zero_iff).mp h0'
      rw [hup'] at hu
      have h2 : Γ.dist p y = 2 := by rw [SimpleGraph.dist_comm]; exact hu.1
      omega
    have hcases : Γ.dist p u = 1 ∨ Γ.dist p u = 2 := by omega
    rcases hcases with h1 | h2
    · obtain ⟨k, hk⟩ := heven
      omega
    · exact h2
  have htrace : traceSet Γ y z = traceSet Γ p y := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [ncard_trace hP hyz, ncard_trace hP hy,
      hP.degree_eq_of_dist_eq (by norm_num) hy]
  have hspan : spanSet Γ p y = spanSet Γ y z := by
    unfold spanSet
    rw [htrace]
  exact hzspan (by rw [hspan]; exact right_mem_spanSet hyz)

theorem exists_adj_ne_three (v a b c : V) (h4 : 4 ≤ Γ.degree v) :
    ∃ u, Γ.Adj v u ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c := by
  classical
  have h4card : 4 ≤ (Γ.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    exact h4
  let A : Finset V := ((Γ.neighborFinset v).erase a).erase b |>.erase c
  have hpos : 0 < A.card := by
    have h1 := Finset.pred_card_le_card_erase (s := Γ.neighborFinset v) (a := a)
    have h2 := Finset.pred_card_le_card_erase
      (s := (Γ.neighborFinset v).erase a) (a := b)
    have h3 := Finset.pred_card_le_card_erase
      (s := ((Γ.neighborFinset v).erase a).erase b) (a := c)
    dsimp only [A]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  dsimp only [A] at hu
  simp only [Finset.mem_erase, mem_neighborFinset] at hu
  exact ⟨u, hu.2.2.2, hu.2.2.1, hu.2.1, hu.1⟩

theorem exists_adj_notMem_of_ncard_le_one (hT : IsThick Γ) {x M : V} (hxM : Γ.Adj M x)
    {S : Set V} (hS : (S ∩ Γ.neighborSet M).ncard ≤ 1) :
    ∃ y, Γ.Adj M y ∧ y ≠ x ∧ y ∉ S := by
  classical
  have h3 : 3 ≤ (Γ.neighborFinset M).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT M
  let A : Finset V := (Γ.neighborFinset M).erase x
  have hAcard : A.card = (Γ.neighborFinset M).card - 1 := by
    rw [Finset.card_erase_of_mem]
    simpa using hxM
  have hA2 : 2 ≤ A.card := by omega
  have hfilter : (A.filter fun y => y ∈ S).card ≤ 1 := by
    have hsub : ((Γ.neighborFinset M).erase x).filter (fun y => y ∈ S) ⊆
        (S ∩ Γ.neighborSet M).toFinset := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset] at hy
      obtain ⟨⟨-, hyM⟩, hyS⟩ := hy
      exact Set.mem_toFinset.mpr ⟨hyS, hyM⟩
    calc
      (A.filter fun y => y ∈ S).card ≤ ((S ∩ Γ.neighborSet M).toFinset).card :=
        Finset.card_le_card hsub
      _ = (S ∩ Γ.neighborSet M).ncard := (Set.ncard_eq_toFinset_card' _).symm
      _ ≤ 1 := hS
  obtain ⟨y, hyAmem, hyS⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := A.filter fun y => y ∈ S) (t := A) (by omega)
  have hyA : Γ.Adj M y ∧ y ≠ x := by
    have h := hyAmem
    dsimp only [A] at h
    simp only [Finset.mem_erase, mem_neighborFinset] at h
    exact ⟨h.2, h.1⟩
  refine ⟨y, hyA.1, hyA.2, ?_⟩
  intro hy
  exact hyS (Finset.mem_filter.mpr ⟨hyAmem, hy⟩)

theorem traceSet_eq_traceSet_of_subset_perp (hP : IsGeneralizedPolygon Γ 4) {p y z : V}
    (hy : Γ.dist p y = 4) (hyz : Γ.dist y z = 4)
    (h : ∀ u, u ∈ traceSet Γ y z → u ∈ perpSet Γ p) :
    traceSet Γ y z = traceSet Γ p y := by
  classical
  have hsub : traceSet Γ y z ⊆ traceSet Γ p y := by
    intro u hu
    refine ⟨?_, hu.1⟩
    have hup : u ∈ perpSet Γ p := h u hu
    rw [mem_perpSet] at hup
    obtain ⟨c⟩ := hP.isBipartite
    have hcu : c u = c y :=
      ((hP.eq_iff_even_dist c y u).2 (by rw [hu.1]; norm_num)).symm
    have hcy : c y = c p := ((hP.eq_iff_even_dist c p y).2 (by rw [hy]; norm_num)).symm
    have heven : Even (Γ.dist p u) := (hP.eq_iff_even_dist c p u).1 (by rw [← hcy, ← hcu])
    have hne0 : Γ.dist p u ≠ 0 := by
      intro h0
      have h0' : Γ.dist u p = 0 := by rwa [SimpleGraph.dist_comm]
      have hup' : u = p := (hP.connected.dist_eq_zero_iff).mp h0'
      rw [hup'] at hu
      have h2 : Γ.dist p y = 2 := by rw [SimpleGraph.dist_comm]; exact hu.1
      omega
    have hcases : Γ.dist p u = 1 ∨ Γ.dist p u = 2 := by omega
    rcases hcases with h1 | h2
    · obtain ⟨k, hk⟩ := heven
      omega
    · exact h2
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [ncard_trace hP hyz, ncard_trace hP hy,
    hP.degree_eq_of_dist_eq (by norm_num) hy]

theorem exists_smul_mem_translationGroupMinus_of_distinct
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L₀ x y₁ y₂ : V} (hp : c p = 0) (hpL₀ : Γ.Adj p L₀)
    (hxL₀ : Γ.Adj L₀ x) (hxp : x ≠ p) (h3 : 3 ≤ t)
    (hy₁ : Γ.dist p y₁ = 4) (hy₂ : Γ.dist p y₂ = 4)
    (hx₁ : Γ.dist y₁ x = 2) (hx₂ : Γ.dist y₂ x = 2)
    (hM₁₂ : commonNeighbor hP hx₁ ≠ commonNeighbor hP hx₂) :
    ∃ g ∈ translationGroupMinus H Γ p L₀, g • y₁ = y₂ := by
  classical
  have h1 : Γ.dist x y₁ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₁
  have h2 : Γ.dist x y₂ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₂
  have hcomm1 : commonNeighbor hP h1 = commonNeighbor hP hx₁ :=
    (existsUnique_commonNeighbor hP h1).unique
      ⟨commonNeighbor_adj_left hP h1, commonNeighbor_adj_right hP h1⟩
      ⟨commonNeighbor_adj_right hP hx₁, commonNeighbor_adj_left hP hx₁⟩
  have hcomm2 : commonNeighbor hP h2 = commonNeighbor hP hx₂ :=
    (existsUnique_commonNeighbor hP h2).unique
      ⟨commonNeighbor_adj_left hP h2, commonNeighbor_adj_right hP h2⟩
      ⟨commonNeighbor_adj_right hP hx₂, commonNeighbor_adj_left hP hx₂⟩
  have hM' : commonNeighbor hP h1 ≠ commonNeighbor hP h2 := by
    rw [hcomm1, hcomm2]
    exact hM₁₂
  have h12 : Γ.dist y₁ y₂ = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP h1 h2 hM'
  by_cases htr : ∃ u, u ∈ traceSet Γ y₁ y₂ ∧ u ∉ perpSet Γ p
  · obtain ⟨u, hu, hup⟩ := htr
    exact exists_smul_mem_translationGroupMinus_of_trace hP hT hM hdeg hreg hp hpL₀ hxL₀ hxp
      hy₁ hy₂ hx₁ hx₂ hM₁₂ hu.1 hu.2 hup
  · push Not at htr
    have htrace₁ : traceSet Γ y₁ y₂ = traceSet Γ p y₁ :=
      traceSet_eq_traceSet_of_subset_perp hP hy₁ h12 htr
    have htrace₂ : traceSet Γ y₁ y₂ = traceSet Γ p y₂ := by
      have hsym : traceSet Γ y₁ y₂ = traceSet Γ y₂ y₁ := by
        ext u
        simp only [traceSet, Set.mem_setOf_eq, and_comm]
      rw [hsym]
      exact traceSet_eq_traceSet_of_subset_perp hP hy₂
        (by rw [SimpleGraph.dist_comm]; exact h12)
        (fun u hu => htr u (by rwa [hsym]))
    have hspan₁ : spanSet Γ p y₁ = spanSet Γ y₁ y₂ := by
      unfold spanSet
      rw [htrace₁]
    have hspan₂ : spanSet Γ p y₂ = spanSet Γ y₁ y₂ := by
      unfold spanSet
      rw [htrace₂]
    have hcx : c x = 0 := by
      have hd : Γ.dist x p = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm hxp)
      have hcp : c x = c p := (hP.eq_iff_even_dist c x p).2 (by rw [hd]; norm_num)
      rw [hcp]
      exact hp
    have hxdeg : 4 ≤ Γ.degree x := by
      rw [hdeg x, if_pos hcx]
      omega
    obtain ⟨M₃, hxM₃, hM₃L₀, hM₃M₁, hM₃M₂⟩ :=
      exists_adj_ne_three x L₀ (commonNeighbor hP hx₁) (commonNeighbor hP hx₂) hxdeg
    have hle : (spanSet Γ y₁ y₂ ∩ Γ.neighborSet M₃).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h12 M₃
    obtain ⟨y₃, hy₃M₃, hy₃x, hy₃span⟩ :=
      exists_adj_notMem_of_ncard_le_one (x := x) (M := M₃) hT hxM₃.symm hle
    have hx₃ : Γ.dist y₃ x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hy₃M₃.symm hxM₃.symm hy₃x
    have h3x : Γ.dist x y₃ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₃
    have hcomm3 : commonNeighbor hP h3x = commonNeighbor hP hx₃ :=
      (existsUnique_commonNeighbor hP h3x).unique
        ⟨commonNeighbor_adj_left hP h3x, commonNeighbor_adj_right hP h3x⟩
        ⟨commonNeighbor_adj_right hP hx₃, commonNeighbor_adj_left hP hx₃⟩
    have hpx : Γ.dist x p = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm hxp)
    have hMx : commonNeighbor hP hpx = L₀ :=
      (eq_commonNeighbor hP hpx hxL₀.symm hpL₀).symm
    have hM₃ : commonNeighbor hP hx₃ = M₃ :=
      (eq_commonNeighbor hP hx₃ hy₃M₃.symm hxM₃).symm
    have hp₃ : Γ.dist p y₃ = 4 :=
      dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hpx h3x
        (by rw [hMx, hcomm3, hM₃]; exact Ne.symm hM₃L₀)
    have h₁₃ : Γ.dist y₁ y₃ = 4 :=
      dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP h1 h3x
        (by rw [hcomm1, hcomm3, hM₃]; exact Ne.symm hM₃M₁)
    have h₂₃ : Γ.dist y₂ y₃ = 4 :=
      dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP h2 h3x
        (by rw [hcomm2, hcomm3, hM₃]; exact Ne.symm hM₃M₂)
    obtain ⟨u₁, hu₁, hup₁⟩ :=
      exists_mem_traceSet_not_mem_perpSet hP hy₁ hp₃ h₁₃ (by rw [hspan₁]; exact hy₃span)
    obtain ⟨u₂, hu₂, hup₂⟩ :=
      exists_mem_traceSet_not_mem_perpSet hP hy₂ hp₃ h₂₃ (by rw [hspan₂]; exact hy₃span)
    obtain ⟨g₁, hg₁G, hg₁⟩ :=
      exists_smul_mem_translationGroupMinus_of_trace hP hT hM hdeg hreg hp hpL₀ hxL₀ hxp
        hy₁ hp₃ hx₁ hx₃ (by rw [hM₃]; exact Ne.symm hM₃M₁) hu₁.1 hu₁.2 hup₁
    obtain ⟨g₂, hg₂G, hg₂⟩ :=
      exists_smul_mem_translationGroupMinus_of_trace hP hT hM hdeg hreg hp hpL₀ hxL₀ hxp
        hy₂ hp₃ hx₂ hx₃ (by rw [hM₃]; exact Ne.symm hM₃M₂) hu₂.1 hu₂.2 hup₂
    refine ⟨g₂⁻¹ * g₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₂G) hg₁G, ?_⟩
    calc
      (g₂⁻¹ * g₁) • y₁ = g₂⁻¹ • (g₁ • y₁) := mul_smul g₂⁻¹ g₁ y₁
      _ = g₂⁻¹ • y₃ := by rw [hg₁]
      _ = y₂ := by rw [← hg₂]; exact inv_smul_smul g₂ y₂

theorem exists_smul_mem_translationGroupMinus_of_same_projection
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L₀ x y₁ y₂ : V} (hp : c p = 0) (hpL₀ : Γ.Adj p L₀)
    (hxL₀ : Γ.Adj L₀ x) (hxp : x ≠ p) (h3 : 3 ≤ t)
    (hy₁ : Γ.dist p y₁ = 4) (hy₂ : Γ.dist p y₂ = 4)
    (hx₁ : Γ.dist y₁ x = 2) (hx₂ : Γ.dist y₂ x = 2) :
    ∃ g ∈ translationGroupMinus H Γ p L₀, g • y₁ = y₂ := by
  classical
  by_cases hM₁₂ : commonNeighbor hP hx₁ = commonNeighbor hP hx₂
  ·
    obtain ⟨M₃, hxM₃, hM₃L₀, hM₃M₁⟩ :=
      exists_adj_ne_two hT x L₀ (commonNeighbor hP hx₁)
    obtain ⟨y₃, hy₃M₃, hy₃x, -⟩ := exists_adj_ne_two hT M₃ x x
    have hx₃ : Γ.dist y₃ x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hy₃M₃.symm hxM₃.symm hy₃x
    have h3x : Γ.dist x y₃ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₃
    have hcomm3 : commonNeighbor hP h3x = commonNeighbor hP hx₃ :=
      (existsUnique_commonNeighbor hP h3x).unique
        ⟨commonNeighbor_adj_left hP h3x, commonNeighbor_adj_right hP h3x⟩
        ⟨commonNeighbor_adj_right hP hx₃, commonNeighbor_adj_left hP hx₃⟩
    have hpx : Γ.dist x p = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm hxp)
    have hMx : commonNeighbor hP hpx = L₀ :=
      (eq_commonNeighbor hP hpx hxL₀.symm hpL₀).symm
    have hM₃ : commonNeighbor hP hx₃ = M₃ :=
      (eq_commonNeighbor hP hx₃ hy₃M₃.symm hxM₃).symm
    have hp₃ : Γ.dist p y₃ = 4 :=
      dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hpx h3x
        (by rw [hMx, hcomm3, hM₃]; exact Ne.symm hM₃L₀)
    have hM₃M₂ : M₃ ≠ commonNeighbor hP hx₂ := by
      rw [← hM₁₂]
      exact hM₃M₁
    obtain ⟨g₁, hg₁G, hg₁⟩ :=
      exists_smul_mem_translationGroupMinus_of_distinct hP hT hM hdeg hreg hp hpL₀ hxL₀ hxp
        h3 hy₁ hp₃ hx₁ hx₃ (by rw [hM₃]; exact Ne.symm hM₃M₁)
    obtain ⟨g₂, hg₂G, hg₂⟩ :=
      exists_smul_mem_translationGroupMinus_of_distinct hP hT hM hdeg hreg hp hpL₀ hxL₀ hxp
        h3 hp₃ hy₂ hx₃ hx₂ (by rw [hM₃]; exact hM₃M₂)
    refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂G hg₁G, ?_⟩
    calc
      (g₂ * g₁) • y₁ = g₂ • (g₁ • y₁) := mul_smul g₂ g₁ y₁
      _ = g₂ • y₃ := by rw [hg₁]
      _ = y₂ := hg₂
  · exact exists_smul_mem_translationGroupMinus_of_distinct hP hT hM hdeg hreg hp hpL₀ hxL₀
      hxp h3 hy₁ hy₂ hx₁ hx₂ hM₁₂

theorem exists_smul_mem_translationGroupMinus_of_dist_eq_four
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L₀ : V} (hp : c p = 0) (hpL₀ : Γ.Adj p L₀) (h3 : 3 ≤ t)
    {y₁ y₂ : V} (hy₁ : Γ.dist p y₁ = 4) (hy₂ : Γ.dist p y₂ = 4) :
    ∃ g ∈ translationGroupMinus H Γ p L₀, g • y₁ = y₂ := by
  classical
  obtain ⟨L₁, hpL₁, hL₁L₀, -⟩ := exists_adj_ne_two hT p L₀ L₀
  have hcL₁ : c L₁ = 1 := by
    have hne := c.valid hpL₁
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c L₁) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hdist₁ : Γ.dist y₁ L₀ = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy₁ hpL₀
  have hdist₂ : Γ.dist y₂ L₀ = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy₂ hpL₀
  let x₁ : V := proj hP hdist₁
  let x₂ : V := proj hP hdist₂
  have hx₁L₀ : Γ.Adj L₀ x₁ := proj_adj hP hdist₁
  have hx₂L₀ : Γ.Adj L₀ x₂ := proj_adj hP hdist₂
  have hx₁ : Γ.dist y₁ x₁ = 2 := proj_dist hP hdist₁
  have hx₂ : Γ.dist y₂ x₂ = 2 := proj_dist hP hdist₂
  have hx₁p : x₁ ≠ p := by
    intro h
    rw [h] at hx₁
    have h2 : Γ.dist p y₁ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₁
    omega
  have hx₂p : x₂ ≠ p := by
    intro h
    rw [h] at hx₂
    have h2 : Γ.dist p y₂ = 2 := by rw [SimpleGraph.dist_comm]; exact hx₂
    omega
  obtain ⟨g₁, hg₁S, hg₁x⟩ :=
    exists_smul_eq_of_mem_symmetryGroup_of_adj hP hT hM (hreg L₁ hcL₁) hpL₁.symm hpL₀.symm
      hL₁L₀ hx₁L₀ hx₂L₀ hx₁p hx₂p
  have hg₁p : g₁ • p = p := by
    have hpL₁' : p ∈ perpSet Γ L₁ := by
      rw [mem_perpSet, SimpleGraph.dist_eq_one_iff_adj.mpr hpL₁.symm]
      norm_num
    exact (mem_fixingSubgroup_iff H).mp hg₁S p hpL₁'
  have hy₁' : Γ.dist p (g₁ • y₁) = 4 := by
    rw [← hg₁p, GPath.dist_smul hP.connected g₁ p y₁]
    exact hy₁
  have hL₀fix : g₁ • L₀ = L₀ := by
    have hL₀perp : L₀ ∈ perpSet Γ L₁ := by
      rw [mem_perpSet]
      have h2 : Γ.dist L₁ L₀ = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_adj_of_adj_of_ne (x := L₀) (y := L₁) (L := p) hP hpL₀.symm
          hpL₁ (Ne.symm hL₁L₀)
      exact Nat.le_of_eq h2
    exact (mem_fixingSubgroup_iff H).mp hg₁S L₀ hL₀perp
  have hdist₁' : Γ.dist (g₁ • y₁) L₀ = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP hy₁' hpL₀
  have hx₁' : Γ.dist (g₁ • y₁) x₂ = 2 := by
    have hdist : Γ.dist (g₁ • y₁) (g₁ • x₁) = 2 := by
      rw [GPath.dist_smul hP.connected g₁ y₁ x₁]
      exact hx₁
    rwa [hg₁x] at hdist
  have hx₁'L₀ : Γ.Adj L₀ x₂ := hx₂L₀
  have hproj : x₂ = proj hP hdist₁' := by
    have hadj : Γ.Adj L₀ (g₁ • x₁) := by
      have h := (GraphAction.adj_smul g₁ L₀ x₁).mpr hx₁L₀
      rwa [hL₀fix] at h
    have hdist : Γ.dist (g₁ • y₁) (g₁ • x₁) = 2 := by
      rw [GPath.dist_smul hP.connected g₁ y₁ x₁]
      exact hx₁
    have h := eq_proj hP hdist₁' hadj hdist
    rwa [hg₁x] at h
  obtain ⟨g₂, hg₂G, hg₂⟩ :=
    exists_smul_mem_translationGroupMinus_of_same_projection hP hT hM hdeg hreg hp hpL₀
      hx₂L₀ hx₂p h3 hy₁' hy₂ hx₁' hx₂
  have hg₁G : g₁ ∈ translationGroupMinus H Γ p L₀ :=
    symmetryGroup_le_translationGroupMinus hpL₁ hL₁L₀ hg₁S
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂G hg₁G, ?_⟩
  calc
    (g₂ * g₁) • y₁ = g₂ • (g₁ • y₁) := mul_smul g₂ g₁ y₁
    _ = y₂ := hg₂

