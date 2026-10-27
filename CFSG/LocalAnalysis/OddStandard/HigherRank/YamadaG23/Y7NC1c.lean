module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC1a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMe
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NXb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g g0 : G} {P U S F M U0 P0 : Subgroup G}

private lemma g0_mem_U0 (h1 : NtOne t g U S U0 P0 g0) : g0 ∈ U0 := by
  rw [h1.U0_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g0)

private lemma g0t_mem_conjSub_U0 (h1 : NtOne t g U S U0 P0 g0) :
    t * g0 * t⁻¹ ∈ conjSub t U0 :=
  (mem_conjSub_iff' t U0 _).mpr ⟨g0, g0_mem_U0 h1, rfl⟩

private lemma U_le_U0 (h1 : NtOne t g U S U0 P0 g0) : U ≤ U0 := by
  rw [h1.U0_eq]
  exact le_sup_left

private lemma U_le_P0 (h1 : NtOne t g U S U0 P0 g0) : U ≤ P0 :=
  (U_le_U0 h1).trans (by rw [← h1.direct.1]; exact le_sup_left)

private lemma conjSub_t_U_le_conjSub_U0 (h1 : NtOne t g U S U0 P0 g0) :
    conjSub t U ≤ conjSub t U0 :=
  Subgroup.map_mono (U_le_U0 h1)

private lemma conjSub_t_U_le_P0 (h1 : NtOne t g U S U0 P0 g0) : conjSub t U ≤ P0 :=
  (conjSub_t_U_le_conjSub_U0 h1).trans (by rw [← h1.direct.1]; exact le_sup_right)

private lemma zpowers_g0_le_P0 (h1 : NtOne t g U S U0 P0 g0) : zpowers g0 ≤ P0 :=
  (Subgroup.zpowers_le.mpr (g0_mem_U0 h1)).trans (by rw [← h1.direct.1]; exact le_sup_left)

private lemma zpowers_g0t_le_P0 (h1 : NtOne t g U S U0 P0 g0) :
    zpowers (t * g0 * t⁻¹) ≤ P0 :=
  (Subgroup.zpowers_le.mpr (g0t_mem_conjSub_U0 h1)).trans
    (by rw [← h1.direct.1]; exact le_sup_right)

private lemma g0_comm_g0t (h1 : NtOne t g U S U0 P0 g0) :
    g0 * (t * g0 * t⁻¹) = (t * g0 * t⁻¹) * g0 :=
  h1.direct.2.2 g0 (g0_mem_U0 h1) _ (g0t_mem_conjSub_U0 h1)

private lemma g0_sq' (h1 : NtOne t g U S U0 P0 g0) : g0 * g0 = 1 := by
  simpa [pow_two] using h1.g0_sq

private lemma g0t_sq' (h1 : NtOne t g U S U0 P0 g0) :
    (t * g0 * t⁻¹) * (t * g0 * t⁻¹) = 1 := by
  calc (t * g0 * t⁻¹) * (t * g0 * t⁻¹) = t * (g0 * g0) * t⁻¹ := by group
    _ = 1 := by rw [g0_sq' h1]; group

private lemma g0_mul_g (h1 : NtOne t g U S U0 P0 g0) : g0 * g = t * g0 * t⁻¹ := by
  rw [← h1.gg0]
  calc g0 * (g0 * (t * g0 * t⁻¹)) = (g0 * g0) * (t * g0 * t⁻¹) := by group
    _ = t * g0 * t⁻¹ := by rw [g0_sq' h1]; group

private lemma g_mul_g0 (h1 : NtOne t g U S U0 P0 g0) : g * g0 = t * g0 * t⁻¹ := by
  rw [← h1.gg0]
  calc (g0 * (t * g0 * t⁻¹)) * g0 = g0 * ((t * g0 * t⁻¹) * g0) := by group
    _ = g0 * (g0 * (t * g0 * t⁻¹)) := by rw [g0_comm_g0t h1]
    _ = (g0 * g0) * (t * g0 * t⁻¹) := by group
    _ = t * g0 * t⁻¹ := by rw [g0_sq' h1]; group

private lemma g_comm_g0 (h1 : NtOne t g U S U0 P0 g0) : g * g0 = g0 * g := by
  rw [g_mul_g0 h1, g0_mul_g h1]

private lemma g_mul_g0t (h1 : NtOne t g U S U0 P0 g0) : g * (t * g0 * t⁻¹) = g0 := by
  rw [← h1.gg0]
  calc (g0 * (t * g0 * t⁻¹)) * (t * g0 * t⁻¹)
      = g0 * ((t * g0 * t⁻¹) * (t * g0 * t⁻¹)) := by group
    _ = g0 := by rw [g0t_sq' h1]; group

private lemma g0t_mul_g (h1 : NtOne t g U S U0 P0 g0) : (t * g0 * t⁻¹) * g = g0 := by
  rw [← h1.gg0]
  calc (t * g0 * t⁻¹) * (g0 * (t * g0 * t⁻¹))
      = ((t * g0 * t⁻¹) * g0) * (t * g0 * t⁻¹) := by group
    _ = (g0 * (t * g0 * t⁻¹)) * (t * g0 * t⁻¹) := by rw [g0_comm_g0t h1]
    _ = g0 * ((t * g0 * t⁻¹) * (t * g0 * t⁻¹)) := by group
    _ = g0 := by rw [g0t_sq' h1]; group

private lemma g_comm_g0t (h1 : NtOne t g U S U0 P0 g0) :
    g * (t * g0 * t⁻¹) = (t * g0 * t⁻¹) * g := by
  rw [g_mul_g0t h1, g0t_mul_g h1]

private lemma P0_eq_gens (h1 : NtOne t g U S U0 P0 g0) :
    P0 = (U ⊔ zpowers g0) ⊔ (conjSub t U ⊔ zpowers (t * g0 * t⁻¹)) := by
  rw [← h1.direct.1, h1.U0_eq]
  simp only [conjSub, Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

private lemma commutator_mem_of_generators (h1 : NtOne t g U S U0 P0 g0) {D' : Subgroup G}
    {b : G} (hN : P0 ⊔ zpowers t ≤ normalizer (D' : Set G))
    (hU : ∀ x ∈ U, ⁅b, x⁆ ∈ D') (hg0 : ⁅b, g0⁆ ∈ D')
    (hUt : ∀ x ∈ conjSub t U, ⁅b, x⁆ ∈ D') (hg0t : ⁅b, t * g0 * t⁻¹⁆ ∈ D')
    (ht : ⁅b, t⁆ ∈ D') :
    ∀ x ∈ P0 ⊔ zpowers t, ⁅b, x⁆ ∈ D' := by
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ normalizer (D' : Set G) ∧ ⁅b, x⁆ ∈ D'}
      one_mem' := ⟨Subgroup.one_mem _, by rw [commutatorElement_one_right]; exact D'.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxN, hxC⟩ ⟨hyN, hyC⟩
        refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
        have hconj : x * ⁅b, y⁆ * x⁻¹ ∈ D' :=
          (Subgroup.mem_set_normalizer_iff.mp hxN ⁅b, y⁆).mp hyC
        rw [show ⁅b, x * y⁆ = ⁅b, x⁆ * (x * ⁅b, y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact D'.mul_mem hxC hconj
      inv_mem' := by
        rintro x ⟨hxN, hxC⟩
        refine ⟨Subgroup.inv_mem _ hxN, ?_⟩
        have hconj : x⁻¹ * ⁅b, x⁆⁻¹ * x ∈ D' :=
          (Subgroup.mem_set_normalizer_iff''.mp hxN ⁅b, x⁆⁻¹).mp (D'.inv_mem hxC)
        rw [show ⁅b, x⁻¹⁆ = x⁻¹ * ⁅b, x⁆⁻¹ * x by
          simp only [commutatorElement_def]; group]
        exact hconj }
  have hU_le : U ≤ T := fun x hx =>
    ⟨hN (Subgroup.mem_sup_left (U_le_P0 h1 hx)), hU x hx⟩
  have hUt_le : conjSub t U ≤ T := fun x hx =>
    ⟨hN (Subgroup.mem_sup_left (conjSub_t_U_le_P0 h1 hx)), hUt x hx⟩
  have hg0_mem : g0 ∈ T :=
    ⟨hN (Subgroup.mem_sup_left (zpowers_g0_le_P0 h1 (Subgroup.mem_zpowers g0))), hg0⟩
  have hg0t_mem : t * g0 * t⁻¹ ∈ T :=
    ⟨hN (Subgroup.mem_sup_left (zpowers_g0t_le_P0 h1 (Subgroup.mem_zpowers _))), hg0t⟩
  have ht_mem : t ∈ T := ⟨hN (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)), ht⟩
  have hjoin : (U ⊔ zpowers g0) ⊔ (conjSub t U ⊔ zpowers (t * g0 * t⁻¹)) ⊔ zpowers t ≤ T :=
    sup_le (sup_le (sup_le hU_le (Subgroup.zpowers_le.mpr hg0_mem))
      (sup_le hUt_le (Subgroup.zpowers_le.mpr hg0t_mem))) (Subgroup.zpowers_le.mpr ht_mem)
  intro x hx
  exact (hjoin (P0_eq_gens h1 ▸ hx)).2

theorem y7n_c1_g_comm_M (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    (hMn : P0 ⊔ zpowers t ≤ normalizer (M : Set G)) : ∀ x ∈ P0 ⊔ zpowers t, ⁅g, x⁆ ∈ M := by
  refine commutator_mem_of_generators h1 hMn ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact h.M_comm x (h.wr.le_left.1 hx)
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (g_comm_g0 h1)]
    exact M.one_mem
  · intro x hx
    exact h.M_comm x (h.wr.le_left.2 hx)
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (g_comm_g0t h1)]
    exact M.one_mem
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr h.tg.symm]
    exact M.one_mem

theorem y7n_c1_normalizes_D (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    (hMn : P0 ⊔ zpowers t ≤ normalizer (M : Set G)) :
    P0 ⊔ zpowers t ≤ normalizer ((M ⊔ zpowers g : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub x (M ⊔ zpowers g) = M ⊔ zpowers g
  have hxM : conjSub x M = M := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMn hx)
  have hgx : ⁅g, x⁆ ∈ M := y7n_c1_g_comm_M h h1 hMn x hx
  have hxg : x * g * x⁻¹ ∈ M ⊔ zpowers g := by
    have hxg' : ⁅x, g⁆ ∈ M := by
      rw [← commutatorElement_inv]
      exact M.inv_mem hgx
    rw [show x * g * x⁻¹ = ⁅x, g⁆ * g by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxg')
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hg_le : conjSub x (zpowers g) ≤ M ⊔ zpowers g := by
    rw [show conjSub x (zpowers g) = zpowers (x * g * x⁻¹) by
      simp only [conjSub, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply],
      Subgroup.zpowers_le]
    exact hxg
  have hmap : conjSub x (M ⊔ zpowers g) ≤ M ⊔ zpowers g := by
    calc conjSub x (M ⊔ zpowers g) = conjSub x M ⊔ conjSub x (zpowers g) := by
          simp only [conjSub, Subgroup.map_sup]
      _ ≤ M ⊔ zpowers g := sup_le ((le_of_eq hxM).trans le_sup_left) hg_le
  have hcard : Nat.card ↥(conjSub x (M ⊔ zpowers g)) = Nat.card ↥(M ⊔ zpowers g) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (K := M ⊔ zpowers g)
      (MulAut.conj x).injective
  exact Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)

theorem y7n_c1_comm_D (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    (hMn : P0 ⊔ zpowers t ≤ normalizer (M : Set G)) :
    ⁅(centEl U g ⊔ zpowers g0) ⊔ conjSub t (centEl U g ⊔ zpowers g0), P0 ⊔ zpowers t⁆ ≤
      M ⊔ zpowers g := by
  have hN : P0 ⊔ zpowers t ≤ normalizer ((M ⊔ zpowers g : Subgroup G) : Set G) :=
    y7n_c1_normalizes_D h h1 hMn
  have hFU_le_M : centEl U g ≤ M := by rw [y7n_M_eq h]; exact le_sup_left
  have hFU : ⁅centEl U g, P0 ⊔ zpowers t⁆ ≤ M ⊔ zpowers g := by
    rw [Subgroup.commutator_le]
    intro m hm x hx
    have hmM : m ∈ M := hFU_le_M hm
    have hxm : x * m⁻¹ * x⁻¹ ∈ M :=
      (Subgroup.mem_set_normalizer_iff.mp (hMn hx) m⁻¹).mp (M.inv_mem hmM)
    have hmem : ⁅m, x⁆ ∈ M := by
      simpa only [commutatorElement_def, mul_assoc] using M.mul_mem hmM hxm
    exact Subgroup.mem_sup_left hmem
  have hJ1_le_P1 : centEl U g ⊔ zpowers g0 ≤ P0 ⊔ zpowers t :=
    sup_le ((hFU_le_M.trans (y7n_M_le_P h)).trans ((y7n_c1_P_le h h1).trans le_sup_left))
      ((zpowers_g0_le_P0 h1).trans le_sup_left)
  have hg0_inv : g0⁻¹ = g0 := mul_eq_one_iff_inv_eq.mp (g0_sq' h1)
  have hg0_t : ⁅g0, t⁆ = g := by
    rw [commutatorElement_def, hg0_inv]
    simpa only [mul_assoc] using h1.gg0
  have hg0_U : ∀ x ∈ U, ⁅g0, x⁆ ∈ M ⊔ zpowers g := by
    intro x hx
    have hconj := y7n_c1_conj_g h h1 x (U_le_U0 h1 hx)
    have hgx : ⁅g, x⁆ ∈ M := h.M_comm x (h.wr.le_left.1 hx)
    have heq : ⁅g0, x⁆ = ⁅g, x⁆ := by
      rw [commutatorElement_def, commutatorElement_def, ← hconj]
    rw [heq]
    exact Subgroup.mem_sup_left hgx
  have hg0_Ut : ∀ x ∈ conjSub t U, ⁅g0, x⁆ ∈ M ⊔ zpowers g := by
    intro x hx
    have hcomm : g0 * x = x * g0 :=
      h1.direct.2.2 g0 (g0_mem_U0 h1) x (conjSub_t_U_le_conjSub_U0 h1 hx)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact Subgroup.mem_sup_left M.one_mem
  have hg0_self : ⁅g0, g0⁆ ∈ M ⊔ zpowers g := by
    rw [commutatorElement_self]
    exact Subgroup.mem_sup_left M.one_mem
  have hg0_g0t : ⁅g0, t * g0 * t⁻¹⁆ ∈ M ⊔ zpowers g := by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (g0_comm_g0t h1)]
    exact Subgroup.mem_sup_left M.one_mem
  have hg0_gen : ∀ x ∈ P0 ⊔ zpowers t, ⁅g0, x⁆ ∈ M ⊔ zpowers g :=
    commutator_mem_of_generators h1 hN hg0_U hg0_self hg0_Ut hg0_g0t
      (by rw [hg0_t]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hzg0 : ⁅zpowers g0, P0 ⊔ zpowers t⁆ ≤ M ⊔ zpowers g :=
    y7n_commutator_zpowers_le
      (hN (hJ1_le_P1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers g0)))) hg0_gen
  have hJ1_comm : ⁅centEl U g ⊔ zpowers g0, P0 ⊔ zpowers t⁆ ≤ M ⊔ zpowers g :=
    y7n_commutator_sup_le (hJ1_le_P1.trans hN) hFU hzg0
  have hconjD : conjSub t (M ⊔ zpowers g) = M ⊔ zpowers g := by
    rw [conjSub, Subgroup.map_sup]
    have hMmap : M.map (MulAut.conj t).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (hMn (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
    have hg_conj : t * g * t⁻¹ = g := by rw [h.tg]; group
    have hzt : (zpowers g).map (MulAut.conj t).toMonoidHom = zpowers g := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg_conj]
    rw [hMmap, hzt]
  have hPt : conjSub t (P0 ⊔ zpowers t) = P0 ⊔ zpowers t := by
    rw [conjSub, Subgroup.map_sup]
    have hP0map : P0.map (MulAut.conj t).toMonoidHom = P0 := (y7n_c1_wr h h1).conjSub_eq
    have hzt : (zpowers t).map (MulAut.conj t).toMonoidHom = zpowers t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
    rw [hP0map, hzt]
  have hJ1t_comm : ⁅conjSub t (centEl U g ⊔ zpowers g0), P0 ⊔ zpowers t⁆ ≤ M ⊔ zpowers g := by
    calc ⁅conjSub t (centEl U g ⊔ zpowers g0), P0 ⊔ zpowers t⁆
        = ⁅conjSub t (centEl U g ⊔ zpowers g0), conjSub t (P0 ⊔ zpowers t)⁆ := by rw [hPt]
      _ = conjSub t ⁅centEl U g ⊔ zpowers g0, P0 ⊔ zpowers t⁆ :=
            (y7n_conjSub_commutator t _ _).symm
      _ ≤ conjSub t (M ⊔ zpowers g) := Subgroup.map_mono hJ1_comm
      _ = M ⊔ zpowers g := hconjD
  have hJ1_le_U0 : centEl U g ⊔ zpowers g0 ≤ U0 := (y7n_c1_J1 h h1).1
  have hJt_le_P1 : conjSub t (centEl U g ⊔ zpowers g0) ≤ P0 ⊔ zpowers t :=
    ((Subgroup.map_mono hJ1_le_U0).trans
      (by rw [← h1.direct.1]; exact le_sup_right)).trans le_sup_left
  exact y7n_commutator_sup_le (sup_le hJ1_le_P1 hJt_le_P1 |>.trans hN) hJ1_comm hJ1t_comm

end CFSG.OddStandard.HigherRank.YamadaG23
