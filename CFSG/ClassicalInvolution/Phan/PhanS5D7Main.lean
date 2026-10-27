module

public import CFSG.ClassicalInvolution.Phan.PhanS5D6Common
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

variable {M}

theorem bf_conicPt_self {e f w : Vec K} {s : K} (hee : bf M e e = 0) (hff : bf M f f = 0)
    (hef : bf M e f = 1) (hwe : bf M w e = 0) (hwf : bf M w f = 0)
    (hs2 : 2 * s + bf M w w = 0) (μ : K) :
    bf M (conicPt f w (s • e) μ) (conicPt f w (s • e) μ) = 0 := by
  have hfe : bf M f e = 1 := by rw [bf_comm, hef]
  have hfw : bf M f w = 0 := by rw [bf_comm, hwf]
  have hew : bf M e w = 0 := by rw [bf_comm, hwe]
  simp only [conicPt, bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe,
    hwe, hwf, hfw, hew]
  linear_combination μ ^ 2 * hs2

theorem bf_conicPt_orth {e f w u : Vec K} {s : K} (he : bf M e u = 0) (hf : bf M f u = 0)
    (hw : bf M w u = 0) (μ : K) : bf M (conicPt f w (s • e) μ) u = 0 := by
  simp only [conicPt, bf_add_left, bf_smul_left, he, hf, hw]
  ring

theorem exists_common_neighbour [Finite K] (hq : 5 ≤ M.q) {a b : Vec K} (ha : IsFF M a)
    (hb : IsFF M b) : ∃ c : Vec K, IsFF M c ∧ Col M c a ∧ Col M c b := by
  obtain ⟨e, f, w, H⟩ := exists_efw ha b
  have h2 := M.two_ne
  have hQ0 : bf M w w ≠ 0 := H.hyp.ww
  obtain ⟨s, hs2, hs0⟩ : ∃ s : K, 2 * s + bf M w w = 0 ∧ s ≠ 0 := by
    refine ⟨-(bf M w w / 2), ?_, neg_ne_zero.mpr (div_ne_zero hQ0 h2)⟩
    field_simp
    ring
  have w1 : ∃ i j : Fin 3, her M (cs f w (s • e) i) (cs f w (s • e) j) ≠ 0 :=
    exists_cs_ne_zero (sesq_her M) hs0 (exists_her_ne_zero ha H.hyp)
  have w2 : ∃ i j : Fin 3, gramForm M b (cs f w (s • e) i) (cs f w (s • e) j) ≠ 0 := by
    refine exists_cs_ne_zero (sesq_gramForm M b) hs0 ?_
    have hr : her M b b ≠ 0 := hb.2
    have key : ∀ x y : Vec K, her M (projB M b x) (projB M b y) ≠ 0 → gramForm M b x y ≠ 0 := by
      intro x y h
      rw [← her_projB hb x y]
      exact mul_ne_zero hr h
    rcases exists_her_ne_zero hb (hypTriple_projB hb H) with h | h | h | h | h | h | h | h | h
    · exact Or.inl (key _ _ h)
    · exact Or.inr (Or.inl (key _ _ h))
    · exact Or.inr (Or.inr (Or.inl (key _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ _ h))))))))
  have hcard : 4 * M.q + 4 < Nat.card K := by
    rw [M.card_K]
    nlinarith
  obtain ⟨μ, hμ1, hμ2⟩ := exists_mu_ne_zero (by omega) hcard (sesq_her M) (sesq_gramForm M b) w1 w2
  have hcc : bf M (conicPt f w (s • e) μ) (conicPt f w (s • e) μ) = 0 :=
    bf_conicPt_self H.hyp.ee H.hyp.ff H.hyp.ef H.hyp.we H.hyp.wf hs2 μ
  have hca : bf M (conicPt f w (s • e) μ) a = 0 :=
    bf_conicPt_orth H.hyp.e_c H.hyp.f_c H.hyp.w_c μ
  have hcsa : bf M (conicPt f w (s • e) μ) (tauV M a) = 0 :=
    bf_conicPt_orth H.hyp.e_sc H.hyp.f_sc H.hyp.w_sc μ
  have hcb : bf M (conicPt f w (s • e) μ) b = 0 := bf_conicPt_orth H.e_b H.f_b H.w_b μ
  have hher_ca : her M (conicPt f w (s • e) μ) a = 0 := hcsa
  have hher_ac : her M a (conicPt f w (s • e) μ) = 0 := by
    rw [her_conj_symm, hher_ca, map_zero]
  refine ⟨conicPt f w (s • e) μ, ⟨hcc, hμ1⟩, ⟨hca, ?_⟩, ⟨hcb, ?_⟩⟩
  · simp only [gram, hher_ca, hher_ac, mul_zero, sub_zero]
    exact mul_ne_zero hμ1 ha.2
  · rw [← gramForm_self]
    exact hμ2

theorem isFF_ev (M : Model K) : IsFF M (ev (.inl 0) : Vec K) := by
  have h1 : tauV M (ev (.inl 0) : Vec K) = ev (.inr (.inl 0)) := by
    funext s
    rcases s with i | i | u <;> simp [tauV, ev, Pi.single_apply]
  refine ⟨?_, ?_⟩
  · rw [bf_ev_inl]
    simp [ev]
  · unfold her
    rw [h1, bf_ev_inr]
    simp [ev]

theorem diamTwo_of_model_five {K : Type} [Field K] [Finite K] (M : Model K) (hq : 5 ≤ M.q) :
    DiamTwo M := by
  have common : ∀ x y : FFPt M, ∃ z : FFPt M, (ffGraph M).Adj x z ∧ (ffGraph M).Adj z y := by
    intro x y
    obtain ⟨v, hv, rfl⟩ := FFPt.exists_vec M x
    obtain ⟨w, hw, rfl⟩ := FFPt.exists_vec M y
    obtain ⟨c, hc, hcv, hcw⟩ := exists_common_neighbour hq hv hw
    exact ⟨FFPt.mk M hc, (ffGraph_adj_mk M hv hc).2 (Col.symm M hcv),
      (ffGraph_adj_mk M hc hw).2 hcw⟩
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff]
    refine ⟨fun x y => ?_, ⟨FFPt.mk M (isFF_ev M)⟩⟩
    obtain ⟨z, hxz, hzy⟩ := common x y
    exact hxz.reachable.trans hzy.reachable
  · rw [SimpleGraph.ediam_le_iff]
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp
    · obtain ⟨z, hxz, hzy⟩ := common x y
      calc (ffGraph M).edist x y ≤ (ffGraph M).edist x z + (ffGraph M).edist z y :=
            SimpleGraph.edist_triangle
        _ = 1 + 1 := by
            rw [SimpleGraph.edist_eq_one_iff_adj.2 hxz, SimpleGraph.edist_eq_one_iff_adj.2 hzy]
        _ = 2 := by norm_num

theorem diamTwo_of_model {K : Type} [Field K] [Finite K] (M : Model K) (hq : 7 ≤ M.q) :
    DiamTwo M :=
  diamTwo_of_model_five M (by omega)

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
