module

public import CFSG.ClassicalInvolution.Phan.PhanS7P1Count
public import CFSG.ClassicalInvolution.Phan.PhanS5D7Main

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.P

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.D

variable {K : Type} [Field K] (M : Model K)

@[expose] def cpr (c d : Vec K) : Vec K := her M c c • d + (-her M d c) • c

@[expose] def shiftOrth (u a x : Vec K) : Vec K := x + (-(bf M x a / bf M u a)) • u

variable {M}

theorem bf_cpr_left (c d x : Vec K) :
    bf M (cpr M c d) x = her M c c * bf M d x + (-her M d c) * bf M c x := by
  simp only [cpr, bf_add_left, bf_smul_left]

theorem bf_cpr_of_orth {c d x : Vec K} (hc : bf M c x = 0) (hd : bf M d x = 0) :
    bf M (cpr M c d) x = 0 := by
  rw [bf_cpr_left, hc, hd]
  ring

theorem bf_cpr_sigma (c d : Vec K) : bf M (cpr M c d) (tauV M c) = 0 := by
  rw [bf_cpr_left]
  have h1 : bf M d (tauV M c) = her M d c := rfl
  have h2 : bf M c (tauV M c) = her M c c := rfl
  rw [h1, h2]
  ring

theorem bf_cpr_right (c d x : Vec K) :
    bf M x (cpr M c d) = her M c c * bf M x d + (-her M d c) * bf M x c := by
  simp only [cpr, bf_add_right, bf_smul_right]

theorem bf_cpr_self {c d : Vec K} (hc : bf M c c = 0) (hd : bf M d d = 0) (hcd : bf M c d = 0) :
    bf M (cpr M c d) (cpr M c d) = 0 := by
  have h1 : bf M (cpr M c d) c = 0 := bf_cpr_of_orth hc (by rw [bf_comm]; exact hcd)
  have h2 : bf M (cpr M c d) d = 0 := bf_cpr_of_orth hcd hd
  rw [bf_cpr_right, h1, h2]
  ring

theorem bf_shiftOrth_a {u a : Vec K} (hA : bf M u a ≠ 0) (x : Vec K) :
    bf M (shiftOrth M u a x) a = 0 := by
  simp only [shiftOrth, bf_add_left, bf_smul_left]
  field_simp
  ring

theorem bf_shiftOrth_of_orth {u a x z : Vec K} (hu : bf M u z = 0) (hx : bf M x z = 0) :
    bf M (shiftOrth M u a x) z = 0 := by
  simp only [shiftOrth, bf_add_left, bf_smul_left, hu, hx]
  ring

theorem bf_shiftOrth_shiftOrth {u a x y : Vec K} (hxu : bf M x u = 0) (hyu : bf M y u = 0)
    (huu : bf M u u = 0) :
    bf M (shiftOrth M u a x) (shiftOrth M u a y) = bf M x y :=
  bf_proj_eq hxu hyu huu _ _

omit [Field K] in
theorem nine_imp {P Q : Vec K → Vec K → Prop} {e f w : Vec K} (hPQ : ∀ x y, P x y → Q x y)
    (h : P e e ∨ P e f ∨ P e w ∨ P f e ∨ P f f ∨ P f w ∨ P w e ∨ P w f ∨ P w w) :
    Q e e ∨ Q e f ∨ Q e w ∨ Q f e ∨ Q f f ∨ Q f w ∨ Q w e ∨ Q w f ∨ Q w w :=
  h.imp (hPQ _ _) (Or.imp (hPQ _ _) (Or.imp (hPQ _ _) (Or.imp (hPQ _ _) (Or.imp (hPQ _ _)
    (Or.imp (hPQ _ _) (Or.imp (hPQ _ _) (Or.imp (hPQ _ _) (hPQ _ _))))))))

theorem exists_cs_gramForm_ne_zero {a b e f w : Vec K} {s : K} (hs : s ≠ 0) (hb : IsFF M b)
    (H : EFW M a b e f w) :
    ∃ i j : Fin 3, gramForm M b (cs f w (s • e) i) (cs f w (s • e) j) ≠ 0 := by
  refine exists_cs_ne_zero (sesq_gramForm M b) hs (nine_imp
    (P := fun x y => her M (projB M b x) (projB M b y) ≠ 0)
    (Q := fun x y => gramForm M b x y ≠ 0) ?_ (exists_her_ne_zero hb (hypTriple_projB hb H)))
  intro x y h
  rw [← her_projB hb x y]
  exact mul_ne_zero hb.2 h

variable [Finite K]

theorem exists_apex_cprime (hq : 7 ≤ M.q) {a c d : Vec K} (ha : IsFF M a) (hc : IsFF M c)
    (hd : IsFF M d) (hcd : Col M c d) (hA : bf M (cpr M c d) a ≠ 0) :
    ∃ f : Vec K, IsFF M f ∧ Col M f c ∧ Col M f d ∧ Col M f a := by
  obtain ⟨e, f, w, H⟩ := exists_efw hc d
  have hdc : bf M d c = 0 := by rw [bf_comm]; exact hcd.1
  have hu1 : bf M (cpr M c d) c = 0 := bf_cpr_of_orth hc.1 hdc
  have hu2 : bf M (cpr M c d) (tauV M c) = 0 := bf_cpr_sigma c d
  have hu3 : bf M (cpr M c d) d = 0 := bf_cpr_of_orth hcd.1 hd.1
  have huu : bf M (cpr M c d) (cpr M c d) = 0 := bf_cpr_self hc.1 hd.1 hcd.1
  have hx : ∀ x : Vec K, bf M x c = 0 → bf M x d = 0 → bf M x (cpr M c d) = 0 := by
    intro x h1 h2
    rw [bf_cpr_right, h1, h2]
    ring
  have he' : bf M e (cpr M c d) = 0 := hx e H.hyp.e_c H.e_b
  have hf' : bf M f (cpr M c d) = 0 := hx f H.hyp.f_c H.f_b
  have hw' : bf M w (cpr M c d) = 0 := hx w H.hyp.w_c H.w_b
  have T : HypTriple M c (shiftOrth M (cpr M c d) a e) (shiftOrth M (cpr M c d) a f)
      (shiftOrth M (cpr M c d) a w) := by
    refine ⟨bf_shiftOrth_of_orth hu1 H.hyp.e_c, bf_shiftOrth_of_orth hu2 H.hyp.e_sc,
      bf_shiftOrth_of_orth hu1 H.hyp.f_c, bf_shiftOrth_of_orth hu2 H.hyp.f_sc,
      bf_shiftOrth_of_orth hu1 H.hyp.w_c, bf_shiftOrth_of_orth hu2 H.hyp.w_sc, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [bf_shiftOrth_shiftOrth he' he' huu]
      exact H.hyp.ee
    · rw [bf_shiftOrth_shiftOrth hf' hf' huu]
      exact H.hyp.ff
    · rw [bf_shiftOrth_shiftOrth he' hf' huu]
      exact H.hyp.ef
    · rw [bf_shiftOrth_shiftOrth hw' he' huu]
      exact H.hyp.we
    · rw [bf_shiftOrth_shiftOrth hw' hf' huu]
      exact H.hyp.wf
    · rw [bf_shiftOrth_shiftOrth hw' hw' huu]
      exact H.hyp.ww
  have Td : EFW M c d (shiftOrth M (cpr M c d) a e) (shiftOrth M (cpr M c d) a f)
      (shiftOrth M (cpr M c d) a w) :=
    ⟨T, bf_shiftOrth_of_orth hu3 H.e_b, bf_shiftOrth_of_orth hu3 H.f_b,
      bf_shiftOrth_of_orth hu3 H.w_b⟩
  have Ta : EFW M c a (shiftOrth M (cpr M c d) a e) (shiftOrth M (cpr M c d) a f)
      (shiftOrth M (cpr M c d) a w) :=
    ⟨T, bf_shiftOrth_a hA e, bf_shiftOrth_a hA f, bf_shiftOrth_a hA w⟩
  generalize shiftOrth M (cpr M c d) a e = E at T Td Ta
  generalize shiftOrth M (cpr M c d) a f = F at T Td Ta
  generalize shiftOrth M (cpr M c d) a w = W at T Td Ta
  have h2 := M.two_ne
  have hQ0 : bf M W W ≠ 0 := T.ww
  obtain ⟨s, hs2, hs0⟩ : ∃ s : K, 2 * s + bf M W W = 0 ∧ s ≠ 0 := by
    refine ⟨-(bf M W W / 2), ?_, neg_ne_zero.mpr (div_ne_zero hQ0 h2)⟩
    field_simp
    ring
  have w1 : ∃ i j : Fin 3, her M (cs F W (s • E) i) (cs F W (s • E) j) ≠ 0 :=
    exists_cs_ne_zero (sesq_her M) hs0 (exists_her_ne_zero hc T)
  have w2 := exists_cs_gramForm_ne_zero hs0 hd Td
  have w3 := exists_cs_gramForm_ne_zero hs0 ha Ta
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := exists_mu_conic_three hq (sesq_her M) (sesq_gramForm M d)
    (sesq_gramForm M a) w1 w2 w3
  have hcc : bf M (conicPt F W (s • E) μ) (conicPt F W (s • E) μ) = 0 :=
    bf_conicPt_self T.ee T.ff T.ef T.we T.wf hs2 μ
  have hc0 : bf M (conicPt F W (s • E) μ) c = 0 := bf_conicPt_orth T.e_c T.f_c T.w_c μ
  have hsc0 : bf M (conicPt F W (s • E) μ) (tauV M c) = 0 :=
    bf_conicPt_orth T.e_sc T.f_sc T.w_sc μ
  have hd0 : bf M (conicPt F W (s • E) μ) d = 0 := bf_conicPt_orth Td.e_b Td.f_b Td.w_b μ
  have ha0 : bf M (conicPt F W (s • E) μ) a = 0 := bf_conicPt_orth Ta.e_b Ta.f_b Ta.w_b μ
  have hher_fc : her M (conicPt F W (s • E) μ) c = 0 := hsc0
  have hher_cf : her M c (conicPt F W (s • E) μ) = 0 := by
    rw [her_conj_symm, hher_fc, map_zero]
  refine ⟨conicPt F W (s • E) μ, ⟨hcc, hμ1⟩, ⟨hc0, ?_⟩, ⟨hd0, ?_⟩, ⟨ha0, ?_⟩⟩
  · simp only [gram, hher_fc, hher_cf, mul_zero, sub_zero]
    exact mul_ne_zero hμ1 hc.2
  · rw [← gramForm_self]
    exact hμ2
  · rw [← gramForm_self]
    exact hμ3

end CFSG.ClassicalInvolution.PhanB3.S.Std.P
