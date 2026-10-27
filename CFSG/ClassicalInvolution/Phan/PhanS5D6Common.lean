module

public import CFSG.ClassicalInvolution.Phan.PhanS5D2Conic
public import CFSG.ClassicalInvolution.Phan.PhanS5D5Exist

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

@[expose] def gramForm (b x y : Vec K) : K := her M b b * her M x y - her M x b * her M b y

theorem sesq_gramForm (b : Vec K) : Sesq M (gramForm M b) := by
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun c x y => ?_, fun c x y => ?_⟩
  · simp only [gramForm, her_add_left]
    ring
  · simp only [gramForm, her_add_right]
    ring
  · simp only [gramForm, her_smul_left]
    ring
  · simp only [gramForm, her_smul_right]
    ring

theorem gramForm_self (b c : Vec K) : gramForm M b c c = gram M c b := by
  simp only [gramForm, gram]
  ring

variable {M}

theorem exists_cs_ne_zero {G : Vec K → Vec K → K} (hG : Sesq M G) {e f w : Vec K} {s : K}
    (hs : s ≠ 0)
    (h : G e e ≠ 0 ∨ G e f ≠ 0 ∨ G e w ≠ 0 ∨ G f e ≠ 0 ∨ G f f ≠ 0 ∨ G f w ≠ 0 ∨ G w e ≠ 0 ∨
      G w f ≠ 0 ∨ G w w ≠ 0) :
    ∃ i j : Fin 3, G (cs f w (s • e) i) (cs f w (s • e) j) ≠ 0 := by
  have hts : M.τ s ≠ 0 := tau_ne_zero M hs
  rcases h with h | h | h | h | h | h | h | h | h
  · refine ⟨2, 2, ?_⟩
    rw [cs_two, hG.smul_left, hG.smul_right]
    exact mul_ne_zero hs (mul_ne_zero hts h)
  · refine ⟨2, 0, ?_⟩
    rw [cs_two, cs_zero, hG.smul_left]
    exact mul_ne_zero hs h
  · refine ⟨2, 1, ?_⟩
    rw [cs_two, cs_one, hG.smul_left]
    exact mul_ne_zero hs h
  · refine ⟨0, 2, ?_⟩
    rw [cs_zero, cs_two, hG.smul_right]
    exact mul_ne_zero hts h
  · refine ⟨0, 0, ?_⟩
    rw [cs_zero]
    exact h
  · refine ⟨0, 1, ?_⟩
    rw [cs_zero, cs_one]
    exact h
  · refine ⟨1, 2, ?_⟩
    rw [cs_one, cs_two, hG.smul_right]
    exact mul_ne_zero hts h
  · refine ⟨1, 0, ?_⟩
    rw [cs_one, cs_zero]
    exact h
  · refine ⟨1, 1, ?_⟩
    rw [cs_one]
    exact h

variable (M)

@[expose] def projB (b x : Vec K) : Vec K := x + (-(her M x b / her M b b)) • b

variable {M}

theorem bf_proj_eq {b x y : Vec K} (hxb : bf M x b = 0) (hyb : bf M y b = 0)
    (hbb : bf M b b = 0) (c₁ c₂ : K) : bf M (x + c₁ • b) (y + c₂ • b) = bf M x y := by
  simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hxb, hyb, hbb,
    bf_comm M b y]
  ring

theorem bf_projB_sb {b x : Vec K} (hb : IsFF M b) (hxb : bf M x (tauV M b) = her M x b) :
    bf M (projB M b x) (tauV M b) = 0 := by
  have hr : her M b b ≠ 0 := hb.2
  simp only [projB, bf_add_left, bf_smul_left, hxb]
  have : bf M b (tauV M b) = her M b b := rfl
  rw [this]
  field_simp
  ring

theorem her_projB {b : Vec K} (hb : IsFF M b) (x y : Vec K) :
    her M b b * her M (projB M b x) (projB M b y) = gramForm M b x y := by
  have hr : her M b b ≠ 0 := hb.2
  simp only [projB, her_add_left, her_add_right, her_smul_left, her_smul_right, map_neg,
    map_div₀, tau_her_self, ← her_conj_symm M y b, gramForm]
  field_simp
  ring

theorem hypTriple_projB {a b e f w : Vec K} (hb : IsFF M b) (H : EFW M a b e f w) :
    HypTriple M b (projB M b e) (projB M b f) (projB M b w) := by
  have hbb : bf M b b = 0 := hb.1
  have he : bf M e b = 0 := H.e_b
  have hf : bf M f b = 0 := H.f_b
  have hw : bf M w b = 0 := H.w_b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [projB, bf_add_left, bf_smul_left, he, hbb]
    ring
  · exact bf_projB_sb hb rfl
  · simp only [projB, bf_add_left, bf_smul_left, hf, hbb]
    ring
  · exact bf_projB_sb hb rfl
  · simp only [projB, bf_add_left, bf_smul_left, hw, hbb]
    ring
  · exact bf_projB_sb hb rfl
  · simp only [projB]
    rw [bf_proj_eq he he hbb]
    exact H.hyp.ee
  · simp only [projB]
    rw [bf_proj_eq hf hf hbb]
    exact H.hyp.ff
  · simp only [projB]
    rw [bf_proj_eq he hf hbb]
    exact H.hyp.ef
  · simp only [projB]
    rw [bf_proj_eq hw he hbb]
    exact H.hyp.we
  · simp only [projB]
    rw [bf_proj_eq hw hf hbb]
    exact H.hyp.wf
  · simp only [projB]
    rw [bf_proj_eq hw hw hbb]
    exact H.hyp.ww

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
