module

public import CFSG.ClassicalInvolution.Phan.PhanQ53LemmaQB
public import CFSG.ClassicalInvolution.Phan.PhanQ52LemmaQA

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Combined

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem her_zero_left (v : V8 K) : her D 0 v = 0 := by
  unfold her
  simp

theorem ColK.coeff_zero {x y : V8 K} (h : ColK D x y) {s t : K}
    (h1 : s * her D x x + t * her D y x = 0) (h2 : s * her D x y + t * her D y y = 0) :
    s = 0 ∧ t = 0 := by
  have hg := h.2
  unfold gram at hg
  have hs : s * (her D x x * her D y y - her D x y * her D y x) = 0 := by
    linear_combination her D y y * h1 - her D y x * h2
  have ht : t * (her D x x * her D y y - her D x y * her D y x) = 0 := by
    linear_combination her D x x * h2 - her D x y * h1
  exact ⟨(mul_eq_zero.1 hs).resolve_right hg, (mul_eq_zero.1 ht).resolve_right hg⟩

theorem ColK.indep {x y : V8 K} (h : ColK D x y) {s t : K} (hst : s • x + t • y = 0) :
    s = 0 ∧ t = 0 := by
  refine h.coeff_zero D ?_ ?_
  · have := congrArg (fun w => her D w x) hst
    simpa only [her_add_left, her_smul_left, her_zero_left] using this
  · have := congrArg (fun w => her D w y) hst
    simpa only [her_add_left, her_smul_left, her_zero_left] using this

theorem ColK.finrank_span {x y : V8 K} (h : ColK D x y) :
    Module.finrank K ↥(Submodule.span K {x, y}) = 2 := by
  have hli : LinearIndependent K ![x, y] :=
    LinearIndependent.pair_iff.2 fun s t hst => h.indep D hst
  have h' := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty] at h'
  simpa using h'

theorem ColK.eq_zero_of_her {x y r : V8 K} (h : ColK D x y) (hr : r ∈ Submodule.span K {x, y})
    (h1 : her D r x = 0) (h2 : her D r y = 0) : r = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hr
  rw [her_add_left, her_smul_left, her_smul_left] at h1 h2
  obtain ⟨hs, ht⟩ := h.coeff_zero D h1 h2
  rw [hs, ht, zero_smul, zero_smul, add_zero]

theorem exists_phanSolid_of_colK [Finite F] [Finite K] (hodd : Odd (Nat.card F))
    (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x)
    {H : Submodule K (V8 K)} (hts : ∀ u ∈ H, ∀ v ∈ H, B8 u v = 0)
    (hdim : Module.finrank K H ≤ 3) (hinf : ∀ v ∈ H, conj D v ∈ H → v = 0) {x y : V8 K}
    (hx : x ∈ H) (hy : y ∈ H) (hxy : ColK D x y) : ∃ W, PhanSolid D W ∧ H ≤ W := by
  by_cases hnd : ∀ u ∈ H, (∀ v ∈ H, her D u v = 0) → u = 0
  · exact exists_phanSolid_of_nondeg D hts hnd hdim hodd h2 hε hσ
  · obtain ⟨r, hr, hrad, hr0⟩ : ∃ r ∈ H, (∀ v ∈ H, her D r v = 0) ∧ r ≠ 0 := by
      by_contra hcon
      exact hnd fun u hu hu' => Classical.byContradiction fun hu0 => hcon ⟨u, hu, hu', hu0⟩
    have hP : Submodule.span K {x, y} ≤ H := by
      rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact hx
      · exact hy
    have hP2 := hxy.finrank_span D
    have hle := Submodule.finrank_mono hP
    have hdim3 : Module.finrank K H = 3 := by
      by_contra hne
      have h22 : Module.finrank K H = 2 := by omega
      have hPH : Submodule.span K {x, y} = H :=
        Submodule.eq_of_le_of_finrank_eq hP (by rw [hP2, h22])
      apply hr0
      exact hxy.eq_zero_of_her D (hPH ▸ hr) (hrad x hx) (hrad y hy)
    exact exists_phanSolid_of_rad D h2 hε hts hdim3 hinf hr hr0 (fun h hh => hrad h hh)

end Combined

section Span

variable {K : Type} [Field K]

theorem ts_span {S : Set (V8 K)} (hS : ∀ u ∈ S, ∀ v ∈ S, B8 u v = 0) :
    ∀ u ∈ Submodule.span K S, ∀ v ∈ Submodule.span K S, B8 u v = 0 := by
  intro u hu v hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem y hy => exact hS x hx y hy
    | zero => simp
    | add y z _ _ hy hz => rw [B8_add_right, hy, hz, add_zero]
    | smul a y _ hy => rw [B8_smul_right, hy, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [B8_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [B8_smul_left, hx, mul_zero]

theorem ts_pair {a b : V8 K} (hQa : Q8 a = 0) (hQb : Q8 b = 0) (hab : B8 a b = 0) :
    ∀ u ∈ Submodule.span K {a, b}, ∀ v ∈ Submodule.span K {a, b}, B8 u v = 0 := by
  apply ts_span
  have hba : B8 b a = 0 := by rw [B8_comm]; exact hab
  have haa : B8 a a = 0 := by rw [B8_self, hQa, mul_zero]
  have hbb : B8 b b = 0 := by rw [B8_self, hQb, mul_zero]
  rintro u (rfl | rfl) v (rfl | rfl) <;> assumption

theorem ts_triple {a b c : V8 K} (hQa : Q8 a = 0) (hQb : Q8 b = 0) (hQc : Q8 c = 0)
    (hab : B8 a b = 0) (hac : B8 a c = 0) (hbc : B8 b c = 0) :
    ∀ u ∈ Submodule.span K {a, b, c}, ∀ v ∈ Submodule.span K {a, b, c}, B8 u v = 0 := by
  apply ts_span
  have hba : B8 b a = 0 := by rw [B8_comm]; exact hab
  have hca : B8 c a = 0 := by rw [B8_comm]; exact hac
  have hcb : B8 c b = 0 := by rw [B8_comm]; exact hbc
  have haa : B8 a a = 0 := by rw [B8_self, hQa, mul_zero]
  have hbb : B8 b b = 0 := by rw [B8_self, hQb, mul_zero]
  have hcc : B8 c c = 0 := by rw [B8_self, hQc, mul_zero]
  rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) <;> assumption

theorem mem_span_triple' {a b c r : V8 K} (hr : r ∈ Submodule.span K {a, b, c}) :
    ∃ s t u : K, r = s • a + t • b + u • c := by
  obtain ⟨s, t, u, h⟩ := Submodule.mem_span_triple.1 hr
  exact ⟨s, t, u, h.symm⟩

theorem finrank_span_three_le (x c e : V8 K) :
    Module.finrank K ↥(Submodule.span K {x, c, e}) ≤ 3 := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({x, c, e} : Finset (V8 K))
  have h2 : (({x, c, e} : Finset (V8 K)) : Set (V8 K)) = {x, c, e} := by simp
  rw [h2] at h
  exact h.trans Finset.card_le_three

end Span

section Rad

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem her_add_rad (x y r : V8 K) (l μ : K) (hxr : her D x r = 0) (hry : her D r y = 0)
    (hrr : her D r r = 0) : her D (x + l • r) (y + μ • r) = her D x y := by
  simp only [her_add_left, her_add_right, her_smul_left, her_smul_right, hxr, hry, hrr,
    mul_zero, add_zero]

theorem gram_add_rad (x y r : V8 K) (l μ : K) (hxr : her D x r = 0) (hrx : her D r x = 0)
    (hyr : her D y r = 0) (hry : her D r y = 0) (hrr : her D r r = 0) :
    gram D (x + l • r) (y + μ • r) = gram D x y := by
  unfold gram
  rw [her_add_rad D x x r l l hxr hrx hrr, her_add_rad D y y r μ μ hyr hry hrr,
    her_add_rad D x y r l μ hxr hry hrr, her_add_rad D y x r μ l hyr hrx hrr]

theorem gram_smul_self (x : V8 K) (l : K) : gram D x (l • x) = 0 := by
  unfold gram
  simp only [her_smul_left, her_smul_right]
  ring

theorem gram_eq_zero_of_rad (x r : V8 K) (l γ : K) (hxr : her D x r = 0) (hrx : her D r x = 0)
    (hrr : her D r r = 0) : gram D x (l • x + γ • r) = 0 := by
  have h := gram_add_rad D x (l • x) r 0 γ hxr hrx (by rw [her_smul_left, hxr, mul_zero])
    (by rw [her_smul_right, hrx, mul_zero]) hrr
  rw [zero_smul, add_zero] at h
  rw [h]
  exact gram_smul_self D x l

theorem her_zero_of_mem_span_pair {a b r : V8 K} (har : her D a r = 0) (hbr : her D b r = 0)
    {z : V8 K} (hz : z ∈ Submodule.span K {a, b}) : her D z r = 0 ∧ her D r z = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hz
  have h1 : her D (s • a + t • b) r = 0 := by
    rw [her_add_left, her_smul_left, her_smul_left, har, hbr, mul_zero, mul_zero, add_zero]
  exact ⟨h1, by rw [her_conj_symm D (s • a + t • b) r, h1, map_zero]⟩

end Rad

end CFSG.ClassicalInvolution.PhanQ
