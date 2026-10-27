module

public import CFSG.ClassicalInvolution.Phan.PhanS0Graph
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std

open CFSG.ClassicalInvolution.Phan

abbrev Vec (K : Type) : Type := Fin 3 ⊕ Fin 3 ⊕ Unit → K

structure Model (K : Type) [Field K] where
  q : ℕ
  τ : K →+* K
  κ : K
  card_K : Nat.card K = q ^ 2
  tau_pow : ∀ x : K, τ x = x ^ q
  tau_tau : ∀ x : K, τ (τ x) = x
  κ_ne : κ ≠ 0
  tau_κ : τ κ = κ
  two_ne : (2 : K) ≠ 0

variable {K : Type} [Field K] (M : Model K)

section Forms

@[expose] def tauV (x : Vec K) : Vec K :=
  Sum.elim (fun i => M.τ (x (.inr (.inl i))))
    (Sum.elim (fun i => M.τ (x (.inl i))) (fun u => M.τ (x (.inr (.inr u)))))

@[expose] def bf (x y : Vec K) : K :=
  ∑ i : Fin 3, (x (.inl i) * y (.inr (.inl i)) + y (.inl i) * x (.inr (.inl i))) +
    M.κ * (x (.inr (.inr ())) * y (.inr (.inr ())))

@[expose] def her (x y : Vec K) : K := bf M x (tauV M y)

@[expose] def gram (x y : Vec K) : K := her M x x * her M y y - her M x y * her M y x

@[expose] def IsFF (x : Vec K) : Prop := bf M x x = 0 ∧ her M x x ≠ 0

@[expose] def Col (x y : Vec K) : Prop := bf M x y = 0 ∧ gram M x y ≠ 0

@[expose] def det3 (x y z : Vec K) : K :=
  her M x x * (her M y y * her M z z - her M y z * her M z y) -
    her M x y * (her M y x * her M z z - her M y z * her M z x) +
    her M x z * (her M y x * her M z y - her M y y * her M z x)

@[expose] def Geom (x y z : Vec K) : Prop :=
  Col M x y ∧ Col M y z ∧ Col M z x ∧ (det3 M x y z ≠ 0 ∨ ∃ s t : K, z = s • x + t • y)

theorem bf_comm (x y : Vec K) : bf M x y = bf M y x := by
  simp only [bf]
  rw [mul_comm (y (.inr (.inr ()))) (x (.inr (.inr ())))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem bf_add_left (x y z : Vec K) : bf M (x + y) z = bf M x z + bf M y z := by
  have hs : ∑ i : Fin 3, ((x + y) (.inl i) * z (.inr (.inl i)) +
      z (.inl i) * (x + y) (.inr (.inl i))) =
      ∑ i : Fin 3, (x (.inl i) * z (.inr (.inl i)) + z (.inl i) * x (.inr (.inl i))) +
        ∑ i : Fin 3, (y (.inl i) * z (.inr (.inl i)) + z (.inl i) * y (.inr (.inl i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  unfold bf
  rw [hs]
  simp only [Pi.add_apply]
  ring

theorem bf_smul_left (c : K) (x y : Vec K) : bf M (c • x) y = c * bf M x y := by
  unfold bf
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem bf_smul_right (c : K) (x y : Vec K) : bf M x (c • y) = c * bf M x y := by
  rw [bf_comm, bf_smul_left, bf_comm]

theorem tauV_tauV (x : Vec K) : tauV M (tauV M x) = x := by
  funext s
  rcases s with i | i | u
  · simp [tauV, M.tau_tau]
  · simp [tauV, M.tau_tau]
  · simp [tauV, M.tau_tau]

theorem tauV_smul (c : K) (x : Vec K) : tauV M (c • x) = M.τ c • tauV M x := by
  funext s
  rcases s with i | i | u <;> simp [tauV]

theorem tauV_add (x y : Vec K) : tauV M (x + y) = tauV M x + tauV M y := by
  funext s
  rcases s with i | i | u <;> simp [tauV]

theorem bf_tauV (x y : Vec K) : bf M (tauV M x) (tauV M y) = M.τ (bf M x y) := by
  simp only [bf, tauV, Sum.elim_inl, Sum.elim_inr, map_add, map_mul, map_sum, M.tau_κ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem her_smul_left (c : K) (x y : Vec K) : her M (c • x) y = c * her M x y := by
  simp only [her, bf_smul_left]

theorem her_smul_right (c : K) (x y : Vec K) : her M x (c • y) = M.τ c * her M x y := by
  simp only [her, tauV_smul, bf_smul_right]

theorem her_add_left (x y z : Vec K) : her M (x + y) z = her M x z + her M y z := by
  simp only [her, bf_add_left]

theorem her_add_right (x y z : Vec K) : her M x (y + z) = her M x y + her M x z := by
  simp only [her, tauV_add, bf_comm M x, bf_add_left]

theorem her_conj_symm (x y : Vec K) : her M y x = M.τ (her M x y) := by
  simp only [her]
  conv_lhs => rw [bf_comm, ← tauV_tauV M y]
  rw [bf_tauV]

theorem tau_her_self (x : Vec K) : M.τ (her M x x) = her M x x := by
  rw [← her_conj_symm]

theorem gram_comm (x y : Vec K) : gram M y x = gram M x y := by
  simp only [gram]
  ring

theorem tau_mul_self_fixed (c : K) : M.τ (c * M.τ c) = c * M.τ c := by
  rw [map_mul, M.tau_tau, mul_comm]

theorem tau_ne_zero {c : K} (hc : c ≠ 0) : M.τ c ≠ 0 := by
  intro h
  apply hc
  have := congrArg M.τ h
  rwa [M.tau_tau, map_zero] at this

theorem norm_ne_zero {c : K} (hc : c ≠ 0) : c * M.τ c ≠ 0 :=
  mul_ne_zero hc (tau_ne_zero M hc)

theorem gram_smul (c d : K) (x y : Vec K) :
    gram M (c • x) (d • y) = (c * M.τ c) * (d * M.τ d) * gram M x y := by
  simp only [gram, her_smul_left, her_smul_right]
  ring

theorem isFF_smul {c : K} (hc : c ≠ 0) {x : Vec K} : IsFF M (c • x) ↔ IsFF M x := by
  have h1 : bf M (c • x) (c • x) = c * c * bf M x x := by
    rw [bf_smul_left, bf_smul_right]
    ring
  have h2 : her M (c • x) (c • x) = (c * M.τ c) * her M x x := by
    rw [her_smul_left, her_smul_right]
    ring
  have h3 := norm_ne_zero M hc
  have hcc : c * c ≠ 0 := mul_ne_zero hc hc
  unfold IsFF
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨(mul_eq_zero.mp a).resolve_left hcc, fun h => b (by rw [h, mul_zero])⟩
  · rintro ⟨a, b⟩
    exact ⟨by rw [a, mul_zero], mul_ne_zero h3 b⟩

theorem col_smul {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) {x y : Vec K} :
    Col M (c • x) (d • y) ↔ Col M x y := by
  have h1 : bf M (c • x) (d • y) = c * d * bf M x y := by
    rw [bf_smul_left, bf_smul_right]
    ring
  have h2 := gram_smul M c d x y
  have h3 := mul_ne_zero (norm_ne_zero M hc) (norm_ne_zero M hd)
  have hcd : c * d ≠ 0 := mul_ne_zero hc hd
  unfold Col
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨(mul_eq_zero.mp a).resolve_left hcd, fun h => b (by rw [h, mul_zero])⟩
  · rintro ⟨a, b⟩
    exact ⟨by rw [a, mul_zero], mul_ne_zero h3 b⟩

theorem Col.symm {x y : Vec K} (h : Col M x y) : Col M y x :=
  ⟨by rw [bf_comm]; exact h.1, by rw [gram_comm]; exact h.2⟩

theorem not_col_self (x : Vec K) : ¬ Col M x x := fun h => h.2 (by simp [gram])

end Forms

section Points

@[expose] def FFPt : Type := {x : Projectivization K (Vec K) // IsFF M x.rep}

theorem exists_smul_rep {v : Vec K} (hv : v ≠ 0) (x : Projectivization K (Vec K))
    (hx : x = Projectivization.mk K v hv) : ∃ c : K, c ≠ 0 ∧ x.rep = c • v := by
  have h : Projectivization.mk K x.rep x.rep_nonzero = Projectivization.mk K v hv := by
    rw [Projectivization.mk_rep, hx]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ x.rep_nonzero hv).1 h
  refine ⟨a, fun h0 => ?_, ha.symm⟩
  subst h0
  simp only [zero_smul] at ha
  exact x.rep_nonzero ha.symm

@[expose] def ffGraph : SimpleGraph (FFPt M) where
  Adj x y := Col M x.1.rep y.1.rep
  symm := ⟨fun _ _ h => Col.symm M h⟩
  loopless := ⟨fun _ h => not_col_self M _ h⟩

noncomputable def FFPt.mk {v : Vec K} (hv : IsFF M v) : FFPt M :=
  have hv0 : v ≠ 0 := fun h => hv.2 (by simp [h, her, bf])
  ⟨Projectivization.mk K v hv0, by
    obtain ⟨c, hc, hrep⟩ := exists_smul_rep hv0 (Projectivization.mk K v hv0) rfl
    rw [hrep, isFF_smul M hc]
    exact hv⟩

theorem FFPt.mk_rep {v : Vec K} (hv : IsFF M v) :
    ∃ c : K, c ≠ 0 ∧ (FFPt.mk M hv).1.rep = c • v := by
  have hv0 : v ≠ 0 := fun h => hv.2 (by simp [h, her, bf])
  exact exists_smul_rep hv0 _ rfl

theorem ffGraph_adj_mk {v w : Vec K} (hv : IsFF M v) (hw : IsFF M w) :
    (ffGraph M).Adj (FFPt.mk M hv) (FFPt.mk M hw) ↔ Col M v w := by
  obtain ⟨c, hc, hcv⟩ := FFPt.mk_rep M hv
  obtain ⟨d, hd, hdw⟩ := FFPt.mk_rep M hw
  show Col M (FFPt.mk M hv).1.rep (FFPt.mk M hw).1.rep ↔ _
  rw [hcv, hdw, col_smul M hc hd]

theorem FFPt.exists_vec (x : FFPt M) : ∃ (v : Vec K) (hv : IsFF M v), x = FFPt.mk M hv :=
  ⟨x.1.rep, x.2, Subtype.ext (Projectivization.mk_rep x.1).symm⟩

end Points

section Geometry

theorem det3_smul (c d e : K) (x y z : Vec K) :
    det3 M (c • x) (d • y) (e • z) =
      (c * M.τ c) * (d * M.τ d) * (e * M.τ e) * det3 M x y z := by
  simp only [det3, her_smul_left, her_smul_right]
  ring

theorem geom_smul {c d e : K} (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) {x y z : Vec K} :
    Geom M (c • x) (d • y) (e • z) ↔ Geom M x y z := by
  have h3 : (c * M.τ c) * (d * M.τ d) * (e * M.τ e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (norm_ne_zero M hc) (norm_ne_zero M hd)) (norm_ne_zero M he)
  have hdet : det3 M (c • x) (d • y) (e • z) ≠ 0 ↔ det3 M x y z ≠ 0 := by
    rw [det3_smul]
    constructor
    · intro h h0
      apply h
      rw [h0, mul_zero]
    · intro h
      exact mul_ne_zero h3 h
  have hsp : (∃ s t : K, e • z = s • (c • x) + t • (d • y)) ↔ ∃ s t : K, z = s • x + t • y := by
    constructor
    · rintro ⟨s, t, h⟩
      refine ⟨e⁻¹ * (s * c), e⁻¹ * (t * d), ?_⟩
      have h' : z = (e⁻¹ * s * c) • x + (e⁻¹ * t * d) • y := by
        have := congrArg (fun w => e⁻¹ • w) h
        simp only [smul_smul, smul_add, inv_mul_cancel₀ he, one_smul] at this
        rw [this]
        simp only [mul_assoc]
      rw [h']
      simp only [mul_assoc]
    · rintro ⟨s, t, h⟩
      refine ⟨e * s * c⁻¹, e * t * d⁻¹, ?_⟩
      rw [h, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 2
      · rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hc, mul_one]
      · rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  unfold Geom
  rw [col_smul M hc hd, col_smul M hd he, col_smul M he hc, hdet, hsp]

end Geometry

section Targets

@[expose] def GeomPt (a b c : FFPt M) : Prop := Geom M a.1.rep b.1.rep c.1.rep

@[expose] def DiamTwo : Prop := (ffGraph M).Connected ∧ (ffGraph M).ediam ≤ 2

@[expose] def geomWalks : ∀ x : FFPt M, Set ((ffGraph M).Walk x x) := fun x =>
  {w | ∃ (y z : FFPt M) (h₁ : (ffGraph M).Adj x y) (h₂ : (ffGraph M).Adj y z)
    (h₃ : (ffGraph M).Adj z x), w = .cons h₁ (.cons h₂ (.cons h₃ .nil)) ∧ GeomPt M x y z}

@[expose] def TriNull : Prop :=
  ∀ (a b c : FFPt M) (hab : (ffGraph M).Adj a b) (hbc : (ffGraph M).Adj b c)
    (hca : (ffGraph M).Adj c a),
    CycleHomotopic (geomWalks M) (.cons hab (.cons hbc (.cons hca .nil)) : (ffGraph M).Walk a a)
      .nil

@[expose] def QuadNullStd : Prop := QuadNull (ffGraph M)

@[expose] def PentNullStd : Prop := PentNull (ffGraph M)

@[expose] def PentApex : Prop := ApexPentagon (G := ffGraph M)

theorem pentNullStd_of_pentApex (hq : QuadNullStd M) (h : PentApex M) : PentNullStd M := by
  intro u p hp
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    refine cycleHomotopic_pent_nil (triWalks (ffGraph M)) ?_ ?_ h h₁ h₂ h₃ h₄ h₅
    · intro u p hp
      exact cycleHomotopic_of_mem _ hp
    · intro u p hp
      exact cycleHomotopic_quad_of_quadNull _ hq (fun {u} p hp => cycleHomotopic_of_mem _ hp) p hp

end Targets

end CFSG.ClassicalInvolution.PhanB3.S.Std
