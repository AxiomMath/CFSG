module

public import CFSG.Fischer.Classification.PartII.O2Herm
public import CFSG.Fischer.Classification.Unitary.Local
import all CFSG.Fischer.F4
public import CFSG.Fischer.Classification.Unitary.Star

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

theorem K_cases (c : K) (hc : c ≠ 0) : c = 1 ∨ c = ω ∨ c = ω * ω := by
  obtain ⟨d, rfl⟩ := eF4.surjective c
  simp only [ne_eq, omega_eq, ← map_zero eF4, ← map_one eF4, ← map_mul, eF4_inj] at hc ⊢
  revert d
  decide

theorem K_eq_add (c₁ c₂ c₃ : K) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (h₃ : c₃ ≠ 0) (h12 : c₁ ≠ c₂)
    (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃) : c₃ = c₁ + c₂ := by
  obtain ⟨d₁, rfl⟩ := eF4.surjective c₁
  obtain ⟨d₂, rfl⟩ := eF4.surjective c₂
  obtain ⟨d₃, rfl⟩ := eF4.surjective c₃
  simp only [ne_eq, ← map_zero eF4, ← map_add, eF4_inj] at *
  revert d₁ d₂ d₃
  decide

theorem K_add_inv (c m : K) (hc : c ≠ 0) (hm : m ≠ 0) (h1 : c * m ≠ 1) :
    c + m⁻¹ = (1 + c * m)⁻¹ * c := by
  obtain ⟨d, rfl⟩ := eF4.surjective c
  obtain ⟨e, rfl⟩ := eF4.surjective m
  simp only [ne_eq, ← map_zero eF4, ← map_one eF4, ← map_add, ← map_mul, ← map_inv₀,
    eF4_inj] at *
  revert d e
  decide

theorem omega_mul_omega_ne_one : ω * ω ≠ 1 := by
  rw [omega_eq, ← map_mul, ← map_one eF4, ne_eq, eF4_inj]
  decide

theorem one_add_eq_zero_iff (c : K) : 1 + c = 0 ↔ c = 1 := by
  rw [add_eq_zero_iff_eq_neg, neg_K, eq_comm]

theorem vadd_self {N : ℕ} (x : Fin N → K) : x + x = 0 := funext fun i => add_self_K (x i)

theorem eq_of_smul_eq_smul {N : ℕ} {x : Fin N → K} (hx : x ≠ 0) {c c' : K}
    (h : c • x = c' • x) : c = c' :=
  smul_left_injective K hx h

section Model

variable {n : ℕ}

theorem lineVec_zero (x : Fin n → K) : lineVec x 0 = ι n x := by
  rw [lineVec, zero_smul, zero_add]

theorem smul_lineVec (c : K) (x : Fin n → K) (a : K) :
    c • lineVec x a = lineVec (c • x) (c * a) := by
  rw [lineVec, lineVec, smul_add, smul_smul, map_smul]

theorem herm_u₀_lineVec (x : Fin n → K) (a : K) : herm frob (u₀ n) (lineVec x a) = a := by
  rw [lineVec, herm_add_right, herm_smul_right, herm_u₀_v₀, herm_u₀_ι, mul_one, add_zero]

theorem lineVec_inj {x y : Fin n → K} {a b : K} (h : lineVec x a = lineVec y b) :
    x = y ∧ a = b :=
  ⟨by rw [← π_lineVec x a, h, π_lineVec], by rw [← herm_u₀_lineVec x a, h, herm_u₀_lineVec]⟩

theorem lineVec_ne_zero {x : Fin n → K} (hx : x ≠ 0) (a : K) : lineVec x a ≠ 0 := fun h =>
  hx (by rw [← π_lineVec x a, h, map_zero])

theorem herm_lineVec_eq (x y : Fin n → K) (a b : K) :
    herm frob (lineVec x a) (lineVec y b) = herm frob x y := by
  rw [herm_lineVec_left, herm_v₀_lineVec, mul_zero, zero_add, herm_ι_left, π_lineVec]

theorem isotropic_lineVec {x : Fin n → K} (hx : herm frob x x = 0) (a : K) :
    herm frob (lineVec x a) (lineVec x a) = 0 := by
  rw [herm_lineVec_eq, hx]

theorem tvU_smul_lineVec {x : Fin n → K} (hx : herm frob x x = 0) (a : K) (y : Fin n → K)
    (b : K) :
    tvU (lineVec x a) • lineVec y b = lineVec (y + herm frob x y • x) (b + herm frob x y * a) := by
  rw [tvU_smul (isotropic_lineVec hx a), herm_lineVec_eq, smul_lineVec, lineVec, lineVec,
    lineVec, map_add, add_smul]
  abel

theorem tqU_smul {m : ℕ} {w : Fin m → K} (hw : herm frob w w = 0) {c : K} (hc : c ≠ 0) :
    tqU (c • w) = tqU w := by
  rw [tqU, tqU, tq, tq, tvU_smul_vec hw hc]

theorem tqU_lineVec_eq_iff (hn : 1 ≤ n) {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (a b : K) :
    tqU (lineVec x a) = tqU (lineVec y b) ↔ ∃ c : K, y = c • x ∧ b = c * a := by
  rw [tqU_eq_tqU_iff (by omega) (lineVec_ne_zero hx0 a) (isotropic_lineVec hx a)
    (lineVec_ne_zero hy0 b) (isotropic_lineVec hy b)]
  refine exists_congr fun c => ?_
  rw [smul_lineVec]
  exact ⟨lineVec_inj, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

theorem tqU_lineVec_commute_iff (hn : 1 ≤ n) {x y : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hy0 : y ≠ 0) (hy : herm frob y y = 0) (a b : K) :
    tqU (lineVec x a) * tqU (lineVec y b) = tqU (lineVec y b) * tqU (lineVec x a) ↔
      herm frob x y = 0 := by
  rw [tqU_commute_iff (by omega) (lineVec_ne_zero hx0 a) (isotropic_lineVec hx a)
    (lineVec_ne_zero hy0 b) (isotropic_lineVec hy b), herm_lineVec_eq]

theorem tqU_lineVec_mem_localClass (hn : 1 ≤ n) {x : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (a : K) :
    tqU (lineVec x a) ∈ LocalClass (DU (n + 2)) (tqU (v₀ n)) := by
  obtain ⟨h1, h2, h3, h4⟩ := lineVec_mem_starVec hx0 hx a
  exact (tqU_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ h1 h2).2 ⟨h3, h4⟩

theorem tqU_mul_mul_lineVec {x y : Fin n → K} (hx : herm frob x x = 0) (hy : herm frob y y = 0)
    (a b : K) :
    tqU (lineVec x a) * tqU (lineVec y b) * tqU (lineVec x a) =
      tqU (lineVec (y + herm frob x y • x) (b + herm frob x y * a)) := by
  rw [tqU_mul_tqU_mul_tqU (isotropic_lineVec hx a) (isotropic_lineVec hy b), tvU_smul_lineVec hx]

end Model

variable {H : Type} [Group H] {E μ : Set H}

theorem commute_iff_of_isTwin {a a' b b' : H} (ha : IsTwin E a a') (hb : IsTwin E b b') :
    a' * b' = b' * a' ↔ a * b = b * a := by
  have h1 := ha.2.2.2 b hb.1
  have h2 := hb.2.2.2 a' ha.2.1
  rw [← h2, eq_comm (a := a' * b), ← h1, eq_comm]

theorem isTwin_mul_mul_left (hP : Pair H E) {t a b : H} (ht : t ∈ E) (h : IsTwin E a b) :
    IsTwin E (t * a * t) (t * b * t) := by
  have := isTwin_conj hP t h
  rwa [Pair.inv_eq hP ht] at this

@[expose] def vecH (E μ : Set H) (f : H) : SecModule E μ := by
  classical exact if h : f ∈ E ∧ f ∉ μ then vec ⟨f, h⟩ else 0

open Classical in
@[expose] def xr (E μ : Set H) (e : H) : H :=
  if e ∈ μ then Classical.epsilon fun f => f ∈ E ∧ f ∉ μ ∧ IsTwin E e f else e

@[expose] def ht (μ : Set H) (e : H) : K := by
  classical exact if e ∈ μ then 0 else 1

omit [Group H] in
theorem ht_of_mem {e : H} (h : e ∈ μ) : ht μ e = 0 := by
  unfold ht; split_ifs; rfl

omit [Group H] in
theorem ht_of_notMem {e : H} (h : e ∉ μ) : ht μ e = 1 := by
  unfold ht; split_ifs; rfl

theorem xr_of_notMem {e : H} (h : e ∉ μ) : xr E μ e = e := by
  unfold xr; split_ifs; rfl

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP h4

theorem fib_nonempty {s : H} (hs : s ∈ μ) : ∃ f : XT E μ, IsTwin E s f := by
  have h3 := hμ.ncard_twinClass_diff hP h4 (hμ.subset hs)
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := twinClass E s \ μ) (by omega)
  exact ⟨⟨x, hx.1.2.1, hx.2⟩, hx.1⟩

theorem xr_spec {e : H} (he : e ∈ E) : xr E μ e ∈ E ∧ xr E μ e ∉ μ ∧ IsTwin E e (xr E μ e) := by
  unfold xr
  split_ifs with h
  · obtain ⟨f, hf⟩ := hμ.fib_nonempty hP h4 h
    exact Classical.epsilon_spec (p := fun f => f ∈ E ∧ f ∉ μ ∧ IsTwin E e f)
      ⟨f, f.2.1, f.2.2, hf⟩
  · exact ⟨he, h, isTwin_refl he⟩

@[expose] def xrT {e : H} (he : e ∈ E) : XT E μ :=
  ⟨xr E μ e, (hμ.xr_spec hP h4 he).1, (hμ.xr_spec hP h4 he).2.1⟩

theorem isTwin_xr {e : H} (he : e ∈ E) : IsTwin E e (xr E μ e) := (hμ.xr_spec hP h4 he).2.2

theorem eq_or_eq_or_eq_jmap {f g : XT E μ} (h : IsTwin E f g) :
    g = f ∨ g = hμ.jmap hP h4 f ∨ g = hμ.jmap hP h4 (hμ.jmap hP h4 f) := by
  have hS := hμ.ncard_twinClass_diff hP h4 f.2.1
  have hj := hμ.isTwin_jmap hP h4 f
  have hjj := isTwin_trans hj (hμ.isTwin_jmap hP h4 _)
  rcases eq_or_eq_or_eq_of_ncard_eq_three hS (a := (f : H)) (b := (hμ.jmap hP h4 f : H))
    (c := (hμ.jmap hP h4 (hμ.jmap hP h4 f) : H)) (x := (g : H))
    ⟨self_mem_twinClass f.2.1, f.2.2⟩ ⟨hj, (hμ.jmap hP h4 f).2.2⟩ ⟨hjj, (hμ.jmap hP h4 _).2.2⟩
    (fun e => hμ.jmap_ne hP h4 f (Subtype.ext e.symm))
    (fun e => hμ.jmap_jmap_ne hP h4 f (Subtype.ext e.symm))
    (fun e => hμ.jmap_ne hP h4 _ (Subtype.ext e.symm)) ⟨h, g.2.2⟩ with e | e | e
  · exact Or.inl (Subtype.ext e)
  · exact Or.inr (Or.inl (Subtype.ext e))
  · exact Or.inr (Or.inr (Subtype.ext e))

theorem not_bform_eq_zero_and (f g : XT E μ) (hfg : (f : H) * g ≠ g * f) :
    ¬ (bform μ (f : H) g = 0 ∧ bform μ (hμ.jmap hP h4 f : H) g = 0) := by
  rintro ⟨h1, h2⟩
  have hgf : (g : H) * f ≠ f * g := fun e => hfg e.symm
  have hj := hμ.isTwin_jmap hP h4 f
  have hjg : (hμ.jmap hP h4 f : H) * g ≠ g * hμ.jmap hP h4 f :=
    not_commute_of_isTwin hj g.2.1 hfg
  have hgj : (g : H) * hμ.jmap hP h4 f ≠ hμ.jmap hP h4 f * g := fun e => hjg e.symm
  rw [bform_comm hP f.2.1 g.2.1, hμ.bform_eq_zero_iff_mate hP g.2.1 g.2.2 f.2.1 f.2.2 hgf] at h1
  rw [bform_comm hP (hμ.jmap hP h4 f).2.1 g.2.1, hμ.bform_eq_zero_iff_mate hP g.2.1 g.2.2
    (hμ.jmap hP h4 f).2.1 (hμ.jmap hP h4 f).2.2 hgj,
    hμ.mate_congr hP g.2.1 g.2.2 f.2.1 hgf hj, h1] at h2
  exact hμ.jmap_ne hP h4 f (Subtype.ext h2.symm)

structure Coords (N : ℕ) where
  ξ : SecModule E μ ≃+ (Fin N → K)
  map_jmod : ∀ v, ξ (hμ.jmod hP h4 v) = ω • ξ v
  herm_eq : ∀ u v, herm frob (ξ u) (ξ v) = hform (hμ.jmod hP h4) (secForm hP) u v

theorem exists_coords : ∃ N, Nonempty (hμ.Coords hP h4 N) := by
  obtain ⟨N, ξ, h1, h2⟩ := hμ.exists_hermEquiv hP h4
  exact ⟨N, ⟨⟨ξ, h1, h2⟩⟩⟩

namespace Coords

variable {hμ hP h4} {N : ℕ} (C : hμ.Coords hP h4 N)

@[expose] def xv (f : XT E μ) : Fin N → K := C.ξ (vec f)

theorem herm_xv (f g : XT E μ) : herm frob (C.xv f) (C.xv g) =
    eF4 (F4.ω * toF4 (bform μ (f : H) g) + toF4 (bform μ (hμ.jmap hP h4 f : H) g)) := by
  rw [xv, xv, C.herm_eq, hform, hF4, secForm_vec, hμ.jmod_vec hP h4, secForm_vec]

theorem xv_jmap (f : XT E μ) : C.xv (hμ.jmap hP h4 f) = ω • C.xv f := by
  rw [xv, xv, ← hμ.jmod_vec hP h4, C.map_jmod]

theorem herm_xv_eq_zero_iff (f g : XT E μ) :
    herm frob (C.xv f) (C.xv g) = 0 ↔ (f : H) * g = g * f := by
  rw [C.herm_xv, ← map_zero eF4, eF4_inj, omega_toF4_eq_zero_iff]
  constructor
  · intro h
    by_contra hfg
    exact hμ.not_bform_eq_zero_and hP h4 f g hfg h
  · intro h
    have hj := hμ.isTwin_jmap hP h4 f
    exact ⟨bform_of_commute h, bform_of_commute ((hj.2.2.2 g g.2.1).1 h.symm).symm⟩

theorem herm_xv_eq_one_iff (f g : XT E μ) :
    herm frob (C.xv f) (C.xv g) = 1 ↔ (f : H) * g ≠ g * f ∧ (f : H) * g * f ∈ μ := by
  rw [C.herm_xv, ← map_one eF4, eF4_inj, omega_toF4_eq_one_iff]
  have hj := hμ.isTwin_jmap hP h4 f
  constructor
  · rintro ⟨h1, h2⟩
    have hjg : (hμ.jmap hP h4 f : H) * g ≠ g * hμ.jmap hP h4 f := (bform_eq_one_iff.1 h2).1
    have hfg : (f : H) * g ≠ g * f := fun e => hjg ((hj.2.2.2 g g.2.1).1 e.symm).symm
    refine ⟨hfg, ?_⟩
    by_contra hm
    rw [bform_of_not_mem hfg hm] at h1
    exact one_ne_zero h1
  · rintro ⟨hfg, hm⟩
    refine ⟨bform_of_mem hm, ?_⟩
    rcases Symplectic.zmod_two_cases (bform μ (hμ.jmap hP h4 f : H) g) with h | h
    · exact absurd ⟨bform_of_mem hm, h⟩ (hμ.not_bform_eq_zero_and hP h4 f g hfg)
    · exact h

theorem herm_xv_self (f : XT E μ) : herm frob (C.xv f) (C.xv f) = 0 :=
  (C.herm_xv_eq_zero_iff f f).2 rfl

theorem xv_ne_zero (hZ : Subgroup.center H = ⊥) (f : XT E μ) : C.xv f ≠ 0 := by
  intro h0
  have hcomm : ∀ g : XT E μ, (f : H) * g = g * f := fun g =>
    (C.herm_xv_eq_zero_iff f g).1 (by rw [h0, herm_zero_left])
  have hall : ∀ x ∈ E, (f : H) * x * (f : H)⁻¹ = x := by
    intro x hx
    have hxf : f * x = x * f := by
      by_cases hxμ : x ∈ μ
      · obtain ⟨r, hr⟩ := hμ.fib_nonempty hP h4 hxμ
        exact (hr.2.2.2 f f.2.1).2 (hcomm r)
      · exact hcomm ⟨x, hx, hxμ⟩
    rw [hxf, mul_inv_cancel_right]
  exact Pair.ne_one hP f.2.1 (Pair.eq_one_of_forall_conj_eq hP hZ hall)

theorem isTwin_of_xv_eq_smul {f g : XT E μ} {c : K} (hc : c ≠ 0) (h : C.xv g = c • C.xv f) :
    IsTwin E (f : H) g := by
  have key : ∀ z : XT E μ, ((f : H) * z = z * f ↔ (g : H) * z = z * g) := fun z => by
    rw [← C.herm_xv_eq_zero_iff, ← C.herm_xv_eq_zero_iff, h, herm_smul_left, mul_eq_zero,
      or_iff_right (frob_ne_zero hc)]
  refine ⟨f.2.1, g.2.1, ?_, fun x hx => ?_⟩
  · rw [← C.herm_xv_eq_zero_iff, h, herm_smul_right, C.herm_xv_self, mul_zero]
  · by_cases hxμ : x ∈ μ
    · obtain ⟨r, hr⟩ := hμ.fib_nonempty hP h4 hxμ
      have h1 := hr.2.2.2 f f.2.1
      have h2 := hr.2.2.2 g g.2.1
      exact eq_comm.trans (h1.trans ((key r).trans (h2.symm.trans eq_comm)))
    · have := key ⟨x, hx, hxμ⟩
      rw [eq_comm, this, eq_comm]

theorem exists_xv_eq_smul {f g : XT E μ} (h : IsTwin E (f : H) g) :
    ∃ c : K, c ≠ 0 ∧ C.xv g = c • C.xv f := by
  rcases hμ.eq_or_eq_or_eq_jmap hP h4 h with rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, (one_smul K _).symm⟩
  · exact ⟨ω, omega_ne_zero, C.xv_jmap f⟩
  · exact ⟨ω * ω, mul_ne_zero omega_ne_zero omega_ne_zero, by
      rw [C.xv_jmap, C.xv_jmap, smul_smul]⟩

theorem exists_xv_eq_smul' (f : XT E μ) {c : K} (hc : c ≠ 0) :
    ∃ g : XT E μ, IsTwin E (f : H) g ∧ C.xv g = c • C.xv f := by
  have hj := hμ.isTwin_jmap hP h4 f
  rcases K_cases c hc with rfl | rfl | rfl
  · exact ⟨f, isTwin_refl f.2.1, (one_smul K _).symm⟩
  · exact ⟨_, hj, C.xv_jmap f⟩
  · exact ⟨_, isTwin_trans hj (hμ.isTwin_jmap hP h4 _), by
      rw [C.xv_jmap, C.xv_jmap, smul_smul]⟩

theorem eq_of_xv_eq (hZ : Subgroup.center H = ⊥) {f g : XT E μ} (h : IsTwin E (f : H) g)
    (hxv : C.xv f = C.xv g) : f = g := by
  have h0 := C.xv_ne_zero hZ f
  rcases hμ.eq_or_eq_or_eq_jmap hP h4 h with rfl | rfl | rfl
  · rfl
  · rw [C.xv_jmap] at hxv
    exact absurd (eq_of_smul_eq_smul h0 ((one_smul K _).trans hxv)).symm omega_ne_one
  · rw [C.xv_jmap, C.xv_jmap, smul_smul] at hxv
    exact absurd (eq_of_smul_eq_smul h0 ((one_smul K _).trans hxv)).symm omega_mul_omega_ne_one

theorem xv_conj {s : H} (hs : s ∈ μ) (f : XT E μ) (hsf : s * f ≠ f * s) {r : XT E μ}
    (hr : IsTwin E s r) :
    C.xv ⟨s * f * s, Pair.mul_mul_mem hP (hμ.subset hs) f.2.1, hμ.conj_notMem hP hs f.2.2⟩ =
      C.xv f + herm frob (C.xv r) (C.xv f) • C.xv r := by
  have hfs : (f : H) * s ≠ s * f := fun e => hsf e.symm
  have hsE := hμ.subset hs
  let m : XT E μ := ⟨mate E μ f s, hμ.mate_mem hP f.2.1 f.2.2 hsE hfs,
    hμ.mate_notMem hP f.2.1 f.2.2 hsE hfs⟩
  have h1 : C.xv ⟨s * f * s, Pair.mul_mul_mem hP hsE f.2.1, hμ.conj_notMem hP hs f.2.2⟩ =
      C.xv f + C.xv m := by
    unfold xv
    rw [hμ.vec_conj hP h4 hs f hsf, map_add]
  rw [h1]
  congr 1
  have hmr : IsTwin E (r : H) m :=
    isTwin_trans (isTwin_symm hr) (hμ.isTwin_mate hP f.2.1 f.2.2 hsE hfs)
  obtain ⟨c, hc0, hc⟩ := C.exists_xv_eq_smul hmr
  have hmf : (m : H) * f ≠ f * m := fun e =>
    hμ.mate_not_commute hP f.2.1 f.2.2 hsE hfs e.symm
  have hone : herm frob (C.xv m) (C.xv f) = 1 := by
    rw [C.herm_xv_eq_one_iff]
    refine ⟨hmf, ?_⟩
    rw [Pair.mul_mul_eq hP m.2.1 f.2.1 hmf]
    exact hμ.mul_mate_mul_mem hP f.2.1 f.2.2 hsE hfs
  rw [hc, herm_smul_left] at hone
  have hval : herm frob (C.xv r) (C.xv f) = c :=
    mul_left_cancel₀ (frob_ne_zero hc0) (hone.trans (frob_mul_self hc0).symm)
  rw [hc, hval]

@[expose] def cv (e : H) : Fin N → K := C.ξ (vecH E μ (xr E μ e))

theorem cv_eq_xv {e : H} (he : e ∈ E) : C.cv e = C.xv (hμ.xrT hP h4 he) := by
  unfold cv vecH
  rw [dite_eq_left ⟨(hμ.xr_spec hP h4 he).1, (hμ.xr_spec hP h4 he).2.1⟩]
  rfl

theorem cv_of_notMem {f : H} (hf : f ∈ E) (hfμ : f ∉ μ) : C.cv f = C.xv ⟨f, hf, hfμ⟩ := by
  rw [C.cv_eq_xv hf]
  congr 1
  exact Subtype.ext (xr_of_notMem hfμ)

theorem herm_cv_eq_zero_iff {a b : H} (ha : a ∈ E) (hb : b ∈ E) :
    herm frob (C.cv a) (C.cv b) = 0 ↔ a * b = b * a := by
  rw [C.cv_eq_xv ha, C.cv_eq_xv hb, C.herm_xv_eq_zero_iff]
  exact commute_iff_of_isTwin (hμ.isTwin_xr hP h4 ha) (hμ.isTwin_xr hP h4 hb)

theorem cv_ne_zero (hZ : Subgroup.center H = ⊥) {a : H} (ha : a ∈ E) : C.cv a ≠ 0 := by
  rw [C.cv_eq_xv ha]
  exact C.xv_ne_zero hZ _

theorem herm_cv_self {a : H} (ha : a ∈ E) : herm frob (C.cv a) (C.cv a) = 0 :=
  (C.herm_cv_eq_zero_iff ha ha).2 rfl

theorem isTwin_iff_cv {a b : H} (ha : a ∈ E) (hb : b ∈ E) :
    IsTwin E a b ↔ ∃ c : K, c ≠ 0 ∧ C.cv b = c • C.cv a := by
  rw [C.cv_eq_xv ha, C.cv_eq_xv hb]
  have hxa := hμ.isTwin_xr hP h4 ha
  have hxb := hμ.isTwin_xr hP h4 hb
  constructor
  · intro h
    exact C.exists_xv_eq_smul (isTwin_trans (isTwin_trans (isTwin_symm hxa) h) hxb)
  · rintro ⟨c, hc, h⟩
    exact isTwin_trans (isTwin_trans hxa (C.isTwin_of_xv_eq_smul hc h)) (isTwin_symm hxb)

theorem herm_cv_eq_one_iff {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hgμ : g ∉ μ) :
    herm frob (C.cv f) (C.cv g) = 1 ↔ f * g ≠ g * f ∧ f * g * f ∈ μ := by
  rw [C.cv_of_notMem hf hfμ, C.cv_of_notMem hg hgμ, C.herm_xv_eq_one_iff]

theorem eq_of_cv_eq (hZ : Subgroup.center H = ⊥) {a b : H} (ha : a ∈ E) (haμ : a ∉ μ)
    (hb : b ∈ E) (hbμ : b ∉ μ) (h : IsTwin E a b) (hcv : C.cv a = C.cv b) : a = b := by
  rw [C.cv_of_notMem ha haμ, C.cv_of_notMem hb hbμ] at hcv
  exact congrArg Subtype.val (C.eq_of_xv_eq hZ (f := ⟨a, ha, haμ⟩) (g := ⟨b, hb, hbμ⟩) h hcv)

theorem cv_conj {t a : H} (ht : t ∈ μ) (ha : a ∈ E) (haμ : a ∉ μ) (hta : t * a ≠ a * t) :
    C.cv (t * a * t) = C.cv a + herm frob (C.cv t) (C.cv a) • C.cv t := by
  rw [C.cv_of_notMem (Pair.mul_mul_mem hP (hμ.subset ht) ha) (hμ.conj_notMem hP ht haμ),
    C.cv_of_notMem ha haμ, C.cv_eq_xv (hμ.subset ht)]
  exact C.xv_conj ht ⟨a, ha, haμ⟩ hta (hμ.isTwin_xr hP h4 (hμ.subset ht))

theorem cv_conj_sec {t t' : H} (ht : t ∈ μ) (ht' : t' ∈ μ) (htt : t * t' ≠ t' * t) :
    ∃ c : K, c ≠ 0 ∧
      C.cv (t * t' * t) = c • (C.cv t' + herm frob (C.cv t) (C.cv t') • C.cv t) := by
  have htE := hμ.subset ht
  have ht'E := hμ.subset ht'
  obtain ⟨hrE, hrμ, hr⟩ := hμ.xr_spec hP h4 ht'E
  have htr : t * xr E μ t' ≠ xr E μ t' * t := not_commute_of_isTwin' hr htE htt
  have h1 := C.cv_conj ht hrE hrμ htr
  have hcr : C.cv (xr E μ t') = C.cv t' := by
    rw [C.cv_of_notMem hrE hrμ, C.cv_eq_xv ht'E]
    rfl
  have htw : IsTwin E (t * t' * t) (t * xr E μ t' * t) := isTwin_mul_mul_left hP htE hr
  obtain ⟨c, hc0, hc⟩ := (C.isTwin_iff_cv (Pair.mul_mul_mem hP htE ht'E)
    (Pair.mul_mul_mem hP htE hrE)).1 htw
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [← hcr, ← h1, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem cv_conj_of_mem {f t : H} (hf : f ∈ E) (hfμ : f ∉ μ) (ht : t ∈ μ)
    (hft : f * t ≠ t * f) :
    C.cv (f * t * f) = (herm frob (C.cv f) (C.cv t))⁻¹ • C.cv t + C.cv f := by
  have htE := hμ.subset ht
  have htf : t * f ≠ f * t := fun e => hft e.symm
  have hne : herm frob (C.cv f) (C.cv t) ≠ 0 := fun h =>
    hft ((C.herm_cv_eq_zero_iff hf htE).1 h)
  rw [Pair.mul_mul_eq hP hf htE hft, C.cv_conj ht hf hfμ htf, add_comm,
    herm_conj frob frob_frob (C.cv f) (C.cv t), frob_eq_inv hne]

theorem cv_conj_of_mul_mul_mem {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hfg : f * g ≠ g * f)
    (h : f * g * f ∈ μ) : ∃ c : K, c ≠ 0 ∧ C.cv (f * g * f) = c • (C.cv g + C.cv f) := by
  have hff := Pair.mul_self hP hf
  have hfu : f * (f * g * f) ≠ f * g * f * f := by
    intro e
    apply hfg
    have h1 : f * (f * g * f) = g * f := by
      rw [← mul_assoc, ← mul_assoc, hff, one_mul]
    have h2 : f * g * f * f = f * g := by rw [mul_assoc, hff, mul_one]
    rw [h1, h2] at e
    exact e.symm
  have hg' : f * (f * g * f) * f = g := by
    rw [← mul_assoc, ← mul_assoc, hff, one_mul, mul_assoc, hff, mul_one]
  have h3 := C.cv_conj_of_mem hf hfμ h hfu
  rw [hg'] at h3
  have hne : herm frob (C.cv f) (C.cv (f * g * f)) ≠ 0 := fun e =>
    hfu ((C.herm_cv_eq_zero_iff hf (hμ.subset h)).1 e)
  refine ⟨herm frob (C.cv f) (C.cv (f * g * f)), hne, ?_⟩
  rw [h3, add_assoc, vadd_self, add_zero, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem cv_conj_of_not_mem (hZ : Subgroup.center H = ⊥) {g f : H} (hg : g ∈ E) (hgμ : g ∉ μ)
    (hf : f ∈ E) (hfμ : f ∉ μ) (hgf : g * f ≠ f * g) (h : g * f * g ∉ μ) :
    C.cv (g * f * g) = (1 + herm frob (C.cv g) (C.cv f))⁻¹ •
      (C.cv f + herm frob (C.cv g) (C.cv f) • C.cv g) := by
  obtain ⟨t, ht, hgt, htg⟩ : ∃ t, t ∈ μ ∧ IsTwin E g t ∧ t ≠ g :=
    ⟨sec E μ g, hμ.sec_mem hg, hμ.isTwin_sec hg, hμ.sec_ne hgμ hg⟩
  obtain ⟨s, hs, hfs⟩ : ∃ s, s ∈ μ ∧ IsTwin E f s := ⟨sec E μ f, hμ.sec_mem hf, hμ.isTwin_sec hf⟩
  have htE := hμ.subset ht
  have hsE := hμ.subset hs
  obtain ⟨cg, hcg0, hcg⟩ := (C.isTwin_iff_cv htE hg).1 (isTwin_symm hgt)
  obtain ⟨cf, hcf0, hcf⟩ := (C.isTwin_iff_cv hsE hf).1 (isTwin_symm hfs)
  have hgs : g * s ≠ s * g := not_commute_of_isTwin' hfs hg hgf
  have hsg : s * g ≠ g * s := fun e => hgs e.symm
  have hts : t * s ≠ s * t := not_commute_of_isTwin hgt hsE hgs
  have htf : t * f ≠ f * t := not_commute_of_isTwin hgt hf hgf
  have htgc : t * g = g * t := hgt.2.2.1.symm
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀, herm frob (C.cv g) (C.cv s) = m₀ := ⟨_, rfl⟩
  have hm₀ : m₀ ≠ 0 := fun e => hgs ((C.herm_cv_eq_zero_iff hg hsE).1 (hm₀def.trans e))
  have hts' : herm frob (C.cv t) (C.cv s) = m₀ * cg := by
    have e1 : m₀ = frob cg * herm frob (C.cv t) (C.cv s) := by
      rw [← hm₀def, hcg, herm_smul_left]
    rw [e1, frob_eq_inv hcg0, mul_comm cg⁻¹, mul_assoc, inv_mul_cancel₀ hcg0, mul_one]
  have hlam : herm frob (C.cv g) (C.cv f) = cf * m₀ := by
    rw [hcf, herm_smul_right, hm₀def]
  have huE : s * g * s ∈ E := Pair.mul_mul_mem hP hsE hg
  have huμ : s * g * s ∉ μ := hμ.conj_notMem hP hs hgμ
  have hu : C.cv (s * g * s) = C.cv g + m₀⁻¹ • C.cv s := by
    rw [C.cv_conj hs hg hgμ hsg, herm_conj frob frob_frob (C.cv g) (C.cv s), hm₀def,
      frob_eq_inv hm₀]
  have hgu : g * (s * g * s) ≠ s * g * s * g := by
    rw [Pair.mul_mul_eq hP hsE hg hsg]
    intro e
    apply hgs
    have h1 : g * (g * s * g) = s * g := by
      rw [← mul_assoc, ← mul_assoc, Pair.mul_self hP hg, one_mul]
    have h2 : g * s * g * g = g * s := by rw [mul_assoc, Pair.mul_self hP hg, mul_one]
    rw [h1, h2] at e
    exact e.symm
  have htu : t * (s * g * s) ≠ s * g * s * t := not_commute_of_isTwin hgt huE hgu
  have hwE : t * (s * g * s) * t ∈ E := Pair.mul_mul_mem hP htE huE
  have hwμ : t * (s * g * s) * t ∉ μ := hμ.conj_notMem hP ht huμ
  have hw : C.cv (t * (s * g * s) * t) = m₀⁻¹ • C.cv s := by
    have h0 : herm frob (C.cv t) (C.cv g) = 0 := (C.herm_cv_eq_zero_iff htE hg).2 htgc
    rw [C.cv_conj ht huE huμ htu, hu, herm_add_right, herm_smul_right, h0, hts', zero_add, hcg,
      ← mul_assoc, inv_mul_cancel₀ hm₀, one_mul, add_comm (cg • C.cv t), add_assoc, vadd_self,
      add_zero]
  have hw' : t * (s * g * s) * t = t * g * s * (t * g) := by
    rw [Pair.mul_mul_eq hP hsE hg hsg,
      show t * g * s * (t * g) = t * g * s * (g * t) from congrArg (t * g * s * ·) htgc]
    group
  have hsw : IsTwin E s (t * (s * g * s) * t) := by
    rw [hw']
    exact (Pair.isTwin_conj_mul_mul hP (isTwin_symm hgt) htg hsE hts).1
  obtain ⟨hvtw, hvne⟩ := Pair.isTwin_conj_mul_mul hP (isTwin_symm hgt) htg hf htf
  have hv' : t * g * f * (t * g) = t * (g * f * g) * t := by
    rw [show t * g * f * (t * g) = t * g * f * (g * t) from congrArg (t * g * f * ·) htgc]
    group
  have hgfg : g * f * g = t * (t * g * f * (t * g)) * t := by
    rw [hv', Pair.mul_mul_mul_mul hP htE]
  obtain ⟨v, hvdef⟩ : ∃ v, t * g * f * (t * g) = v := ⟨_, rfl⟩
  rw [hvdef] at hvtw hvne hgfg
  have hvE : v ∈ E := hvtw.2.1
  have hvμ : v ∉ μ := fun hvm => h (by rw [hgfg]; exact hμ.mul_mul_mem t ht v hvm)
  have hsv : IsTwin E s v := isTwin_trans (isTwin_symm hfs) hvtw
  obtain ⟨c', hc'0, hc'⟩ := (C.isTwin_iff_cv hsE hvE).1 hsv
  have hkk : t * g * (t * g) = 1 := by
    rw [show t * g * (t * g) = t * g * (g * t) from congrArg (t * g * ·) htgc]
    rw [show t * g * (g * t) = t * (g * g) * t by group, Pair.mul_self hP hg, mul_one,
      Pair.mul_self hP htE]
  have hfw : f ≠ t * (s * g * s) * t := by
    intro e
    apply hvμ
    rw [← hvdef, e, hw']
    have e2 : t * g * (t * g * s * (t * g)) * (t * g) =
        t * g * (t * g) * s * (t * g * (t * g)) := by
      group
    rw [e2, hkk, one_mul, mul_one]
    exact hs
  have hvw : v ≠ t * (s * g * s) * t := by
    intro e
    rw [hw', ← hvdef] at e
    exact hfμ (mul_left_cancel (mul_right_cancel e) ▸ hs)
  have hcf_c' : cf ≠ c' := fun e => hvne (C.eq_of_cv_eq hZ hf hfμ hvE hvμ hvtw
    (by rw [hcf, hc', e])).symm
  have hcf_m : cf ≠ m₀⁻¹ := fun e => hfw (C.eq_of_cv_eq hZ hf hfμ hwE hwμ
    (isTwin_trans hfs hsw) (by rw [hcf, hw, e]))
  have hc'_m : c' ≠ m₀⁻¹ := fun e => hvw (C.eq_of_cv_eq hZ hvE hvμ hwE hwμ
    (isTwin_trans (isTwin_symm hsv) hsw) (by rw [hc', hw, e]))
  have hc'eq : c' = cf + m₀⁻¹ :=
    K_eq_add cf m₀⁻¹ c' hcf0 (inv_ne_zero hm₀) hc'0 hcf_m hcf_c' hc'_m.symm
  have htv : t * v ≠ v * t := not_commute_of_isTwin' hsv htE hts
  have hlam1 : cf * m₀ ≠ 1 := fun e =>
    h ((C.herm_cv_eq_one_iff hg hgμ hf hfμ).1 (hlam.trans e)).2
  have hc'' : c' = (1 + cf * m₀)⁻¹ * cf := hc'eq.trans (K_add_inv cf m₀ hcf0 hm₀ hlam1)
  rw [hgfg, C.cv_conj ht hvE hvμ htv, hc', herm_smul_right, hts', hlam, hcf, hcg, hc'']
  module

@[expose] def mvec (e : H) : Fin (N + 2) → K := lineVec (C.cv e) (ht μ e)

@[expose] def toModel (e : H) : U2 (N + 2) := tqU (C.mvec e)

theorem toModel_of_mem {s : H} (hs : s ∈ μ) : C.toModel s = tqU (ι N (C.cv s)) := by
  rw [toModel, mvec, ht_of_mem hs, lineVec_zero]

theorem toModel_of_notMem {f : H} (hf : f ∉ μ) : C.toModel f = tqU (lineVec (C.cv f) 1) := by
  rw [toModel, mvec, ht_of_notMem hf]

theorem toModel_mem (hZ : Subgroup.center H = ⊥) (hN : 1 ≤ N) {e : H} (he : e ∈ E) :
    C.toModel e ∈ LocalClass (DU (N + 2)) (tqU (v₀ N)) :=
  tqU_lineVec_mem_localClass hN (C.cv_ne_zero hZ he) (C.herm_cv_self he) _

theorem toModel_commute_iff (hZ : Subgroup.center H = ⊥) (hN : 1 ≤ N) {a b : H} (ha : a ∈ E)
    (hb : b ∈ E) : C.toModel a * C.toModel b = C.toModel b * C.toModel a ↔ a * b = b * a := by
  rw [toModel, toModel, mvec, mvec, tqU_lineVec_commute_iff hN (C.cv_ne_zero hZ ha)
    (C.herm_cv_self ha) (C.cv_ne_zero hZ hb) (C.herm_cv_self hb), C.herm_cv_eq_zero_iff ha hb]

theorem toModel_mul_mul (hZ : Subgroup.center H = ⊥) {a b : H} (ha : a ∈ E) (hb : b ∈ E) :
    C.toModel (a * b * a) = C.toModel a * C.toModel b * C.toModel a := by
  have habE := Pair.mul_mul_mem hP ha hb
  rw [toModel, toModel, toModel, mvec, mvec, mvec,
    tqU_mul_mul_lineVec (C.herm_cv_self ha) (C.herm_cv_self hb)]
  by_cases hab : a * b = b * a
  · have e1 : a * b * a = b := by rw [hab, mul_assoc, Pair.mul_self hP ha, mul_one]
    rw [e1, (C.herm_cv_eq_zero_iff ha hb).2 hab, zero_smul, add_zero, zero_mul, add_zero]
  suffices hsuff : ∃ c : K, c ≠ 0 ∧
      lineVec (C.cv b + herm frob (C.cv a) (C.cv b) • C.cv a)
        (ht μ b + herm frob (C.cv a) (C.cv b) * ht μ a) =
        c • lineVec (C.cv (a * b * a)) (ht μ (a * b * a)) by
    obtain ⟨c, hc, he⟩ := hsuff
    rw [he, tqU_smul (isotropic_lineVec (C.herm_cv_self habE) _) hc]
  have hl0 : herm frob (C.cv a) (C.cv b) ≠ 0 := fun e => hab ((C.herm_cv_eq_zero_iff ha hb).1 e)
  by_cases haμ : a ∈ μ <;> by_cases hbμ : b ∈ μ
  · obtain ⟨c, hc, he⟩ := C.cv_conj_sec haμ hbμ hab
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [ht_of_mem (hμ.mul_mul_mem a haμ b hbμ), ht_of_mem haμ, ht_of_mem hbμ, he, smul_lineVec,
      smul_smul, inv_mul_cancel₀ hc, one_smul, mul_zero, mul_zero, add_zero]
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul, ht_of_notMem (hμ.conj_notMem hP haμ hbμ), ht_of_mem haμ, ht_of_notMem hbμ,
      C.cv_conj haμ hb hbμ hab, mul_zero, add_zero]
  · refine ⟨herm frob (C.cv a) (C.cv b), hl0, ?_⟩
    have hab' : a * b * a ∉ μ := by
      rw [Pair.mul_mul_eq hP ha hb hab]
      exact hμ.conj_notMem hP hbμ haμ
    rw [ht_of_notMem hab', ht_of_mem hbμ, ht_of_notMem haμ, C.cv_conj_of_mem ha haμ hbμ hab,
      smul_lineVec, smul_add, smul_smul, mul_inv_cancel₀ hl0, one_smul, zero_add]
  · by_cases habμ : a * b * a ∈ μ
    · obtain ⟨c, hc, he⟩ := C.cv_conj_of_mul_mul_mem ha haμ hab habμ
      have hl1 : herm frob (C.cv a) (C.cv b) = 1 :=
        (C.herm_cv_eq_one_iff ha haμ hb hbμ).2 ⟨hab, habμ⟩
      refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
      rw [ht_of_mem habμ, ht_of_notMem haμ, ht_of_notMem hbμ, he, hl1, one_smul, one_mul,
        smul_lineVec, smul_smul, inv_mul_cancel₀ hc, one_smul, mul_zero, add_self_K]
    · have hl1 : herm frob (C.cv a) (C.cv b) ≠ 1 := fun e =>
        habμ ((C.herm_cv_eq_one_iff ha haμ hb hbμ).1 e).2
      have h1l : 1 + herm frob (C.cv a) (C.cv b) ≠ 0 := fun e =>
        hl1 ((one_add_eq_zero_iff _).1 e)
      refine ⟨1 + herm frob (C.cv a) (C.cv b), h1l, ?_⟩
      rw [ht_of_notMem habμ, ht_of_notMem haμ, ht_of_notMem hbμ,
        C.cv_conj_of_not_mem hZ ha haμ hb hbμ hab habμ, smul_lineVec, smul_smul,
        mul_inv_cancel₀ h1l, one_smul, mul_one, mul_one]

theorem toModel_injOn (hZ : Subgroup.center H = ⊥) (hN : 1 ≤ N) : Set.InjOn C.toModel E := by
  intro a ha b hb hab
  obtain ⟨c, hcv, hht⟩ := (tqU_lineVec_eq_iff hN (C.cv_ne_zero hZ ha) (C.herm_cv_self ha)
    (C.cv_ne_zero hZ hb) (C.herm_cv_self hb) _ _).1 hab
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcv
    exact C.cv_ne_zero hZ hb hcv
  have htw : IsTwin E a b := (C.isTwin_iff_cv ha hb).2 ⟨c, hc, hcv⟩
  by_cases haμ : a ∈ μ <;> by_cases hbμ : b ∈ μ
  · exact hμ.eq_of_isTwin a haμ b hbμ htw
  · rw [ht_of_mem haμ, ht_of_notMem hbμ, mul_zero] at hht
    exact absurd hht one_ne_zero
  · rw [ht_of_notMem haμ, ht_of_mem hbμ, mul_one] at hht
    exact absurd hht.symm hc
  · rw [ht_of_notMem haμ, ht_of_notMem hbμ, mul_one] at hht
    rw [← hht, one_smul] at hcv
    exact C.eq_of_cv_eq hZ ha haμ hb hbμ htw hcv.symm

end Coords

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
