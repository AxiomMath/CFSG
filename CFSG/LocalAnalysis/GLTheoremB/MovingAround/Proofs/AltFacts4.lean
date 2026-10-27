module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1210
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Alt
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Chev2
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Wreath

variable {D : Type*} [Group D] {p : ℕ}

abbrev Wr (D : Type*) [Group D] (p : ℕ) : Type _ :=
  RegularWreathProduct D (Multiplicative (ZMod p))

theorem left_mul_of_right {u v : Wr D p} (hu : u.right = 1) (x : Multiplicative (ZMod p)) :
    (u * v).left x = u.left x * v.left x := by
  simp [hu]

theorem left_mul (u v : Wr D p) (x : Multiplicative (ZMod p)) :
    (u * v).left x = u.left x * v.left (u.right⁻¹ * x) :=
  rfl

theorem left_inv_of_right {u : Wr D p} (hu : u.right = 1) (x : Multiplicative (ZMod p)) :
    u⁻¹.left x = (u.left x)⁻¹ := by
  simp [hu]

theorem pow_of_right {u : Wr D p} (hu : u.right = 1) (n : ℕ) :
    (u ^ n).right = 1 ∧ ∀ x, (u ^ n).left x = (u.left x) ^ n := by
  induction n with
  | zero => exact ⟨rfl, fun x => by simp⟩
  | succ n ih =>
    refine ⟨by rw [pow_succ]; simp [ih.1, hu], fun x => ?_⟩
    rw [pow_succ, left_mul_of_right ih.1, ih.2 x, pow_succ]

theorem conj_left {b u : Wr D p} (hu : u.right = 1) (x : Multiplicative (ZMod p)) :
    (b * u * b⁻¹).left x = b.left x * u.left (b.right⁻¹ * x) * (b.left x)⁻¹ := by
  simp [hu, mul_assoc]

theorem conj_right {b u : Wr D p} (hu : u.right = 1) : (b * u * b⁻¹).right = 1 := by
  simp [hu]

theorem comm_iff {a u : Wr D p} (hu : u.right = 1) :
    u * a = a * u ↔ ∀ x, u.left x * a.left x = a.left x * u.left (a.right⁻¹ * x) := by
  constructor
  · intro h x
    have := congrArg (fun w => w.left x) h
    simpa [hu] using this
  · intro h
    ext x
    · simpa [hu] using h x
    · simp [hu]

theorem gen_of_ne_one (hp : p.Prime) {σ : Multiplicative (ZMod p)} (hσ : σ ≠ 1)
    (q : Multiplicative (ZMod p)) : ∃ j : ℕ, σ ^ j = q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have htop := zpowers_eq_top_of_prime_card hcard hσ
  have hq : q ∈ Subgroup.zpowers σ := by rw [htop]; exact Subgroup.mem_top q
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.2 hq)
  exact ⟨j, hj⟩

theorem eq_one_of_comm (hp : p.Prime) {a u : Wr D p} (ha : a.right ≠ 1) (hu : u.right = 1)
    (hc : u * a = a * u) {x0 : Multiplicative (ZMod p)} (h0 : u.left x0 = 1) : u = 1 := by
  have hc' := (comm_iff hu).1 hc
  have key : ∀ j : ℕ, u.left (a.right ^ j * x0) = 1 := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have h1 := hc' (a.right ^ (j + 1) * x0)
      have h2 : a.right⁻¹ * (a.right ^ (j + 1) * x0) = a.right ^ j * x0 := by
        rw [pow_succ', mul_assoc, inv_mul_cancel_left]
      rw [h2, ih, mul_one] at h1
      exact mul_right_cancel (h1.trans (one_mul _).symm)
  ext x
  · obtain ⟨j, hj⟩ := gen_of_ne_one hp ha (x * x0⁻¹)
    have := key j
    rw [hj, inv_mul_cancel_right] at this
    simpa using this
  · simpa using hu

@[expose] def projProd (F : Subgroup (Wr D p)) : Subgroup (Wr D p) where
  carrier := {w | w.right = 1 ∧ ∀ k, ∃ f ∈ F, f.right = 1 ∧ w.left k = f.left k}
  mul_mem' := by
    rintro w₁ w₂ ⟨h1r, h1⟩ ⟨h2r, h2⟩
    refine ⟨by simp [h1r, h2r], fun k => ?_⟩
    obtain ⟨f₁, hf₁, hf₁r, hk₁⟩ := h1 k
    obtain ⟨f₂, hf₂, hf₂r, hk₂⟩ := h2 k
    refine ⟨f₁ * f₂, F.mul_mem hf₁ hf₂, by simp [hf₁r, hf₂r], ?_⟩
    rw [left_mul_of_right h1r, left_mul_of_right hf₁r, hk₁, hk₂]
  one_mem' := ⟨rfl, fun _ => ⟨1, F.one_mem, rfl, rfl⟩⟩
  inv_mem' := by
    rintro w ⟨hr, h⟩
    refine ⟨by simp [hr], fun k => ?_⟩
    obtain ⟨f, hf, hfr, hk⟩ := h k
    exact ⟨f⁻¹, F.inv_mem hf, by simp [hfr],
      by rw [left_inv_of_right hr, left_inv_of_right hfr, hk]⟩

theorem mem_projProd {F : Subgroup (Wr D p)} {w : Wr D p} :
    w ∈ projProd F ↔ w.right = 1 ∧ ∀ k, ∃ f ∈ F, f.right = 1 ∧ w.left k = f.left k :=
  Iff.rfl

theorem projProd_isElemAbelian {F : Subgroup (Wr D p)} (hF : IsElemAbelian p F) :
    IsElemAbelian p (projProd F) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩
  · obtain ⟨hxr, hx⟩ := x.2
    obtain ⟨hyr, hy⟩ := y.2
    show (x : Wr D p) * y = y * x
    ext k
    · rw [left_mul_of_right hxr, left_mul_of_right hyr]
      obtain ⟨f, hf, hfr, hk⟩ := hx k
      obtain ⟨g, hg, hgr, hk'⟩ := hy k
      have hc : f * g = g * f := congrArg Subtype.val (hF.1.is_comm.comm ⟨f, hf⟩ ⟨g, hg⟩)
      have h2 := congrArg (fun w => w.left k) hc
      simp only [left_mul_of_right hfr, left_mul_of_right hgr] at h2
      rw [hk, hk', h2]
    · simp [hxr, hyr]
  · obtain ⟨hr, h⟩ := hw
    obtain ⟨hpr, hpl⟩ := pow_of_right hr p
    ext k
    · rw [hpl k]
      obtain ⟨f, hf, hfr, hk⟩ := h k
      rw [hk, ← (pow_of_right hfr p).2 k, hF.2 f hf]
    · simpa using hpr

theorem le_projProd {F : Subgroup (Wr D p)} (hFb : ∀ f ∈ F, f.right = 1) : F ≤ projProd F :=
  fun f hf => ⟨hFb f hf, fun _ => ⟨f, hf, hFb f hf, rfl⟩⟩

theorem conj_mem_projProd {F : Subgroup (Wr D p)} {b : Wr D p} (hb : ∀ f ∈ F, f * b = b * f)
    {h : Wr D p} (hh : h ∈ projProd F) : b * h * b⁻¹ ∈ projProd F := by
  obtain ⟨hr, hl⟩ := hh
  refine ⟨conj_right hr, fun k => ?_⟩
  obtain ⟨f, hf, hfr, hk⟩ := hl (b.right⁻¹ * k)
  refine ⟨f, hf, hfr, ?_⟩
  have h1 : b * f * b⁻¹ = f := by rw [← hb f hf, mul_inv_cancel_right]
  rw [conj_left hr, hk, ← conj_left hfr, h1]

theorem mem_normalizer_projProd {F : Subgroup (Wr D p)} {b : Wr D p} (hb : ∀ f ∈ F, f * b = b * f) :
    b ∈ Subgroup.normalizer ((projProd F : Subgroup (Wr D p)) : Set (Wr D p)) := by
  have hb' : ∀ f ∈ F, f * b⁻¹ = b⁻¹ * f := fun f hf =>
    (show Commute f b from hb f hf).inv_right
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_projProd hb
  · intro hh
    have := conj_mem_projProd hb' hh
    simpa [mul_assoc] using this

theorem mem_of_comm (hp : p.Prime) {F : Subgroup (Wr D p)} {b : Wr D p} (hb1 : b.right ≠ 1)
    (hFb : ∀ f ∈ F, f * b = b * f) {h : Wr D p} (hh : h ∈ projProd F) (hc : h * b = b * h) :
    h ∈ F := by
  obtain ⟨hr, hl⟩ := hh
  obtain ⟨f, hf, hfr, h1⟩ := hl 1
  have hu : (h * f⁻¹).right = 1 := by simp [hr, hfr]
  have hfb' : f⁻¹ * b = b * f⁻¹ := (show Commute f b from hFb f hf).inv_left
  have hcu : h * f⁻¹ * b = b * (h * f⁻¹) := by
    rw [mul_assoc, hfb', ← mul_assoc, hc, mul_assoc]
  have h0 : (h * f⁻¹).left 1 = 1 := by
    rw [left_mul_of_right hr, left_inv_of_right hfr, h1, mul_inv_cancel]
  have := eq_one_of_comm hp hb1 hu hcu h0
  rw [mul_inv_eq_one] at this
  rw [this]
  exact hf

theorem orderOf_eq_of_ne_one (hp : p.Prime) {σ : Multiplicative (ZMod p)} (hσ : σ ≠ 1) :
    orderOf σ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hσp : σ ^ p = 1 := by
    have := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := σ)
    rwa [hcard] at this
  exact orderOf_eq_prime hσp hσ

theorem zpow_eq_one_of_right (hp : p.Prime) {a : Wr D p} (ha : a.right ≠ 1) (hap : a ^ p = 1) {k : ℤ}
    (hk : (a ^ k).right = 1) : a ^ k = 1 := by
  have h1 : a.right ^ k = 1 := by
    have := map_zpow (RegularWreathProduct.rightHom (D := D) (Q := Multiplicative (ZMod p))) a k
    rw [RegularWreathProduct.rightHom_eq_right] at this
    rw [← this]
    exact hk
  have h2 : ((orderOf a.right : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [orderOf_eq_of_ne_one hp ha] at h2
  have h3 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
  exact orderOf_dvd_iff_zpow_eq_one.1 ((Int.natCast_dvd_natCast.2 h3).trans h2)

theorem exists_shear (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) (hFe : IsElemAbelian p F)
    {f₀ : Wr D p} (hf₀ : f₀ ∈ F) : ∃ h ∈ projProd F, h * a = f₀ * a * h := by
  have hf₀r := hFb f₀ hf₀
  let ind : Multiplicative (ZMod p) → ℕ := fun x => Classical.choose (gen_of_ne_one hp ha x)
  have hind : ∀ x, a.right ^ ind x = x := fun x => Classical.choose_spec (gen_of_ne_one hp ha x)
  let h : Wr D p := ⟨fun x => f₀.left x ^ ind x, 1⟩
  have hmem : h ∈ projProd F := by
    refine ⟨rfl, fun k => ⟨f₀ ^ ind k, F.pow_mem hf₀ _, (pow_of_right hf₀r _).1, ?_⟩⟩
    rw [(pow_of_right hf₀r _).2 k]
  refine ⟨h, hmem, ?_⟩
  have hc := (comm_iff hf₀r).1 (hFa f₀ hf₀)
  have hord := orderOf_eq_of_ne_one hp ha
  have hf₀p : ∀ x, f₀.left x ^ p = 1 := fun x => by
    rw [← (pow_of_right hf₀r p).2 x, hFe.2 f₀ hf₀]
    rfl
  ext x
  · have hr : (f₀ * a).right = a.right := by simp [hf₀r]
    rw [left_mul_of_right (show h.right = 1 from rfl), left_mul, left_mul_of_right hf₀r, hr]
    show f₀.left x ^ ind x * a.left x =
      f₀.left x * a.left x * f₀.left (a.right⁻¹ * x) ^ ind (a.right⁻¹ * x)
    set y := f₀.left x
    set c := a.left x
    set z := f₀.left (a.right⁻¹ * x)
    set n := ind (a.right⁻¹ * x)
    have hyc : y * c = c * z := hc x
    have hz : z = c⁻¹ * y * c⁻¹⁻¹ := by rw [inv_inv, mul_assoc, hyc, inv_mul_cancel_left]
    have hczn : c * z ^ n = y ^ n * c := by
      rw [hz, conj_pow, inv_inv, mul_assoc, ← mul_assoc c, mul_inv_cancel, one_mul]
    have hmod : ind x ≡ n + 1 [MOD p] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, hind x, pow_succ', hind, mul_inv_cancel_left]
    have hyo : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hf₀p x)
    have hy : y ^ ind x = y ^ (n + 1) := pow_eq_pow_iff_modEq.2 (hmod.of_dvd hyo)
    rw [mul_assoc, hczn, ← mul_assoc, ← pow_succ', hy]
  · simp [h, hf₀r]

@[expose] def single (F : Subgroup (Wr D p)) (hFb : ∀ f ∈ F, f.right = 1)
    (j : Multiplicative (ZMod p)) : ↥F →* Wr D p where
  toFun f := ⟨Pi.mulSingle j ((f : Wr D p).left j), 1⟩
  map_one' := by
    ext x
    · simp
    · rfl
  map_mul' f g := by
    have h1 : ((f * g : ↥F) : Wr D p).left j = (f : Wr D p).left j * (g : Wr D p).left j :=
      left_mul_of_right (hFb f f.2) j
    ext x
    · rw [left_mul_of_right rfl]
      simp only [h1, Pi.mulSingle_mul, Pi.mul_apply]
    · simp

theorem single_apply {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1} {j : Multiplicative (ZMod p)}
    (f : ↥F) : single F hFb j f = ⟨Pi.mulSingle j ((f : Wr D p).left j), 1⟩ :=
  rfl

theorem single_injective (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) (j : Multiplicative (ZMod p)) :
    Function.Injective (single F hFb j) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  have h1 : (f : Wr D p).left j = 1 := by
    have := congrArg (fun w => w.left j) hf
    simpa [single_apply] using this
  exact Subtype.ext (eq_one_of_comm hp ha (hFb f f.2) (hFa f f.2) h1)

theorem single_mem_projProd {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1}
    {j : Multiplicative (ZMod p)} (f : ↥F) : single F hFb j f ∈ projProd F := by
  refine ⟨rfl, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    exact ⟨f, f.2, hFb f f.2, by simp [single_apply]⟩
  · exact ⟨1, F.one_mem, rfl, by simp [single_apply, hk]⟩

theorem single_commute {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1}
    {i j : Multiplicative (ZMod p)} (hij : i ≠ j) (f g : ↥F) :
    Commute (single F hFb i f) (single F hFb j g) := by
  show single F hFb i f * single F hFb j g = single F hFb j g * single F hFb i f
  ext x
  · rw [left_mul_of_right rfl, left_mul_of_right rfl]
    simp only [single_apply]
    by_cases hx : x = i
    · subst hx
      rw [Pi.mulSingle_eq_of_ne hij, mul_one, Pi.mulSingle_eq_same, one_mul]
    · rw [Pi.mulSingle_eq_of_ne hx, one_mul, mul_one]
  · rfl

@[expose] def pair (F : Subgroup (Wr D p)) (hFb : ∀ f ∈ F, f.right = 1) {i j : Multiplicative (ZMod p)}
    (hij : i ≠ j) : ↥F × ↥F →* Wr D p :=
  (single F hFb i).noncommCoprod (single F hFb j) (single_commute hij)

theorem pair_injective (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) {i j : Multiplicative (ZMod p)}
    (hij : i ≠ j) : Function.Injective (pair F hFb hij) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨f, g⟩ hfg
  have hfg' : single F hFb i f * single F hFb j g = 1 := hfg
  have hi := congrArg (fun w => w.left i) hfg'
  have hj := congrArg (fun w => w.left j) hfg'
  simp only [left_mul_of_right (show (single F hFb i f).right = 1 from rfl)] at hi hj
  simp only [single_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij,
    Pi.mulSingle_eq_of_ne hij.symm, mul_one, one_mul, RegularWreathProduct.one_left,
    Pi.one_apply] at hi hj
  have hf : f = 1 := Subtype.ext (eq_one_of_comm hp ha (hFb f f.2) (hFa f f.2) hi)
  have hg : g = 1 := Subtype.ext (eq_one_of_comm hp ha (hFb g g.2) (hFa g g.2) hj)
  rw [hf, hg]
  rfl

theorem pair_range_le {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1} {i j : Multiplicative (ZMod p)}
    (hij : i ≠ j) : (pair F hFb hij).range ≤ projProd F := by
  rintro _ ⟨⟨f, g⟩, rfl⟩
  exact (projProd F).mul_mem (single_mem_projProd f) (single_mem_projProd g)

theorem single_range_le_pair {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1}
    {i j : Multiplicative (ZMod p)} (hij : i ≠ j) : (single F hFb i).range ≤ (pair F hFb hij).range := by
  rintro _ ⟨f, rfl⟩
  refine ⟨(f, 1), ?_⟩
  show single F hFb i f * single F hFb j 1 = single F hFb i f
  rw [map_one, mul_one]

@[expose] def coordSub (i : Multiplicative (ZMod p)) : Subgroup (Wr D p) where
  carrier := {w | w.right = 1 ∧ ∀ k, k ≠ i → w.left k = 1}
  mul_mem' := by
    rintro w₁ w₂ ⟨h1r, h1⟩ ⟨h2r, h2⟩
    exact ⟨by simp [h1r, h2r], fun k hk => by rw [left_mul_of_right h1r, h1 k hk, h2 k hk, one_mul]⟩
  one_mem' := ⟨rfl, fun _ _ => rfl⟩
  inv_mem' := by
    rintro w ⟨hr, h⟩
    exact ⟨by simp [hr], fun k hk => by rw [left_inv_of_right hr, h k hk, inv_one]⟩

theorem coordSub_comm_single {F : Subgroup (Wr D p)} {hFb : ∀ f ∈ F, f.right = 1}
    {i j : Multiplicative (ZMod p)} (hij : i ≠ j) {w : Wr D p} (hw : w ∈ coordSub i) (f : ↥F) :
    w * single F hFb j f = single F hFb j f * w := by
  obtain ⟨hr, hl⟩ := hw
  ext x
  · rw [left_mul_of_right hr, left_mul_of_right rfl]
    simp only [single_apply]
    by_cases hx : x = i
    · subst hx
      rw [Pi.mulSingle_eq_of_ne hij, mul_one, one_mul]
    · rw [hl x hx, one_mul, mul_one]
  · simp [hr, single_apply]

theorem mem_iSup_coordSub [Finite (Multiplicative (ZMod p))] {u : Wr D p} (hu : u.right = 1) :
    u ∈ ⨆ i, (coordSub i : Subgroup (Wr D p)) := by
  classical
  haveI : Fintype (Multiplicative (ZMod p)) := Fintype.ofFinite _
  suffices key : ∀ S : Finset (Multiplicative (ZMod p)), ∀ u : Wr D p, u.right = 1 →
      (∀ k, k ∉ S → u.left k = 1) → u ∈ ⨆ i, (coordSub i : Subgroup (Wr D p)) from
    key Finset.univ u hu (fun k hk => absurd (Finset.mem_univ k) hk)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro u hu h
    have : u = 1 := by
      ext x
      · exact h x (Finset.notMem_empty x)
      · exact hu
    rw [this]
    exact Subgroup.one_mem _
  | insert i S hiS ih =>
    intro u hu h
    let c : Wr D p := ⟨Pi.mulSingle i (u.left i), 1⟩
    let u' : Wr D p := ⟨fun k => if k = i then 1 else u.left k, 1⟩
    have hc : c ∈ coordSub i := ⟨rfl, fun k hk => by simp [c, hk]⟩
    have hu' : u' ∈ ⨆ i, (coordSub i : Subgroup (Wr D p)) := by
      refine ih u' rfl fun k hk => ?_
      by_cases hki : k = i
      · simp [u', hki]
      · simp only [u', hki, if_false]
        exact h k (by simp [hki, hk])
    have heq : u = c * u' := by
      ext k
      · rw [left_mul_of_right rfl]
        by_cases hki : k = i
        · subst hki
          simp [c, u']
        · simp [c, u', hki]
      · simp [c, u', hu]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem i hc) hu'

theorem mem_iSup_coordSub_sup (hp : p.Prime) {a : Wr D p} (ha : a.right ≠ 1) (w : Wr D p) :
    w ∈ (⨆ i, (coordSub i : Subgroup (Wr D p))) ⊔ Subgroup.zpowers a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := gen_of_ne_one hp ha w.right
  have hu : (w * (a ^ j)⁻¹).right = 1 := by
    have := map_pow (RegularWreathProduct.rightHom (D := D) (Q := Multiplicative (ZMod p))) a j
    rw [RegularWreathProduct.rightHom_eq_right] at this
    simp only [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right]
    rw [this, hj, mul_inv_cancel]
  have h1 := mem_iSup_coordSub (D := D) hu
  have h2 : w = (w * (a ^ j)⁻¹) * a ^ j := by rw [inv_mul_cancel_right]
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j))

theorem mem_sup_zpowers {G : Type*} [Group G] {S : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (S : Set G)) {x : G} (hx : x ∈ S ⊔ Subgroup.zpowers b) :
    ∃ s ∈ S, ∃ k : ℤ, x = s * b ^ k := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left S (Subgroup.zpowers b)
    ((Subgroup.zpowers_le).2 hb)] at hx
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨s, hs, k, rfl⟩

theorem mem_normalizer_of_comm {G : Type*} [Group G] {S : Subgroup G} {b : G}
    (hb : ∀ s ∈ S, s * b = b * s) : b ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    rw [← hb s hs, mul_inv_cancel_right]
    exact hs
  · intro hs
    have ht := hb _ hs
    have h1 : b * s = b * (b * s * b⁻¹) := by simpa [mul_assoc] using ht
    have h2 : b * s * b⁻¹ = s := (mul_left_cancel h1).symm
    rwa [h2] at hs

theorem centralizer_claim (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hap : a ^ p = 1) (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f)
    (hFe : IsElemAbelian p F) {x : Wr D p} (hx : x ∈ F ⊔ Subgroup.zpowers a)
    (hxH : x ∉ projProd F) {n : Wr D p} (hn : n ∈ projProd F ⊔ Subgroup.zpowers a)
    (hxn : x * n = n * x) : n ∈ F ⊔ Subgroup.zpowers a := by
  obtain ⟨f, hf, i, rfl⟩ := mem_sup_zpowers (mem_normalizer_of_comm hFa) hx
  obtain ⟨h, hh, j, rfl⟩ := mem_sup_zpowers (mem_normalizer_projProd hFa) hn
  have hHe := projProd_isElemAbelian hFe
  have hfH : f ∈ projProd F := le_projProd hFb hf
  have hfh : Commute f h := congrArg Subtype.val (hHe.1.is_comm.comm ⟨f, hfH⟩ ⟨h, hh⟩)
  have hfa : ∀ k : ℤ, Commute f (a ^ k) := fun k => (show Commute f a from hFa f hf).zpow_right k
  have hai : (a ^ i).right ≠ 1 := by
    intro h1
    apply hxH
    rw [zpow_eq_one_of_right hp ha hap h1, mul_one]
    exact hfH
  have hX : Commute (f * a ^ i) (h * a ^ j) := hxn
  have hXa : Commute (f * a ^ i) (a ^ j)⁻¹ :=
    ((hfa j).mul_left (Commute.zpow_zpow_self a i j)).inv_right
  have hXh : Commute (f * a ^ i) h := by
    have := hX.mul_right hXa
    rwa [mul_inv_cancel_right] at this
  have hah : Commute (a ^ i) h := by
    have := hfh.inv_left.mul_left hXh
    rwa [inv_mul_cancel_left] at this
  have hFai : ∀ g ∈ F, g * a ^ i = a ^ i * g := fun g hg =>
    (show Commute g a from hFa g hg).zpow_right i
  have hhF : h ∈ F := mem_of_comm hp hai hFai hh hah.symm
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hhF)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j))

theorem normalizer_claim (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hap : a ^ p = 1) (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f)
    (hFe : IsElemAbelian p F) {A0 : Subgroup (Wr D p)} (hA0 : A0 ≤ F ⊔ Subgroup.zpowers a)
    (haA0 : a ∈ A0) {f₀ : Wr D p} (hf₀F : f₀ ∈ F) (hf₀A : f₀ ∈ A0) (hf₀1 : f₀ ≠ 1) :
    ∃ h ∈ projProd F, (∀ y ∈ A0, h * y * h⁻¹ ∈ A0) ∧ h ∉ F ⊔ Subgroup.zpowers a := by
  obtain ⟨h, hh, hsh⟩ := exists_shear hp ha hFb hFa hFe hf₀F
  have hHe := projProd_isElemAbelian hFe
  have hconj : h * a * h⁻¹ = f₀ * a := by rw [hsh, mul_inv_cancel_right]
  refine ⟨h, hh, fun y hy => ?_, fun hmem => ?_⟩
  · obtain ⟨f, hf, k, rfl⟩ := mem_sup_zpowers (mem_normalizer_of_comm hFa) (hA0 hy)
    have hfA0 : f ∈ A0 := by
      have := A0.mul_mem hy (A0.zpow_mem haA0 (-k))
      rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
    have hcf : h * f * h⁻¹ = f := by
      have hfh : f * h = h * f :=
        congrArg Subtype.val (hHe.1.is_comm.comm ⟨f, le_projProd hFb hf⟩ ⟨h, hh⟩)
      rw [← hfh, mul_inv_cancel_right]
    have heq : h * (f * a ^ k) * h⁻¹ = (h * f * h⁻¹) * (h * a * h⁻¹) ^ k := by
      rw [conj_zpow]
      group
    rw [heq, hcf, hconj]
    exact A0.mul_mem hfA0 (A0.zpow_mem (A0.mul_mem hf₀A haA0) k)
  · obtain ⟨f, hf, k, hk⟩ := mem_sup_zpowers (mem_normalizer_of_comm hFa) hmem
    have hr : (a ^ k).right = 1 := by
      have h1 : h.right = (f * a ^ k).right := by rw [hk]
      simpa [hh.1, hFb f hf] using h1.symm
    rw [zpow_eq_one_of_right hp ha hap hr, mul_one] at hk
    have hca : h * a = a * h := by rw [hk]; exact hFa f hf
    apply hf₀1
    have h2 : f₀ * a * h = 1 * a * h := by rw [← hsh, hca, one_mul]
    exact mul_right_cancel (mul_right_cancel h2)

theorem card_projProd (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) :
    Nat.card (projProd F) = Nat.card F ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let ψ : (Multiplicative (ZMod p) → ↥F) → ↥(projProd F) := fun g =>
    ⟨⟨fun k => (g k : Wr D p).left k, 1⟩, rfl, fun k => ⟨g k, (g k).2, hFb _ (g k).2, rfl⟩⟩
  have hinj : Function.Injective ψ := by
    intro g g' hgg'
    funext k
    have h1 : (g k : Wr D p).left k = (g' k : Wr D p).left k := by
      have := congrArg (fun w : ↥(projProd F) => (w : Wr D p).left k) hgg'
      exact this
    have hu : ((g k : Wr D p) * (g' k : Wr D p)⁻¹).right = 1 := by
      simp [hFb _ (g k).2, hFb _ (g' k).2]
    have huF : (g k : Wr D p) * (g' k : Wr D p)⁻¹ ∈ F := F.mul_mem (g k).2 (F.inv_mem (g' k).2)
    have h0 : ((g k : Wr D p) * (g' k : Wr D p)⁻¹).left k = 1 := by
      rw [left_mul_of_right (hFb _ (g k).2), left_inv_of_right (hFb _ (g' k).2), h1, mul_inv_cancel]
    have := eq_one_of_comm hp ha hu (hFa _ huF) h0
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨w, hwr, hwl⟩
    have key := hwl
    choose g hg using key
    refine ⟨fun k => ⟨g k, (hg k).1⟩, ?_⟩
    apply Subtype.ext
    ext k
    · exact ((hg k).2.2).symm
    · exact hwr.symm
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_fun, hcard]

theorem card_single_range (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) (j : Multiplicative (ZMod p)) :
    Nat.card (single F hFb j).range = Nat.card F :=
  Nat.card_congr (MonoidHom.ofInjective (single_injective hp ha hFb hFa j)).toEquiv.symm

theorem card_pair_range (hp : p.Prime) {F : Subgroup (Wr D p)} {a : Wr D p} (ha : a.right ≠ 1)
    (hFb : ∀ f ∈ F, f.right = 1) (hFa : ∀ f ∈ F, f * a = a * f) {i j : Multiplicative (ZMod p)}
    (hij : i ≠ j) : Nat.card (pair F hFb hij).range = Nat.card F * Nat.card F := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MonoidHom.ofInjective (pair_injective hp ha hFb hFa hij)).toEquiv.symm

end Wreath

section Generic

theorem isElemAbelian_of_le {Y : Type*} [Group Y] {p : ℕ} {E H : Subgroup Y}
    (hE : IsElemAbelian p E) (hHE : H ≤ E) : IsElemAbelian p H :=
  ⟨⟨⟨fun x y => Subtype.ext (show (x : Y) * y = y * x from congrArg Subtype.val
      (hE.1.is_comm.comm (⟨x, hHE x.2⟩ : E) ⟨y, hHE y.2⟩))⟩⟩, fun x hx => hE.2 x (hHE hx)⟩

theorem isElemAbelian_comap {Y Z : Type*} [Group Y] [Group Z] {p : ℕ} (f : Y →* Z)
    (hf : Function.Injective f) {E : Subgroup Z} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · show f (x * y) = f (y * x)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨f x, x.2⟩ ⟨f y, y.2⟩)
  · rw [map_pow, hE.2 _ hx, map_one]

theorem isElemAbelian_map' {Y Z : Type*} [Group Y] [Group Z] {p : ℕ} (f : Y →* Z)
    {E : Subgroup Y} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.1 y.2
    show (x : Z) * y = y * x
    rw [← hxe, ← hye, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩))
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x' hx', map_one]

theorem isPGroup_of_isElemAbelian {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] {E : Subgroup Y}
    (hE : IsElemAbelian p E) : IsPGroup p ↥E :=
  fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

theorem card_eq_pow_pRank {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime] {E : Subgroup Y}
    (hE : IsElemAbelian p E) : Nat.card E = p ^ CFSG.Open.pRank p E := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hE)
  obtain ⟨E0, hE0, -, hc⟩ := Lemma1210.exists_elemAb_pRank hp.out.one_lt E
  have h1 : k ≤ CFSG.Open.pRank p E := Lemma1210.le_pRank_of_elemAb hp.out.one_lt le_rfl hE hk
  have h2 : p ^ CFSG.Open.pRank p E ≤ p ^ k := by
    rw [← hc, ← hk]
    exact Subgroup.card_le_of_le hE0
  have h3 : CFSG.Open.pRank p E ≤ k := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h2
  rw [hk, le_antisymm h1 h3]

variable {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}

theorem inf_eq_bot_of_coprime [Fact p.Prime] {O X : Subgroup Γ} (hO : Nat.Coprime p (Nat.card O))
    (hX : IsPGroup p ↥X) : X ⊓ O = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hX
  exact Subgroup.inf_eq_bot_of_coprime (by rw [hk]; exact hO.pow_left k)

theorem frattini_lift [hp : Fact p.Prime] (O X : Subgroup Γ) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O)) (hX : IsPGroup p ↥X) {n : Γ}
    (hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X ⊔ O) :
    ∃ c ∈ X ⊔ O, ∃ m ∈ Subgroup.normalizer (X : Set Γ), n = c * m := by
  have hXO : X ⊓ O = ⊥ := inf_eq_bot_of_coprime hO hX
  have hWc := Lemma1210.card_sup_of_inf_bot hXO
  have hXpos : 0 < Nat.card X := Nat.card_pos
  set W : Subgroup Γ := X ⊔ O with hWdef
  set X' : Subgroup Γ := X.map (MulAut.conj n).toMonoidHom with hX'def
  have hX'W : X' ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hn x hx
  have hXX' : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hX'p : IsPGroup p ↥X' := hX.map (MulAut.conj n).toMonoidHom
  have hP₁p : IsPGroup p ↥(X.subgroupOf W) :=
    hX.comap_of_injective W.subtype Subtype.val_injective
  have hP₂p : IsPGroup p ↥(X'.subgroupOf W) :=
    hX'p.comap_of_injective W.subtype Subtype.val_injective
  have hP₁c : Nat.card ↥(X.subgroupOf W) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ W)).toEquiv
  have hP₂c : Nat.card ↥(X'.subgroupOf W) = Nat.card X := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX'W).toEquiv, hXX']
  have hidx : ∀ H : Subgroup ↥W, Nat.card ↥H = Nat.card X → ¬ p ∣ H.index := by
    intro H hH
    have h1 := Subgroup.card_mul_index H
    rw [hH, hWc] at h1
    have h2 : H.index = Nat.card O := Nat.eq_of_mul_eq_mul_left hXpos (by rw [h1, mul_comm])
    rw [h2]
    intro h3
    have := Nat.Coprime.coprime_dvd_right h3 hO
    exact hp.out.one_lt.ne' ((Nat.coprime_self p).1 this)
  let S₁ : Sylow p ↥W := IsPGroup.toSylow hP₁p (hidx _ hP₁c)
  let S₂ : Sylow p ↥W := IsPGroup.toSylow hP₂p (hidx _ hP₂c)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) S₁ S₂
  have hS₂coe : (S₂ : Subgroup ↥W) = X'.subgroupOf W := rfl
  have hS₁coe : (S₁ : Subgroup ↥W) = X.subgroupOf W := rfl
  have hmem : ∀ x' ∈ X', ∃ y ∈ X, (g : Γ) * y * (g : Γ)⁻¹ = x' := by
    intro x' hx'
    have h1 : (⟨x', hX'W hx'⟩ : ↥W) ∈ (S₂ : Subgroup ↥W) := by
      rw [hS₂coe]
      exact Subgroup.mem_subgroupOf.2 hx'
    rw [← hg, Sylow.coe_subgroup_smul] at h1
    obtain ⟨h, hh, hgh⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [hS₁coe] at hh
    refine ⟨(h : Γ), Subgroup.mem_subgroupOf.1 hh, ?_⟩
    have := congrArg Subtype.val hgh
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  refine ⟨(g : Γ), g.2, (g : Γ)⁻¹ * n, ?_, by simp⟩
  set m : Γ := (g : Γ)⁻¹ * n with hm
  have hsub : ∀ x ∈ X, m⁻¹⁻¹ * x * m⁻¹ ∈ X := by
    intro x hx
    obtain ⟨y, hy, hgy⟩ := hmem (n * x * n⁻¹) ⟨x, hx, rfl⟩
    have hy' : y = (g : Γ)⁻¹ * (n * x * n⁻¹) * (g : Γ) := by
      rw [← hgy]
      group
    have : m⁻¹⁻¹ * x * m⁻¹ = y := by
      rw [hy', hm]
      group
    rw [this]
    exact hy
  have := Lemma1210.mem_normalizer_of_conj_inv_mem X m⁻¹ hsub
  exact (Subgroup.inv_mem_iff _).1 this

theorem normalizer_map_le [Fact p.Prime] (O X : Subgroup Γ) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O)) (hX : IsPGroup p ↥X) :
    Subgroup.normalizer ((X.map (QuotientGroup.mk' O) : Subgroup (Γ ⧸ O)) : Set (Γ ⧸ O)) ≤
      (Subgroup.normalizer (X : Set Γ)).map (QuotientGroup.mk' O) := by
  intro nb hnb
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
  have hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X ⊔ O := by
    intro x hx
    have h1 : QuotientGroup.mk' O (n * x * n⁻¹) ∈ X.map (QuotientGroup.mk' O) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hnb _).1 ⟨x, hx, rfl⟩
    have h2 : n * x * n⁻¹ ∈ (X.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  obtain ⟨c, hc, m, hm, rfl⟩ := frattini_lift O X hO hX hn
  have hc' : QuotientGroup.mk' O c ∈ X.map (QuotientGroup.mk' O) := by
    have : c ∈ (X.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact hc
    exact this
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 hc'
  refine ⟨x * m, Subgroup.mul_mem _ (Subgroup.le_normalizer hx) hm, ?_⟩
  rw [map_mul, map_mul, hxc]

theorem exists_lift [Fact p.Prime] (O : Subgroup Γ) [O.Normal] (hO : Nat.Coprime p (Nat.card O))
    (Yb : Subgroup (Γ ⧸ O)) (hYb : IsPGroup p ↥Yb) {A : Subgroup Γ} (hA : IsPGroup p ↥A)
    (hAY : A.map (QuotientGroup.mk' O) ≤ Yb) :
    ∃ P : Subgroup Γ, A ≤ P ∧ IsPGroup p ↥P ∧ P ⊓ O = ⊥ ∧ P.map (QuotientGroup.mk' O) = Yb := by
  set T : Subgroup Γ := Yb.comap (QuotientGroup.mk' O) with hTdef
  have hAT : A ≤ T := Subgroup.map_le_iff_le_comap.1 hAY
  have hA' : IsPGroup p ↥(A.subgroupOf T) := hA.comap_of_injective T.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hA'
  set P : Subgroup Γ := (S : Subgroup ↥T).map T.subtype with hPdef
  have hPp : IsPGroup p ↥P := S.isPGroup'.map T.subtype
  have hAP : A ≤ P := fun x hx => ⟨⟨x, hAT hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPT : P ≤ T := Subgroup.map_subtype_le _
  have hPO : P ⊓ O = ⊥ := inf_eq_bot_of_coprime hO hPp
  have hcP : Nat.card P = p ^ (Nat.card T).factorization p := by
    rw [hPdef, Subgroup.card_map_of_injective T.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  have hTc : Nat.card T = Nat.card O * Nat.card Yb := Lemma1210.card_comap_mk O Yb
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hYb
  have hpp : p.Prime := Fact.out
  have hpO : ¬ p ∣ Nat.card O := fun h => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO h)
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card T).factorization p = k := by
    rw [hTc, hk, Nat.factorization_mul hO0 (pow_ne_zero _ hpp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpO, zero_add, hpp.factorization_pow,
      Finsupp.single_eq_same]
  refine ⟨P, hAP, hPp, hPO, ?_⟩
  have hle : P.map (QuotientGroup.mk' O) ≤ Yb := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPT hx
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Lemma1210.card_map_mk_of_inf_eq_bot O P hPO, hcP, hfac, hk]

end Generic

section Lift

variable {G : Type} [Group G] [Finite G] {p : ℕ}

@[expose] def liftSub {W : Type*} [Group W] {P : Subgroup G} (Θ : ↥P →* W) (S' : Subgroup W) :
    Subgroup G :=
  (S'.comap Θ).map P.subtype

variable {W : Type*} [Group W] {P : Subgroup G} {Θ : ↥P →* W}

theorem mem_liftSub {S' : Subgroup W} {x : G} :
    x ∈ liftSub Θ S' ↔ ∃ hx : x ∈ P, Θ ⟨x, hx⟩ ∈ S' := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem liftSub_le (S' : Subgroup W) : liftSub Θ S' ≤ P := Subgroup.map_subtype_le _

theorem liftSub_mono {S' T' : Subgroup W} (h : S' ≤ T') : liftSub Θ S' ≤ liftSub Θ T' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem card_liftSub (hΘ : Function.Injective Θ) {S' : Subgroup W} (hS : S' ≤ Θ.range) :
    Nat.card (liftSub Θ S') = Nat.card S' := by
  rw [liftSub, Subgroup.card_map_of_injective P.subtype_injective]
  calc Nat.card (S'.comap Θ) = Nat.card ((S'.comap Θ).map Θ) :=
        (Subgroup.card_map_of_injective hΘ).symm
    _ = Nat.card S' := by rw [Subgroup.map_comap_eq, inf_of_le_right hS]

theorem isElemAbelian_liftSub (hΘ : Function.Injective Θ) {S' : Subgroup W}
    (hS : IsElemAbelian p S') : IsElemAbelian p (liftSub Θ S') :=
  isElemAbelian_map' _ (isElemAbelian_comap Θ hΘ hS)

theorem exists_lift_hom [hp : Fact p.Prime] {N : Subgroup G}
    {Xb : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} (e : ↥Xb ≃* W) (Y' : Subgroup W)
    (hY' : IsPGroup p ↥Y') {A : Subgroup G} (hAN : A ≤ N) (hA : IsPGroup p ↥A)
    (hAY : ∀ (x : G) (hx : x ∈ A), ∃ hX : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hAN hx⟩ ∈ Xb,
      e ⟨_, hX⟩ ∈ Y') :
    ∃ (P : Subgroup G) (hPN : P ≤ N), A ≤ P ∧ IsPGroup p ↥P ∧ ∃ Θ : ↥P →* W,
      Function.Injective Θ ∧ Θ.range = Y' ∧
      ∀ (x : G) (hx : x ∈ P), ((e.symm (Θ ⟨x, hx⟩) : ↥Xb) : ↥N ⧸ GLAPPrimeCore p ↥N) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hPN hx⟩ := by
  set O := GLAPPrimeCore p ↥N with hOdef
  have hO : Nat.Coprime p (Nat.card O) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥N
  let ι : W →* ↥N ⧸ O := Xb.subtype.comp e.symm.toMonoidHom
  set Yb : Subgroup (↥N ⧸ O) := Y'.map ι with hYbdef
  have hYb : IsPGroup p ↥Yb := hY'.map ι
  have hAΓ : IsPGroup p ↥(A.subgroupOf N) := hA.comap_of_injective N.subtype Subtype.val_injective
  have hAY' : (A.subgroupOf N).map (QuotientGroup.mk' O) ≤ Yb := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨hX, hXY⟩ := hAY x (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨e ⟨_, hX⟩, hXY, ?_⟩
    show ((e.symm (e ⟨_, hX⟩) : ↥Xb) : ↥N ⧸ O) = QuotientGroup.mk' O ⟨x, hxN⟩
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨P0, hAP0, hP0p, hP0O, hP0Y⟩ := exists_lift O hO Yb hYb hAΓ hAY'
  set P : Subgroup G := P0.map N.subtype with hPdef
  have hPN : P ≤ N := Subgroup.map_subtype_le P0
  have hmemP0 : ∀ (x : G) (hx : x ∈ P), (⟨x, hPN hx⟩ : ↥N) ∈ P0 := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have hXb : ∀ x : ↥P, QuotientGroup.mk' O (Subgroup.inclusion hPN x) ∈ Xb := by
    intro x
    have h1 : QuotientGroup.mk' O (Subgroup.inclusion hPN x) ∈ Yb := by
      rw [← hP0Y]
      exact ⟨_, hmemP0 x x.2, rfl⟩
    obtain ⟨w, -, hw⟩ := h1
    rw [← hw]
    exact (e.symm w).2
  let f : ↥P →* ↥Xb :=
    ((QuotientGroup.mk' O).comp (Subgroup.inclusion hPN)).codRestrict Xb hXb
  let Θ : ↥P →* W := e.toMonoidHom.comp f
  have hfΘ : ∀ x : ↥P, e.symm (Θ x) = f x := fun x => e.symm_apply_apply (f x)
  refine ⟨P, hPN, ?_, hP0p.map N.subtype, Θ, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hAN hx⟩, hAP0 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : f x = 1 := by
      have := hfΘ x
      rw [hx, map_one] at this
      exact this.symm
    have h2 : QuotientGroup.mk' O (Subgroup.inclusion hPN x) = 1 := congrArg Subtype.val h1
    have h3 : Subgroup.inclusion hPN x ∈ P0 ⊓ O :=
      ⟨hmemP0 x x.2, (QuotientGroup.eq_one_iff _).1 h2⟩
    rw [hP0O, Subgroup.mem_bot] at h3
    exact Subtype.ext (show (x : G) = 1 from congrArg Subtype.val h3)
  · ext w
    constructor
    · rintro ⟨x, rfl⟩
      have h1 : QuotientGroup.mk' O (Subgroup.inclusion hPN x) ∈ Yb := by
        rw [← hP0Y]
        exact ⟨_, hmemP0 x x.2, rfl⟩
      obtain ⟨w', hw', hw'eq⟩ := h1
      have : Θ x = w' := by
        apply e.symm.injective
        rw [hfΘ]
        apply Subtype.ext
        exact hw'eq.symm
      rw [this]
      exact hw'
    · intro hw
      have h1 : ι w ∈ Yb := ⟨w, hw, rfl⟩
      rw [← hP0Y] at h1
      obtain ⟨y, hy, hyw⟩ := h1
      refine ⟨⟨(y : G), ⟨y, hy, rfl⟩⟩, ?_⟩
      apply e.symm.injective
      rw [hfΘ]
      apply Subtype.ext
      exact hyw
  · intro x hx
    rw [hfΘ]
    rfl

end Lift

section Cover

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_one (K : Subgroup G) : GLBConj 1 K = K := by
  ext y
  rw [mem_gLBConj]
  simp

theorem barX_mono {p : ℕ} {N X Y : Subgroup G} (h : X ≤ Y) : barX p N X ≤ barX p N Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem map_liftSub {p : ℕ} {N : Subgroup G} {W : Type*} [Group W]
    {Xb : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} (e : ↥Xb ≃* W) {P : Subgroup G} (hPN : P ≤ N)
    {Θ : ↥P →* W}
    (hcompat : ∀ (x : G) (hx : x ∈ P), ((e.symm (Θ ⟨x, hx⟩) : ↥Xb) : ↥N ⧸ GLAPPrimeCore p ↥N) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hPN hx⟩)
    {S' : Subgroup W} (hS : S' ≤ Θ.range) :
    ((liftSub Θ S').subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore p ↥N)) =
      S'.map (Xb.subtype.comp e.symm.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨hxP, hxS⟩ := mem_liftSub.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨Θ ⟨x, hxP⟩, hxS, hcompat x hxP⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, rfl⟩ := hS hw
    refine ⟨⟨(x0 : G), hPN x0.2⟩, Subgroup.mem_subgroupOf.2 (mem_liftSub.2 ⟨x0.2, hw⟩), ?_⟩
    exact (hcompat x0 x0.2).symm

theorem not_le_M {m p : ℕ} [hp : Fact p.Prime] {B M E A N K : Subgroup G}
    (h11 : Sec11 G m p B M E A) (hA3 : CFSG.Open.pRank p A = 3) (hcov : ¬ Covers p N M K)
    {Dt : Type} [Group Dt] {Xb : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} (hKX : barX p N K ≤ Xb)
    (e : ↥Xb ≃* Wr Dt p)
    {P : Subgroup G} (hPN : P ≤ N) (hPp : IsPGroup p ↥P) {Θ : ↥P →* Wr Dt p}
    (hΘ : Function.Injective Θ)
    (hcompat : ∀ (x : G) (hx : x ∈ P), ((e.symm (Θ ⟨x, hx⟩) : ↥Xb) : ↥N ⧸ GLAPPrimeCore p ↥N) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hPN hx⟩)
    {F' : Subgroup (Wr Dt p)} {a' : Wr Dt p} (ha' : a'.right ≠ 1)
    (hFb : ∀ f ∈ F', f.right = 1) (hFa : ∀ f ∈ F', f * a' = a' * f) (hFe : IsElemAbelian p F')
    (hFc : Nat.card F' = p ^ 2) (hHr : projProd F' ≤ Θ.range)
    (ha'M : ((e.symm a' : ↥Xb) : ↥N ⧸ GLAPPrimeCore p ↥N) ∈ barX p N M)
    (hHM : liftSub Θ (projProd F') ≤ M) : False := by
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥N)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥N
  have hHp : IsPGroup p ↥(liftSub Θ (projProd F')) := hPp.to_le (liftSub_le _)
  obtain ⟨R, hRM, hHR⟩ := Sec12c.exists_isSylowIn_above hHM hHp
  have h104 := (lemma104_v_holds h11.toSec10Fails h11.pair (Or.inr hA3) hRM).1
  have hHe : IsElemAbelian p (liftSub Θ (projProd F')) :=
    isElemAbelian_liftSub hΘ (projProd_isElemAbelian hFe)
  have hcoord : ∀ i, (coordSub i : Subgroup (Wr Dt p)).map (Xb.subtype.comp e.symm.toMonoidHom) ≤
      barX p N M := by
    intro i
    have hji : a'.right * i ≠ i := by
      intro hj
      apply ha'
      have := congrArg (· * i⁻¹) hj
      simpa [mul_assoc] using this
    have hX'E : (single F' hFb (a'.right * i)).range ≤ (pair F' hFb hji).range :=
      single_range_le_pair hji
    have hE'H : (pair F' hFb hji).range ≤ projProd F' := pair_range_le hji
    have hE'r : (pair F' hFb hji).range ≤ Θ.range := hE'H.trans hHr
    have hX'r : (single F' hFb (a'.right * i)).range ≤ Θ.range := hX'E.trans hE'r
    have hE4 : IsEkIn p 4 R (liftSub Θ (pair F' hFb hji).range) := by
      refine ⟨(liftSub_mono hE'H).trans hHR, isElemAbelian_of_le hHe (liftSub_mono hE'H), ?_⟩
      rw [card_liftSub hΘ hE'r, card_pair_range hp.out ha' hFb hFa hji, hFc]
      ring
    obtain ⟨-, -, Astar, hAstar, hE4A⟩ := h104 _ hE4
    set X := liftSub Θ (single F' hFb (a'.right * i)).range with hXdef
    have hXA : X ≤ Astar := (liftSub_mono hX'E).trans hE4A
    have hXe : IsElemAbelian p X := isElemAbelian_of_le hHe (liftSub_mono (hX'E.trans hE'H))
    have hXc : Nat.card X = p ^ 2 := by
      rw [card_liftSub hΘ hX'r, card_single_range hp.out ha' hFb hFa _, hFc]
    have hXr : 2 ≤ CFSG.Open.pRank p X := Lemma1210.le_pRank_of_elemAb hp.out.one_lt le_rfl hXe hXc
    have hNX : Subgroup.normalizer (X : Set G) ≤ M :=
      le_trans (Lemma1210.normalizer_le_GLBCore' hXA hXr) hAstar.2.clause_d
    have hXN : X ≤ N := (liftSub_le _).trans hPN
    have hXNp : IsPGroup p ↥(X.subgroupOf N) :=
      (hPp.to_le (liftSub_le _)).comap_of_injective N.subtype Subtype.val_injective
    have hFr := normalizer_map_le (GLAPPrimeCore p ↥N) (X.subgroupOf N) hO hXNp
    rw [map_liftSub e hPN hcompat hX'r] at hFr
    rintro _ ⟨w, hw, rfl⟩
    have hwn : (Xb.subtype.comp e.symm.toMonoidHom) w ∈ Subgroup.normalizer
        (((single F' hFb (a'.right * i)).range.map (Xb.subtype.comp e.symm.toMonoidHom) :
          Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
      apply mem_normalizer_of_comm
      rintro _ ⟨s, ⟨f, rfl⟩, rfl⟩
      rw [← map_mul, ← map_mul, coordSub_comm_single hji.symm hw f]
    obtain ⟨n, hn, hnw⟩ := hFr hwn
    have hnX : (n : G) ∈ Subgroup.normalizer (X : Set G) := by
      have h1 : ∀ x ∈ X, ((n : G)⁻¹)⁻¹ * x * (n : G)⁻¹ ∈ X := by
        intro x hx
        have h2 := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hXN hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
        rw [Subgroup.mem_subgroupOf] at h2
        simpa using h2
      exact (Subgroup.inv_mem_iff _).1 (Lemma1210.mem_normalizer_of_conj_inv_mem X _ h1)
    exact ⟨n, Subgroup.mem_subgroupOf.2 (hNX hnX), hnw⟩
  have hTop : ∀ w : Wr Dt p, (Xb.subtype.comp e.symm.toMonoidHom) w ∈ barX p N M := by
    intro w
    have hle : (⨆ i, (coordSub i : Subgroup (Wr Dt p))) ⊔ Subgroup.zpowers a' ≤
        (barX p N M).comap (Xb.subtype.comp e.symm.toMonoidHom) := by
      apply sup_le
      · exact iSup_le fun i => Subgroup.map_le_iff_le_comap.1 (hcoord i)
      · rw [Subgroup.zpowers_le]
        exact ha'M
    exact hle (mem_iSup_coordSub_sup hp.out ha' w)
  apply hcov
  intro y hy
  have := hTop (e ⟨y, hKX hy⟩)
  simpa using this

end Cover

section Main

theorem isElemAbelian_range {G W : Type*} [Group G] [Group W] {p : ℕ} {A : Subgroup G}
    (hA : IsElemAbelian p A) (φ : ↥A →* W) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩
  · obtain ⟨x', hx'⟩ := x.2
    obtain ⟨y', hy'⟩ := y.2
    show (x : W) * y = y * x
    rw [← hx', ← hy', ← map_mul, ← map_mul, hA.1.is_comm.comm x' y']
  · obtain ⟨x, rfl⟩ := hw
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hA.2 x x.2)
    rw [this, map_one]

theorem input1210b_wreathRk_holds :
    ∀ (G : Type) [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G},
      Lemma129Common p M E A N K →
      ((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) →
      Lemma129IvBData p N K E A →
      ∃ (F : Subgroup G) (a : G) (H : Subgroup G),
        IsEkIn p 2 A F ∧ a ∈ E ⊓ A ∧ A = F ⊔ Subgroup.zpowers a ∧
        CFSG.Open.IsElemAbelian p H ∧ F ≤ H ∧
        (∀ y ∈ E ⊓ A, ∀ x ∈ H, y * x * y⁻¹ ∈ H) ∧
        IsPGroup p ↥(H ⊔ (E ⊓ A)) ∧ ¬ H ≤ M ∧
        (∀ x ∈ A, x ∉ H → ∀ n ∈ H ⊔ (E ⊓ A), x * n = n * x → n ∈ A) ∧
        (∃ n ∈ H ⊔ (E ⊓ A), n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n ∉ A) ∧
        a ∉ H ∧ Nat.card ↥H = p ^ (2 * p) := by
  intro G _ _ m p B M E A N D h K hK _ hb
  obtain ⟨Dt, _, -, e, -, -, -, a, haEA, -, htop⟩ := hb
  have h11 : Sec11 G m p B M E A := h.toSec11
  have hpp : p.Prime := (h.toSec11.toSec10Fails.toSec10.standing.beta).1
  haveI hpf : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hAe : IsElemAbelian p A := (lemma104_ii_holds h11.toSec10Fails h11.pair).2.2.1
  have hA3 : CFSG.Open.pRank p A = 3 := hK.2.1.1
  have hE2 : CFSG.Open.pRank p (E ⊓ A) = 2 := hK.2.1.2
  have hAM : A ≤ M := h11.pair.1.2.1.1.1.1
  have hcov : ¬ Covers p N M K := hK.2.2.1
  have hAN : A ≤ N := by
    intro x hx
    apply h.hD
    apply Lemma1210.mem_normalizer_of_conj_inv_mem D x
    intro d hd
    have hdA : d ∈ A := h.plane.1 hd
    have hc : x * d = d * x := Lemma1210.isElemAbelian_comm_gen hAe hx hdA
    have hx' : x⁻¹ * d * x = d := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hx']
    exact hd
  have haA : a ∈ A := haEA.2
  have hAp : IsPGroup p ↥A := isPGroup_of_isElemAbelian hAe
  have hAΓp : IsPGroup p ↥(A.subgroupOf N) := hAp.comap_of_injective N.subtype Subtype.val_injective
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥N)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥N
  have hcardQ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hKKs : K ≤ ⨆ g ∈ A, GLBConj g K :=
    le_iSup₂_of_le (1 : G) A.one_mem (le_of_eq (gLBConj_one K).symm)
  have hKX : barX p N K ≤ barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A :=
    (barX_mono hKKs).trans le_sup_left
  have hAXb : ∀ x : ↥A, QuotientGroup.mk' (GLAPPrimeCore p ↥N) (Subgroup.inclusion hAN x) ∈
      barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A := fun x =>
    Subgroup.mem_sup_right ⟨Subgroup.inclusion hAN x, x.2, rfl⟩
  let φ : ↥A →* Wr Dt p := e.toMonoidHom.comp
    (((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (Subgroup.inclusion hAN)).codRestrict _ hAXb)
  have hφe : ∀ x : ↥A, e.symm (φ x) = ⟨_, hAXb x⟩ := fun x => e.symm_apply_apply _
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (Subgroup.inclusion hAN x) = 1 := by
      have := hφe x
      rw [hx, map_one] at this
      exact (congrArg Subtype.val this).symm
    have h2 : Subgroup.inclusion hAN x ∈ A.subgroupOf N ⊓ GLAPPrimeCore p ↥N :=
      ⟨x.2, (QuotientGroup.eq_one_iff _).1 h1⟩
    rw [inf_eq_bot_of_coprime hO hAΓp, Subgroup.mem_bot] at h2
    exact Subtype.ext (show (x : G) = 1 from congrArg Subtype.val h2)
  obtain ⟨a', ha'def⟩ : ∃ a' : Wr Dt p, a' = φ ⟨a, haA⟩ := ⟨_, rfl⟩
  have ha'1 : a'.right ≠ 1 := by
    intro h1
    have hq : Multiplicative.ofAdd (1 : ZMod p) ∈ Subgroup.map
        (RegularWreathProduct.rightHom.comp e.toMonoidHom)
        ((barX p N (Subgroup.zpowers a)).subgroupOf
          (barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyq⟩ := hq
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hz)
    have hz' : z = (⟨a, hAN haA⟩ : ↥N) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    have hy' : y = e.symm (a' ^ k) := by
      apply Subtype.ext
      rw [map_zpow, Subgroup.coe_zpow, ha'def, hφe, ← hzy, hz', map_zpow]
      rfl
    have h2 : (RegularWreathProduct.rightHom.comp e.toMonoidHom) y = 1 := by
      rw [hy', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_zpow]
      show a'.right ^ k = 1
      rw [h1]
      exact one_zpow k
    rw [h2] at hyq
    have h3 : (1 : ZMod p) = 0 := by
      have := congrArg Multiplicative.toAdd hyq
      simpa using this.symm
    exact one_ne_zero h3
  let ψ : ↥A →* Multiplicative (ZMod p) := RegularWreathProduct.rightHom.comp φ
  have hψa : ψ ⟨a, haA⟩ = a'.right := by rw [ha'def]; rfl
  have hψs : ∀ q, ∃ j : ℕ, ψ (⟨a, haA⟩ ^ j) = q := by
    intro q
    obtain ⟨j, hj⟩ := gen_of_ne_one hpp ha'1 q
    exact ⟨j, by rw [map_pow, hψa, hj]⟩
  have hψsurj : Function.Surjective ψ := fun q => by
    obtain ⟨j, hj⟩ := hψs q
    exact ⟨_, hj⟩
  have hAc : Nat.card A = p ^ 3 := by rw [card_eq_pow_pRank hAe, hA3]
  have hFAc : Nat.card ψ.ker = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have h2 : Nat.card (↥A ⧸ ψ.ker) = p :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv).trans hcardQ
    rw [h2, hAc] at h1
    have h3 : p * p ^ 2 = p * Nat.card ψ.ker := by rw [← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpp.pos h3).symm
  have hFE : IsEkIn p 2 A (ψ.ker.map A.subtype) :=
    ⟨Subgroup.map_subtype_le _, isElemAbelian_of_le hAe (Subgroup.map_subtype_le _),
      by rw [Subgroup.card_map_of_injective A.subtype_injective, hFAc]⟩
  have hdecomp : ∀ x : ↥A, ∃ j : ℕ, x * (⟨a, haA⟩ ^ j)⁻¹ ∈ ψ.ker := by
    intro x
    obtain ⟨j, hj⟩ := hψs (ψ x)
    refine ⟨j, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hj]
    exact mul_inv_cancel _
  have hAFa : A = ψ.ker.map A.subtype ⊔ Subgroup.zpowers a := by
    apply le_antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := hdecomp ⟨x, hx⟩
      have hx' : x = ((⟨x, hx⟩ * (⟨a, haA⟩ ^ j)⁻¹ : ↥A) : G) * a ^ j := by simp
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, hj, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j))
    · exact sup_le (Subgroup.map_subtype_le _) ((Subgroup.zpowers_le).2 haA)
  obtain ⟨F', hF'def⟩ : ∃ F' : Subgroup (Wr Dt p), F' = ψ.ker.map φ := ⟨_, rfl⟩
  have hF'b : ∀ f ∈ F', f.right = 1 := by
    rw [hF'def]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hRange : IsElemAbelian p φ.range := isElemAbelian_range hAe φ
  have hF'le : F' ≤ φ.range := hF'def ▸ Subgroup.map_le_range φ ψ.ker
  have hF'e : IsElemAbelian p F' := isElemAbelian_of_le hRange hF'le
  have hcommR : ∀ u ∈ φ.range, ∀ v ∈ φ.range, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hRange.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have ha'R : a' ∈ φ.range := ⟨⟨a, haA⟩, ha'def.symm⟩
  have hF'a : ∀ f ∈ F', f * a' = a' * f := fun f hf => hcommR f (hF'le hf) a' ha'R
  have hF'c : Nat.card F' = p ^ 2 := by rw [hF'def, Subgroup.card_map_of_injective hφinj, hFAc]
  have ha'p : a' ^ p = 1 := by
    rw [ha'def, ← map_pow]
    have : (⟨a, haA⟩ : ↥A) ^ p = 1 := Subtype.ext (by simpa using hAe.2 a haA)
    rw [this, map_one]
  have hRangeEq : φ.range = F' ⊔ Subgroup.zpowers a' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨j, hj⟩ := hdecomp x
      have hx : x = (x * (⟨a, haA⟩ ^ j)⁻¹) * ⟨a, haA⟩ ^ j := by rw [inv_mul_cancel_right]
      rw [hx, map_mul, map_pow, ← ha'def]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hF'def ▸ ⟨_, hj, rfl⟩))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers a') j))
    · exact sup_le hF'le ((Subgroup.zpowers_le).2 ha'R)
  have hRangeNorm : φ.range ≤
      Subgroup.normalizer ((projProd F' : Subgroup (Wr Dt p)) : Set (Wr Dt p)) := fun y hy =>
    mem_normalizer_projProd fun f hf => hcommR f (hF'le hf) y hy
  obtain ⟨Y', hY'def⟩ : ∃ Y' : Subgroup (Wr Dt p), Y' = projProd F' ⊔ φ.range := ⟨_, rfl⟩
  have hY'p : IsPGroup p ↥Y' := by
    rw [hY'def]
    exact IsPGroup.to_sup_of_normal_left'
      (isPGroup_of_isElemAbelian (projProd_isElemAbelian hF'e))
      (isPGroup_of_isElemAbelian hRange) hRangeNorm
  have hAY : ∀ (x : G) (hx : x ∈ A),
      ∃ hX : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hAN hx⟩ ∈
        barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A, e ⟨_, hX⟩ ∈ Y' := fun x hx =>
    ⟨hAXb ⟨x, hx⟩, hY'def ▸ Subgroup.mem_sup_right ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨P, hPN, hAP, hPp, Θ, hΘ, hΘr, hcompat⟩ := exists_lift_hom e Y' hY'p hAN hAp hAY
  have hΘA : ∀ (x : G) (hx : x ∈ A), Θ ⟨x, hAP hx⟩ = φ ⟨x, hx⟩ := by
    intro x hx
    apply e.symm.injective
    apply Subtype.ext
    rw [hcompat, hφe]
    rfl
  have hHr : projProd F' ≤ Θ.range := by
    rw [hΘr, hY'def]
    exact le_sup_left
  have hsupP : liftSub Θ (projProd F') ⊔ (E ⊓ A) ≤ P :=
    sup_le (liftSub_le _) (inf_le_right.trans hAP)
  have hle : liftSub Θ (projProd F') ⊔ (E ⊓ A) ≤
      liftSub Θ (projProd F' ⊔ Subgroup.zpowers a') := by
    apply sup_le (liftSub_mono le_sup_left)
    intro y hy
    refine mem_liftSub.2 ⟨hAP hy.2, ?_⟩
    rw [hΘA y hy.2]
    have : φ ⟨y, hy.2⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hRangeEq] at this
    exact (sup_le_sup_right (le_projProd hF'b) _) this
  have ha'M : ((e.symm a' : ↥(barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A)) :
      ↥N ⧸ GLAPPrimeCore p ↥N) ∈ barX p N M := by
    rw [ha'def, hφe]
    exact ⟨⟨a, hAN haA⟩, hAM haA, rfl⟩
  refine ⟨ψ.ker.map A.subtype, a, liftSub Θ (projProd F'), hFE, haEA, hAFa,
    isElemAbelian_liftSub hΘ (projProd_isElemAbelian hF'e), ?_, ?_, hPp.to_le hsupP,
    fun hHM => not_le_M h11 hA3 hcov hKX e hPN hPp hΘ hcompat ha'1 hF'b hF'a hF'e hF'c hHr
      ha'M hHM, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨x, hx, rfl⟩
    refine mem_liftSub.2 ⟨hAP x.2, ?_⟩
    show Θ ⟨(x : G), hAP x.2⟩ ∈ projProd F'
    rw [hΘA _ x.2]
    exact le_projProd hF'b (hF'def ▸ ⟨x, hx, rfl⟩)
  ·
    intro y hy x hx
    obtain ⟨hxP, hxH⟩ := mem_liftSub.1 hx
    have hyP : y ∈ P := hAP hy.2
    refine mem_liftSub.2 ⟨P.mul_mem (P.mul_mem hyP hxP) (P.inv_mem hyP), ?_⟩
    have h1 : Θ ⟨y * x * y⁻¹, P.mul_mem (P.mul_mem hyP hxP) (P.inv_mem hyP)⟩ =
        Θ ⟨y, hyP⟩ * Θ ⟨x, hxP⟩ * (Θ ⟨y, hyP⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, hΘA y hy.2]
    exact (Subgroup.mem_normalizer_iff.1 (hRangeNorm ⟨⟨y, hy.2⟩, rfl⟩) _).1 hxH
  ·
    intro x hx hxH n hn hxn
    have hxP := hAP hx
    have hnP : n ∈ P := hsupP hn
    have hn' : Θ ⟨n, hnP⟩ ∈ projProd F' ⊔ Subgroup.zpowers a' := (mem_liftSub.1 (hle hn)).2
    have hx' : Θ ⟨x, hxP⟩ ∈ F' ⊔ Subgroup.zpowers a' := by
      rw [hΘA x hx, ← hRangeEq]
      exact ⟨_, rfl⟩
    have hxH' : Θ ⟨x, hxP⟩ ∉ projProd F' := fun h => hxH (mem_liftSub.2 ⟨hxP, h⟩)
    have hcomm : Θ ⟨x, hxP⟩ * Θ ⟨n, hnP⟩ = Θ ⟨n, hnP⟩ * Θ ⟨x, hxP⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxn
    have h1 := centralizer_claim hpp ha'1 ha'p hF'b hF'a hF'e hx' hxH' hn' hcomm
    rw [← hRangeEq] at h1
    obtain ⟨w, hw⟩ := h1
    have h2 : (⟨n, hnP⟩ : ↥P) = ⟨w, hAP w.2⟩ := hΘ (by rw [hΘA _ w.2]; exact hw.symm)
    rw [show n = (w : G) from congrArg Subtype.val h2]
    exact w.2
  ·
    have hA0c : Nat.card ((E ⊓ A).subgroupOf A) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
        card_eq_pow_pRank (isElemAbelian_of_le hAe inf_le_right), hE2]
    have hex : ∃ x0 : ↥A, x0 ∈ (E ⊓ A).subgroupOf A ∧ x0 ∈ ψ.ker ∧ x0 ≠ 1 := by
      by_contra hne
      push Not at hne
      have hinj : Function.Injective (ψ.comp ((E ⊓ A).subgroupOf A).subtype) := by
        rw [injective_iff_map_eq_one]
        intro y hy
        exact Subtype.ext (hne y y.2 hy)
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [hA0c, hcardQ] at h1
      have : p < p ^ 2 := by nlinarith [hpp.two_le]
      omega
    obtain ⟨x0, hx0A, hx0F, hx01⟩ := hex
    have hA0le : ((E ⊓ A).subgroupOf A).map φ ≤ F' ⊔ Subgroup.zpowers a' :=
      hRangeEq ▸ Subgroup.map_le_range φ _
    have haA0 : a' ∈ ((E ⊓ A).subgroupOf A).map φ :=
      ⟨⟨a, haA⟩, Subgroup.mem_subgroupOf.2 haEA, ha'def.symm⟩
    have hf₀F : φ x0 ∈ F' := hF'def ▸ ⟨x0, hx0F, rfl⟩
    have hf₀A : φ x0 ∈ ((E ⊓ A).subgroupOf A).map φ := ⟨x0, hx0A, rfl⟩
    have hf₀1 : φ x0 ≠ 1 := fun h0 => hx01 (hφinj (by rw [h0, map_one]))
    obtain ⟨h', hh'H, hh'N, hh'A⟩ :=
      normalizer_claim hpp ha'1 ha'p hF'b hF'a hF'e hA0le haA0 hf₀F hf₀A hf₀1
    obtain ⟨n0, hn0⟩ := hHr hh'H
    refine ⟨(n0 : G), Subgroup.mem_sup_left (mem_liftSub.2 ⟨n0.2, ?_⟩), ?_, ?_⟩
    · show Θ n0 ∈ projProd F'
      rw [hn0]
      exact hh'H
    · have h1 : ∀ y ∈ E ⊓ A, ((n0 : G)⁻¹)⁻¹ * y * (n0 : G)⁻¹ ∈ E ⊓ A := by
        intro y hy
        rw [inv_inv]
        have hyP : y ∈ P := hAP hy.2
        have hzP : (n0 : G) * y * (n0 : G)⁻¹ ∈ P := P.mul_mem (P.mul_mem n0.2 hyP) (P.inv_mem n0.2)
        have hz : Θ ⟨(n0 : G) * y * (n0 : G)⁻¹, hzP⟩ = h' * φ ⟨y, hy.2⟩ * h'⁻¹ := by
          rw [← hn0, ← hΘA y hy.2, ← map_inv, ← map_mul, ← map_mul]
          rfl
        have hmem : Θ ⟨(n0 : G) * y * (n0 : G)⁻¹, hzP⟩ ∈ ((E ⊓ A).subgroupOf A).map φ := by
          rw [hz]
          exact hh'N _ ⟨⟨y, hy.2⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
        obtain ⟨w, hw, hwz⟩ := hmem
        have h2 : (⟨(n0 : G) * y * (n0 : G)⁻¹, hzP⟩ : ↥P) = ⟨w, hAP w.2⟩ :=
          hΘ (by rw [hΘA _ w.2]; exact hwz.symm)
        rw [show (n0 : G) * y * (n0 : G)⁻¹ = (w : G) from congrArg Subtype.val h2]
        exact Subgroup.mem_subgroupOf.1 hw
      exact (Subgroup.inv_mem_iff _).1 (Lemma1210.mem_normalizer_of_conj_inv_mem (E ⊓ A) _ h1)
    · intro hn0A
      apply hh'A
      rw [← hn0, show n0 = ⟨(n0 : G), hAP hn0A⟩ from rfl, hΘA _ hn0A, ← hRangeEq]
      exact ⟨_, rfl⟩
  ·
    intro haH
    obtain ⟨haP, haH'⟩ := mem_liftSub.1 haH
    rw [hΘA a haA, ← ha'def] at haH'
    exact ha'1 haH'.1
  ·
    rw [card_liftSub hΘ hHr, card_projProd hpp ha'1 hF'b hF'a, hF'c, ← pow_mul]

theorem input1210b_wreath_holds : Lemma1210.Input1210b_wreath := by
  intro G _ _ m p B M E A N D h K hK htype hdata
  obtain ⟨F, a, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ :=
    input1210b_wreathRk_holds G h hK htype hdata
  exact ⟨F, a, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem lemma1210_b_holds : Lemma1210_bStatement :=
  lemma1210_b_of_inputs input1210b_wreath_holds

end Main

section Catalogue

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (lieModel_of_classical lieModel_lie lieModel_typeA)

theorem exists_lieModel_tagged (d : ValidLieTypeIndex) :
    ∃ (t : StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel (CFSGIndex.lie d).Group t n p f ∧
      p = d.1.characteristic ∧
      (t = .PSL → ∃ (r : ℕ) (q : PrimePower), d.1 = .A r q ∧ n = r + 1 ∧ p = q.p ∧ f = q.exponent) := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q => exact ⟨_, _, _, _, lieModel_typeA r q hv, by simp, fun _ => ⟨r, q, rfl, rfl, rfl, rfl⟩⟩
  | twistedA r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)),
      by simp, by simp⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, _, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)),
        by simp, by simp⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _)), by simp, by simp⟩
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _)), by simp, by simp⟩
  | C r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _)),
      by simp, by simp⟩
  | D r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)),
      by simp, by simp⟩
  | twistedD r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)),
      by simp, by simp⟩
  | E6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩, by simp, by simp⟩
  | E7 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩, by simp, by simp⟩
  | E8 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩, by simp, by simp⟩
  | F4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩, by simp, by simp⟩
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩, by simp, by simp⟩
  | twistedE6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩, by simp, by simp⟩
  | trialityD4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩, by simp, by simp⟩
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩,
      by simp, by simp⟩
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩,
      by simp, by simp⟩
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩,
      by simp, by simp⟩
  | tits =>
    exact ⟨_, _, _, _, lieModel_lie (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩, by simp, by simp⟩

theorem tuple_of_card_60 (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (hc : Nat.card X = 60) : t = .PSL ∧ n = 2 ∧ ((p = 2 ∧ f = 2) ∨ (p = 5 ∧ f = 1)) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hm := hadm.2.2
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 60 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 60 := (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases Prop1116Design.prime_dvd_sixty hp hpd with rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 2) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm (by omega) with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        dsimp only at hm <;> revert hm hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;>
        decide

theorem tuple_of_card_360 (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (hc : Nat.card X = 360) : t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hm := hadm.2.2
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 360 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 360 := (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases Prop1116Design.prime_dvd_threesixty hp hpd with rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 3) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm (by omega) with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        dsimp only at hm <;> revert hm hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;>
        decide

theorem tuple_of_card_20160 (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (hc : Nat.card X = 20160) :
    t = .PSL ∧ ((n = 3 ∧ p = 2 ∧ f = 2) ∨ (n = 4 ∧ p = 2 ∧ f = 1)) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hm := hadm.2.2
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 20160 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 20160 := (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_L34 hp hpd with rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 6) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm (by omega) with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
        revert hm hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        dsimp only at hm <;> revert hm hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;>
        decide

theorem not_card_6048_seven (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n f : ℕ} (hadm : StatedLieAdmissible t n 7 f) (hX : CFSG.Blueprint.LieModel X t n 7 f)
    (hc : Nat.card X = 6048) : False := by
  have hf : 1 ≤ f := hadm.2.1
  have hm := hadm.2.2
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 1) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework hadm (by omega) with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
      revert hm hord <;> decide
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> dsimp only at hm <;>
      revert hm hord <;> decide
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      dsimp only at hm <;> revert hm hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;>
      decide

theorem alt8_order_six : ∃ x : alternatingGroup (Fin 8), orderOf x = 6 := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2 * (Equiv.swap 3 4 * Equiv.swap 5 6), ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · rw [Subgroup.orderOf_mk, orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hm0
    interval_cases m <;> decide

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem prime_dvd_168 {p : ℕ} (hp : p.Prime) (h : p ∣ 168) : p = 2 ∨ p = 3 ∨ p = 7 := by
  rw [show (168 : ℕ) = 2 ^ 3 * 3 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))

theorem prime_dvd_6048 {p : ℕ} (hp : p.Prime) (h : p ∣ 6048) : p = 2 ∨ p = 3 ∨ p = 7 := by
  rw [show (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h3)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))

theorem dvd_card_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f) :
    p ∣ Nat.card X := by
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨hfin, -, hfac⟩ := hO X t n p f hadm hX
  haveI := hfin
  apply Nat.dvd_of_factorization_pos
  rw [hfac]
  exact Nat.mul_ne_zero (by omega) (by omega)

section Certified


theorem exists_blueprint_tagged {S : Type} [Group S] (d : ValidLieTypeIndex)
    (e : S ≃* (CFSGIndex.lie d).Group) :
    ∃ (t : StatedLieTag) (n p f : ℕ), CFSG.Blueprint.LieModel S t n p f ∧
      p = d.1.characteristic ∧
      (t = .PSL → ∃ (r : ℕ) (q : PrimePower), d.1 = .A r q ∧ n = r + 1 ∧ p = q.p ∧ f = q.exponent) := by
  obtain ⟨t, n, p, f, hM, hp, htag⟩ := exists_lieModel_tagged d
  exact ⟨t, n, p, f, CFSG.Blueprint.LieModel.of_mulEquiv e.symm
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hM), hp, htag⟩

theorem not_dup_of_valid (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .A r q)
    (h : (r = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (r = 3 ∧ q.card = 2)) : False := by
  have hval : (LieTypeIndex.A r q).Valid := hd ▸ d.2
  refine ((LieTypeIndex.valid_iff _).1 hval).2 ((LieTypeIndex.isDuplicateRepresentative_iff _).2 ?_)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem inputAltNotLie_holds : Prop1116Design.InputAltNotLie := by
  intro m idx hm
  refine ⟨fun e => ?_⟩
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨t, n, p, f, hX, -, htag⟩ := exists_blueprint_tagged idx e
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  rcases (show m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ 9 ≤ m by omega) with rfl | rfl | rfl | rfl | h9
  · obtain ⟨rfl, rfl, hpf⟩ := tuple_of_card_60 hO hadm hX Prop1116Design.card_alt_five
    obtain ⟨r, q, hd, hn, hpq, hfq⟩ := htag rfl
    refine not_dup_of_valid idx hd (Or.inl ⟨by omega, ?_⟩)
    rw [PrimePower.card_def, ← hpq, ← hfq]
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := tuple_of_card_360 hO hadm hX Prop1116Design.card_alt_six
    obtain ⟨r, q, hd, hn, hpq, hfq⟩ := htag rfl
    refine not_dup_of_valid idx hd (Or.inl ⟨by omega, Or.inr (Or.inr ?_)⟩)
    rw [PrimePower.card_def, ← hpq, ← hfq]
    norm_num
  · exact CFSG.ComponentClassification.CatFC.not_lieModel_of_alt7 hO hadm hX ⟨MulEquiv.refl _⟩
  · obtain ⟨rfl, h⟩ := tuple_of_card_20160 hO hadm hX card_alt_eight
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨x, hx⟩ := alt8_order_six
      exact CFSG.SeitzReduction.SporadicRefine.not_lieModel_psl_three_two_of_orderOf_six hx hX
    · obtain ⟨r, q, hd, hn, hpq, hfq⟩ := htag rfl
      refine not_dup_of_valid idx hd (Or.inr ⟨by omega, ?_⟩)
      rw [PrimePower.card_def, ← hpq, ← hfq]
      norm_num
  · exact CFSG.OddStandard.AltStdSec.false_of_lieModel_alt hO h9 (MulEquiv.refl _) hadm hX

theorem inputChevTwoOdd_holds : Prop1116Design.InputChevTwoOdd := by
  intro S _ q hq hq2 hq3 hchq hch2
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases hchq with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      obtain ⟨t, n, p, f, hX, hp, htag⟩ := exists_blueprint_tagged d e
      have hpq : p = q := hp.trans hdq
      subst hpq
      have hadm := CFSG.Blueprint.LieModel.admissible hX
      have hpS : p ∣ Nat.card S := dvd_card_of_lieModel hO hadm hX
      rcases hch2 with ⟨i', hi', ⟨e'⟩⟩ | ⟨i', hi', ⟨e'⟩⟩
      · cases i' with
        | cyclic _ _ => exact hi'.elim
        | alternating _ _ => exact hi'.elim
        | sporadic _ => exact hi'.elim
        | lie d' =>
          have hd2 : d'.1.characteristic = 2 := hi'
          obtain ⟨t', n', p', f', hX', hp', -⟩ := exists_blueprint_tagged d' e'
          have hp2 : p' = 2 := hp'.trans hd2
          subst hp2
          have hadm' := CFSG.Blueprint.LieModel.admissible hX'
          rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm' hadm hq2
              (hO S _ _ _ _ hadm' hX').2.1 (hO S _ _ _ _ hadm hX).2.1 with
            ⟨-, -, -, rfl, rfl, h5⟩ | ⟨-, -, -, rfl, rfl, h7⟩ | ⟨-, -, -, -, -, h3⟩
          · exfalso
            obtain ⟨r, q0, hd, hn, hpq0, hfq0⟩ := htag rfl
            refine not_dup_of_valid d hd (Or.inl ⟨by omega, Or.inr (Or.inl ?_)⟩)
            rw [PrimePower.card_def, ← hpq0, ← hfq0, h5]
          · have hp7 : p = 7 := by
              have hdvd : p ∣ 7 := h7 ▸ dvd_pow_self p (by have := hadm.2.1; omega)
              exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hdvd
            refine Or.inr ⟨?_, hp7⟩
            obtain ⟨-, K, hK, hKf, hKc, ⟨φ⟩⟩ := hX.statedClassicalModel (by decide)
            exact ⟨K, hK, hKf, hKc.trans h7, ⟨φ⟩⟩
          · exfalso
            have hdvd : p ∣ 3 := h3 ▸ dvd_pow_self p (by have := hadm.2.1; omega)
            exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hdvd)
      · cases i' with
        | cyclic _ _ => exact hi'.elim
        | sporadic _ => exact hi'.elim
        | alternating n0 hn0 =>
          exact ((inputAltNotLie_holds n0 d hn0).false (e'.symm.trans e)).elim
        | lie d' =>
          obtain ⟨d1, hv'⟩ := d'
          cases d1 with
          | A r q' =>
            rcases r with _ | _ | r
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
            ·
              have hq'7 : q'.card = 7 := by
                simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi'
              have hY : CFSG.Blueprint.LieModel S .PSL (0 + 1 + 1) q'.p q'.exponent :=
                CFSG.Blueprint.LieModel.of_mulEquiv e'.symm
                  (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
                    (lieModel_typeA (0 + 1) q' hv'))
              have hord := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
              rw [← PrimePower.card_def, hq'7] at hord
              have hS : Nat.card S = 168 := by
                simp only [lieOrderNumerator, lieOrderDivisor] at hord
                norm_num at hord
                omega
              have hp7 : p = 7 := by
                rcases prime_dvd_168 hq (hS ▸ hpS) with h | h | h
                · exact absurd h hq2
                · exact absurd h hq3
                · exact h
              refine Or.inr ⟨?_, hp7⟩
              obtain ⟨-, K, hK, hKf, hKc, ⟨φ⟩⟩ := hY.statedClassicalModel (by decide)
              exact ⟨K, hK, hKf, by rw [hKc, ← PrimePower.card_def, hq'7], ⟨φ⟩⟩
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
          | twistedA r q' =>
            rcases r with _ | _ | _ | _ | r
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
            ·
              exfalso
              have hq'3 : q'.card = 3 := by
                simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi'
              have hY : CFSG.Blueprint.LieModel S .PSU (0 + 1 + 1 + 1) q'.p q'.exponent :=
                CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
                  (lieModel_of_classical
                    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (0 + 1 + 1) q' hv' e'))
              have hord := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
              rw [← PrimePower.card_def, hq'3] at hord
              have hn : lieOrderNumerator .PSU (0 + 1 + 1 + 1) 3 = 6048 := by decide
              have hd : lieOrderDivisor .PSU (0 + 1 + 1 + 1) 3 = 1 := by decide
              have hS : Nat.card S = 6048 := by
                rw [hn, hd, mul_one] at hord
                exact hord
              have hp7 : p = 7 := by
                rcases prime_dvd_6048 hq (hS ▸ hpS) with h | h | h
                · exact absurd h hq2
                · exact absurd h hq3
                · exact h
              subst hp7
              exact not_card_6048_seven hO hadm hX hS
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
            · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
          | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi'
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n0 hn0 =>
      rcases hi with ⟨rfl, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
      · exact absurd h hq2
      · exact Or.inl ⟨⟨e⟩, h⟩
      · exact absurd h hq2
      · exact absurd h hq3
      · exact absurd h hq2
    | lie d =>
      exfalso
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A r q' =>
        rcases r with _ | _ | r <;>
          simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq2, hq3] at hi
      | twistedA r q' =>
        rcases r with _ | _ | _ | _ | r <;>
          simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq2, hq3] at hi
      | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

end Certified

end Catalogue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4
