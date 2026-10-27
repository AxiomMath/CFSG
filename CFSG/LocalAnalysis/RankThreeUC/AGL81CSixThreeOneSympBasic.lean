module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympDefs
import CFSG.LocalAnalysis.ComponentInitial.OddSymplecticSummand

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup
  neg_one_mem_bilinIsometryGroup)
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply
  symplecticTransvection_mul symplecticTransvection_zero
  symplecticTransvection_mem_bilinIsometryGroup alternating_pairing_surjectivity)

theorem isometry_of_similitude_of_orderOf_eq_prime_pow {p : ℕ} [Fact p.Prime] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] {B : LinearMap.BilinForm (ZMod p) W} (hB : B ≠ 0)
    {x : (Module.End (ZMod p) W)ˣ} {k : ℕ} (hx : orderOf x = p ^ k) {c : ZMod p}
    (hc : ∀ u v : W, B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) =
      c * B u v) :
    ∀ u v : W, B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v := by
  let f : Module.End (ZMod p) W := x
  have hfpow : ∀ m : ℕ, ∀ u v : W, B ((f ^ m) u) ((f ^ m) v) = c ^ m * B u v := by
    intro m
    induction m with
    | zero => intro u v; simp
    | succ m ih =>
        intro u v
        have hstep : B ((f ^ (m + 1)) u) ((f ^ (m + 1)) v) =
            B ((f ^ m) (f u)) ((f ^ m) (f v)) := by
          rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [hstep, ih (f u) (f v), hc u v, pow_succ]
        ring
  have hfix : f ^ (p ^ k) = 1 := by
    have h1 : x ^ (p ^ k) = 1 := by rw [← hx, pow_orderOf_eq_one]
    simpa [f] using congrArg Units.val h1
  have hc1 : c ^ (p ^ k) = 1 := by
    by_contra hne
    apply hB
    refine BilinForm.ext fun u v => ?_
    have h := hfpow (p ^ k) u v
    rw [hfix, Module.End.one_apply] at h
    have hzero : (c ^ (p ^ k) - 1) * B u v = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr h.symm
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  have hc_eq : c = 1 := by
    have h := ZMod.pow_card_pow (p := p) (n := k) c
    rw [← h]
    exact hc1
  intro u v
  rw [hc u v, hc_eq, one_mul]

theorem isometry_of_mem_of_oPPrimeHull {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W] {B : LinearMap.BilinForm (ZMod p) W} (hB : B ≠ 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} (hH : oPPrimeHull p H = H)
    (hsim : ∀ x ∈ H, ∃ c : ZMod p, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = c * B u v) :
    ∀ x ∈ H, ∀ u v : W, B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) =
      B u v := by
  rw [oPPrimeHull] at hH
  rw [← hH]
  refine (Subgroup.closure_le (bilinIsometryGroup B)).mpr ?_
  rintro x ⟨hxH, k, hk⟩
  change x ∈ bilinIsometryGroup B
  rw [mem_bilinIsometryGroup]
  obtain ⟨c, hc⟩ := hsim x hxH
  exact isometry_of_similitude_of_orderOf_eq_prime_pow hB hk hc

def planeTransvection {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K W) (hB : B.IsAlt) (e₁ e₂ : W) (a b : K) :
    (Module.End K W)ˣ :=
  symplecticTransvection B hB e₁ (-a) * symplecticTransvection B hB e₂ (-b)

theorem planeTransvection_apply {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt} {e₁ e₂ : W}
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0)
    (a b : K) (x : W) :
    ((planeTransvection B hB e₁ e₂ a b : Module.End K W) x) =
      x + (a * B e₁ x) • e₁ + (b * B e₂ x) • e₂ := by
  rw [planeTransvection, Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply,
    symplecticTransvection_apply]
  have hBx1 : B (x + ((-b) * B x e₂) • e₂) e₁ = B x e₁ := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h21, smul_zero, add_zero]
  rw [hBx1, ← hB.neg_eq e₁ x, ← hB.neg_eq e₂ x]
  module

theorem planeTransvection_mul {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt} {e₁ e₂ : W}
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0)
    (a b a' b' : K) :
    planeTransvection B hB e₁ e₂ a b * planeTransvection B hB e₁ e₂ a' b' =
      planeTransvection B hB e₁ e₂ (a + a') (b + b') := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [Units.val_mul, Module.End.mul_apply, planeTransvection_apply h11 h12 h21 h22,
    planeTransvection_apply h11 h12 h21 h22, planeTransvection_apply h11 h12 h21 h22]
  simp only [map_add, map_smul, h11, h12, h21, h22, mul_zero, add_zero]
  module

theorem planeTransvection_zero {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt} {e₁ e₂ : W}
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    planeTransvection B hB e₁ e₂ 0 0 = 1 := by
  simp [planeTransvection, symplecticTransvection_zero]

theorem planeTransvection_mem_bilinIsometryGroup {K : Type*} [Field K] {W : Type*}
    [AddCommGroup W] [Module K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt}
    {e₁ e₂ : W} (a b : K) :
    planeTransvection B hB e₁ e₂ a b ∈ bilinIsometryGroup B := by
  rw [planeTransvection]
  exact (bilinIsometryGroup B).mul_mem
    (symplecticTransvection_mem_bilinIsometryGroup hB e₁ (-a))
    (symplecticTransvection_mem_bilinIsometryGroup hB e₂ (-b))

theorem planeTransvection_apply_of_mem_span {K : Type*} [Field K] {W : Type*}
    [AddCommGroup W] [Module K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt}
    {e₁ e₂ : W} (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0)
    (h22 : B e₂ e₂ = 0) (a b : K) {u : W}
    (hu : u ∈ Submodule.span K ({e₁, e₂} : Set W)) :
    ((planeTransvection B hB e₁ e₂ a b : Module.End K W) u) = u := by
  have hfix : ∀ y : W, ((planeTransvection B hB e₁ e₂ a b : Module.End K W) y) =
      y + (a * B e₁ y) • e₁ + (b * B e₂ y) • e₂ :=
    planeTransvection_apply h11 h12 h21 h22 a b
  refine Submodule.span_induction (p := fun u _ =>
    ((planeTransvection B hB e₁ e₂ a b : Module.End K W) u) = u) ?_ ?_ ?_ ?_ hu
  · rintro u (rfl | rfl)
    · rw [hfix]; simp [h11, h21]
    · rw [hfix]; simp [h12, h22]
  · simp
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro c x _ hx
    rw [map_smul, hx]

def planeTransvectionHom {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K W) (hB : B.IsAlt) (e₁ e₂ : W)
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    Multiplicative (K × K) →* (Module.End K W)ˣ where
  toFun v := planeTransvection B hB e₁ e₂ (v.toAdd).1 (v.toAdd).2
  map_one' := planeTransvection_zero h11 h12 h21 h22
  map_mul' v w := by
    have hv : (v * w).toAdd = v.toAdd + w.toAdd := rfl
    rw [hv, Prod.fst_add, Prod.snd_add, planeTransvection_mul h11 h12 h21 h22]

theorem planeTransvection_eq_one {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt}
    {e₁ e₂ : W} (hBnd : B.Nondegenerate) (hli : LinearIndependent K ![e₁, e₂])
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0)
    (a b : K) :
    planeTransvection B hB e₁ e₂ a b = 1 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := alternating_pairing_surjectivity hBnd hli (fun _ : Fin 2 => (1 : K))
    have hx₁ : B e₁ x ≠ 0 := by
      have h1 : B e₁ x = 1 := by simpa using congrFun hx 0
      rw [h1]
      exact one_ne_zero
    have hx₂ : B e₂ x ≠ 0 := by
      have h1 : B e₂ x = 1 := by simpa using congrFun hx 1
      rw [h1]
      exact one_ne_zero
    have hact := congrArg (fun g : (Module.End K W)ˣ =>
      (g : Module.End K W) x) h
    rw [planeTransvection_apply h11 h12 h21 h22 a b x] at hact
    simp only [Units.val_one, Module.End.one_apply] at hact
    have hsum : (a * B e₁ x) • e₁ + (b * B e₂ x) • e₂ = 0 := by
      have h' : x + ((a * B e₁ x) • e₁ + (b * B e₂ x) • e₂) = x + 0 := by
        calc x + ((a * B e₁ x) • e₁ + (b * B e₂ x) • e₂)
            = (x + (a * B e₁ x) • e₁) + (b * B e₂ x) • e₂ := (add_assoc _ _ _).symm
          _ = x := hact
          _ = x + 0 := (add_zero x).symm
      exact add_left_cancel h'
    obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp hli) (a * B e₁ x) (b * B e₂ x) hsum
    exact ⟨(mul_eq_zero.mp ha).resolve_right hx₁, (mul_eq_zero.mp hb).resolve_right hx₂⟩
  · rintro ⟨rfl, rfl⟩
    exact planeTransvection_zero h11 h12 h21 h22

theorem planeTransvectionHom_injective {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt}
    {e₁ e₂ : W} (hBnd : B.Nondegenerate) (hli : LinearIndependent K ![e₁, e₂])
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    Function.Injective (planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22) := by
  intro v w hvw
  have h1 : planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22 (v * w⁻¹) = 1 := by
    rw [map_mul]
    rw [show (planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22) (w⁻¹) =
      ((planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22) w)⁻¹ from map_inv _ _]
    rw [hvw]
    exact mul_inv_cancel _
  have h2 : planeTransvection B hB e₁ e₂ ((v * w⁻¹).toAdd).1 ((v * w⁻¹).toAdd).2 = 1 := h1
  obtain ⟨ha, hb⟩ :=
    (planeTransvection_eq_one hBnd hli h11 h12 h21 h22 _ _).mp h2
  have hzero : (v * w⁻¹).toAdd = 0 := Prod.ext ha hb
  have hveq : v * w⁻¹ = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hzero
  calc v = v * (w⁻¹ * w) := by rw [inv_mul_cancel, mul_one]
    _ = v * w⁻¹ * w := by rw [mul_assoc]
    _ = 1 * w := by rw [hveq]
    _ = w := one_mul w

theorem card_range_planeTransvectionHom {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W} {hB : B.IsAlt}
    {e₁ e₂ : W} (hBnd : B.Nondegenerate) (hli : LinearIndependent K ![e₁, e₂])
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    Nat.card (planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22).range = Nat.card K ^ 2 := by
  have hD : Nat.card (Multiplicative (K × K)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, pow_two]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (planeTransvectionHom_injective hBnd hli h11 h12 h21 h22)).toEquiv).symm.trans hD

theorem isElemAbelian_range_planeTransvectionHom {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [CharP K p] {W : Type*} [AddCommGroup W] [Module K W] {B : LinearMap.BilinForm K W}
    {hB : B.IsAlt} {e₁ e₂ : W} (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0)
    (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    CFSG.Open.IsElemAbelian p
      (planeTransvectionHom B hB e₁ e₂ h11 h12 h21 h22).range := by
  have hpow : ∀ v : Multiplicative (K × K), v ^ p = 1 := by
    intro v
    have hcast : ∀ n : ℕ, (v ^ n).toAdd = n • v.toAdd := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ]
          change (v ^ n).toAdd + v.toAdd = (n + 1) • v.toAdd
          rw [ih, succ_nsmul]
    apply Multiplicative.toAdd.injective
    rw [hcast p]
    change p • v.toAdd = 0
    ext <;> simp [nsmul_eq_mul, CharP.cast_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro x y
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    change (x : (Module.End K W)ˣ) * (y : (Module.End K W)ˣ) =
      (y : (Module.End K W)ˣ) * (x : (Module.End K W)ˣ)
    rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm v w]
  · intro x hx
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hx
    rw [← hv, ← map_pow, hpow, map_one]

theorem exists_isotropic_pair_of_finrank_four {K : Type*} [Field K] {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : Module.finrank K W = 4) (B : LinearMap.BilinForm K W) (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) :
    ∃ e₁ e₂ : W, LinearIndependent K ![e₁, e₂] ∧ B e₁ e₁ = 0 ∧ B e₁ e₂ = 0 ∧
      B e₂ e₁ = 0 ∧ B e₂ e₂ = 0 := by
  obtain ⟨m, b, hdim, hInl, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      B hB hBnd
  have hm : m = 2 := by omega
  subst m
  refine ⟨b (Sum.inl 0), b (Sum.inl 1), ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp : LinearIndependent K (fun i : Fin 2 => b (Sum.inl i)) :=
      b.linearIndependent.comp (fun i : Fin 2 => Sum.inl i) (fun i j hij => by
        simpa using hij)
    have hfun : (fun i : Fin 2 => b (Sum.inl i)) = ![b (Sum.inl 0), b (Sum.inl 1)] := by
      funext i
      fin_cases i <;> simp
    rwa [hfun] at hcomp
  · simpa using hInl 0 0
  · simpa using hInl 0 1
  · simpa using hInl 1 0
  · simpa using hInl 1 1

private theorem finrank_span_pair {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    {e₁ e₂ : W} (hli : LinearIndependent K ![e₁, e₂]) :
    Module.finrank K (Submodule.span K ({e₁, e₂} : Set W)) = 2 := by
  have hspan : Submodule.span K ({e₁, e₂} : Set W) =
      Submodule.span K (Set.range ![e₁, e₂]) := by
    rw [Matrix.range_cons_cons_empty]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

private theorem isOrthogonal_span_pair {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {B : LinearMap.BilinForm K W} {e₁ e₂ : W}
    (h11 : B e₁ e₁ = 0) (h12 : B e₁ e₂ = 0) (h21 : B e₂ e₁ = 0) (h22 : B e₂ e₂ = 0) :
    ∀ u ∈ Submodule.span K ({e₁, e₂} : Set W),
      ∀ v ∈ Submodule.span K ({e₁, e₂} : Set W), B u v = 0 := by
  let π : Submodule K W := Submodule.span K ({e₁, e₂} : Set W)
  have hπorth : π ≤ B.orthogonal π := by
    rw [show π = Submodule.span K ({e₁, e₂} : Set W) from rfl, Submodule.span_le]
    intro u hu
    rcases hu with hu | hu
    · rw [hu]
      refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
      have hker : π ≤ LinearMap.ker (B.flip e₁) := by
        rw [show π = Submodule.span K ({e₁, e₂} : Set W) from rfl, Submodule.span_le]
        intro y hy
        rcases hy with hy | hy
        · rw [hy]; simpa [LinearMap.mem_ker] using h11
        · rw [hy]; simpa [LinearMap.mem_ker] using h21
      intro n hn
      simpa [LinearMap.mem_ker] using hker hn
    · rw [hu]
      refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
      have hker : π ≤ LinearMap.ker (B.flip e₂) := by
        rw [show π = Submodule.span K ({e₁, e₂} : Set W) from rfl, Submodule.span_le]
        intro y hy
        rcases hy with hy | hy
        · rw [hy]; simpa [LinearMap.mem_ker] using h12
        · rw [hy]; simpa [LinearMap.mem_ker] using h22
      intro n hn
      simpa [LinearMap.mem_ker] using hker hn
  intro u hu v hv
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (hπorth hv)) u hu

theorem hasIsotropicPlaneGroup_of_forall_isometry_mem {p : ℕ} [Fact p.Prime] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hH : ∀ g : (Module.End (ZMod p) W)ˣ, (∀ u v : W,
      B ((g : Module.End (ZMod p) W) u) ((g : Module.End (ZMod p) W) v) = B u v) → g ∈ H) :
    HasIsotropicPlaneGroup p B H := by
  haveI : FiniteDimensional (ZMod p) W := ‹Module.Finite (ZMod p) W›
  have hAlt : B.IsAlt := hBalt
  have hBnd' : B.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (show B.SeparatingLeft from hBnd)
  obtain ⟨e₁, e₂, hli, h11, h12, h21, h22⟩ :=
    exists_isotropic_pair_of_finrank_four hW B hAlt hBnd'
  let E : Subgroup (Module.End (ZMod p) W)ˣ :=
    (planeTransvectionHom B hAlt e₁ e₂ h11 h12 h21 h22).range
  let π : Submodule (ZMod p) W := Submodule.span (ZMod p) ({e₁, e₂} : Set W)
  have hπfin : Module.finrank (ZMod p) π = 2 := finrank_span_pair hli
  have hπiso : ∀ u ∈ π, ∀ v ∈ π, B u v = 0 := isOrthogonal_span_pair h11 h12 h21 h22
  refine ⟨hH (-1) (neg_one_mem_bilinIsometryGroup B), E, ?_, ?_, ?_, π, hπfin, hπiso, ?_⟩
  · intro e he
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp he
    exact hH _ (planeTransvection_mem_bilinIsometryGroup (v.toAdd).1 (v.toAdd).2)
  · exact isElemAbelian_range_planeTransvectionHom h11 h12 h21 h22
  · rw [show E = (planeTransvectionHom B hAlt e₁ e₂ h11 h12 h21 h22).range from rfl,
      card_range_planeTransvectionHom hBnd' hli h11 h12 h21 h22, Nat.card_zmod]
  · intro e he u hu
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp he
    exact planeTransvection_apply_of_mem_span h11 h12 h21 h22 (v.toAdd).1 (v.toAdd).2 hu

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
