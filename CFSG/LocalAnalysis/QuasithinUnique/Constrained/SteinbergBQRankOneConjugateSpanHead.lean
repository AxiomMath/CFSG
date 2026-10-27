module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQRankOneChainIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.QuasithinUnique

open Module

namespace SteinbergBQ.RankOneHead

open SteinbergBQ.RankOne

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem conj_mem_closure_conj {H : Subgroup (LinearMap.GeneralLinearGroup F V)}
    {t : LinearMap.GeneralLinearGroup F V} {g : LinearMap.GeneralLinearGroup F V} (hg : g ∈ H)
    {n : LinearMap.GeneralLinearGroup F V}
    (hn : n ∈ Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹}) :
    g * n * g⁻¹ ∈ Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹} := by
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨g * h, H.mul_mem hg hh, by group⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have h1 : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have h1 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ hx

theorem closure_conj_le {H : Subgroup (LinearMap.GeneralLinearGroup F V)}
    {t : LinearMap.GeneralLinearGroup F V} (ht : t ∈ H) :
    Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹} ≤ H := by
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, rfl⟩
  exact H.mul_mem (H.mul_mem hh ht) (H.inv_mem hh)

theorem mul_apply' (g h : LinearMap.GeneralLinearGroup F V) (v : V) :
    ((g * h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v =
      (g : V →ₗ[F] V) ((h : V →ₗ[F] V) v) := by
  rw [Units.val_mul, Module.End.mul_apply]

theorem injective_apply (g : LinearMap.GeneralLinearGroup F V) :
    Function.Injective (g : V →ₗ[F] V) := fun x y hxy => by
  rw [← inv_apply_apply g x, hxy, inv_apply_apply]

theorem eq_span_of_finrank_eq_one [FiniteDimensional F V] {E : Submodule F V}
    (hE : finrank F E = 1) {e : V} (he : e ∈ E) (he0 : e ≠ 0) : E = F ∙ e := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem e E).2 he) ?_
  rw [finrank_span_singleton he0, hE]

theorem finrank_map_of_disjoint {W : Type*} [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (E : Submodule F V) (hE : Disjoint E (LinearMap.ker f)) :
    finrank F (E.map f) = finrank F E := by
  rw [← LinearMap.range_domRestrict]
  refine LinearMap.finrank_range_of_inj fun x y hxy => ?_
  have h1 : (x : V) - y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.2 hxy
  have h2 : (x : V) - y ∈ E := E.sub_mem x.2 y.2
  exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hE) _ h2 h1))

theorem one_add_pow_of_sq_eq_zero {f : V →ₗ[F] V} (hf : f * f = 0) (n : ℕ) :
    (1 + f) ^ n = 1 + n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_assoc, hf,
      smul_zero, add_zero, succ_nsmul]
    abel

theorem trivialOnBoth_le_pCore {p : ℕ} [CharP F p] (H : Subgroup (LinearMap.GeneralLinearGroup F V))
    {C : Submodule F V}
    (hCH : ∀ h ∈ H, ∀ c ∈ C, (h : V →ₗ[F] V) c ∈ C) {a : H}
    (ha : (∀ c ∈ C, ((a : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c) ∧
      ∀ v, ((a : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C) :
    a ∈ CFSG.pCore p H := by
  classical
  let A : Subgroup H :=
    { carrier := {a | (∀ c ∈ C, ((a : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c) ∧
        ∀ v, ((a : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C}
      one_mem' := ⟨fun c _ => rfl, fun v => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun c hc => ?_, fun v => ?_⟩
        · change ((a * b : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c
          rw [mul_apply', hb1 c hc, ha1 c hc]
        · change ((a * b : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C
          rw [mul_apply']
          have h1 := C.add_mem (ha2 (((b : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v))
            (hb2 v)
          rwa [sub_add_sub_cancel] at h1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨fun c hc => ?_, fun v => ?_⟩
        · change ((a⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c
          conv_lhs => rw [← ha1 c hc]
          exact inv_apply_apply _ c
        · change ((a⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C
          have h1 := ha2 (((a⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v)
          rw [apply_inv_apply] at h1
          have h2 := C.neg_mem h1
          rwa [neg_sub] at h2 }
  have hAn : A.Normal := by
    refine ⟨fun a ha g => ⟨fun c hc => ?_, fun v => ?_⟩⟩
    · change ((g * a * g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c
      rw [mul_apply', mul_apply', ha.1 _ (hCH _ (g⁻¹).2 c hc)]
      exact apply_inv_apply (g : LinearMap.GeneralLinearGroup F V) c
    · change ((g * a * g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C
      rw [mul_apply', mul_apply']
      have h1 := hCH _ g.2 _ (ha.2 (((g⁻¹ : LinearMap.GeneralLinearGroup F V) :
        V →ₗ[F] V) v))
      rwa [map_sub, apply_inv_apply] at h1
  have hAp : IsPGroup p A := by
    intro a
    refine ⟨1, ?_⟩
    obtain ⟨ha1, ha2⟩ := a.2
    set f : V →ₗ[F] V := ((a : H) : LinearMap.GeneralLinearGroup F V) - 1 with hf
    have hfC : ∀ v, f v ∈ C := fun v => by
      rw [hf, LinearMap.sub_apply, Module.End.one_apply]
      exact ha2 v
    have hff : f * f = 0 := by
      ext v
      rw [Module.End.mul_apply, LinearMap.zero_apply, hf, LinearMap.sub_apply,
        Module.End.one_apply, ha1 _ (hfC v), sub_self]
    have h1 : (((a : H) : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) = 1 + f := by
      rw [hf]
      abel
    have h2 : (p • f : V →ₗ[F] V) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, h1,
      one_add_pow_of_sq_eq_zero hff, h2, add_zero]
    rfl
  have hA : A ≤ CFSG.pCore p H := le_sSup ⟨hAn, hAp⟩
  exact hA ha

end SteinbergBQ.RankOneHead

open SteinbergBQ.RankOne SteinbergBQ.RankOneHead

theorem rank_one_conjugate_span_faithful_irreducible_head {p : ℕ} [Fact p.Prime] {F V : Type*}
    [Field F] [CharP F p] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (LinearMap.GeneralLinearGroup F V)) [Finite H] (hOp : CFSG.pCore p H = ⊥)
    {t : LinearMap.GeneralLinearGroup F V} (ht : t ∈ H)
    (hrank : finrank F (LinearMap.range ((t : V →ₗ[F] V) - 1)) = 1) {E : Submodule F V}
    (hE : E = LinearMap.range ((t : V →ₗ[F] V) - 1))
    (hspan : ⨆ h ∈ H, E.map (h : V →ₗ[F] V) = ⊤) {N : Subgroup (LinearMap.GeneralLinearGroup F V)}
    (hN : N = Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹}) {C : Submodule F V}
    (hC : ∀ v, v ∈ C ↔ ∀ n ∈ N, (n : V →ₗ[F] V) v = v) :
    Submodule.span F {x | ∃ n ∈ N, ∃ v, x = (n : V →ₗ[F] V) v - v} = ⊤ ∧
      C ≠ ⊤ ∧ (∀ h ∈ H, ∀ c ∈ C, (h : V →ₗ[F] V) c ∈ C) ∧
      (∀ W : Submodule F V, (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[F] V) w ∈ W) → W ≠ ⊤ → W ≤ C) ∧
      ∃ ρ : H →* LinearMap.GeneralLinearGroup F (V ⧸ C),
        (∀ (h : H) (v : V), ((ρ h : LinearMap.GeneralLinearGroup F (V ⧸ C)) :
          (V ⧸ C) →ₗ[F] (V ⧸ C)) (C.mkQ v) =
            C.mkQ (((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v)) ∧
        Function.Injective ρ ∧ Nontrivial (V ⧸ C) ∧
        (∀ U : Submodule F (V ⧸ C), (∀ h : H, ∀ u ∈ U,
          ((ρ h : LinearMap.GeneralLinearGroup F (V ⧸ C)) : (V ⧸ C) →ₗ[F] (V ⧸ C)) u ∈ U) →
            U = ⊥ ∨ U = ⊤) ∧
        Set.InjOn C.mkQ E ∧
        ∀ x : H, (∃ h ∈ H, (x : LinearMap.GeneralLinearGroup F V) = h * t * h⁻¹) →
          finrank F (LinearMap.range (((ρ x : LinearMap.GeneralLinearGroup F (V ⧸ C)) :
            (V ⧸ C) →ₗ[F] (V ⧸ C)) - 1)) = 1 := by
  classical
  subst hN
  set N := Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹} with hNdef
  have hNH : N ≤ H := closure_conj_le ht
  have htN : t ∈ N := Subgroup.subset_closure ⟨1, H.one_mem, by group⟩
  have hTe : ∀ v, ((t : V →ₗ[F] V) - 1) v = (t : V →ₗ[F] V) v - v := fun v => by
    rw [LinearMap.sub_apply, Module.End.one_apply]
  have hCH : ∀ h ∈ H, ∀ c ∈ C, (h : V →ₗ[F] V) c ∈ C := by
    intro h hh c hc
    rw [hC]
    intro n hn
    have h1 := (hC c).1 hc (h⁻¹ * n * h)
      (by simpa using conj_mem_closure_conj (H.inv_mem hh) hn)
    rw [mul_apply', mul_apply'] at h1
    have h2 := congrArg (h : V →ₗ[F] V) h1
    rwa [apply_inv_apply] at h2
  have hEne : ∃ e ∈ E, e ≠ 0 := by
    by_contra h1
    push Not at h1
    have h2 : E = ⊥ := (Submodule.eq_bot_iff E).2 h1
    rw [← hE, h2, finrank_bot] at hrank
    exact absurd hrank (by norm_num)
  have hrankE : finrank F E = 1 := hE ▸ hrank
  have hEC : E ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro e ⟨heE, heC⟩
    by_contra he0
    have h1 : E ≤ C := by
      rw [eq_span_of_finrank_eq_one hrankE heE he0]
      exact (Submodule.span_singleton_le_iff_mem e C).2 heC
    have h2 : (⊤ : Submodule F V) ≤ C := by
      rw [← hspan]
      refine iSup₂_le fun h hh => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hCH h hh x (h1 hx)
    obtain ⟨e', he'E, he'0⟩ := hEne
    obtain ⟨w, rfl⟩ : ∃ w, ((t : V →ₗ[F] V) - 1) w = e' := by
      rw [hE] at he'E
      exact he'E
    apply he'0
    rw [hTe, (hC w).1 (h2 Submodule.mem_top) t htN, sub_self]
  have hCtop : C ≠ ⊤ := by
    intro h1
    obtain ⟨e, heE, he0⟩ := hEne
    have h2 : e ∈ E ⊓ C := ⟨heE, h1 ▸ Submodule.mem_top⟩
    rw [hEC] at h2
    exact he0 ((Submodule.mem_bot F).1 h2)
  have hVN : Submodule.span F {x | ∃ n ∈ N, ∃ v, x = (n : V →ₗ[F] V) v - v} = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup₂_le fun h hh => ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hE] at hx
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨h * t * h⁻¹, Subgroup.subset_closure ⟨h, hh, rfl⟩,
      (h : V →ₗ[F] V) w, ?_⟩
    rw [hTe, map_sub, mul_apply', mul_apply', inv_apply_apply]
  have hmax : ∀ W : Submodule F V, (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[F] V) w ∈ W) → W ≠ ⊤ →
      W ≤ C := by
    intro W hW hWtop
    have htW : ∀ w ∈ W, (t : V →ₗ[F] V) w = w := by
      intro w hw
      by_contra h1
      have h2 : ((t : V →ₗ[F] V) - 1) w ≠ 0 := by
        rw [hTe]
        exact sub_ne_zero.2 h1
      have h3 : ((t : V →ₗ[F] V) - 1) w ∈ W := by
        rw [hTe]
        exact W.sub_mem (hW t ht w hw) hw
      have h4 : E ≤ W := by
        rw [eq_span_of_finrank_eq_one hrankE (hE ▸ LinearMap.mem_range_self _ w) h2]
        exact (Submodule.span_singleton_le_iff_mem _ W).2 h3
      apply hWtop
      rw [eq_top_iff, ← hspan]
      refine iSup₂_le fun h hh => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hW h hh x (h4 hx)
    have hfixN : ∀ n ∈ N, ∀ w ∈ W, (n : V →ₗ[F] V) w = w := by
      intro n hn
      induction hn using Subgroup.closure_induction'' with
      | mem x hx =>
        intro w hw
        obtain ⟨h, hh, rfl⟩ := hx
        rw [mul_apply', mul_apply', htW _ (hW _ (H.inv_mem hh) w hw), apply_inv_apply]
      | inv_mem x hx =>
        intro w hw
        obtain ⟨h, hh, rfl⟩ := hx
        have h1 : ((h * t * h⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) w = w := by
          rw [mul_apply', mul_apply', htW _ (hW _ (H.inv_mem hh) w hw), apply_inv_apply]
        conv_lhs => rw [← h1]
        exact inv_apply_apply _ w
      | one =>
        intro w _
        rfl
      | mul x y _ _ hx hy =>
        intro w hw
        rw [mul_apply', hy w hw, hx w hw]
    intro w hw
    rw [hC]
    intro n hn
    exact hfixN n hn w hw
  have hinv : ∀ h : H, C ≤ C.comap ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) :=
    fun h c hc => hCH _ h.2 c hc
  let ρ₀ : H →* Module.End F (V ⧸ C) :=
    { toFun := fun h => C.mapQ C ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) (hinv h)
      map_one' := by
        refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun v => ?_
        rw [Submodule.mapQ_apply, Module.End.one_apply]
        rfl
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun v => ?_
        rw [Module.End.mul_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
          Submodule.mapQ_apply, Subgroup.coe_mul, mul_apply'] }
  let ρ : H →* LinearMap.GeneralLinearGroup F (V ⧸ C) := ρ₀.toHomUnits
  have hρ : ∀ (h : H) (v : V), ((ρ h : LinearMap.GeneralLinearGroup F (V ⧸ C)) :
      (V ⧸ C) →ₗ[F] (V ⧸ C)) (C.mkQ v) =
        C.mkQ (((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v) := fun h v =>
    Submodule.mapQ_apply (h := hinv h) _ _ _ v
  have hNt : Nontrivial (V ⧸ C) := Submodule.Quotient.nontrivial_iff.2 hCtop
  refine ⟨hVN, hCtop, hCH, hmax, ρ, hρ, ?_, hNt, ?_, ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro h hh1
    have hhC : ∀ v, ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v ∈ C := by
      intro v
      have h1 := hρ h v
      rw [hh1, Units.val_one, Module.End.one_apply] at h1
      exact (Submodule.Quotient.eq C).1 h1.symm
    have hcomm : ∀ n (hn : n ∈ N), h * ⟨n, hNH hn⟩ = ⟨n, hNH hn⟩ * h := by
      intro n hn
      have h1 : h * ⟨n, hNH hn⟩ * h⁻¹ * (⟨n, hNH hn⟩ : H)⁻¹ ∈ CFSG.pCore p H := by
        refine trivialOnBoth_le_pCore H hCH ⟨fun c hc => ?_, fun v => ?_⟩
        · have hn' : ∀ c ∈ C, (n : V →ₗ[F] V) c = c := fun c hc => (hC c).1 hc n hn
          have hninv : ∀ c ∈ C, ((n⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) c = c :=
            fun c hc => by
              conv_lhs => rw [← hn' c hc]
              exact inv_apply_apply _ c
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [mul_apply', mul_apply', mul_apply', hninv c hc,
            hn' _ (hCH _ (H.inv_mem h.2) c hc), apply_inv_apply]
        · have h2 : ρ (h * ⟨n, hNH hn⟩ * h⁻¹ * (⟨n, hNH hn⟩ : H)⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, hh1, inv_one, one_mul, mul_one,
              mul_inv_cancel]
          have h3 := hρ (h * ⟨n, hNH hn⟩ * h⁻¹ * (⟨n, hNH hn⟩ : H)⁻¹) v
          rw [h2, Units.val_one, Module.End.one_apply] at h3
          exact (Submodule.Quotient.eq C).1 h3.symm
      rw [hOp, Subgroup.mem_bot] at h1
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
    have hfix : ∀ x ∈ Submodule.span F {x | ∃ n ∈ N, ∃ v, x = (n : V →ₗ[F] V) v - v},
        ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x = x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, hn, v, rfl⟩ := hx
        have h1 := congrArg (fun k : H => ((k : LinearMap.GeneralLinearGroup F V) :
          V →ₗ[F] V) v) (hcomm n hn)
        simp only [Subgroup.coe_mul, mul_apply'] at h1
        set c := ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v - v with hc
        have h2 : ((h : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) v = v + c := by
          rw [hc]
          abel
        rw [map_sub, h1, h2, map_add, (hC c).1 (hhC v) n hn]
        abel
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | smul a x _ hx => rw [map_smul, hx]
    apply Subtype.ext
    apply Units.ext
    ext v
    exact hfix v (hVN ▸ Submodule.mem_top)
  ·
    intro U hU
    set W := U.comap C.mkQ with hW
    have hWH : ∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[F] V) w ∈ W := by
      intro h hh w hw
      rw [hW, Submodule.mem_comap] at hw ⊢
      have h1 := hU ⟨h, hh⟩ _ hw
      rwa [hρ] at h1
    by_cases hWt : W = ⊤
    · right
      rw [eq_top_iff]
      intro u _
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective C u
      have h1 : v ∈ W := hWt ▸ Submodule.mem_top
      exact h1
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective C u
      have h1 : v ∈ C := hmax W hWH hWt hu
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h1
  ·
    intro x hx y hy hxy
    have h1 : x - y ∈ C := (Submodule.Quotient.eq C).1 hxy
    have h2 : x - y ∈ E ⊓ C := ⟨E.sub_mem hx hy, h1⟩
    rw [hEC] at h2
    exact sub_eq_zero.1 ((Submodule.mem_bot F).1 h2)
  ·
    rintro x ⟨h, hh, hx⟩
    have h1 : (((ρ x : LinearMap.GeneralLinearGroup F (V ⧸ C)) : (V ⧸ C) →ₗ[F] (V ⧸ C)) - 1) ∘ₗ
        C.mkQ = C.mkQ ∘ₗ ((h : V →ₗ[F] V) ∘ₗ ((t : V →ₗ[F] V) - 1) ∘ₗ
          ((h⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V)) := by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
        Module.End.one_apply]
      rw [hρ, hx, mul_apply', mul_apply', map_sub (h : V →ₗ[F] V), apply_inv_apply, map_sub]
    have h2 : LinearMap.range (((ρ x : LinearMap.GeneralLinearGroup F (V ⧸ C)) :
        (V ⧸ C) →ₗ[F] (V ⧸ C)) - 1) =
        (E.map (h : V →ₗ[F] V)).map C.mkQ := by
      rw [← LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ C), h1,
        LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top,
        ← hE]
      exact LinearMap.range_eq_top.2 fun v => ⟨(h : V →ₗ[F] V) v, inv_apply_apply h v⟩
    rw [h2, finrank_map_of_disjoint, finrank_map_of_disjoint, hrankE]
    · rw [Submodule.disjoint_def]
      intro e _ he
      exact injective_apply h (by rw [LinearMap.mem_ker.1 he, map_zero])
    · rw [Submodule.disjoint_def]
      rintro _ ⟨e, heE, rfl⟩ he
      rw [Submodule.ker_mkQ] at he
      have h3 : e ∈ C := by
        have h4 := hCH _ (H.inv_mem hh) _ he
        rwa [inv_apply_apply] at h4
      have h4 : e ∈ E ⊓ C := ⟨heE, h3⟩
      rw [hEC] at h4
      rw [(Submodule.mem_bot F).1 h4, map_zero]

end CFSG.QuasithinUnique
