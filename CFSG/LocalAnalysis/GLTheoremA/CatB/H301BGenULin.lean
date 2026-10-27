module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlagLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open CFSG.PreuniquenessRankFour.Helpers (faithful_binary_elementary_linear_action_dimension_bound)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self_two (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem neg_eq_self_two (v : V) : -v = v :=
  neg_eq_iff_add_eq_zero.2 (add_self_two v)

section Form

variable {bil : V → V → ZMod 2} (hadd : ∀ x y w, bil (x + y) w = bil x w + bil y w)
include hadd

private theorem bil_zero_left (w : V) : bil 0 w = 0 :=
  map_zero (AddMonoidHom.mk' (fun x => bil x w) fun x y => hadd x y w)

private theorem bil_sub_left (x y w : V) : bil (x - y) w = bil x w - bil y w :=
  map_sub (AddMonoidHom.mk' (fun x => bil x w) fun x y => hadd x y w) x y

private theorem bil_smul_left (c : ZMod 2) (x w : V) : bil (c • x) w = c * bil x w := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
  · rw [zero_smul, zero_mul, bil_zero_left hadd]
  · rw [one_smul, one_mul]

end Form

theorem false_of_isotropic_invariant [Finite V] {E : Type*} [CommGroup E] [Finite E] {k : ℕ}
    (hcard : Nat.card E = 3 ^ k) (hpow : ∀ e : E, e ^ 3 = 1) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 2 * k)
    (bil : V → V → ZMod 2) (hadd : ∀ x y w, bil (x + y) w = bil x w + bil y w)
    (hnd : ∀ w, (∀ v, bil v w = 0) → w = 0) (hρbil : ∀ e v w, bil (ρ e v) (ρ e w) = bil v w)
    (Y : Submodule (ZMod 2) V) (hY : Y ≠ ⊥) (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, bil y y' = 0)
    (hYinv : ∀ e, ∀ y ∈ Y, ρ e y ∈ Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinv' : ∀ e : E, ∀ w, ρ e (ρ e⁻¹ w) = w := fun e w => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  obtain ⟨W, hmemW⟩ : ∃ W : Submodule (ZMod 2) V, ∀ w, w ∈ W ↔ ∀ y ∈ Y, bil w y = 0 :=
    ⟨{ carrier := {w | ∀ y ∈ Y, bil w y = 0}
       add_mem' := fun {a b} ha hb y hy => by rw [hadd, ha y hy, hb y hy, add_zero]
       zero_mem' := fun y _ => bil_zero_left hadd y
       smul_mem' := fun c {a} ha y hy => by rw [bil_smul_left hadd, ha y hy, mul_zero] },
      fun w => Iff.rfl⟩
  have hYW : Y ≤ W := fun y hy => (hmemW y).2 fun y' hy' => hYiso y hy y' hy'
  have hW : W ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY
    refine hy0 (hnd y fun v => ?_)
    have hv : v ∈ W := by rw [htop]; exact Submodule.mem_top
    exact (hmemW v).1 hv y hy
  have hinv : ∀ e : E, ∀ w ∈ W, ρ e w ∈ W := fun e w hw => (hmemW _).2 fun y hy => by
    rw [← hinv' e y, hρbil]
    exact (hmemW w).1 hw _ (hYinv e⁻¹ y hy)
  have hstep : ∀ x : E, (∀ w ∈ W, ρ x w = w) → ∀ v, ρ x v - v ∈ W := by
    intro x hx v
    refine (hmemW _).2 fun y hy => ?_
    have h1 : bil (ρ x v) y = bil v y := by
      calc bil (ρ x v) y = bil (ρ x v) (ρ x y) := by rw [hx y (hYW hy)]
        _ = bil v y := hρbil x v y
    rw [bil_sub_left hadd, h1, sub_self]
  have hmap : ∀ e : E, W.map ((ρ e : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W := fun e => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => hinv e w hw) fun w hw => ?_
    exact ⟨ρ e⁻¹ w, hinv e⁻¹ w hw, hinv' e w⟩
  let r : E →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun e => (ρ e).ofSubmodules W W (hmap e)
      map_one' := LinearEquiv.ext fun w => Subtype.ext (by
        show ρ 1 (w : V) = w
        rw [map_one]
        rfl)
      map_mul' := fun a b => LinearEquiv.ext fun w => Subtype.ext (by
        show ρ (a * b) (w : V) = ρ a (ρ b w)
        rw [map_mul, LinearEquiv.mul_apply]) }
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hfix : ∀ w ∈ W, ρ x w = w := fun w hw =>
      congrArg (fun φ : W ≃ₗ[ZMod 2] W => (φ ⟨w, hw⟩ : V)) hx
    have hsq : ∀ v, ρ x (ρ x v) = v := fun v => by
      have h1 := hfix _ (hstep x hfix v)
      rw [map_sub] at h1
      have h2 : ρ x (ρ x v) = (ρ x v - v) + ρ x v := by rw [← h1]; abel
      rw [h2, sub_add_eq_add_sub, add_self_two, zero_sub, neg_eq_self_two]
    have h3 : ∀ v, ρ x (ρ x (ρ x v)) = v := fun v => by
      have : ρ x ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
      have h := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ v) this
      simpa [pow_succ, LinearEquiv.mul_apply] using h
    apply hρ
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    have := h3 v
    rw [hsq] at this
    exact this
  have hlt := Submodule.finrank_lt hW
  have hle := faithful_binary_elementary_linear_action_dimension_bound (acting := E) (space := W)
    3 k (by norm_num) hcard hpow r hr
  omega

theorem eq_bot_of_normalizes_isometry [Finite V] {k : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * k)
    (bil : V → V → ZMod 2) (hadd : ∀ x y w, bil (x + y) w = bil x w + bil y w)
    (hnd : ∀ w, (∀ v, bil v w = 0) → w = 0)
    {E T : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ k)
    (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V)))
    (hEbil : ∀ g ∈ E, ∀ v w, bil (g v) (g w) = bil v w)
    (hTbil : ∀ g ∈ T, ∀ v w, bil (g v) (g w) = bil v w) : T = ⊥ := by
  haveI : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective _ DFunLike.coe_injective
  by_contra hT0
  obtain ⟨S, hS⟩ : ∃ S : Set V, ∀ u, u ∈ S ↔ ∃ t ∈ T, ∃ v, u = t v - v :=
    ⟨{u | ∃ t ∈ T, ∃ v, u = t v - v}, fun u => Iff.rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Submodule (ZMod 2) V, ∀ c, c ∈ C ↔ ∀ t ∈ T, t c = c :=
    ⟨{ carrier := {c | ∀ t ∈ T, t c = c}
       add_mem' := fun {a b} ha hb t ht => by rw [map_add, ha t ht, hb t ht]
       zero_mem' := fun t _ => map_zero t
       smul_mem' := fun c {a} ha t ht => by rw [map_smul, ha t ht] },
      fun c => Iff.rfl⟩
  have hgen : ∀ t ∈ T, ∀ v, t v - v ∈ Submodule.span (ZMod 2) S := fun t ht v =>
    Submodule.subset_span ((hS _).2 ⟨t, ht, v, rfl⟩)
  have hDC : ∀ d ∈ Submodule.span (ZMod 2) S, ∀ c ∈ C, bil d c = 0 := by
    intro d hd c hc
    induction hd using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨t, ht, v, rfl⟩ := (hS u).1 hu
      calc bil (t v - v) c = bil (t v) c - bil v c := bil_sub_left hadd _ _ _
        _ = bil (t v) (t c) - bil v c := by rw [(hC c).1 hc t ht]
        _ = 0 := by rw [hTbil t ht, sub_self]
    | zero => exact bil_zero_left hadd c
    | add x y _ _ hx hy => rw [hadd, hx, hy, add_zero]
    | smul a x _ hx => rw [bil_smul_left hadd, hx, mul_zero]
  have hDT : ∀ s ∈ T, ∀ u ∈ Submodule.span (ZMod 2) S,
      (s : V ≃ₗ[ZMod 2] V) u ∈ Submodule.span (ZMod 2) S := by
    intro s hs u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨t, ht, v, rfl⟩ := (hS u).1 hu
      have e : s (t v - v) = ((s * t) v - v) - (s v - v) := by
        rw [map_sub, LinearEquiv.mul_apply]
        abel
      rw [e]
      exact Submodule.sub_mem _ (hgen _ (T.mul_mem hs ht) v) (hgen s hs v)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hDE : ∀ g ∈ E, ∀ u ∈ Submodule.span (ZMod 2) S,
      (g : V ≃ₗ[ZMod 2] V) u ∈ Submodule.span (ZMod 2) S := by
    intro g hg u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨t, ht, v, rfl⟩ := (hS u).1 hu
      have htg : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hET hg) t).1 ht
      have e : g (t v - v) = (g * t * g⁻¹) (g v) - g v := by
        rw [map_sub]
        show g (t v) - g v = g (t (g.symm (g v))) - g v
        rw [LinearEquiv.symm_apply_apply]
      rw [e]
      exact hgen _ htg _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hCE : ∀ g ∈ E, ∀ c ∈ C, (g : V ≃ₗ[ZMod 2] V) c ∈ C := by
    intro g hg c hc
    refine (hC _).2 fun t ht => ?_
    have htg : g⁻¹ * t * g ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 (hET (E.inv_mem hg)) t).1 ht
      rwa [inv_inv] at this
    calc t (g c) = g ((g⁻¹ * t * g) c) := (g.apply_symm_apply (t (g c))).symm
      _ = g c := by rw [(hC c).1 hc _ htg]
  have hD0 : Submodule.span (ZMod 2) S ≠ ⊥ := by
    obtain ⟨t, ht, ht1⟩ := (Subgroup.bot_or_exists_ne_one T).resolve_left hT0
    obtain ⟨v, hv⟩ : ∃ v, t v ≠ v := by
      by_contra h
      push Not at h
      exact ht1 (LinearEquiv.ext h)
    exact (Submodule.ne_bot_iff _).2 ⟨t v - v, hgen t ht v, sub_ne_zero.2 hv⟩
  obtain ⟨y, hyD, hy0, hyfix⟩ :=
    CFSG.Quasithin.H13.Flag.exists_fixed_mem T hT (Submodule.span (ZMod 2) S) hDT hD0
  haveI := hE.1
  letI : CommGroup E := IsMulCommutative.instCommGroup
  refine false_of_isotropic_invariant (E := E) hEc (fun e => Subtype.ext (hE.2 e e.2))
    E.subtype E.subtype_injective hdim bil hadd hnd (fun e v w => hEbil e e.2 v w)
    (Submodule.span (ZMod 2) S ⊓ C) ?_ ?_ ?_
  · exact (Submodule.ne_bot_iff _).2 ⟨y, Submodule.mem_inf.2 ⟨hyD, (hC y).2 hyfix⟩, hy0⟩
  · intro a ha b hb
    exact hDC a (Submodule.mem_inf.1 ha).1 b (Submodule.mem_inf.1 hb).2
  · intro e a ha
    exact Submodule.mem_inf.2
      ⟨hDE e e.2 a (Submodule.mem_inf.1 ha).1, hCE e e.2 a (Submodule.mem_inf.1 ha).2⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
