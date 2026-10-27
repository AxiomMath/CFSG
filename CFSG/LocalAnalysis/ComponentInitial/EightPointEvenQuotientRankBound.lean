module

public import CFSG.GroupActions.PermutationModuleHeart
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

section Defs

variable (Ξ : Type*)

abbrev constQuot : Type _ :=
  (Ξ → ZMod 2) ⧸ Submodule.span (ZMod 2) {(1 : Ξ → ZMod 2)}

variable {Ξ}

@[expose] noncomputable def constQuotAct (g : Equiv.Perm Ξ) :
    constQuot Ξ →ₗ[ZMod 2] constQuot Ξ :=
  Submodule.mapQ _ _ (CFSG.GroupActions.permFun (p := 2) g) (by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.mem_span_singleton_self _)

@[expose] def constQuotFixed (U : Subgroup (Equiv.Perm Ξ)) : Submodule (ZMod 2) (constQuot Ξ) where
  carrier := {q | ∀ u ∈ U, constQuotAct u q = q}
  add_mem' := fun ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c q hq u hu => by rw [map_smul, hq u hu]

end Defs

namespace EightPointQuotient

variable {Ξ : Type*}

@[expose] def dispFun (U : Subgroup (Equiv.Perm Ξ)) : Submodule (ZMod 2) (Ξ → ZMod 2) where
  carrier := {f | ∀ u ∈ U, ∃ c : ZMod 2, ∀ ξ, f (u ξ) = f ξ + c}
  add_mem' := by
    rintro f g hf hg u hu
    obtain ⟨c, hc⟩ := hf u hu
    obtain ⟨c', hc'⟩ := hg u hu
    exact ⟨c + c', fun ξ => by simp only [Pi.add_apply, hc, hc']; ring⟩
  zero_mem' := fun _ _ => ⟨0, fun _ => by simp⟩
  smul_mem' := by
    rintro a f hf u hu
    obtain ⟨c, hc⟩ := hf u hu
    exact ⟨a * c, fun ξ => by simp only [Pi.smul_apply, smul_eq_mul, hc]; ring⟩

theorem mem_span_one_iff {g : Ξ → ZMod 2} :
    g ∈ Submodule.span (ZMod 2) {(1 : Ξ → ZMod 2)} ↔ ∃ c : ZMod 2, ∀ ξ, g ξ = c := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun ξ => by simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun ξ => by simp [hc]⟩

theorem constQuotFixed_eq_map (U : Subgroup (Equiv.Perm Ξ)) :
    constQuotFixed U = (dispFun U).map (Submodule.mkQ _) := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  constructor
  · intro hq
    refine ⟨f, fun u hu => ?_, rfl⟩
    have h := hq u⁻¹ (U.inv_mem hu)
    rw [constQuotAct, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq,
      mem_span_one_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun ξ => ?_⟩
    have := hc ξ
    rw [Pi.sub_apply, CFSG.GroupActions.permFun_apply, inv_inv] at this
    rw [← this]
    ring
  · rintro ⟨g, hg, hgf⟩ u hu
    simp only [Submodule.mkQ_apply] at hgf ⊢
    rw [← hgf, constQuotAct, Submodule.mapQ_apply, Submodule.Quotient.eq, mem_span_one_iff]
    obtain ⟨c, hc⟩ := hg u⁻¹ (U.inv_mem hu)
    exact ⟨c, fun ξ => by
      rw [Pi.sub_apply, CFSG.GroupActions.permFun_apply, hc]
      ring⟩

theorem finrank_constQuotFixed_add_one_le [Finite Ξ] [Nonempty Ξ] (U : Subgroup (Equiv.Perm Ξ)) :
    finrank (ZMod 2) (constQuotFixed U) + 1 ≤ finrank (ZMod 2) (dispFun U) := by
  let φ := (Submodule.mkQ (Submodule.span (ZMod 2) {(1 : Ξ → ZMod 2)})).comp
    (dispFun U).subtype
  have hrange : LinearMap.range φ = constQuotFixed U := by
    rw [constQuotFixed_eq_map, LinearMap.range_comp, Submodule.range_subtype]
  have h1 : (1 : Ξ → ZMod 2) ∈ dispFun U := fun _ _ => ⟨0, fun _ => by simp⟩
  have hker : (⟨1, h1⟩ : dispFun U) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)
  have hne : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    obtain ⟨ξ⟩ := ‹Nonempty Ξ›
    have := congrFun (congrArg Subtype.val hker) ξ
    simp at this
  have hpos := Submodule.finrank_eq_zero.not.mpr hne
  change ¬ finrank (ZMod 2) (LinearMap.ker φ) = 0 at hpos
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at hrn
  change finrank (ZMod 2) (constQuotFixed U) + finrank (ZMod 2) (LinearMap.ker φ) =
    finrank (ZMod 2) (dispFun U) at hrn
  omega

section Core

@[expose] def dispFunV (V Ξ : Type*) [AddCommGroup V] [AddAction V Ξ] :
    Submodule (ZMod 2) (Ξ → ZMod 2) where
  carrier := {f | ∀ v : V, ∃ c : ZMod 2, ∀ ξ, f (v +ᵥ ξ) = f ξ + c}
  add_mem' := by
    rintro f g hf hg v
    obtain ⟨c, hc⟩ := hf v
    obtain ⟨c', hc'⟩ := hg v
    exact ⟨c + c', fun ξ => by simp only [Pi.add_apply, hc, hc']; ring⟩
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  smul_mem' := by
    rintro a f hf v
    obtain ⟨c, hc⟩ := hf v
    exact ⟨a * c, fun ξ => by simp only [Pi.smul_apply, smul_eq_mul, hc]; ring⟩

variable {Ξ : Type*} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddAction V Ξ]

@[expose] def stabSub (ξ : Ξ) : Submodule (ZMod 2) V :=
  AddSubgroup.toZModSubmodule 2 (AddAction.stabilizer V ξ)

theorem mem_stabSub {ξ : Ξ} {v : V} : v ∈ stabSub ξ ↔ v +ᵥ ξ = ξ := by
  simp [stabSub]

omit [AddAction V Ξ] in
theorem f2_add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem stabSub_vadd (w : V) (ξ : Ξ) : stabSub (w +ᵥ ξ) = stabSub (V := V) ξ := by
  ext v
  rw [mem_stabSub, mem_stabSub, ← add_vadd, add_comm, add_vadd]
  exact vadd_left_cancel_iff w

@[expose] noncomputable def dispHom (ξ₀ : Ξ) {f : Ξ → ZMod 2} (hf : f ∈ dispFunV V Ξ) :
    V →ₗ[ZMod 2] ZMod 2 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => f (v +ᵥ ξ₀) - f ξ₀
      map_zero' := by simp
      map_add' := fun v w => by
        obtain ⟨c, hc⟩ := hf v
        obtain ⟨c', hc'⟩ := hf w
        simp only [add_vadd, hc, hc']
        ring }

theorem dispHom_spec (ξ₀ : Ξ) {f : Ξ → ZMod 2} (hf : f ∈ dispFunV V Ξ) (v : V) (ξ : Ξ) :
    f (v +ᵥ ξ) = f ξ + dispHom ξ₀ hf v := by
  obtain ⟨c, hc⟩ := hf v
  show f (v +ᵥ ξ) = f ξ + (f (v +ᵥ ξ₀) - f ξ₀)
  rw [hc, hc ξ₀]
  ring

theorem one_add_lt_two_pow {n : ℕ} (hn : 2 ≤ n) : 1 + n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

theorem arith_bound {ι : Type*} (s : Finset ι) (d : ℕ) (μ : ι → ℕ)
    (h : ∑ i ∈ s, 2 ^ (d + μ i) = 8) :
    (∑ i ∈ s, (1 + μ i)) + 2 * d ≤ 7 ∨ (d = 0 ∧ ∀ i ∈ s, μ i ≤ 1) := by
  have hsum : 2 ^ d * ∑ i ∈ s, 2 ^ μ i = 8 := by
    rw [Finset.mul_sum]
    simpa [pow_add] using h
  have hle : ∑ i ∈ s, (1 + μ i) ≤ ∑ i ∈ s, 2 ^ μ i := Finset.sum_le_sum fun i _ => by
    have := Nat.lt_two_pow_self (n := μ i)
    omega
  by_cases hd : d = 0
  · subst hd
    rw [pow_zero, one_mul] at hsum
    by_cases hμ : ∀ i ∈ s, μ i ≤ 1
    · exact Or.inr ⟨rfl, hμ⟩
    · left
      simp only [not_forall, not_le] at hμ
      obtain ⟨i₀, hi₀, hμi₀⟩ := hμ
      have hlt : ∑ i ∈ s, (1 + μ i) < ∑ i ∈ s, 2 ^ μ i :=
        Finset.sum_lt_sum (fun i _ => by have := Nat.lt_two_pow_self (n := μ i); omega)
          ⟨i₀, hi₀, one_add_lt_two_pow hμi₀⟩
      omega
  · left
    have hpos : 0 < ∑ i ∈ s, 2 ^ μ i := by
      by_contra h0
      rw [Nat.le_zero.mp (not_lt.mp h0), mul_zero] at hsum
      omega
    have hd3 : d ≤ 3 := by
      by_contra hd3
      have : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ d ≤ 2 ^ d * ∑ i ∈ s, 2 ^ μ i := Nat.le_mul_of_pos_right _ hpos
      omega
    interval_cases d <;> norm_num at hsum <;> omega

theorem eq_or_eq_of_ncard_eq_two {s : Set Ξ} (hs : s.ncard = 2) {a b ξ : Ξ} (hab : a ≠ b)
    (ha : a ∈ s) (hb : b ∈ s) (hξ : ξ ∈ s) : ξ = a ∨ ξ = b := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hξ
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hξ with rfl | rfl <;>
    simp_all

theorem rank_add_finrank_dispFunV_le [Finite Ξ] [Finite V] (hΞ : Nat.card Ξ = 8)
    (hfaith : ∀ v : V, (∀ ξ : Ξ, v +ᵥ ξ = ξ) → v = 0)
    (hswap : ∀ (v : V) (a b : Ξ), a ≠ b → v +ᵥ a = b → v +ᵥ b = a →
      (∀ ξ, ξ ≠ a → ξ ≠ b → v +ᵥ ξ = ξ) → False)
    (hV : ∃ v : V, v ≠ 0) :
    finrank (ZMod 2) V + finrank (ZMod 2) (dispFunV V Ξ) ≤ 7 := by
  classical
  obtain ⟨ξ₀⟩ : Nonempty Ξ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Ξ)).1
  let Ω := AddAction.orbitRel.Quotient V Ξ
  let _ : Fintype Ω := Fintype.ofFinite Ω
  have hrep : ∀ ξ : Ξ, ∃ w : V, w +ᵥ (Quotient.mk'' ξ : Ω).out = ξ := by
    intro ξ
    have h := Quotient.mk_out' (s₁ := AddAction.orbitRel V Ξ) ξ
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨-w, by rw [← hw, neg_vadd_vadd]⟩
  have hstab_rep : ∀ ξ : Ξ, stabSub (V := V) ξ = stabSub (Quotient.mk'' ξ : Ω).out := by
    intro ξ
    obtain ⟨w, hw⟩ := hrep ξ
    calc stabSub (V := V) ξ = stabSub (w +ᵥ (Quotient.mk'' ξ : Ω).out) := by rw [hw]
      _ = stabSub (Quotient.mk'' ξ : Ω).out := stabSub_vadd w _
  set r := finrank (ZMod 2) V with hr
  have hcardV : Nat.card V = 2 ^ r := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  let S : Ω → Submodule (ZMod 2) V := fun ω => stabSub ω.out
  let L : Submodule (ZMod 2) V := ⨆ ω, S ω
  set ℓ := finrank (ZMod 2) L with hℓ
  have hSL : ∀ ω, S ω ≤ L := fun ω => le_iSup S ω
  have hσℓ : ∀ ω, finrank (ZMod 2) (S ω) ≤ ℓ := fun ω => Submodule.finrank_mono (hSL ω)
  have hℓr : ℓ ≤ r := Submodule.finrank_le L
  have hstabcard : ∀ ξ : Ξ, Nat.card (AddAction.stabilizer V ξ) =
      2 ^ finrank (ZMod 2) (stabSub (V := V) ξ) := by
    intro ξ
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := stabSub (V := V) ξ)
    rw [Nat.card_zmod] at h
    exact h
  have horb : ∀ ξ : Ξ, (AddAction.orbit V ξ).ncard * 2 ^ finrank (ZMod 2) (stabSub (V := V) ξ) =
      2 ^ r := by
    intro ξ
    rw [← hstabcard, ← hcardV, ← AddAction.index_stabilizer, mul_comm,
      AddSubgroup.card_mul_index]
  have horb' : ∀ ω : Ω, (AddAction.orbit V ω.out).ncard =
      2 ^ ((r - ℓ) + (ℓ - finrank (ZMod 2) (S ω))) := by
    intro ω
    have h := horb ω.out
    have e : r = (r - ℓ) + (ℓ - finrank (ZMod 2) (S ω)) + finrank (ZMod 2) (S ω) := by
      have := hσℓ ω
      omega
    rw [e, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have hsum8 : ∑ ω : Ω, (AddAction.orbit V ω.out).ncard = 8 := by
    rw [← hΞ, Nat.card_congr (AddAction.selfEquivSigmaOrbits V Ξ), Nat.card_sigma]
    simp only [Nat.card_coe_set_eq]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ fun _ => rfl
  have hfaithS : ∀ v : V, (∀ ω : Ω, v ∈ S ω) → v = 0 := by
    intro v hv
    apply hfaith
    intro ξ
    have h : v ∈ stabSub (Quotient.mk'' ξ : Ω).out := hv (Quotient.mk'' ξ)
    rw [← hstab_rep ξ] at h
    exact mem_stabSub.mp h
  have hdual : ∀ (f : Ξ → ZMod 2) (hf : f ∈ dispFunV V Ξ),
      dispHom ξ₀ hf ∈ L.dualAnnihilator := by
    intro f hf
    rw [Submodule.mem_dualAnnihilator]
    have hle : L ≤ LinearMap.ker (dispHom ξ₀ hf) := iSup_le fun ω v hv => by
      rw [LinearMap.mem_ker]
      have h := dispHom_spec ξ₀ hf v ω.out
      rw [mem_stabSub.mp hv] at h
      simpa using h
    exact fun w hw => hle hw
  have : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  let Φ : dispFunV V Ξ → (Ω → ZMod 2) × L.dualAnnihilator := fun f =>
    (fun ω => (f : Ξ → ZMod 2) ω.out, ⟨dispHom ξ₀ f.2, hdual f f.2⟩)
  have hΦ : Function.Injective Φ := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : dispHom ξ₀ hf = dispHom ξ₀ hg := congrArg Subtype.val h2
    apply Subtype.ext
    funext ξ
    obtain ⟨w, hw⟩ := hrep ξ
    show f ξ = g ξ
    rw [← hw, dispHom_spec ξ₀ hf, dispHom_spec ξ₀ hg, congrFun h1 _, h2']
  have hD : Nat.card L.dualAnnihilator = 2 ^ (r - ℓ) := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
    change ℓ + finrank (ZMod 2) L.dualAnnihilator = r at h1
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := L.dualAnnihilator)
    rw [Nat.card_zmod] at h2
    change Nat.card L.dualAnnihilator = 2 ^ finrank (ZMod 2) L.dualAnnihilator at h2
    rw [h2]
    congr 1
    omega
  have hFle : finrank (ZMod 2) (dispFunV V Ξ) ≤ Fintype.card Ω + (r - ℓ) := by
    have h := Nat.card_le_card_of_injective Φ hΦ
    rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Ω), hD,
      ← pow_add] at h
    have h' := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := dispFunV V Ξ)
    rw [Nat.card_zmod] at h'
    change Nat.card (dispFunV V Ξ) = 2 ^ finrank (ZMod 2) (dispFunV V Ξ) at h'
    rw [h'] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  let S' : Ω → Submodule (ZMod 2) L := fun ω => (S ω).comap L.subtype
  let ψ : L →ₗ[ZMod 2] ((ω : Ω) → L ⧸ S' ω) := LinearMap.pi fun ω => (S' ω).mkQ
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_pi, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_iInf] at hx
    rw [Submodule.mem_bot]
    refine Subtype.ext (hfaithS x fun ω => ?_)
    have h := hx ω
    rwa [Submodule.ker_mkQ, Submodule.mem_comap] at h
  have hquot : ∀ ω, finrank (ZMod 2) (L ⧸ S' ω) = ℓ - finrank (ZMod 2) (S ω) := by
    intro ω
    have h := Submodule.finrank_quotient_add_finrank (S' ω)
    have h' := (Submodule.comapSubtypeEquivOfLe (hSL ω)).finrank_eq
    change finrank (ZMod 2) (L ⧸ S' ω) + finrank (ZMod 2) (S' ω) = ℓ at h
    change finrank (ZMod 2) (S' ω) = finrank (ZMod 2) (S ω) at h'
    omega
  have hpi : finrank (ZMod 2) ((ω : Ω) → L ⧸ S' ω) = ∑ ω, (ℓ - finrank (ZMod 2) (S ω)) := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun ω _ => hquot ω
  have hℓμ : ℓ ≤ ∑ ω, (ℓ - finrank (ZMod 2) (S ω)) := by
    rw [← hpi]
    exact LinearMap.finrank_le_finrank_of_injective hψ
  set d := r - ℓ with hd
  set μ : Ω → ℕ := fun ω => ℓ - finrank (ZMod 2) (S ω) with hμ
  have hℓμ' : ℓ ≤ ∑ ω, μ ω := hℓμ
  have hsum : ∑ ω : Ω, 2 ^ (d + μ ω) = 8 := by
    rw [← hsum8]
    exact Finset.sum_congr rfl fun ω _ => (horb' ω).symm
  have hk : ∑ ω : Ω, (1 + μ ω) = Fintype.card Ω + ∑ ω, μ ω := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rcases arith_bound Finset.univ d μ hsum with h | ⟨hd0, hμ1⟩
  · omega
  have hk8 : Fintype.card Ω + ∑ ω, μ ω = 8 := by
    have h2 : ∀ ω ∈ (Finset.univ : Finset Ω), 2 ^ (d + μ ω) = 1 + μ ω := by
      intro ω hω
      have h1 := hμ1 ω hω
      rw [hd0, zero_add]
      interval_cases μ ω <;> rfl
    rw [Finset.sum_congr rfl h2, hk] at hsum
    exact hsum
  have hr1 : 0 < r := Module.finrank_pos_iff_exists_ne_zero.mpr hV
  have hlt : ℓ < ∑ ω, μ ω := by
    by_contra hge
    have heq : ℓ = ∑ ω, μ ω := le_antisymm hℓμ' (not_lt.mp hge)
    have hsurj : Function.Surjective ψ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [hpi]; exact heq)).mp hψ
    obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, μ ω₀ = 1 := by
      by_contra hno
      simp only [not_exists] at hno
      have h0 : ∑ ω, μ ω = 0 := Finset.sum_eq_zero fun ω hω => by
        have := hμ1 ω hω
        have := hno ω
        omega
      omega
    have hpos : 0 < finrank (ZMod 2) (L ⧸ S' ω₀) := by
      rw [hquot]
      show 0 < μ ω₀
      omega
    obtain ⟨y₀, hy₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨x, hx⟩ := hsurj (Pi.single ω₀ y₀)
    have hxω : ∀ ω, ω ≠ ω₀ → (x : V) ∈ S ω := by
      intro ω hω
      have h := congrFun hx ω
      rw [LinearMap.pi_apply, Pi.single_eq_of_ne hω, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at h
      exact h
    have hxω₀ : (x : V) ∉ S ω₀ := by
      intro hmem
      have h := congrFun hx ω₀
      rw [LinearMap.pi_apply, Pi.single_eq_same, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ S' ω₀ from hmem)] at h
      exact hy₀ h.symm
    have hab : ω₀.out ≠ (x : V) +ᵥ ω₀.out := fun h => hxω₀ (mem_stabSub.mpr h.symm)
    have hxb : (x : V) +ᵥ ((x : V) +ᵥ ω₀.out) = ω₀.out := by
      rw [← add_vadd, f2_add_self, zero_vadd]
    have horb2 : (AddAction.orbit V ω₀.out).ncard = 2 := by
      rw [horb' ω₀]
      show 2 ^ (d + μ ω₀) = 2
      rw [hd0, hω₀]
      rfl
    refine hswap x ω₀.out _ hab rfl hxb fun ξ hξa hξb => ?_
    by_cases hξ : (Quotient.mk'' ξ : Ω) = ω₀
    · exfalso
      obtain ⟨w, hw⟩ := hrep ξ
      have hξorb : ξ ∈ AddAction.orbit V ω₀.out := by
        rw [← hξ]
        exact AddAction.mem_orbit_iff.mpr ⟨w, hw⟩
      rcases eq_or_eq_of_ncard_eq_two horb2 hab (AddAction.mem_orbit_self _)
        (AddAction.mem_orbit _ _) hξorb with h | h
      exacts [hξa h, hξb h]
    · have h : (x : V) ∈ stabSub (Quotient.mk'' ξ : Ω).out := hxω _ hξ
      rw [← hstab_rep ξ] at h
      exact mem_stabSub.mp h
  omega

end Core

end EightPointQuotient

open EightPointQuotient in
theorem eight_point_even_permutation_quotient_elementary_rank_bound {Ξ : Type*} [Fintype Ξ]
    [DecidableEq Ξ] (hΞ : Fintype.card Ξ = 8) (U : Subgroup (Equiv.Perm Ξ)) (hU : U ≠ ⊥)
    (hcomm : ∀ u ∈ U, ∀ w ∈ U, u * w = w * u) (hsq : ∀ u ∈ U, u * u = 1)
    (heven : ∀ u ∈ U, Equiv.Perm.sign u = 1) (r : ℕ) (hr : Nat.card U = 2 ^ r) :
    r + finrank (ZMod 2) (constQuotFixed U) ≤ 6 := by
  let _ : CommGroup U := { (inferInstance : Group U) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let _ : Module (ZMod 2) (Additive U) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, pow_two]
    exact Subtype.ext (hsq _ (Additive.toMul x).2)
  have hvadd : ∀ (v : Additive U) (ξ : Ξ),
      v +ᵥ ξ = ((Additive.toMul v : U) : Equiv.Perm Ξ) ξ := fun _ _ => rfl
  have hfaith : ∀ v : Additive U, (∀ ξ : Ξ, v +ᵥ ξ = ξ) → v = 0 := by
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    ext ξ
    rw [← hvadd, hv ξ]
    rfl
  have hswap : ∀ (v : Additive U) (a b : Ξ), a ≠ b → v +ᵥ a = b → v +ᵥ b = a →
      (∀ ξ, ξ ≠ a → ξ ≠ b → v +ᵥ ξ = ξ) → False := by
    intro v a b hab h1 h2 h3
    have hperm : ((Additive.toMul v : U) : Equiv.Perm Ξ) = Equiv.swap a b := by
      ext ξ
      by_cases hξa : ξ = a
      · rw [hξa, ← hvadd, h1, Equiv.swap_apply_left]
      by_cases hξb : ξ = b
      · rw [hξb, ← hvadd, h2, Equiv.swap_apply_right]
      rw [← hvadd, h3 ξ hξa hξb, Equiv.swap_apply_of_ne_of_ne hξa hξb]
    have h := heven _ (Additive.toMul v).2
    rw [hperm, Equiv.Perm.sign_swap hab] at h
    exact absurd h (by decide)
  have hV : ∃ v : Additive U, v ≠ 0 := by
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    exact ⟨Additive.ofMul u, fun h => hu (Additive.ofMul.injective h)⟩
  have hfinrank : finrank (ZMod 2) (Additive U) = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    rw [Nat.card_zmod] at h
    have h2 : Nat.card (Additive U) = Nat.card U := rfl
    rw [h2, hr] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hdisp : dispFunV (Additive U) Ξ = dispFun U := by
    ext f
    constructor
    · intro hf u hu
      exact hf (Additive.ofMul ⟨u, hu⟩)
    · intro hf v
      exact hf _ (Additive.toMul v).2
  have hcore := rank_add_finrank_dispFunV_le (V := Additive U) (Ξ := Ξ)
    (by rw [Nat.card_eq_fintype_card, hΞ]) hfaith hswap hV
  rw [hfinrank, hdisp] at hcore
  have : Nonempty Ξ := Fintype.card_pos_iff.mp (by omega)
  have hA := finrank_constQuotFixed_add_one_le (Ξ := Ξ) U
  omega

end CFSG.LocalAnalysis.ComponentInitial
