module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreCls

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFRRank

open CFSG.Open Module
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem pow_three_eq_one_of_apply {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W ≃ₗ[ZMod 2] W) (h : ∀ x, f (f (f x)) = x) : f ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact h x

private theorem cube_apply' {a : V ≃ₗ[ZMod 2] V} (h : a ^ 3 = 1) (x : V) : a (a (a x)) = x := by
  have h3 : (a ^ 3) x = x := by rw [h]; rfl
  simpa [pow_succ, LinearEquiv.mul_apply] using h3

theorem map_eq_of_inv {a : V ≃ₗ[ZMod 2] V} (h3 : a ^ 3 = 1) {W : Submodule (ZMod 2) V}
    (hW : ∀ x ∈ W, a x ∈ W) : W.map (a : V →ₗ[ZMod 2] V) = W := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hW x hx
  · intro x hx
    exact Submodule.mem_map.2 ⟨a (a x), hW _ (hW x hx), cube_apply' h3 x⟩

theorem ofSubmodules_pow_three {a : V ≃ₗ[ZMod 2] V} (h3 : a ^ 3 = 1) {W : Submodule (ZMod 2) V}
    (hW : W.map (a : V →ₗ[ZMod 2] V) = W) : (a.ofSubmodules W W hW) ^ 3 = 1 :=
  pow_three_eq_one_of_apply _ fun x => Subtype.ext (by
    simp only [LinearEquiv.ofSubmodules_apply]
    exact cube_apply' h3 x)

theorem inv2_zpowers [Finite V] {a : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V}
    (hW : ∀ x ∈ W, a x ∈ W) : Inv2 (Subgroup.zpowers a) W := by
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) fun f g h => LinearEquiv.ext
      (congrFun h)
  have hpow : ∀ k : ℕ, ∀ x ∈ W, (a ^ k) x ∈ W := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih (a x) (hW x hx)
  intro g hg x hx
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hg)
  rw [← hk]
  exact hpow k x hx

noncomputable def glue {P P' : Submodule (ZMod 2) V} (h : IsCompl P P') :
    (P ≃ₗ[ZMod 2] P) × (P' ≃ₗ[ZMod 2] P') →* (V ≃ₗ[ZMod 2] V) where
  toFun f := ((Submodule.prodEquivOfIsCompl P P' h).symm.trans
    (LinearEquiv.prodCongr f.1 f.2)).trans (Submodule.prodEquivOfIsCompl P P' h)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change (Submodule.prodEquivOfIsCompl P P' h) (LinearEquiv.prodCongr 1 1
      ((Submodule.prodEquivOfIsCompl P P' h).symm x)) = x
    have h1 : ∀ y : P × P', LinearEquiv.prodCongr (1 : P ≃ₗ[ZMod 2] P) (1 : P' ≃ₗ[ZMod 2] P') y = y :=
      fun y => rfl
    rw [h1, LinearEquiv.apply_symm_apply]
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    simp

theorem glue_apply_left {P P' : Submodule (ZMod 2) V} (h : IsCompl P P')
    (f : (P ≃ₗ[ZMod 2] P) × (P' ≃ₗ[ZMod 2] P')) (p : P) : glue h f (p : V) = f.1 p := by
  change (Submodule.prodEquivOfIsCompl P P' h) (LinearEquiv.prodCongr f.1 f.2
    ((Submodule.prodEquivOfIsCompl P P' h).symm p)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp

theorem glue_apply_right {P P' : Submodule (ZMod 2) V} (h : IsCompl P P')
    (f : (P ≃ₗ[ZMod 2] P) × (P' ≃ₗ[ZMod 2] P')) (p : P') : glue h f (p : V) = f.2 p := by
  change (Submodule.prodEquivOfIsCompl P P' h) (LinearEquiv.prodCongr f.1 f.2
    ((Submodule.prodEquivOfIsCompl P P' h).symm p)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  simp

theorem glue_injective {P P' : Submodule (ZMod 2) V} (h : IsCompl P P') :
    Function.Injective (glue h) := by
  refine (injective_iff_map_eq_one (glue h)).2 fun f hf => ?_
  refine Prod.ext (LinearEquiv.ext fun p => Subtype.ext ?_) (LinearEquiv.ext fun p => Subtype.ext ?_)
  · rw [← glue_apply_left h f p, hf]
    rfl
  · rw [← glue_apply_right h f p, hf]
    rfl

theorem glue_ofSubmodules (a : V ≃ₗ[ZMod 2] V) {P P' : Submodule (ZMod 2) V} (h : IsCompl P P')
    (hP : P.map (a : V →ₗ[ZMod 2] V) = P) (hP' : P'.map (a : V →ₗ[ZMod 2] V) = P') :
    glue h (a.ofSubmodules P P hP, a.ofSubmodules P' P' hP') = a := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨⟨p, p'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl P P' h).surjective x
  rw [Submodule.coe_prodEquivOfIsCompl', map_add, map_add, glue_apply_left, glue_apply_right]
  simp only [LinearEquiv.ofSubmodules_apply]

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem exists_plane [FiniteDimensional (ZMod 2) V] {a : V ≃ₗ[ZMod 2] V} (h3 : a ^ 3 = 1)
    (hn : 2 ≤ finrank (ZMod 2) V) :
    ∃ (P : Submodule (ZMod 2) V) (hP : ∀ x ∈ P, a x ∈ P), finrank (ZMod 2) P = 2 ∧
      ∃ H : Subgroup (P ≃ₗ[ZMod 2] P), IsElemAbelian 3 H ∧ Nat.card H = 3 ∧
        ∀ g ∈ H, g * a.ofSubmodules P P (map_eq_of_inv h3 hP) =
          a.ofSubmodules P P (map_eq_of_inv h3 hP) * g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2V : ∀ v : V, v + v = 0 := add_self_eq_zero'
  by_cases hfix : ∀ x : V, a x = x
  ·
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨y, hy⟩ := exists_ne (0 : V)
    have hlt : Submodule.span (ZMod 2) {y} < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => ?_
      have h1 := finrank_span_singleton (K := ZMod 2) hy
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨z, -, hz⟩ := SetLike.exists_of_lt hlt
    have hli : LinearIndependent (ZMod 2) ![y, z] := by
      rw [LinearIndependent.pair_iff' hy]
      intro c hc
      exact hz (hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self y))
    set P := Submodule.span (ZMod 2) (Set.range ![y, z]) with hPdef
    have hP2 : finrank (ZMod 2) P = 2 := by
      rw [hPdef, finrank_span_eq_card hli, Fintype.card_fin]
    have hPinv : ∀ x ∈ P, a x ∈ P := fun x hx => by rw [hfix x]; exact hx
    refine ⟨P, hPinv, hP2, ?_⟩
    obtain ⟨E0, hE0, hE0c⟩ := Std.exists_elemAb_card P 2 hP2
    have hres : a.ofSubmodules P P (map_eq_of_inv h3 hPinv) = 1 :=
      LinearEquiv.ext fun x => Subtype.ext (by
        rw [LinearEquiv.ofSubmodules_apply, hfix]
        rfl)
    refine ⟨E0, hE0, by rw [hE0c]; norm_num, fun g _ => ?_⟩
    rw [hres, mul_one, one_mul]
  ·
    push Not at hfix
    obtain ⟨x, hx⟩ := hfix
    set y := a x + x with hydef
    have hy : y ≠ 0 := fun h => hx (by
      have h1 : a x = -x := eq_neg_of_add_eq_zero_left h
      rw [h1, neg_eq_iff_add_eq_zero]
      exact h2V x)
    have haay : a (a y) = a y + y := by
      have h1 := cube_apply' h3 x
      simp only [hydef, map_add]
      rw [h1]
      have h4 : a (a x) + a x + (a x + x) = a (a x) + x + (a x + a x) := by abel
      rw [h4, h2V, add_zero, add_comm]
    have hay : a y ≠ y := fun h => hy (by
      have h1 := haay
      rw [h, h, h2V] at h1
      exact h1)
    have hay0 : a y ≠ 0 := fun h => hy (by
      have h1 := congrArg a.symm h
      rwa [LinearEquiv.symm_apply_apply, map_zero] at h1)
    have hli : LinearIndependent (ZMod 2) ![y, a y] := by
      rw [LinearIndependent.pair_iff' hy]
      intro c hc
      rcases zmod2_cases c with rfl | rfl
      · rw [zero_smul] at hc
        exact hay0 hc.symm
      · rw [one_smul] at hc
        exact hay hc.symm
    set P := Submodule.span (ZMod 2) (Set.range ![y, a y]) with hPdef
    have hyP : y ∈ P := Submodule.subset_span ⟨0, rfl⟩
    have hayP : a y ∈ P := Submodule.subset_span ⟨1, rfl⟩
    have hP2 : finrank (ZMod 2) P = 2 := by
      rw [hPdef, finrank_span_eq_card hli, Fintype.card_fin]
    have hPinv : ∀ v ∈ P, a v ∈ P := by
      have hle : P ≤ P.comap (a : V →ₗ[ZMod 2] V) := by
        rw [hPdef, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hayP
        · change a (a y) ∈ P
          rw [haay]
          exact P.add_mem hayP hyP
      exact fun v hv => hle hv
    refine ⟨P, hPinv, hP2, ?_⟩
    set c := a.ofSubmodules P P (map_eq_of_inv h3 hPinv) with hcdef
    have hc3 : c ^ 3 = 1 := ofSubmodules_pow_three h3 _
    have hc1 : c ≠ 1 := fun h => hay (by
      have h1 := congrArg (fun f : P ≃ₗ[ZMod 2] P => ((f ⟨y, hyP⟩ : P) : V)) h
      simpa [hcdef] using h1)
    refine ⟨Subgroup.zpowers c, isElemAbelian_of_forall _ ?_ ?_, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.zpow_zpow_self c i j).eq
    · rintro _ ⟨i, rfl⟩
      change (c ^ i) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
    · rintro _ ⟨i, rfl⟩
      exact (Commute.self_zpow c i).eq.symm

theorem exists_elemAb_commute (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      finrank (ZMod 2) V = n → ∀ a : V ≃ₗ[ZMod 2] V, a ^ 3 = 1 →
        ∃ m : ℕ, n ≤ 2 * m + 1 ∧ ∃ T : Subgroup (V ≃ₗ[ZMod 2] V), IsElemAbelian 3 T ∧
          Nat.card T = 3 ^ m ∧ ∀ t ∈ T, t * a = a * t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn a h3
  by_cases h2 : n < 2
  · refine ⟨0, by omega, ⊥, isElemAbelian_of_forall _ ?_ ?_, by simp, ?_⟩
    · intro x hx y hy
      rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]
    · intro x hx
      rw [Subgroup.mem_bot.1 hx, one_pow]
    · intro t ht
      rw [Subgroup.mem_bot.1 ht, one_mul, mul_one]
  push Not at h2
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨P, hPinv, hP2, H, hH, hHc, hHa⟩ := exists_plane h3 (hn ▸ h2)
  haveI : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  have hodd : Odd (Fintype.card (Subgroup.zpowers a)) := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  obtain ⟨P', hP'inv, hc⟩ := exists_inv_compl (Subgroup.zpowers a) hodd P (inv2_zpowers hPinv)
  have hP'a : ∀ x ∈ P', a x ∈ P' := hP'inv a (Subgroup.mem_zpowers a)
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  have hP'n : finrank (ZMod 2) P' = n - 2 := by omega
  set aP := a.ofSubmodules P P (map_eq_of_inv h3 hPinv) with haP
  set aP' := a.ofSubmodules P' P' (map_eq_of_inv h3 hP'a) with haP'
  obtain ⟨m, hm, T', hT', hT'c, hT'a⟩ :=
    ih (n - 2) (by omega) P' hP'n aP' (ofSubmodules_pow_three h3 _)
  have hga : glue hc (aP, aP') = a := glue_ofSubmodules a hc _ _
  refine ⟨m + 1, by omega, (H.prod T').map (glue hc), ?_, ?_, ?_⟩
  · refine Std.isElemAbelian_map' _ (isElemAbelian_of_forall _ ?_ ?_)
    · intro x hx y hy
      rw [Subgroup.mem_prod] at hx hy
      exact Prod.ext (congrArg Subtype.val (hH.1.is_comm.comm ⟨_, hx.1⟩ ⟨_, hy.1⟩))
        (congrArg Subtype.val (hT'.1.is_comm.comm ⟨_, hx.2⟩ ⟨_, hy.2⟩))
    · intro x hx
      rw [Subgroup.mem_prod] at hx
      exact Prod.ext (by rw [Prod.pow_fst, hH.2 _ hx.1]; rfl)
        (by rw [Prod.pow_snd, hT'.2 _ hx.2]; rfl)
  · rw [Subgroup.card_map_of_injective (glue_injective hc),
      Nat.card_congr (Subgroup.prodEquiv H T').toEquiv, Nat.card_prod, hHc, hT'c, pow_succ,
      mul_comm]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ H.prod T' := hx
    rw [Subgroup.mem_prod] at hx'
    conv_lhs => rw [← hga]
    conv_rhs => rw [← hga]
    rw [← map_mul, ← map_mul]
    exact congrArg (glue hc) (Prod.ext (hHa _ hx'.1) (hT'a _ hx'.2))

theorem exists_elemAb81_commute [FiniteDimensional (ZMod 2) V] (hn : 8 ≤ finrank (ZMod 2) V)
    (a : V ≃ₗ[ZMod 2] V) (h3 : a ^ 3 = 1) :
    ∃ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ Subgroup.centralizer {a} ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) fun f g h => LinearEquiv.ext
      (congrFun h)
  obtain ⟨m, hm, T, hT, hTc, hTa⟩ := exists_elemAb_commute _ V rfl a h3
  obtain ⟨E0, hE0⟩ := Sylow.exists_subgroup_card_pow_prime (G := T) 3 (n := 4)
    (by rw [hTc]; exact pow_dvd_pow 3 (by omega))
  refine ⟨E0.map T.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hTa x.1 x.2
  · have hle := Subgroup.map_subtype_le E0
    exact isElemAbelian_of_forall _ (fun x hx y hy => congrArg Subtype.val
      (hT.1.is_comm.comm ⟨x, hle hx⟩ ⟨y, hle hy⟩)) fun x hx => hT.2 x (hle hx)
  · rw [Subgroup.card_map_of_injective T.subtype_injective, hE0]

end CFSG.LocalAnalysis.GLTheoremA.SFRRank

end
