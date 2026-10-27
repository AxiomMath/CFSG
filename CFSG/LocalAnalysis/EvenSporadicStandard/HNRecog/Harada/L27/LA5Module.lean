module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.LA5Cyclic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Module

theorem perfect_trivial_on_orbit_span {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : W →ₗ[ZMod 2] W) (G : Subgroup (W ≃ₗ[ZMod 2] W)) (hG : ⁅G, G⁆ = G)
    (hGσ : ∀ g ∈ G, ∀ x, g (σ x) = σ (g x)) (u : W)
    (hGu : ∀ g ∈ G, g u ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)) :
    ∀ g ∈ G, ∀ x ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u), g x = x := by
  let M : Submodule (ZMod 2) W := Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)
  have hσM : ∀ x ∈ M, σ x ∈ M := by
    have hle : M ≤ M.comap σ := by
      change Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u) ≤
        (Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)).comap σ
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      change σ ((σ ^ i) u) ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)
      exact Submodule.subset_span ⟨i + 1, by
        show (σ ^ (i + 1)) u = σ ((σ ^ i) u)
        rw [pow_succ', Module.End.mul_apply]⟩
    intro x hx
    exact hle hx
  have hσMpow : ∀ i : ℕ, ∀ y ∈ M, (σ ^ i) y ∈ M := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hσM _ (ih y hy)
  have hpres : ∀ a ∈ G, ∀ x ∈ M, a x ∈ M := by
    intro a ha
    have hcommσ : ∀ x : W, (a : W →ₗ[ZMod 2] W) (σ x) = σ ((a : W →ₗ[ZMod 2] W) x) :=
      fun x => hGσ a ha x
    have hcomm : ∀ i : ℕ, (a : W →ₗ[ZMod 2] W) ((σ ^ i) u) =
        (σ ^ i) ((a : W →ₗ[ZMod 2] W) u) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ']
        simp only [Module.End.mul_apply]
        rw [hcommσ ((σ ^ i) u), ih]
    have hle : M ≤ M.comap (a : W →ₗ[ZMod 2] W) := by
      change Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u) ≤
        (Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)).comap
          (a : W →ₗ[ZMod 2] W)
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      change (a : W →ₗ[ZMod 2] W) ((σ ^ i) u) ∈
        Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)
      rw [hcomm i]
      exact hσMpow i ((a : W →ₗ[ZMod 2] W) u) (hGu a ha)
    intro x hx
    exact hle hx
  let K : Subgroup (W ≃ₗ[ZMod 2] W) :=
    { carrier := {a | ∀ x ∈ M, a x = x}
      one_mem' := by intro x hx; rfl
      mul_mem' := by
        intro a b ha hb x hx
        rw [LinearEquiv.mul_apply, hb x hx, ha x hx]
      inv_mem' := by
        intro a ha x hx
        exact a.injective (by simp [ha x hx]) }
  have hGK : G ≤ K := by
    rw [← hG, Subgroup.commutator_le]
    intro g hg h hh x hx
    have hint : (h⁻¹ : W ≃ₗ[ZMod 2] W) x ∈ M := hpres h⁻¹ (G.inv_mem hh) x hx
    have h1 : (h : W ≃ₗ[ZMod 2] W) ((g⁻¹ : W ≃ₗ[ZMod 2] W) ((h⁻¹ : W ≃ₗ[ZMod 2] W) x)) =
        (g⁻¹ : W ≃ₗ[ZMod 2] W) ((h : W ≃ₗ[ZMod 2] W) ((h⁻¹ : W ≃ₗ[ZMod 2] W) x)) :=
      commute_on_orbit_span σ (h : W →ₗ[ZMod 2] W)
        (((g⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W))
        (hGσ h hh) (fun y => hGσ g⁻¹ (G.inv_mem hg) y) u
        (hGu h hh) (hGu g⁻¹ (G.inv_mem hg)) hint
    rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, h1]
    simp
  intro g hg x hx
  exact hGK hg x hx

theorem no_order_five_commuting_a5_pair {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hdim : Module.finrank (ZMod 2) W = 8) (r : W ≃ₗ[ZMod 2] W) (hr5 : r ^ 5 = 1) (hr1 : r ≠ 1)
    (F P' : Subgroup (W ≃ₗ[ZMod 2] W)) (eF : F ≃* alternatingGroup (Fin 5))
    (eP : P' ≃* alternatingGroup (Fin 5))
    (hFr : ∀ f ∈ F, f * r = r * f) (hPr : ∀ p ∈ P', p * r = r * p)
    (hFfpf : ∀ f ∈ F, orderOf f = 5 → ∀ x : W, f x = x → x = 0)
    (w : W) (hw : w ≠ 0) (hPw : ∀ p ∈ P', p w = w) : False := by
  let σ : Module.End (ZMod 2) W := (r : W →ₗ[ZMod 2] W)
  have hσ5 : σ ^ 5 = 1 := by
    change (r : W →ₗ[ZMod 2] W) ^ 5 = 1
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 2) (M := W)) r 5
    rw [hr5, map_one] at h
    simpa using h.symm
  have h51 : ((5 : ℕ) : ZMod 2) = 1 := by decide
  let e : Module.End (ZMod 2) W := ∑ i ∈ Finset.range 5, σ ^ i
  have h5e : (5 : ℕ) • e = e := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 5 e, h51, one_smul]
  have he_mul_neg : e * (1 - σ) = 0 := by
    have h := geom_sum_mul_neg σ 5
    rw [hσ5, sub_self] at h
    simpa [e] using h
  have heσ : e * σ = e := by
    have h := he_mul_neg
    rw [mul_sub, mul_one] at h
    exact (sub_eq_zero.mp h).symm
  have hσe : σ * e = e := by
    have hmul : (1 - σ) * e = 0 := by
      have h := mul_neg_geom_sum σ 5
      rw [hσ5, sub_self] at h
      simpa [e] using h
    have h := hmul
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hee : e * e = e := by
    have hterm : ∀ i : ℕ, e * σ ^ i = e := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, ← mul_assoc, ih, heσ]
    calc e * e = e * (∑ i ∈ Finset.range 5, σ ^ i) := rfl
      _ = ∑ i ∈ Finset.range 5, e * σ ^ i := by rw [Finset.mul_sum]
      _ = ∑ _i ∈ Finset.range 5, e := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = 5 • e := by simp
      _ = e := h5e
  have he_fix : ∀ x : W, σ x = x → e x = x := by
    intro x hx
    have hpow : ∀ i : ℕ, (σ ^ i) x = x := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, Module.End.mul_apply, hx, ih]
    change (∑ i ∈ Finset.range 5, σ ^ i) x = x
    rw [LinearMap.sum_apply]
    simp only [hpow]
    rw [Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 5 x, h51, one_smul]
  haveI hfin : FiniteDimensional (ZMod 2) W :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  let C : Submodule (ZMod 2) W := LinearMap.ker (σ - 1)
  let U : Submodule (ZMod 2) W := LinearMap.ker e
  have hCiff : ∀ x : W, x ∈ C ↔ σ x = x := by
    intro x
    change (σ - 1) x = 0 ↔ σ x = x
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hCinfU : C ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxC, hxU⟩ := hx
    have hxfix : σ x = x := (hCiff x).mp hxC
    change e x = 0 at hxU
    rw [he_fix x hxfix] at hxU
    exact hxU
  have hrange : LinearMap.range e = C := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [hCiff]
      change (σ * e) x = e x
      rw [hσe]
    · intro x hx
      rw [hCiff] at hx
      exact ⟨x, he_fix x hx⟩
  have hCUdim : Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) U = 8 := by
    have h := LinearMap.finrank_range_add_finrank_ker (e : W →ₗ[ZMod 2] W)
    rw [hdim, hrange] at h
    exact h
  have hUstab : ∀ x ∈ U, σ x ∈ U := by
    intro x hx
    change e (σ x) = 0
    change (e * σ) x = 0
    rw [heσ]
    change e x = 0 at hx
    exact hx
  have hUr : ∀ x ∈ U, (r : W →ₗ[ZMod 2] W) x ∈ U := by
    intro x hx
    change e ((r : W →ₗ[ZMod 2] W) x) = 0
    change (e * σ) x = 0
    rw [heσ]
    change e x = 0 at hx
    exact hx
  have hUmap : U.map (r : W →ₗ[ZMod 2] W) = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      intro x hx
      exact hUr x hx
    · rw [LinearEquiv.finrank_map_eq]
  let rU : ↥U ≃ₗ[ZMod 2] ↥U := (r : W ≃ₗ[ZMod 2] W).ofSubmodules U U hUmap
  have hrU_apply : ∀ y : ↥U, ((rU y : ↥U) : W) = r (y : W) := fun y => rfl
  let σU : ↥U →ₗ[ZMod 2] ↥U := (rU : ↥U →ₗ[ZMod 2] ↥U)
  have hrU5 : rU ^ 5 = 1 := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [LinearEquiv.coe_pow]
    have hiter : ∀ n : ℕ, ((rU ^[n] x : ↥U) : W) = r^[n] (x : W) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply' rU n x, Function.iterate_succ_apply' r n (x : W)]
        rw [hrU_apply, ih]
    rw [hiter 5, ← LinearEquiv.coe_pow r 5, hr5]
    simp
  have hσU5 : σU ^ 5 = 1 := by
    change (rU : ↥U →ₗ[ZMod 2] ↥U) ^ 5 = 1
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 2) (M := ↥U)) rU 5
    rw [hrU5, map_one] at h
    simpa using h.symm
  have hσU_coe : ∀ y : ↥U, ((σU y : ↥U) : W) = σ (y : W) := fun y => rfl
  have hfixU : ∀ y : ↥U, σU y = y → y = 0 := by
    intro y hy
    have hyW : σ (y : W) = (y : W) := by
      have h1 : ((σU y : ↥U) : W) = (y : W) := congrArg (fun z : ↥U => (z : W)) hy
      rwa [hσU_coe y] at h1
    have hmemC : (y : W) ∈ C := (hCiff _).mpr hyW
    have hmemU : (y : W) ∈ U := y.2
    have hmem : (y : W) ∈ C ⊓ U := Submodule.mem_inf.mpr ⟨hmemC, hmemU⟩
    rw [hCinfU] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hUdvd : 4 ∣ Module.finrank (ZMod 2) U :=
    four_dvd_finrank_of_fpf σU hσU5 hfixU
  have hUne : U ≠ ⊥ := by
    intro hUbot
    have hfinU : Module.finrank (ZMod 2) U = 0 := by rw [hUbot, finrank_bot]
    have hCtop : C = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hdim, ← hCUdim, hfinU, add_zero]
    have hσ1 : σ = 1 := by
      ext x
      exact (hCiff x).mp (by rw [hCtop]; trivial)
    have hr_eq : r = 1 := by
      ext x
      have hx : σ x = (1 : W →ₗ[ZMod 2] W) x :=
        congrArg (fun f : W →ₗ[ZMod 2] W => f x) hσ1
      simpa [σ] using hx
    exact hr1 hr_eq
  have hUcases : Module.finrank (ZMod 2) U = 4 ∨ Module.finrank (ZMod 2) U = 8 := by
    obtain ⟨k, hk⟩ := hUdvd
    have hUle : Module.finrank (ZMod 2) U ≤ 8 := by
      rw [← hdim]
      exact Submodule.finrank_le U
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exfalso
        apply hUne
        rw [← Submodule.finrank_eq_zero]
        rw [hk0, mul_zero] at hk
        exact hk
      · exact hkpos
    have hk2 : k ≤ 2 := by omega
    have : k = 1 ∨ k = 2 := by omega
    rcases this with h | h <;> [left; right] <;> omega
  have hcommF : ∀ f ∈ F, ∀ x,
      (f : W →ₗ[ZMod 2] W) (σ x) = σ ((f : W →ₗ[ZMod 2] W) x) := by
    intro f hf x
    have h := congrArg (fun g : W ≃ₗ[ZMod 2] W => g x) (hFr f hf)
    change (f : W →ₗ[ZMod 2] W) ((r : W →ₗ[ZMod 2] W) x) =
      (r : W →ₗ[ZMod 2] W) ((f : W →ₗ[ZMod 2] W) x)
    simpa [LinearEquiv.mul_apply] using h
  have hcommP : ∀ p ∈ P', ∀ x,
      (p : W →ₗ[ZMod 2] W) (σ x) = σ ((p : W →ₗ[ZMod 2] W) x) := by
    intro p hp x
    have h := congrArg (fun g : W ≃ₗ[ZMod 2] W => g x) (hPr p hp)
    change (p : W →ₗ[ZMod 2] W) ((r : W →ₗ[ZMod 2] W) x) =
      (r : W →ₗ[ZMod 2] W) ((p : W →ₗ[ZMod 2] W) x)
    simpa [LinearEquiv.mul_apply] using h
  have comm_e : ∀ a : W →ₗ[ZMod 2] W, (∀ x, a (σ x) = σ (a x)) → a * e = e * a := by
    intro a ha
    have hc : Commute a σ := (commute_iff_eq a σ).mpr (LinearMap.ext ha)
    change a * (∑ i ∈ Finset.range 5, σ ^ i) =
      (∑ i ∈ Finset.range 5, σ ^ i) * a
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (commute_iff_eq _ _).mp (hc.pow_right i))
  have hFUstab : ∀ f ∈ F, ∀ x ∈ U, (f : W →ₗ[ZMod 2] W) x ∈ U := by
    intro f hf x hx
    have hfe : e * (f : W →ₗ[ZMod 2] W) = (f : W →ₗ[ZMod 2] W) * e :=
      (comm_e (f : W →ₗ[ZMod 2] W) (hcommF f hf)).symm
    change e ((f : W →ₗ[ZMod 2] W) x) = 0
    change (e * (f : W →ₗ[ZMod 2] W)) x = 0
    rw [hfe, Module.End.mul_apply]
    change (f : W →ₗ[ZMod 2] W) (e x) = 0
    change e x = 0 at hx
    rw [hx, map_zero]
  rcases hUcases with hU4 | hU8
  · obtain ⟨u, huU, hu0⟩ := (Submodule.ne_bot_iff U).mp hUne
    let M : Submodule (ZMod 2) W := Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)
    have hpowU : ∀ i : ℕ, (σ ^ i) u ∈ U := by
      intro i
      induction i with
      | zero => simpa using huU
      | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hUstab _ ih
    have hMU : M ≤ U := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact hpowU i
    have hMfix : ∀ x ∈ M, σ x = x → x = 0 := by
      intro x hxM hx
      have hxC : x ∈ C := (hCiff x).mpr hx
      have hxU : x ∈ U := hMU hxM
      have hmem : x ∈ C ⊓ U := Submodule.mem_inf.mpr ⟨hxC, hxU⟩
      rw [hCinfU] at hmem
      simpa using hmem
    have hM4 : Module.finrank (ZMod 2) M = 4 :=
      finrank_span_orbit_eq_four σ hσ5 hu0 hMfix
    have hMUeq : M = U := by
      refine Submodule.eq_of_le_of_finrank_eq hMU ?_
      rw [hM4, hU4]
    have hFU : ∀ f ∈ F, (f : W ≃ₗ[ZMod 2] W) u ∈ M := by
      intro f hf
      rw [hMUeq]
      exact hFUstab f hf u huU
    have hFfix : ∀ f ∈ F, ∀ x ∈ M, (f : W ≃ₗ[ZMod 2] W) x = x :=
      perfect_trivial_on_orbit_span σ F (commutator_eq_self_of_equiv_a5 F eF) hcommF u hFU
    obtain ⟨y, hy5⟩ := exists_orderOf_eq_five_a5
    let f5 : F := eF.symm y
    have hf5ord : orderOf (f5 : W ≃ₗ[ZMod 2] W) = 5 := by
      rw [Subgroup.orderOf_coe]
      have h1 := MulEquiv.orderOf_eq eF f5
      rw [show eF f5 = y from eF.apply_symm_apply y, hy5] at h1
      exact h1.symm
    have huM : u ∈ M := by rw [hMUeq]; exact huU
    have hf5u : (f5 : W ≃ₗ[ZMod 2] W) u = u := hFfix f5 f5.2 u huM
    exact hu0 (hFfpf (f5 : W ≃ₗ[ZMod 2] W) f5.2 hf5ord u hf5u)
  · have hCbot : C = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      omega
    have hfixW : ∀ x : W, σ x = x → x = 0 := by
      intro x hx
      have hxC : x ∈ C := (hCiff x).mpr hx
      rw [hCbot] at hxC
      simpa using hxC
    let ℓ : Submodule (ZMod 2) W := Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) w)
    have hℓσ : ∀ x ∈ ℓ, σ x ∈ ℓ := by
      have hle : ℓ ≤ ℓ.comap σ := by
        change Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) w) ≤
          (Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) w)).comap σ
        rw [Submodule.span_le]
        rintro y ⟨i, rfl⟩
        change σ ((σ ^ i) w) ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) w)
        exact Submodule.subset_span ⟨i + 1, by
          show (σ ^ (i + 1)) w = σ ((σ ^ i) w)
          rw [pow_succ', Module.End.mul_apply]⟩
      intro x hx
      exact hle hx
    have hℓ4 : Module.finrank (ZMod 2) ℓ = 4 :=
      finrank_span_orbit_eq_four σ hσ5 hw (fun x _ hx => hfixW x hx)
    have hPpow : ∀ p ∈ P', ∀ i : ℕ,
        (p : W →ₗ[ZMod 2] W) ((σ ^ i) w) = (σ ^ i) ((p : W →ₗ[ZMod 2] W) w) := by
      intro p hp i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ']
        simp only [Module.End.mul_apply]
        rw [hcommP p hp ((σ ^ i) w), ih]
    have hPfixℓ : ∀ p ∈ P', ∀ x ∈ ℓ, (p : W ≃ₗ[ZMod 2] W) x = x := by
      intro p hp x hx
      suffices h : x ∈ LinearMap.ker ((p : W →ₗ[ZMod 2] W) - 1) by
        change ((p : W →ₗ[ZMod 2] W) - 1) x = 0 at h
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
        exact h
      have hker : ℓ ≤ LinearMap.ker ((p : W →ₗ[ZMod 2] W) - 1) := by
        change Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) w) ≤
          LinearMap.ker ((p : W →ₗ[ZMod 2] W) - 1)
        rw [Submodule.span_le]
        rintro y ⟨i, rfl⟩
        change ((p : W →ₗ[ZMod 2] W) - 1) ((σ ^ i) w) = 0
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hPpow p hp i]
        congr 1
        simpa using hPw p hp
      exact hker hx
    have hℓp : ∀ p ∈ P', ℓ ≤ ℓ.comap (p : W →ₗ[ZMod 2] W) := by
      intro p hp x hx
      change (p : W ≃ₗ[ZMod 2] W) x ∈ ℓ
      rw [hPfixℓ p hp x hx]
      exact hx
    let Q := W ⧸ ℓ
    let σbar : Q →ₗ[ZMod 2] Q := Submodule.mapQ ℓ ℓ σ (fun x hx => hℓσ x hx)
    have hQdim : Module.finrank (ZMod 2) Q = 4 := by
      change Module.finrank (ZMod 2) (W ⧸ ℓ) = 4
      have h := Submodule.finrank_quotient_add_finrank ℓ
      rw [hdim, hℓ4] at h
      omega
    have hTinj : Function.Injective (σ - 1 : W →ₗ[ZMod 2] W) := by
      rw [← LinearMap.ker_eq_bot]
      exact hCbot
    have hTℓ_stab : ∀ x ∈ ℓ, (σ - 1) x ∈ ℓ := by
      intro x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact Submodule.sub_mem ℓ (hℓσ x hx) hx
    let Tℓ : ↥ℓ →ₗ[ZMod 2] ↥ℓ :=
      ((σ - 1).comp ℓ.subtype).codRestrict ℓ (fun x => hTℓ_stab x.1 x.2)
    have hTℓ_coe : ∀ x : ↥ℓ, ((Tℓ x : ↥ℓ) : W) = (σ - 1) (x : W) := fun x => rfl
    have hTℓ_inj : Function.Injective Tℓ := by
      intro a b hab
      apply Subtype.ext
      apply hTinj
      have h := congrArg (fun z : ↥ℓ => (z : W)) hab
      rwa [hTℓ_coe a, hTℓ_coe b] at h
    have hTℓ_surj : Function.Surjective Tℓ := LinearMap.surjective_of_injective hTℓ_inj
    have hσbar_fpf : ∀ x : Q, σbar x = x → x = 0 := by
      intro x
      refine Submodule.Quotient.induction_on ℓ x ?_
      intro y hx
      have hrel : (σ - 1) y ∈ ℓ := by
        have h2 := (Submodule.Quotient.eq ℓ).mp
          (show Submodule.Quotient.mk (σ y) = Submodule.Quotient.mk y from hx)
        simpa [LinearMap.sub_apply, Module.End.one_apply] using h2
      obtain ⟨z, hz⟩ := hTℓ_surj ⟨(σ - 1) y, hrel⟩
      have hzy : (z : W) = y := by
        apply hTinj
        have h3 : ((Tℓ z : ↥ℓ) : W) = ((⟨(σ - 1) y, hrel⟩ : ↥ℓ) : W) :=
          congrArg (fun w : ↥ℓ => (w : W)) hz
        rwa [hTℓ_coe z] at h3
      rw [← hzy]
      exact (Submodule.Quotient.mk_eq_zero ℓ).mpr z.2
    have hσbar5 : σbar ^ 5 = 1 := by
      apply LinearMap.ext
      intro x
      refine Submodule.Quotient.induction_on ℓ x ?_
      intro y
      have hiter : ∀ n : ℕ, (σbar ^ n) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk ((σ ^ n) y) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, ih]
          rw [show σbar (Submodule.Quotient.mk ((σ ^ n) y)) =
            Submodule.Quotient.mk (σ ((σ ^ n) y)) from Submodule.mapQ_apply ℓ ℓ σ ((σ ^ n) y)]
          congr 1
          rw [pow_succ', Module.End.mul_apply]
      rw [hiter 5, hσ5, Module.End.one_apply, Module.End.one_apply]
    have hℓmap : ∀ p ∈ P', ℓ.map (p : W →ₗ[ZMod 2] W) = ℓ := by
      intro p hp
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap]
        intro x hx
        rw [Submodule.mem_comap]
        change (p : W ≃ₗ[ZMod 2] W) x ∈ ℓ
        rw [hPfixℓ p hp x hx]
        exact hx
      · intro x hx
        exact Submodule.mem_map.mpr ⟨x, hx, by
          change (p : W ≃ₗ[ZMod 2] W) x = x
          exact hPfixℓ p hp x hx⟩
    let φ : P' →* (Q ≃ₗ[ZMod 2] Q) :=
      { toFun := fun p => Submodule.Quotient.equiv ℓ ℓ (p : W ≃ₗ[ZMod 2] W) (hℓmap p.1 p.2)
        map_one' := by
          apply LinearEquiv.ext
          intro x
          refine Submodule.Quotient.induction_on ℓ x ?_
          intro y
          simp
        map_mul' := by
          intro p q
          apply LinearEquiv.ext
          intro x
          refine Submodule.Quotient.induction_on ℓ x ?_
          intro y
          simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
          change Submodule.Quotient.mk ((p * q : W ≃ₗ[ZMod 2] W) y) =
            Submodule.Quotient.mk ((p : W ≃ₗ[ZMod 2] W) ((q : W ≃ₗ[ZMod 2] W) y))
          rw [LinearEquiv.mul_apply] }
    let GQ : Subgroup (Q ≃ₗ[ZMod 2] Q) := φ.range
    have hGQ : ⁅GQ, GQ⁆ = GQ := by
      haveI hPperf : Group.IsPerfect P' :=
        Subgroup.isPerfect_iff.mpr (commutator_eq_self_of_equiv_a5 P' eP)
      haveI hGQperf : Group.IsPerfect GQ := Group.IsPerfect.range (f := φ)
      exact Subgroup.commutator_eq_self
    have hφcomm : ∀ p (hp : p ∈ P'), ∀ x : Q,
        (φ ⟨p, hp⟩ : Q →ₗ[ZMod 2] Q) (σbar x) =
          σbar ((φ ⟨p, hp⟩ : Q →ₗ[ZMod 2] Q) x) := by
      intro p hp x
      refine Submodule.Quotient.induction_on ℓ x ?_
      intro y
      have hL : (φ ⟨p, hp⟩ : Q →ₗ[ZMod 2] Q) (Submodule.Quotient.mk (σ y)) =
          Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) (σ y)) := by
        change (Submodule.Quotient.equiv ℓ ℓ (p : W ≃ₗ[ZMod 2] W) (hℓmap p hp))
            (Submodule.Quotient.mk (σ y)) =
          Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) (σ y))
        simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
      have hR : (φ ⟨p, hp⟩ : Q →ₗ[ZMod 2] Q) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) y) := by
        change (Submodule.Quotient.equiv ℓ ℓ (p : W ≃ₗ[ZMod 2] W) (hℓmap p hp))
            (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) y)
        simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
      rw [show σbar (Submodule.Quotient.mk y) = Submodule.Quotient.mk (σ y) from
        Submodule.mapQ_apply ℓ ℓ σ y, hL, hR]
      rw [show σbar (Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) y)) =
        Submodule.Quotient.mk (σ ((p : W →ₗ[ZMod 2] W) y)) from
        Submodule.mapQ_apply ℓ ℓ σ ((p : W →ₗ[ZMod 2] W) y)]
      rw [hcommP p hp y]
    have hGQσ : ∀ g ∈ GQ, ∀ x : Q, g (σbar x) = σbar (g x) := by
      intro g hg x
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hg
      exact hφcomm p p.2 x
    haveI hQfin : Finite Q := by
      change Finite (W ⧸ ℓ)
      exact Finite.of_surjective (Submodule.Quotient.mk (p := ℓ))
        (Submodule.Quotient.mk_surjective ℓ)
    have hℓne : ℓ ≠ ⊤ := by
      intro htop
      have h8 : Module.finrank (ZMod 2) ℓ = 8 := by rw [htop, finrank_top, hdim]
      omega
    have hex : ∃ x, x ∉ ℓ := by
      by_contra h
      apply hℓne
      rw [Submodule.eq_top_iff']
      intro x
      exact of_not_not (not_exists.mp h x)
    obtain ⟨x0, hx0⟩ := hex
    let u : Q := Submodule.Quotient.mk x0
    have hu0 : u ≠ 0 := by
      change Submodule.Quotient.mk x0 ≠ 0
      intro h
      exact hx0 ((Submodule.Quotient.mk_eq_zero ℓ).mp h)
    have hu_orbit : Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σbar ^ i) u) = ⊤ := by
      have h4 : Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σbar ^ i) u)) = 4 :=
        finrank_span_orbit_eq_four σbar hσbar5 hu0 (fun x _ hx => hσbar_fpf x hx)
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [h4, hQdim]
    have htriv : ∀ g ∈ GQ, ∀ x : Q, g x = x := by
      have h := perfect_trivial_on_orbit_span σbar GQ hGQ hGQσ u (by
        intro g hg
        rw [hu_orbit]
        trivial)
      intro g hg x
      exact h g hg x (by rw [hu_orbit]; trivial)
    have hmod : ∀ p ∈ P', ∀ x : W, (p : W ≃ₗ[ZMod 2] W) x - x ∈ ℓ := by
      intro p hp x
      have hg : φ ⟨p, hp⟩ ∈ GQ := MonoidHom.mem_range.mpr ⟨⟨p, hp⟩, rfl⟩
      have h := htriv (φ ⟨p, hp⟩) hg (Submodule.Quotient.mk x)
      have h' : (Submodule.Quotient.mk ((p : W →ₗ[ZMod 2] W) x) : Q) =
          (Submodule.Quotient.mk x : Q) := h
      have := (Submodule.Quotient.eq ℓ).mp h'
      simpa [LinearMap.sub_apply] using this
    have hsq : ∀ p ∈ P', ∀ x : W,
        (p : W ≃ₗ[ZMod 2] W) ((p : W ≃ₗ[ZMod 2] W) x) = x := by
      intro p hp x
      have hpx : (p : W ≃ₗ[ZMod 2] W) x - x ∈ ℓ := hmod p hp x
      have hfix : (p : W ≃ₗ[ZMod 2] W) ((p : W ≃ₗ[ZMod 2] W) x - x) =
          (p : W ≃ₗ[ZMod 2] W) x - x := hPfixℓ p hp _ hpx
      rw [map_sub] at hfix
      have h2 : (p : W ≃ₗ[ZMod 2] W) x + (p : W ≃ₗ[ZMod 2] W) x = 0 := by
        rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 ((p : W ≃ₗ[ZMod 2] W) x),
          show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_smul]
      have hx2 : x + x = 0 := by
        rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x,
          show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_smul]
      have hsum : (p : W ≃ₗ[ZMod 2] W) ((p : W ≃ₗ[ZMod 2] W) x) + x = 0 := by
        have := sub_eq_sub_iff_add_eq_add.mp hfix
        rwa [h2] at this
      have hneg : (-x : W) = x := (eq_neg_of_add_eq_zero_left hx2).symm
      calc (p : W ≃ₗ[ZMod 2] W) ((p : W ≃ₗ[ZMod 2] W) x)
          = -x := eq_neg_of_add_eq_zero_left hsum
        _ = x := hneg
    obtain ⟨y3, hy3⟩ := exists_orderOf_eq_three_a5
    let p3 : P' := eP.symm y3
    have hp3ord : orderOf (p3 : W ≃ₗ[ZMod 2] W) = 3 := by
      rw [Subgroup.orderOf_coe]
      have h1 := MulEquiv.orderOf_eq eP p3
      rw [show eP p3 = y3 from eP.apply_symm_apply y3, hy3] at h1
      exact h1.symm
    have hp3sq : (p3 : W ≃ₗ[ZMod 2] W) * (p3 : W ≃ₗ[ZMod 2] W) = 1 := by
      ext x
      simpa [LinearEquiv.mul_apply] using hsq p3 p3.2 x
    have hp3cube : (p3 : W ≃ₗ[ZMod 2] W) ^ 3 = 1 := by
      rw [← hp3ord]
      exact pow_orderOf_eq_one _
    have hp3one : (p3 : W ≃ₗ[ZMod 2] W) = 1 := by
      have h2 : (p3 : W ≃ₗ[ZMod 2] W) ^ 2 = 1 := by rw [pow_two]; exact hp3sq
      calc (p3 : W ≃ₗ[ZMod 2] W) = (p3 : W ≃ₗ[ZMod 2] W) * 1 := (mul_one _).symm
        _ = (p3 : W ≃ₗ[ZMod 2] W) * (p3 : W ≃ₗ[ZMod 2] W) ^ 2 := by rw [h2]
        _ = (p3 : W ≃ₗ[ZMod 2] W) ^ 3 := by rw [pow_succ']; rfl
        _ = 1 := hp3cube
    have h1 : orderOf (p3 : W ≃ₗ[ZMod 2] W) = 1 := by rw [hp3one, orderOf_one]
    omega

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
