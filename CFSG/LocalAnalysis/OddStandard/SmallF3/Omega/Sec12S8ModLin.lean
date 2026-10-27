module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModLina
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Polynomial

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem sec12S8Mod_lin_decomp (c : W ≃ₗ[ZMod 2] W) (hc3 : c ^ 3 = 1) (e : W) :
    ∃ x y : W, c x = x ∧ c (c y) + c y + y = 0 ∧ e = x + y := by
  have hc3' : c * c * c = 1 := by
    have h := hc3
    rwa [pow_three'] at h
  have hc3e : ∀ u : W, c (c (c u)) = u := by
    intro u
    have h := congrArg (fun f : W ≃ₗ[ZMod 2] W => f u) hc3'
    simpa [LinearEquiv.mul_apply] using h
  refine ⟨c (c e) + c e + e, c (c e) + c e, ?_, ?_, ?_⟩
  · simp only [map_add]
    rw [hc3e]
    abel
  · have hcy : c (c (c e) + c e) = e + c (c e) := by
      simp only [map_add, hc3e]
    have hccy : c (c (c (c e) + c e)) = c e + e := by
      rw [hcy]
      simp only [map_add, hc3e]
    rw [hccy, hcy]
    calc (c e + e) + (e + c (c e)) + (c (c e) + c e)
        = (e + e) + (c (c e) + c (c e)) + (c e + c e) := by abel
      _ = 0 := by simp [sec12S8Mod_charTwo]
  · have hxy : (c (c e) + c e + e) + (c (c e) + c e) = e := by
      calc (c (c e) + c e + e) + (c (c e) + c e)
          = (c (c e) + c (c e)) + (c e + c e) + e := by abel
        _ = e := by simp [sec12S8Mod_charTwo]
    exact hxy.symm

theorem sec12S8Mod_lin_card_D (hW : Nat.card W = 2 ^ 8) (c : W ≃ₗ[ZMod 2] W) (hc3 : c ^ 3 = 1)
    (hc16 : Nat.card {v : W // c v = v} = 16) :
    Nat.card {y : W // c (c y) + c y + y = 0} = 16 := by
  set C : Submodule (ZMod 2) W := LinearMap.ker ((c : Module.End (ZMod 2) W) + 1) with hC
  set D : Submodule (ZMod 2) W :=
    LinearMap.ker ((c : Module.End (ZMod 2) W) * (c : Module.End (ZMod 2) W)
      + (c : Module.End (ZMod 2) W) + 1) with hD
  have hCmem : ∀ z : W, z ∈ C ↔ c z = z := by
    intro z
    rw [hC]
    change ((c : Module.End (ZMod 2) W) + 1) z = 0 ↔ (c : Module.End (ZMod 2) W) z = z
    simp only [LinearMap.add_apply, Module.End.one_apply]
    constructor
    · intro h
      calc (c : Module.End (ZMod 2) W) z = (c : Module.End (ZMod 2) W) z + 0 :=
            (add_zero _).symm
        _ = (c : Module.End (ZMod 2) W) z + (z + z) := by rw [sec12S8Mod_charTwo]
        _ = ((c : Module.End (ZMod 2) W) z + z) + z := by abel
        _ = 0 + z := by rw [h]
        _ = z := zero_add z
    · intro h
      rw [h, sec12S8Mod_charTwo]
  have hDmem : ∀ z : W, z ∈ D ↔ c (c z) + c z + z = 0 := by
    intro z
    rw [hD]
    change ((c : Module.End (ZMod 2) W) * (c : Module.End (ZMod 2) W)
        + (c : Module.End (ZMod 2) W) + 1) z = 0 ↔
      (c : Module.End (ZMod 2) W) ((c : Module.End (ZMod 2) W) z)
        + (c : Module.End (ZMod 2) W) z + z = 0
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  have hcompl : IsCompl C D := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro z hz
      rw [Submodule.mem_inf] at hz
      obtain ⟨hzC, hzD⟩ := hz
      have hzfix : c z = z := (hCmem z).mp hzC
      have hzD' : c (c z) + c z + z = 0 := (hDmem z).mp hzD
      rw [hzfix] at hzD'
      rw [hzfix] at hzD'
      simpa [sec12S8Mod_charTwo] using hzD'
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro e
      obtain ⟨x, y, hx, hy, he⟩ := sec12S8Mod_lin_decomp c hc3 e
      rw [he]
      exact Submodule.add_mem_sup ((hCmem x).mpr hx) ((hDmem y).mpr hy)
  have hcardprod : Nat.card (C × D) = Nat.card W :=
    Nat.card_congr (Submodule.prodEquivOfIsCompl C D hcompl).toEquiv
  have hWCD : Nat.card W = Nat.card C * Nat.card D := by
    rw [← hcardprod, Nat.card_prod]
  have hCcard : Nat.card C = 16 := by
    have hsub : Nat.card C = Nat.card {v : W // c v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight hCmem)
    rw [hsub, hc16]
  have hDsub : Nat.card {y : W // c (c y) + c y + y = 0} = Nat.card D :=
    (Nat.card_congr (Equiv.subtypeEquivRight hDmem)).symm
  have hmain : Nat.card W = Nat.card C * Nat.card D := hWCD
  rw [hW, hCcard] at hmain
  have hpow : (2 : ℕ) ^ 8 = 256 := by decide
  rw [hpow] at hmain
  have hDval : Nat.card D = 16 := by omega
  rw [hDsub]
  exact hDval

theorem sec12S8Mod_lin_orbit (g : W ≃ₗ[ZMod 2] W) (hg5 : g ^ 5 = 1)
    (hgfix : ∀ v : W, g v = v → v = 0) (S : Submodule (ZMod 2) W) (hS : ∀ v ∈ S, g v ∈ S) :
    Nat.card S % 5 = 1 := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun v => ⟨g v, hS v v.2⟩
  have hf5 : f ^ 5 = 1 := by
    funext v
    apply Subtype.ext
    change (g ^ 5) (v : W) = (v : W)
    exact congrArg (fun e : W ≃ₗ[ZMod 2] W => e (v : W)) hg5
  have hfix : Fintype.card (Function.fixedPoints (f : S → S)) = 1 := by
    have hset : Function.fixedPoints (f : S → S) = {0} := by
      ext v
      rw [Function.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hv
        apply Subtype.ext
        apply hgfix
        have h := congrArg (fun w : S => (w : W)) hv
        simpa [f] using h
      · intro hv
        subst hv
        apply Subtype.ext
        simp [f]
    have hcard : Fintype.card (Function.fixedPoints (f : S → S)) =
        Fintype.card ({0} : Set S) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by
        show v ∈ Function.fixedPoints (f : S → S) ↔ v ∈ ({0} : Set S)
        rw [hset]))
    simpa using hcard
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) (f := f) (p := 5) (n := 1) hf5
  rw [hfix] at hmod
  rw [Nat.ModEq] at hmod
  simpa [Nat.card_eq_fintype_card] using hmod

theorem sec12S8Mod_lin_cyclic (hW : Nat.card W = 2 ^ 8) (g c : W ≃ₗ[ZMod 2] W)
    (hg5 : g ^ 5 = 1) (hgfix : ∀ v : W, g v = v → v = 0) (hc3 : c ^ 3 = 1)
    (hc16 : Nat.card {v : W // c v = v} = 16) (hgc : g * c = c * g) {d : W}
    (hd : c (c d) + c d + d = 0) (hd0 : d ≠ 0) {e : W} (he : c (c e) + c e + e = 0) :
    ∃ p : (ZMod 2)[X], e = (aeval (g : Module.End (ZMod 2) W) p) d := by
  let G : Module.End (ZMod 2) W := g
  let φ : (ZMod 2)[X] →ₗ[ZMod 2] W :=
    (LinearMap.applyₗ d).comp (Polynomial.aeval G).toLinearMap
  have hφ : ∀ p, φ p = (aeval G p) d := by
    intro p
    simp [φ, LinearMap.comp_apply]
  set S : Submodule (ZMod 2) W :=
    Submodule.span (ZMod 2) (Set.range fun n : ℕ => (G ^ n) d) with hS
  set D : Submodule (ZMod 2) W :=
    LinearMap.ker ((c : Module.End (ZMod 2) W) * (c : Module.End (ZMod 2) W)
      + (c : Module.End (ZMod 2) W) + 1) with hDdef
  have hDmem : ∀ z : W, z ∈ D ↔ c (c z) + c z + z = 0 := by
    intro z
    rw [hDdef]
    change ((c : Module.End (ZMod 2) W) * (c : Module.End (ZMod 2) W)
        + (c : Module.End (ZMod 2) W) + 1) z = 0 ↔
      (c : Module.End (ZMod 2) W) ((c : Module.End (ZMod 2) W) z)
        + (c : Module.End (ZMod 2) W) z + z = 0
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  have hcg : ∀ v : W, c (g v) = g (c v) := by
    intro v
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e v) hgc
    simpa [LinearEquiv.mul_apply] using h.symm
  have hDg : ∀ y : W, c (c y) + c y + y = 0 → c (c (g y)) + c (g y) + g y = 0 := by
    intro y hy
    have hgy : c (g y) = g (c y) := hcg y
    have hgcy : c (g (c y)) = g (c (c y)) := hcg (c y)
    have hcc : c (c (g y)) = g (c (c y)) := by rw [hgy, hgcy]
    calc c (c (g y)) + c (g y) + g y
        = g (c (c y)) + g (c y) + g y := by rw [hcc, hgy]
      _ = g (c (c y) + c y + y) := by rw [map_add, map_add]
      _ = 0 := by rw [hy, map_zero]
  have hDgpow : ∀ n : ℕ, c (c ((G ^ n) d)) + c ((G ^ n) d) + (G ^ n) d = 0 := by
    intro n
    induction n with
    | zero => simpa [G] using hd
    | succ m ih =>
        have hstep : (G ^ (m + 1)) d = g ((G ^ m) d) := by
          simp [G, pow_succ', Module.End.mul_apply]
        rw [hstep]
        exact hDg _ ih
  have hSD : S ≤ D := by
    rw [hS]
    apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    exact (hDmem _).mpr (hDgpow n)
  have hSmap : S.map (g : W →ₗ[ZMod 2] W) ≤ S := by
    rw [hS, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := hy
    exact Submodule.subset_span ⟨n + 1, by simp [G, pow_succ', Module.End.mul_apply]⟩
  have hSstab : ∀ v ∈ S, g v ∈ S := fun v hv =>
    hSmap (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  have hdS : d ∈ S := by
    rw [hS]
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hSmod : Nat.card S % 5 = 1 := sec12S8Mod_lin_orbit g hg5 hgfix S hSstab
  have hDcard : Nat.card D = 16 := by
    have hsub : Nat.card D = Nat.card {y : W // c (c y) + c y + y = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight hDmem)
    rw [hsub, sec12S8Mod_lin_card_D hW c hc3 hc16]
  have hdvd : Nat.card S ∣ Nat.card D := by
    simpa using AddSubgroup.card_dvd_of_le (Submodule.toAddSubgroup_mono hSD)
  have hSne1 : Nat.card S ≠ 1 := by
    intro h1
    haveI : Subsingleton S := (Finite.card_le_one_iff_subsingleton).mp (le_of_eq h1)
    have hzero : (⟨d, hdS⟩ : S) = 0 := Subsingleton.elim _ _
    exact hd0 (congrArg Subtype.val hzero)
  obtain ⟨k, hk4, hk⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 4) Nat.prime_two).mp (by
      simpa [hDcard] using hdvd)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hSne1 hk
  have hkmod : 2 ^ k % 5 = 1 := by rw [← hk]; exact hSmod
  have hS16 : Nat.card S = 16 := by
    interval_cases k
    · exact absurd rfl hk0
    · exact absurd hkmod (by decide)
    · exact absurd hkmod (by decide)
    · exact absurd hkmod (by decide)
    · rw [hk]; decide
  have hSrange : S ≤ LinearMap.range φ := by
    rw [hS]
    apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    exact ⟨X ^ n, by rw [hφ, Polynomial.aeval_X_pow]⟩
  have heD : e ∈ D := (hDmem e).mpr he
  have hSD_eq : S = D := by
    classical
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype D := Fintype.ofFinite D
    apply SetLike.coe_injective
    apply Set.eq_of_subset_of_card_le hSD
    have hle : Fintype.card D ≤ Fintype.card S := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hS16, hDcard]
    exact hle
  have heS : e ∈ S := by
    rw [hSD_eq]
    exact heD
  obtain ⟨p, hp⟩ := hSrange heS
  exact ⟨p, hp.symm.trans (hφ p)⟩

theorem sec12S8Mod_lin_frob (g : Module.End (ZMod 2) W) (q : (ZMod 2)[X]) :
    (aeval g q) ^ 4 = aeval (g ^ 4) q := by
  have hexp : ∀ f : (ZMod 2)[X], expand (ZMod 2) 2 f = f ^ 2 := by
    intro f
    have h := map_frobenius_expand (R := ZMod 2) (p := 2) (f := f)
    rw [ZMod.frobenius_zmod] at h
    simpa using h
  have hq : q ^ 4 = expand (ZMod 2) 4 q := by
    conv_rhs => rw [show (4 : ℕ) = 2 ^ 2 by decide, expand_pow]
    change q ^ 4 = expand (ZMod 2) 2 (expand (ZMod 2) 2 q)
    rw [hexp q, hexp (q ^ 2)]
    ring
  calc (aeval g q) ^ 4 = aeval g (q ^ 4) := (map_pow (aeval g) q 4).symm
    _ = aeval g (expand (ZMod 2) 4 q) := by rw [hq]
    _ = aeval (g ^ 4) q := expand_aeval 4 q g

theorem sec12S8Mod_lin (hW : Nat.card W = 2 ^ 8) (g c w : W ≃ₗ[ZMod 2] W) (hg5 : g ^ 5 = 1)
    (hgfix : ∀ v : W, g v = v → v = 0) (hc3 : c ^ 3 = 1)
    (hc16 : Nat.card {v : W // c v = v} = 16) (hgc : g * c = c * g)
    (hwg : w * g * w⁻¹ = g⁻¹) (hwc : w * c * w⁻¹ = c⁻¹) : False := by
  let G : Module.End (ZMod 2) W := g
  have hgcE : (c : Module.End (ZMod 2) W) * G = G * (c : Module.End (ZMod 2) W) := by
    ext v
    simpa [G, Module.End.mul_apply, LinearEquiv.mul_apply] using
      (congrArg (fun e : W ≃ₗ[ZMod 2] W => e v) hgc).symm
  have hc3e : ∀ u : W, c (c (c u)) = u := by
    intro u
    have h : c * c * c = 1 := by
      have hh := hc3
      rwa [pow_three'] at hh
    have hh := congrArg (fun f : W ≃ₗ[ZMod 2] W => f u) h
    simpa [LinearEquiv.mul_apply] using hh
  have hc_inv : c⁻¹ = c ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ' c 2]
    exact hc3
  have hc_inv_inv : c⁻¹ * c⁻¹ = c := by
    rw [hc_inv, ← pow_add, show (2 + 2 : ℕ) = 3 + 1 from rfl, pow_add, hc3, one_mul,
      pow_one]
  have hc4 : c ^ 4 = c := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hc3, one_mul, pow_one]
  have hDcard := sec12S8Mod_lin_card_D hW c hc3 hc16
  haveI : Nontrivial {y : W // c (c y) + c y + y = 0} :=
    (Finite.one_lt_card_iff_nontrivial).mp (by rw [hDcard]; decide)
  obtain ⟨dsub, hdne⟩ :=
    exists_ne (⟨0, by simp⟩ : {y : W // c (c y) + c y + y = 0})
  let d : W := dsub.1
  have hd : c (c d) + c d + d = 0 := dsub.2
  have hd0 : d ≠ 0 := fun h => hdne (Subtype.ext h)
  have hcdP : c (c (c d)) + c (c d) + c d = 0 := by
    rw [hc3e d]
    have h : d + c (c d) + c d = c (c d) + c d + d := by abel
    rw [h, hd]
  obtain ⟨q, hq⟩ := sec12S8Mod_lin_cyclic hW g c hg5 hgfix hc3 hc16 hgc hd hd0 hcdP
  have hcomm_apply : ∀ (p : (ZMod 2)[X]) (u : W),
      c ((aeval G p) u) = (aeval G p) (c u) := by
    intro p u
    have h := congrArg (fun f : Module.End (ZMod 2) W => f u)
      (sec12S8Mod_commute_aeval G (c : Module.End (ZMod 2) W) hgcE p)
    simpa [Module.End.mul_apply, LinearEquiv.coe_toLinearMap] using h
  have hA : ∀ x : W, c (c x) + c x + x = 0 → c x = (aeval G q) x := by
    intro x hx
    obtain ⟨p, hp⟩ := sec12S8Mod_lin_cyclic hW g c hg5 hgfix hc3 hc16 hgc hd hd0 hx
    calc c x = c ((aeval G p) d) := by rw [hp]
      _ = (aeval G p) (c d) := hcomm_apply p d
      _ = (aeval G p) ((aeval G q) d) := by rw [hq]
      _ = (aeval G p * aeval G q) d := by rw [Module.End.mul_apply]
      _ = (aeval G (p * q)) d := by rw [map_mul]
      _ = (aeval G (q * p)) d := by rw [mul_comm]
      _ = (aeval G q * aeval G p) d := by rw [map_mul]
      _ = (aeval G q) ((aeval G p) d) := by rw [Module.End.mul_apply]
      _ = (aeval G q) x := by rw [hp]
  have hwc_apply : ∀ z : W, c (w⁻¹ z) = w⁻¹ (c⁻¹ z) := by
    intro z
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e z) hwc
    have h' : w (c (w⁻¹ z)) = c⁻¹ z := by simpa [LinearEquiv.mul_apply] using h
    calc c (w⁻¹ z) = w⁻¹ (w (c (w⁻¹ z))) := by simp
      _ = w⁻¹ (c⁻¹ z) := by rw [h']
  have hDwinv : ∀ y : W, c (c y) + c y + y = 0 → c (c (w⁻¹ y)) + c (w⁻¹ y) + w⁻¹ y = 0 := by
    intro y hy
    have h1 : c (w⁻¹ y) = w⁻¹ (c⁻¹ y) := hwc_apply y
    have h2 : c (c (w⁻¹ y)) = w⁻¹ (c y) := by
      rw [h1, hwc_apply (c⁻¹ y)]
      rw [show c⁻¹ (c⁻¹ y) = c y from by rw [← LinearEquiv.mul_apply, hc_inv_inv]]
    rw [h2, h1, ← map_add, ← map_add]
    rw [show c y + c⁻¹ y + y = 0 from by
      rw [show c⁻¹ y = c (c y) from by rw [hc_inv, pow_two, LinearEquiv.mul_apply]]
      rw [show c y + c (c y) + y = c (c y) + c y + y from by abel, hy]]
    simp
  have hwgE : (w : Module.End (ZMod 2) W) * G * (w.symm : Module.End (ZMod 2) W)
      = ((g⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) := by
    ext v
    simpa [G, Module.End.mul_apply, LinearEquiv.mul_apply] using
      congrArg (fun e : W ≃ₗ[ZMod 2] W => e v) hwg
  have hg4E : ((g⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) = G ^ 4 := by
    have hmul : g * g ^ 4 = 1 := by
      rw [← pow_succ' g 4]
      exact hg5
    have hginv : g⁻¹ = g ^ 4 := inv_eq_of_mul_eq_one_right hmul
    rw [hginv]
    exact map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) g 4
  have hconj : ∀ u : W, w ((aeval G q) (w⁻¹ u)) = aeval (G ^ 4) q u := fun u =>
    sec12S8Mod_conj_aeval w G (by rw [hwgE, hg4E]) q u
  have hfrob : (aeval G q) ^ 4 = aeval (G ^ 4) q := sec12S8Mod_lin_frob G q
  have hfinal : ∀ x : W, c (c x) + c x + x = 0 → x = 0 := by
    intro x hx
    have hx' : c (w⁻¹ x) = (aeval G q) (w⁻¹ x) := hA (w⁻¹ x) (hDwinv x hx)
    have hDc : ∀ y : W, c (c y) + c y + y = 0 → c (c (c y)) + c (c y) + c y = 0 := by
      intro y hy
      rw [hc3e y]
      have h : y + c (c y) + c y = c (c y) + c y + y := by abel
      rw [h, hy]
    have hDcpow : ∀ k : ℕ, c (c ((c ^ k) x)) + c ((c ^ k) x) + (c ^ k) x = 0 := by
      intro k
      induction k with
      | zero => simpa using hx
      | succ m ih =>
          have hstep : (c ^ (m + 1)) x = c ((c ^ m) x) := by
            simp [pow_succ', Module.End.mul_apply]
          rw [hstep]
          exact hDc _ ih
    have hstep : c⁻¹ x = aeval (G ^ 4) q x := by
      calc c⁻¹ x = w (w⁻¹ (c⁻¹ x)) := by simp
        _ = w (c (w⁻¹ x)) := by rw [← hwc_apply x]
        _ = w ((aeval G q) (w⁻¹ x)) := by rw [hx']
        _ = aeval (G ^ 4) q x := hconj x
    have hfe : ∀ j : ℕ, ((aeval G q) ^ j) x = (c ^ j) x := by
      intro j
      induction j with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', Module.End.mul_apply, ih]
          rw [← hA ((c ^ k) x) (hDcpow k)]
          rw [pow_succ', LinearEquiv.mul_apply]
    have h4 : c⁻¹ x = c x := by
      calc c⁻¹ x = aeval (G ^ 4) q x := hstep
        _ = ((aeval G q) ^ 4) x := by rw [← hfrob]
        _ = (c ^ 4) x := hfe 4
        _ = c x := by rw [hc4]
    have hcc : c (c x) = c x := by
      rw [show c (c x) = (c ^ 2) x from by rw [pow_two, LinearEquiv.mul_apply]]
      rw [← hc_inv]
      exact h4
    have hP0 : c (c x) + c x + x = 0 := hx
    rw [hcc] at hP0
    simpa [sec12S8Mod_charTwo] using hP0
  exact hd0 (hfinal d hd)

end CFSG.OddStandard.SmallF3.Omega
