module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutUCenter
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply elt mat_elt E)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

variable {K : Type} [Field K]

section Orbits

variable {m : ℕ}

theorem exists_torusParam {i j : Fin m} (hij : i ≠ j) (u v : Kˣ) :
    ∃ t : Fin m → Kˣ, t i = u ∧ t j = v :=
  ⟨fun k => if k = i then u else if k = j then v else 1, by simp, by simp [Ne.symm hij]⟩

theorem exists_conj_diagSp_twoCentralElt_eq [Finite K] [CharP K 2] {i j : Fin m} (hij : i ≠ j)
    {a b : K} (hab : ¬(a = 0 ∧ b = 0)) :
    ∃ (t : Fin m → Kˣ) (κ : SpTwoCentral),
      diagSp K m t * twoCentralElt m i j a b * (diagSp K m t)⁻¹ = twoCentralRep m i j κ := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  by_cases ha : a = 0
  ·
    have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
    obtain ⟨t, hti, htj⟩ := exists_torusParam (K := K) hij 1 (Units.mk0 b hb)⁻¹
    refine ⟨t, .a2, ?_⟩
    rw [conj_diagSp_twoCentralElt, twoCentralRep, hti, htj, ha]
    congr 1
    · simp [SpTwoCentral.params]
    · simp [SpTwoCentral.params, hb]
  · have hr0 : r ≠ 0 := by
      rintro rfl
      exact ha (by rw [hr, mul_zero])
    by_cases hb : b = 0
    ·
      obtain ⟨t, hti, htj⟩ := exists_torusParam (K := K) hij (Units.mk0 r hr0)⁻¹ 1
      refine ⟨t, .b1, ?_⟩
      rw [conj_diagSp_twoCentralElt, twoCentralRep, hti, htj, hb]
      congr 1
      · simp only [SpTwoCentral.params, Units.val_inv_eq_inv_val, Units.val_mk0, hr]
        field_simp
      · simp [SpTwoCentral.params]
    ·
      obtain ⟨t, hti, htj⟩ := exists_torusParam (K := K) hij (Units.mk0 r hr0)⁻¹
        (Units.mk0 (r⁻¹ * b) (mul_ne_zero (inv_ne_zero hr0) hb))⁻¹
      refine ⟨t, .c2, ?_⟩
      rw [conj_diagSp_twoCentralElt, twoCentralRep, hti, htj]
      congr 1
      · simp only [SpTwoCentral.params, Units.val_inv_eq_inv_val, Units.val_mk0, hr]
        field_simp
      · simp only [SpTwoCentral.params, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp

end Orbits

section Classes

theorem exists_conj_mem_sylow_of_isPGroup' {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P) (U : Sylow p X) :
    ∃ x : X, ∀ y ∈ P, x * y * x⁻¹ ∈ (U : Subgroup X) := by
  obtain ⟨U', hU'⟩ := hP.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq X U' U
  refine ⟨x, fun y hy => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simpa [mul_assoc] using hU' hy

theorem isPGroup_unipotent [Finite K] [CharP K 2] (r : ℕ) : IsPGroup 2 (unipotent r K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  rw [← hP]
  exact P.isPGroup'

theorem exists_perm_zero_one (n : ℕ) :
    ∃ π : Equiv.Perm (Fin (n + 3)), π 0 = 1 ∧ π 1 = 2 := by
  have h01 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  have h02 : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_two] at h'
    omega
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12)]

theorem exists_conj_eq_spRep [Finite K] [CharP K 2] {n : ℕ} {z : StatedSp (n + 3) K}
    (hz : z ≠ 1) {U : Sylow 2 (StatedSp (n + 3) K)}
    (hzU : ∀ u ∈ (U : Subgroup (StatedSp (n + 3) K)), u * z = z * u) :
    ∃ (κ : SpTwoCentral) (c : StatedSp (n + 3) K), c * z * c⁻¹ = spRep n κ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup' (isPGroup_unipotent (K := K) (n + 3)) U
  have hz' : g⁻¹ * z * g ∈
      centralizer (unipotent (n + 1 + 2) K : Set (StatedSp (n + 1 + 2) K)) := by
    rw [mem_centralizer_iff]
    intro u hu
    have h := hzU _ (hg u hu)
    calc u * (g⁻¹ * z * g) = g⁻¹ * ((g * u * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * u * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * z * g * u := by group
  obtain ⟨a, b, hab⟩ := (centralizer_unipotent (m := n + 1) (K := K)).le hz'
  have hab0 : ¬(a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    rw [twoCentralElt_zero] at hab
    apply hz
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [← hab, mul_one, mul_inv_cancel]
  have h01 : (0 : Fin (n + 3)) ≠ 1 := by simp
  obtain ⟨t, κ, htκ⟩ := exists_conj_diagSp_twoCentralElt_eq (K := K) h01 hab0
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_zero_one n
  refine ⟨κ, permSp K π * diagSp K (n + 3) t * g⁻¹, ?_⟩
  have hc : permSp K π * diagSp K (n + 3) t * g⁻¹ * z * (permSp K π * diagSp K (n + 3) t * g⁻¹)⁻¹ =
      permSp K π * (diagSp K (n + 3) t * (g⁻¹ * z * g) * (diagSp K (n + 3) t)⁻¹) *
        (permSp K π)⁻¹ := by group
  rw [hc, ← hab]
  change permSp K π * (diagSp K (n + 3) t * twoCentralElt (n + 3) 0 1 a b *
    (diagSp K (n + 3) t)⁻¹) * (permSp K π)⁻¹ = spRep n κ
  rw [htκ, twoCentralRep, conj_permSp_twoCentralElt, hπ0, hπ1]
  rfl

theorem exists_sylow_commute_spRep [Finite K] [CharP K 2] (n : ℕ) (κ : SpTwoCentral) :
    ∃ U : Sylow 2 (StatedSp (n + 3) K),
      ∀ u ∈ (U : Subgroup (StatedSp (n + 3) K)), u * spRep n κ = spRep n κ * u := by
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (n + 3)
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_zero_one n
  refine ⟨permSp K π • P, fun u hu => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv, hP] at hu
  have hzc := spHighRootCenter_le_centralizer_unipotent (m := n + 1) (K := K)
    ⟨(κ.params K).1, (κ.params K).2, rfl⟩
  rw [mem_centralizer_iff] at hzc
  have h := hzc _ hu
  have hrep : spRep n κ = permSp K π * twoCentralElt (n + 3) 0 1 (κ.params K).1 (κ.params K).2 *
      (permSp K π)⁻¹ := by
    rw [conj_permSp_twoCentralElt, hπ0, hπ1]
    rfl
  rw [hrep]
  set w := twoCentralElt (n + 3) 0 1 (κ.params K).1 (κ.params K).2
  change (permSp K π)⁻¹ * u * (permSp K π) * w = w * ((permSp K π)⁻¹ * u * (permSp K π)) at h
  calc u * (permSp K π * w * (permSp K π)⁻¹) =
      permSp K π * ((permSp K π)⁻¹ * u * permSp K π * w) * (permSp K π)⁻¹ := by group
    _ = permSp K π * (w * ((permSp K π)⁻¹ * u * permSp K π)) * (permSp K π)⁻¹ := by rw [h]
    _ = permSp K π * w * (permSp K π)⁻¹ * u := by group

end Classes

section AutU

theorem mem_range_conj_of_fix_sylow_sp [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r)
    (U : Sylow 2 (StatedSp r K)) (β : MulAut (StatedSp r K))
    (hβ : ∀ u ∈ (U : Subgroup (StatedSp r K)), β u = u) :
    β ∈ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup' (isPGroup_unipotent (K := K) r) U
  set i0 : Fin r := ⟨0, by omega⟩
  set β' := (MulAut.conj g)⁻¹ * β * MulAut.conj g with hβ'
  have hfix : ∀ c : K, β' (elt (.positiveLong i0) c) = elt (.positiveLong i0) c := by
    intro c
    have hmem := hg _ (elt_positiveLong_mem_unipotent i0 c)
    rw [hβ', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hβ _ hmem,
      MulAut.conj_inv_apply]
    group
  obtain ⟨s, hs⟩ := exists_eq_conj_of_forall_elt_fix hr hfix
  refine ⟨g * s * g⁻¹, ?_⟩
  have hβeq : β = MulAut.conj g * β' * (MulAut.conj g)⁻¹ := by
    rw [hβ']
    group
  rw [hβeq, hs, map_mul, map_mul, map_inv]

theorem mem_range_conj_of_fix_sylow_of_mulEquiv [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r)
    {X : Type*} [Group X] (e : X ≃* StatedSp r K) (U : Sylow 2 X) (β : MulAut X)
    (hβ : ∀ u ∈ (U : Subgroup X), β u = u) : β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set U' : Sylow 2 (StatedSp r K) := U.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨y, hy⟩ := mem_range_conj_of_fix_sylow_sp hr U' (MulAut.congr e β) fun u hu => by
    obtain ⟨x, hx, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hβ x hx]
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem exists_conj_eq_spRep_of_mulEquiv [Finite K] [CharP K 2] {n : ℕ} {X : Type*} [Group X]
    (e : X ≃* StatedSp (n + 3) K) {z : X} (hz : z ≠ 1) {U : Sylow 2 X}
    (hzU : ∀ u ∈ (U : Subgroup X), u * z = z * u) :
    ∃ (κ : SpTwoCentral) (c : X), c * z * c⁻¹ = e.symm (spRep n κ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set U' : Sylow 2 (StatedSp (n + 3) K) := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hz' : e z ≠ 1 := fun h => hz (e.injective (h.trans (map_one e).symm))
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep hz' (U := U') fun u hu => by
    obtain ⟨x, hx, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hzU x hx]
  refine ⟨κ, e.symm c, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end AutU

section Fusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_spRep_of_hnot (hset : SeitzSetting G L) {n : ℕ} [Finite K] [CharP K 2]
    (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    ∃ (g : G) (κ : SpTwoCentral), g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) := by
  obtain ⟨g, z, hzL, hgz, hz1, U, hU⟩ := exists_conj_eq_mul_twoCentral hset (by omega) e ht hKt
    hnot fun U β hβ => mem_range_conj_of_fix_sylow_of_mulEquiv (by omega) e U β hβ
  have hz' : (⟨z, hzL⟩ : L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep_of_mulEquiv e hz' (U := U) fun u hu =>
    Subtype.ext (hU u hu)
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hct : (c : G) * t = t * c := (mem_centralizer_iff.1 htC _ c.2)
  refine ⟨g * (c : G)⁻¹, κ, ?_⟩
  have hc' : (c : G) * z * (c : G)⁻¹ = (e.symm (spRep n κ) : G) := by
    rw [← hc]
    rfl
  calc (g * (c : G)⁻¹)⁻¹ * t * (g * (c : G)⁻¹) = (c : G) * (g⁻¹ * t * g) * (c : G)⁻¹ := by group
    _ = ((c : G) * t) * z * (c : G)⁻¹ := by rw [hgz]; group
    _ = t * ((c : G) * z * (c : G)⁻¹) := by rw [hct]; group
    _ = t * (e.symm (spRep n κ) : G) := by rw [hc']

theorem exists_conj_eq_mul_twoCentral_twoSided_of_hnot (hset : SeitzSetting G L) {r : ℕ}
    (hr : 3 ≤ r) [Finite K] [CharP K 2] (e : L ≃* StatedSp r K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ :=
  exists_conj_eq_mul_twoCentral_twoSided hset hr e ht hKt hnot fun U β hβ =>
    mem_range_conj_of_fix_sylow_of_mulEquiv hr e U β hβ

theorem exists_conj_eq_mul_spRep_twoSided_of_hnot (hset : SeitzSetting G L) {n : ℕ} [Finite K]
    [CharP K 2] (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ (κ : SpTwoCentral) (c : L), (c : G) * z * (c : G)⁻¹ = (e.symm (spRep n κ) : G)) ∧
      (∃ (κ' : SpTwoCentral) (c' : CFSG.conjugate L x), (c' : G) * z * (c' : G)⁻¹ =
        ((conjugateMulEquiv L x (e.symm (spRep n κ')) : CFSG.conjugate L x) : G)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  obtain ⟨x, z, hz, hxz, hz1, ⟨U, hU⟩, ⟨U', hU'⟩, hact⟩ :=
    exists_conj_eq_mul_twoCentral_twoSided_of_hnot hset (by omega) e ht hKt hnot
  refine ⟨x, z, hz, hxz, ?_, ?_, hact⟩
  · have hz' : (⟨z, hz.1⟩ : L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep_of_mulEquiv e hz' (U := U) fun u hu =>
      Subtype.ext (hU u hu)
    exact ⟨κ, c, by rw [← hc]; rfl⟩
  · have hz' : (⟨z, hz.2⟩ : CFSG.conjugate L x) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    obtain ⟨κ', c', hc'⟩ := exists_conj_eq_spRep_of_mulEquiv
      ((conjugateMulEquiv L x).symm.trans e) hz' (U := U') fun u hu => Subtype.ext (hU' u hu)
    refine ⟨κ', c', ?_⟩
    rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm] at hc'
    rw [← hc']
    rfl

end Fusion

end CFSG.SeitzReduction.SymplecticPilot
