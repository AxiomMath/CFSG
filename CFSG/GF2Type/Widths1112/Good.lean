module

public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.GF2Type.Widths1112.Core
public import CFSG.GF2Type.Widths1112.Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial

namespace CFSG.GF2Type.Widths1112

variable {G : Type} [Group G] [Finite G]

instance finiteO (S : Setting G) : Finite S.O :=
  Finite.of_injective (fun s : S.O => ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

@[expose] def IsGood (S : Setting G) (v : S.Qt) : Prop :=
  v ≠ 0 ∧ S.q v = 0 ∧ ¬ 2 ^ (2 * S.width - 2) ∣ Nat.card S.Mbar ∧
    ∃ H : Subgroup S.O, H ≤ S.Mbar ∧
      (∀ h ∈ H, ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      ∀ U : Submodule (ZMod 2) S.Qt, v ∈ U →
        U ≤ LinearMap.ker (QuadraticMap.polarBilin S.q v) →
        (∀ h ∈ H, U.map (((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = U) →
        U = Submodule.span (ZMod 2) {v} ∨ U = LinearMap.ker (QuadraticMap.polarBilin S.q v)

@[expose] def GoodThroughSingular (S : Setting G) : Prop :=
  ∀ v : S.Qt, v ≠ 0 → S.q v = 0 → ∀ U : Submodule (ZMod 2) S.Qt, v ∈ U →
    2 ≤ Module.finrank (ZMod 2) U → (∀ u ∈ U, S.q u = 0) →
    (∀ m ∈ S.Mbar, ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v →
      U.map (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = U) →
    ∃ u ∈ U, u ≠ v ∧ IsGood S u

def stabL (S : Setting G) (v : S.Qt) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) where
  carrier := {g | (∃ s : S.M, ((S.ρ s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = g) ∧ g v = v}
  mul_mem' := by
    rintro a b ⟨⟨s₁, rfl⟩, ha⟩ ⟨⟨s₂, rfl⟩, hb⟩
    refine ⟨⟨s₁ * s₂, ?_⟩, ?_⟩
    · rw [map_mul, Subgroup.coe_mul]
    · show ((S.ρ s₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ s₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
      rw [hb, ha]
  one_mem' := by
    refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [map_one, Subgroup.coe_one]
    · rfl
  inv_mem' := by
    rintro a ⟨⟨s, rfl⟩, ha⟩
    refine ⟨⟨s⁻¹, ?_⟩, ?_⟩
    · rw [map_inv, Subgroup.coe_inv]
    · exact ((S.ρ s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_eq.mpr ha.symm

theorem rho_mem_stabL (S : Setting G) {x : G} (hxQ : x ∈ S.QG) {c : G} (hc : c ∈ S.M)
    (hcx : c * x = x * c) :
    ((S.ρ ⟨c, hc⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ stabL S (S.cl x) := by
  have hconj : c * x * c⁻¹ = x := by
    rw [hcx]
    exact mul_inv_cancel_right x c
  exact ⟨⟨⟨c, hc⟩, rfl⟩, (S.ρ_cl ⟨c, hc⟩ hxQ).trans (congrArg S.cl hconj)⟩

theorem map_le_stabL (S : Setting G) {v : S.Qt} (H : Subgroup S.O) (hH : H ≤ S.Mbar)
    (hfix : ∀ h ∈ H, ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    H.map S.O.subtype ≤ stabL S v := by
  rintro _ ⟨h, hh, rfl⟩
  have hmem : h ∈ S.ρ.range := hH hh
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨⟨s, congrArg (fun k : S.O => ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hs⟩, hfix h hh⟩

theorem card_stabL_dvd (S : Setting G) (v : S.Qt) :
    Nat.card (stabL S v) ∣ Nat.card S.Mbar := by
  have hle : stabL S v ≤ S.Mbar.map S.O.subtype := by
    rintro g ⟨⟨s, hs⟩, -⟩
    have hρ : S.ρ s ∈ S.ρ.range := MonoidHom.mem_range.mpr ⟨s, rfl⟩
    exact ⟨S.ρ s, hρ, hs⟩
  calc Nat.card (stabL S v) ∣ Nat.card (S.Mbar.map S.O.subtype) :=
        Subgroup.card_dvd_of_le hle
    _ = Nat.card S.Mbar := Subgroup.card_map_of_injective S.O.subtype_injective

theorem stabL_isometry (S : Setting G) {v : S.Qt} {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ stabL S v) (u : S.Qt) : S.q (g u) = S.q u := by
  obtain ⟨⟨s, rfl⟩, -⟩ := hg
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ s).2 u

theorem exists_lift (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hx : S.cl x ≠ 0)
    {g : S.Qt ≃ₗ[ZMod 2] S.Qt} (hg : g ∈ stabL S (S.cl x)) :
    ∃ (c : G) (hc : c ∈ S.M), c * x = x * c ∧
      ((S.ρ ⟨c, hc⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = g := by
  have hg' : (∃ s : S.M, ((S.ρ s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = g) ∧ g (S.cl x) = S.cl x := hg
  obtain ⟨⟨s, hs⟩, hgv⟩ := hg'
  have hsxQ : (s : G) * x * (s : G)⁻¹ ∈ S.QG := S.conj_mem_QG s.2 hxQ
  have hcl : S.cl ((s : G) * x * (s : G)⁻¹) = S.cl x := by
    rw [← S.ρ_cl s hxQ, hs]
    exact hgv
  rcases (S.cl_eq_cl_iff hxQ hsxQ).mp hcl.symm with hcase | hcase
  · exact ⟨(s : G), s.2, (mul_inv_eq_iff_eq_mul).mp hcase, hs⟩
  · obtain ⟨y, hy⟩ := exists_polar_eq_one S.q_nondegenerate hx
    obtain ⟨t, htQ, rfl⟩ := S.exists_cl y
    have hxt : x * t ≠ t * x := (S.polar_cl_eq_one_iff hxQ htQ).mp hy
    have hzt : S.z * t = t * S.z := (S.z_comm_QG htQ).symm
    have hzx : S.z * x = x * S.z := (S.z_comm_QG hxQ).symm
    have hxzt : x * t * x⁻¹ * t⁻¹ = S.z := by
      rcases S.commutator_eq_one_or_z hxQ htQ with h1 | h1
      · exfalso
        apply hxt
        calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
          _ = t * x := by rw [h1, one_mul]
      · exact h1
    have hxt' : x * t = S.z * (t * x) := by
      calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
        _ = S.z * (t * x) := by rw [hxzt]
    have hconj_t : t⁻¹ * S.z * t = S.z := by
      calc t⁻¹ * S.z * t = t⁻¹ * (S.z * t) := by group
        _ = t⁻¹ * (t * S.z) := by rw [hzt]
        _ = S.z := by group
    have ht1 : t⁻¹ * x * t = S.z * x := by
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
        _ = t⁻¹ * (S.z * (t * x)) := by rw [hxt']
        _ = (t⁻¹ * S.z * t) * x := by group
        _ = S.z * x := by rw [hconj_t]
    have htM : t ∈ S.M := S.QG_le_M htQ
    have hcM : t⁻¹ * (s : G) ∈ S.M := S.M.mul_mem (S.M.inv_mem htM) s.2
    have hconj : t⁻¹ * (s : G) * x * (t⁻¹ * (s : G))⁻¹ = x := by
      calc t⁻¹ * (s : G) * x * (t⁻¹ * (s : G))⁻¹ = t⁻¹ * ((s : G) * x * (s : G)⁻¹) * t := by group
        _ = t⁻¹ * (x * S.z) * t := by rw [hcase]
        _ = t⁻¹ * x * (S.z * t) := by group
        _ = t⁻¹ * x * (t * S.z) := by rw [hzt]
        _ = (t⁻¹ * x * t) * S.z := by group
        _ = (S.z * x) * S.z := by rw [ht1]
        _ = x := by rw [hzx, mul_assoc, S.z_mul_z, mul_one]
    have hcx : t⁻¹ * (s : G) * x = x * (t⁻¹ * (s : G)) := (mul_inv_eq_iff_eq_mul).mp hconj
    have hinv : S.ρ ⟨t⁻¹, S.M.inv_mem htM⟩ = 1 := (S.ρ_eq_one_iff _).mpr (S.QG.inv_mem htQ)
    have hprod : (⟨t⁻¹ * (s : G), hcM⟩ : S.M) = (⟨t⁻¹, S.M.inv_mem htM⟩ : S.M) * s := rfl
    have hρ : S.ρ ⟨t⁻¹ * (s : G), hcM⟩ = S.ρ ⟨t⁻¹, S.M.inv_mem htM⟩ * S.ρ s := by
      rw [hprod, map_mul]
    refine ⟨t⁻¹ * (s : G), hcM, hcx, ?_⟩
    rw [hρ, hinv, one_mul]
    exact hs

theorem isGood_eichler (S : Setting G) {v : S.Qt} (hv : IsGood S v)
    {g : S.Qt ≃ₗ[ZMod 2] S.Qt} (hg : g ∈ stabL S v)
    (hgt : ∀ u, polar S.q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v}) : g = 1 := by
  obtain ⟨hv0, hqv, h2, H, hHM, hHfix, hirr⟩ := hv
  have hHS : H.map S.O.subtype ≤ stabL S v := map_le_stabL S H hHM hHfix
  refine eichler_eq_one S.q S.q_nondegenerate hv0 hqv (stabL S v)
    (fun g hg u => stabL_isometry S hg u) (fun g hg => hg.2) (H.map S.O.subtype) hHS ?_ ?_ hg hgt
  · intro U hvU hUk hH'
    exact hirr U hvU hUk (fun h hh => hH' _ (Subgroup.mem_map_of_mem S.O.subtype hh))
  · intro hdiv
    apply h2
    rw [S.finrank_Qt_eq_two_mul_width] at hdiv
    exact dvd_trans hdiv (card_stabL_dvd S v)

theorem isGood_irred (S : Setting G) {v : S.Qt} (hv : IsGood S v) (Y : Submodule (ZMod 2) S.Qt)
    (hvY : v ∈ Y) (hY : Y ≤ LinearMap.ker (QuadraticMap.polarBilin S.q v))
    (hinv : ∀ g ∈ stabL S v, ∀ y ∈ Y, g y ∈ Y) :
    Y = Submodule.span (ZMod 2) {v} ∨ Y = LinearMap.ker (QuadraticMap.polarBilin S.q v) := by
  obtain ⟨-, -, -, H, hHM, hHfix, hirr⟩ := hv
  have hHS : H.map S.O.subtype ≤ stabL S v := map_le_stabL S H hHM hHfix
  refine hirr Y hvY hY ?_
  intro h hh
  have hg : ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ stabL S v :=
    hHS (Subgroup.mem_map_of_mem S.O.subtype hh)
  have hgi : ((h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ stabL S v :=
    hHS (Subgroup.mem_map_of_mem S.O.subtype (H.inv_mem hh))
  have hmul : ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact hinv _ hg y hy
  · intro y hy
    refine Submodule.mem_map.mpr ⟨((h⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y, hinv _ hgi y hy, ?_⟩
    have key := congrArg (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => e y) hmul
    exact key

private lemma isGood_O2_mem_stabL (S : Setting G) {v : S.Qt} {g : S.Qt ≃ₗ[ZMod 2] S.Qt} :
    g ∈ stabL S v ↔ (∃ s : S.M, ((S.ρ s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = g) ∧ g v = v :=
  Iff.rfl

private def isGood_O2_sub {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Y L : Submodule (ZMod 2) V) (N : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Submodule (ZMod 2) V where
  carrier := {u | u ∈ Y ∧ ∀ n ∈ N, n u - u ∈ L}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.add_mem ha hb, fun n hn => ?_⟩
    have e : n (a + b) - (a + b) = (n a - a) + (n b - b) := by
      rw [map_add]
      abel
    rw [e]
    exact L.add_mem (ha' n hn) (hb' n hn)
  zero_mem' := by
    refine ⟨Y.zero_mem, fun n _ => ?_⟩
    rw [map_zero, sub_self]
    exact L.zero_mem
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨Y.smul_mem c hx, fun n hn => ?_⟩
    have e : n (c • x) - c • x = c • (n x - x) := by
      rw [map_smul, smul_sub]
    rw [e]
    exact L.smul_mem c (hx' n hn)

private lemma mem_isGood_O2_sub {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Y L : Submodule (ZMod 2) V) (N : Subgroup (V ≃ₗ[ZMod 2] V)) (u : V) :
    u ∈ isGood_O2_sub Y L N ↔ (u ∈ Y ∧ ∀ n ∈ N, n u - u ∈ L) :=
  Iff.rfl

private lemma isGood_O2_map_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Y : Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V)
    (h1 : ∀ y ∈ Y, g y ∈ Y) (h2 : ∀ y ∈ Y, g⁻¹ y ∈ Y) :
    Y.map (g : V →ₗ[ZMod 2] V) = Y := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact h1 y hy
  · intro y hy
    refine ⟨g⁻¹ y, h2 y hy, ?_⟩
    have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f y) (mul_inv_cancel g)
    exact h

theorem isGood_O2 (S : Setting G) {v : S.Qt} (hv : IsGood S v)
    (N : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt)) (hNS : N ≤ stabL S v)
    (hNn : ∀ s ∈ stabL S v, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hv0 : v ≠ 0 := hv.1
  have hqv : S.q v = 0 := hv.2.1
  have hw2 : 2 ≤ S.width := by
    by_contra hlt
    have hlt' := not_le.mp hlt
    apply hv.2.2.1
    have h0 : 2 * S.width - 2 = 0 := by omega
    rw [h0, pow_zero]
    exact one_dvd _
  haveI hfin : Finite S.Qt := Nat.finite_of_card_ne_zero (by rw [S.card_Qt]; positivity)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule (ZMod 2) S.Qt,
      Y = LinearMap.ker (QuadraticMap.polarBilin S.q v) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Submodule (ZMod 2) S.Qt,
      L = Submodule.span (ZMod 2) {v} := ⟨_, rfl⟩
  have hYmem : ∀ u, u ∈ Y ↔ QuadraticMap.polar S.q v u = 0 := by
    intro u
    rw [hYdef, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
  have hvY : v ∈ Y := by
    rw [hYmem, QuadraticMap.polar_self, hqv, smul_zero]
  have hLY : L ≤ Y := by
    rw [hLdef]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvY)
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one S.q_nondegenerate hv0
  have hdim : Module.finrank (ZMod 2) Y + 1 = 2 * S.width := by
    have h := finrank_ker_polarBilin (q := S.q) (v := v) (y := y₀) hy₀
    rw [S.finrank_Qt_eq_two_mul_width, ← hYdef] at h
    exact h
  have hLne : L ≠ Y := by
    intro h
    have h1 : Module.finrank (ZMod 2) L = 1 := by
      rw [hLdef]
      exact finrank_span_singleton hv0
    rw [h] at h1
    omega
  have hLlt : L < Y := lt_of_le_of_ne hLY hLne
  have hpol : ∀ s ∈ stabL S v, ∀ u,
      QuadraticMap.polar S.q v (s u) = QuadraticMap.polar S.q v u := by
    intro s hs u
    have hsv : s v = v := ((isGood_O2_mem_stabL S).mp hs).2
    have h := polar_map_isometry (stabL_isometry S hs) v u
    rw [hsv] at h
    exact h
  have hinvY : ∀ s ∈ stabL S v, ∀ y ∈ Y, s y ∈ Y := by
    intro s hs y hy
    refine (hYmem (s y)).mpr ?_
    rw [hpol s hs y]
    exact (hYmem y).mp hy
  have hLmap : ∀ s ∈ stabL S v, L.map (s : S.Qt →ₗ[ZMod 2] S.Qt) = L := by
    intro s hs
    have hsv : (s : S.Qt →ₗ[ZMod 2] S.Qt) v = v := ((isGood_O2_mem_stabL S).mp hs).2
    rw [hLdef, Submodule.map_span, Set.image_singleton, hsv]
  have hYN : ∀ g ∈ N, Y.map (g : S.Qt →ₗ[ZMod 2] S.Qt) = Y := fun g hg =>
    isGood_O2_map_eq Y g (hinvY g (hNS hg)) (hinvY g⁻¹ (inv_mem (hNS hg)))
  have hLN : ∀ g ∈ N, L.map (g : S.Qt →ₗ[ZMod 2] S.Qt) = L := fun g hg =>
    hLmap g (hNS hg)
  obtain ⟨w, hwY, hwL, hwN⟩ := exists_fixed_mod Y L hLlt N hN2 hYN hLN
  obtain ⟨Y₁, hY₁def⟩ : ∃ Y₁ : Submodule (ZMod 2) S.Qt, Y₁ = isGood_O2_sub Y L N :=
    ⟨_, rfl⟩
  have hY₁mem : ∀ u, u ∈ Y₁ ↔ (u ∈ Y ∧ ∀ n ∈ N, n u - u ∈ L) := fun u => by
    rw [hY₁def]
    exact mem_isGood_O2_sub Y L N u
  have hv1 : v ∈ Y₁ := by
    refine (hY₁mem v).mpr ⟨hvY, fun n hn => ?_⟩
    rw [((isGood_O2_mem_stabL S).mp (hNS hn)).2, sub_self]
    exact L.zero_mem
  have hY₁Y : Y₁ ≤ Y := by
    intro u hu
    exact ((hY₁mem u).mp hu).1
  have hinv1 : ∀ s ∈ stabL S v, ∀ y ∈ Y₁, s y ∈ Y₁ := by
    intro s hs y hy
    obtain ⟨hyY, hyN⟩ := (hY₁mem y).mp hy
    refine (hY₁mem (s y)).mpr ⟨hinvY s hs y hyY, fun n hn => ?_⟩
    have hm : s⁻¹ * n * s ∈ N := by
      have h := hNn s⁻¹ (inv_mem hs) n hn
      rwa [inv_inv] at h
    have h1 : (s⁻¹ * n * s) y - y ∈ L := hyN _ hm
    have hmul : s * (s⁻¹ * n * s) = n * s := by group
    have h4 : s ((s⁻¹ * n * s) y) = n (s y) := by
      have h := congrArg (fun f : S.Qt ≃ₗ[ZMod 2] S.Qt => f y) hmul
      exact h
    have h2 : s ((s⁻¹ * n * s) y - y) = n (s y) - s y := by
      rw [map_sub, h4]
    have h3 : s ((s⁻¹ * n * s) y - y) ∈ L.map (s : S.Qt →ₗ[ZMod 2] S.Qt) :=
      Submodule.mem_map_of_mem h1
    rw [hLmap s hs, h2] at h3
    exact h3
  have hY₁ker : Y₁ ≤ LinearMap.ker (QuadraticMap.polarBilin S.q v) := by
    rw [← hYdef]
    exact hY₁Y
  have hirr := isGood_irred S hv Y₁ hv1 hY₁ker hinv1
  rw [← hLdef, ← hYdef] at hirr
  rcases hirr with hL | hY'
  · exfalso
    have hwY₁ : w ∈ Y₁ := (hY₁mem w).mpr ⟨hwY, hwN⟩
    rw [hL] at hwY₁
    exact hwL hwY₁
  · have hall : ∀ u ∈ Y, ∀ n ∈ N, n u - u ∈ L := by
      intro u hu n hn
      have hu' : u ∈ Y₁ := by
        rw [hY']
        exact hu
      exact ((hY₁mem u).mp hu').2 n hn
    have hone : ∀ n ∈ N, n = 1 := by
      intro n hn
      apply isGood_eichler S hv (hNS hn)
      intro u hu
      have huY : u ∈ Y := (hYmem u).mpr ((QuadraticMap.polar_comm S.q v u).trans hu)
      rw [← hLdef]
      exact hall u huY n hn
    rw [Subgroup.eq_bot_iff_forall]
    exact hone

theorem isGood_basic (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x)) :
    orderOf x = 2 ∧ x * S.z = S.z * x ∧ S.z ∉ zpowers x := by
  obtain ⟨hne, hq, -, -⟩ := hgood
  have hx2 : x ^ 2 = 1 := (S.q_cl_eq_zero_iff hxQ).mp hq
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hne S.cl_one
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  refine ⟨orderOf_eq_prime hx2 hx1, S.z_comm_QG hxQ, ?_⟩
  intro hz
  rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hxx).mp hz with h | h
  · exact S.z_ne_one h
  · exact hne (by rw [← h]; exact S.cl_z)

theorem two_le_width_of_isGood (S : Setting G) {v : S.Qt} (hv : IsGood S v) :
    2 ≤ S.width := by
  obtain ⟨-, -, hnd, -⟩ := hv
  by_contra hlt
  have h0 : 2 * S.width - 2 = 0 := by omega
  apply hnd
  rw [h0, pow_zero]
  exact one_dvd _

theorem Qx_eq_clPre (S : Setting G) {x : G} (hxQ : x ∈ S.QG) :
    S.QG ⊓ centralizer ({x} : Set G) =
      S.clPre (LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x))) := by
  ext y
  rw [Subgroup.mem_inf, S.mem_clPre, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hyQ, hyc⟩
    exact ⟨hyQ, (S.polar_cl_eq_zero_iff hxQ hyQ).mpr hyc.symm⟩
  · rintro ⟨hyQ, hpol⟩
    exact ⟨hyQ, ((S.polar_cl_eq_zero_iff hxQ hyQ).mp hpol).symm⟩

theorem card_Qx (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hx : S.cl x ≠ 0) :
    Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) = 2 ^ (2 * S.width) := by
  haveI : Finite S.Qt := Nat.finite_of_card_ne_zero (by rw [S.card_Qt]; positivity)
  obtain ⟨y, hy⟩ := exists_polar_eq_one S.q_nondegenerate hx
  have h1 := finrank_ker_polarBilin hy
  rw [S.finrank_Qt_eq_two_mul_width] at h1
  rw [Qx_eq_clPre S hxQ, S.card_clPre, S.card_submodule, ← h1]
  ring

theorem exists_comm_pair_Qx (S : Setting G) {x : G} (hxQ : x ∈ S.QG)
    (hgood : IsGood S (S.cl x)) :
    S.z ∈ ⁅(S.QG ⊓ centralizer ({x} : Set G) : Subgroup G),
      (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G)⁆ := by
  haveI : Finite S.Qt := Nat.finite_of_card_ne_zero (by rw [S.card_Qt]; positivity)
  have hw2 : 2 ≤ S.width := two_le_width_of_isGood S hgood
  have hx0 : S.cl x ≠ 0 := by
    obtain ⟨h0, -⟩ := hgood
    exact h0
  have hz2 : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
  have hstep1 : ∃ a ∈ LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)),
      ∃ b ∈ LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)), polar S.q a b = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy⟩ := exists_polar_eq_one S.q_nondegenerate hx0
    have h1 := finrank_ker_polarBilin hy
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    have hle : LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)) ≤
        LinearMap.BilinForm.orthogonal S.q.polarBilin
          (LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x))) := by
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b hb
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hz2 _ (hcon b hb a ha)
    have h2 := Submodule.finrank_mono hle
    have h3 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate
      (LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)))
    rw [S.finrank_Qt_eq_two_mul_width] at h3
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := hstep1
  obtain ⟨u, hu, rfl⟩ := S.exists_cl a
  obtain ⟨w, hw, rfl⟩ := S.exists_cl b
  have hu' : u ∈ (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [Qx_eq_clPre S hxQ]
    exact S.mem_clPre.mpr ⟨hu, ha⟩
  have hw' : w ∈ (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [Qx_eq_clPre S hxQ]
    exact S.mem_clPre.mpr ⟨hw, hb⟩
  have hne : u * w ≠ w * u := (S.polar_cl_eq_one_iff hu hw).mp hab
  rcases S.commutator_eq_one_or_z hu hw with h | h
  · exfalso
    apply hne
    calc u * w = u * w * u⁻¹ * w⁻¹ * (w * u) := by group
      _ = w * u := by rw [h, one_mul]
  · have hmem := Subgroup.commutator_mem_commutator hu' hw'
    rw [commutatorElement_def, h] at hmem
    exact hmem

theorem hnorm_Qx (S : Setting G) {x : G} (hxQ : x ∈ S.QG) :
    centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) ≤
      normalizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ c ∈ centralizer ({x} : Set G), c ∈ centralizer ({S.z} : Set G) →
      ∀ h ∈ S.QG ⊓ centralizer ({x} : Set G),
        c * h * c⁻¹ ∈ S.QG ⊓ centralizer ({x} : Set G) := by
    intro c hcx hcz h hh
    rw [Subgroup.mem_inf] at hh ⊢
    exact ⟨S.conj_mem_QG hcz hh.1,
      (centralizer ({x} : Set G)).mul_mem
        ((centralizer ({x} : Set G)).mul_mem hcx hh.2)
        ((centralizer ({x} : Set G)).inv_mem hcx)⟩
  intro c hc
  rw [Subgroup.mem_inf] at hc
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe]
  constructor
  · exact key c hc.1 hc.2 h
  · intro hh
    have h' := key c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc.1)
      ((centralizer ({S.z} : Set G)).inv_mem hc.2) _ hh
    have e : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
    rwa [e] at h'

private theorem s5c_conj_identity {H : Type*} [Group H] {c q x : H} (hcx : c * x = x * c)
    (hxx : x * x = 1) (hn : q⁻¹ * c⁻¹ * q * c = 1 ∨ q⁻¹ * c⁻¹ * q * c = x) :
    c * q * c⁻¹ = q * (q⁻¹ * c⁻¹ * q * c) := by
  have hdef : c⁻¹ * q * c = q * (q⁻¹ * c⁻¹ * q * c) := by group
  rcases hn with h | h
  · have h1 : c⁻¹ * q * c = q := by rw [hdef, h, mul_one]
    have h2 : q * c = c * q := by
      calc q * c = c * (c⁻¹ * q * c) := by group
        _ = c * q := by rw [h1]
    rw [h, mul_one]
    calc c * q * c⁻¹ = q * c * c⁻¹ := by rw [h2]
      _ = q := by group
  · have h1 : c⁻¹ * q * c = q * x := by rw [hdef, h]
    have h2 : q * c = c * q * x := by
      calc q * c = c * (c⁻¹ * q * c) := by group
        _ = c * (q * x) := by rw [h1]
        _ = c * q * x := by group
    have h3 : c * q = q * x * c := by
      calc c * q = c * q * (x * x) := by rw [hxx, mul_one]
        _ = c * q * x * x := by group
        _ = q * c * x := by rw [← h2]
        _ = q * (c * x) := by group
        _ = q * (x * c) := by rw [hcx]
        _ = q * x * c := by group
    rw [h]
    calc c * q * c⁻¹ = q * x * c * c⁻¹ := by rw [h3]
      _ = q * x := by group

private theorem s5c_gt_step (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hxx : x * x = 1)
    {c : G} (hcM : c ∈ S.M) (hcx : c * x = x * c)
    (hc : ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), q⁻¹ * c⁻¹ * q * c ∈ zpowers x)
    {q : G} (hq : q ∈ S.QG) (hqx : q * x = x * q) :
    ((S.ρ ⟨c, hcM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) - S.cl q ∈
      Submodule.span (ZMod 2) {S.cl x} := by
  have hqC : q ∈ S.QG ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqx⟩
  have hn1 := (Setting.mem_zpowers_iff_of_mul_self hxx).mp (hc q hqC)
  have hnQG : q⁻¹ * c⁻¹ * q * c ∈ S.QG := by
    rcases hn1 with h | h
    · rw [h]
      exact S.QG.one_mem
    · rw [h]
      exact hxQ
  have hgq : ((S.ρ ⟨c, hcM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl (c * q * c⁻¹) :=
    S.ρ_cl ⟨c, hcM⟩ hq
  rw [hgq, s5c_conj_identity hcx hxx hn1, S.cl_mul hq hnQG, add_sub_cancel_left]
  rcases hn1 with h | h
  · rw [h, S.cl_one]
    exact Submodule.zero_mem _
  · rw [h]
    exact Submodule.mem_span_singleton_self _

theorem hb_of_isGood (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x))
    {c : G} (hcx : c * x = x * c) (hcz : c * S.z = S.z * c)
    (hc : ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), q⁻¹ * c⁻¹ * q * c ∈ zpowers x) :
    c ∈ closure ({x, S.z} : Set G) := by
  obtain ⟨hxord, hxz, hzx⟩ := isGood_basic S hxQ hgood
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hxord] at h
    rw [← pow_two]
    exact h
  have hcM : c ∈ S.M := S.mem_M_iff.mpr hcz
  have hg : ((S.ρ ⟨c, hcM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ stabL S (S.cl x) :=
    rho_mem_stabL S hxQ hcM hcx
  have hgt : ∀ u, polar S.q u (S.cl x) = 0 →
      ((S.ρ ⟨c, hcM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈
        Submodule.span (ZMod 2) {S.cl x} := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := S.exists_cl u
    exact s5c_gt_step S hxQ hxx hcM hcx hc hq ((S.polar_cl_eq_zero_iff hq hxQ).mp hu)
  have hg1 := isGood_eichler S hgood hg hgt
  have hcQG : c ∈ S.QG := (S.ρ_eq_one_iff ⟨c, hcM⟩).mp (Subtype.ext hg1)
  have hcomm : ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), q * c = c * q := by
    intro q hqC
    have hqQ : q ∈ S.QG := (Subgroup.mem_inf.mp hqC).1
    have hcomm1 := S.commutator_eq_one_or_z (S.QG.inv_mem hqQ) (S.QG.inv_mem hcQG)
    rw [inv_inv, inv_inv] at hcomm1
    have hn1 : q⁻¹ * c⁻¹ * q * c = 1 := by
      rcases hcomm1 with h2 | h2
      · exact h2
      · rcases (Setting.mem_zpowers_iff_of_mul_self hxx).mp (hc q hqC) with h3 | h3
        · exact h3
        · have hzx' : S.z = x := h2.symm.trans h3
          have hzmem : S.z ∈ zpowers x := by
            rw [hzx']
            exact mem_zpowers x
          exact absurd hzmem hzx
    have h1 : c⁻¹ * q * c = q := by
      calc c⁻¹ * q * c = q * (q⁻¹ * c⁻¹ * q * c) := by group
        _ = q := by rw [hn1, mul_one]
    calc q * c = c * (c⁻¹ * q * c) := by group
      _ = c * q := by rw [h1]
  have hcmem : S.cl c ∈ Submodule.span (ZMod 2) {S.cl x} := by
    have hKN : LinearMap.ker (S.q.polarBilin (S.cl x)) =
        LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {S.cl x}) := by
      ext m
      rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
      constructor
      · intro hm n hn
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
        rw [map_smul, LinearMap.smul_apply, hm, smul_zero]
      · intro hm
        exact hm _ (Submodule.mem_span_singleton_self _)
    have hdbl : LinearMap.BilinForm.orthogonal S.q.polarBilin
        (LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {S.cl x})) =
          Submodule.span (ZMod 2) {S.cl x} :=
      LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _
    have h1 : S.cl c ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
        (LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {S.cl x})) := by
      rw [← hKN, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [LinearMap.mem_ker] at hn
      obtain ⟨q', hq', rfl⟩ := S.exists_cl n
      rw [QuadraticMap.polarBilin_apply_apply] at hn ⊢
      have hxq' : x * q' = q' * x := (S.polar_cl_eq_zero_iff hxQ hq').mp hn
      have hq'C : q' ∈ S.QG ⊓ centralizer ({x} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hq', mem_centralizer_singleton_iff.mpr hxq'.symm⟩
      exact (S.polar_cl_eq_zero_iff hq' hcQG).mpr (hcomm q' hq'C)
    rwa [hdbl] at h1
  have hcases : c = 1 ∨ c = x ∨ c = S.z ∨ c = x * S.z := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hcmem
    have hZ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hZ a with rfl | rfl
    · rw [zero_smul] at ha
      rcases (S.cl_eq_zero_iff hcQG).mp ha.symm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · rw [one_smul] at ha
      rcases (S.cl_eq_cl_iff hxQ hcQG).mp ha with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  exact (mem_closure_pair_iff hxx S.z_mul_z hxz).mpr hcases

private theorem he_isGood_stab_le (S : Setting G) {x : G} (hxQ : x ∈ S.QG)
    (P : Subgroup G)
    (hPC : P ≤ centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G)) :
    (P.subgroupOf S.M).map (S.O.subtype.comp S.ρ) ≤ stabL S (S.cl x) := by
  rintro _ ⟨c, hc, rfl⟩
  have hcx : (c : G) * x = x * (c : G) :=
    mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPC (Subgroup.mem_subgroupOf.mp hc))).1
  exact rho_mem_stabL S hxQ c.2 hcx

private theorem he_isGood_conj (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x))
    (P : Subgroup G)
    (hPC : P ≤ centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G))
    (hn : centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) ≤ normalizer (P : Set G)) :
    ∀ s ∈ stabL S (S.cl x), ∀ n ∈ (P.subgroupOf S.M).map (S.O.subtype.comp S.ρ),
      s * n * s⁻¹ ∈ (P.subgroupOf S.M).map (S.O.subtype.comp S.ρ) := by
  intro s hs n hn'
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hn'
  obtain ⟨c, hc, hcx, rfl⟩ := exists_lift S hxQ hgood.1 hs
  have hcC : c ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hcx
  have hcN : c ∈ normalizer (P : Set G) := hn (Subgroup.mem_inf.mpr ⟨hcC, hc⟩)
  have hconj : c * (p : G) * c⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hcN (p : G)).mp (Subgroup.mem_subgroupOf.mp hp)
  refine Subgroup.mem_map.mpr ⟨(⟨c, hc⟩ : S.M) * p * (⟨c, hc⟩ : S.M)⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr hconj
  · rw [map_mul, map_mul, map_inv]
    rfl

private theorem he_isGood_pgroup (S : Setting G) (P : Subgroup G) (hP2 : IsPGroup 2 P) :
    IsPGroup 2 ((P.subgroupOf S.M).map (S.O.subtype.comp S.ρ)) :=
  (IsPGroup.comap_subtype (K := S.M) hP2).map (S.O.subtype.comp S.ρ)

theorem he_of_isGood (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x))
    (P : Subgroup G) (hP2 : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G))
    (hn : centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) ≤ normalizer (P : Set G)) :
    P ≤ S.QG ⊓ centralizer ({x} : Set G) := by
  intro g hg
  have hgC := hPC hg
  have hgx : g ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hgC).1
  have hgM : g ∈ S.M := (Subgroup.mem_inf.mp hgC).2
  have hbot : (P.subgroupOf S.M).map (S.O.subtype.comp S.ρ) = ⊥ :=
    isGood_O2 S hgood ((P.subgroupOf S.M).map (S.O.subtype.comp S.ρ))
      (he_isGood_stab_le S hxQ P hPC) (he_isGood_conj S hxQ hgood P hPC hn)
      (he_isGood_pgroup S P hP2)
  have hmem : (S.O.subtype.comp S.ρ) ⟨g, hgM⟩ ∈ (P.subgroupOf S.M).map (S.O.subtype.comp S.ρ) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hρ : S.ρ ⟨g, hgM⟩ = 1 := Subtype.ext hmem
  exact Subgroup.mem_inf.mpr ⟨(S.ρ_eq_one_iff ⟨g, hgM⟩).mp hρ, hgx⟩

theorem hc_of_isGood (S : Setting G) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x))
    (P : Subgroup G) (hPQ : P ≤ S.QG ⊓ centralizer ({x} : Set G))
    (hn : centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) ≤ normalizer (P : Set G)) :
    P ≤ closure ({x, S.z} : Set G) ∨
      P ⊔ closure ({x, S.z} : Set G) = S.QG ⊓ centralizer ({x} : Set G) := by
  obtain ⟨hord, hxz, -⟩ := isGood_basic S hxQ hgood
  have hxx : x * x = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hzz : S.z * S.z = 1 := S.z_mul_z
  have hxT : x ∈ closure ({x, S.z} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hzT : S.z ∈ closure ({x, S.z} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hxne : S.cl x ≠ 0 := hgood.1
  have hPQ' : ∀ p ∈ P, p ∈ S.QG := fun p hp => (Subgroup.mem_inf.mp (hPQ hp)).1
  have hPC : ∀ p ∈ P, p * x = x * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPQ hp)).2
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule (ZMod 2) S.Qt,
      Y = Submodule.span (ZMod 2) {S.cl x} ⊔ S.clSub P := ⟨_, rfl⟩
  have hvY : S.cl x ∈ Y := by
    rw [hYdef]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hYK : Y ≤ LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)) := by
    rw [hYdef]
    refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker,
        QuadraticMap.polarBilin_apply_apply]
      exact CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero S.q (S.cl x)
    · intro w hw
      obtain ⟨p, hpP, hpQ, rfl⟩ := S.mem_clSub_iff.mp hw
      rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
      exact (S.polar_cl_eq_zero_iff hxQ hpQ).mpr (hPC p hpP).symm
  have hinv : ∀ g ∈ stabL S (S.cl x), ∀ y ∈ Y, g y ∈ Y := by
    intro g hg y hy
    obtain ⟨c, hc, hcx, rfl⟩ := exists_lift S hxQ hxne hg
    have hgv : ((S.ρ ⟨c, hc⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x := hg.2
    have hcN : c ∈ normalizer (P : Set G) :=
      hn (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcx,
        Subgroup.mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp hc)⟩)
    have hcP : ∀ p ∈ P, c * p * c⁻¹ ∈ P := fun p hp =>
      (Subgroup.mem_normalizer_iff.mp hcN p).mp hp
    rw [hYdef] at hy ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    refine add_mem ?_ ?_
    · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [map_smul, hgv]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _))
    · obtain ⟨p, hpP, hpQ, rfl⟩ := S.mem_clSub_iff.mp hb
      have h1 : ((S.ρ ⟨c, hc⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl p) = S.cl (c * p * c⁻¹) :=
        S.ρ_cl ⟨c, hc⟩ hpQ
      rw [h1]
      exact Submodule.mem_sup_right
        (S.cl_mem_clSub (hcP p hpP) (S.conj_mem_QG hc hpQ))
  rcases isGood_irred S hgood Y hvY hYK hinv with hYL | hYKe
  · left
    intro p hp
    have hpQ : p ∈ S.QG := hPQ' p hp
    have hcl : S.cl p ∈ Y := by
      rw [hYdef]
      exact Submodule.mem_sup_right (S.cl_mem_clSub hp hpQ)
    rw [hYL] at hcl
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hcl
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with rfl | rfl
    · rw [zero_smul] at ha
      rcases (S.cl_eq_zero_iff hpQ).mp ha.symm with h | h
      · exact (mem_closure_pair_iff hxx hzz hxz).mpr (Or.inl h)
      · exact (mem_closure_pair_iff hxx hzz hxz).mpr (Or.inr (Or.inr (Or.inl h)))
    · rw [one_smul] at ha
      rcases (S.cl_eq_cl_iff hxQ hpQ).mp ha with h | h
      · exact (mem_closure_pair_iff hxx hzz hxz).mpr (Or.inr (Or.inl h))
      · exact (mem_closure_pair_iff hxx hzz hxz).mpr (Or.inr (Or.inr (Or.inr h)))
  · right
    apply le_antisymm
    · have hxQx : x ∈ S.QG ⊓ centralizer ({x} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have hzQx : S.z ∈ S.QG ⊓ centralizer ({x} : Set G) :=
        Subgroup.mem_inf.mpr ⟨S.z_mem_QG, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
      exact sup_le hPQ ((Subgroup.closure_le _).mpr
        (Set.insert_subset_iff.mpr ⟨hxQx, Set.singleton_subset_iff.mpr hzQx⟩))
    · intro q hq
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
      have hqx : x * q = q * x := (Subgroup.mem_centralizer_singleton_iff.mp hqC).symm
      have hmemK : S.cl q ∈ LinearMap.ker (QuadraticMap.polarBilin S.q (S.cl x)) := by
        rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
        exact (S.polar_cl_eq_zero_iff hxQ hqQ).mpr hqx
      rw [← hYKe, hYdef] at hmemK
      obtain ⟨a', ha', b, hb, hab⟩ := Submodule.mem_sup.mp hmemK
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ha'
      obtain ⟨p, hpP, hpQ, rfl⟩ := S.mem_clSub_iff.mp hb
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with rfl | rfl
      · rw [zero_smul, zero_add] at hab
        rcases (S.cl_eq_cl_iff hpQ hqQ).mp hab with h | h
        · rw [h]
          exact Subgroup.mem_sup_left hpP
        · rw [h]
          exact mul_mem (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right hzT)
      · rw [one_smul, ← S.cl_mul hxQ hpQ] at hab
        rcases (S.cl_eq_cl_iff (S.QG.mul_mem hxQ hpQ) hqQ).mp hab with h | h
        · rw [h]
          exact mul_mem (Subgroup.mem_sup_right hxT) (Subgroup.mem_sup_left hpP)
        · rw [h]
          exact mul_mem (mul_mem (Subgroup.mem_sup_right hxT) (Subgroup.mem_sup_left hpP))
            (Subgroup.mem_sup_right hzT)

theorem pCoreOf_facts (K : Subgroup G) :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 K) ∧ CFSG.Open.pCoreOf 2 K ≤ K ∧
      ∀ k ∈ K, ∀ r ∈ CFSG.Open.pCoreOf 2 K, k * r * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CFSG.Open.pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  · rw [CFSG.Open.pCoreOf]
    exact Subgroup.map_subtype_le _
  · intro k hk r hr
    rw [CFSG.Open.pCoreOf] at hr ⊢
    obtain ⟨o', ho', rfl⟩ := hr
    exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

private theorem zpow_eq_one_or_self_S5f {x : G} (hx2 : orderOf x = 2) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have h2 : ((orderOf x : ℕ) : ℤ) = 2 := by exact_mod_cast hx2
  have h := zpow_mod_orderOf x k
  rw [h2] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h, h0, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

private theorem normalizer_zpowers_eq_centralizer_S5f {x : G} (hx2 : orderOf x = 2) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  ext g
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.mp h x).mp (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rcases zpow_eq_one_or_self_S5f hx2 k with h2 | h2
    · exfalso
      have hk' : g * x * g⁻¹ = 1 := by
        rw [h2] at hk
        exact hk.symm
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hk']
        _ = 1 := by group
    · have hk' : g * x * g⁻¹ = x := by
        rw [h2] at hk
        exact hk.symm
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [hk']
  · intro h
    have hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute x g := (Subgroup.mem_centralizer_singleton_iff.mp h).symm
      exact (hcomm.zpow_left k).eq
    exact (Subgroup.centralizer_le_normalizer _) hg

theorem hCR_of_charTwo (hchar : CFSG.Open.IsCharTwoType G) {x : G} (hx2 : orderOf x = 2) :
    ∀ y ∈ centralizer ({x} : Set G),
      (∀ r ∈ CFSG.Open.pCoreOf 2 (centralizer ({x} : Set G)), y * r = r * y) →
      y ∈ CFSG.Open.pCoreOf 2 (centralizer ({x} : Set G)) := by
  intro y hy hcomm
  have hloc : CFSG.Open.IsTwoLocal (centralizer ({x} : Set G)) := by
    unfold CFSG.Open.IsTwoLocal
    refine ⟨Subgroup.zpowers x, ?_, ?_, ?_⟩
    · intro hbot
      rw [Subgroup.zpowers_eq_bot] at hbot
      rw [hbot, orderOf_one] at hx2
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
    · exact (normalizer_zpowers_eq_centralizer_S5f hx2).symm
  have hcent : y ∈ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcomm h hh).symm
  exact hchar (centralizer ({x} : Set G)) hloc (Subgroup.mem_inf.mpr ⟨hy, hcent⟩)

theorem conj_z_of_isGood (S : Setting G) (hchar : CFSG.Open.IsCharTwoType G)
    (hw : 9 ≤ S.width) {x : G} (hxQ : x ∈ S.QG) (hgood : IsGood S (S.cl x)) :
    ∀ h ∈ centralizer ({x} : Set G), h * S.z * h⁻¹ = S.z ∨ h * S.z * h⁻¹ = S.z * x := by
  obtain ⟨hx2, hxz, hzx⟩ := isGood_basic S hxQ hgood
  have hx0 : S.cl x ≠ 0 := hgood.1
  obtain ⟨hR2, hRx, hRn⟩ := pCoreOf_facts (centralizer ({x} : Set G))
  have hCR := hCR_of_charTwo hchar hx2
  have hQG : IsPGroup 2 S.QG := S.extraspecial.1.map S.M.subtype
  have hxQx : x ∈ S.QG ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzQx : S.z ∈ S.QG ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨S.z_mem_QG, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hQxC : S.QG ⊓ centralizer ({x} : Set G) ≤
      centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) := by
    intro g hg
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).2, S.QG_le_M (Subgroup.mem_inf.mp hg).1⟩
  have hd : 2 ^ 17 ≤ Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [card_Qx S hxQ hx0]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : ∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G),
      (∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), q⁻¹ * c⁻¹ * q * c ∈ zpowers x) →
        c ∈ closure ({x, S.z} : Set G) := fun c hc hcond =>
    hb_of_isGood S hxQ hgood
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1)
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2) hcond
  exact central_lemma_R (CFSG.Open.pCoreOf 2 (centralizer ({x} : Set G))) hR2 hRx hRn hCR
    hx2 S.orderOf_z hxz hzx (S.QG ⊓ centralizer ({x} : Set G)) (hQG.to_le inf_le_left) hQxC
    hxQx hzQx (hnorm_Qx S hxQ) (exists_comm_pair_Qx S hxQ hgood) hb
    (hc_of_isGood S hxQ hgood) hd (he_of_isGood S hxQ hgood)

theorem exists_escape (S : Setting G) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {x : G} (hx : x ∈ S.QG ⊓ S.Qa g)
    (hxa : S.cl x ≠ 0 ∧ S.cl x ≠ S.cl (g * S.z * g⁻¹)) :
    ∃ w ∈ centralizer ({x} : Set G), w * S.z * w⁻¹ ≠ S.z ∧ w * S.z * w⁻¹ ≠ S.z * x := by
  obtain ⟨hxQ, hxQt⟩ := Subgroup.mem_inf.mp hx
  have htt : g * S.z * g⁻¹ * (g * S.z * g⁻¹) = 1 := by
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
    group
  have htz : g * S.z * g⁻¹ * S.z = S.z * (g * S.z * g⁻¹) := S.z_comm_QG haQ
  have he : x ∉ closure ({g * S.z * g⁻¹, S.z} : Set G) := by
    intro hxc
    rcases (CFSG.GF2Type.Widths1112.mem_closure_pair_iff htt S.z_mul_z htz).mp hxc with
      h | h | h | h
    · exact hxa.1 (by rw [h, S.cl_one])
    · exact hxa.2 (by rw [h])
    · exact hxa.1 (by rw [h, S.cl_z])
    · exact hxa.2 (by rw [h, S.cl_mul_z haQ])
  obtain ⟨u, hu, hu1, -⟩ := (S.lemma_3_8_2 (g := g) (t := g * S.z * g⁻¹) (e := x) rfl haQ hne
    hxQ hxQt he) (g * S.z * g⁻¹) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) S.z
    (Set.mem_insert _ _) hne
  refine ⟨u, (Subgroup.mem_inf.mp hu).2, ?_, ?_⟩
  · rw [hu1]
    exact hne
  · rw [hu1]
    intro h
    apply he
    have hx' : x = S.z * (g * S.z * g⁻¹) := by
      rw [h, ← mul_assoc, S.z_mul_z, one_mul]
    rw [hx']
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem exists_good_mem_inf (S : Setting G) (hF3 : GoodThroughSingular S)
    (h2 : (Nat.card S.Mbar).factorization 2 + 3 ≤ 2 * S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ x ∈ S.QG ⊓ S.Qa g, IsGood S (S.cl x) ∧ S.cl x ≠ S.cl (g * S.z * g⁻¹) := by
  have hX : S.QG ⊓ S.Qa g ≤ S.QG := inf_le_left
  have haX : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa g := ⟨haQ, (S.conjBy g).z_mem_QG⟩
  have hzX : S.z ∈ S.QG ⊓ S.Qa g :=
    ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG (g := g) rfl haQ hne⟩
  have hv0 : S.cl (g * S.z * g⁻¹) ≠ 0 := by
    intro h
    rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
    · exact (S.conjBy g).z_ne_one h1
    · exact hne h1
  have hqv : S.q (S.cl (g * S.z * g⁻¹)) = 0 := by
    rw [S.q_cl_eq_zero_iff haQ, pow_two]
    exact (S.conjBy g).z_mul_z
  have hvU : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := S.cl_mem_clSub haX haQ
  have hTS : ∀ u ∈ S.clSub (S.QG ⊓ S.Qa g), S.q u = 0 := by
    intro u hu
    obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
    rw [S.q_cl_eq_zero_iff hxQ]
    exact S.QG_inf_Qa_sq hne hxX
  have hcardX : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) =
      2 * Nat.card (S.clSub (S.QG ⊓ S.Qa g)) := by
    have h := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
    rwa [S.clPre_clSub hX hzX] at h
  have hLX : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) =
      2 ^ (2 * S.width) := by
    rw [S.card_Lbar_mul g, S.card_L0 haQ hne]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.card (S.Lbar g) = 2 ^ j := by
    haveI := S.isElementaryAbelian_Lbar haQ
    exact (IsPGroup.iff_card).mp (CFSG.IsElementaryAbelian.isPGroup 2 ↥(S.Lbar g))
  haveI : Finite S.Mbar := Finite.of_surjective _ S.ρ.rangeRestrict_surjective
  have hMpos : Nat.card S.Mbar ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ j ∣ Nat.card S.Mbar := by
    rw [← hj]
    exact Subgroup.card_dvd_of_le (S.Lbar_le_Mbar g)
  have hjle : j ≤ (Nat.card S.Mbar).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hMpos).mp hdvd
  have hfin : 2 ≤ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := by
    have hU := S.card_submodule (S.clSub (S.QG ⊓ S.Qa g))
    have h3 : (2 : ℕ) ^ (j + 1 + Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))) =
        2 ^ (2 * S.width) := by
      rw [← hLX, hj, hcardX, hU]
      ring
    have h4 := Nat.pow_right_injective le_rfl h3
    omega
  have hle : ∀ m ∈ S.Mbar,
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) →
      (S.clSub (S.QG ⊓ S.Qa g)).map
        (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ≤
        S.clSub (S.QG ⊓ S.Qa g) := by
    intro m hm hfix
    have hm' : m ∈ S.ρ.range := hm
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hm'
    have hstab : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ stabL S (S.cl (g * S.z * g⁻¹)) := by
      show (∃ s' : S.M, ((S.ρ s' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
          ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧
        ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)
      exact ⟨⟨s, congrArg (fun k : S.O => (k : S.Qt ≃ₗ[ZMod 2] S.Qt)) hs⟩, hfix⟩
    obtain ⟨c, hc, hca, hρc⟩ := exists_lift S haQ hv0 hstab
    have hcT : c ∈ (S.conjBy g).M := (S.conjBy g).mem_M_iff.mpr hca
    have hcX : ∀ y ∈ S.QG ⊓ S.Qa g, c * y * c⁻¹ ∈ S.QG ⊓ S.Qa g := fun y hy =>
      ⟨S.conj_mem_QG hc hy.1, (S.conjBy g).conj_mem_QG hcT hy.2⟩
    have hact : ∀ y ∈ S.QG, ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) =
        S.cl (c * y * c⁻¹) := fun y hy =>
      (LinearEquiv.congr_fun hρc (S.cl y)).symm.trans (S.ρ_cl ⟨c, hc⟩ hy)
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, hyX, hyQ, rfl⟩ := S.mem_clSub_iff.mp hu
    show ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) ∈ S.clSub (S.QG ⊓ S.Qa g)
    rw [hact y hyQ]
    exact S.cl_mem_clSub (hcX y hyX) (S.conj_mem_QG hc hyQ)
  have key2 : ∀ (m : S.O) (u : S.Qt),
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u ∧
        ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u :=
    fun m u => ⟨((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).apply_symm_apply u,
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_apply u⟩
  have hinv : ∀ m ∈ S.Mbar,
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) →
      (S.clSub (S.QG ⊓ S.Qa g)).map
        (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        S.clSub (S.QG ⊓ S.Qa g) := by
    intro m hm hfix
    refine le_antisymm (hle m hm hfix) ?_
    intro u hu
    have hminvMem : m⁻¹ ∈ S.Mbar := S.Mbar.inv_mem hm
    have hfix' : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      have h := (key2 m (S.cl (g * S.z * g⁻¹))).2
      rw [hfix] at h
      exact h
    have hy : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ S.clSub (S.QG ⊓ S.Qa g) :=
      hle m⁻¹ hminvMem hfix' (Submodule.mem_map_of_mem hu)
    exact Submodule.mem_map.mpr ⟨_, hy, (key2 m u).1⟩
  obtain ⟨u, huU, huv, hgood⟩ :=
    hF3 (S.cl (g * S.z * g⁻¹)) hv0 hqv (S.clSub (S.QG ⊓ S.Qa g)) hvU hfin hTS hinv
  obtain ⟨x, hxX, -, rfl⟩ := S.mem_clSub_iff.mp huU
  exact ⟨x, hxX, hgood, huv⟩

theorem false_of_goodThroughSingular (S : Setting G) (hchar : CFSG.Open.IsCharTwoType G)
    (hw : 9 ≤ S.width) (hF3 : GoodThroughSingular S)
    (h2 : (Nat.card S.Mbar).factorization 2 + 3 ≤ 2 * S.width)
    (hnwc : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) : False := by
  obtain ⟨g, haQ, hne⟩ := hnwc
  obtain ⟨x, hx, hgood, hxa⟩ := exists_good_mem_inf S hF3 h2 haQ hne
  have hx0 : S.cl x ≠ 0 := hgood.1
  obtain ⟨w, hw', hw1, hw2⟩ := exists_escape S haQ hne hx ⟨hx0, hxa⟩
  rcases conj_z_of_isGood S hchar hw (Subgroup.mem_inf.mp hx).1 hgood w hw' with h | h
  · exact hw1 h
  · exact hw2 h

end CFSG.GF2Type.Widths1112
