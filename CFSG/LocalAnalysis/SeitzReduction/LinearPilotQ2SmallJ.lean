module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8Kinds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFusion

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift centralizerPerfectCore)

section Generic

variable {G : Type*} [Group G]

theorem mem_centralizer_of_forall_commutator_mem {E N : Subgroup G} (hE : ⁅E, E⁆ = E)
    (hEN : ∀ x ∈ E, x ∈ N → ∀ y ∈ E, x * y = y * x) {w : G}
    (hconj : ∀ x ∈ E, w * x * w⁻¹ ∈ E) (hw : ∀ x ∈ E, w * x * w⁻¹ * x⁻¹ ∈ N) :
    w ∈ centralizer (E : Set G) := by
  have : Group.IsPerfect E := isPerfect_iff.mpr hE
  have hcE : ∀ x : E, w * (x : G) * w⁻¹ * (x : G)⁻¹ ∈ E := fun x =>
    mul_mem (hconj x x.2) (inv_mem x.2)
  have hcZ : ∀ x : E, (⟨_, hcE x⟩ : E) ∈ center E := fun x => mem_center_iff.2 fun y =>
    Subtype.ext (hEN _ (hcE x) (hw x x.2) y y.2).symm
  have hcomm : ∀ x y : E, (w * (y : G) * w⁻¹ * (y : G)⁻¹) * (x : G) =
      (x : G) * (w * (y : G) * w⁻¹ * (y : G)⁻¹) := fun x y =>
    hEN _ (hcE y) (hw y y.2) x x.2
  let δ : E →* center E :=
    { toFun := fun x => ⟨⟨_, hcE x⟩, hcZ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
        have h1 := hcomm ⟨w * x * w⁻¹, hconj x x.2⟩ y
        have h2 := hcomm x y
        simp only at h1 h2
        calc w * (x * y) * w⁻¹ * ((y : G)⁻¹ * (x : G)⁻¹) =
            (w * x * w⁻¹) * (w * (y : G) * w⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ := by group
          _ = (w * (y : G) * w⁻¹ * (y : G)⁻¹) * (w * x * w⁻¹) * (x : G)⁻¹ := by rw [h1]
          _ = (w * (y : G) * w⁻¹ * (y : G)⁻¹) * (w * x * w⁻¹ * (x : G)⁻¹) := by group
          _ = (w * x * w⁻¹ * (x : G)⁻¹) * (w * (y : G) * w⁻¹ * (y : G)⁻¹) := by
            have h3 := hEN _ (hcE y) (hw y y.2) _ (hcE x)
            rw [h3] }
  have hker : commutator E ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  rw [mem_centralizer_iff]
  intro x hx
  have h1 : δ ⟨x, hx⟩ = 1 := hker (mem_top _)
  have h2 : w * x * w⁻¹ * x⁻¹ = 1 := congrArg (fun z : center E => ((z : E) : G)) h1
  calc x * w = (w * x * w⁻¹ * x⁻¹)⁻¹ * (w * x) := by group
    _ = w * x := by rw [h2, inv_one, one_mul]

end Generic

section GenericStd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem map_conj_le_of_conj_eq_of_forall_commutator_mem
    (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {E N : Subgroup G} (hE : ⁅E, E⁆ = E)
    (hEN : ∀ x ∈ E, x ∈ N → ∀ y ∈ E, x * y = y * x) {g w : G} (hg : g⁻¹ * t * g = w)
    (hwE : ∀ x ∈ E, w * x * w⁻¹ ∈ E) (hw : ∀ x ∈ E, w * x * w⁻¹ * x⁻¹ ∈ N) :
    E.map (MulAut.conj g).toMonoidHom ≤ L ∧ Nat.card E ∣ Nat.card L := by
  have hwC := mem_centralizer_of_forall_commutator_mem hE hEN hwE hw
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxw : x * w = w * x := mem_centralizer_iff.1 hwC x hx
    rw [← hg] at hxw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hxw]
      _ = t * (g * x * g⁻¹) := by group
  have hEgp : ⁅E.map (MulAut.conj g).toMonoidHom, E.map (MulAut.conj g).toMonoidHom⁆ =
      E.map (MulAut.conj g).toMonoidHom := by
    rw [← map_commutator, hE]
  have hle := std_perfect_le hset hOut htC ht hEgp hEg
  refine ⟨hle, ?_⟩
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact Subgroup.card_dvd_of_le hle

end GenericStd

section Root

theorem card_rootSL2_two {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) (hn : 3 ≤ n)
    {a b : Fin n} (hab : a ≠ b) : Nat.card (rootSL2 (K := K) a b) = 6 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ⟩ := rootSL2_mulEquiv (K := K) hab hn
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Nat.card_congr φ.toEquiv, Matrix.card_SL_field, hq, Fin.prod_univ_two]
  rfl

theorem mem_normalizer_of_mem_rootSL2_two {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1) {j : LinearFlag.projectiveSL n K}
    (hj : j ∈ rootSL2 a b) : j ∈ normalizer (X₀ : Set (LinearFlag.projectiveSL n K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hR := card_rootSL2_two hK hn hab
  have hidx : (X₀.subgroupOf (rootSL2 (K := K) a b)).index = 2 := by
    have h1 := Subgroup.card_mul_index (X₀.subgroupOf (rootSL2 (K := K) a b))
    rw [Nat.card_congr (X₀.subgroupOfEquivOfLe hX₀).toEquiv, hX₀c, hK, hR] at h1
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := hnorm.conj_mem ⟨x, hX₀ hx⟩ (mem_subgroupOf.2 hx) ⟨j, hj⟩
    exact mem_subgroupOf.1 h1
  · intro hx
    have hxR : x ∈ rootSL2 (K := K) a b := by
      have h2 : j⁻¹ * (j * x * j⁻¹) * j ∈ rootSL2 (K := K) a b :=
        mul_mem (mul_mem (inv_mem hj) (hX₀ hx)) hj
      simpa [mul_assoc] using h2
    have h1 := hnorm.conj_mem ⟨j * x * j⁻¹, hX₀ hx⟩ (mem_subgroupOf.2 hx) ⟨j⁻¹, inv_mem hj⟩
    have h3 : j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x := by group
    have h4 := mem_subgroupOf.1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    rwa [h3] at h4

end Root

section BLift

variable {G : Type} [Group G] [Finite G]

theorem forall_mem_oddCore_commute_of_perfectCore_eq {X : Subgroup G}
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))) = Kc) (hB : HasBLift Kc) :
    ∀ x ∈ centralizerPerfectCore X,
      x ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype →
      ∀ y ∈ centralizerPerfectCore X, x * y = y * x := by
  obtain ⟨q, -, hqc, -, hqapp⟩ := exists_surjective_neighbourCore_of_perfectCore_eq hcore hB
  rintro x hx ⟨o, ho, rfl⟩ y hy
  have hker : (⟨_, hx⟩ : centralizerPerfectCore X) ∈ q.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hqapp]
    exact (QuotientGroup.eq_one_iff _).2 (by simpa using ho)
  have h1 := mem_center_iff.1 (hqc hker) ⟨y, hy⟩
  exact (congrArg Subtype.val h1).symm

end BLift

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem map_symm_mem_normalizer {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    {c : LinearFlag.projectiveSL n K} (hc : c ∈ normalizer (X₀ : Set (LinearFlag.projectiveSL n K)))
    : ((e.symm c : L) : G) ∈ normalizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
        Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have key : ∀ x₀ : LinearFlag.projectiveSL n K,
      ((e.symm c : L) : G) * ((e.symm x₀ : L) : G) * ((e.symm c : L) : G)⁻¹ =
        ((e.symm (c * x₀ * c⁻¹) : L) : G) := by
    intro x₀
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · rintro ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩
    refine ⟨e.symm (c * x₀ * c⁻¹), ⟨c * x₀ * c⁻¹, (mem_normalizer_iff.1 hc x₀).1 hx₀, rfl⟩, ?_⟩
    exact (key x₀).symm
  · rintro ⟨_, ⟨y₀, hy₀, rfl⟩, hy⟩
    have hxL : x ∈ L := by
      have hy' : ((e.symm y₀ : L) : G) = ((e.symm c : L) : G) * x * ((e.symm c : L) : G)⁻¹ := hy
      have h1 : x = ((e.symm c : L) : G)⁻¹ * ((e.symm y₀ : L) : G) * ((e.symm c : L) : G) := by
        rw [hy']
        group
      rw [h1]
      exact mul_mem (mul_mem (inv_mem (e.symm c).2) (e.symm y₀).2) (e.symm c).2
    set x₀ := e ⟨x, hxL⟩ with hx₀def
    have hx : ((e.symm x₀ : L) : G) = x := by rw [hx₀def, MulEquiv.symm_apply_apply]
    have hcy : c * x₀ * c⁻¹ = y₀ := by
      apply e.symm.injective
      apply Subtype.ext
      rw [← key, hx]
      exact hy.symm
    refine ⟨e.symm x₀, ⟨x₀, (mem_normalizer_iff.1 hc x₀).2 (hcy ▸ hy₀), rfl⟩, hx⟩

omit [Finite G] in
theorem mem_normalizer_centralizerPerfectCore {X : Subgroup G} {j : G}
    (hj : j ∈ normalizer (X : Set G)) :
    j ∈ normalizer (centralizerPerfectCore X : Set G) := by
  have hjC : j ∈ normalizer (centralizer (X : Set G) : Set G) := by
    have hX : ∀ x : G, x ∈ X ↔ j * x * j⁻¹ ∈ X := mem_normalizer_iff.1 hj
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [mem_centralizer_iff] at hh ⊢
      intro x hx
      have hx' : j⁻¹ * x * j ∈ X := by
        have := (hX (j⁻¹ * x * j)).2 (by simpa [mul_assoc] using hx)
        exact this
      have h1 := hh _ hx'
      calc x * (j * h * j⁻¹) = j * ((j⁻¹ * x * j) * h) * j⁻¹ := by group
        _ = j * (h * (j⁻¹ * x * j)) * j⁻¹ := by rw [h1]
        _ = j * h * j⁻¹ * x := by group
    · intro hh
      rw [mem_centralizer_iff] at hh ⊢
      intro x hx
      have h1 := hh _ ((hX x).1 hx)
      calc x * h = j⁻¹ * ((j * x * j⁻¹) * (j * h * j⁻¹)) * j := by group
        _ = j⁻¹ * ((j * h * j⁻¹) * (j * x * j⁻¹)) * j := by rw [h1]
        _ = h * x := by group
  exact CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ hjC

theorem card_dvd_of_acts_as_linear_two (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (hB : ∀ x ∈ centralizerPerfectCore X,
      x ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype →
      ∀ y ∈ centralizerPerfectCore X, x * y = y * x)
    (hact : ∀ x ∈ centralizerPerfectCore X,
      ((e.symm (xab hab 1) : L) : G) * x * ((e.symm (xab hab 1) : L) : G)⁻¹ * (t * x * t⁻¹)⁻¹ ∈
        (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype) :
    ∃ g : G, (centralizerPerfectCore X).map (MulAut.conj g).toMonoidHom ≤ L ∧
      Nat.card (centralizerPerfectCore X) ∣ Nat.card L := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have hOut := isSolvable_outer_of_mulEquiv (by omega : 3 ≤ n) e
  obtain ⟨x, z, hxz, hz, -, -, -⟩ :=
    exists_conj_eq_mul_transvection_twoSided_two hset (by omega) hK e htC ht
  obtain ⟨g, y, hey, -, -, hg⟩ :=
    exists_conj_eq_mul_xab' e (le_centralizer_of_mem_centralizer htC) hab ⟨x, z, hz, hxz⟩
  have hy : y = e.symm (xab hab 1) := by rw [← hey, MulEquiv.symm_apply_apply]
  subst hy
  set j : G := ((e.symm (xab hab 1) : L) : G) with hjdef
  have htX : t ∈ centralizer (X : Set G) := hX ▸ mem_centralizer_map_symm e X₀ htC
  have hjX : j ∈ normalizer (X : Set G) := by
    rw [hX]
    exact map_symm_mem_normalizer e (mem_normalizer_of_mem_rootSL2_two hK (by omega) hab hX₀
      hX₀c (xab_mem_rootSL2 hab 1))
  have htE : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer htX)
  have hjE := mem_normalizer_centralizerPerfectCore hjX
  have hwE : ∀ x ∈ centralizerPerfectCore X, (t * j) * x * (t * j)⁻¹ ∈
      centralizerPerfectCore X := by
    intro x hx
    have h1 := (mem_normalizer_iff.1 htE (j * x * j⁻¹)).1 ((mem_normalizer_iff.1 hjE x).1 hx)
    simpa [mul_assoc] using h1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hOt : ∀ o ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      t * o * t⁻¹ ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨⟨t, htX⟩ * o * ⟨t, htX⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (oddCore (centralizer (X : Set G))).Normal).conj_mem o ho ⟨t, htX⟩
  have hw : ∀ x ∈ centralizerPerfectCore X, (t * j) * x * (t * j)⁻¹ * x⁻¹ ∈
      (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype := by
    intro x hx
    have h1 := hOt _ (hact x hx)
    have h2 : t * (j * x * j⁻¹ * (t * x * t⁻¹)⁻¹) * t⁻¹ = (t * j) * x * (t * j)⁻¹ * x⁻¹ := by
      have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      calc t * (j * x * j⁻¹ * (t * x * t⁻¹)⁻¹) * t⁻¹ =
          t * j * x * j⁻¹ * (t * x⁻¹ * t⁻¹) * t⁻¹ := by group
        _ = t * j * x * j⁻¹ * t * x⁻¹ * (t * t) := by rw [ht']; group
        _ = t * j * x * j⁻¹ * t⁻¹ * x⁻¹ := by rw [htt, ht', mul_one]
        _ = (t * j) * x * (t * j)⁻¹ * x⁻¹ := by group
    rwa [h2] at h1
  obtain ⟨hle, hdvd⟩ := map_conj_le_of_conj_eq_of_forall_commutator_mem hset.standardSetting hOut
    htC ht (CFSG.Quasithin.perfectCore_perfect _) hB hg hwE hw
  exact ⟨g, hle, hdvd⟩

end Setting

end CFSG.SeitzReduction.LinearPilot
