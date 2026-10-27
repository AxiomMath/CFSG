module

public import CFSG.LargeExtraspecial.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GriessLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith

section ConjAutLemmas

variable {H : Type*} [Group H] {Q : Subgroup H}

theorem conjAut_mul (hQn : Q.Normal) (a b : H) :
    conjAut hQn (a * b) = conjAut hQn a * conjAut hQn b :=
  map_mul (@MulAut.conjNormal H _ Q hQn) a b

theorem conjAut_mul_apply (hQn : Q.Normal) (a b : H) (q : Q) :
    conjAut hQn (a * b) q = conjAut hQn a (conjAut hQn b q) := by
  rw [conjAut_mul, MulAut.mul_apply]

theorem conjAut_one (hQn : Q.Normal) : conjAut hQn (1 : H) = 1 :=
  map_one (@MulAut.conjNormal H _ Q hQn)

theorem conjAut_inv (hQn : Q.Normal) (a : H) :
    conjAut hQn a⁻¹ = (conjAut hQn a)⁻¹ :=
  map_inv (@MulAut.conjNormal H _ Q hQn) a

theorem conjAut_eq_of_mul_inv_mem_center (hQn : Q.Normal) {a b : H}
    (h : a * b⁻¹ ∈ (Subgroup.center Q).map Q.subtype) : conjAut hQn a = conjAut hQn b := by
  obtain ⟨c, hc, hcab⟩ := h
  have hcab' : (c : H) = a * b⁻¹ := hcab
  ext y
  have hby : b * (y : H) * b⁻¹ ∈ Q := hQn.conj_mem _ y.2 b
  have hcommQ : (c : ↥Q) * ⟨b * (y : H) * b⁻¹, hby⟩ = ⟨b * (y : H) * b⁻¹, hby⟩ * c :=
    (Subgroup.mem_center_iff.mp hc ⟨b * (y : H) * b⁻¹, hby⟩).symm
  have hcomm : (c : H) * (b * (y : H) * b⁻¹) = (b * (y : H) * b⁻¹) * (c : H) :=
    congrArg Subtype.val hcommQ
  calc (conjAut hQn a y : H) = a * (y : H) * a⁻¹ := conjAut_apply hQn a y
    _ = ((a * b⁻¹) * b) * (y : H) * ((a * b⁻¹) * b)⁻¹ := by group
    _ = (c : H) * (b * (y : H) * b⁻¹) * (c : H)⁻¹ := by rw [← hcab']; group
    _ = b * (y : H) * b⁻¹ := by rw [hcomm]; group
    _ = (conjAut hQn b y : H) := (conjAut_apply hQn b y).symm

theorem mul_inv_mem_center_of_conjAut_eq (hQn : Q.Normal)
    (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q) {a b : H}
    (h : conjAut hQn a = conjAut hQn b) :
    a * b⁻¹ ∈ (Subgroup.center Q).map Q.subtype := by
  have hcent : a * b⁻¹ ∈ Subgroup.centralizer (Q : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : b⁻¹ * y * b ∈ Q := by
      simpa using hQn.conj_mem y hy b⁻¹
    have hh := congrArg (fun φ : MulAut ↥Q => ((φ ⟨b⁻¹ * y * b, hy1⟩ : ↥Q) : H)) h
    simp only [conjAut_apply, Subgroup.coe_mk] at hh
    have hconj : a * (b⁻¹ * y * b) * a⁻¹ = y := by
      rw [hh]
      group
    calc y * (a * b⁻¹) = a * (b⁻¹ * y * b) * a⁻¹ * (a * b⁻¹) := by rw [hconj]
      _ = (a * b⁻¹) * y := by rw [← hconj]; group
  have hQ : a * b⁻¹ ∈ Q := hCQ hcent
  refine ⟨⟨a * b⁻¹, hQ⟩, ?_, rfl⟩
  refine Subgroup.mem_center_iff.mpr fun z => ?_
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent (z : H) z.2)

end ConjAutLemmas

section LinearLemmas

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixed_of_conj_mul_fixed (g h : V ≃ₗ[ZMod 2] V) (v : V)
    (hv : (g * h * g⁻¹) v = v) : h (g⁻¹ v) = g⁻¹ v := by
  have hv' : g (h (g⁻¹ v)) = v := by
    calc g (h (g⁻¹ v)) = (g * h) (g⁻¹ v) := (LinearEquiv.mul_apply g h (g⁻¹ v)).symm
      _ = (g * h * g⁻¹) v := (LinearEquiv.mul_apply (g * h) g⁻¹ v).symm
      _ = v := hv
  have := congrArg (fun w => g⁻¹ w) hv'
  simpa using this

end LinearLemmas

section ExtraspecialLemmas

variable {H : Type*} [Group H] {Q : Subgroup H} [Finite Q] (hQn : Q.Normal)

theorem mem_center_of_mul_mul_inv_mem_center_of_fixedFree
    (hE : IsExtraspecialPGroup 2 Q) [Module (ZMod 2) (Additive (Abelianization Q))]
    {u : ↥Q} {N x' : H}
    (hfree : ∀ v : Additive (Abelianization Q), conjLinEquiv hQn x' v = v → v = 0)
    (hc : ((u : H) * N * x') * (N * x' * N⁻¹ * (u : H) * N)⁻¹ ∈
      (Subgroup.center Q).map Q.subtype) :
    u ∈ Subgroup.center Q := by
  classical
  obtain ⟨c, hcQ, hcH⟩ := hc
  have hcH' : (c : H) = ((u : H) * N * x') * (N * x' * N⁻¹ * (u : H) * N)⁻¹ := hcH
  have hAB : (u : H) * N * x' = (c : H) * (N * x' * N⁻¹ * (u : H) * N) := by
    rw [hcH']; group
  have h1 : (u : H) * (N * x' * N⁻¹) = (c : H) * ((N * x' * N⁻¹) * (u : H)) := by
    have h := congrArg (fun t : H => t * N⁻¹) hAB
    simpa only [mul_assoc, mul_inv_cancel_right, mul_inv_cancel, mul_one] using h
  have h2 : (N * x' * N⁻¹)⁻¹ * (u : H) * (N * x' * N⁻¹) =
      ((N * x' * N⁻¹)⁻¹ * (c : H) * (N * x' * N⁻¹)) * (u : H) := by
    have h := congrArg (fun t : H => (N * x' * N⁻¹)⁻¹ * t) h1
    simpa only [mul_assoc] using h
  let d : ↥Q := conjAut hQn (N * x' * N⁻¹)⁻¹ c
  have hdH : (d : H) = (N * x' * N⁻¹)⁻¹ * (c : H) * (N * x' * N⁻¹) := by
    change (conjAut hQn (N * x' * N⁻¹)⁻¹ c : H) = _
    rw [conjAut_apply, inv_inv]
  have h2Q : conjAut hQn (N * x' * N⁻¹)⁻¹ u = d * u := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, conjAut_apply, inv_inv, hdH]
    exact h2
  have hπd : Additive.ofMul (Abelianization.of d) = 0 := by
    have hd : d = conjAut hQn (N * x' * N⁻¹)⁻¹ c := rfl
    rw [hd, ← conjLinEquiv_apply hQn (N * x' * N⁻¹)⁻¹ c,
      (ofMul_of_eq_zero_iff hE c).mpr hcQ, map_zero]
  have h3 : conjLinEquiv hQn (N * x' * N⁻¹)⁻¹ (Additive.ofMul (Abelianization.of u)) =
      Additive.ofMul (Abelianization.of u) := by
    rw [conjLinEquiv_apply hQn (N * x' * N⁻¹)⁻¹ u, h2Q, ofMul_of_mul, hπd, zero_add]
  have h3inv : (conjLinEquiv hQn (N * x' * N⁻¹))⁻¹ (Additive.ofMul (Abelianization.of u)) =
      Additive.ofMul (Abelianization.of u) := by
    rw [← map_inv (conjLinEquiv hQn) (N * x' * N⁻¹)]
    exact h3
  have hvC : conjLinEquiv hQn (N * x' * N⁻¹) (Additive.ofMul (Abelianization.of u)) =
      Additive.ofMul (Abelianization.of u) := by
    have h := congrArg (conjLinEquiv hQn (N * x' * N⁻¹)) h3inv
    simpa using h.symm
  have hCmul : conjLinEquiv hQn (N * x' * N⁻¹) =
      conjLinEquiv hQn N * conjLinEquiv hQn x' * (conjLinEquiv hQn N)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [hCmul] at hvC
  have hw : conjLinEquiv hQn x' ((conjLinEquiv hQn N)⁻¹ (Additive.ofMul (Abelianization.of u))) =
      (conjLinEquiv hQn N)⁻¹ (Additive.ofMul (Abelianization.of u)) :=
    fixed_of_conj_mul_fixed _ _ _ hvC
  have hw0 : (conjLinEquiv hQn N)⁻¹ (Additive.ofMul (Abelianization.of u)) = 0 := hfree _ hw
  have hπu0 : Additive.ofMul (Abelianization.of u) = 0 := by
    have := congrArg (conjLinEquiv hQn N) hw0
    simpa using this
  exact (ofMul_of_eq_zero_iff hE u).mp hπu0

end ExtraspecialLemmas

namespace Setting

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
  (S : Setting G) (S' : Setting G')

theorem exists_mulEquiv_conjAut_eq_of_induce
    (a : S.Qt ≃ₗ[ZMod 2] S'.Qt) {x : S.M} {x' : S'.M}
    (hx : ∀ v : S.Qt, a ((S.ρ x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a v))
    (hfree : ∀ v : S'.Qt, (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) v = v → v = 0)
    {φ : ↥S.Q ≃* ↥S'.Q} (hφ : ∀ q, a (S.toQt q) = S'.toQt (φ q)) :
    ∃ φ₁ : ↥S.Q ≃* ↥S'.Q, (∀ q, a (S.toQt q) = S'.toQt (φ₁ q)) ∧
      ∀ q, φ₁ (conjAut S.normal x q) = conjAut S'.normal x' (φ₁ q) := by
  classical
  have hcen : ∀ y : ↥S.Q, φ (conjAut S.normal x y) *
      (conjAut S'.normal x' (φ y))⁻¹ ∈ Subgroup.center ↥S'.Q := by
    intro y
    refine (S'.toQt_eq_zero_iff _).mp ?_
    rw [S'.toQt_mul, S'.toQt_inv]
    have hcls : S'.toQt (φ (conjAut S.normal x y)) =
        S'.toQt (conjAut S'.normal x' (φ y)) := by
      calc S'.toQt (φ (conjAut S.normal x y)) = a (S.toQt (conjAut S.normal x y)) :=
            (hφ _).symm
        _ = a ((S.ρ x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.toQt y)) := congrArg a (S.ρ_toQt x y).symm
        _ = (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a (S.toQt y)) := hx _
        _ = (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (S'.toQt (φ y)) := by rw [hφ y]
        _ = S'.toQt (conjAut S'.normal x' (φ y)) := S'.ρ_toQt x' (φ y)
    rw [hcls, add_neg_cancel]
  obtain ⟨u, hu⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_conj_compat
    (hQn := S.normal) (hQn' := S'.normal) S'.extraspecial φ x x' hcen
  let L : S'.Qt →ₗ[ZMod 2] S'.Qt :=
    (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt).toLinearMap - LinearMap.id
  have hL_apply : ∀ v : S'.Qt, L v = (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) v - v := by
    intro v
    simp [L]
  have hLinj : Function.Injective L := by
    intro a₁ a₂ hab
    have h0 : L (a₁ - a₂) = 0 := by rw [map_sub, hab, sub_self]
    have hfix : (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a₁ - a₂) = a₁ - a₂ := by
      rw [hL_apply] at h0
      exact sub_eq_zero.mp h0
    exact sub_eq_zero.mp (hfree (a₁ - a₂) hfix)
  have hsurj : Function.Surjective L := (Finite.injective_iff_surjective).mp hLinj
  obtain ⟨w, hw⟩ := hsurj (S'.toQt u)
  have hw' : (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) w - w = S'.toQt u := by
    simpa only [L, LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply] using hw
  obtain ⟨v, hv⟩ := S'.exists_toQt w
  have hv' : (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (S'.toQt v) = S'.toQt u + S'.toQt v := by
    have h : (S'.ρ x' : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (S'.toQt v) - S'.toQt v = S'.toQt u := by
      rw [hv]
      exact hw'
    exact sub_eq_iff_eq_add.mp h
  refine ⟨φ.trans (conjAut S'.normal v), ?_, ?_⟩
  · intro q
    rw [MulEquiv.trans_apply]
    have h1 : S'.toQt (conjAut S'.normal v (φ q)) = S'.toQt (φ q) := by
      rw [← S'.ρ_toQt v (φ q), S'.ρ_eq_one_of_mem_Q v.2]
      rfl
    rw [h1]
    exact hφ q
  · intro q
    have hd_center : ((v * u) * conjAut S'.normal x' v⁻¹) ∈ Subgroup.center ↥S'.Q := by
      refine (S'.toQt_eq_zero_iff _).mp ?_
      rw [S'.toQt_mul, S'.toQt_mul, ← S'.ρ_toQt x' v⁻¹, S'.toQt_inv, map_neg]
      rw [hv']
      abel
    have hkey : conjAut S'.normal ((v : S'.M) * ((u : S'.M) * x')) =
        conjAut S'.normal (x' * (v : S'.M)) := by
      refine conjAut_eq_of_mul_inv_mem_center S'.normal ⟨(v * u) * conjAut S'.normal x' v⁻¹,
        hd_center, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply]
      group
    have hL : (φ.trans (conjAut S'.normal v)) (conjAut S.normal x q) =
        conjAut S'.normal ((v : S'.M) * ((u : S'.M) * x')) (φ q) := by
      rw [MulEquiv.trans_apply, hu q, ← conjAut_mul_apply]
    have hR : conjAut S'.normal x' ((φ.trans (conjAut S'.normal v)) q) =
        conjAut S'.normal (x' * (v : S'.M)) (φ q) := by
      rw [MulEquiv.trans_apply, ← conjAut_mul_apply]
    rw [hL, hR, hkey]

theorem exists_mulEquiv_Q_of_isometry
    {N : Subgroup S.M} {N' : Subgroup S'.M} (θN : ↥N ≃* ↥N')
    (a : S.Qt ≃ₗ[ZMod 2] S'.Qt) (ha : ∀ v, S'.q (a v) = S.q v)
    (hequiv : ∀ (n : ↥N) (v : S.Qt),
      a ((S.ρ n : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (S'.ρ (θN n) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a v))
    {x : S.M} (hxN : x ∈ N) (hx1 : x ≠ 1)
    (hXN : ∀ n ∈ N, n * x * n⁻¹ ∈ Subgroup.zpowers x)
    (hfpf : ∀ y : ↥N, (y : S.M) ∈ Subgroup.zpowers x → y ≠ 1 →
      ∀ v : S'.Qt, (S'.ρ (θN y) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) v = v → v = 0) :
    ∃ θQ : ↥S.Q ≃* ↥S'.Q, (∀ q, a (S.toQt q) = S'.toQt (θQ q)) ∧
      ∀ (n : ↥N) (q : ↥S.Q),
        θQ (conjAut S.normal (n : S.M) q) = conjAut S'.normal ((θN n : ↥N') : S'.M) (θQ q) := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_mulEquiv_of_isometry
    S.extraspecial S'.extraspecial a ha
  let xN : ↥N := ⟨x, hxN⟩
  have hxN_ne : xN ≠ 1 := fun h => hx1 (congrArg (fun n : ↥N => (n : S.M)) h)
  have hxmem : (xN : S.M) ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one x⟩
  have hfree_x : ∀ v : S'.Qt, (S'.ρ (θN xN) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) v = v → v = 0 :=
    fun v hv => hfpf xN hxmem hxN_ne v hv
  have hx_equiv : ∀ v : S.Qt, a ((S.ρ (xN : S.M) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (S'.ρ (θN xN) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a v) := fun v => hequiv xN v
  obtain ⟨φ₁, hφ₁a, hφ₁x⟩ :=
    exists_mulEquiv_conjAut_eq_of_induce S S' a hx_equiv hfree_x hφ₀
  let good : Subgroup ↥N :=
    { carrier := {n : ↥N | ∀ q : ↥S.Q, φ₁ (conjAut S.normal (n : S.M) q) =
        conjAut S'.normal ((θN n : ↥N') : S'.M) (φ₁ q)}
      one_mem' := by
        intro q
        rw [Subgroup.coe_one, conjAut_one, map_one θN, Subgroup.coe_one, conjAut_one]
        simp
      mul_mem' := by
        intro a b ha hb q
        rw [Subgroup.coe_mul, conjAut_mul_apply, ha, hb, ← conjAut_mul_apply]
        congr 1
        rw [map_mul θN, Subgroup.coe_mul]
      inv_mem' := by
        intro a ha q
        have hθ : ((θN a⁻¹ : ↥N') : S'.M) = (((θN a : ↥N') : S'.M))⁻¹ := by
          rw [map_inv θN, Subgroup.coe_inv]
        rw [hθ, conjAut_inv]
        have h := ha (conjAut S.normal ((a⁻¹ : ↥N) : S.M) q)
        have hcomp : conjAut S.normal ((a : ↥N) : S.M)
            (conjAut S.normal ((a⁻¹ : ↥N) : S.M) q) = q := by
          rw [← conjAut_mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
            conjAut_one]
          simp
        rw [hcomp] at h
        have h3 := congrArg (fun y => (conjAut S'.normal ((θN a : ↥N') : S'.M))⁻¹ y) h
        simpa using h3.symm }
  have hzp : Subgroup.zpowers xN ≤ good := Subgroup.zpowers_le.mpr hφ₁x
  refine ⟨φ₁, hφ₁a, ?_⟩
  intro n q
  have hcen : ∀ y : ↥S.Q, φ₁ (conjAut S.normal (n : S.M) y) *
      (conjAut S'.normal ((θN n : ↥N') : S'.M) (φ₁ y))⁻¹ ∈ Subgroup.center ↥S'.Q := by
    intro y
    refine (S'.toQt_eq_zero_iff _).mp ?_
    rw [S'.toQt_mul, S'.toQt_inv]
    have hcls : S'.toQt (φ₁ (conjAut S.normal (n : S.M) y)) =
        S'.toQt (conjAut S'.normal ((θN n : ↥N') : S'.M) (φ₁ y)) := by
      calc S'.toQt (φ₁ (conjAut S.normal (n : S.M) y)) =
            a (S.toQt (conjAut S.normal (n : S.M) y)) := (hφ₁a _).symm
        _ = a ((S.ρ (n : S.M) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.toQt y)) :=
            congrArg a (S.ρ_toQt (n : S.M) y).symm
        _ = (S'.ρ ((θN n : ↥N') : S'.M) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (a (S.toQt y)) :=
            hequiv n (S.toQt y)
        _ = (S'.ρ ((θN n : ↥N') : S'.M) : S'.Qt ≃ₗ[ZMod 2] S'.Qt) (S'.toQt (φ₁ y)) := by
            rw [hφ₁a y]
        _ = S'.toQt (conjAut S'.normal ((θN n : ↥N') : S'.M) (φ₁ y)) :=
            S'.ρ_toQt _ (φ₁ y)
    rw [hcls, add_neg_cancel]
  obtain ⟨u, hu⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_conj_compat
    (hQn := S.normal) (hQn' := S'.normal) S'.extraspecial φ₁ (n : S.M)
    ((θN n : ↥N') : S'.M) hcen
  let yN : ↥N := n * xN * n⁻¹
  have hyN_mem : yN ∈ Subgroup.zpowers xN := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hXN n n.2)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk
  have hyN_good : ∀ r : ↥S.Q, φ₁ (conjAut S.normal (yN : S.M) r) =
      conjAut S'.normal ((θN yN : ↥N') : S'.M) (φ₁ r) := hzp hyN_mem
  have hθy : ((θN yN : ↥N') : S'.M) =
      ((θN n : ↥N') : S'.M) * ((θN xN : ↥N') : S'.M) * (((θN n : ↥N') : S'.M))⁻¹ := by
    rw [show yN = n * xN * n⁻¹ from rfl, map_mul θN, map_mul θN, map_inv θN,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hkey : conjAut S'.normal
        (((u : S'.M) * ((θN n : ↥N') : S'.M)) * ((θN xN : ↥N') : S'.M)) =
      conjAut S'.normal
        (((θN yN : ↥N') : S'.M) * ((u : S'.M) * ((θN n : ↥N') : S'.M))) := by
    ext r
    have h1 : conjAut S'.normal
          (((u : S'.M) * ((θN n : ↥N') : S'.M)) * ((θN xN : ↥N') : S'.M)) r =
        φ₁ (conjAut S.normal ((n : S.M) * x) (φ₁.symm r)) := by
      rw [conjAut_mul_apply]
      have hinner : conjAut S'.normal ((θN xN : ↥N') : S'.M) r =
          φ₁ (conjAut S.normal x (φ₁.symm r)) := by
        conv_lhs => rw [← MulEquiv.apply_symm_apply φ₁ r]
        exact (hφ₁x (φ₁.symm r)).symm
      rw [hinner, ← hu (conjAut S.normal x (φ₁.symm r)), ← conjAut_mul_apply]
    have h2 : conjAut S'.normal
          (((θN yN : ↥N') : S'.M) * ((u : S'.M) * ((θN n : ↥N') : S'.M))) r =
        φ₁ (conjAut S.normal (yN : S.M) (conjAut S.normal (n : S.M) (φ₁.symm r))) := by
      rw [conjAut_mul_apply]
      have hinner : conjAut S'.normal ((u : S'.M) * ((θN n : ↥N') : S'.M)) r =
          φ₁ (conjAut S.normal (n : S.M) (φ₁.symm r)) := by
        conv_lhs => rw [← MulEquiv.apply_symm_apply φ₁ r]
        exact (hu (φ₁.symm r)).symm
      rw [hinner, ← hyN_good (conjAut S.normal (n : S.M) (φ₁.symm r))]
    rw [h1, h2, ← conjAut_mul_apply]
    have helem : (n : S.M) * x = (yN : S.M) * (n : S.M) := by
      have hy : (yN : S.M) = (n : S.M) * x * ((n : S.M))⁻¹ := rfl
      rw [hy]
      group
    rw [helem]
  have hc : (((u : S'.M) * ((θN n : ↥N') : S'.M)) * ((θN xN : ↥N') : S'.M)) *
      ((((θN yN : ↥N') : S'.M) * ((u : S'.M) * ((θN n : ↥N') : S'.M))))⁻¹ ∈
      (Subgroup.center ↥S'.Q).map S'.Q.subtype :=
    mul_inv_mem_center_of_conjAut_eq S'.normal S'.centralizer_le hkey
  rw [hθy] at hc
  have hfree' : ∀ v : S'.Qt, conjLinEquiv S'.normal ((θN xN : ↥N') : S'.M) v = v → v = 0 :=
    hfree_x
  have hu_center : u ∈ Subgroup.center ↥S'.Q :=
    mem_center_of_mul_mul_inv_mem_center_of_fixedFree (H := S'.M) (Q := S'.Q)
      S'.normal S'.extraspecial hfree' (by simpa only [mul_assoc] using hc)
  calc φ₁ (conjAut S.normal (n : S.M) q)
      = conjAut S'.normal ((u : S'.M) * ((θN n : ↥N') : S'.M)) (φ₁ q) := hu q
    _ = conjAut S'.normal ((θN n : ↥N') : S'.M) (φ₁ q) := by
        have hcu : conjAut S'.normal ((u : S'.M) * ((θN n : ↥N') : S'.M)) =
            conjAut S'.normal ((θN n : ↥N') : S'.M) :=
          conjAut_eq_of_mul_inv_mem_center (Q := S'.Q) S'.normal
            (a := (u : S'.M) * ((θN n : ↥N') : S'.M))
            (b := ((θN n : ↥N') : S'.M)) ⟨u, hu_center, by simp⟩
        rw [hcu]

end Setting

end CFSG.LargeExtraspecial
