module

public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth
public import CFSG.LieType.SeitzGeneration.OrthHyperScope
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Cube

theorem exists_cube_of_three {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e₁ e₂ e₃ : G}
    (h12 : Commute e₁ e₂) (h13 : Commute e₁ e₃) (h23 : Commute e₂ e₃) (h₁ : e₁ ^ p = 1)
    (h₂ : e₂ ^ p = 1) (h₃ : e₃ ^ p = 1)
    (hi : ∀ i j k : ℤ, e₁ ^ i * e₂ ^ j * e₃ ^ k = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (∀ x ∈ E, ∃ i j k : ℤ, x = e₁ ^ i * e₂ ^ j * e₃ ^ k) ∧ e₁ ∈ E ∧ e₂ ∈ E ∧ e₃ ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := fun h => by
    have := (hi 1 0 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne2 : e₂ ≠ 1 := fun h => by
    have := (hi 0 1 0 (by rw [h]; simp)).2.1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne3 : e₃ ≠ 1 := fun h => by
    have := (hi 0 0 1 (by rw [h]; simp)).2.2
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have ho₃ : orderOf e₃ = p := orderOf_eq_prime h₃ hne3
  have hc12 : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : G) (b : G)
    rw [← hk, ← hl]
    exact h12.zpow_zpow k l
  let f₂ : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hc12
  have hc3 : ∀ (a : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂))
      (c : ↥(Subgroup.zpowers e₃)), Commute (f₂ a) ((Subgroup.zpowers e₃).subtype c) := by
    intro a c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.1.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
    change Commute ((a.1 : G) * (a.2 : G)) (c : G)
    rw [← hk, ← hl, ← hm]
    exact (h13.zpow_zpow k m).mul_left (h23.zpow_zpow l m)
  let f₃ : (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) × ↥(Subgroup.zpowers e₃) →* G :=
    MonoidHom.noncommCoprod f₂ (Subgroup.zpowers e₃).subtype hc3
  have hf : Function.Injective f₃ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨a, b⟩, c⟩ hab
    have hab' : (a : G) * b * c = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
    rw [← hk, ← hl, ← hm] at hab'
    obtain ⟨hpk, hpl, hpm⟩ := hi k l m hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨n, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨n, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    have hc : c = 1 := by
      apply Subtype.ext
      rw [← hm]
      obtain ⟨n, rfl⟩ := hpm
      rw [zpow_mul, zpow_natCast, h₃, one_zpow]
      rfl
    rw [ha, hb, hc]
    rfl
  have hcard : Nat.card ((↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) ×
      ↥(Subgroup.zpowers e₃)) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers, ho₁,
      ho₂, ho₃]
    ring
  refine ⟨f₃.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩,
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard, fun x hx => ?_,
    ⟨((⟨e₁, Subgroup.mem_zpowers e₁⟩, 1), 1), by simp [f₃, f₂]⟩,
    ⟨((1, ⟨e₂, Subgroup.mem_zpowers e₂⟩), 1), by simp [f₃, f₂]⟩,
    ⟨((1, 1), ⟨e₃, Subgroup.mem_zpowers e₃⟩), by simp [f₃, f₂]⟩⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (Prod.ext (mul_comm' x.1.1 z.1.1) (mul_comm' x.1.2 z.1.2))
      (mul_comm' x.2 z.2)
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have hpow : ∀ (e : G) (he : e ^ p = 1) (a : ↥(Subgroup.zpowers e)), a ^ p = 1 := by
      intro e he a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      change (a : G) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
    have : x ^ p = 1 := Prod.ext (Prod.ext (hpow e₁ h₁ x.1.1) (hpow e₂ h₂ x.1.2))
      (hpow e₃ h₃ x.2)
    rw [this, map_one]
  · obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
    refine ⟨k, l, m, ?_⟩
    change (a : G) * b * c = _
    rw [← hk, ← hl, ← hm]

end Cube

section Blocks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace QBlock

variable {M : Type} [AddCommGroup M] [Module K M] (B : QBlock Q M)

@[expose] def blkEquivOf (T T' : M →ₗ[K] M) (h1 : T ∘ₗ T' = LinearMap.id)
    (h2 : T' ∘ₗ T = LinearMap.id) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (B.blk T) (B.blk T')
    (LinearMap.ext fun v => by
      change B.blk T (B.blk T' v) = v
      rw [← blk_comp, h1, blk_id])
    (LinearMap.ext fun v => by
      change B.blk T' (B.blk T v) = v
      rw [← blk_comp, h2, blk_id])

variable (T T' : M →ₗ[K] M) (h1 : T ∘ₗ T' = LinearMap.id) (h2 : T' ∘ₗ T = LinearMap.id)

theorem blkEquivOf_apply (v : V) : B.blkEquivOf T T' h1 h2 v = B.blk T v := rfl

theorem blkEquivOf_pow_apply (n : ℕ) (v : V) :
    (B.blkEquivOf T T' h1 h2 ^ n) v = B.blk (T ^ n) v := by
  induction n generalizing v with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (B.blk_id v).symm
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, blkEquivOf_apply, ← blk_comp, pow_succ']
    rfl

theorem blkEquivOf_pow_eq_one {n : ℕ} (hT : T ^ n = 1) : B.blkEquivOf T T' h1 h2 ^ n = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [blkEquivOf_pow_apply, hT]
  exact B.blk_id v

theorem blkEquivOf_mem_orthogonalGroup (hT : ∀ x, B.qM (T x) = B.qM x) :
    B.blkEquivOf T T' h1 h2 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => B.Q_blk T hT v

end QBlock

@[expose] def pairBlock (P : HypPair Q) : QBlock Q (K × K) where
  ι :=
    { toFun := fun y => y.1 • P.e + y.2 • P.f
      map_add' := fun y z => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
      map_smul' := fun c y => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, smul_add,
          mul_smul] }
  m :=
    { toFun := fun v => (polar Q v P.f, polar Q v P.e)
      map_add' := fun v w => by simp [polar_add_left]
      map_smul' := fun c v => by simp [polar_smul_left] }
  qM y := y.1 * y.2
  m_ι y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, polar_add_left, polar_smul_left, P.polar_ef,
      P.polar_fe, P.polar_ee, P.polar_ff, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  Q_add v y hv := by
    have h1 : polar Q v P.f = 0 := congrArg Prod.fst hv
    have h2 : polar Q v P.e = 0 := congrArg Prod.snd hv
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [QuadraticMap.map_add Q, Q_pair P, polar_add_right, polar_smul_right, polar_smul_right, h1,
      h2]
    ring

theorem pairBlock_ι (P : HypPair Q) (y : K × K) : (pairBlock P).ι y = y.1 • P.e + y.2 • P.f :=
  rfl

theorem pairBlock_m (P : HypPair Q) (v : V) : (pairBlock P).m v = (polar Q v P.f, polar Q v P.e) :=
  rfl

theorem pairBlock_m_ι_of_orth {P P' : HypPair Q} (h : P.Orth P') (y : K × K) :
    (pairBlock P').m ((pairBlock P).ι y) = 0 := by
  have a1 : polar Q P.e P'.f = 0 := h.ef
  have a2 : polar Q P.f P'.f = 0 := h.ff
  have a3 : polar Q P.e P'.e = 0 := h.ee
  have a4 : polar Q P.f P'.e = 0 := h.fe
  simp [pairBlock_m, pairBlock_ι, polar_add_left, polar_smul_left, a1, a2, a3, a4]

@[expose] def diagT (ζ : K) : K × K →ₗ[K] K × K := LinearMap.prodMap (ζ • LinearMap.id)
  (ζ⁻¹ • LinearMap.id)

theorem diagT_apply (ζ : K) (y : K × K) : diagT ζ y = (ζ * y.1, ζ⁻¹ * y.2) := rfl

theorem diagT_comp {ζ : K} (hζ : ζ ≠ 0) : diagT ζ ∘ₗ diagT ζ⁻¹ = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  simp [diagT_apply, hζ]

theorem diagT_comp' {ζ : K} (hζ : ζ ≠ 0) : diagT ζ⁻¹ ∘ₗ diagT ζ = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  simp [diagT_apply, hζ]

theorem diagT_pow (ζ : K) (n : ℕ) : diagT ζ ^ n = diagT (ζ ^ n) := by
  induction n with
  | zero => exact LinearMap.ext fun y => by simp [diagT_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    refine LinearMap.ext fun y => Prod.ext ?_ ?_
    · change ζ ^ n * (ζ * y.1) = ζ ^ (n + 1) * y.1
      ring
    · change (ζ ^ n)⁻¹ * (ζ⁻¹ * y.2) = (ζ ^ (n + 1))⁻¹ * y.2
      rw [pow_succ, mul_inv]
      ring

theorem diagT_qM {ζ : K} (hζ : ζ ≠ 0) (P : HypPair Q) (y : K × K) :
    (pairBlock P).qM (diagT ζ y) = (pairBlock P).qM y := by
  change ζ * y.1 * (ζ⁻¹ * y.2) = y.1 * y.2
  field_simp

end Blocks

section SL2

theorem exists_sl2_order {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K ^ 2 - 1) :
    ∃ x : Matrix (Fin 2) (Fin 2) K, x.det = 1 ∧ x ^ p = 1 ∧ x ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact hpq.trans (dvd_mul_left _ _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) K) p
    hdvd
  refine ⟨(x : Matrix (Fin 2) (Fin 2) K), x.2, ?_, ?_⟩
  · have h1 : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) K =>
      (y : Matrix (Fin 2) (Fin 2) K)) h1
    simpa using this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm

end SL2

section Bridge

variable {d : TauCeti.ValidLieTypeIndex} {K V : Type} [Field K] [Finite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_hyperGen_of_stable_cube {π : elementaryGroup Q →* Cat d}
    (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {E : Subgroup (elementaryGroup Q)} (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hWQ : ∀ x ∈ W, Q x = 0)
    (hWE : ∀ g ∈ E, ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, -, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩
  have hker := not_dvd_card_ker_of_scalar hc hp hp2
  have hinj : ∀ x ∈ E, π x = 1 → x = 1 := by
    intro x hx hπx
    have hxk : x ∈ π.ker := hπx
    have hxp : x ^ p = 1 := hE.2 x hx
    by_contra hx1
    have hord : orderOf (⟨x, hxk⟩ : π.ker) = p :=
      orderOf_eq_prime (Subtype.ext (by simpa using hxp)) (fun h => hx1 (congrArg Subtype.val h))
    exact hker (hord ▸ orderOf_dvd_natCard _)
  have hcard' : Nat.card (E.map π) = p ^ 3 := by
    rw [← hEcard]
    refine (Nat.card_congr (Equiv.ofBijective (fun x : E => (⟨π x, x, x.2, rfl⟩ : E.map π))
      ⟨fun a b hab => ?_, fun y => ?_⟩)).symm
    · have h1 : π a = π b := congrArg Subtype.val hab
      have h2 : π ((a : elementaryGroup Q) * (b : elementaryGroup Q)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := hinj _ (E.mul_mem a.2 (E.inv_mem b.2)) h2
      exact Subtype.ext (mul_inv_eq_one.mp h3)
    · obtain ⟨_, x, hx, rfl⟩ := y
      exact ⟨⟨x, hx⟩, rfl⟩
  have hE' : IsElemAbelian p (E.map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE π
  refine ⟨E.map π, hE', hcard', hyperGen_top_of_singular_stable hc.nondegenerate rfl π
    hc.surjective hp hp2 hpK hker hE' hcard' hW0 hWQ fun g hg u hu => ?_⟩
  obtain ⟨a, ha, hag⟩ := hg
  have hz : a⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
  obtain ⟨c, hcs⟩ := mem_scalars.mp (hc.ker_scalar _ hz)
  have hgz : (g : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) * ((a⁻¹ * g : elementaryGroup Q) : V ≃ₗ[K] V) := by
    simp
  rw [hgz, LinearEquiv.mul_apply]
  refine hWE a ha _ ?_
  rw [hcs]
  exact W.smul_mem _ hu

end Bridge

end CFSG.LieType.SeitzGeneration
