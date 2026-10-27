module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.CentralAbelian
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.AutTwoGroup
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists Subgroup
open scoped commutatorElement

section Commutator

variable {G : Type*} [Group G]

private theorem commutator_sq_eq_one {a b : G} (hz : ⁅a, b⁆ ∈ center G)
    (hb : a * b ^ 2 = b ^ 2 * a) : ⁅a, b⁆ ^ 2 = 1 := by
  set z := ⁅a, b⁆ with hzdef
  have h1 : a * b = z * b * a := by rw [hzdef, commutatorElement_def]; group
  have hzb : b * z = z * b := mem_center_iff.1 hz b
  have h2 : z ^ 2 * (b ^ 2 * a) = b ^ 2 * a := by
    calc z ^ 2 * (b ^ 2 * a) = z * b * (z * b * a) := by
          simp only [sq, mul_assoc]; rw [← mul_assoc b z (b * a), hzb, mul_assoc]
      _ = a * b ^ 2 := by rw [← h1, ← mul_assoc, ← h1, sq, mul_assoc]
      _ = b ^ 2 * a := hb
  exact mul_eq_right.1 h2

end Commutator

section Linear

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_pow_eq_one_of_algHom [Nonempty ι] {F : Type*} [Field F] [Algebra K F]
    (φ : F →ₐ[K] Matrix ι ι K) {x y : GL ι K} (hx : ∀ a, Commute (x : Matrix ι ι K) (φ a))
    (hy : ∀ a, Commute (y : Matrix ι ι K) (φ a)) {ζ : F}
    (h : (y : Matrix ι ι K) * x = φ ζ * x * y) :
    ∃ m, 0 < m ∧ m ≤ Fintype.card ι ∧ m * Module.finrank K F = Fintype.card ι ∧ ζ ^ m = 1 := by
  let : Module F (ι → K) := Module.compHom (ι → K) φ.toRingHom
  have : IsScalarTower K F (ι → K) := ⟨fun k a v => by
    change φ (k • a) *ᵥ v = k • (φ a *ᵥ v)
    rw [map_smul, smul_mulVec]⟩
  let lin : ∀ M : Matrix ι ι K, (∀ a, Commute M (φ a)) → (ι → K) →ₗ[F] (ι → K) := fun M hM =>
    { toFun := fun v => M *ᵥ v
      map_add' := mulVec_add M
      map_smul' := fun a v => by
        change M *ᵥ (φ a *ᵥ v) = φ a *ᵥ (M *ᵥ v)
        rw [mulVec_mulVec, mulVec_mulVec, (hM a).eq] }
  have hdet : ∀ (u : GL ι K) (hu : ∀ a, Commute (u : Matrix ι ι K) (φ a)),
      LinearMap.det (lin u hu) ≠ 0 := by
    intro u hu h0
    have hu' : ∀ a, Commute ((u⁻¹ : GL ι K) : Matrix ι ι K) (φ a) :=
      fun a => (hu a).units_inv_left
    have hid : (lin u hu).comp (lin _ hu') = LinearMap.id := LinearMap.ext fun v => by
      change (u : Matrix ι ι K) *ᵥ (((u⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    have := congrArg LinearMap.det hid
    rw [LinearMap.det_comp, h0, zero_mul, LinearMap.det_id] at this
    exact zero_ne_one this
  have hcomp : (lin y hy).comp (lin x hx) = ζ • (lin x hx).comp (lin y hy) := by
    refine LinearMap.ext fun v => ?_
    change (y : Matrix ι ι K) *ᵥ ((x : Matrix ι ι K) *ᵥ v) =
      φ ζ *ᵥ ((x : Matrix ι ι K) *ᵥ ((y : Matrix ι ι K) *ᵥ v))
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, h, Matrix.mul_assoc]
  have htower := Module.finrank_mul_finrank K F (ι → K)
  rw [Module.finrank_fintype_fun_eq_card] at htower
  have hcard := Fintype.card_pos (α := ι)
  refine ⟨Module.finrank F (ι → K), Nat.pos_of_ne_zero fun h0 => ?_,
    Nat.le_of_dvd hcard (Dvd.intro_left _ htower), by rw [mul_comm]; exact htower, ?_⟩
  · rw [h0, mul_zero] at htower
    omega
  · have hd := congrArg LinearMap.det hcomp
    rw [LinearMap.det_smul, LinearMap.det_comp, LinearMap.det_comp,
      mul_comm (LinearMap.det (lin y hy))] at hd
    exact mul_right_cancel₀ (mul_ne_zero (hdet x hx) (hdet y hy)) (by rw [one_mul]; exact hd.symm)

private theorem trace_eq_zero_and_even (hK : ringChar K ≠ 2) {g h z : GL ι K}
    (hz : (z : Matrix ι ι K) = -1) (hgh : h * g = z * g * h) :
    trace (g : Matrix ι ι K) = 0 ∧ Even (Fintype.card ι) := by
  have hM : (h : Matrix ι ι K) * (g : Matrix ι ι K) = -((g : Matrix ι ι K) * (h : Matrix ι ι K)) := by
    have := congrArg (fun w : GL ι K => (w : Matrix ι ι K)) hgh
    simpa [hz] using this
  constructor
  · have h1 : trace ((h : Matrix ι ι K) * (g : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K)) = trace (g : Matrix ι ι K) := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hM, Matrix.neg_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, trace_neg] at h1
    exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hK).1 h1
  · have h1 := congrArg det hM
    rw [det_mul, det_neg, det_mul, mul_comm (det (h : Matrix ι ι K))] at h1
    have hne : det (g : Matrix ι ι K) * det (h : Matrix ι ι K) ≠ 0 :=
      mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
        ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
    have h2 : (-1 : K) ^ Fintype.card ι = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; exact h1.symm)
    exact (neg_one_pow_eq_one_iff_even (Ring.neg_one_ne_one_of_char_ne_two hK)).1 h2

theorem card_quotient_le_of_trace {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (ρ : G →* GL ι K) (htr : ∀ g ∉ N, trace (ρ g : Matrix ι ι K) = 0)
    (hn : (Fintype.card ι : K) ≠ 0) : Nat.card (G ⧸ N) ≤ Fintype.card ι ^ 2 := by
  classical
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hρ : ∀ a b : G, (ρ a : Matrix ι ι K) * ρ b = ρ (a * b) := fun a b => by
    rw [map_mul, Units.val_mul]
  have hli : LinearIndependent K fun q : G ⧸ N => (ρ q.out : Matrix ι ι K) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun M => trace (M * (ρ j.out⁻¹ : Matrix ι ι K))) hc
    simp only [Finset.sum_mul, smul_mul_assoc, hρ, trace_sum, trace_smul, Matrix.zero_mul,
      trace_zero] at h1
    rw [Finset.sum_eq_single j (fun q _ hq => ?_) (by simp), mul_inv_cancel, map_one,
      Units.val_one, trace_one, smul_eq_mul] at h1
    · exact (mul_eq_zero.1 h1).resolve_right hn
    · rw [htr _ fun hmem => hq ?_, smul_zero]
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' j]
      exact QuotientGroup.eq_iff_div_mem.2 (by rwa [div_eq_mul_inv])
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Module.finrank_self, mul_one] at this
  rw [Nat.card_eq_fintype_card, sq]
  exact this

theorem mem_commutant_of_mem_center {Y : Subgroup (GL ι K)} {z : Y}
    (hz : z ∈ center Y) : ((z : GL ι K) : Matrix ι ι K) ∈ commutant Y :=
  mem_commutant.2 fun g hg => by
    have := congrArg (fun w : Y => ((w : GL ι K) : Matrix ι ι K)) (mem_center_iff.1 hz ⟨g, hg⟩)
    simpa using this

variable [Finite K]

theorem exists_pow_eq_one_of_mul_eq [Nonempty ι] {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) {x y z : Y} (hz : z ∈ center Y) (h : y * x = z * x * y) :
    ∃ m, 0 < m ∧ m ≤ Fintype.card ι ∧ m * Module.finrank K (commutant Y) = Fintype.card ι ∧
      z ^ m = 1 := by
  let : Field (commutant Y) := commutantField hirr
  let : Algebra K (commutant Y) := (commutant Y).algebra
  have hc : ∀ (w : Y) (a : commutant Y),
      Commute ((w : GL ι K) : Matrix ι ι K) ((commutant Y).val a) :=
    fun w a => mem_commutant.1 a.2 w w.2
  obtain ⟨m, hm0, hm, hdeg, hζ⟩ := exists_pow_eq_one_of_algHom (commutant Y).val (hc x) (hc y)
    (ζ := ⟨_, mem_commutant_of_mem_center hz⟩) (by
      have := congrArg (fun w : Y => ((w : GL ι K) : Matrix ι ι K)) h
      simpa using this)
  refine ⟨m, hm0, hm, hdeg, Subtype.ext (Units.ext ?_)⟩
  have := congrArg Subtype.val hζ
  simpa using this

theorem isCyclic_of_injective_center [Nonempty ι] {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) {G : Type*} [Group G] [Finite G] (f : G →* Y)
    (hf : Function.Injective f) (hc : ∀ g, f g ∈ center Y) : IsCyclic G := by
  let : Field (commutant Y) := commutantField hirr
  let φ : G →* commutant Y :=
    { toFun := fun g => ⟨_, mem_commutant_of_mem_center (hc g)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  exact isCyclic_of_subgroup_isDomain φ fun a b hab =>
    hf (Subtype.ext (Units.ext (congrArg Subtype.val hab)))

private theorem coe_eq_neg_one [Nonempty ι] {Y : Subgroup (GL ι K)} (hirr : IsIrreducibleOn Y)
    {z : Y} (hz : z ∈ center Y) (h2 : z ^ 2 = 1) (h1 : z ≠ 1) :
    ((z : GL ι K) : Matrix ι ι K) = -1 := by
  let : Field (commutant Y) := commutantField hirr
  set ζ : commutant Y := ⟨_, mem_commutant_of_mem_center hz⟩
  have hζ : ζ * ζ = 1 := Subtype.ext (by
    simpa [sq] using congrArg (fun w : Y => ((w : GL ι K) : Matrix ι ι K)) h2)
  rcases mul_self_eq_one_iff.1 hζ with h | h
  · exact absurd (Subtype.ext (Units.ext (congrArg Subtype.val h))) h1
  · exact congrArg Subtype.val h

end Linear

section Normal

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem eq_two_of_noncomm [Nonempty ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) {s : ℕ} (hs : s.Prime) (hs3 : s ≠ 3) {C : Subgroup Y}
    (hCs : IsPGroup s C) (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) {x y : Y} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : y * x ≠ x * y) : s = 2 := by
  set z := ⁅y, x⁆ with hzdef
  have hyx : y * x = z * x * y := by rw [hzdef, commutatorElement_def]; group
  obtain ⟨m, hm0, hm, -, hzm⟩ := exists_pow_eq_one_of_mul_eq hirr (hcomm y hy x hx) hyx
  have hzC : z ∈ C := by
    rw [hzdef, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hx) (inv_mem hy)) (inv_mem hx)
  obtain ⟨k, hk⟩ := hCs ⟨z, hzC⟩
  have hzk : z ^ s ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hs).1 (orderOf_dvd_of_pow_eq_one hzk)
  have hz1 : z ≠ 1 := fun h => hxy (by rw [hyx, h, one_mul])
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hsm : s ∣ m := (dvd_pow_self s hj0).trans (hj ▸ orderOf_dvd_of_pow_eq_one hzm)
  have h4 : s ≤ 4 := (Nat.le_of_dvd hm0 hsm).trans (hm.trans hι)
  have := hs.two_le
  interval_cases s
  · rfl
  · exact absurd rfl hs3
  · exact absurd hs (by norm_num)

private theorem trace_eq_zero_of_noncomm [Nonempty ι] {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) (hK : ringChar K ≠ 2) {C : Subgroup Y}
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) (hpow : ∀ x ∈ C, x ^ 2 ∈ center Y) {a b : Y}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a * b ≠ b * a) :
    trace ((b : GL ι K) : Matrix ι ι K) = 0 ∧ Even (Fintype.card ι) := by
  have hz := hcomm a ha b hb
  have hab' : a * b = ⁅a, b⁆ * b * a := by rw [commutatorElement_def]; group
  have hz2 : ⁅a, b⁆ ^ 2 = 1 := commutator_sq_eq_one hz (mem_center_iff.1 (hpow b hb) a)
  have hz1 : ⁅a, b⁆ ≠ 1 := fun h => hab (by rw [hab', h, one_mul])
  exact trace_eq_zero_and_even hK (coe_eq_neg_one hirr hz hz2 hz1) (congrArg Subtype.val hab')

theorem card_quotient_center_le_sixteen [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hirr : IsIrreducibleOn Y) (hK : ringChar K ≠ 2) {C : Subgroup Y}
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) (hpow : ∀ x ∈ C, x ^ 2 ∈ center Y) {x y : Y}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : y * x ≠ x * y) : Nat.card (C ⧸ center C) ≤ 16 := by
  have hn : (Fintype.card ι : K) ≠ 0 := by
    obtain ⟨r, hr⟩ := (trace_eq_zero_of_noncomm hirr hK hcomm hpow hy hx hxy).2
    have h0 := Fintype.card_pos (α := ι)
    have h2 := Ring.two_ne_zero hK
    have hr' : ((r + r : ℕ) : K) = 2 * r := by push_cast; ring
    rw [hr, hr']
    refine mul_ne_zero h2 ?_
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · simp
    · exact_mod_cast h2
  calc Nat.card (C ⧸ center C) ≤ Fintype.card ι ^ 2 :=
        card_quotient_le_of_trace (Y.subtype.comp C.subtype) (fun b hb => ?_) hn
    _ ≤ 16 := by nlinarith
  rw [mem_center_iff] at hb
  push Not at hb
  obtain ⟨a, ha⟩ := hb
  exact (trace_eq_zero_of_noncomm hirr hK hcomm hpow a.2 b.2 fun h => ha (Subtype.ext h)).1

private theorem centralizes_of_two [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y)
    (h3 : Nat.Coprime 3 (Nat.card Y)) (hK : ringChar K ≠ 2) {C : Subgroup Y} [C.Normal]
    (hCs : IsPGroup 2 C) (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y)
    (hpow : ∀ x ∈ C, x ^ 2 ∈ center Y)
    (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) {x y : Y} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : y * x ≠ x * y) (g : Y) {c : Y} (hc : c ∈ C) : g * c * g⁻¹ = c := by
  have hsq : ∀ a : C, a ^ 2 ∈ center C := fun a =>
    mem_center_iff.2 fun b => Subtype.ext (by simpa using mem_center_iff.1 (hpow a a.2) b)
  have hcyc : IsCyclic (center C) :=
    isCyclic_of_injective_center hirr (C.subtype.comp (center C).subtype)
      (C.subtype_injective.comp (center C).subtype_injective) fun a =>
        hcen _ a.1.2 fun b hb => by simpa using congrArg Subtype.val (mem_center_iff.1 a.2 ⟨b, hb⟩)
  have := hY
  have hG := eq_bot_of_isPerfect_of_coprime_three hCs hcyc hsq
    (card_quotient_center_le_sixteen hι hirr hK hcomm hpow hx hy hxy)
    (G := (MulAut.conjNormal : Y →* MulAut C).range) (Group.IsPerfect.range _)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_range_dvd _) h3)
  have h1 : MulAut.conjNormal g = (1 : MulAut C) := by
    have : MulAut.conjNormal g ∈ (MulAut.conjNormal : Y →* MulAut C).range := ⟨g, rfl⟩
    rwa [hG] at this
  have := congrArg (fun α : MulAut C => ((α ⟨c, hc⟩ : C) : Y)) h1
  simpa [MulAut.conjNormal_apply] using this

private theorem centralizes_of_interface [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y)
    (h3 : Nat.Coprime 3 (Nat.card Y)) {s : ℕ} (hs : s.Prime) (hs3 : s ≠ 3)
    (hsK : s ≠ ringChar K) {C : Subgroup Y} [C.Normal] (hCs : IsPGroup s C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) (hpow : ∀ x ∈ C, x ^ s ∈ center Y)
    (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) (g : Y) {c : Y} (hc : c ∈ C) :
    g * c * g⁻¹ = c := by
  by_cases hab : ∀ x ∈ C, ∀ y ∈ C, y * x = x * y
  · rw [mem_center_iff.1 (hcen c hc (hab c hc)) g, mul_inv_cancel_right]
  push Not at hab
  obtain ⟨x, hx, y, hy, hxy⟩ := hab
  obtain rfl : s = 2 := eq_two_of_noncomm hι hirr hs hs3 hCs hcomm hx hy hxy
  exact centralizes_of_two hι hY hirr h3 (Ne.symm hsK) hCs hcomm hpow hcen hx hy hxy g hc

theorem le_center_of_forall_fix {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {s : ℕ} [hs : Fact s.Prime] {P : Subgroup G} [P.Normal] {C : Subgroup P}
    (hthomp : ∀ α : MulAut P, Nat.Coprime (orderOf α) s → (∀ x ∈ C, α x = x) → α = 1)
    (hfix : ∀ g : G, ∀ c : P, c ∈ C → g * (c : G) * g⁻¹ = c) : P ≤ center G := by
  let f : G →* MulAut P := MulAut.conjNormal
  have hR : IsPGroup s f.range := by
    rintro ⟨_, g, rfl⟩
    set n := orderOf (f g)
    have hn : n ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos (orderOf_map_dvd f g)
      (orderOf_pos g))
    refine ⟨n.factorization s, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    refine hthomp _ ?_ fun c hc => Subtype.ext ?_
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ hs.out.ne_zero) (Nat.ordProj_dvd n s)]
      exact (Nat.coprime_ordCompl hs.out hn).symm
    · rw [← map_pow, MulAut.conjNormal_apply]
      exact hfix _ c hc
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : f.range = ⊥ := by
    by_contra hne
    have : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent f.range hR.isNilpotent
  intro x hx
  refine mem_center_iff.2 fun g => ?_
  have h1 : f g = 1 := by
    have : f g ∈ f.range := ⟨g, rfl⟩
    rwa [hbot] at this
  have := congrArg (fun α : MulAut P => ((α ⟨x, hx⟩ : P) : G)) h1
  simp only [f, MulAut.conjNormal_apply, MulAut.one_apply] at this
  exact (mul_inv_eq_iff_eq_mul.1 this)

theorem critical_center_le_center (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hY : Group.IsPerfect Y) {s : ℕ} [hs : Fact s.Prime]
    (hsK : s ≠ ringChar K) {P : Subgroup Y} [P.Normal] (hPs : IsPGroup s P) {C : Subgroup P}
    (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C) :
    (C ⊓ centralizer (C : Set P)).map P.subtype ≤ center Y := by
  have := hC.1
  have : (centralizer (C : Set P)).Characteristic :=
    CFSG.SectionRank.Ccomm.characteristic_centralizer C
  have : (C ⊓ centralizer (C : Set P)).Characteristic :=
    CFSG.SectionRank.Ccomm.characteristic_inf _ _
  have hp : IsPGroup s ((C ⊓ centralizer (C : Set P)).map P.subtype) :=
    (hPs.to_subgroup _).of_equiv
      ((C ⊓ centralizer (C : Set P)).equivMapOfInjective _ P.subtype_injective)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  refine le_center_of_normal_of_isMulCommutative hι hY inferInstance ⟨⟨fun a b => ?_⟩⟩ ?_
  · obtain ⟨_, a, ha, rfl⟩ := a
    obtain ⟨_, b, hb, rfl⟩ := b
    exact Subtype.ext (congrArg Subtype.val (mem_centralizer_iff.1 ha.2 b hb.1)).symm
  · rw [hk]
    exact ((Nat.coprime_primes (CharP.char_is_prime K (ringChar K)) hs.out).2
      (Ne.symm hsK)).pow_right k

theorem critical_interface {G : Type*} [Group G] [Finite G] {s : ℕ} [Fact s.Prime]
    {P : Subgroup G} (hPs : IsPGroup s P) {C : Subgroup P}
    (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C)
    (hZ : (C ⊓ centralizer (C : Set P)).map P.subtype ≤ center G) :
    (∀ x ∈ C.map P.subtype, ∀ y ∈ C.map P.subtype, ⁅x, y⁆ ∈ center G) ∧
      (∀ x ∈ C.map P.subtype, x ^ s ∈ center G) ∧
      ∀ x ∈ C.map P.subtype, (∀ y ∈ C.map P.subtype, y * x = x * y) → x ∈ center G := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hZ (mem_map_of_mem P.subtype
      (hC.2.2.1 (commutator_mem_commutator (mem_top a) hb)))
    simpa [commutatorElement_def] using this
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := CFSG.SectionRank.Ccomm.pow_mem_frattini (hPs.to_subgroup C) ⟨a, ha⟩
    have := hZ (mem_map_of_mem P.subtype (hC.2.1 (mem_map_of_mem C.subtype h1)))
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩ hcom
    refine hZ (mem_map_of_mem P.subtype ⟨ha, mem_centralizer_iff.2 fun b hb => ?_⟩)
    exact Subtype.ext (hcom b (mem_map_of_mem P.subtype hb))

end Normal

theorem le_center_of_normal_of_isPGroup {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y)
    (h3 : Nat.Coprime 3 (Nat.card Y)) {s : ℕ} (hs : s.Prime) (hsK : s ≠ ringChar K)
    {P : Subgroup Y} (hP : P.Normal) (hPs : IsPGroup s P) : P ≤ Subgroup.center Y := by
  by_cases hs3 : s = 3
  · subst hs3
    intro x hx
    obtain ⟨k, hk⟩ := hPs ⟨x, hx⟩
    have h1 : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ Nat.gcd (3 ^ k) (Nat.card Y) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard x)
    rw [Nat.Coprime.gcd_eq_one (h3.pow_left k), Nat.dvd_one, orderOf_eq_one_iff] at h2
    rw [h2]
    exact one_mem _
  rcases isEmpty_or_nonempty ι with hι0 | hι0
  · exact fun x _ => mem_center_iff.2 fun g =>
      Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))
  have : Fact s.Prime := ⟨hs⟩
  have := hY
  have := hP
  obtain ⟨C, hC, -, hthomp⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical hPs
  obtain ⟨hcomm, hpow, hcen⟩ :=
    critical_interface hPs hC (critical_center_le_center hι hY hsK hPs hC)
  have := hC.1
  refine le_center_of_forall_fix hthomp fun g c hc => ?_
  exact centralizes_of_interface hι hY hirr h3 hs hs3 hsK
    ((hPs.to_subgroup C).of_equiv (C.equivMapOfInjective _ P.subtype_injective)) hcomm hpow
    hcen g (mem_map_of_mem P.subtype hc)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
