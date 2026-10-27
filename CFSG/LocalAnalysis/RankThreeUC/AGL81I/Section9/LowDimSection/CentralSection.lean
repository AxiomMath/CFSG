module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.AutTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.AutThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.CentralNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists Subgroup
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

private theorem dvd_of_pow_eq_one_of_isPGroup {s : ℕ} (hs : s.Prime) {C : Subgroup G}
    (hC : IsPGroup s C) {z : G} (hz : z ∈ C) (hz1 : z ≠ 1) {m : ℕ} (hm : z ^ m = 1) : s ∣ m := by
  obtain ⟨k, hk⟩ := hC ⟨z, hz⟩
  have hzk : z ^ s ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hs).1 (orderOf_dvd_of_pow_eq_one hzk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.1 (by simpa using hj))
  exact (dvd_pow_self s hj0).trans (hj ▸ orderOf_dvd_of_pow_eq_one hm)

private theorem mem_center_of_coe_mem_center {C : Subgroup G} {a : C} (h : (a : G) ∈ center G) :
    a ∈ center C :=
  mem_center_iff.2 fun b => Subtype.ext (by simpa using mem_center_iff.1 h b)

end Group

section Linear

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem trace_eq_zero_of_scalar {g h z : GL ι K} {c : K} (hz : (z : Matrix ι ι K) = c • 1)
    (hc : c ≠ 1) (hgh : h * g = z * g * h) : trace (g : Matrix ι ι K) = 0 := by
  have hM : (h : Matrix ι ι K) * (g : Matrix ι ι K) =
      c • ((g : Matrix ι ι K) * (h : Matrix ι ι K)) := by
    have := congrArg (fun w : GL ι K => (w : Matrix ι ι K)) hgh
    simpa [hz, Matrix.mul_assoc] using this
  have h1 : trace ((h : Matrix ι ι K) * (g : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K)) =
      trace (g : Matrix ι ι K) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [hM, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, trace_smul,
    smul_eq_mul] at h1
  have : (c - 1) * trace (g : Matrix ι ι K) = 0 := by rw [sub_mul, h1]; ring
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem exists_eq_smul_one_of_finrank {Y : Subgroup (GL ι K)}
    (hdeg : Module.finrank K (commutant Y) = 1) {z : Y} (hz : z ∈ center Y) :
    ∃ c : K, ((z : GL ι K) : Matrix ι ι K) = c • 1 := by
  have hbot := Subalgebra.eq_bot_of_finrank_one hdeg
  have hmem := mem_commutant_of_mem_center hz
  rw [hbot, Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

theorem card_quotient_center_le_of_scalar [Finite K] {Y : Subgroup (GL ι K)}
    (hscal : ∀ z ∈ center Y, ∃ c : K, ((z : GL ι K) : Matrix ι ι K) = c • 1)
    (hn : (Fintype.card ι : K) ≠ 0) {C : Subgroup Y}
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) :
    Nat.card (C ⧸ center C) ≤ Fintype.card ι ^ 2 := by
  refine card_quotient_le_of_trace (Y.subtype.comp C.subtype) (fun b hb => ?_) hn
  rw [mem_center_iff] at hb
  push Not at hb
  obtain ⟨a, ha⟩ := hb
  have hz := hcomm (a : Y) a.2 (b : Y) b.2
  obtain ⟨c, hc⟩ := hscal _ hz
  have hab : (a : Y) * (b : Y) = ⁅(a : Y), (b : Y)⁆ * (b : Y) * (a : Y) := by
    rw [commutatorElement_def]; group
  refine trace_eq_zero_of_scalar hc (fun h1 => ha (Subtype.ext ?_)) (congrArg Subtype.val hab)
  have h1' : ⁅(a : Y), (b : Y)⁆ = 1 := Subtype.ext (Units.ext (by rw [hc, h1, one_smul]; rfl))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hab, h1', one_mul]

end Linear

section Normal

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_dvd_of_noncomm [Nonempty ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) {s : ℕ} (hs : s.Prime) {C : Subgroup Y} (hCs : IsPGroup s C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) {x y : Y} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : y * x ≠ x * y) :
    ∃ m, 0 < m ∧ s ∣ m ∧ m ≤ 4 ∧ m * Module.finrank K (commutant Y) = Fintype.card ι := by
  set z := ⁅y, x⁆ with hzdef
  have hyx : y * x = z * x * y := by rw [hzdef, commutatorElement_def]; group
  obtain ⟨m, hm0, hm, hdeg, hzm⟩ := exists_pow_eq_one_of_mul_eq hirr (hcomm y hy x hx) hyx
  have hzC : z ∈ C := by
    rw [hzdef, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hx) (inv_mem hy)) (inv_mem hx)
  have hz1 : z ≠ 1 := fun h => hxy (by rw [hyx, h, one_mul])
  exact ⟨m, hm0, dvd_of_pow_eq_one_of_isPGroup hs hCs hzC hz1 hzm, hm.trans hι, hdeg⟩

theorem isCyclic_center_of_le [Nonempty ι] {Y : Subgroup (GL ι K)} (hirr : IsIrreducibleOn Y)
    {C : Subgroup Y} (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) :
    IsCyclic (center C) :=
  isCyclic_of_injective_center hirr (C.subtype.comp (center C).subtype)
    (C.subtype_injective.comp (center C).subtype_injective) fun a =>
      hcen _ a.1.2 fun b hb => by simpa using congrArg Subtype.val (mem_center_iff.1 a.2 ⟨b, hb⟩)

theorem alt_of_mulAut_two_of_noncomm [Nonempty ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y) (hK : ringChar K ≠ 2) {C : Subgroup Y}
    [C.Normal] (hCs : IsPGroup 2 C) (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y)
    (hpow : ∀ x ∈ C, x ^ 2 ∈ center Y)
    (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) {x y : Y} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : y * x ≠ x * y) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (ψ : (MulAut.conjNormal : Y →* MulAut C).range →* S)
    (hψ : Function.Surjective ψ) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  have := hY
  exact nonempty_alt_of_mulAut_two hCs (isCyclic_center_of_le hirr hcen)
    (fun a => mem_center_of_coe_mem_center (by simpa using hpow _ a.2))
    (card_quotient_center_le_sixteen hι hirr hK hcomm hpow hx hy hxy) (Group.IsPerfect.range _)
    hS ψ hψ

theorem card_quotient_center_le_nine [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hirr : IsIrreducibleOn Y) (hK : ringChar K ≠ 3) {C : Subgroup Y}
    (hCs : IsPGroup 3 C) (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y) {x y : Y} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : y * x ≠ x * y) : Nat.card (C ⧸ center C) ≤ 9 := by
  obtain ⟨m, hm0, ⟨k, rfl⟩, hm4, hdeg⟩ :=
    exists_dvd_of_noncomm hι hirr Nat.prime_three hCs hcomm hx hy hxy
  obtain rfl : k = 1 := by omega
  have := Fintype.card_pos (α := ι)
  have hd : Module.finrank K (commutant Y) = 1 := by omega
  have hn : Fintype.card ι = 3 := by omega
  have h3 : ((3 : ℕ) : K) ≠ 0 := fun h => hK <| (Nat.prime_dvd_prime_iff_eq
    (CharP.char_is_prime K (ringChar K)) Nat.prime_three).1 ((CharP.cast_eq_zero_iff K _ 3).1 h)
  have := card_quotient_center_le_of_scalar (fun z hz => exists_eq_smul_one_of_finrank hd hz)
    (by rwa [hn]) hcomm
  rwa [hn] at this

theorem false_of_mulAut_three_of_noncomm [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y)
    (hK : ringChar K ≠ 3) {C : Subgroup Y} [C.Normal] (hCs : IsPGroup 3 C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y)
    (hpow : ∀ x ∈ C, x ^ 3 ∈ center Y)
    (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) {x y : Y} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : y * x ≠ x * y) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (ψ : (MulAut.conjNormal : Y →* MulAut C).range →* S)
    (hψ : Function.Surjective ψ) : False := by
  have := hY
  have hcC : commutator C ≤ center C := by
    rw [commutator_def, commutator_le]
    exact fun a _ b _ => mem_center_of_coe_mem_center
      (by simpa [commutatorElement_def] using hcomm _ a.2 _ b.2)
  exact false_of_mulAut_three hCs (isCyclic_center_of_le hirr hcen) hcC
    (fun a => mem_center_of_coe_mem_center (by simpa using hpow _ a.2))
    (card_quotient_center_le_nine hι hirr hK hCs hcomm hx hy hxy) (Group.IsPerfect.range _)
    hS ψ hψ

end Normal

section Minimal

theorem map_centralizer_eq_bot {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    {C : Subgroup Y} [C.Normal] {g c : Y} (hc : c ∈ C) (hgc : g * c * g⁻¹ ≠ c) :
    (centralizer (C : Set Y)).map ψ = ⊥ := by
  refine (map_eq_bot_or_eq_top_of_normal hψ inferInstance).resolve_right fun htop =>
    hmin (centralizer (C : Set Y)) (fun h => hgc ?_) ?_
  · have hg : g ∈ centralizer (C : Set Y) := h ▸ mem_top g
    rw [← mem_centralizer_iff.1 hg c hc, mul_inv_cancel_right]
  · rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    exact htop

theorem exists_surjective_mulAut {Y S : Type*} [Group Y] [Group S] {C : Subgroup Y} [C.Normal]
    {ψ : Y →* S} (hψ : Function.Surjective ψ) (hbot : (centralizer (C : Set Y)).map ψ = ⊥) :
    ∃ ψ' : (MulAut.conjNormal : Y →* MulAut C).range →* S, Function.Surjective ψ' := by
  set f := (MonoidHom.rangeRestrict (MulAut.conjNormal : Y →* MulAut C))
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  suffices h : f.ker ≤ ψ.ker by
    refine ⟨f.liftOfSurjective hf ⟨ψ, h⟩, fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hψ x
    exact ⟨f a, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a⟩
  intro g hg
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hg
  have hgc : g ∈ centralizer (C : Set Y) := mem_centralizer_iff.2 fun c hc => by
    have := congrArg (fun α : MulAut C => ((α ⟨c, hc⟩ : C) : Y)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have := mem_map_of_mem ψ hgc
  rwa [hbot, mem_bot] at this

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem alt_of_not_centralizes [Nonempty ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) {ψ : ↥Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    {s : ℕ} (hs : s.Prime) (hsK : s ≠ ringChar K) {C : Subgroup Y} [C.Normal]
    (hCs : IsPGroup s C) (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ center Y)
    (hpow : ∀ x ∈ C, x ^ s ∈ center Y)
    (hcen : ∀ x ∈ C, (∀ y ∈ C, y * x = x * y) → x ∈ center Y) {g c : Y} (hc : c ∈ C)
    (hgc : g * c * g⁻¹ ≠ c) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  have hnc : ¬ ∀ x ∈ C, ∀ y ∈ C, y * x = x * y := fun hab =>
    hgc (by rw [mem_center_iff.1 (hcen c hc (hab c hc)) g, mul_inv_cancel_right])
  push Not at hnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨ψ', hψ'⟩ := exists_surjective_mulAut hψ (map_centralizer_eq_bot hψ hmin hc hgc)
  obtain ⟨m, hm0, hsm, hm4, -⟩ := exists_dvd_of_noncomm hι hirr hs hCs hcomm hx hy hxy
  have hs4 : s ≤ 4 := (Nat.le_of_dvd hm0 hsm).trans hm4
  have := hs.two_le
  interval_cases s
  · exact alt_of_mulAut_two_of_noncomm hι hY hirr (Ne.symm hsK) hCs hcomm hpow hcen hx hy hxy hS
      ψ' hψ'
  · exact (false_of_mulAut_three_of_noncomm hι hY hirr (Ne.symm hsK) hCs hcomm hpow hcen hx hy
      hxy hS ψ' hψ').elim
  · exact absurd hs (by norm_num)

end Minimal

theorem le_center_or_alt_of_minimal {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)}
    (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (ψ : ↥Y →* S) (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    {s : ℕ} (hs : s.Prime) (hsK : s ≠ ringChar K) {N : Subgroup Y} (hN : N.Normal)
    (hNs : IsPGroup s N) :
    N ≤ Subgroup.center Y ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rcases isEmpty_or_nonempty ι with hι0 | hι0
  · exact Or.inl fun x _ => mem_center_iff.2 fun g =>
      Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))
  have : Fact s.Prime := ⟨hs⟩
  have := hY
  have := hN
  obtain ⟨C, hC, -, hthomp⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical hNs
  obtain ⟨hcomm, hpow, hcen⟩ :=
    critical_interface hNs hC (critical_center_le_center hι hY hsK hNs hC)
  have := hC.1
  by_cases hfix : ∀ g : Y, ∀ c : N, c ∈ C → g * (c : Y) * g⁻¹ = c
  · exact Or.inl (le_center_of_forall_fix hthomp hfix)
  push Not at hfix
  obtain ⟨g, c, hc, hgc⟩ := hfix
  exact Or.inr (alt_of_not_centralizes hι hY hirr hS hψ hmin hs hsK
    ((hNs.to_subgroup C).of_equiv (C.equivMapOfInjective _ N.subtype_injective)) hcomm hpow hcen
    (mem_map_of_mem N.subtype hc) hgc)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
