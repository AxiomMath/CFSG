module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALayer
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

section Cover

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem frobGL_comp_eq' {K : Type} [Field K] {ψ ψ' : K ≃+* K} (h : ∀ c, ψ' (ψ c) = c)
    (A : GL (Fin 3) K) : frobGL ψ' (frobGL ψ A) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL]
  ext i k
  simp only [Matrix.map_apply, h]

@[expose] noncomputable def frobSL (hK : PiField π p f K) (σ : K ≃+* K) :
    MulAut ↥(slPi π 3 (p ^ f) K) where
  toFun s := ⟨frobGL σ s, frobGL_mem_slPi hK σ s.2⟩
  invFun s := ⟨frobGL σ.symm s, frobGL_mem_slPi hK σ.symm s.2⟩
  left_inv s := Subtype.ext (frobGL_comp_eq' (fun c => σ.symm_apply_apply c) s)
  right_inv s := Subtype.ext (frobGL_comp_eq' (fun c => σ.apply_symm_apply c) s)
  map_mul' _ _ := Subtype.ext (map_mul (frobGL σ) _ _)

theorem coe_frobSL (hK : PiField π p f K) (σ : K ≃+* K) (s : ↥(slPi π 3 (p ^ f) K)) :
    ((frobSL hK σ s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = frobGL σ s :=
  rfl

theorem mem_fixSub_frobSL (hK : PiField π p f K) (σ : K ≃+* K) (s : ↥(slPi π 3 (p ^ f) K)) :
    s ∈ fixSub (frobSL hK σ) ↔ frobGL σ (s : GL (Fin 3) K) = s := by
  rw [mem_fixSub]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_three_mul (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ f₀, f = 3 * f₀ := by
  have := hK.finite
  have hn : ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = p ^ n ∧ (n = f ∨ n = 2 * f) := by
    cases π
    · exact ⟨2 * f, by have := hK.one_le; omega, by
        rw [hK.card, piCard, Bool.cond_false, ← pow_mul, mul_comm], Or.inr rfl⟩
    · exact ⟨f, hK.one_le, by rw [hK.card]; rfl, Or.inl rfl⟩
  obtain ⟨n, hn1, hnK, hnf⟩ := hn
  obtain ⟨-, -, -, -, hc, -⟩ := CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
    p n hK.prime hn1 K hnK
  have h3 : 3 ∣ n := by
    rw [← hc, ← hσ]
    exact orderOf_dvd_natCard σ
  rcases hnf with rfl | rfl
  · exact h3
  · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3 : 3 ∣ f) |> fun h => by
      obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩

theorem eq_or_eq_sq_of_pow' {F : Type} [Field F] {r : ℕ} {φ ψ : F ≃+* F} (hφ : ∀ c, φ c = c ^ r)
    (hψ : (∀ c, ψ c = c ^ r) ∨ ∀ c, ψ c = c ^ (r ^ 2)) : ψ = φ ∨ ψ = φ ^ 2 := by
  rcases hψ with h | h
  · exact Or.inl (RingEquiv.ext fun c => by rw [h, hφ])
  · refine Or.inr (RingEquiv.ext fun c => ?_)
    have h2 : (φ ^ 2) c = φ (φ c) := by rw [pow_two, RingAut.mul_apply]
    rw [h, h2, hφ, hφ, ← pow_mul, pow_two]

theorem exists_fixed_data (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ (f₀ : ℕ) (φ : K ≃+* K) (K₀ : Subfield K), f = 3 * f₀ ∧
      (∀ c, φ c = c ^ piCard π (p ^ f₀)) ∧ orderOf φ = 3 ∧ (σ = φ ∨ σ = φ ^ 2) ∧
      (∀ c, c ∈ K₀ ↔ σ c = c) ∧ PiField π p f₀ K₀ := by
  have := hK.finite
  obtain ⟨f₀, hf⟩ := exists_three_mul hK hσ
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  obtain ⟨K₀, hK₀, hcard⟩ := exists_fixedField hK hf hσ
  refine ⟨f₀, φ, K₀, hf, hφ, hφ3, ?_, hK₀, ⟨hK.prime, hf₀, hcard⟩⟩
  obtain ⟨n, hn1, hnK, hnf⟩ : ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = p ^ n ∧ n = 3 * (n / 3) ∧
      piCard π (p ^ f₀) = p ^ (n / 3) := by
    cases π
    · refine ⟨2 * f, by omega, ?_, by omega, ?_⟩
      · rw [hK.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]
      · rw [piCard, Bool.cond_false, ← pow_mul]
        congr 1
        omega
    · refine ⟨f, by omega, by rw [hK.card]; rfl, by omega, ?_⟩
      rw [piCard, Bool.cond_true]
      congr 1
      omega
  obtain ⟨-, hform⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hn1 hnK hσ
  refine eq_or_eq_sq_of_pow' (r := p ^ (n / 3)) (fun c => by rw [hφ, hnf.2]) ?_
  rcases hform with h | h
  · exact Or.inl h
  · refine Or.inr fun c => ?_
    have h2 : 2 * n / 3 = n / 3 * 2 := by omega
    rw [h, h2, pow_mul]

theorem isQuasisimple_open {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨(Group.isPerfect_def (G := Q)).1 h.1, h.2.1⟩

theorem isQuasisimple_open_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : CFSG.Open.IsQuasisimple X') : CFSG.Open.IsQuasisimple X :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm h

theorem isQuasisimple_slPi (hK : PiField π p f K) (hq : π = false → p ^ f ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) := by
  have := hK.finite
  cases π
  · have : Fact p.Prime := ⟨hK.prime⟩
    have hcard : Nat.card K = (p ^ f) ^ 2 := by
      rw [hK.card, piCard, Bool.cond_false]
    have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      exact hq rfl h
    exact isQuasisimple_open
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl hnq).1
  · have h := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
    exact isQuasisimple_open_of_mulEquiv (statedSLEquiv 3 K) (isQuasisimple_open h)

structure FrobData (hK : PiField π p f K) (σ : K ≃+* K) where
  f₀ : ℕ
  φ : K ≃+* K
  K₀ : Subfield K
  hf : f = 3 * f₀
  hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)
  hφ3 : orderOf φ = 3
  hKσ : ∀ c, c ∈ K₀ ↔ σ c = c
  hKφ : ∀ c, c ∈ K₀ ↔ φ c = c
  hP : PiField π p f₀ K₀

theorem exists_frobData (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    Nonempty (FrobData hK σ) := by
  obtain ⟨f₀, φ, K₀, hf, hφ, hφ3, hσφ, hKσ, hP⟩ := exists_fixed_data hK hσ
  exact ⟨⟨f₀, φ, K₀, hf, hφ, hφ3, hKσ, fun c => (hKσ c).trans (fixed_iff_of_sq hφ3 hσφ c), hP⟩⟩

variable {hK : PiField π p f K} {σ : K ≃+* K}

@[expose] noncomputable def FrobData.incl (d : FrobData hK σ) :
    ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* ↥(slPi π 3 (p ^ f) K) where
  toFun s := ⟨subGL d.K₀ s, (subGL_mem_slPi_iff hK d.hf d.hφ d.hKφ d.hP s).2 s.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem FrobData.coe_incl (d : FrobData hK σ) (s : ↥(slPi π 3 (p ^ d.f₀) d.K₀)) :
    ((d.incl s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = subGL d.K₀ s :=
  rfl

theorem FrobData.incl_injective (d : FrobData hK σ) : Function.Injective d.incl := fun _ _ h =>
  Subtype.ext (subGL_injective d.K₀ (congrArg Subtype.val h))

theorem FrobData.mem_range_incl (d : FrobData hK σ) (s : ↥(slPi π 3 (p ^ f) K)) :
    s ∈ d.incl.range ↔ frobGL σ (s : GL (Fin 3) K) = s := by
  constructor
  · rintro ⟨t, rfl⟩
    exact frobGL_subGL d.hKσ t
  · intro h
    obtain ⟨B, hB⟩ := exists_subGL_eq d.hKσ h
    have hB' : B ∈ slPi π 3 (p ^ d.f₀) d.K₀ :=
      (subGL_mem_slPi_iff hK d.hf d.hφ d.hKφ d.hP B).1 (hB ▸ s.2)
    exact ⟨⟨B, hB'⟩, Subtype.ext hB⟩

theorem FrobData.fixSub_eq (d : FrobData hK σ) : fixSub (frobSL hK σ) = d.incl.range := by
  ext s
  rw [mem_fixSub_frobSL, d.mem_range_incl]

@[expose] noncomputable def FrobData.fixEquiv (d : FrobData hK σ) :
    ↥(fixSub (frobSL hK σ)) ≃* ↥(slPi π 3 (p ^ d.f₀) d.K₀) :=
  ((MulEquiv.subgroupCongr d.fixSub_eq).trans
    (MonoidHom.ofInjective d.incl_injective).symm)

@[expose] def FixData (Y : Type) [Group Y] (α : MulAut Y) : Prop :=
  ∃ S : Subgroup Y, S ≤ fixSub α ∧ ⁅fixSub α, fixSub α⁆ ≤ S ∧
    (∀ a ∈ fixSub α, ∃ n : ℕ, a ^ 3 ^ n ∈ S) ∧ CFSG.Open.IsQuasisimple ↥S ∧ IsL3Type ↥S ∧
    (∀ z : ↥S, z ∈ Subgroup.center ↥S → z ^ 3 = 1) ∧ 3 ∣ Nat.card ↥S ∧
    (∀ z : ↥S, z ∈ Subgroup.center ↥S → (z : Y) ∈ Subgroup.center Y) ∧
    Subgroup.center Y ≤ S ∧
    ((∃ z ∈ Subgroup.center Y, z ≠ 1) → fixSub α = S ∧ IsSLThreeEpsAny ↥S)

theorem FrobData.pow_eq (d : FrobData hK σ) : p ^ f = (p ^ d.f₀) ^ 3 :=
  (congrArg (p ^ ·) d.hf).trans (pow_mul' p 3 d.f₀)

theorem FrobData.modThree (d : FrobData hK σ) (hq : ModThree π (p ^ f)) :
    ModThree π (p ^ d.f₀) :=
  modThree_of_cube (by rw [← d.pow_eq]; exact hq)

theorem FrobData.map_center_incl (d : FrobData hK σ) (hq : ModThree π (p ^ f)) :
    (Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀)).map d.incl =
      Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
  have hq₀ := d.modThree hq
  have hle : (Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀)).map d.incl ≤
      Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_center d.hP hq₀ hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, FrobData.coe_incl, hζ, subGL_scalar]
    have hc := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar
      (Units.map (d.K₀.subtype : d.K₀ →* K) ζ) (g : GL (Fin 3) K)
    exact hc.eq
  have := hK.finite
  have : Finite ↥(slPi π 3 (p ^ f) K) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective d.incl_injective, card_center_slPi d.hP hq₀,
    card_center_slPi hK hq]

theorem pow_three_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {c : ↥(slPi π 3 (p ^ f) K)} (hc : c ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K)) : c ^ 3 = 1 := by
  obtain ⟨ζ, hζ3, hζ⟩ := exists_scalar_of_mem_center hK hq hc
  apply Subtype.ext
  rw [Subgroup.coe_pow, hζ, ← map_pow, hζ3, map_one]
  rfl

theorem center_slPi_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Subgroup.center ↥(slPi π 3 (p ^ f) K) =
      (StatedScalars (Fin 3) K).subgroupOf (slPi π 3 (p ^ f) K) := by
  ext z
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_center hK hq hz
    exact ⟨ζ, hζ.symm⟩
  · rintro ⟨c, hc⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (g : GL (Fin 3) K)).eq

theorem isL3Type_slPi_quot (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    IsL3Type (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have e := QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hq)
  cases π
  · exact Or.inr ⟨K, inferInstance, inferInstance, p ^ f, by rw [hK.card, piCard, Bool.cond_false],
      hq, Or.inl ⟨e⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, by rw [hK.card, piCard, Bool.cond_true]; exact hq,
      Or.inl ⟨e⟩⟩

theorem three_dvd_card_slPi_quot (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    3 ∣ Nat.card (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have e := QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hq)
  rw [Nat.card_congr e.toEquiv]
  cases π
  · exact CFSG.Quasithin.F134.three_dvd_card_statedProj_statedSU_three hK.prime hK.one_le
      (by rw [hK.card, piCard, Bool.cond_false])
  · exact CFSG.Quasithin.F134.three_dvd_card_statedProj_statedSL_three

theorem three_dvd_card_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    3 ∣ Nat.card ↥(slPi π 3 (p ^ f) K) := by
  have := hK.finite
  have h := (Subgroup.center ↥(slPi π 3 (p ^ f) K)).card_mul_index
  rw [← h]
  exact Dvd.dvd.mul_left (three_dvd_card_slPi_quot hK hq) _

theorem isQuasisimple_quotient_center {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) :
    CFSG.Open.IsQuasisimple (X ⧸ Subgroup.center X) := by
  have hperf : Group.IsPerfect X := (Group.isPerfect_def (G := X)).2 hq.1
  have hP : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hc : Subgroup.center ((X ⧸ Subgroup.center X)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot X
  refine ⟨(Group.isPerfect_def).1 hP, ?_⟩
  have e := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have := hq.2
  exact e.isSimpleGroup

theorem commutator_le_self {Y : Type*} [Group Y] (F : Subgroup Y) : ⁅F, F⁆ ≤ F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem fixData_frobSL (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : π = false → p ^ f ≠ 8) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    FixData ↥(slPi π 3 (p ^ f) K) (frobSL hK σ) := by
  obtain ⟨d⟩ := exists_frobData hK hσ
  have hq₀ := d.modThree hq
  have hne : π = false → p ^ d.f₀ ≠ 2 := fun h h2 => h8 h (by rw [d.pow_eq, h2]; norm_num)
  have hqs : CFSG.Open.IsQuasisimple ↥(fixSub (frobSL hK σ)) :=
    isQuasisimple_open_of_mulEquiv d.fixEquiv (isQuasisimple_slPi d.hP hne)
  have hcen : ∀ z : ↥(slPi π 3 (p ^ f) K), z ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) →
      z ∈ d.incl.range := fun z hz => by
    rw [← d.map_center_incl hq] at hz
    obtain ⟨z₀, -, rfl⟩ := hz
    exact ⟨z₀, rfl⟩
  have hcenS : ∀ z : ↥(fixSub (frobSL hK σ)), z ∈ Subgroup.center ↥(fixSub (frobSL hK σ)) →
      d.fixEquiv z ∈ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := fun z hz => by
    have := Subgroup.map_center_eq d.fixEquiv
    rw [← this]
    exact ⟨z, hz, rfl⟩
  refine ⟨fixSub (frobSL hK σ), le_rfl, commutator_le_self _, fun a ha => ⟨0, by simpa using ha⟩,
    hqs, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨rfl, ?_⟩⟩
  ·
    cases π
    · refine Or.inr ⟨d.K₀, inferInstance, ?_, p ^ d.f₀, ?_, hq₀, Or.inr ⟨d.fixEquiv⟩⟩
      · have := d.hP.finite
        infer_instance
      · rw [d.hP.card, piCard, Bool.cond_false]
    · refine Or.inl ⟨d.K₀, inferInstance, ?_, ?_, Or.inr ⟨d.fixEquiv⟩⟩
      · have := d.hP.finite
        infer_instance
      · rw [d.hP.card, piCard, Bool.cond_true]
        exact hq₀
  · intro z hz
    apply d.fixEquiv.injective
    rw [map_pow, map_one]
    exact pow_three_of_mem_center d.hP hq₀ (hcenS z hz)
  · rw [Nat.card_congr d.fixEquiv.toEquiv]
    exact three_dvd_card_slPi d.hP hq₀
  ·
    intro z hz
    have h1 : d.fixEquiv z ∈ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
      have := Subgroup.map_center_eq d.fixEquiv
      rw [← this] at *
      exact ⟨z, hz, rfl⟩
    have h2 : d.incl (d.fixEquiv z) ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
      rw [← d.map_center_incl hq]
      exact ⟨_, h1, rfl⟩
    have h3 : d.incl (d.fixEquiv z) = (z : ↥(slPi π 3 (p ^ f) K)) :=
      (show ((d.fixEquiv.symm (d.fixEquiv z) : ↥(fixSub (frobSL hK σ))) :
        ↥(slPi π 3 (p ^ f) K)) = d.incl (d.fixEquiv z) from rfl).symm.trans
        (congrArg Subtype.val (d.fixEquiv.symm_apply_apply z))
    rw [← h3]
    exact h2
  · intro z hz
    rw [d.fixSub_eq]
    exact hcen z hz
  ·
    cases π
    · refine Or.inr ⟨d.K₀, inferInstance, ?_, p ^ d.f₀, ?_, hq₀, hne rfl, ⟨d.fixEquiv⟩⟩
      · have := d.hP.finite
        infer_instance
      · rw [d.hP.card, piCard, Bool.cond_false]
    · refine Or.inl ⟨d.K₀, inferInstance, ?_, ?_, ⟨d.fixEquiv⟩⟩
      · have := d.hP.finite
        infer_instance
      · rw [d.hP.card, piCard, Bool.cond_true]
        exact hq₀

theorem fixData_frobSL_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : π = false → p ^ f ≠ 8) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    FixData (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))
      (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)) := by
  obtain ⟨d⟩ := exists_frobData hK hσ
  have hq₀ := d.modThree hq
  have hne : π = false → p ^ d.f₀ ≠ 2 := fun h h2 => h8 h (by rw [d.pow_eq, h2]; norm_num)
  have hne' : π = false → p ^ f ≠ 2 := fun h h2 => h8 h (by
    have := d.pow_eq
    have h3 : p ^ d.f₀ ≤ p ^ f := by rw [d.pow_eq]; exact Nat.le_self_pow (by norm_num) _
    rw [h2] at h3
    have hp1 : 2 ≤ p ^ d.f₀ := le_trans hK.prime.two_le
      (Nat.le_self_pow (by have := d.hP.one_le; omega) p)
    have hp2 : p ^ d.f₀ = 2 := by omega
    rw [this, hp2]; norm_num)
  set G := ↥(slPi π 3 (p ^ f) K) with hG
  let pm : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  have hsurj : Function.Surjective pm := QuotientGroup.mk'_surjective _
  have hker : ∀ c, pm c = 1 → c ∈ Subgroup.center G := fun c h => (QuotientGroup.eq_one_iff c).1 h
  have hc : ∀ x, pm (frobSL hK σ x) = centerDescend G (frobSL hK σ) (pm x) := fun x => rfl
  have h3 : ∀ c, pm c = 1 → ∃ n : ℕ, c ^ 3 ^ n = 1 := fun c h =>
    ⟨1, by simpa using pow_three_of_mem_center hK hq (hker c h)⟩
  have hGq : CFSG.Open.IsQuasisimple G := isQuasisimple_slPi hK hne'
  have hGp : Group.IsPerfect G := (Group.isPerfect_def (G := G)).2 hGq.1
  have hcQ : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot G
  set S := fixSub (frobSL hK σ) with hS
  let θ : ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* G ⧸ Subgroup.center G := pm.comp d.incl
  have hrange : θ.range = S.map pm := by
    rw [MonoidHom.range_comp, ← d.fixSub_eq]
  have hker' : θ.ker = Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
    ext s0
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : d.incl s0 ∈ Subgroup.center G := hker _ h
      rw [← d.map_center_incl hq] at h1
      obtain ⟨z, hz, hzs⟩ := h1
      rwa [← d.incl_injective hzs]
    · intro h
      apply (QuotientGroup.eq_one_iff _).2
      rw [← d.map_center_incl hq]
      exact ⟨s0, h, rfl⟩
  let e1 : ↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) ≃*
      ↥(S.map pm) :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      ((QuotientGroup.quotientKerEquivRange θ).trans (MulEquiv.subgroupCongr hrange))
  have hS₀q : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ d.f₀) d.K₀) := isQuasisimple_slPi d.hP hne
  have hS₀p : Group.IsPerfect ↥(slPi π 3 (p ^ d.f₀) d.K₀) :=
    (Group.isPerfect_def).2 hS₀q.1
  have hcSP : Subgroup.center ↥(S.map pm) = ⊥ :=
    center_eq_bot_of_mulEquiv_of_center_eq_bot e1.symm
      (Group.IsPerfect.center_quotient_center_eq_bot _)
  refine ⟨S.map pm, ?_, fixSub_commutator_le_map hsurj hker hc,
    fun a ha => exists_pow_mem_map_fixSub hsurj hker h3 hc ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hc, mem_fixSub.1 hx]
  · exact isQuasisimple_open_of_mulEquiv e1.symm (isQuasisimple_quotient_center hS₀q)
  · exact isL3Type_of_mulEquiv e1 (isL3Type_slPi_quot d.hP hq₀)
  · intro z hz
    rw [hcSP] at hz
    rw [Subgroup.mem_bot.1 hz]
    exact one_pow 3
  · rw [Nat.card_congr e1.symm.toEquiv]
    exact three_dvd_card_slPi_quot d.hP hq₀
  · intro z hz
    rw [hcSP] at hz
    have : z = 1 := Subgroup.mem_bot.1 hz
    rw [this]
    exact Subgroup.one_mem _
  · rw [hcQ]
    exact bot_le
  · rintro ⟨z, hz, hz1⟩
    rw [hcQ] at hz
    exact absurd (Subgroup.mem_bot.1 hz) hz1

end Cover


theorem isSLThreeEpsAny_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSLThreeEpsAny Y) : IsSLThreeEpsAny Y' := by
  rcases h with ⟨K, hK, hf, hc, ⟨g⟩⟩ | ⟨K, hK, hf, q, hc, hq, hq2, ⟨g⟩⟩
  · exact Or.inl ⟨K, hK, hf, hc, ⟨e.symm.trans g⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hc, hq, hq2, ⟨e.symm.trans g⟩⟩

theorem fixSub_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (α : MulAut Y) :
    fixSub (MulAut.congr e α) = (fixSub α).map e.toMonoidHom := by
  ext y'
  rw [mem_fixSub, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨e.symm y', ?_, by simp⟩
    rw [mem_fixSub]
    apply e.injective
    have := h
    rw [MulAut.congr_apply] at this
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.congr_apply]
    simp [(mem_fixSub.1 hy)]

theorem FixData.congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {α : MulAut Y}
    (h : FixData Y α) : FixData Y' (MulAut.congr e α) := by
  obtain ⟨S, hSF, hcomm, hpow, hqs, hty, hz3, h3d, hcen, hZS, hex⟩ := h
  have hF := fixSub_congr e α
  have hZ : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Y' :=
    Subgroup.map_center_eq e
  let g : ↥S ≃* ↥(S.map e.toMonoidHom) := Subgroup.equivMapOfInjective S e.toMonoidHom e.injective
  have hg : ∀ z : ↥S, ((g z : ↥(S.map e.toMonoidHom)) : Y') = e (z : Y) := fun z => rfl
  refine ⟨S.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF]; exact Subgroup.map_mono hSF
  · rw [hF, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm
  · intro a' ha'
    rw [hF] at ha'
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨n, hn⟩ := hpow a ha
    exact ⟨n, ⟨a ^ 3 ^ n, hn, by simp⟩⟩
  · exact isQuasisimple_open_of_mulEquiv g.symm hqs
  · exact isL3Type_of_mulEquiv g hty
  · intro z' hz'
    have h1 : g.symm z' ∈ Subgroup.center ↥S := by
      have := Subgroup.map_center_eq g.symm
      rw [← this]
      exact ⟨z', hz', rfl⟩
    have h2 := hz3 _ h1
    apply g.symm.injective
    rw [map_pow, h2, map_one]
  · rw [Nat.card_congr g.toEquiv] at h3d
    exact h3d
  · intro z' hz'
    have h1 : g.symm z' ∈ Subgroup.center ↥S := by
      have := Subgroup.map_center_eq g.symm
      rw [← this]
      exact ⟨z', hz', rfl⟩
    have h2 := hcen _ h1
    have h3 : (z' : Y') = e ((g.symm z' : ↥S) : Y) := by
      rw [← hg, MulEquiv.apply_symm_apply]
    rw [h3, ← hZ]
    exact ⟨_, h2, rfl⟩
  · intro z' hz'
    rw [← hZ] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨z, hZS hz, rfl⟩
  · rintro ⟨z', hz', hz'1⟩
    rw [← hZ] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    obtain ⟨hFS, hAny⟩ := hex ⟨z, hz, fun h => hz'1 (by simp [h])⟩
    exact ⟨by rw [hF, hFS], isSLThreeEpsAny_of_mulEquiv g hAny⟩

end CFSG.HardMathSupport.Solomon.Coordinator
