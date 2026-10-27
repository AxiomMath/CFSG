module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpf
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Orb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

open Module Matrix CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
open CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

theorem spForm_eq_zero_of_singular {R₀ : Submodule (ZMod 2) VV} (hts : ∀ x ∈ R₀, Q8 x = 0)
    {x y : VV} (hx : x ∈ R₀) (hy : y ∈ R₀) : spForm 4 (ZMod 2) x y = 0 := by
  rw [← polar_Q8]
  have h := hts (x + y) (R₀.add_mem hx hy)
  simp only [QuadraticMap.polar, h, hts x hx, hts y hy, sub_zero]

theorem spForm_fixV_movV {t : StatedSp 4 (ZMod 2)} (ht3 : t ^ 3 = 1) {x y : VV}
    (hx : x ∈ fixV t) (hy : y ∈ movV t) : spForm 4 (ZMod 2) x y = 0 := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 (movV_le_range ht3 hy)
  have htx : spEnd t x = x := by
    rw [fixV_eq_ker, LinearMap.mem_ker] at hx
    simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hx
  have h1 : spForm 4 (ZMod 2) x (spEnd t z) = spForm 4 (ZMod 2) x z := by
    have := I2016Sp.spForm_spEnd t x z
    rwa [htx] at this
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, sub_self]

theorem spForm_comm_zero {x y : VV} (h : spForm 4 (ZMod 2) x y = 0) : spForm 4 (ZMod 2) y x = 0 := by
  exact (spForm_isAlt (r := 4) (K := ZMod 2)).eq_iff.1 h

theorem eq_movV_of_invariant {t : StatedSp 4 (ZMod 2)} (hM : finrank (ZMod 2) (movV t) = 2)
    {W : Submodule (ZMod 2) VV} (hWle : W ≤ movV t) (hWinv : ∀ w ∈ W, spEnd t w ∈ W)
    (hne : W ≠ ⊥) : W = movV t := by
  have heven := even_finrank_of_le_movV hWle hWinv
  have hle := Submodule.finrank_mono hWle
  rw [hM] at hle
  have hpos := Submodule.one_le_finrank_iff.2 hne
  have h2 : finrank (ZMod 2) W = 2 := by
    obtain ⟨k, hk⟩ := heven
    have hk' : finrank (ZMod 2) W = k + k := hk
    have hle' : finrank (ZMod 2) W ≤ 2 := hle
    have hpos' : 1 ≤ finrank (ZMod 2) W := hpos
    omega
  exact Submodule.eq_of_le_of_finrank_eq hWle (by rw [h2, hM])

theorem le_fixV_of_isotropic {t : StatedSp 4 (ZMod 2)} (ht3 : t ^ 3 = 1)
    (hM : finrank (ZMod 2) (movV t) = 2) {R₀ : Submodule (ZMod 2) VV}
    (hiso : ∀ x ∈ R₀, ∀ y ∈ R₀, spForm 4 (ZMod 2) x y = 0) (hinv : ∀ x ∈ R₀, spEnd t x ∈ R₀) :
    R₀ ≤ fixV t := by
  have hMinv : ∀ w ∈ movV t, spEnd t w ∈ movV t := fun w hw => apply_mem_movV_of_commute rfl hw
  have hWbot : R₀ ⊓ movV t = ⊥ := by
    by_contra hne
    have hWM := eq_movV_of_invariant hM (inf_le_right : R₀ ⊓ movV t ≤ movV t)
      (fun w hw => ⟨hinv w hw.1, hMinv w hw.2⟩) hne
    have hMR : movV t ≤ R₀ := hWM ▸ inf_le_left
    have hzero : movV t = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      refine (spForm_nondegenerate (r := 4) (K := ZMod 2)).1 y fun v => ?_
      have hv : v ∈ fixV t ⊔ movV t := by rw [fixV_sup_movV ht3]; exact Submodule.mem_top
      obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, spForm_comm_zero (spForm_fixV_movV ht3 hx₀ hy),
        hiso y (hMR hy) x₁ (hMR hx₁), add_zero]
    rw [hzero, finrank_bot] at hM
    omega
  intro x hx
  have h3 : spEnd t (spEnd t (spEnd t x)) = x := by
    have := congrArg (fun f : Module.End (ZMod 2) VV => f x) (spEnd_pow ht3)
    simpa [pow_succ, Module.End.mul_apply] using this
  have hc : spEnd t x + spEnd t (spEnd t x) ∈ R₀ ⊓ movV t := by
    refine Submodule.mem_inf.2 ⟨R₀.add_mem (hinv x hx) (hinv _ (hinv x hx)), ?_⟩
    rw [movV, primaryComponent, LinearMap.mem_ker, q2_eq]
    simp only [pow_two, map_add, map_mul, Polynomial.aeval_X, map_one, Module.End.mul_apply,
      LinearMap.add_apply, Module.End.one_apply, h3]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize x i = p
    generalize (spEnd t) x i = q
    generalize (spEnd t) ((spEnd t) x) i = r
    revert p q r
    decide +revert
  rw [hWbot, Submodule.mem_bot] at hc
  have hab : spEnd t x = spEnd t (spEnd t x) := by
    funext i
    have := congrFun hc i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    generalize (spEnd t) x i = q at this ⊢
    generalize (spEnd t) ((spEnd t) x) i = r at this ⊢
    revert q r
    decide +revert
  have hbx : spEnd t (spEnd t x) = x := by
    have := congrArg (spEnd t) hab
    rw [h3] at this
    exact this
  rw [fixV_eq_ker, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  rw [hab, hbx, sub_self]

theorem finrank_le_three {t : StatedSp 4 (ZMod 2)} (ht3 : t ^ 3 = 1)
    (hM : finrank (ZMod 2) (movV t) = 2) {R₀ : Submodule (ZMod 2) VV}
    (hiso : ∀ x ∈ R₀, ∀ y ∈ R₀, spForm 4 (ZMod 2) x y = 0) (hle : R₀ ≤ fixV t) :
    finrank (ZMod 2) R₀ ≤ 3 := by
  have hnd := spForm_nondegenerate (r := 4) (K := ZMod 2)
  have hperp : finrank (ZMod 2) ((spForm 4 (ZMod 2)).orthogonal R₀) =
      finrank (ZMod 2) VV - finrank (ZMod 2) R₀ := LinearMap.BilinForm.finrank_orthogonal hnd R₀
  have h1 : R₀ ≤ (spForm 4 (ZMod 2)).orthogonal R₀ := fun y hy x hx => hiso x hx y hy
  have h2 : movV t ≤ (spForm 4 (ZMod 2)).orthogonal R₀ := fun y hy x hx =>
    spForm_fixV_movV ht3 (hle hx) hy
  have h3 : R₀ ⊔ movV t ≤ (spForm 4 (ZMod 2)).orthogonal R₀ := sup_le h1 h2
  have hdisj : R₀ ⊓ movV t = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ fixV t ⊓ movV t := ⟨hle hv.1, hv.2⟩
    rw [fixV_inf_movV] at this
    exact this
  have h4 : finrank (ZMod 2) (R₀ ⊔ movV t : Submodule (ZMod 2) VV) + finrank (ZMod 2) (R₀ ⊓ movV t : Submodule (ZMod 2) VV) =
      finrank (ZMod 2) R₀ + finrank (ZMod 2) (movV t) := Submodule.finrank_sup_add_finrank_inf_eq R₀ (movV t)
  rw [hdisj, finrank_bot] at h4
  have h5 : finrank (ZMod 2) (R₀ ⊔ movV t : Submodule (ZMod 2) VV) ≤ finrank (ZMod 2) ((spForm 4 (ZMod 2)).orthogonal R₀) :=
    Submodule.finrank_mono h3
  have h8 : finrank (ZMod 2) VV = 8 := I2016Sp.finrank_V8
  have hR : finrank (ZMod 2) R₀ ≤ finrank (ZMod 2) VV := Submodule.finrank_le R₀
  omega

abbrev mat (x : ↥Om8) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))

theorem mat_mul (x y : ↥Om8) : mat (x * y) = mat x * mat y := by
  simp [mat]

theorem mat_one : mat (1 : ↥Om8) = 1 := by
  simp [mat]

theorem mat_inv_mul (x : ↥Om8) : mat x⁻¹ * mat x = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (x : ↥Om8) : mat x * mat x⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

@[expose] noncomputable def actOn (Y : Subgroup ↥Om8) (R₀ : Submodule (ZMod 2) VV)
    (hinv : ∀ y ∈ Y, ∀ x ∈ R₀, mat y *ᵥ x ∈ R₀) : ↥Y →* Equiv.Perm ↥R₀ where
  toFun y :=
    { toFun := fun v => ⟨mat y.1 *ᵥ (v : VV), hinv y.1 y.2 v v.2⟩
      invFun := fun v => ⟨mat y.1⁻¹ *ᵥ (v : VV), hinv y.1⁻¹ (Y.inv_mem y.2) v v.2⟩
      left_inv := fun v => Subtype.ext (by
        simp only [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec])
      right_inv := fun v => Subtype.ext (by
        simp only [Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]) }
  map_one' := by
    ext v
    simp [mat_one]
  map_mul' := fun a b => by
    ext v
    simp [mat_mul, Matrix.mulVec_mulVec]

@[expose] def fixSub (r : VV) : Subgroup ↥Om8 where
  carrier := {x | mat x *ᵥ r = r}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by simp [mat_one]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc mat a⁻¹ *ᵥ r = mat a⁻¹ *ᵥ (mat a *ᵥ r) := by rw [ha]
      _ = r := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

theorem m1_core (hcard : Nat.card ↥Om8 = 3 ^ 5 * 716800)
    {g : ↥Om8} (hg3 : g ^ 3 = 1)
    (hM : finrank (ZMod 2) (movV (Subgroup.inclusion om8_le_sp8 g)) = 2)
    {L : Subgroup ↥Om8} [Group.IsPerfect L]
    (h27 : 27 ∣ Nat.card ↥(L ⊔ Subgroup.zpowers g))
    {R₀ : Submodule (ZMod 2) VV} (hR0 : R₀ ≠ ⊥) (hts : ∀ x ∈ R₀, Q8 x = 0)
    (hinv : ∀ y ∈ L ⊔ Subgroup.zpowers g, ∀ x ∈ R₀, mat y *ᵥ x ∈ R₀) : False := by
  have ht3 : (Subgroup.inclusion om8_le_sp8 g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hspE : ∀ (y : ↥Om8) (v : VV), spEnd (Subgroup.inclusion om8_le_sp8 y) v = mat y *ᵥ v :=
    fun y v => rfl
  have hgY : g ∈ L ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hiso : ∀ x ∈ R₀, ∀ y ∈ R₀, spForm 4 (ZMod 2) x y = 0 := fun x hx y hy =>
    spForm_eq_zero_of_singular hts hx hy
  have hle : R₀ ≤ fixV (Subgroup.inclusion om8_le_sp8 g) :=
    le_fixV_of_isotropic ht3 hM hiso (fun x hx => by rw [hspE]; exact hinv g hgY x hx)
  have hd3 := finrank_le_three ht3 hM hiso hle
  have hgfix : ∀ x ∈ R₀, mat g *ᵥ x = x := by
    intro x hx
    have h := hle hx
    rw [fixV_eq_ker, LinearMap.mem_ker] at h
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hspE] at h
    exact h
  obtain ⟨r₀, hr₀, hr₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
  suffices h : ∃ P : Subgroup ↥Om8, 27 ∣ Nat.card P ∧ ∃ r ∈ R₀, r ≠ 0 ∧ ∀ x ∈ P, mat x *ᵥ r = r by
    obtain ⟨P, hP27, r, hr, hr0, hPr⟩ := h
    exact not_dvd_card_of_fixing hcard hr0 (hts r hr) hPr hP27
  by_cases hd : finrank (ZMod 2) R₀ ≤ 2
  · refine ⟨L ⊔ Subgroup.zpowers g, h27, r₀, hr₀, hr₀0, ?_⟩
    have hcardR : Nat.card ↥R₀ ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      calc 2 ^ finrank (ZMod 2) R₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
        _ = 4 := by norm_num
    have hψ : (actOn (L ⊔ Subgroup.zpowers g) R₀ hinv).comp (Subgroup.inclusion le_sup_left) = 1 :=
      perfect_hom_perm_trivial hcardR _
    have hLfix : L ≤ fixSub r₀ := by
      intro l hl
      have h := congrArg (fun f : Equiv.Perm ↥R₀ => f ⟨r₀, hr₀⟩) (DFunLike.congr_fun hψ ⟨l, hl⟩)
      have h2 := congrArg Subtype.val h
      exact h2
    have hgF : Subgroup.zpowers g ≤ fixSub r₀ := (Subgroup.zpowers_le).2 (hgfix r₀ hr₀)
    exact fun x hx => sup_le hLfix hgF hx
  · have hd3' : finrank (ZMod 2) R₀ = 3 := by omega
    have hcardR : Nat.card ↥R₀ = 8 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd3', Nat.card_zmod]
      norm_num
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P⟩ : Nonempty (Sylow 3 ↥(L ⊔ Subgroup.zpowers g)) := inferInstance
    have hP27 : 27 ∣ Nat.card (P : Subgroup ↥(L ⊔ Subgroup.zpowers g)) := by
      rw [Sylow.card_eq_multiplicity P]
      have hne : Nat.card ↥(L ⊔ Subgroup.zpowers g) ≠ 0 := Nat.card_pos.ne'
      have h3 : 3 ^ 3 ∣ Nat.card ↥(L ⊔ Subgroup.zpowers g) := by simpa using h27
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 h3
      have h4 := pow_dvd_pow 3 this
      simpa using h4
    letI : MulAction ↥(P : Subgroup ↥(L ⊔ Subgroup.zpowers g)) ↥R₀ :=
      MulAction.compHom ↥R₀ ((actOn (L ⊔ Subgroup.zpowers g) R₀ hinv).comp
        (P : Subgroup ↥(L ⊔ Subgroup.zpowers g)).subtype)
    have hmod := (P.isPGroup').card_modEq_card_fixedPoints ↥R₀
    have hfix : ∃ v : ↥R₀, v ∈ MulAction.fixedPoints ↥(P : Subgroup ↥(L ⊔ Subgroup.zpowers g)) ↥R₀ ∧
        v ≠ 0 := by
      by_contra hno
      push Not at hno
      have hle1 : Nat.card (MulAction.fixedPoints ↥(P : Subgroup ↥(L ⊔ Subgroup.zpowers g)) ↥R₀) ≤ 1 := by
        refine Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ?_⟩
        rw [hno a.1 a.2, hno b.1 b.2]
      rw [hcardR] at hmod
      have h8 := hmod
      unfold Nat.ModEq at h8
      omega
    obtain ⟨v, hvfix, hv0⟩ := hfix
    refine ⟨(P : Subgroup ↥(L ⊔ Subgroup.zpowers g)).map (L ⊔ Subgroup.zpowers g).subtype, ?_,
      v.1, v.2, fun h => hv0 (Subtype.ext h), ?_⟩
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact hP27
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
      have h := MulAction.mem_fixedPoints.1 hvfix ⟨p, hp⟩
      have h2 := congrArg Subtype.val h
      exact h2

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

end
