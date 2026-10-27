module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBBasis
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBHomMatrix

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix

@[reducible] def commGroupOfForallCommute {G : Type*} [Group G] {W : Subgroup G}
    (h : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) : CommGroup W :=
  { (inferInstance : Group W) with mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

structure Z4Basis {G : Type*} [Group G] (W : Subgroup G) (m : ℕ) where
  toFun : (Fin m → ZMod 4) → G
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y
  mem' : ∀ x, toFun x ∈ W
  injective' : Function.Injective toFun
  surj' : ∀ w ∈ W, ∃ x, toFun x = w

namespace Z4Basis

variable {G : Type*} [Group G] {W : Subgroup G} {m : ℕ}

instance : CoeFun (Z4Basis W m) (fun _ => (Fin m → ZMod 4) → G) :=
  ⟨Z4Basis.toFun⟩

variable (Φ : Z4Basis W m)

theorem map_add (x y : Fin m → ZMod 4) : Φ (x + y) = Φ x * Φ y :=
  Φ.map_add' x y

theorem mem (x : Fin m → ZMod 4) : Φ x ∈ W :=
  Φ.mem' x

theorem injective : Function.Injective Φ :=
  Φ.injective'

@[expose] noncomputable def coord (w : G) : Fin m → ZMod 4 := by
  classical
  exact if h : w ∈ W then Classical.choose (Φ.surj' w h) else 0

theorem apply_coord {w : G} (hw : w ∈ W) : Φ (Φ.coord w) = w := by
  classical
  rw [coord, dite_eq_left hw]
  exact Classical.choose_spec (Φ.surj' w hw)

theorem coord_apply (x : Fin m → ZMod 4) : Φ.coord (Φ x) = x :=
  Φ.injective (Φ.apply_coord (Φ.mem x))

@[expose] noncomputable def conjAddHom {l : G} (hl : l ∈ normalizer (W : Set G)) :
    (Fin m → ZMod 4) →+ (Fin m → ZMod 4) where
  toFun x := Φ.coord (l * Φ x * l⁻¹)
  map_zero' := by
    have h0 : Φ 0 = 1 := by
      have h := Φ.map_add 0 0
      rw [add_zero] at h
      exact mul_eq_left.1 h.symm
    rw [h0, mul_one, mul_inv_cancel, ← h0, coord_apply]
  map_add' x y := by
    have hx := (mem_normalizer_iff.1 hl (Φ x)).1 (Φ.mem x)
    have hy := (mem_normalizer_iff.1 hl (Φ y)).1 (Φ.mem y)
    have hxy := (mem_normalizer_iff.1 hl (Φ (x + y))).1 (Φ.mem (x + y))
    apply Φ.injective
    show Φ (Φ.coord (l * Φ (x + y) * l⁻¹)) =
      Φ (Φ.coord (l * Φ x * l⁻¹) + Φ.coord (l * Φ y * l⁻¹))
    rw [Φ.apply_coord hxy, Φ.map_add (Φ.coord _) (Φ.coord _), Φ.apply_coord hx, Φ.apply_coord hy,
      Φ.map_add]
    group

theorem apply_conjAddHom {l : G} (hl : l ∈ normalizer (W : Set G)) (x : Fin m → ZMod 4) :
    Φ (Φ.conjAddHom hl x) = l * Φ x * l⁻¹ :=
  Φ.apply_coord ((mem_normalizer_iff.1 hl (Φ x)).1 (Φ.mem x))

theorem conjAddHom_mul {l l' : G} (hl : l ∈ normalizer (W : Set G))
    (hl' : l' ∈ normalizer (W : Set G)) :
    Φ.conjAddHom (mul_mem hl hl') = (Φ.conjAddHom hl).comp (Φ.conjAddHom hl') := by
  refine AddMonoidHom.ext fun x => ?_
  apply Φ.injective
  rw [AddMonoidHom.comp_apply, Φ.apply_conjAddHom, Φ.apply_conjAddHom, Φ.apply_conjAddHom]
  group

theorem conjAddHom_one :
    Φ.conjAddHom (one_mem (normalizer (W : Set G))) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun x => ?_
  apply Φ.injective
  rw [Φ.apply_conjAddHom, AddMonoidHom.id_apply]
  group

@[expose] noncomputable def conjMat {l : G} (hl : l ∈ normalizer (W : Set G)) :
    Matrix (Fin m) (Fin m) (ZMod 4) :=
  LinearMap.toMatrix' ((Φ.conjAddHom hl).toZModLinearMap 4)

theorem conjMat_mul {l l' : G} (hl : l ∈ normalizer (W : Set G))
    (hl' : l' ∈ normalizer (W : Set G)) :
    Φ.conjMat hl * Φ.conjMat hl' = Φ.conjMat (mul_mem hl hl') := by
  rw [conjMat, conjMat, conjMat, ← LinearMap.toMatrix'_comp, Φ.conjAddHom_mul hl hl']
  rfl

theorem conjMat_congr {l l' : G} (hl : l ∈ normalizer (W : Set G))
    (hl' : l' ∈ normalizer (W : Set G)) (h : l = l') : Φ.conjMat hl = Φ.conjMat hl' := by
  subst h
  rfl

theorem conjMat_one : Φ.conjMat (one_mem (normalizer (W : Set G))) = 1 := by
  rw [conjMat, Φ.conjAddHom_one, ← LinearMap.toMatrix'_id]
  rfl

theorem conjMat_mul_self {l : G} (hl : l ∈ normalizer (W : Set G)) (hll : l * l = 1) :
    Φ.conjMat hl * Φ.conjMat hl = 1 := by
  rw [Φ.conjMat_mul hl hl, Φ.conjMat_congr _ (one_mem _) hll, Φ.conjMat_one]

theorem conjMat_comm {l l' : G} (hl : l ∈ normalizer (W : Set G))
    (hl' : l' ∈ normalizer (W : Set G)) (hc : l * l' = l' * l) :
    Φ.conjMat hl * Φ.conjMat hl' = Φ.conjMat hl' * Φ.conjMat hl := by
  rw [Φ.conjMat_mul hl hl', Φ.conjMat_mul hl' hl, Φ.conjMat_congr _ _ hc]

theorem map_redFour_conjMat {V : Subgroup G} (b : ElemBasis V m)
    (hsq : ∀ x, Φ x * Φ x = b (fun i => redFour (x i))) {l : G} (hl : l ∈ normalizer (W : Set G))
    {M : Matrix (Fin m) (Fin m) (ZMod 2)} (hM : ∀ y, l * b y * l⁻¹ = b (M *ᵥ y)) :
    (Φ.conjMat hl).map redFour = M := by
  ext i j
  set y := Φ.conjAddHom hl (Pi.single j 1) with hy
  have hred : (fun k => redFour ((Pi.single j (1 : ZMod 4) : Fin m → ZMod 4) k)) =
      (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  have h1 : b (fun k => redFour (y k)) = b (M *ᵥ Pi.single j 1) := by
    rw [← hsq, hy, Φ.apply_conjAddHom, ← hM, ← hred, ← hsq]
    group
  have h2 := congrFun (b.injective h1) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
  rw [Matrix.map_apply, conjMat, LinearMap.toMatrix'_apply]
  exact h2

end Z4Basis

section Coordinates

variable {G : Type*} [Group G] {W V : Subgroup G} {m : ℕ}

theorem redFour_val (q : ZMod 4) : (redFour q).val = q.val % 2 := by
  revert q
  decide +kernel

theorem twiceHom_val (r : ZMod 2) : (twiceHom r).val = 2 * r.val := by
  revert r
  decide +kernel

theorem eq_twiceHom_of_redFour_eq_zero {q : ZMod 4} (hq : redFour q = 0) :
    q = twiceHom ((q.val / 2 : ℕ) : ZMod 2) := by
  revert q
  decide +kernel

theorem exists_z4Basis (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hWc : Nat.card W = 4 ^ m)
    (hVW : V ≤ W) (hV2 : ∀ v ∈ V, v * v = 1) (b : ElemBasis V m) {w : Fin m → G}
    (hw : ∀ i, w i ∈ W) (hww : ∀ i, w i * w i = b (Pi.single i 1)) :
    ∃ Φ : Z4Basis W m, ∀ x, Φ x * Φ x = b (fun i => redFour (x i)) := by
  let _ := commGroupOfForallCommute hcomm
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hWc]; positivity)
  set w' : Fin m → W := fun i => ⟨w i, hw i⟩ with hw'
  set v' : Fin m → W := fun i => ⟨b (Pi.single i 1), hVW (b.mem _)⟩ with hv'
  have hwv : ∀ i, w' i ^ 2 = v' i := fun i => Subtype.ext (by rw [sq]; exact hww i)
  have hv1 : ∀ i, v' i ^ 2 = 1 := fun i => Subtype.ext (by rw [sq]; exact hV2 _ (b.mem _))
  have hw4 : ∀ i, w' i ^ 4 = 1 := fun i => by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hwv, hv1]
  have hb : ∀ y : Fin m → ZMod 2, (⟨b y, hVW (b.mem y)⟩ : W) = ∏ i, v' i ^ (y i).val := by
    let bH : Multiplicative (Fin m → ZMod 2) →* W :=
      { toFun := fun y => ⟨b y.toAdd, hVW (b.mem _)⟩
        map_one' := Subtype.ext b.map_zero
        map_mul' := fun x y => Subtype.ext (b.map_add x.toAdd y.toAdd) }
    intro y
    have hy : Multiplicative.ofAdd y =
        ∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) ^ (y i).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_pow, toAdd_ofAdd]
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul', nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    have := congrArg bH hy
    rw [map_prod] at this
    simp only [map_pow] at this
    exact this
  set Φ₀ : (Fin m → ZMod 4) → W := fun x => ∏ i, w' i ^ (x i).val with hΦ₀
  have hΦadd : ∀ x y, Φ₀ (x + y) = Φ₀ x * Φ₀ y := by
    intro x y
    simp only [hΦ₀, Pi.add_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((x i).val + (y i).val) (hw4 i), ZMod.val_add]
  have hΦsq : ∀ x, Φ₀ x * Φ₀ x = ⟨b (fun i => redFour (x i)), hVW (b.mem _)⟩ := by
    intro x
    rw [hb]
    simp only [hΦ₀, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, ← two_mul, pow_mul, hwv, redFour_val, ← pow_eq_pow_mod _ (hv1 i)]
  have hΦinj : Function.Injective Φ₀ := by
    intro x y hxy
    have hsub : Φ₀ (x - y) = 1 := by
      have h := hΦadd (x - y) y
      rw [sub_add_cancel, hxy] at h
      exact mul_eq_right.1 h.symm
    have hz2 : (fun i => redFour ((x - y) i)) = 0 := by
      apply b.injective
      have h := congrArg Subtype.val (hΦsq (x - y))
      rw [hsub, one_mul] at h
      rw [b.map_zero]
      exact h.symm
    set h : Fin m → ZMod 2 := fun i => ((((x - y) i).val / 2 : ℕ) : ZMod 2) with hh
    have hzh : ∀ i, (x - y) i = twiceHom (h i) := fun i =>
      eq_twiceHom_of_redFour_eq_zero (congrFun hz2 i)
    have hbh : b h = 1 := by
      have h3 : Φ₀ (x - y) = ∏ i, v' i ^ (h i).val := by
        simp only [hΦ₀]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hzh i, twiceHom_val, pow_mul, hwv]
      rw [← hb h, hsub] at h3
      exact (congrArg Subtype.val h3).symm
    have h0 : h = 0 := b.injective (hbh.trans b.map_zero.symm)
    have hz0 : x - y = 0 := funext fun i => by
      rw [hzh i, h0]
      rfl
    exact sub_eq_zero.1 hz0
  have hcard : Nat.card W ≤ Nat.card (Fin m → ZMod 4) := by
    rw [hWc, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsurj := (hΦinj.bijective_of_nat_card_le hcard).2
  refine ⟨{ toFun := fun x => (Φ₀ x : G)
            map_add' := fun x y => by rw [hΦadd]; rfl
            mem' := fun x => (Φ₀ x).2
            injective' := fun x y h => hΦinj (Subtype.ext h)
            surj' := fun v hv => by
              obtain ⟨x, hx⟩ := hsurj ⟨v, hv⟩
              exact ⟨x, congrArg Subtype.val hx⟩ }, fun x => ?_⟩
  exact congrArg Subtype.val (hΦsq x)

end Coordinates

theorem kleinFour_mul_mul_mul : kleinFourA * kleinFourB * kleinFourA * kleinFourB = 1 := by
  decide +kernel

theorem homocyclic_exclusion {G : Type*} [Group G] [Finite G] {W V L₁ : Subgroup G}
    (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hWc : Nat.card W = 2 ^ 8) (hVW : V ≤ W)
    (hVc : Nat.card V = 2 ^ 4) (hV2 : ∀ v ∈ V, v * v = 1) (hWV : ∀ w ∈ W, w * w ∈ V)
    (hL₁W : L₁ ≤ normalizer (W : Set G))
    (haut : ∀ f : V ≃* V, ∃ l ∈ L₁, ∀ v : V, ((f v : V) : G) = l * v * l⁻¹)
    (hfaith : ∀ l ∈ L₁, (∀ v ∈ V, l * v * l⁻¹ = v) → l = 1) :
    ∀ w ∈ W, w * w = 1 := by
  by_contra hcon
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ W, w * w ≠ 1 := by
    by_contra h'
    exact hcon fun w hw => by_contra fun h => h' ⟨w, hw, h⟩
  have hsq : ∀ v ∈ V, ∃ w ∈ W, w * w = v := by
    intro v hv
    by_cases hv1 : v = 1
    · exact ⟨1, one_mem _, by rw [hv1, one_mul]⟩
    obtain ⟨l, hl, hlv⟩ :=
      exists_conj_eq_of_forall_mulEquiv' hVc hV2 haut (hWV w₀ hw₀) hv hw₀1 hv1
    refine ⟨l * w₀ * l⁻¹, (mem_normalizer_iff.1 (hL₁W hl) w₀).1 hw₀, ?_⟩
    rw [← hlv]
    group
  obtain ⟨b⟩ := exists_elemBasis hVc hV2
  choose w hw hww using fun i : Fin 4 => hsq (b (Pi.single i 1)) (b.mem _)
  obtain ⟨Φ, hΦ⟩ := exists_z4Basis hcomm (by rw [hWc]; norm_num) hVW hV2 b hw hww
  obtain ⟨la, hla, hlav⟩ := b.exists_conj_eq_of_forall_mulEquiv haut kleinFourA kleinFourA
    kleinFourA_mul_self kleinFourA_mul_self
  obtain ⟨lb, hlb, hlbv⟩ := b.exists_conj_eq_of_forall_mulEquiv haut kleinFourB kleinFourB
    kleinFourB_mul_self kleinFourB_mul_self
  have hrel : ∀ g ∈ L₁, (∀ x, g * b x * g⁻¹ = b x) → g = 1 := fun g hg h =>
    hfaith g hg fun v hv => by
      obtain ⟨x, rfl⟩ := b.exists_eq hv
      exact h x
  have haa : la * la = 1 := hrel _ (mul_mem hla hla) fun x => by
    calc la * la * b x * (la * la)⁻¹ = la * (la * b x * la⁻¹) * la⁻¹ := by group
      _ = b (kleinFourA *ᵥ (kleinFourA *ᵥ x)) := by rw [hlav, hlav]
      _ = b x := by rw [Matrix.mulVec_mulVec, kleinFourA_mul_self, Matrix.one_mulVec]
  have hbb : lb * lb = 1 := hrel _ (mul_mem hlb hlb) fun x => by
    calc lb * lb * b x * (lb * lb)⁻¹ = lb * (lb * b x * lb⁻¹) * lb⁻¹ := by group
      _ = b (kleinFourB *ᵥ (kleinFourB *ᵥ x)) := by rw [hlbv, hlbv]
      _ = b x := by rw [Matrix.mulVec_mulVec, kleinFourB_mul_self, Matrix.one_mulVec]
  have habab : la * lb * la * lb = 1 :=
    hrel _ (mul_mem (mul_mem (mul_mem hla hlb) hla) hlb) fun x => by
      calc la * lb * la * lb * b x * (la * lb * la * lb)⁻¹ =
          la * (lb * (la * (lb * b x * lb⁻¹) * la⁻¹) * lb⁻¹) * la⁻¹ := by group
        _ = b (kleinFourA *ᵥ (kleinFourB *ᵥ (kleinFourA *ᵥ (kleinFourB *ᵥ x)))) := by
          rw [hlbv, hlav, hlbv, hlav]
        _ = b x := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            kleinFour_mul_mul_mul, Matrix.one_mulVec]
  have hla' : la⁻¹ = la := inv_eq_of_mul_eq_one_right haa
  have hlb' : lb⁻¹ = lb := inv_eq_of_mul_eq_one_right hbb
  have hab : la * lb = lb * la := by
    have h1 : (la * lb)⁻¹ = la * lb := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact habab)
    rw [mul_inv_rev, hla', hlb'] at h1
    exact h1.symm
  exact not_exists_lift_kleinFour (Φ.map_redFour_conjMat b hΦ (hL₁W hla) hlav)
    (Φ.map_redFour_conjMat b hΦ (hL₁W hlb) hlbv) (Φ.conjMat_mul_self (hL₁W hla) haa)
    (Φ.conjMat_mul_self (hL₁W hlb) hbb) (Φ.conjMat_comm (hL₁W hla) (hL₁W hlb) hab)

end CFSG.SeitzReduction.LinearPilot
