module

public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QExt
public import CFSG.RankThree.PartOne.BRANCH.RankSylow

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

@[expose] def ia : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def ir : Fin Tag.G2.rank := ⟨1, by decide⟩

@[expose] noncomputable def tz (s t : Kˣ) : ModGL .G2 K :=
  torusElt .G2 K ia s * torusElt .G2 K ir t

theorem cartan_ia_ia : Tag.G2.cartan ia ia = 2 := by decide

theorem cartan_ia_ir : Tag.G2.cartan ia ir = -1 := by decide

theorem cartan_ir_ia : Tag.G2.cartan ir ia = -3 := by decide

theorem cartan_ir_ir : Tag.G2.cartan ir ir = 2 := by decide

theorem tz_mul (s t s' t' : Kˣ) : tz s t * tz s' t' = (tz (s * s') (t * t') : ModGL .G2 K) := by
  unfold tz
  rw [torusElt_mul, torusElt_mul]
  calc torusElt .G2 K ia s * torusElt .G2 K ir t * (torusElt .G2 K ia s' * torusElt .G2 K ir t')
      = torusElt .G2 K ia s * (torusElt .G2 K ir t * torusElt .G2 K ia s') *
          torusElt .G2 K ir t' := by group
    _ = torusElt .G2 K ia s * (torusElt .G2 K ia s' * torusElt .G2 K ir t) *
          torusElt .G2 K ir t' := by rw [torusElt_mul_comm ir ia t s']
    _ = _ := by group

theorem tz_one_one : tz 1 1 = (1 : ModGL .G2 K) := by
  simp [tz, torusElt_one]

theorem tz_left (s : Kˣ) : tz s 1 = (torusElt .G2 K ia s : ModGL .G2 K) := by
  simp [tz, torusElt_one]

theorem tz_right (t : Kˣ) : tz 1 t = (torusElt .G2 K ir t : ModGL .G2 K) := by
  simp [tz, torusElt_one]

theorem tz_split (s t : Kˣ) : tz s t = (tz s 1 * tz 1 t : ModGL .G2 K) := by
  rw [tz_mul, mul_one, one_mul]

theorem tz_inv (s t : Kˣ) : (tz s t : ModGL .G2 K)⁻¹ = tz s⁻¹ t⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tz_mul, mul_inv_cancel, mul_inv_cancel, tz_one_one]

@[expose] noncomputable def n0 : ModGL .G2 K := weylElt .G2 K ia 1
@[expose] noncomputable def n1 : ModGL .G2 K := weylElt .G2 K ir 1

theorem n0_tz_left (s : Kˣ) : (n0 : ModGL .G2 K) * tz s 1 * n0⁻¹ = tz s⁻¹ 1 := by
  have h := weylElt_one_mul_torusElt_mul_inv .G2 K ia ia s
  rw [cartan_ia_ia] at h
  rw [tz_left, tz_left, n0, h, ← torusElt_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem n0_tz_right (t : Kˣ) : (n0 : ModGL .G2 K) * tz 1 t * n0⁻¹ = tz (t ^ 3) t := by
  have h := weylElt_one_mul_torusElt_mul_inv .G2 K ia ir t
  rw [cartan_ir_ia] at h
  rw [tz_right, n0, h]
  have e : t ^ (-(-3 : ℤ)) = t ^ 3 := by norm_num
  rw [e, tz, torusElt_mul_comm]

theorem n1_tz_left (s : Kˣ) : (n1 : ModGL .G2 K) * tz s 1 * n1⁻¹ = tz s s := by
  have h := weylElt_one_mul_torusElt_mul_inv .G2 K ir ia s
  rw [cartan_ia_ir] at h
  rw [tz_left, n1, h]
  have e : s ^ (-(-1 : ℤ)) = s := by norm_num
  rw [e, tz]

theorem n1_tz_right (t : Kˣ) : (n1 : ModGL .G2 K) * tz 1 t * n1⁻¹ = tz 1 t⁻¹ := by
  have h := weylElt_one_mul_torusElt_mul_inv .G2 K ir ir t
  rw [cartan_ir_ir] at h
  rw [tz_right, tz_right, n1, h, ← torusElt_mul]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem n0_tz (s t : Kˣ) : (n0 : ModGL .G2 K) * tz s t * n0⁻¹ = tz (s⁻¹ * t ^ 3) t := by
  rw [tz_split, show (n0 : ModGL .G2 K) * (tz s 1 * tz 1 t) * n0⁻¹ =
    (n0 * tz s 1 * n0⁻¹) * (n0 * tz 1 t * n0⁻¹) by group, n0_tz_left, n0_tz_right, tz_mul, one_mul]

theorem n1_tz (s t : Kˣ) : (n1 : ModGL .G2 K) * tz s t * n1⁻¹ = tz s (s * t⁻¹) := by
  rw [tz_split, show (n1 : ModGL .G2 K) * (tz s 1 * tz 1 t) * n1⁻¹ =
    (n1 * tz s 1 * n1⁻¹) * (n1 * tz 1 t * n1⁻¹) by group, n1_tz_left, n1_tz_right, tz_mul, mul_one]


@[expose] def pair (s t : Kˣ) : Fin Tag.G2.rank → Kˣ := fun i => if i = ia then s else t

theorem pair_ia (s t : Kˣ) : pair s t ia = s := by simp [pair]

theorem pair_ir (s t : Kˣ) : pair s t ir = t := by
  have : ir ≠ ia := by decide
  simp [pair, this]

theorem coe_torusCoordHom_pair (s t : Kˣ) :
    ((torusCoordHom .G2 K (pair s t) : torusGroup .G2 K) : ModGL .G2 K) = tz s t := by
  rw [coe_torusCoordHom]
  show (List.ofFn (n := 2) fun i => torusElt .G2 K i (pair s t i)).prod = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  show torusElt .G2 K ia (pair s t ia) * torusElt .G2 K ir (pair s t ir) = tz s t
  rw [pair_ia, pair_ir]
  rfl

theorem tz_injective {s t s' t' : Kˣ} (h : (tz s t : ModGL .G2 K) = tz s' t') :
    s = s' ∧ t = t' := by
  have hinj : Function.Injective (torusCoordHom .G2 K) :=
    torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_G2
  have := hinj (a₁ := pair s t) (a₂ := pair s' t')
    (Subtype.ext (by rw [coe_torusCoordHom_pair, coe_torusCoordHom_pair]; exact h))
  exact ⟨by simpa [pair_ia] using congrFun this ia, by simpa [pair_ir] using congrFun this ir⟩

theorem tz_mem_torusGroup (s t : Kˣ) : (tz s t : ModGL .G2 K) ∈ torusGroup .G2 K := by
  have := (torusCoordHom .G2 K (pair s t)).2
  rwa [coe_torusCoordHom_pair] at this

theorem exists_tz_of_mem_torusGroup {g : ModGL .G2 K} (hg : g ∈ torusGroup .G2 K) :
    ∃ s t : Kˣ, g = tz s t := by
  obtain ⟨b, hb⟩ := torusCoordHom_surjective (τ := .G2) (R := K) ⟨g, hg⟩
  refine ⟨b ia, b ir, ?_⟩
  have h1 : ((torusCoordHom .G2 K b : torusGroup .G2 K) : ModGL .G2 K) = g :=
    congrArg Subtype.val hb
  have h2 : (pair (b ia) (b ir)) = b := by
    funext i
    by_cases hi : i = ia
    · subst hi; exact pair_ia _ _
    · have : i = ir := by revert hi; revert i; decide
      subst this; exact pair_ir _ _
  rw [← h1]
  conv_lhs => rw [← h2]
  exact coe_torusCoordHom_pair _ _

@[expose] noncomputable def yq : ModGL .G2 K := n0 * n1 * (n0 * n1)

theorem yq_tz (s t : Kˣ) :
    (yq : ModGL .G2 K) * tz s t * yq⁻¹ = tz (s * (t ^ 3)⁻¹) (s * (t ^ 2)⁻¹) := by
  have key : ∀ a b z : ModGL .G2 K, (a * b * (a * b)) * z * (a * b * (a * b))⁻¹ =
      a * (b * (a * (b * z * b⁻¹) * a⁻¹) * b⁻¹) * a⁻¹ := by
    intros; group
  rw [yq, key, n1_tz, n0_tz, n1_tz, n0_tz]
  congr 1 <;> (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_pow]; module)

theorem braid : ((n0 : ModGL .G2 K) * n1) ^ 3 = (n1 * n0) ^ 3 := by
  have h := prod_alternatingWord_weylElt .G2 K ia ir
  rw [cartan_ia_ir, cartan_ir_ia] at h
  have h6 : TauCeti.coxeterOrder ((-1 : ℤ) * (-3)) = 6 := by
    rw [show ((-1 : ℤ) * (-3)) = 3 by norm_num]
    exact TauCeti.coxeterOrder_three
  rw [h6] at h
  simp [CoxeterSystem.alternatingWord] at h
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact h


@[expose] def tz2 : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ s t : Kˣ, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ g = tz s t}
  mul_mem' := by
    rintro _ _ ⟨s, t, hs, ht, rfl⟩ ⟨s', t', hs', ht', rfl⟩
    exact ⟨s * s', t * t', by rw [mul_pow, hs, hs', one_mul], by rw [mul_pow, ht, ht', one_mul],
      tz_mul s t s' t'⟩
  one_mem' := ⟨1, 1, one_pow _, one_pow _, tz_one_one.symm⟩
  inv_mem' := by
    rintro _ ⟨s, t, hs, ht, rfl⟩
    exact ⟨s⁻¹, t⁻¹, by rw [inv_pow, hs, inv_one], by rw [inv_pow, ht, inv_one], tz_inv s t⟩

theorem n0_sq : (n0 : ModGL .G2 K) ^ 2 = tz (-1) 1 := by
  rw [pow_two, n0, weylElt_one_mul_self, tz_left]

theorem n1_sq : (n1 : ModGL .G2 K) ^ 2 = tz 1 (-1) := by
  rw [pow_two, n1, weylElt_one_mul_self, tz_right]

theorem n0_sq_mem : (n0 : ModGL .G2 K) ^ 2 ∈ (tz2 : Subgroup (ModGL .G2 K)) := by
  rw [n0_sq]
  exact ⟨-1, 1, by simp, one_pow _, rfl⟩

theorem n1_sq_mem : (n1 : ModGL .G2 K) ^ 2 ∈ (tz2 : Subgroup (ModGL .G2 K)) := by
  rw [n1_sq]
  exact ⟨1, -1, one_pow _, by simp, rfl⟩

theorem n0_conj_tz2 : ∀ x ∈ (tz2 : Subgroup (ModGL .G2 K)), n0 * x * n0⁻¹ ∈ tz2 := by
  rintro _ ⟨s, t, hs, ht, rfl⟩
  refine ⟨s⁻¹ * t ^ 3, t, ?_, ht, n0_tz s t⟩
  have : (s⁻¹ * t ^ 3) ^ 2 = (s ^ 2)⁻¹ * (t ^ 2) ^ 3 := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  rw [this, hs, ht]
  simp

theorem n1_conj_tz2 : ∀ x ∈ (tz2 : Subgroup (ModGL .G2 K)), n1 * x * n1⁻¹ ∈ tz2 := by
  rintro _ ⟨s, t, hs, ht, rfl⟩
  refine ⟨s, s * t⁻¹, hs, ?_, n1_tz s t⟩
  have : (s * t⁻¹) ^ 2 = s ^ 2 * (t ^ 2)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  rw [this, hs, ht]
  simp

theorem pow_six_mem_tz2 : ((n0 : ModGL .G2 K) * n1) ^ 6 ∈ (tz2 : Subgroup (ModGL .G2 K)) :=
  pow_six_mem tz2 n0 n1 n0_sq_mem n1_sq_mem n0_conj_tz2 n1_conj_tz2 braid

theorem yq_pow_three : (yq : ModGL .G2 K) ^ 3 = 1 := by
  obtain ⟨s, t, hs, ht, h⟩ := (pow_six_mem_tz2 : ((n0 : ModGL .G2 K) * n1) ^ 6 ∈ tz2)
  have hy : (yq : ModGL .G2 K) ^ 3 = tz s t := by
    rw [← h, yq, ← sq, ← pow_mul]
  have hconj : (yq : ModGL .G2 K) * yq ^ 3 * yq⁻¹ = yq ^ 3 := by group
  rw [hy, yq_tz] at hconj
  obtain ⟨h1, h2⟩ := tz_injective hconj
  have ht3 : t ^ 3 = 1 := by
    have : (t ^ 3)⁻¹ = 1 := mul_eq_left.1 h1
    simpa using this
  have ht1 : t = 1 := by
    have : t = t ^ 3 * (t ^ 2)⁻¹ := by group
    rw [this, ht3, ht]
    simp
  have hs1 : s = 1 := by
    rw [ht, inv_one, mul_one] at h2
    rw [h2, ht1]
  rw [hy, hs1, ht1, tz_one_one]

theorem torusGroup_le_adjoint : torusGroup .G2 K ≤ adjointGroup .G2 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem tz_mem_adjointGroup (s t : Kˣ) : (tz s t : ModGL .G2 K) ∈ adjointGroup .G2 K :=
  torusGroup_le_adjoint (tz_mem_torusGroup s t)

theorem yq_mem_adjointGroup : (yq : ModGL .G2 K) ∈ adjointGroup .G2 K :=
  mul_mem (mul_mem (weylElt_mem_adjointGroup ia 1) (weylElt_mem_adjointGroup ir 1))
    (mul_mem (weylElt_mem_adjointGroup ia 1) (weylElt_mem_adjointGroup ir 1))

variable (K) in
@[expose] noncomputable def torusSub : Subgroup (adjointGroup .G2 K) :=
  (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)

variable (K) in
@[expose] noncomputable def yG : adjointGroup .G2 K := ⟨yq, yq_mem_adjointGroup⟩

theorem mem_torusSub {x : adjointGroup .G2 K} :
    x ∈ torusSub K ↔ (x : ModGL .G2 K) ∈ torusGroup .G2 K := Iff.rfl

noncomputable def coord (x : torusSub K) : Kˣ × Kˣ :=
  (Classical.choose (exists_tz_of_mem_torusGroup (mem_torusSub.1 x.2)),
    Classical.choose (Classical.choose_spec (exists_tz_of_mem_torusGroup (mem_torusSub.1 x.2))))

theorem tz_coord (x : torusSub K) : ((x : adjointGroup .G2 K) : ModGL .G2 K) =
    tz (coord x).1 (coord x).2 :=
  Classical.choose_spec (Classical.choose_spec (exists_tz_of_mem_torusGroup (mem_torusSub.1 x.2)))

theorem coord_injective : Function.Injective (coord (K := K)) := by
  intro x x' h
  apply Subtype.ext
  apply Subtype.ext
  rw [tz_coord, tz_coord, h]

theorem tz_pow (s t : Kˣ) (n : ℕ) : (tz s t : ModGL .G2 K) ^ n = tz (s ^ n) (t ^ n) := by
  induction n with
  | zero => simp [tz_one_one]
  | succ n ih => rw [pow_succ, ih, tz_mul, pow_succ, pow_succ]

theorem tz_pow_three {s t : Kˣ} (h : (tz s t : ModGL .G2 K) ^ 3 = 1) : s ^ 3 = 1 ∧ t ^ 3 = 1 := by
  rw [tz_pow, ← tz_one_one] at h
  exact tz_injective h

theorem coord_pow_three {x : torusSub K} (hx : (x : adjointGroup .G2 K) ^ 3 = 1) :
    (coord x).1 ^ 3 = 1 ∧ (coord x).2 ^ 3 = 1 := by
  have h : ((x : adjointGroup .G2 K) : ModGL .G2 K) ^ 3 = 1 := by
    have := congrArg (Subtype.val : adjointGroup .G2 K → ModGL .G2 K) hx
    simpa using this
  rw [tz_coord] at h
  exact tz_pow_three h

theorem coord_fixed {x : torusSub K}
    (h : yG K * (x : adjointGroup .G2 K) * (yG K)⁻¹ = x) :
    (coord x).1 = 1 ∧ (coord x).2 ^ 3 = 1 := by
  have h' : (yq : ModGL .G2 K) * ((x : adjointGroup .G2 K) : ModGL .G2 K) * yq⁻¹ =
      ((x : adjointGroup .G2 K) : ModGL .G2 K) := congrArg Subtype.val h
  rw [tz_coord, yq_tz] at h'
  obtain ⟨h1, h2⟩ := tz_injective h'
  have ht3 : (coord x).2 ^ 3 = 1 := by
    have : ((coord x).2 ^ 3)⁻¹ = 1 := mul_eq_left.1 h1
    simpa using this
  refine ⟨?_, ht3⟩
  have h3 : (coord x).1 = (coord x).2 * (coord x).2 ^ 2 := mul_inv_eq_iff_eq_mul.1 h2
  rw [h3, ← pow_succ', ht3]

theorem yG_pow_three : yG K ^ 3 = 1 := Subtype.ext (by simpa [yG] using yq_pow_three)

theorem yG_conj_mem {x : adjointGroup .G2 K} (hx : x ∈ torusSub K) :
    yG K * x * (yG K)⁻¹ ∈ torusSub K := by
  obtain ⟨s, t, hst⟩ := exists_tz_of_mem_torusGroup (mem_torusSub.1 hx)
  rw [mem_torusSub]
  have : ((yG K * x * (yG K)⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      yq * (x : ModGL .G2 K) * yq⁻¹ := rfl
  rw [this, hst, yq_tz]
  exact tz_mem_torusGroup _ _

theorem yG_not_mem {g : Kˣ} (hg : g ≠ 1) : yG K ∉ torusSub K := by
  intro hy
  obtain ⟨s0, t0, h0⟩ := exists_tz_of_mem_torusGroup (mem_torusSub.1 hy)
  have h1 : (yq : ModGL .G2 K) * tz g 1 * yq⁻¹ = tz g 1 := by
    have : (yq : ModGL .G2 K) = tz s0 t0 := h0
    rw [this, tz_inv, tz_mul, tz_mul]
    congr 1
    · rw [mul_comm s0 g, mul_assoc, mul_inv_cancel, mul_one]
    · simp
  rw [yq_tz] at h1
  have := (tz_injective h1).2
  apply hg
  simpa using this

theorem ext3_torusSub {g : Kˣ} (hg : g ≠ 1) : Ext3 (torusSub K) (yG K) where
  pow_three := yG_pow_three
  normal := fun _ hx => yG_conj_mem hx
  not_mem := yG_not_mem hg

theorem torusSub_comm {a b : adjointGroup .G2 K} (ha : a ∈ torusSub K) (hb : b ∈ torusSub K) :
    a * b = b * a := by
  obtain ⟨s, t, hst⟩ := exists_tz_of_mem_torusGroup (mem_torusSub.1 ha)
  obtain ⟨s', t', hst'⟩ := exists_tz_of_mem_torusGroup (mem_torusSub.1 hb)
  apply Subtype.ext
  show (a : ModGL .G2 K) * b = b * a
  rw [hst, hst', tz_mul, tz_mul, mul_comm s, mul_comm t]

theorem card_le_nine_of_le_torus {F : Subgroup (adjointGroup .G2 K)} (hF : F ≤ torusSub K)
    (h3 : ∀ x ∈ F, x ^ 3 = 1) : Nat.card F ≤ 9 := by
  let φ : F → (Fin 2 → Kˣ) := fun x =>
    ![(coord ⟨x.1, hF x.2⟩).1, (coord ⟨x.1, hF x.2⟩).2]
  have hinj : Function.Injective φ := by
    intro x x' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hc := coord_injective (Prod.ext h0 h1)
    exact Subtype.ext (congrArg (fun z : torusSub K => (z : adjointGroup .G2 K)) hc)
  have hpow : ∀ x i, φ x i ^ 3 = 1 := by
    intro x i
    obtain ⟨h1, h2⟩ := coord_pow_three (x := ⟨x.1, hF x.2⟩) (h3 x.1 x.2)
    fin_cases i
    · exact h1
    · exact h2
  have := CFSG.RankThree.PartOne.BRANCH.card_le_pow_of_injective_units (L := K) (k := 2) (r := 3)
    (by norm_num) φ hinj hpow
  simpa using this

theorem card_le_three_of_fixed {F : Subgroup (adjointGroup .G2 K)} (hF : F ≤ torusSub K)
    (h : ∀ x ∈ F, x ^ 3 = 1 ∧ yG K * x * (yG K)⁻¹ = x) : Nat.card F ≤ 3 := by
  let φ : F → (Fin 1 → Kˣ) := fun x => fun _ => (coord ⟨x.1, hF x.2⟩).2
  have hfix : ∀ x : F, (coord (⟨x.1, hF x.2⟩ : torusSub K)).1 = 1 ∧
      (coord (⟨x.1, hF x.2⟩ : torusSub K)).2 ^ 3 = 1 := fun x =>
    coord_fixed (x := ⟨x.1, hF x.2⟩) (h x.1 x.2).2
  have hinj : Function.Injective φ := by
    intro x x' hx
    have h0 := congrFun hx 0
    simp only [φ] at h0
    have hc := coord_injective (Prod.ext ((hfix x).1.trans (hfix x').1.symm) h0)
    exact Subtype.ext (congrArg (fun z : torusSub K => (z : adjointGroup .G2 K)) hc)
  have hpow : ∀ x i, φ x i ^ 3 = 1 := fun x i => (hfix x).2
  have := CFSG.RankThree.PartOne.BRANCH.card_le_pow_of_injective_units (L := K) (k := 1) (r := 3)
    (by norm_num) φ hinj hpow
  simpa using this

end CFSG.AGLEmbedding.KFactProofs.G2Q
