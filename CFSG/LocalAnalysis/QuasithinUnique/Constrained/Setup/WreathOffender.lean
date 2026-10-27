module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathBase
public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement

section Res

variable {W : Type*} [CommGroup W]

@[expose] def resHom {X : Type*} [Group X] (φ : X →* MulAut W) (H : Subgroup W)
    (h : ∀ x, φ x • H = H) : X →* MulAut ↥H where
  toFun x := restrictAut H (φ x) (h x)
  map_one' := by
    rw [restrictAut_eq_one_iff]
    intro x _
    simp
  map_mul' x y := by
    ext z
    show ((φ (x * y) : MulAut W) (z : W)) = (φ x) ((φ y) (z : W))
    rw [map_mul]
    rfl

end Res

section Weight

variable {W : Type*} [CommGroup W] {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W}
  {hF : PlaneFamily I} {A : Subgroup (MulAut W)}

omit [DecidableEq ι] in
theorem PlaneFamily.finite_W (hF : PlaneFamily I) : Finite W := by
  classical
  have : ∀ i, Finite ↥(I i) := fun i =>
    Nat.finite_of_card_ne_zero (by rw [hF.card_I i]; norm_num)
  exact Finite.of_equiv _ hF.coordEquiv.toEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem finite_mulAut_of_finite [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

structure ElemAbelianData (hF : PlaneFamily I) (A : Subgroup (MulAut W)) : Prop where
  le_permuting : A ≤ permuting I
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  sq : ∀ a ∈ A, a ^ 2 = 1

variable (h : ElemAbelianData hF A)

@[expose] noncomputable def actHom : ↥A →* Equiv.Perm ι :=
  (permHom hF).comp (Subgroup.inclusion h.le_permuting)

omit [DecidableEq ι] in
theorem smul_plane (a : ↥A) (i : ι) :
    (a : MulAut W) • I i = I (actHom h a i) :=
  permHom_spec hF ⟨a, h.le_permuting a.2⟩ i

noncomputable abbrev actGp : Subgroup (Equiv.Perm ι) := (actHom h).range

@[expose] noncomputable def stabA (i₀ : ι) : Subgroup ↥A :=
  (MulAction.stabilizer (Equiv.Perm ι) i₀).comap (actHom h)

omit [DecidableEq ι] in
theorem mem_stabA {i₀ : ι} {a : ↥A} : a ∈ stabA h i₀ ↔ actHom h a i₀ = i₀ := by
  simp [stabA, MulAction.mem_stabilizer_iff]

@[expose] noncomputable def kerOrbit (i₀ : ι) : Subgroup ↥A where
  carrier := {a | ∀ i ∈ MulAction.orbit ↥(actGp h) i₀, ∀ x ∈ I i, (a : MulAut W) x = x}
  one_mem' := fun i _ x _ => rfl
  mul_mem' := fun {a b} ha hb i hi x hx => by
    show ((a : MulAut W) * (b : MulAut W)) x = x
    rw [MulAut.mul_apply, hb i hi x hx, ha i hi x hx]
  inv_mem' := fun {a} ha i hi x hx => by
    show ((a : MulAut W)⁻¹) x = x
    exact (MulEquiv.symm_apply_eq _).mpr (ha i hi x hx).symm

omit [DecidableEq ι] in
theorem smul_plane_stabA (i₀ : ι) (a : ↥(stabA h i₀)) :
    ((a : ↥A) : MulAut W) • I i₀ = I i₀ := by
  rw [smul_plane h (a : ↥A) i₀, (mem_stabA h).mp a.2]

@[expose] noncomputable def stabRes (i₀ : ι) : ↥(stabA h i₀) →* MulAut ↥(I i₀) :=
  resHom (A.subtype.comp (stabA h i₀).subtype) (I i₀) fun a => smul_plane_stabA h i₀ a

omit [DecidableEq ι] in
theorem stabA_index (i₀ : ι) :
    (stabA h i₀).index = (MulAction.orbit ↥(actGp h) i₀).ncard := by
  have h1 : stabA h i₀ =
      (MulAction.stabilizer ↥(actGp h) i₀).comap (actHom h).rangeRestrict := by
    ext a
    rw [mem_stabA, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  rw [h1, Subgroup.index_comap_of_surjective _ (actHom h).rangeRestrict_surjective,
    MulAction.index_stabilizer]

@[expose] def fixPlane (i₀ : ι) : Subgroup ↥(I i₀) where
  carrier := {x | ∀ a : ↥(stabA h i₀), ((a : ↥A) : MulAut W) (x : W) = x}
  one_mem' := fun a => by simp
  mul_mem' := fun {x y} hx hy a => by
    have h1 := hx a
    have h2 := hy a
    simp only [Subgroup.coe_mul, map_mul, h1, h2]
  inv_mem' := fun {x} hx a => by
    have h1 := hx a
    simp only [Subgroup.coe_inv, map_inv, h1]

omit [DecidableEq ι] in
theorem isPGroup_range_stabRes (i₀ : ι) : IsPGroup 2 ↥(stabRes h i₀).range := by
  intro r
  refine ⟨1, ?_⟩
  obtain ⟨a, ha⟩ := r.2
  have h1 : (a : ↥(stabA h i₀)) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have := h.sq _ (a : ↥A).2
    simpa using this
  have h2 : (r : MulAut ↥(I i₀)) ^ 2 = 1 := by
    rw [← ha, ← map_pow, h1, map_one]
  apply Subtype.ext
  simpa using h2

omit [DecidableEq ι] in
theorem ElemAbelianData.finite (_h : ElemAbelianData hF A) : Finite ↥A := by
  have := hF.finite_W
  have := finite_mulAut_of_finite (W := W)
  infer_instance

omit [DecidableEq ι] in
theorem stabRes_eq_one_iff (i₀ : ι) (k : ↥(stabA h i₀)) :
    stabRes h i₀ k = 1 ↔ ∀ x ∈ I i₀, ((k : ↥A) : MulAut W) x = x :=
  restrictAut_eq_one_iff (I i₀) ((k : ↥A) : MulAut W) (smul_plane_stabA h i₀ k)

omit [DecidableEq ι] in
theorem range_stabRes_sq (i₀ : ι) : ∀ r ∈ (stabRes h i₀).range, r ^ 2 = 1 := by
  rintro r ⟨a, rfl⟩
  have h1 : (a : ↥(stabA h i₀)) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have := h.sq _ (a : ↥A).2
    simpa using this
  rw [← map_pow, h1, map_one]

omit [DecidableEq ι] in
theorem card_range_stabRes_le (i₀ : ι) : Nat.card ↥(stabRes h i₀).range ≤ 2 := by
  have := hF.klein i₀
  exact card_le_two_of_isPGroup (isPGroup_range_stabRes h i₀)

omit [DecidableEq ι] in
theorem card_range_mul_card_fixPlane_le (i₀ : ι) :
    Nat.card ↥(stabRes h i₀).range * Nat.card ↥(fixPlane h i₀) ≤ 4 := by
  have hk := hF.klein i₀
  have hfinI : Finite ↥(I i₀) := Nat.finite_of_card_ne_zero (by rw [hF.card_I i₀]; norm_num)
  by_cases hR : (stabRes h i₀).range = ⊥
  · rw [hR, Subgroup.card_bot, one_mul]
    calc Nat.card ↥(fixPlane h i₀) ≤ Nat.card ↥(I i₀) := Subgroup.card_le_card_group _
      _ = 4 := hF.card_I i₀
  · obtain ⟨σ, hσ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
    have hσ1 : (σ : MulAut ↥(I i₀)) ≠ 1 := fun h1 => hσ (Subtype.ext h1)
    have hσ2 : (σ : MulAut ↥(I i₀)) * σ = 1 := by
      rw [← pow_two]
      exact range_stabRes_sq h i₀ σ σ.2
    obtain ⟨a, ha⟩ := σ.2
    have hfix : Nat.card ↥(fixPlane h i₀) ≤ 2 := by
      have hc := card_fixed_of_invol hσ1 hσ2
      rw [← hc]
      refine Nat.card_le_card_of_injective (fun x => ⟨x, ?_⟩) ?_
      · show (σ : MulAut ↥(I i₀)) x = x
        rw [← ha]
        apply Subtype.ext
        exact x.2 a
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        exact Subtype.ext h1
    calc Nat.card ↥(stabRes h i₀).range * Nat.card ↥(fixPlane h i₀) ≤ 2 * 2 :=
          Nat.mul_le_mul (card_range_stabRes_le h i₀) hfix
      _ = 4 := by norm_num

omit [DecidableEq ι] in
theorem map_ker_stabRes_le (i₀ : ι) :
    ((stabRes h i₀).ker).map (stabA h i₀).subtype ≤ kerOrbit h i₀ := by
  rintro _ ⟨k, hk, rfl⟩ i hi x hx
  obtain ⟨b, rfl⟩ := MulAction.mem_orbit_iff.mp hi
  obtain ⟨c, hc⟩ := b.2
  have hbi : (b • i₀ : ι) = actHom h c i₀ := by
    show (b : Equiv.Perm ι) i₀ = _
    rw [← hc]
  rw [hbi, ← smul_plane h c i₀] at hx
  obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hky : ((k : ↥A) : MulAut W) y = y := (stabRes_eq_one_iff h i₀ k).mp hk y hy
  have hcomm := h.comm _ (k : ↥A).2 _ c.2
  show ((k : ↥A) : MulAut W) ((c : MulAut W) y) = (c : MulAut W) y
  have := congrArg (fun g : MulAut W => g y) hcomm
  simp only [MulAut.mul_apply] at this
  rw [this, hky]

omit [DecidableEq ι] in
theorem kerOrbit_index_le (i₀ : ι) :
    (kerOrbit h i₀).index ≤
      Nat.card ↥(stabRes h i₀).range * (MulAction.orbit ↥(actGp h) i₀).ncard := by
  have hfin : Finite ↥A := h.finite
  set K := stabA h i₀ with hK
  set K₀ := (stabRes h i₀).ker with hK₀
  set K₀' := K₀.map K.subtype with hK₀'
  have hle : K₀' ≤ kerOrbit h i₀ := map_ker_stabRes_le h i₀
  have hK₀K : K₀' ≤ K := Subgroup.map_subtype_le K₀
  have h1 : (kerOrbit h i₀).index ∣ K₀'.index := Subgroup.index_dvd_of_le hle
  have h2 : K₀'.relIndex K * K.index = K₀'.index := Subgroup.relIndex_mul_index hK₀K
  have h3 : K₀'.relIndex K = Nat.card ↥(stabRes h i₀).range := by
    rw [Subgroup.relIndex]
    have : K₀'.subgroupOf K = K₀ :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective K₀
    rw [this, Subgroup.index_ker]
  have hpos : K₀'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (kerOrbit h i₀).index ≤ K₀'.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h1
    _ = Nat.card ↥(stabRes h i₀).range * (MulAction.orbit ↥(actGp h) i₀).ncard := by
      rw [← h2, h3, stabA_index h]

omit [DecidableEq ι] in
theorem orbit_ineq (i₀ : ι) :
    (kerOrbit h i₀).index * Nat.card ↥(fixPlane h i₀) ≤
      4 * (MulAction.orbit ↥(actGp h) i₀).ncard := by
  calc (kerOrbit h i₀).index * Nat.card ↥(fixPlane h i₀)
      ≤ (Nat.card ↥(stabRes h i₀).range * (MulAction.orbit ↥(actGp h) i₀).ncard) *
          Nat.card ↥(fixPlane h i₀) := Nat.mul_le_mul_right _ (kerOrbit_index_le h i₀)
    _ = (Nat.card ↥(stabRes h i₀).range * Nat.card ↥(fixPlane h i₀)) *
          (MulAction.orbit ↥(actGp h) i₀).ncard := by ring
    _ ≤ 4 * (MulAction.orbit ↥(actGp h) i₀).ncard :=
          Nat.mul_le_mul_right _ (card_range_mul_card_fixPlane_le h i₀)

open CFSG.Quasithin (fixV)

abbrev OrbitQuot (h : ElemAbelianData hF A) : Type _ :=
  MulAction.orbitRel.Quotient ↥(actGp h) ι

omit [DecidableEq ι] in
theorem mem_orbit_out (h : ElemAbelianData hF A) (i : ι) :
    i ∈ MulAction.orbit ↥(actGp h) ((Quotient.mk'' i : OrbitQuot h).out : ι) := by
  have h1 : Quotient.mk'' ((Quotient.mk'' i : OrbitQuot h).out : ι) = (Quotient.mk'' i : OrbitQuot h) :=
    Quotient.out_eq' _
  rw [Quotient.eq''] at h1
  exact MulAction.mem_orbit_symm.mp (MulAction.orbitRel_apply.mp h1)

omit [DecidableEq ι] in
theorem iInf_kerOrbit_eq_bot (h : ElemAbelianData hF A) :
    (⨅ ω : OrbitQuot h, kerOrbit h ω.out) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_iInf] at ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show (a : MulAut W) = 1
  apply hF.autEq_of_forall_plane
  intro i x hx
  exact ha (Quotient.mk'' i) i (mem_orbit_out h i) x hx

omit [DecidableEq ι] in
theorem card_A_le_prod_index (h : ElemAbelianData hF A) [Fintype (OrbitQuot h)] :
    Nat.card ↥A ≤ ∏ ω : OrbitQuot h, (kerOrbit h ω.out).index := by
  have h1 := Subgroup.index_iInf_le (fun ω : OrbitQuot h => kerOrbit h ω.out)
  rw [iInf_kerOrbit_eq_bot h, Subgroup.index_bot] at h1
  exact h1

theorem card_fixV_le (h : ElemAbelianData hF A) [Fintype (OrbitQuot h)] :
    Nat.card ↥(fixV A) ≤ ∏ ω : OrbitQuot h, Nat.card ↥(fixPlane h ω.out) := by
  classical
  have hfinI : ∀ i, Finite ↥(fixPlane h i) := fun i =>
    have : Finite ↥(I i) := Nat.finite_of_card_ne_zero (by rw [hF.card_I i]; norm_num)
    inferInstance
  rw [← Nat.card_pi]
  have hmem : ∀ (c : ↥(fixV A)) (i : ι), ((hF.coord i (c : W) : ↥(I i)) : ↥(I i)) ∈ fixPlane h i := by
    intro c i a
    have hc : ((a : ↥A) : MulAut W) (c : W) = (c : W) := c.2 _ (a : ↥A).2
    have hσ : actHom h (a : ↥A) i = i := (mem_stabA h).mp a.2
    have := coord_perm hF (g := ((a : ↥A) : MulAut W)) (σ := actHom h (a : ↥A))
      (fun j => smul_plane h (a : ↥A) j) i (c : W)
    rw [hc] at this
    rw [hσ] at this
    exact this.symm
  let f : ↥(fixV A) → ∀ ω : OrbitQuot h, ↥(fixPlane h ω.out) :=
    fun c ω => ⟨hF.coord ω.out (c : W), hmem c ω.out⟩
  apply Nat.card_le_card_of_injective f
  intro c d hcd
  apply Subtype.ext
  have hcoord : ∀ ω : OrbitQuot h, hF.coord ω.out (c : W) = hF.coord ω.out (d : W) := fun ω =>
    congrArg Subtype.val (congrFun hcd ω)
  have main : ∀ (ω : OrbitQuot h) (a : ↥A),
      hF.coord (actHom h a ω.out) (c : W) = hF.coord (actHom h a ω.out) (d : W) := by
    intro ω a
    have key : ∀ e : ↥(fixV A), ((hF.coord (actHom h a ω.out) (e : W) : ↥(I _)) : W) =
        (a : MulAut W) ((hF.coord ω.out (e : W) : ↥(I _)) : W) := by
      intro e
      have := coord_perm hF (g := (a : MulAut W)) (σ := actHom h a)
        (fun j => smul_plane h a j) ω.out (e : W)
      rw [e.2 _ a.2] at this
      exact this
    apply Subtype.ext
    rw [key c, key d, hcoord ω]
  apply hF.eq_of_coord_eq
  intro i
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp (mem_orbit_out h i)
  obtain ⟨a, ha⟩ := b.2
  have hbi : actHom h a ((Quotient.mk'' i : OrbitQuot h).out : ι) = i := by
    have h1 : actHom h a ((Quotient.mk'' i : OrbitQuot h).out : ι) =
        b • ((Quotient.mk'' i : OrbitQuot h).out : ι) := by
      show _ = (b : Equiv.Perm ι) _
      rw [← ha]
    exact h1.trans hb
  have := main (Quotient.mk'' i) a
  rwa [hbi] at this

theorem four_mul_le_four_pow (n : ℕ) : 4 * n ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · nlinarith

theorem four_mul_lt_four_pow {n : ℕ} (hn : 2 ≤ n) : 4 * n < 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

omit [DecidableEq ι] in
theorem orbit_eq_orbit_out (h : ElemAbelianData hF A) (ω : OrbitQuot h) :
    ω.orbit = MulAction.orbit ↥(actGp h) ω.out :=
  MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq'

omit [DecidableEq ι] in
theorem sum_orbit_ncard (h : ElemAbelianData hF A) [Fintype (OrbitQuot h)] :
    ∑ ω : OrbitQuot h, ω.orbit.ncard = Fintype.card ι := by
  have h1 := Nat.card_congr (MulAction.selfEquivSigmaOrbits' ↥(actGp h) ι)
  rw [Nat.card_sigma, Nat.card_eq_fintype_card] at h1
  rw [h1]
  exact Finset.sum_congr rfl fun ω _ => (Nat.card_coe_set_eq _).symm

theorem weight_le (h : ElemAbelianData hF A) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ 4 ^ Fintype.card ι := by
  classical
  have : Finite (OrbitQuot h) := Quotient.finite _
  have : Fintype (OrbitQuot h) := Fintype.ofFinite _
  calc Nat.card ↥A * Nat.card ↥(fixV A)
      ≤ (∏ ω : OrbitQuot h, (kerOrbit h ω.out).index) *
          ∏ ω : OrbitQuot h, Nat.card ↥(fixPlane h ω.out) :=
        Nat.mul_le_mul (card_A_le_prod_index h) (card_fixV_le h)
    _ = ∏ ω : OrbitQuot h, ((kerOrbit h ω.out).index * Nat.card ↥(fixPlane h ω.out)) :=
        Finset.prod_mul_distrib.symm
    _ ≤ ∏ ω : OrbitQuot h, (4 * ω.orbit.ncard) := by
        refine Finset.prod_le_prod fun ω _ => ?_
        rw [orbit_eq_orbit_out h ω]
        exact orbit_ineq h ω.out
    _ ≤ ∏ ω : OrbitQuot h, 4 ^ ω.orbit.ncard :=
        Finset.prod_le_prod fun ω _ => four_mul_le_four_pow _
    _ = 4 ^ ∑ ω : OrbitQuot h, ω.orbit.ncard := Finset.prod_pow_eq_pow_sum _ _ _
    _ = 4 ^ Fintype.card ι := by rw [sum_orbit_ncard h]

theorem weight_lt_of_moved (h : ElemAbelianData hF A) (hmv : ∃ a : ↥A, ∃ i, actHom h a i ≠ i) :
    Nat.card ↥A * Nat.card ↥(fixV A) < 4 ^ Fintype.card ι := by
  classical
  have : Finite (OrbitQuot h) := Quotient.finite _
  have : Fintype (OrbitQuot h) := Fintype.ofFinite _
  obtain ⟨a, i, hai⟩ := hmv
  set ω₀ : OrbitQuot h := Quotient.mk'' i with hω₀
  have hfinι : Finite ι := inferInstance
  have hi : i ∈ ω₀.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
  have hai' : actHom h a i ∈ ω₀.orbit := by
    rw [orbit_eq_orbit_out h ω₀]
    have := mem_orbit_out h i
    rw [← MulAction.orbit_eq_iff.mpr this] 
    exact ⟨⟨actHom h a, a, rfl⟩, rfl⟩
  have hn : 2 ≤ ω₀.orbit.ncard := by
    have : 1 < ω₀.orbit.ncard :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨i, actHom h a i, hi, hai', fun e => hai e.symm⟩
    omega
  have hle : ∀ ω : OrbitQuot h, (kerOrbit h ω.out).index * Nat.card ↥(fixPlane h ω.out) ≤
      4 * ω.orbit.ncard := fun ω => by
    rw [orbit_eq_orbit_out h ω]
    exact orbit_ineq h ω.out
  have hprod : Nat.card ↥A * Nat.card ↥(fixV A) ≤
      ∏ ω : OrbitQuot h, (4 * ω.orbit.ncard) := by
    calc Nat.card ↥A * Nat.card ↥(fixV A)
        ≤ (∏ ω : OrbitQuot h, (kerOrbit h ω.out).index) *
            ∏ ω : OrbitQuot h, Nat.card ↥(fixPlane h ω.out) :=
          Nat.mul_le_mul (card_A_le_prod_index h) (card_fixV_le h)
      _ = ∏ ω : OrbitQuot h, ((kerOrbit h ω.out).index * Nat.card ↥(fixPlane h ω.out)) :=
          Finset.prod_mul_distrib.symm
      _ ≤ ∏ ω : OrbitQuot h, (4 * ω.orbit.ncard) :=
          Finset.prod_le_prod fun ω _ => hle ω
  have hsplit1 : ∏ ω : OrbitQuot h, (4 * ω.orbit.ncard) =
      (4 * ω₀.orbit.ncard) * ∏ ω ∈ Finset.univ.erase ω₀, (4 * ω.orbit.ncard) :=
    (Finset.mul_prod_erase Finset.univ (fun ω => 4 * ω.orbit.ncard) (Finset.mem_univ ω₀)).symm
  have hsplit2 : ∏ ω : OrbitQuot h, 4 ^ ω.orbit.ncard =
      (4 ^ ω₀.orbit.ncard) * ∏ ω ∈ Finset.univ.erase ω₀, 4 ^ ω.orbit.ncard :=
    (Finset.mul_prod_erase Finset.univ (fun ω => 4 ^ ω.orbit.ncard) (Finset.mem_univ ω₀)).symm
  have hrest : ∏ ω ∈ Finset.univ.erase ω₀, (4 * ω.orbit.ncard) ≤
      ∏ ω ∈ Finset.univ.erase ω₀, 4 ^ ω.orbit.ncard :=
    Finset.prod_le_prod fun ω _ => four_mul_le_four_pow _
  have hpos : 0 < ∏ ω ∈ Finset.univ.erase ω₀, 4 ^ ω.orbit.ncard :=
    Finset.prod_pos fun ω _ => pow_pos (by norm_num) _
  calc Nat.card ↥A * Nat.card ↥(fixV A)
      ≤ ∏ ω : OrbitQuot h, (4 * ω.orbit.ncard) := hprod
    _ = (4 * ω₀.orbit.ncard) * ∏ ω ∈ Finset.univ.erase ω₀, (4 * ω.orbit.ncard) := hsplit1
    _ ≤ (4 * ω₀.orbit.ncard) * ∏ ω ∈ Finset.univ.erase ω₀, 4 ^ ω.orbit.ncard :=
        Nat.mul_le_mul_left _ hrest
    _ < (4 ^ ω₀.orbit.ncard) * ∏ ω ∈ Finset.univ.erase ω₀, 4 ^ ω.orbit.ncard :=
        Nat.mul_lt_mul_of_pos_right (four_mul_lt_four_pow hn) hpos
    _ = ∏ ω : OrbitQuot h, 4 ^ ω.orbit.ncard := hsplit2.symm
    _ = 4 ^ ∑ ω : OrbitQuot h, ω.orbit.ncard := Finset.prod_pow_eq_pow_sum _ _ _
    _ = 4 ^ Fintype.card ι := by rw [sum_orbit_ncard h]

omit [DecidableEq ι] in
theorem PlaneFamily.card_W (hF : PlaneFamily I) : Nat.card W = 4 ^ Fintype.card ι := by
  classical
  rw [← Nat.card_congr hF.coordEquiv.toEquiv, Nat.card_pi]
  simp [hF.card_I]

end Weight

section BaseCase

variable {W : Type*} [CommGroup W] {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W}
  {hF : PlaneFamily I} {A : Subgroup (MulAut W)}

open CFSG.Quasithin (fixV)

@[expose] def resI (hB : A ≤ baseGp I) (i : ι) : ↥A →* MulAut ↥(I i) :=
  resHom A.subtype (I i) fun a => hB a.2 i

omit [Fintype ι] [DecidableEq ι] in
theorem resI_eq_one_iff (hB : A ≤ baseGp I) (i : ι) (a : ↥A) :
    resI hB i a = 1 ↔ ∀ x ∈ I i, (a : MulAut W) x = x :=
  restrictAut_eq_one_iff (I i) (a : MulAut W) (hB a.2 i)

@[expose] def Rg (hB : A ≤ baseGp I) (i : ι) : Subgroup (MulAut ↥(I i)) := (resI hB i).range

@[expose] def Ffix (I : ι → Subgroup W) (A : Subgroup (MulAut W)) (i : ι) : Subgroup ↥(I i) where
  carrier := {x | ∀ a : ↥A, (a : MulAut W) (x : W) = x}
  one_mem' := fun a => by simp
  mul_mem' := fun {x y} hx hy a => by
    have h1 := hx a
    have h2 := hy a
    simp only [Subgroup.coe_mul, map_mul, h1, h2]
  inv_mem' := fun {x} hx a => by
    have h1 := hx a
    simp only [Subgroup.coe_inv, map_inv, h1]

omit [Fintype ι] [DecidableEq ι] in
theorem Rg_sq (h : ElemAbelianData hF A) (hB : A ≤ baseGp I) (i : ι) :
    ∀ r ∈ Rg hB i, r ^ 2 = 1 := by
  rintro r ⟨a, rfl⟩
  have h1 : a ^ 2 = 1 := by
    apply Subtype.ext
    have := h.sq _ a.2
    simpa using this
  rw [← map_pow, h1, map_one]

omit [Fintype ι] [DecidableEq ι] in
theorem card_Rg_le (h : ElemAbelianData hF A) (hB : A ≤ baseGp I) (i : ι) :
    Nat.card ↥(Rg hB i) ≤ 2 := by
  have hk := hF.klein i
  refine card_le_two_of_isPGroup ?_
  intro r
  refine ⟨1, ?_⟩
  have h2 : (r : MulAut ↥(I i)) ^ 2 = 1 := Rg_sq h hB i r r.2
  apply Subtype.ext
  simpa using h2

omit [Fintype ι] [DecidableEq ι] in
theorem card_Rg_mul_card_Ffix_le (h : ElemAbelianData hF A) (hB : A ≤ baseGp I) (i : ι) :
    Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i) ≤ 4 := by
  have hk := hF.klein i
  have hfinI : Finite ↥(I i) := Nat.finite_of_card_ne_zero (by rw [hF.card_I i]; norm_num)
  by_cases hR : Rg hB i = ⊥
  · rw [hR, Subgroup.card_bot, one_mul]
    calc Nat.card ↥(Ffix I A i) ≤ Nat.card ↥(I i) := Subgroup.card_le_card_group _
      _ = 4 := hF.card_I i
  · obtain ⟨σ, hσ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
    have hσ1 : (σ : MulAut ↥(I i)) ≠ 1 := fun h1 => hσ (Subtype.ext h1)
    have hσ2 : (σ : MulAut ↥(I i)) * σ = 1 := by
      rw [← pow_two]
      exact Rg_sq h hB i σ σ.2
    obtain ⟨a, ha⟩ := σ.2
    have hfix : Nat.card ↥(Ffix I A i) ≤ 2 := by
      have hc := card_fixed_of_invol hσ1 hσ2
      rw [← hc]
      refine Nat.card_le_card_of_injective (fun x => ⟨x, ?_⟩) ?_
      · show (σ : MulAut ↥(I i)) x = x
        rw [← ha]
        apply Subtype.ext
        exact x.2 a
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        exact Subtype.ext h1
    calc Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i) ≤ 2 * 2 :=
          Nat.mul_le_mul (card_Rg_le h hB i) hfix
      _ = 4 := by norm_num

@[expose] def phiA (hB : A ≤ baseGp I) : ↥A → ∀ i, ↥(Rg hB i) :=
  fun a i => ⟨resI hB i a, a, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem phiA_injective (hF : PlaneFamily I) (hB : A ≤ baseGp I) : Function.Injective (phiA hB) := by
  intro a a' haa'
  apply Subtype.ext
  apply hF.autEq_of_forall_plane
  intro i x hx
  have h1 := congrArg Subtype.val (congrFun haa' i)
  have := congrArg (fun r : MulAut ↥(I i) => ((r ⟨x, hx⟩ : ↥(I i)) : W)) h1
  exact this

omit [DecidableEq ι] in
theorem card_A_le_prod_Rg (h : ElemAbelianData hF A) (hB : A ≤ baseGp I) :
    Nat.card ↥A ≤ ∏ i, Nat.card ↥(Rg hB i) := by
  classical
  rw [← Nat.card_pi]
  have hfin : Finite ↥A := h.finite
  have : ∀ i, Finite ↥(Rg hB i) := fun i => have := hF.klein i; inferInstance
  exact Nat.card_le_card_of_injective _ (phiA_injective hF hB)

theorem card_fixV_le_prod_Ffix (hF : PlaneFamily I) (hB : A ≤ baseGp I) :
    Nat.card ↥(fixV A) ≤ ∏ i, Nat.card ↥(Ffix I A i) := by
  classical
  have : ∀ i, Finite ↥(Ffix I A i) := fun i =>
    have : Finite ↥(I i) := Nat.finite_of_card_ne_zero (by rw [hF.card_I i]; norm_num)
    inferInstance
  rw [← Nat.card_pi]
  have hmem : ∀ (c : ↥(fixV A)) (i : ι), hF.coord i (c : W) ∈ Ffix I A i := by
    intro c i a
    have hc : ((a : ↥A) : MulAut W) (c : W) = (c : W) := c.2 _ a.2
    have := coord_perm hF (g := (a : MulAut W)) (σ := 1)
      (fun j => by simpa using hB a.2 j) i (c : W)
    rw [hc] at this
    exact this.symm
  refine Nat.card_le_card_of_injective
    (fun c i => (⟨hF.coord i (c : W), hmem c i⟩ : ↥(Ffix I A i))) ?_
  intro c d hcd
  apply Subtype.ext
  apply hF.eq_of_coord_eq
  intro i
  exact congrArg Subtype.val (congrFun hcd i)

theorem prod_eq_four_of_le {x : ι → ℕ} (hx : ∀ i, x i ≤ 4)
    (hprod : ∏ i, x i = 4 ^ Fintype.card ι) : ∀ i, x i = 4 := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  have hjlt : x j < 4 := lt_of_le_of_ne (hx j) hj
  have hrest : ∏ i ∈ Finset.univ.erase j, x i ≤ 4 ^ (Fintype.card ι - 1) := by
    calc ∏ i ∈ Finset.univ.erase j, x i ≤ ∏ i ∈ Finset.univ.erase j, 4 :=
          Finset.prod_le_prod fun i _ => hx i
      _ = 4 ^ (Fintype.card ι - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  have hr : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  have h4 : (4 : ℕ) ^ Fintype.card ι = 4 * 4 ^ (Fintype.card ι - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 4 ^ (Fintype.card ι - 1) := pow_pos (by norm_num) _
  have hsplit : 4 ^ Fintype.card ι = x j * ∏ i ∈ Finset.univ.erase j, x i := by
    rw [← hprod]
    exact (Finset.mul_prod_erase Finset.univ x (Finset.mem_univ j)).symm
  have : x j * ∏ i ∈ Finset.univ.erase j, x i ≤ x j * 4 ^ (Fintype.card ι - 1) :=
    Nat.mul_le_mul_left _ hrest
  have h5 : x j * 4 ^ (Fintype.card ι - 1) < 4 * 4 ^ (Fintype.card ι - 1) :=
    Nat.mul_lt_mul_of_pos_right hjlt hpos
  omega

theorem eq_case_cards (h : ElemAbelianData hF A) (hB : A ≤ baseGp I)
    (hw : Nat.card ↥A * Nat.card ↥(fixV A) = 4 ^ Fintype.card ι) :
    Nat.card ↥A = ∏ i, Nat.card ↥(Rg hB i) ∧ Nat.card ↥(fixV A) = ∏ i, Nat.card ↥(Ffix I A i) ∧
      ∀ i, Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i) = 4 := by
  classical
  have hfin : Finite ↥A := h.finite
  have hfinW := hF.finite_W
  have h1 := card_A_le_prod_Rg h hB
  have h2 := card_fixV_le_prod_Ffix hF hB
  have h3 : ∏ i, (Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i)) ≤ 4 ^ Fintype.card ι := by
    calc ∏ i, (Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i)) ≤ ∏ _i : ι, 4 :=
          Finset.prod_le_prod fun i _ => card_Rg_mul_card_Ffix_le h hB i
      _ = 4 ^ Fintype.card ι := by simp
  have hA0 : 0 < Nat.card ↥A := Nat.card_pos
  have hC0 : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  rw [Finset.prod_mul_distrib] at h3
  set α := ∏ i, Nat.card ↥(Rg hB i) with hα
  set γ := ∏ i, Nat.card ↥(Ffix I A i) with hγ
  have hα0 : 0 < α := Finset.prod_pos fun i _ => by
    have := hF.klein i
    exact Nat.card_pos
  have hAα : Nat.card ↥A = α := by
    by_contra hne
    have hlt : Nat.card ↥A < α := lt_of_le_of_ne h1 hne
    have : Nat.card ↥A * Nat.card ↥(fixV A) < α * γ :=
      calc Nat.card ↥A * Nat.card ↥(fixV A) < α * Nat.card ↥(fixV A) :=
            Nat.mul_lt_mul_of_pos_right hlt hC0
        _ ≤ α * γ := Nat.mul_le_mul_left _ h2
    omega
  have hCγ : Nat.card ↥(fixV A) = γ := by
    by_contra hne
    have hlt : Nat.card ↥(fixV A) < γ := lt_of_le_of_ne h2 hne
    have : Nat.card ↥A * Nat.card ↥(fixV A) < α * γ :=
      calc Nat.card ↥A * Nat.card ↥(fixV A) = α * Nat.card ↥(fixV A) := by rw [hAα]
        _ < α * γ := Nat.mul_lt_mul_of_pos_left hlt hα0
    omega
  refine ⟨hAα, hCγ, ?_⟩
  apply prod_eq_four_of_le (x := fun i => Nat.card ↥(Rg hB i) * Nat.card ↥(Ffix I A i))
  · exact fun i => card_Rg_mul_card_Ffix_le h hB i
  · rw [Finset.prod_mul_distrib, ← hw, hAα, hCγ]

theorem le_baseGp_of_weight_eq (h : ElemAbelianData hF A)
    (hw : Nat.card ↥A * Nat.card ↥(fixV A) = 4 ^ Fintype.card ι) : A ≤ baseGp I := by
  intro a ha i
  by_contra hne
  have hmv : ∃ a : ↥A, ∃ i, actHom h a i ≠ i := by
    refine ⟨⟨a, ha⟩, i, fun hfix => hne ?_⟩
    have := smul_plane h ⟨a, ha⟩ i
    rw [hfix] at this
    exact this
  have := weight_lt_of_moved h hmv
  omega

@[expose] def CoordCond (I : ι → Subgroup W) (J : Finset ι) (t : ∀ i, MulAut ↥(I i))
    (g : MulAut W) : Prop :=
  ∀ i, (∀ x : ↥(I i), g (x : W) = x) ∨
    (i ∈ J ∧ ∀ x : ↥(I i), g (x : W) = ((t i x : ↥(I i)) : W))

structure IsCoordProduct (I : ι → Subgroup W) (A : Subgroup (MulAut W)) (J : Finset ι)
    (t : ∀ i, MulAut ↥(I i)) : Prop where
  invol : ∀ i ∈ J, t i ≠ 1 ∧ t i * t i = 1
  mem_iff : ∀ g : MulAut W, g ∈ A ↔ CoordCond I J t g

open Classical in
@[expose] noncomputable def tOf (hB : A ≤ baseGp I) (i : ι) : MulAut ↥(I i) :=
  if hi : Rg hB i = ⊥ then 1
  else ((Subgroup.ne_bot_iff_exists_ne_one.mp hi).choose : MulAut ↥(I i))

omit [Fintype ι] [DecidableEq ι] in
theorem tOf_spec (hB : A ≤ baseGp I) {i : ι} (hi : Rg hB i ≠ ⊥) :
    tOf hB i ∈ Rg hB i ∧ tOf hB i ≠ 1 := by
  classical
  have h1 := (Subgroup.ne_bot_iff_exists_ne_one.mp hi).choose_spec
  have h2 : tOf hB i = ((Subgroup.ne_bot_iff_exists_ne_one.mp hi).choose : MulAut ↥(I i)) := by
    unfold tOf
    simp [hi]
  rw [h2]
  exact ⟨(Subgroup.ne_bot_iff_exists_ne_one.mp hi).choose.2, fun h => h1 (Subtype.ext h)⟩

theorem isCoordProduct_of_weight_eq (h : ElemAbelianData hF A)
    (hw : Nat.card ↥A * Nat.card ↥(fixV A) = 4 ^ Fintype.card ι) :
    ∃ (J : Finset ι) (t : ∀ i, MulAut ↥(I i)), IsCoordProduct I A J t ∧ (A ≠ ⊥ → J.Nonempty) := by
  classical
  have hB := le_baseGp_of_weight_eq h hw
  obtain ⟨hα, hγ, hprod⟩ := eq_case_cards h hB hw
  have hfin : Finite ↥A := h.finite
  have hfinR : ∀ i, Finite ↥(Rg hB i) := fun i => have := hF.klein i; inferInstance
  have hcard2 : ∀ i, Rg hB i ≠ ⊥ → Nat.card ↥(Rg hB i) = 2 := by
    intro i hi
    have h1 := card_Rg_le h hB i
    have h2 : Nat.card ↥(Rg hB i) ≠ 1 := fun e => hi (Subgroup.eq_bot_of_card_eq _ e)
    have h3 : 0 < Nat.card ↥(Rg hB i) := Nat.card_pos
    omega
  have hone_or : ∀ i, Rg hB i ≠ ⊥ → ∀ r ∈ Rg hB i, r = 1 ∨ r = tOf hB i := by
    intro i hi r hr
    by_cases hr1 : r = 1
    · exact Or.inl hr1
    · right
      obtain ⟨hmem, hne⟩ := tOf_spec hB hi
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(Rg hB i))).mp (hcard2 i hi)
      have e1 : (⟨r, hr⟩ : ↥(Rg hB i)) = y := hy _ (fun e => hr1 (congrArg Subtype.val e))
      have e2 : (⟨tOf hB i, hmem⟩ : ↥(Rg hB i)) = y := hy _ (fun e => hne (congrArg Subtype.val e))
      exact congrArg Subtype.val (e1.trans e2.symm)
  refine ⟨Finset.univ.filter fun i => Rg hB i ≠ ⊥, tOf hB, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have hi' : Rg hB i ≠ ⊥ := (Finset.mem_filter.mp hi).2
    obtain ⟨hmem, hne⟩ := tOf_spec hB hi'
    exact ⟨hne, by rw [← pow_two]; exact Rg_sq h hB i _ hmem⟩
  · intro g
    constructor
    · intro hg i
      by_cases hi : Rg hB i = ⊥
      · left
        have hmem : resI hB i ⟨g, hg⟩ ∈ Rg hB i := ⟨⟨g, hg⟩, rfl⟩
        rw [hi, Subgroup.mem_bot] at hmem
        intro x
        exact (resI_eq_one_iff hB i ⟨g, hg⟩).mp hmem x x.2
      · have hmem : resI hB i ⟨g, hg⟩ ∈ Rg hB i := ⟨⟨g, hg⟩, rfl⟩
        rcases hone_or i hi _ hmem with h1 | h1
        · left
          intro x
          exact (resI_eq_one_iff hB i ⟨g, hg⟩).mp h1 x x.2
        · right
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, fun x => ?_⟩
          have := congrArg (fun r : MulAut ↥(I i) => ((r x : ↥(I i)) : W)) h1
          exact this
    · intro hcond
      have hex : ∀ i, ∃ r : ↥(Rg hB i), ∀ x : ↥(I i), g (x : W) = ((r.1 x : ↥(I i)) : W) := by
        intro i
        rcases hcond i with hid | ⟨hiJ, hx⟩
        · exact ⟨1, fun x => by simpa using hid x⟩
        · have hi' : Rg hB i ≠ ⊥ := (Finset.mem_filter.mp hiJ).2
          exact ⟨⟨tOf hB i, (tOf_spec hB hi').1⟩, hx⟩
      choose y hy using hex
      have hbij : Function.Bijective (phiA hB) := by
        have : Finite (∀ i, ↥(Rg hB i)) := inferInstance
        refine (phiA_injective hF hB).bijective_of_nat_card_le ?_
        rw [Nat.card_pi, ← hα]
      obtain ⟨a, ha⟩ := hbij.2 y
      have hag : (a : MulAut W) = g := by
        apply hF.autEq_of_forall_plane
        intro i x hx
        have h1 : resI hB i a = (y i : MulAut ↥(I i)) := congrArg Subtype.val (congrFun ha i)
        have h2 := hy i ⟨x, hx⟩
        rw [h2]
        have := congrArg (fun r : MulAut ↥(I i) => ((r ⟨x, hx⟩ : ↥(I i)) : W)) h1
        exact this
      rw [← hag]
      exact a.2
  · intro hne
    by_contra hJ
    have hJe : (Finset.univ.filter fun i => Rg hB i ≠ ⊥) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    have hall : ∀ i, Rg hB i = ⊥ := by
      intro i
      by_contra hi
      have : i ∈ (Finset.univ.filter fun i => Rg hB i ≠ ⊥) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hJe] at this
      exact absurd this (Finset.notMem_empty i)
    apply hne
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have : a = 1 := by
      apply hF.autEq_of_forall_plane
      intro i x hx
      have hmem : resI hB i ⟨a, ha⟩ ∈ Rg hB i := ⟨⟨a, ha⟩, rfl⟩
      rw [hall i, Subgroup.mem_bot] at hmem
      rw [(resI_eq_one_iff hB i ⟨a, ha⟩).mp hmem x hx]
      rfl
    exact this

omit [Fintype ι] [DecidableEq ι] in
theorem smul_eq_of_coordCond {J : Finset ι} {t : ∀ i, MulAut ↥(I i)} {g : MulAut W}
    (hg : CoordCond I J t g) (i : ι) : g • I i = I i := by
  ext z
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rcases hg i with hid | ⟨-, ht⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : g x = x := hid ⟨x, hx⟩
      show g x ∈ I i
      rw [h1]
      exact hx
    · intro hz
      exact ⟨z, hz, hid ⟨z, hz⟩⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      show g x ∈ I i
      rw [ht ⟨x, hx⟩]
      exact (t i ⟨x, hx⟩).2
    · intro hz
      obtain ⟨y, hy⟩ := (t i).surjective ⟨z, hz⟩
      refine ⟨(y : W), y.2, ?_⟩
      show g (y : W) = z
      rw [ht y]
      exact congrArg Subtype.val hy

omit [Fintype ι] [DecidableEq ι] in
theorem IsCoordProduct.le_baseGp {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) : A ≤ baseGp I :=
  fun g hg i => smul_eq_of_coordCond ((hC.mem_iff g).mp hg) i

theorem coordCond_blockAut (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    {β : ∀ i, MulAut ↥(I i)} (hβ : ∀ i, β i = 1 ∨ (i ∈ J ∧ β i = t i)) :
    CoordCond I J t (hF.blockAut β) := by
  intro i
  rcases hβ i with h1 | ⟨hiJ, h2⟩
  · left
    intro x
    rw [hF.blockAut_apply β x.2, h1]
    rfl
  · right
    refine ⟨hiJ, fun x => ?_⟩
    rw [hF.blockAut_apply β x.2, h2]

theorem IsCoordProduct.exists_block (hF : PlaneFamily I) {J : Finset ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∈ J) :
    ∃ b ∈ A, ∀ x : ↥(I i), (b : MulAut W) (x : W) = ((t i x : ↥(I i)) : W) := by
  classical
  let β : ∀ j, MulAut ↥(I j) := Pi.mulSingle i (t i)
  have hβ : ∀ j, β j = 1 ∨ (j ∈ J ∧ β j = t j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      right
      exact ⟨hi, by simp [β]⟩
    · left
      simp [β, Pi.mulSingle_eq_of_ne hj]
  refine ⟨hF.blockAut β, (hC.mem_iff _).mpr (coordCond_blockAut hF hβ), fun x => ?_⟩
  rw [hF.blockAut_apply β x.2]
  simp [β]

theorem IsCoordProduct.phiA_bijective (hF : PlaneFamily I) {J : Finset ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t) :
    Function.Bijective (phiA hC.le_baseGp) := by
  refine ⟨phiA_injective hF hC.le_baseGp, fun y => ?_⟩
  have hy : ∀ i, (y i : MulAut ↥(I i)) = 1 ∨ (i ∈ J ∧ (y i : MulAut ↥(I i)) = t i) := by
    intro i
    obtain ⟨a, ha⟩ := (y i).2
    rcases (hC.mem_iff a).mp a.2 i with hid | ⟨hiJ, ht⟩
    · left
      rw [← ha]
      exact (resI_eq_one_iff hC.le_baseGp i a).mpr fun x hx => hid ⟨x, hx⟩
    · right
      refine ⟨hiJ, ?_⟩
      rw [← ha]
      ext x
      exact ht x
  refine ⟨⟨hF.blockAut fun i => (y i : MulAut ↥(I i)),
    (hC.mem_iff _).mpr (coordCond_blockAut hF hy)⟩, ?_⟩
  funext i
  apply Subtype.ext
  ext x
  show hF.blockAut (fun i => (y i : MulAut ↥(I i))) x = _
  rw [hF.blockAut_apply _ x.2]

omit [Fintype ι] [DecidableEq ι] in
theorem IsCoordProduct.Rg_cases {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) {i : ι} (r : MulAut ↥(I i)) (hr : r ∈ Rg hC.le_baseGp i) :
    r = 1 ∨ (i ∈ J ∧ r = t i) := by
  obtain ⟨a, rfl⟩ := hr
  rcases (hC.mem_iff a).mp a.2 i with hid | ⟨hiJ, ht⟩
  · left
    exact (resI_eq_one_iff hC.le_baseGp i a).mpr fun x hx => hid ⟨x, hx⟩
  · right
    refine ⟨hiJ, ?_⟩
    ext x
    exact ht x

omit [Fintype ι] [DecidableEq ι] in
theorem IsCoordProduct.Rg_eq_bot {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∉ J) : Rg hC.le_baseGp i = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rcases hC.Rg_cases r hr with h | ⟨h, -⟩
  · rw [Subgroup.mem_bot]
    exact h
  · exact absurd h hi

theorem IsCoordProduct.mem_Rg (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∈ J) : t i ∈ Rg hC.le_baseGp i := by
  obtain ⟨b, hb, hbx⟩ := hC.exists_block hF hi
  refine ⟨⟨b, hb⟩, ?_⟩
  ext x
  exact hbx x

theorem IsCoordProduct.card_Rg (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∈ J) :
    Nat.card ↥(Rg hC.le_baseGp i) = 2 := by
  rw [Nat.card_eq_two_iff' (1 : ↥(Rg hC.le_baseGp i))]
  refine ⟨⟨t i, hC.mem_Rg hF hi⟩, fun e => (hC.invol i hi).1 (congrArg Subtype.val e),
    fun y hy => ?_⟩
  rcases hC.Rg_cases y.1 y.2 with h | ⟨-, h⟩
  · exact absurd (Subtype.ext h) hy
  · exact Subtype.ext h

omit [DecidableEq ι] in
theorem PlaneFamily.finite_subgroup (hF : PlaneFamily I) (B : Subgroup (MulAut W)) :
    Finite ↥B := by
  have := hF.finite_W
  have := finite_mulAut_of_finite (W := W)
  infer_instance

theorem IsCoordProduct.card_A (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) : Nat.card ↥A = 2 ^ J.card := by
  classical
  have hbij := hC.phiA_bijective hF
  have h1 : Nat.card ↥A = Nat.card (∀ i, ↥(Rg hC.le_baseGp i)) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [h1, Nat.card_pi]
  have h2 : ∀ i, Nat.card ↥(Rg hC.le_baseGp i) = if i ∈ J then 2 else 1 := by
    intro i
    split_ifs with hi
    · exact hC.card_Rg hF hi
    · rw [hC.Rg_eq_bot hi, Subgroup.card_bot]
  simp only [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem coord_mem_Ffix (hF : PlaneFamily I) (hB : A ≤ baseGp I) (c : ↥(fixV A)) (i : ι) :
    hF.coord i (c : W) ∈ Ffix I A i := by
  intro a
  have hc : ((a : ↥A) : MulAut W) (c : W) = (c : W) := c.2 _ a.2
  have := coord_perm hF (g := (a : MulAut W)) (σ := 1)
    (fun j => by simpa using hB a.2 j) i (c : W)
  rw [hc] at this
  exact this.symm

@[expose] noncomputable def psiC (hF : PlaneFamily I) (hB : A ≤ baseGp I) :
    ↥(fixV A) → ∀ i, ↥(Ffix I A i) :=
  fun c i => ⟨hF.coord i (c : W), coord_mem_Ffix hF hB c i⟩

theorem psiC_bijective (hF : PlaneFamily I) (hB : A ≤ baseGp I) :
    Function.Bijective (psiC hF hB) := by
  refine ⟨?_, ?_⟩
  · intro c d hcd
    apply Subtype.ext
    apply hF.eq_of_coord_eq
    intro i
    exact congrArg Subtype.val (congrFun hcd i)
  · intro x
    let c : W := hF.coordEquiv (fun i => (x i : ↥(I i)))
    have hc : c ∈ fixV A := by
      intro a ha
      have h1 : c = ∏ i, ((x i : ↥(I i)) : W) := hF.coordEquiv_apply _
      show (a : MulAut W) c = c
      rw [h1, map_prod]
      exact Finset.prod_congr rfl fun i _ => (x i).2 ⟨a, ha⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    funext i
    apply Subtype.ext
    show hF.coord i c = (x i : ↥(I i))
    simp [PlaneFamily.coord, c]

theorem card_fixV_eq_prod_Ffix (hF : PlaneFamily I) (hB : A ≤ baseGp I) :
    Nat.card ↥(fixV A) = ∏ i, Nat.card ↥(Ffix I A i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr (Equiv.ofBijective _ (psiC_bijective hF hB))

omit [Fintype ι] [DecidableEq ι] in
theorem IsCoordProduct.card_Ffix_of_notMem (hF : PlaneFamily I) {J : Finset ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∉ J) :
    Nat.card ↥(Ffix I A i) = 4 := by
  have : Ffix I A i = ⊤ := by
    rw [eq_top_iff]
    intro x _ a
    rcases (hC.mem_iff a).mp a.2 i with hid | ⟨h, -⟩
    · exact hid x
    · exact absurd h hi
  rw [this, Subgroup.card_top]
  exact hF.card_I i

theorem IsCoordProduct.card_Ffix_of_mem (hF : PlaneFamily I) {J : Finset ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t) {i : ι} (hi : i ∈ J) :
    Nat.card ↥(Ffix I A i) = 2 := by
  have hk := hF.klein i
  obtain ⟨b, hb, hbx⟩ := hC.exists_block hF hi
  have hiff : ∀ x : ↥(I i), x ∈ Ffix I A i ↔ t i x = x := by
    intro x
    constructor
    · intro hx
      have h1 := hx ⟨b, hb⟩
      have h2 := hbx x
      exact Subtype.ext (h2.symm.trans h1)
    · intro hx a
      rcases (hC.mem_iff a).mp a.2 i with hid | ⟨-, ht⟩
      · exact hid x
      · rw [ht x, hx]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_fixed_of_invol (hC.invol i hi).1 (hC.invol i hi).2

theorem prod_two_four (J : Finset ι) :
    ∏ i : ι, (if i ∈ J then 2 else 4 : ℕ) = 2 ^ (2 * Fintype.card ι - J.card) := by
  classical
  have h1 : ∀ i : ι, (if i ∈ J then (2 : ℕ) else 4) = 2 ^ (if i ∈ J then 1 else 2) := by
    intro i
    split_ifs <;> norm_num
  simp only [h1]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hJ : (Finset.univ.filter fun i => i ∈ J) = J := by
    ext i
    simp
  have hJc : (Finset.univ.filter fun i => i ∉ J).card = Fintype.card ι - J.card := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ, hJ]
  rw [hJ, hJc]
  have hle : J.card ≤ Fintype.card ι := Finset.card_le_univ J
  omega

theorem IsCoordProduct.card_fixV (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) :
    Nat.card ↥(fixV A) = 2 ^ (2 * Fintype.card ι - J.card) := by
  rw [card_fixV_eq_prod_Ffix hF hC.le_baseGp]
  have h : ∀ i, Nat.card ↥(Ffix I A i) = if i ∈ J then 2 else 4 := by
    intro i
    split_ifs with hi
    · exact hC.card_Ffix_of_mem hF hi
    · exact hC.card_Ffix_of_notMem hF hi
  simp only [h]
  exact prod_two_four J

theorem IsCoordProduct.weight_eq (hF : PlaneFamily I) {J : Finset ι} {t : ∀ i, MulAut ↥(I i)}
    (hC : IsCoordProduct I A J t) :
    Nat.card ↥A * Nat.card ↥(fixV A) = 4 ^ Fintype.card ι := by
  rw [hC.card_A hF, hC.card_fixV hF, ← pow_add]
  have hle : J.card ≤ Fintype.card ι := Finset.card_le_univ J
  have : J.card + (2 * Fintype.card ι - J.card) = 2 * Fintype.card ι := by omega
  rw [this, pow_mul]
  norm_num

@[expose] def coordGp (I : ι → Subgroup W) (J : Finset ι) (t : ∀ i, MulAut ↥(I i))
    (ht : ∀ i ∈ J, t i * t i = 1) : Subgroup (MulAut W) where
  carrier := {g | CoordCond I J t g}
  one_mem' := fun i => Or.inl fun x => rfl
  mul_mem' := by
    intro g g' hg hg' i
    rcases hg i with hid | ⟨hiJ, hgt⟩
    · rcases hg' i with hid' | ⟨hiJ', hgt'⟩
      · left
        intro x
        show g (g' x) = x
        rw [hid' x, hid x]
      · right
        refine ⟨hiJ', fun x => ?_⟩
        show g (g' x) = _
        rw [hgt' x]
        exact hid (t i x)
    · rcases hg' i with hid' | ⟨hiJ', hgt'⟩
      · right
        refine ⟨hiJ, fun x => ?_⟩
        show g (g' x) = _
        rw [hid' x]
        exact hgt x
      · left
        intro x
        show g (g' x) = x
        rw [hgt' x, hgt (t i x)]
        have := congrArg (fun r : MulAut ↥(I i) => ((r x : ↥(I i)) : W)) (ht i hiJ)
        exact this
  inv_mem' := by
    intro g hg i
    rcases hg i with hid | ⟨hiJ, hgt⟩
    · left
      intro x
      show g⁻¹ x = x
      exact (MulEquiv.symm_apply_eq _).mpr (hid x).symm
    · right
      refine ⟨hiJ, fun x => ?_⟩
      show g⁻¹ x = _
      apply (MulEquiv.symm_apply_eq _).mpr
      rw [hgt (t i x)]
      have := congrArg (fun r : MulAut ↥(I i) => ((r x : ↥(I i)) : W)) (ht i hiJ)
      exact this.symm

omit [Fintype ι] [DecidableEq ι] in
theorem isCoordProduct_coordGp (J : Finset ι) (t : ∀ i, MulAut ↥(I i))
    (ht : ∀ i ∈ J, t i ≠ 1 ∧ t i * t i = 1) :
    IsCoordProduct I (coordGp I J t fun i hi => (ht i hi).2) J t :=
  ⟨ht, fun _ => Iff.rfl⟩

theorem IsCoordProduct.card_J_le_one_of_strict (hF : PlaneFamily I) {J : Finset ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t)
    (hstrict : ∀ B : Subgroup (MulAut W), ⊥ < B → B < A →
      Nat.card ↥B * Nat.card ↥(fixV B) < Nat.card ↥A * Nat.card ↥(fixV A)) :
    J.card ≤ 1 := by
  by_contra hcard
  push Not at hcard
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  have ht : ∀ k ∈ ({i} : Finset ι), t k * t k = 1 := fun k hk => by
    rw [Finset.mem_singleton] at hk
    subst hk
    exact (hC.invol k hi).2
  have hinv : ∀ k ∈ ({i} : Finset ι), t k ≠ 1 ∧ t k * t k = 1 := fun k hk => by
    rw [Finset.mem_singleton] at hk
    subst hk
    exact hC.invol k hi
  have hCB := isCoordProduct_coordGp ({i} : Finset ι) t hinv
  set B := coordGp I {i} t ht with hB
  have hBA : B ≤ A := fun g hg => (hC.mem_iff g).mpr (fun k => by
    rcases hg k with hid | ⟨hk, hx⟩
    · exact Or.inl hid
    · refine Or.inr ⟨?_, hx⟩
      rw [Finset.mem_singleton] at hk
      subst hk
      exact hi)
  have hB1 : ⊥ < B := by
    rw [bot_lt_iff_ne_bot]
    intro hbot
    have h1 : Nat.card ↥B = 2 ^ ({i} : Finset ι).card := hCB.card_A hF
    rw [hbot, Subgroup.card_bot] at h1
    simp at h1
  have hBlt : B < A := by
    refine lt_of_le_of_ne hBA fun heq => ?_
    obtain ⟨b, hbA, hbx⟩ := hC.exists_block hF hj
    have hbB : b ∈ B := heq ▸ hbA
    rcases hbB j with hid | ⟨hjm, -⟩
    · apply (hC.invol j hj).1
      ext x
      have := hbx x
      rw [hid x] at this
      exact this.symm
    · rw [Finset.mem_singleton] at hjm
      exact hij hjm.symm
  have := hstrict B hB1 hBlt
  rw [hCB.weight_eq hF, hC.weight_eq hF] at this
  exact lt_irrefl _ this

theorem IsCoordProduct.no_proper_of_single (hF : PlaneFamily I) {i : ι}
    {t : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A {i} t) (B : Subgroup (MulAut W))
    (hB1 : ⊥ < B) (hBA : B < A) : False := by
  have hcard : Nat.card ↥A = 2 := by simpa using hC.card_A hF
  have hfin : Finite ↥A := hF.finite_subgroup A
  have hdvd : Nat.card ↥B ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hBA.le
  have hne : Nat.card ↥B ≠ 1 := fun h1 =>
    (bot_lt_iff_ne_bot.mp hB1) (Subgroup.eq_bot_of_card_eq _ h1)
  have h2 : Nat.card ↥B = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  exact hBA.ne (Subgroup.eq_of_le_of_card_ge hBA.le (by rw [hcard, h2]))

theorem binary_plane_wreath_offenders
    (hF : PlaneFamily I) {A : Subgroup (MulAut W)}
    (hAp : ∀ a ∈ A, ∀ i, ∃ j, a • I i = I j) (hA : CFSG.Quasithin.IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card W ∧
    (A ≠ ⊥ →
      (Nat.card ↥A * Nat.card ↥(fixV A) = Nat.card W ↔
        ∃ (J : Finset ι) (t : ∀ i, MulAut ↥(I i)), J.Nonempty ∧ IsCoordProduct I A J t)) ∧
    (∀ (J : Finset ι) (t : ∀ i, MulAut ↥(I i)), IsCoordProduct I A J t →
      Nat.card ↥A = 2 ^ J.card ∧ Nat.card ↥(fixV A) = 2 ^ (2 * Fintype.card ι - J.card)) ∧
    (A ≠ ⊥ →
      (Nat.card W ≤ Nat.card ↥A * Nat.card ↥(fixV A) ↔
        ∃ (J : Finset ι) (t : ∀ i, MulAut ↥(I i)), J.Nonempty ∧ IsCoordProduct I A J t)) ∧
    (A ≠ ⊥ →
      ((Nat.card W ≤ Nat.card ↥A * Nat.card ↥(fixV A) ∧
        ∀ B : Subgroup (MulAut W), ⊥ < B → B < A →
          Nat.card ↥B * Nat.card ↥(fixV B) < Nat.card ↥A * Nat.card ↥(fixV A)) ↔
        ∃ (i : ι) (t : ∀ i, MulAut ↥(I i)), IsCoordProduct I A {i} t)) := by
  have h : ElemAbelianData hF A :=
    ⟨fun a ha => (mem_permuting_iff hF).mpr (hAp a ha), hA.1, hA.2⟩
  have hW : Nat.card W = 4 ^ Fintype.card ι := hF.card_W
  have hle : Nat.card ↥A * Nat.card ↥(fixV A) ≤ 4 ^ Fintype.card ι := weight_le h
  have part2 : A ≠ ⊥ → (Nat.card ↥A * Nat.card ↥(fixV A) = 4 ^ Fintype.card ι ↔
      ∃ (J : Finset ι) (t : ∀ i, MulAut ↥(I i)), J.Nonempty ∧ IsCoordProduct I A J t) := by
    intro hne
    constructor
    · intro hw
      obtain ⟨J, t, hC, hJ⟩ := isCoordProduct_of_weight_eq h hw
      exact ⟨J, t, hJ hne, hC⟩
    · rintro ⟨J, t, -, hC⟩
      exact hC.weight_eq hF
  refine ⟨by rw [hW]; exact hle, ?_, ?_, ?_, ?_⟩
  · intro hne
    rw [hW]
    exact part2 hne
  · intro J t hC
    exact ⟨hC.card_A hF, hC.card_fixV hF⟩
  · intro hne
    rw [hW]
    constructor
    · intro hge
      exact (part2 hne).mp (le_antisymm hle hge)
    · intro hex
      exact ((part2 hne).mpr hex).ge
  · intro hne
    constructor
    · rintro ⟨hge, hstrict⟩
      rw [hW] at hge
      obtain ⟨J, t, hJ, hC⟩ := (part2 hne).mp (le_antisymm hle hge)
      have hcard1 : J.card ≤ 1 := hC.card_J_le_one_of_strict hF hstrict
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (le_antisymm hcard1 (Finset.card_pos.mpr hJ))
      subst hi
      exact ⟨i, t, hC⟩
    · rintro ⟨i, t, hC⟩
      exact ⟨by rw [hW, hC.weight_eq hF],
        fun B hB1 hBA => (hC.no_proper_of_single hF B hB1 hBA).elim⟩

end BaseCase

end CFSG.QuasithinUnique.Setup.Wreath
