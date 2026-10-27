module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Root

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem bar_mat_ZPsub {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    h.bar (mat z ιe₁ ιf₁) = mat z ιe₁ ιf₁ := by
  obtain ⟨hzU, e1, -, e3, -, -, -, e7, -, -⟩ := mem_ZPsub.1 hz
  obtain ⟨-, -, -, -, -, r6⟩ := U_rel hzU
  rw [e1, e3, e7] at r6
  exact bar_eq_of_add_eq_zero h (by simpa using r6)

theorem eq_of_mat_ZPsub {z z' : hypSU h 2 1} (hz : z ∈ ZPsub h) (hz' : z' ∈ ZPsub h)
    (e : mat z ιe₁ ιf₁ = mat z' ιe₁ ιf₁) : z = z' :=
  mat_injective (by rw [mat_eq_of_mem_ZPsub hz, mat_eq_of_mem_ZPsub hz', e])

theorem mat_mul_ZPsub {z z' : hypSU h 2 1} (hz : z ∈ ZPsub h) (hz' : z' ∈ ZPsub h) :
    mat (z * z') ιe₁ ιf₁ = mat z ιe₁ ιf₁ + mat z' ιe₁ ιf₁ := by
  rw [mat_mul, mat_eq_of_mem_ZPsub hz, mat_eq_of_mem_ZPsub hz', Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm ιe₁_ne_ιf₁)]
  simp [Matrix.one_apply_ne ιe₁_ne_ιf₁, add_comm]

@[expose] noncomputable def zRoot (h : UnitaryFieldData 2 f K) (c : h.fixedField) :
    hypSU h 2 1 :=
  (exists_rootZP h (h.mem_fixedField.1 c.2)).choose

theorem zRoot_mem (c : h.fixedField) : zRoot h c ∈ ZPsub h :=
  (exists_rootZP h (h.mem_fixedField.1 c.2)).choose_spec.1

theorem mat_zRoot (c : h.fixedField) : mat (zRoot h c) ιe₁ ιf₁ = c :=
  (exists_rootZP h (h.mem_fixedField.1 c.2)).choose_spec.2

theorem eq_zRoot {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    z = zRoot h ⟨mat z ιe₁ ιf₁, h.mem_fixedField.2 (bar_mat_ZPsub hz)⟩ :=
  eq_of_mat_ZPsub hz (zRoot_mem _) (by rw [mat_zRoot])

theorem zRoot_eq_of_coe_eq {z : hypSU h 2 1} (hz : z ∈ ZPsub h) {c : h.fixedField}
    (e : mat z ιe₁ ιf₁ = c) : z = zRoot h c :=
  eq_of_mat_ZPsub hz (zRoot_mem _) (by rw [mat_zRoot, e])

theorem zRoot_add (c c' : h.fixedField) : zRoot h (c + c') = zRoot h c * zRoot h c' :=
  (zRoot_eq_of_coe_eq (mul_mem (zRoot_mem c) (zRoot_mem c'))
    (by rw [mat_mul_ZPsub (zRoot_mem c) (zRoot_mem c'), mat_zRoot, mat_zRoot,
      Subfield.coe_add])).symm

theorem zRoot_zero : zRoot h 0 = 1 :=
  (zRoot_eq_of_coe_eq (one_mem _) (by rw [mat_one, Matrix.one_apply_ne ιe₁_ne_ιf₁,
    ZeroMemClass.coe_zero])).symm

theorem zRoot_injective : Function.Injective (zRoot h) := fun c c' e =>
  Subtype.ext (by rw [← mat_zRoot c, ← mat_zRoot c', e])

end Root

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
  (d : Data G h)

theorem η_zRoot_mem (c : h.fixedField) : d.η (zRoot h c) ∈ d.Zp := ⟨_, zRoot_mem c, rfl⟩

@[expose] noncomputable def ιZp : Multiplicative h.fixedField ≃* d.Zp :=
  MulEquiv.ofBijective
    ({ toFun := fun c => ⟨d.η (zRoot h (Multiplicative.toAdd c)), d.η_zRoot_mem _⟩
       map_one' := Subtype.ext (by simp [zRoot_zero])
       map_mul' := fun c c' => Subtype.ext (by simp [zRoot_add]) } :
      Multiplicative h.fixedField →* d.Zp)
    ⟨fun c c' e => by
      have e' : d.η (zRoot h (Multiplicative.toAdd c)) = d.η (zRoot h (Multiplicative.toAdd c')) :=
        congrArg (fun y : d.Zp => (y : G)) e
      have := zRoot_injective (d.η_injOn (ZPsub_le_U (zRoot_mem _)) (ZPsub_le_U (zRoot_mem _)) e')
      simpa using this, by
      rintro ⟨x, z, hz, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨mat z ιe₁ ιf₁, h.mem_fixedField.2 (bar_mat_ZPsub hz)⟩,
        Subtype.ext ?_⟩
      change d.η (zRoot h ⟨mat z ιe₁ ιf₁, _⟩) = d.η z
      rw [← eq_zRoot hz]⟩

theorem coe_ιZp (c : h.fixedField) : (d.ιZp (Multiplicative.ofAdd c) : G) = d.η (zRoot h c) :=
  rfl

theorem conj_ιZp_torus {j : hypSU h 2 1} (hj : j ∈ hypTorus h 2 1) {b : h.fixedField}
    (h1 : mat j ιe₁ ιe₁ = b) (h4 : mat j ιf₁ ιf₁ = (b : K)⁻¹) (x : h.fixedField) :
    d.η j * (d.ιZp (Multiplicative.ofAdd x) : G) * (d.η j)⁻¹ =
      d.ιZp (Multiplicative.ofAdd (b * b * x)) := by
  obtain ⟨hm, he⟩ := jSU_conj_ZPsub hj h1 h4 (zRoot_mem x)
  rw [coe_ιZp, coe_ιZp, ← map_inv, ← map_mul, ← map_mul,
    zRoot_eq_of_coe_eq hm (c := b * b * x) (by rw [he, mat_zRoot]; push_cast; ring)]

theorem act_zRoot {x : Gam h} (hZ : ∀ z ∈ ZPsub h, actΓ h x z ∈ ZPsub h) {l : h.fixedField}
    (hl : ∀ z ∈ ZPsub h, mat (actΓ h x z) ιe₁ ιf₁ = l * mat z ιe₁ ιf₁) (c : h.fixedField) :
    actΓ h x (zRoot h c) = zRoot h (l * c) :=
  zRoot_eq_of_coe_eq (hZ _ (zRoot_mem c)) (by rw [hl _ (zRoot_mem c), mat_zRoot]; push_cast; rfl)

end Data

namespace Data

open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo oTwo_le le_normalizer_oTwo isPGroup_oTwo)

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem finite_fixedField (h : UnitaryFieldData 2 f K) : Finite h.fixedField :=
  Nat.finite_of_card_ne_zero (by rw [h.card_fixedField]; positivity)

omit [Finite G] in
theorem charP_fixedField (h : UnitaryFieldData 2 f K) : CharP h.fixedField 2 :=
  finite_field_prime_power_characteristic Nat.prime_two h.one_le h.card_fixedField

theorem Hyp.I_le (hd : d.Hyp) :
    d.I ≤ centralizer ({d.t} : Set G) ⊓ normalizer (d.tP : Set G) := by
  intro i hi
  have hit : i ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.pull_le_L _ hi)
  have hiP := d.I_le_normalizer_P hi
  refine ⟨hit, mem_normalizer_of_conj_le fun y hy => ?_⟩
  obtain ⟨p, hp, hyp | hyp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hy <;> subst y
  · exact mem_sup_right ((mem_normalizer_iff.1 hiP p).1 hp)
  · have hct : i * d.t * i⁻¹ = d.t := by
      rw [mem_centralizer_singleton_iff.1 hit, mul_inv_cancel_right]
    have e : i * (d.t * p) * i⁻¹ = (i * d.t * i⁻¹) * (i * p * i⁻¹) := by group
    rw [e, hct]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ((mem_normalizer_iff.1 hiP p).1 hp))

theorem Hyp.exists_scalar_of_trivial (hd : d.Hyp) {e : G}
    (he : e ∈ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G))
    (hK : ∀ k ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G), e * k * e⁻¹ * k⁻¹ ∈ d.B₂) :
    ∃ a : h.fixedField, a ≠ 0 ∧ ∀ x : h.fixedField,
      e * (d.ιZp (Multiplicative.ofAdd x) : G) * e⁻¹ = d.ιZp (Multiplicative.ofAdd (a * x)) := by
  have hxL := hd.centralizer_le_normalizer he.2
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨e, hxL⟩)
  obtain ⟨hcol, hrow⟩ := hd.lift_flag he.1 hxL hy
  have hN : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 →
      ∃ v ∈ A₂sub h, actΓ h y n = v * n := by
    intro n hn hnU
    have hηn := hd.mem_K₀_of_mem_L (d.η_mem n) fun z hz => by
      obtain ⟨z', hz', rfl⟩ := hz
      rw [← map_mul, ← map_mul, N₂sub_comm_ZPsub hn hz']
    have hwB := hK _ hηn
    have hwL : e * d.η n * e⁻¹ * (d.η n)⁻¹ ∈ d.L :=
      mul_mem ((mem_normalizer_iff.1 hxL _).1 (d.η_mem n)) (inv_mem (d.η_mem n))
    obtain ⟨a, ha, hwa | hwa⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hwB
    · obtain ⟨v, hv, hva⟩ := ha
      refine ⟨v, hv, ?_⟩
      have e1 : d.η (actΓ h y n) = d.η (v * n) := by
        rw [← d.conj_η_eq hxL hy, map_mul, hva, ← hwa]
        group
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_U hnU
      obtain ⟨k', hk'⟩ := exists_pow_eq_one_of_mem_U (mul_mem (A₂sub_le_U hv) hnU)
      refine hd.eq_of_η_eq_of_two e1 (k := k + k') ?_ ?_
      · rw [← act_pow, pow_add, pow_mul, hk, one_pow, CFSG.RankThree.PartOne.U5K.Hyp.act_one]
      · rw [pow_add, mul_comm, pow_mul, hk', one_pow]
    · exfalso
      have : d.t ∈ d.L := by
        have := mul_mem hwL (inv_mem (d.A₂_le_L ha))
        rwa [hwa, mul_inv_cancel_right] at this
      exact hd.t_not_mem_L this
  have hZ : ∀ z ∈ ZPsub h, actΓ h y z ∈ ZPsub h := fun z hz => hd.act_mem_ZPsub he.1 hxL hy hz
  obtain ⟨l, hl0, hlb, hl⟩ := exists_scalar_act_ZPsub (right_eq_one_of_act_N₂ hcol hrow hN) hZ
  refine ⟨⟨l, h.mem_fixedField.2 hlb⟩, fun e0 => hl0 (congrArg Subtype.val e0), fun x => ?_⟩
  rw [coe_ιZp, coe_ιZp, d.conj_η_eq hxL hy, act_zRoot hZ (l := ⟨l, h.mem_fixedField.2 hlb⟩) hl x]

theorem Hyp.exists_trivial_of_scalar (hd : d.Hyp) {a : h.fixedField} (ha : a ≠ 0) :
    ∃ e ∈ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G),
      (∀ k ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
        centralizer ({d.t} : Set G), e * k * e⁻¹ * k⁻¹ ∈ d.B₂) ∧
      ∀ x : h.fixedField,
        e * (d.ιZp (Multiplicative.ofAdd x) : G) * e⁻¹ = d.ιZp (Multiplicative.ofAdd (a * x)) := by
  have := finite_fixedField h
  have := charP_fixedField h
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2) a
  have hb0 : (b : K) ≠ 0 := fun e0 => ha (by rw [hb, show b = 0 from Subtype.ext e0, mul_zero])
  obtain ⟨j, hj, h1, h2, h3, h4, h5⟩ := exists_jSU h hb0 (h.mem_fixedField.1 b.2)
  obtain ⟨hjt, hjN⟩ := hd.I_le ⟨j, hj, rfl⟩
  refine ⟨d.η j, ⟨d.normalizer_tP_le_normalizer_ZtP hjN, hjt⟩, fun k hk => ?_, fun x => ?_⟩
  · have hkL := hd.centralizer_le_normalizer hk.2
    obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨k, hkL⟩)
    have hfix : ∀ z ∈ ZPsub h, actΓ h y z = z := by
      intro z hz
      have e1 : d.η (actΓ h y z) = d.η z := by
        rw [← d.conj_η_eq hkL hy, ← mem_centralizer_iff.1 hk.1.2 (d.η z) ⟨z, hz, rfl⟩,
          mul_inv_cancel_right]
      refine eq_of_innM_eq_of_sq hd.center_hypPSU (d.innM_eq_of_η_eq e1) ?_
        (Vsub_sq (ZPsub_le_Vsub hz))
      rw [← CFSG.RankThree.PartOne.U5K.Hyp.act_mul, Vsub_sq (ZPsub_le_Vsub hz),
        CFSG.RankThree.PartOne.U5K.Hyp.act_one]
    have hcol := lmat_col_e₁ (x := y) (by rw [hfix _ z₁SU_mem_ZPsub]; exact z₁SU_mem_ZPsub)
    have hσ : (mat j).map y.1.right = mat j := by
      rw [torus_mat hj, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext c
      apply right_apply_eq_of_centralizes hfix
      rcases c with i | c | i <;> (try fin_cases i) <;> (try fin_cases c)
      · show h.bar (mat j ιe₁ ιe₁) = mat j ιe₁ ιe₁
        rw [h1, h.mem_fixedField.1 b.2]
      · show h.bar (mat j ιe₂ ιe₂) = mat j ιe₂ ιe₂
        rw [h2, map_one]
      · show h.bar (mat j ιz ιz) = mat j ιz ιz
        rw [h3, map_one]
      · show h.bar (mat j ιf₁ ιf₁) = mat j ιf₁ ιf₁
        rw [h4, map_inv₀, h.mem_fixedField.1 b.2]
      · show h.bar (mat j ιf₂ ιf₂) = mat j ιf₂ ιf₂
        rw [h5, map_one]
    have hA := act_mul_inv_mem_A₂sub hcol (lmat_row_f₁ hcol) hj ⟨h2, h3, h5⟩ hσ
    have e2 : k * d.η j * k⁻¹ * (d.η j)⁻¹ ∈ d.B₂ := by
      rw [d.conj_η_eq hkL hy, ← map_inv, ← map_mul]
      exact mem_sup_right ⟨_, hA, rfl⟩
    have e3 : d.η j * k * (d.η j)⁻¹ * k⁻¹ = (k * d.η j * k⁻¹ * (d.η j)⁻¹)⁻¹ := by group
    rw [e3]
    exact inv_mem e2
  · rw [d.conj_ιZp_torus hj h1 h4, hb]

theorem B₄_eq_oTwo (d : Data G h) : d.B₄ = oTwo (normalizer (d.ZtP : Set G)) :=
  pCore_map_eq_oTwo _

theorem Hyp.two_core_B₄ (hd : d.Hyp) :
    d.B₄ ≤ centralizer (d.Zp : Set G) ∧
      (∀ x ∈ d.B₄, ∀ k ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
        centralizer ({d.t} : Set G), x * k * x⁻¹ * k⁻¹ ∈ d.B₂) ∧
      d.B₄ ⊓ centralizer ({d.t} : Set G) = d.B₂ ∧
      (∀ y ∈ d.Zp, ∃ x ∈ d.B₄, x⁻¹ * d.t * x = d.t * y) ∧
      ∀ g ∈ normalizer (d.ZtP : Set G), ∃ c ∈ normalizer (d.ZtP : Set G) ⊓
        centralizer ({d.t} : Set G), ∃ x ∈ d.B₄, g = c * x := by
  have := finite_fixedField h
  have := charP_fixedField h
  have hc := hd.cosetData
  set H := normalizer (d.ZtP : Set G) with hH
  have hBn' : ∀ g ∈ H, ∀ b ∈ d.B₂, g * b * g⁻¹ ∈ d.B₂ := fun g hg b hb =>
    (mem_normalizer_iff.mp (hd.normalizer_ZtP_le_normalizer_B₂ hg) b).mp hb
  have hK : ∀ g ∈ H, ∀ k ∈ H ⊓ centralizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G),
      g * k * g⁻¹ ∈ H ⊓ centralizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun g hg k hk => hc.conj_mem_kernel hg hk
  set E := centralizerMod H (H ⊓ centralizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G)) d.B₂
    hK hBn' with hE
  have hEH : E ≤ H := fun e he => he.1
  have hEn : H ≤ normalizer (E : Set G) := fun g hg => by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_centralizerMod hg, fun hx => ?_⟩
    have := conj_mem_centralizerMod (H.inv_mem hg) hx
    simpa [mul_assoc] using this
  have hK2 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have := hd.four_le
    omega
  have htr : ∀ y ∈ d.Zp, ∃ g ∈ H, g⁻¹ * d.t * g = d.t * y := fun y hy => by
    obtain ⟨g, hg, e⟩ := hd.transitive_tP y hy
    exact ⟨g, d.normalizer_tP_le_normalizer_ZtP hg, e⟩
  have htrE := hc.exists_conj_eq_mul_of_frobenius hK2 d.ιZp htr hEH hEn
    (fun e he => hd.exists_scalar_of_trivial ⟨he.1.1, he.2⟩ he.1.2)
    (fun a ha => by
      obtain ⟨e, he, heK, hex⟩ := hd.exists_trivial_of_scalar ha
      exact ⟨e, ⟨⟨he.1, heK⟩, he.2⟩, hex⟩)
  rw [B₄_eq_oTwo]
  exact hc.two_core hd.isPGroup_B₂ hd.B₂_le_K₀ hd.normalizer_ZtP_le_normalizer_B₂
    (fun R hR hRn hR2 => hd.le_B₂_of_normal' hR hRn hR2) fun y hy => by
      obtain ⟨e, he, het⟩ := htrE y hy
      exact ⟨e, ⟨he.1.1, he.2⟩, he.1.2, het⟩

theorem B₄_le (d : Data G h) : d.B₄ ≤ normalizer (d.ZtP : Set G) := by
  rw [B₄_eq_oTwo]
  exact oTwo_le _

theorem le_normalizer_B₄ (d : Data G h) :
    normalizer (d.ZtP : Set G) ≤ normalizer (d.B₄ : Set G) := by
  rw [B₄_eq_oTwo]
  exact le_normalizer_oTwo _

theorem Hyp.t_mem_K₀ (hd : d.Hyp) :
    d.t ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) :=
  ⟨⟨d.tP_le_normalizer_ZtP (mem_sup_left (mem_zpowers _)),
    mem_centralizer_iff.2 fun _ hz => hd.comm_t (d.Zp_le_L hz)⟩,
    mem_centralizer_singleton_iff.2 rfl⟩

theorem Hyp.tP_le_K₀ (hd : d.Hyp) :
    d.tP ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) :=
  sup_le (zpowers_le.2 hd.t_mem_K₀) hd.P_le_K₀

omit [Finite G] in
theorem mem_centralizer_zpowers {c t : G} (hc : c ∈ centralizer ({t} : Set G)) :
    c ∈ centralizer (zpowers t : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 hc).symm k).eq

theorem Hyp.normalizer_Zp_inf (hd : d.Hyp) :
    normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) =
      normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G) := by
  refine le_antisymm (fun c hc => ⟨?_, hc.2⟩) (inf_le_inf_right _ hd.normalizer_ZtP_le)
  rw [hd.ZtP_eq]
  exact mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hc.2))
    hc.1

theorem Hyp.tP_inf_L (hd : d.Hyp) : d.tP ⊓ d.L = d.P := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right d.P_le_L)
  obtain ⟨hx, hxL⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨p, hp, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hx
  · exact hp
  · exfalso
    have := mul_mem hxL (inv_mem (d.P_le_L hp))
    rw [mul_inv_cancel_right] at this
    exact hd.t_not_mem_L this

theorem Hyp.normalizer_tP_inf (hd : d.Hyp) :
    normalizer (d.tP : Set G) ⊓ centralizer ({d.t} : Set G) =
      normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G) := by
  have h1 : normalizer (d.tP : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G) := by
    intro c hc
    refine ⟨?_, hc.2⟩
    rw [← hd.tP_inf_L]
    exact mem_normalizer_inf hc.1 (hd.centralizer_le_normalizer hc.2)
  have h2 : normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer (d.tP : Set G) ⊓ centralizer ({d.t} : Set G) := fun c hc =>
    ⟨mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hc.2))
      hc.1, hc.2⟩
  exact le_antisymm h1 h2

theorem Hyp.B₄_le_normalizer_tP (hd : d.Hyp) : d.B₄ ≤ normalizer (d.tP : Set G) := by
  obtain ⟨-, hK, -, -, -⟩ := hd.two_core_B₄
  intro m hm
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have e : m * x * m⁻¹ = (m * x * m⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact mul_mem (hd.B₂_spec.2.1 (hK m hm x (hd.tP_le_K₀ hx))) hx

theorem Hyp.exists_crossedHom_B₄ (hd : d.Hyp) :
    ∃ φ : d.B₄ →* d.Zp, Function.Surjective φ ∧ φ.ker = d.B₂.subgroupOf d.B₄ ∧
      (∀ x : d.B₄, (φ x : G) = (x : G)⁻¹ * d.t * x * d.t) ∧
      ∀ c ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G), ∀ x : d.B₄,
        ∃ hx : c * x * c⁻¹ ∈ d.B₄, (φ ⟨c * x * c⁻¹, hx⟩ : G) = c * φ x * c⁻¹ := by
  obtain ⟨hZ, -, hB₂, htr, -⟩ := hd.two_core_B₄
  have hc := hd.cosetData
  set φ := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossedHom hd.t_mul_t d.Zp d.B₄ hZ
    fun y hy => hc.crossed_mem y (d.B₄_le hy) with hφ
  refine ⟨φ, ?_, ?_, fun x => rfl, fun c hc' x => ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxt⟩ := htr y hy
    exact ⟨⟨x, hx⟩, Subtype.ext ((hc.crossed_eq_iff hy).2 hxt)⟩
  · ext x
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_ker_crossedHom, mem_subgroupOf, ← hB₂, mem_inf,
      mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨x.2, e⟩, fun e => e.2⟩
  · have hcN : c ∈ normalizer (d.ZtP : Set G) := (hd.normalizer_Zp_inf ▸ hc').1
    refine ⟨(mem_normalizer_iff.1 (d.le_normalizer_B₄ hcN) x).1 x.2, ?_⟩
    exact CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 hc'.2)

theorem Hyp.card_B₄ (hd : d.Hyp) : Nat.card d.B₄ = 2 * (2 ^ f) ^ 8 := by
  obtain ⟨hZ, -, hB₂, -, -⟩ := hd.two_core_B₄
  obtain ⟨φ, hsurj, hker, -, -⟩ := hd.exists_crossedHom_B₄
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaD.card_eq_card_ker_mul_card_range φ
  rw [hker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, d.card_Zp,
    Nat.card_congr (subgroupOfEquivOfLe (hB₂.symm ▸ inf_le_left : d.B₂ ≤ d.B₄)).toEquiv,
    hd.card_B₂] at h1
  rw [h1]
  ring

theorem Hyp.sec3_2 (hd : d.Hyp) :
    normalizer (d.ZtP : Set G) =
        d.B₄ ⊔ (normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G)) ∧
      (∀ g ∈ normalizer (d.ZtP : Set G), ∃ x ∈ d.B₄,
        ∃ c ∈ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c) ∧
      d.B₂ ≤ d.B₄ ∧ d.B₄ ⊓ centralizer ({d.t} : Set G) = d.B₂ ∧
      Nat.card d.B₄ = 2 * (2 ^ f) ^ 8 ∧
      (∃ φ : d.B₄ →* d.Zp, Function.Surjective φ ∧ φ.ker = d.B₂.subgroupOf d.B₄ ∧
        (∀ x : d.B₄, (φ x : G) = (x : G)⁻¹ * d.t * x * d.t) ∧
        ∀ c ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G), ∀ x : d.B₄,
          ∃ hx : c * x * c⁻¹ ∈ d.B₄, (φ ⟨c * x * c⁻¹, hx⟩ : G) = c * φ x * c⁻¹) ∧
      normalizer (d.tP : Set G) =
        d.B₄ ⊔ (normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G)) ∧
      ∀ g ∈ normalizer (d.tP : Set G), ∃ x ∈ d.B₄,
        ∃ c ∈ normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c := by
  obtain ⟨-, -, hB₂, -, hfac⟩ := hd.two_core_B₄
  have hB₂B₄ : d.B₂ ≤ d.B₄ := hB₂.symm ▸ inf_le_left
  have hfac' : ∀ g ∈ normalizer (d.ZtP : Set G), ∃ x ∈ d.B₄,
      ∃ c ∈ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c := by
    intro g hg
    obtain ⟨c, hc, x, hx, rfl⟩ := hfac g hg
    exact ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (d.le_normalizer_B₄ hc.1) x).1 hx, c, hc, by group⟩
  have hfacP : ∀ g ∈ normalizer (d.tP : Set G), ∃ x ∈ d.B₄,
      ∃ c ∈ normalizer (d.P : Set G) ⊓ centralizer ({d.t} : Set G), g = x * c := by
    intro g hg
    obtain ⟨x, hx, c, hc, rfl⟩ := hfac' g (d.normalizer_tP_le_normalizer_ZtP hg)
    have hcN : c ∈ normalizer (d.tP : Set G) := by
      have := mul_mem (inv_mem (hd.B₄_le_normalizer_tP hx)) hg
      rwa [inv_mul_cancel_left] at this
    exact ⟨x, hx, c, hd.normalizer_tP_inf ▸ ⟨hcN, hc.2⟩, rfl⟩
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le d.B₄_le inf_le_left), hfac', hB₂B₄, hB₂,
    hd.card_B₄, hd.exists_crossedHom_B₄, le_antisymm (fun g hg => ?_)
      (sup_le hd.B₄_le_normalizer_tP (hd.normalizer_tP_inf ▸ inf_le_left)), hfacP⟩
  · obtain ⟨x, hx, c, hc, rfl⟩ := hfac' g hg
    exact mul_mem (mem_sup_left hx) (mem_sup_right hc)
  · obtain ⟨x, hx, c, hc, rfl⟩ := hfacP g hg
    exact mul_mem (mem_sup_left hx) (mem_sup_right hc)

omit [Finite G] in
theorem mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ centralizer (A : Set G))
    (hB : x ∈ centralizer (B : Set G)) : x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ centralizer ({x} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hA a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hB b hb))
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hle hy)

theorem Hyp.exists_mem_Zp_ne_one (hd : d.Hyp) : ∃ y ∈ d.Zp, y ≠ 1 := by
  have hZ1 : d.Zp ≠ ⊥ := fun e => by
    have := d.card_Zp
    rw [e, Subgroup.card_bot] at this
    have h4 := hd.four_le
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ1
  exact ⟨y, hy, fun e => hy1 (Subtype.ext e)⟩

theorem Hyp.centerIn_B₄ (hd : d.Hyp) : CFSG.centerIn d.B₄ = d.Zp := by
  obtain ⟨hZ, -, hB₂, htr, -⟩ := hd.two_core_B₄
  have hB₂B₄ : d.B₂ ≤ d.B₄ := hB₂.symm ▸ inf_le_left
  have hZB₂ : d.Zp ≤ d.B₂ :=
    (le_sup_right : d.Zp ≤ zpowers d.t ⊔ d.Zp).trans (hd.ZtP_eq ▸ hd.B₂_spec.1)
  have htB₄ : d.t ∈ d.B₄ := hB₂B₄ (mem_sup_left (mem_zpowers _))
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  have hcen : ∀ {u a : G}, u ∈ zpowers d.t → a ∈ d.A₂ →
      u * a ∈ centralizer (d.B₄ : Set G) → a ∈ d.Zp := by
    intro u a hu ha hua
    rw [← hZA]
    refine ⟨ha, mem_centralizer_iff.2 fun y hy => ?_⟩
    have h1 := mem_centralizer_iff.1 hua y (hB₂B₄ (mem_sup_right hy))
    have h2 : y * u = u * y := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
      exact (Commute.zpow_right (hd.comm_t (d.A₂_le_L hy)) k).eq
    have : u * (y * a) = u * (a * y) := by
      calc u * (y * a) = (u * y) * a := by group
        _ = (y * u) * a := by rw [h2]
        _ = y * (u * a) := by group
        _ = u * a * y := h1
        _ = u * (a * y) := by group
    exact mul_left_cancel this
  refine le_antisymm (fun z hz => ?_) fun z hz =>
    ⟨hB₂B₄ (hZB₂ hz), mem_centralizer_iff.2 fun x hx => (mem_centralizer_iff.1 (hZ hx) z hz).symm⟩
  obtain ⟨hzB, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzt : z ∈ centralizer ({d.t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzc d.t htB₄).symm
  obtain ⟨a, ha, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L
    (hB₂ ▸ Subgroup.mem_inf.2 ⟨hzB, hzt⟩ : z ∈ d.B₂)
  · exact hcen (one_mem _) ha (by rwa [one_mul])
  · exfalso
    have haZ := hcen (mem_zpowers _) ha hzc
    have htc : d.t ∈ centralizer (d.B₄ : Set G) := by
      have := mul_mem hzc (inv_mem (mem_centralizer_iff.2 fun x hx =>
        (mem_centralizer_iff.1 (hZ hx) a haZ).symm))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨y, hy, hy1⟩ := hd.exists_mem_Zp_ne_one
    obtain ⟨x, hx, hxt⟩ := htr y hy
    have e : x⁻¹ * d.t * x = d.t := by
      rw [mul_assoc, ← mem_centralizer_iff.1 htc x hx, inv_mul_cancel_left]
    rw [e] at hxt
    exact hy1 (by simpa using hxt)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
