module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBUFourUnitaryAxisFlagMaps
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate
public import CFSG.Monster.B.Short.Extraspecial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace FourUnitary

namespace AxisFlag

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups Subgroup

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

variable (B) in
@[expose] def flagU (e f : W) (g : LinearMap.GeneralLinearGroup F W) : W :=
  ((g : W →ₗ[F] W) f - f) - B f ((g : W →ₗ[F] W) f - f) • e

theorem flagU_of_apply (hB : B.IsSymm) {e f : W} (hef : B e f = 1) {u : W}
    (hu : u ∈ partnerPerp B e f) {a : F} {g : LinearMap.GeneralLinearGroup F W}
    (hgf : (g : W →ₗ[F] W) f = f + u + a • e) : flagU B e f g = u := by
  have h1 : (g : W →ₗ[F] W) f - f = u + a • e := by rw [hgf]; abel
  rw [flagU, h1, map_add, map_smul, (mem_partnerPerp.1 hu).2, B_f_e hB hef, smul_eq_mul,
    mul_one, zero_add, add_sub_cancel_right]

theorem flagMap_apply_f (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {u : W} (hu : u ∈ partnerPerp B e f) (a : F) :
    flagMap B e u a f = f + u + a • e :=
  (flagMap_spec hB he hf hef hu a).2.2.1

theorem flagU_mem (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ axisKernel B e) :
    flagU B e f g ∈ partnerPerp B e f := by
  obtain ⟨u, hu, a, -, -, hgf⟩ := eq_flagMap_of_mem hB he hf hef hg
  rw [flagU_of_apply hB hef hu hgf]
  exact hu

theorem coe_mul_eq_flagMap (hB : B.IsSymm) {e : W} (he : B e e = 0)
    {g g' : LinearMap.GeneralLinearGroup F W} {u v : W} (heu : B e u = 0) (hev : B e v = 0)
    {a b : F} (hg : (g : W →ₗ[F] W) = flagMap B e u a)
    (hg' : (g' : W →ₗ[F] W) = flagMap B e v b) :
    ((g * g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) =
      flagMap B e (u + v) (a + b + B u v) := by
  have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
  rw [Units.val_mul, Module.End.mul_eq_comp, hg, hg', flagMap_comp he hue hev]

theorem flagU_mul (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {g g' : LinearMap.GeneralLinearGroup F W} (hg : g ∈ axisKernel B e)
    (hg' : g' ∈ axisKernel B e) : flagU B e f (g * g') = flagU B e f g + flagU B e f g' := by
  obtain ⟨u, hu, a, -, hgeq, hgf⟩ := eq_flagMap_of_mem hB he hf hef hg
  obtain ⟨v, hv, b, -, hg'eq, hg'f⟩ := eq_flagMap_of_mem hB he hf hef hg'
  have huv : u + v ∈ partnerPerp B e f := add_mem hu hv
  have hmul := coe_mul_eq_flagMap hB he (mem_partnerPerp.1 hu).1 (mem_partnerPerp.1 hv).1 hgeq
    hg'eq
  rw [flagU_of_apply hB hef huv (by rw [hmul, flagMap_apply_f hB he hf hef huv]),
    flagU_of_apply hB hef hu hgf, flagU_of_apply hB hef hv hg'f]

variable (B) in
@[expose] def flagHom (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) : axisKernel B e →* Multiplicative (partnerPerp B e f) where
  toFun g := Multiplicative.ofAdd ⟨flagU B e f g, flagU_mem hB he hf hef g.2⟩
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    apply Subtype.ext
    simp [flagU]
  map_mul' g g' := by
    rw [← ofAdd_add]
    congr 1
    exact Subtype.ext (flagU_mul hB he hf hef g.2 g'.2)

theorem mem_ker_flagHom (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {g : axisKernel B e} :
    g ∈ (flagHom B hB he hf hef).ker ↔ flagU B e f g = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one, Submodule.mk_eq_zero]

theorem flagHom_surjective (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) : Function.Surjective (flagHom B hB he hf hef) := by
  intro w
  obtain ⟨⟨u, hu⟩, rfl⟩ : ∃ x, Multiplicative.ofAdd x = w := ⟨Multiplicative.toAdd w, rfl⟩
  obtain ⟨a, ha⟩ := hF.traceLin_surjective ⟨B u u, hB.eq u u⟩
  have htr : hF.trace a = B u u := congrArg Subtype.val ha
  have heu := (mem_partnerPerp.1 hu).1
  refine ⟨⟨flagGL B hB he heu htr, flagGL_mem hB he heu htr⟩, ?_⟩
  change Multiplicative.ofAdd _ = _
  congr 1
  exact Subtype.ext (flagU_of_apply hB hef hu (by rw [coe_flagGL, flagMap_apply_f hB he hf hef hu]))

theorem trace_one : hF.trace 1 = 0 := by
  rw [trace_eq, map_one, one_add_one_eq_two, two_eq_zero hF]

variable (B) in
theorem trace_one_eq : hF.trace 1 = B 0 0 := by
  rw [trace_one, map_zero]

theorem coe_transvectionGL (e : W) (he : B e e = 0) :
    (hermTransvectionGL B he 1 : W →ₗ[F] W) = flagMap B e 0 1 := by
  rw [coe_hermTransvectionGL, flagMap_zero_one]

theorem transvectionGL_mem_axisKernel (hB : B.IsSymm) {e : W} (he : B e e = 0) :
    hermTransvectionGL B he 1 ∈ axisKernel B e := by
  have h : hermTransvectionGL B he 1 = flagGL B hB he (map_zero (B e)) (trace_one_eq B) :=
    Units.ext (coe_transvectionGL e he)
  rw [h]
  exact flagGL_mem hB he _ _

theorem eq_zero_or_one_of_trace (a : F) (ha : hF.trace a = 0) : a = 0 ∨ a = 1 := by
  rw [trace_eq, bar_eq_sq] at ha
  have h : a * (1 + a) = 0 := by linear_combination ha
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h - two_eq_zero hF)

theorem ker_flagHom (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) :
    (flagHom B hB he hf hef).ker = zpowers ⟨_, transvectionGL_mem_axisKernel hB he⟩ := by
  apply le_antisymm
  · intro g hg
    rw [mem_ker_flagHom] at hg
    obtain ⟨u, hu, a, htr, hgeq, hgf⟩ := eq_flagMap_of_mem hB he hf hef g.2
    rw [flagU_of_apply hB hef hu hgf] at hg
    subst hg
    rw [map_zero] at htr
    rcases eq_zero_or_one_of_trace a htr with rfl | rfl
    · have h1 : g = 1 := Subtype.ext (Units.ext (by rw [hgeq, flagMap_zero_zero]; rfl))
      rw [h1]
      exact one_mem _
    · have h1 : g = ⟨_, transvectionGL_mem_axisKernel hB he⟩ :=
        Subtype.ext (Units.ext (by rw [hgeq, coe_transvectionGL e he]))
      rw [h1]
      exact mem_zpowers _
  · rw [zpowers_le, mem_ker_flagHom]
    refine flagU_of_apply hB hef (zero_mem _) (a := 1) ?_
    change hermTransvection B e 1 f = f + 0 + (1 : F) • e
    rw [transvection_one_apply, hef, add_zero]

theorem orderOf_transvection_mk (hB : B.IsSymm) (hBl : B.SeparatingLeft) {e : W} (he0 : e ≠ 0)
    (he : B e e = 0) :
    orderOf (⟨_, transvectionGL_mem_axisKernel hB he⟩ : axisKernel B e) = 2 := by
  rw [Subgroup.orderOf_mk, orderOf_transvectionGL hBl he0 he]

theorem transvection_mem_center (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) :
    (⟨_, transvectionGL_mem_axisKernel hB he⟩ : axisKernel B e) ∈ center (axisKernel B e) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨u, hu, a, -, hgeq, -⟩ := eq_flagMap_of_mem hB he hf hef g.2
  have heu := (mem_partnerPerp.1 hu).1
  have hT := coe_transvectionGL e he
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul,
    coe_mul_eq_flagMap hB he heu (map_zero (B e)) hgeq hT,
    coe_mul_eq_flagMap hB he (map_zero (B e)) heu hT hgeq]
  simp only [add_zero, zero_add, map_zero, LinearMap.zero_apply]
  rw [add_comm a 1]

theorem center_le_ker [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {e f : W} (he0 : e ≠ 0) (he : B e e = 0) (hf : B f f = 0) (hef : B e f = 1) :
    center (axisKernel B e) ≤ (flagHom B hB he hf hef).ker := by
  intro g hg
  rw [mem_ker_flagHom]
  obtain ⟨u, hu, a, -, hgeq, hgf⟩ := eq_flagMap_of_mem hB he hf hef g.2
  rw [flagU_of_apply hB hef hu hgf]
  by_contra hu0
  obtain ⟨-, -, -, hD, -⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).2 f hef hf
  have hne : ∃ v ∈ partnerPerp B e f, B u v ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (congrArg Subtype.val (hD ⟨u, hu⟩ fun y => by
      rw [LinearMap.domRestrict₁₂_apply]
      exact h y y.2))
  obtain ⟨v₀, hv₀, hv₀'⟩ := hne
  obtain ⟨ω, hω⟩ := hF.exists_bar_ne
  have hv : (ω / B u v₀) • v₀ ∈ partnerPerp B e f := Submodule.smul_mem _ _ hv₀
  have huv : B u ((ω / B u v₀) • v₀) = ω := by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀']
  obtain ⟨b, hb⟩ := hF.traceLin_surjective
    ⟨B ((ω / B u v₀) • v₀) ((ω / B u v₀) • v₀), hB.eq _ _⟩
  have htrb : hF.trace b = B ((ω / B u v₀) • v₀) ((ω / B u v₀) • v₀) := congrArg Subtype.val hb
  have hev := (mem_partnerPerp.1 hv).1
  have heu := (mem_partnerPerp.1 hu).1
  have hcomm := mem_center_iff.1 hg ⟨flagGL B hB he hev htrb, flagGL_mem hB he hev htrb⟩
  have h1 := coe_mul_eq_flagMap hB he heu hev hgeq (coe_flagGL hB he hev htrb)
  have h2 := coe_mul_eq_flagMap hB he hev heu (coe_flagGL hB he hev htrb) hgeq
  have h4 : flagMap B e ((ω / B u v₀) • v₀ + u) (b + a + B ((ω / B u v₀) • v₀) u) f =
      flagMap B e (u + (ω / B u v₀) • v₀) (a + b + B u ((ω / B u v₀) • v₀)) f := by
    rw [← h1, ← h2]
    exact congrArg (fun φ : LinearMap.GeneralLinearGroup F W => (φ : W →ₗ[F] W) f)
      (congrArg Subtype.val hcomm)
  rw [flagMap_apply_f hB he hf hef (add_mem hv hu),
    flagMap_apply_f hB he hf hef (add_mem hu hv)] at h4
  have h5 := (decomp_unique hB hf hef (add_mem hv hu) (add_mem hu hv) h4).2
  rw [add_comm b a] at h5
  have h6 := add_left_cancel h5
  apply hω
  rw [← huv, hB.eq u, h6]

theorem center_eq_ker [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {e f : W} (he0 : e ≠ 0) (he : B e e = 0) (hf : B f f = 0) (hef : B e f = 1) :
    center (axisKernel B e) = (flagHom B hB he hf hef).ker := by
  refine le_antisymm (center_le_ker hB hBl he0 he hf hef) ?_
  rw [ker_flagHom hB he hf hef, zpowers_le]
  exact transvection_mem_center hB he hf hef

theorem natCard_partnerPerp [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {e f : W} (he0 : e ≠ 0) (he : B e e = 0) (hf : B f f = 0) (hef : B e f = 1) :
    Nat.card (partnerPerp B e f) = 2 ^ (2 * (finrank F W - 2)) := by
  obtain ⟨-, -, -, -, hfin⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).2 f hef hf
  have : Finite F := hF.finite
  rw [Module.natCard_eq_pow_finrank (K := F), hF.card, ← pow_mul]
  congr 2

theorem natCard_axisKernel [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : 2 ≤ finrank F W) {e f : W} (he0 : e ≠ 0) (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) : Nat.card (axisKernel B e) = 2 ^ (2 * finrank F W - 3) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (flagHom B hB he hf hef).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (flagHom_surjective hB he hf hef)).toEquiv, ker_flagHom hB he hf hef, Nat.card_zpowers,
    orderOf_transvection_mk hB hBl he0 he, Nat.card_congr Multiplicative.toAdd,
    natCard_partnerPerp hB hBl he0 he hf hef, ← pow_succ] at h1
  rw [h1]
  congr 1
  omega

theorem sq_mem_ker (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) (g : axisKernel B e) : g ^ 2 ∈ (flagHom B hB he hf hef).ker := by
  rw [MonoidHom.mem_ker, map_pow, pow_two]
  obtain ⟨w, hw⟩ : ∃ w, Multiplicative.ofAdd w = flagHom B hB he hf hef g := ⟨_, rfl⟩
  rw [← hw, ← ofAdd_add, add_self_vec hF, ofAdd_zero]

theorem isExtraspecial_axisKernel [FiniteDimensional F W] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hd : 3 ≤ finrank F W) {e f : W} (he0 : e ≠ 0) (he : B e e = 0)
    (hf : B f f = 0) (hef : B e f = 1) : IsExtraspecial 2 (axisKernel B e) := by
  have hZ : ∀ g : axisKernel B e, g ∈ center (axisKernel B e) ↔
      g ∈ (flagHom B hB he hf hef).ker := fun g => by
    rw [center_eq_ker hB hBl he0 he hf hef]
  refine ⟨?_, ?_, ?_⟩
  · rw [center_eq_ker hB hBl he0 he hf hef, ker_flagHom hB he hf hef, Nat.card_zpowers,
      orderOf_transvection_mk hB hBl he0 he]
  · have hcomm : IsMulCommutative (axisKernel B e ⧸ center (axisKernel B e)) := ⟨⟨fun x y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ,
        MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
        mul_comm (flagHom B hB he hf hef g') (flagHom B hB he hf hef g), inv_mul_cancel]⟩⟩
    exact { toIsMulCommutative := hcomm
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
              obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
              rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hZ]
              exact sq_mem_ker hB he hf hef g }
  ·
    obtain ⟨-, -, -, -, hfin⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).2 f hef hf
    obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F)
      (M := partnerPerp B e f)).1 (by
        change 0 < finrank F ((Submodule.span F {e, f}).orthogonalBilin B)
        omega)
    obtain ⟨g, hg⟩ := flagHom_surjective hB he hf hef (Multiplicative.ofAdd w)
    refine ⟨⟨QuotientGroup.mk g, 1, fun h => hw ?_⟩⟩
    rw [QuotientGroup.eq_one_iff, hZ, MonoidHom.mem_ker, hg, ofAdd_eq_one] at h
    exact h

theorem det_eq_one [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft) {e f : W}
    (he0 : e ≠ 0) (he : B e e = 0) (hf : B f f = 0) (hef : B e f = 1)
    {g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ axisKernel B e) :
    LinearMap.det (g : W →ₗ[F] W) = 1 := by
  have hsq := sq_mem_ker hB he hf hef ⟨g, hg⟩
  rw [ker_flagHom hB he hf hef] at hsq
  have hT2 := pow_orderOf_eq_one (⟨_, transvectionGL_mem_axisKernel hB he⟩ : axisKernel B e)
  rw [orderOf_transvection_mk hB hBl he0 he] at hT2
  have h4 : g ^ 4 = 1 := by
    have h := congrArg Subtype.val (show ((⟨g, hg⟩ : axisKernel B e) ^ 2) ^ 2 = 1 by
      rcases eq_one_or_eq_of_mem_zpowers (orderOf_transvection_mk hB hBl he0 he) hsq with
        h | h
      · rw [h, one_pow]
      · rw [h, hT2])
    rw [← pow_mul] at h
    exact h
  have hdet := congrArg (fun x : LinearMap.GeneralLinearGroup F W => LinearMap.det
    (x : W →ₗ[F] W)) h4
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at hdet
  have hne : LinearMap.det (g : W →ₗ[F] W) ≠ 0 := (g.isUnit.map LinearMap.det).ne_zero
  have h3 := pow_three_eq_one hF hne
  calc LinearMap.det (g : W →ₗ[F] W) = LinearMap.det (g : W →ₗ[F] W) ^ 3 *
        LinearMap.det (g : W →ₗ[F] W) := by rw [h3, one_mul]
    _ = LinearMap.det (g : W →ₗ[F] W) ^ 4 := by ring
    _ = 1 := hdet

theorem apply_normalized {e : W} {g : LinearMap.GeneralLinearGroup F W}
    (hg : g ∈ axisKernel B e) {y : W} (hy : B y y = 0) (hey : B e y = 1) :
    B ((g : W →ₗ[F] W) y) ((g : W →ₗ[F] W) y) = 0 ∧ B e ((g : W →ₗ[F] W) y) = 1 := by
  obtain ⟨hgU, hge, -⟩ := mem_axisKernel.1 hg
  refine ⟨by rw [mem_sesqUnitaryGroup.1 hgU, hy], ?_⟩
  conv_lhs => rw [← hge]
  rw [mem_sesqUnitaryGroup.1 hgU, hey]

theorem existsUnique_apply_f (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {y : W} (hy : B y y = 0) (hey : B e y = 1) :
    ∃! g : axisKernel B e, ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = y := by
  obtain ⟨u, hu, a, htr, rfl⟩ := exists_decomp hB he hf hef hy hey
  have heu := (mem_partnerPerp.1 hu).1
  refine ⟨⟨flagGL B hB he heu htr, flagGL_mem hB he heu htr⟩, flagMap_apply_f hB he hf hef hu a,
    fun g' hg' => ?_⟩
  obtain ⟨u', hu', a', -, hg'eq, hg'f⟩ := eq_flagMap_of_mem hB he hf hef g'.2
  have hg'' : ((g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = f + u + a • e := hg'
  rw [hg'f] at hg''
  obtain ⟨rfl, rfl⟩ := decomp_unique hB hf hef hu' hu hg''
  exact Subtype.ext (Units.ext hg'eq)

theorem existsUnique_line (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {y : W} (hy : B y y = 0) (hey : B e y ≠ 0) :
    ∃! g : axisKernel B e, (F ∙ ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) =
      F ∙ y := by
  have hc : (B e y)⁻¹ ≠ 0 := inv_ne_zero hey
  have hy' : B ((B e y)⁻¹ • y) ((B e y)⁻¹ • y) = 0 := by
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hy, mul_zero]
  have hey' : B e ((B e y)⁻¹ • y) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hey]
  obtain ⟨g, hg, hguniq⟩ := existsUnique_apply_f hB he hf hef hy' hey'
  refine ⟨g, ?_, fun g' hg' => hguniq g' ?_⟩
  · show (F ∙ ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) = F ∙ y
    rw [hg, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
  · have hg'' : (F ∙ ((g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) = F ∙ y := hg'
    show ((g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = (B e y)⁻¹ • y
    have hmem : ((g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f ∈ F ∙ y := by
      rw [← hg'']
      exact Submodule.mem_span_singleton_self _
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 := (apply_normalized g'.2 hf hef).2
    rw [← hd, map_smul, smul_eq_mul] at h1
    rw [← hd, eq_inv_of_mul_eq_one_left h1]

end AxisFlag

end FourUnitary

open FourUnitary FourUnitary.AxisFlag Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups Subgroup in
theorem four_element_unitary_axis_flag_kernel_and_regular_orbit {F : Type*} [Field F]
    (hF : UnitaryFieldData 2 1 F) {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hd : 3 ≤ finrank F W) {e : W} (he0 : e ≠ 0) (he : B e e = 0) :
    (∃ f : W, B f f = 0 ∧ B e f = 1) ∧
    ∃ hT : hermTransvectionGL B he 1 ∈ axisKernel B e,
      (hermTransvectionGL B he 1 : W →ₗ[F] W) = flagMap B e 0 1 ∧
      flagMap B e 0 0 = LinearMap.id ∧
      center (axisKernel B e) = zpowers ⟨_, hT⟩ ∧
      commutator (axisKernel B e) = zpowers ⟨_, hT⟩ ∧
      (∀ g : axisKernel B e, g ∈ center (axisKernel B e) ↔
        ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = flagMap B e 0 0 ∨
          ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = flagMap B e 0 1) ∧
      IsExtraspecialPGroup 2 (axisKernel B e) ∧
      Nat.card (axisKernel B e) = 2 ^ (2 * finrank F W - 3) ∧
      Nat.card (axisKernel B e) = 2 ^ (1 + 2 * (finrank F W - 2)) ∧
      axisKernel B e ≤ sesqSpecialUnitaryGroup B ∧
      ∀ f : W, B f f = 0 → B e f = 1 →
        IsCompl (Submodule.span F {e, f}) (partnerPerp B e f) ∧
        finrank F (partnerPerp B e f) = finrank F W - 2 ∧
        (∀ g : LinearMap.GeneralLinearGroup F W, g ∈ axisKernel B e ↔
          ∃ u ∈ partnerPerp B e f, ∃ a : F, hF.trace a = B u u ∧
            (g : W →ₗ[F] W) = flagMap B e u a) ∧
        (∀ u ∈ partnerPerp B e f, ∀ a : F, hF.trace a = B u u →
          ∃ g ∈ axisKernel B e, (g : W →ₗ[F] W) = flagMap B e u a) ∧
        (∀ u ∈ partnerPerp B e f, ∀ v ∈ partnerPerp B e f, ∀ a b : F,
          flagMap B e u a ∘ₗ flagMap B e v b = flagMap B e (u + v) (a + b + B u v)) ∧
        (∀ g ∈ axisKernel B e, ∀ y : W, B y y = 0 → B e y = 1 →
          B ((g : W →ₗ[F] W) y) ((g : W →ₗ[F] W) y) = 0 ∧ B e ((g : W →ₗ[F] W) y) = 1) ∧
        (∀ y : W, B y y = 0 → B e y = 1 →
          ∃! g : axisKernel B e, ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = y) ∧
        ∀ y : W, B y y = 0 → B e y ≠ 0 →
          ∃! g : axisKernel B e,
            (F ∙ ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) = F ∙ y := by
  obtain ⟨f₀, hef₀, hf₀⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).1
  have hT := transvectionGL_mem_axisKernel hB he
  have hext := isExtraspecial_axisKernel hB hBl hd he0 he hf₀ hef₀
  have : Finite F := hF.finite
  have : Finite W := Module.finite_of_finite F
  have : Finite (W →ₗ[F] W) := Finite.of_injective _ DFunLike.coe_injective
  have hext' : IsExtraspecialPGroup 2 (axisKernel B e) :=
    isExtraspecialPGroup_iff_isExtraspecial.2 hext
  have hZ : center (axisKernel B e) = zpowers ⟨_, hT⟩ := by
    rw [center_eq_ker hB hBl he0 he hf₀ hef₀, ker_flagHom hB he hf₀ hef₀]
  have hcard := natCard_axisKernel hB hBl (by omega) he0 he hf₀ hef₀
  refine ⟨⟨f₀, hf₀, hef₀⟩, hT, coe_transvectionGL e he, flagMap_zero_zero e, hZ,
    hext'.2.1.trans hZ, fun g => ?_, hext', hcard, by rw [hcard]; congr 1; omega,
    fun g hg => mem_sesqSpecialUnitaryGroup.2
      ⟨(mem_axisKernel.1 hg).1, det_eq_one hB hBl he0 he hf₀ hef₀ hg⟩,
    fun f hf hef => ?_⟩
  · rw [hZ]
    constructor
    · intro hg
      rcases eq_one_or_eq_of_mem_zpowers (orderOf_transvection_mk hB hBl he0 he) hg with h | h
      · left
        rw [h, flagMap_zero_zero]
        rfl
      · right
        rw [h]
        exact coe_transvectionGL e he
    · rintro (h | h)
      · have h1 : g = 1 := Subtype.ext (Units.ext (by rw [h, flagMap_zero_zero]; rfl))
        rw [h1]
        exact one_mem _
      · have h1 : g = ⟨_, hT⟩ := Subtype.ext (Units.ext (by rw [h, coe_transvectionGL e he]))
        rw [h1]
        exact mem_zpowers _
  obtain ⟨-, -, hcompl, -, hfin⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).2 f hef hf
  refine ⟨hcompl, hfin, fun g => ⟨fun hg => ?_, ?_⟩, fun u hu a htr => ?_,
    fun u hu v hv a b => ?_, fun g hg y hy hey => apply_normalized hg hy hey,
    fun y hy hey => existsUnique_apply_f hB he hf hef hy hey,
    fun y hy hey => existsUnique_line hB he hf hef hy hey⟩
  · obtain ⟨u, hu, a, htr, hgeq, -⟩ := eq_flagMap_of_mem hB he hf hef hg
    exact ⟨u, hu, a, htr, hgeq⟩
  · rintro ⟨u, hu, a, htr, hgeq⟩
    have heu := (mem_partnerPerp.1 hu).1
    have h1 : g = flagGL B hB he heu htr := Units.ext hgeq
    rw [h1]
    exact flagGL_mem hB he heu htr
  · have heu := (mem_partnerPerp.1 hu).1
    exact ⟨_, flagGL_mem hB he heu htr, coe_flagGL hB he heu htr⟩
  · have hue : B u e = 0 := by rw [← hB.eq e u, (mem_partnerPerp.1 hu).1, map_zero]
    exact flagMap_comp he hue (mem_partnerPerp.1 hv).1 a b

end CFSG.LocalAnalysis.GorensteinLyons
