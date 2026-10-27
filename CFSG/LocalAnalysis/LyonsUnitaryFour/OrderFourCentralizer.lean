module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Local
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Local

public section

namespace CFSG.RankTwoShapes.UnitaryFourW

variable {K : Type} [Field K] {hK : Nat.card K = 16}

theorem mul_comm_iff (v w : unitaryFourW K hK) :
    v * w = w * v ↔ fst v ^ 4 * fst w = fst v * fst w ^ 4 := by
  have := charP_two_of_natCard_eq_sixteen hK
  constructor
  · intro h
    have h2 := congrArg snd h
    rw [snd_mul, snd_mul] at h2
    linear_combination h2
  · intro h
    ext
    · rw [fst_mul, fst_mul, add_comm]
    · rw [snd_mul, snd_mul]
      linear_combination h

theorem orderOf_eq_four (w : unitaryFourW K hK) (hw : fst w ≠ 0) : orderOf w = 4 := by
  have h4 : w ^ 4 = 1 := pow_four_eq_one w
  have h2 : w ^ 2 ≠ 1 := by
    rw [Ne, sq_eq_one_iff_mem_center, center_eq_ker_firstCoord, mem_ker_firstCoord]
    exact hw
  have hdvd : orderOf w ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [h4])
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · rw [pow_zero, orderOf_eq_one_iff] at hkeq
    exact absurd (by rw [hkeq, one_pow]) h2
  · exact absurd (by rw [← hkeq.trans (pow_one 2)]; exact pow_orderOf_eq_one w) h2
  · rw [hkeq]; norm_num

theorem fst_ne_zero_of_orderOf (w : unitaryFourW K hK) (hw : orderOf w = 4) : fst w ≠ 0 := by
  intro h0
  have hc : w ∈ Subgroup.center (unitaryFourW K hK) := by
    rw [center_eq_ker_firstCoord, mem_ker_firstCoord]; exact h0
  have h2 := (sq_eq_one_iff_mem_center w).mpr hc
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hw] at this
  norm_num at this

theorem natCard_centralizer (w : unitaryFourW K hK) (hw : fst w ≠ 0) :
    Nat.card (Subgroup.centralizer ({w} : Set (unitaryFourW K hK))) = 16 := by
  classical
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  have : Finite (unitaryFourW K hK) := finite_unitaryFourW
  set Cw := Subgroup.centralizer ({w} : Set (unitaryFourW K hK)) with hCw
  set φ : Cw →* Multiplicative K := (firstCoord hK).comp Cw.subtype with hφ
  have hle : Subgroup.center (unitaryFourW K hK) ≤ Cw := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hz w).symm
  have hker : Nat.card φ.ker = 4 := by
    have hkereq : φ.ker = (Subgroup.center (unitaryFourW K hK)).subgroupOf Cw := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, center_eq_ker_firstCoord, MonoidHom.mem_ker]
      rfl
    rw [hkereq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, natCard_center]
  have hmem : ∀ c : K, Multiplicative.ofAdd c ∈ φ.range ↔ c ^ 4 * fst w = c * fst w ^ 4 := by
    intro c
    constructor
    · rintro ⟨v, hv⟩
      have hvc : fst (v : unitaryFourW K hK) = c := by
        have := congrArg Multiplicative.toAdd hv
        simpa [hφ] using this
      have hcomm : (v : unitaryFourW K hK) * w = w * v :=
        Subgroup.mem_centralizer_singleton_iff.mp v.2
      rw [← hvc]
      exact (mul_comm_iff _ _).mp hcomm
    · intro h
      obtain ⟨v, hv⟩ := exists_fst_eq (hK := hK) c
      have hvC : v ∈ Cw := by
        rw [hCw, Subgroup.mem_centralizer_singleton_iff, mul_comm_iff, hv]
        exact h
      exact ⟨⟨v, hvC⟩, by simp [hφ, hv]⟩
  have hrange : Nat.card φ.range = 4 := by
    have e1 : φ.range ≃ {c : K // c ^ 4 * fst w = c * fst w ^ 4} :=
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative K),
          (hmem _).mp (by simp)⟩
        invFun := fun c => ⟨Multiplicative.ofAdd (c : K), (hmem _).mpr c.2⟩
        left_inv := fun x => by simp
        right_inv := fun c => by simp }
    have e2 : {t : K // t ^ 4 = t} ≃ {c : K // c ^ 4 * fst w = c * fst w ^ 4} :=
      Equiv.subtypeEquiv (Equiv.mulRight₀ (fst w) hw) (fun t => by
        show t ^ 4 = t ↔ (t * fst w) ^ 4 * fst w = (t * fst w) * fst w ^ 4
        have h5 : fst w ^ 5 ≠ 0 := pow_ne_zero 5 hw
        constructor
        · intro h; linear_combination fst w ^ 5 * h
        · intro h
          have h' : t ^ 4 * fst w ^ 5 = t * fst w ^ 5 := by linear_combination h
          exact mul_right_cancel₀ h5 h')
    rw [Nat.card_congr e1, ← Nat.card_congr e2, natCard_pow_four_eq_self hK]
  have h := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, hrange] at h
  omega

end CFSG.RankTwoShapes.UnitaryFourW

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_homocyclic_of_commute {Q : Type*} [Group Q] [Finite Q] {x y : Q}
    {e : ℕ} (hx : orderOf x = 2 ^ e) (hy : orderOf y = 2 ^ e) (hxy : Commute x y)
    (hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (A : Subgroup Q) (hxA : x ∈ A)
    (hyA : y ∈ A) (hA : Nat.card A ≤ 4 ^ e) :
    Nat.card A = 4 ^ e ∧
      Nonempty (A ≃* Multiplicative (ZMod (2 ^ e)) × Multiplicative (ZMod (2 ^ e))) := by
  let f : Subgroup.zpowers x × Subgroup.zpowers y →* Q :=
    MonoidHom.noncommCoprod (Subgroup.zpowers x).subtype (Subgroup.zpowers y).subtype
      (by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact hxy.zpow_zpow i j)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    change a * b = 1 at hab
    have hab' : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
    have hmem : a ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y :=
      ⟨ha, hab' ▸ (Subgroup.zpowers y).inv_mem hb⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : b = 1 := by
      have := hab' ▸ hmem
      exact inv_eq_one.mp this
    ext <;> simp [hmem, hb1]
  have hfrange : f.range ≤ A := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    change a * b ∈ A
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact A.mul_mem (A.zpow_mem hxA i) (A.zpow_mem hyA j)
  have hcardprod : Nat.card (Subgroup.zpowers x × Subgroup.zpowers y) = 4 ^ e := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx, hy, ← mul_pow]
    norm_num
  have hcardA : Nat.card A = 4 ^ e := by
    apply le_antisymm hA
    calc 4 ^ e = Nat.card f.range := by
          rw [← hcardprod]; exact Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
      _ ≤ Nat.card A := Subgroup.card_le_of_le hfrange
  have hrangeEq : f.range = A :=
    Subgroup.eq_of_le_of_card_ge hfrange (by
      rw [hcardA, ← hcardprod]
      exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le)
  have hcyc : ∀ z : Q, orderOf z = 2 ^ e →
      Nonempty (Subgroup.zpowers z ≃* Multiplicative (ZMod (2 ^ e))) := by
    intro z hz
    have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ e := by rw [Nat.card_zpowers, hz]
    exact ⟨((zmodCyclicMulEquiv inferInstance).symm).trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)⟩
  obtain ⟨ex⟩ := hcyc x hx
  obtain ⟨ey⟩ := hcyc y hy
  exact ⟨hcardA, ⟨((MulEquiv.subgroupCongr hrangeEq).symm.trans
    (MonoidHom.ofInjective hfinj).symm).trans (MulEquiv.prodCongr ex ey)⟩⟩

theorem unitary_four_sylow_centralizer_order_four {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx : orderOf x = 4) :
    Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 16 ∧
    Nonempty (((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  classical
  obtain ⟨K, _, _, hK, ⟨φ⟩, -⟩ := CFSG.RankTwoShapes.unitaryFour_sylow_normCoordinates hT U
  have := CFSG.RankTwoShapes.charP_two_of_natCard_eq_sixteen hK
  have : Finite (CFSG.RankTwoShapes.unitaryFourW K hK) :=
    CFSG.RankTwoShapes.UnitaryFourW.finite_unitaryFourW
  obtain ⟨e₀⟩ := hSU
  set ψ := e₀.trans φ with hψ
  set Sg := (S : Subgroup G) with hSg
  set x' : Sg := ⟨x, hxS⟩ with hx'def
  have hx' : orderOf (ψ x') = 4 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx
  have ha := CFSG.RankTwoShapes.UnitaryFourW.fst_ne_zero_of_orderOf _ hx'
  set a := CFSG.RankTwoShapes.UnitaryFourW.fst (ψ x') with hadef
  set CS := Subgroup.centralizer ({x'} : Set Sg) with hCS
  set A := Sg ⊓ Subgroup.centralizer ({x} : Set G) with hA
  have hmapS : CS.map Sg.subtype = A := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s * x' = x' * s := Subgroup.mem_centralizer_singleton_iff.mp hs
      exact Subgroup.mem_inf.mpr ⟨s.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hs')⟩
    · intro hg
      obtain ⟨hgS, hgC⟩ := Subgroup.mem_inf.mp hg
      exact ⟨⟨g, hgS⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)), rfl⟩
  have hmapW : CS.map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ x'} : Set (CFSG.RankTwoShapes.unitaryFourW K hK)) := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s * x' = x' * s := Subgroup.mem_centralizer_singleton_iff.mp hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hs']
    · intro hv
      obtain ⟨s, rfl⟩ := ψ.surjective v
      refine ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply ψ.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hv
  have hcard : Nat.card A = 16 := by
    rw [← hmapS, Subgroup.card_map_of_injective Sg.subtype_injective,
      ← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hmapW,
      CFSG.RankTwoShapes.UnitaryFourW.natCard_centralizer _ ha]
  obtain ⟨l, hl⟩ := CFSG.RankTwoShapes.exists_sq_add_self_add_one_eq_zero hK
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hl3 : l ^ 3 = 1 := by linear_combination (l + 1) * hl - (l ^ 2 + l + 1) * h2K
  have hl4 : l ^ 4 = l := by linear_combination l * hl3
  have hl0 : l ≠ 0 := by rintro rfl; norm_num at hl
  have hl21 : l ^ 2 ≠ 1 := by
    intro h
    have h' : l = 0 := by linear_combination hl - h - h2K
    exact hl0 h'
  obtain ⟨v₀, hv₀⟩ := CFSG.RankTwoShapes.UnitaryFourW.exists_fst_eq (hK := hK) (l * a)
  have hv₀ne : CFSG.RankTwoShapes.UnitaryFourW.fst v₀ ≠ 0 := by
    rw [hv₀]; exact mul_ne_zero hl0 ha
  have hv₀comm : v₀ * ψ x' = ψ x' * v₀ := by
    rw [CFSG.RankTwoShapes.UnitaryFourW.mul_comm_iff, hv₀, ← hadef]
    linear_combination a ^ 5 * hl4
  have hsq_ne : (ψ x') ^ 2 ≠ v₀ ^ 2 := by
    intro h
    have h2 := congrArg CFSG.RankTwoShapes.UnitaryFourW.snd h
    rw [CFSG.RankTwoShapes.UnitaryFourW.snd_sq, CFSG.RankTwoShapes.UnitaryFourW.snd_sq, hv₀,
      ← hadef] at h2
    have h5 : a ^ 5 ≠ 0 := pow_ne_zero 5 ha
    have h3 : (l ^ 2 - 1) * a ^ 5 = 0 := by
      linear_combination (-1 : K) * h2 - l ^ 2 * a ^ 5 * hl3
    rcases mul_eq_zero.mp h3 with h | h
    · exact hl21 (sub_eq_zero.mp h)
    · exact h5 h
  set y' : Sg := ψ.symm v₀ with hy'def
  have hψy : ψ y' = v₀ := by rw [hy'def, MulEquiv.apply_symm_apply]
  have hxy' : x' * y' = y' * x' := by
    apply ψ.injective
    rw [map_mul, map_mul, hψy]
    exact hv₀comm.symm
  have hxy : Commute x (y' : G) := congrArg Subtype.val hxy'
  have hyord : orderOf (y' : G) = 4 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, hψy]
    exact CFSG.RankTwoShapes.UnitaryFourW.orderOf_eq_four _ hv₀ne
  have hyS : (y' : G) ∈ Sg := y'.2
  have hsqG : x ^ 2 ≠ (y' : G) ^ 2 := by
    intro h
    apply hsq_ne
    have h' : x' ^ 2 = y' ^ 2 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow]; exact h)
    rw [← hψy, ← map_pow, ← map_pow, h']
  have hx4 : orderOf x = 2 ^ 2 := by rw [hx]; norm_num
  have hy4 : orderOf (y' : G) = 2 ^ 2 := by rw [hyord]; norm_num
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers (y' : G) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htx, hty⟩
    rw [Subgroup.mem_bot]
    by_contra ht1
    have hdvd : orderOf t ∣ 2 ^ 2 := hx4 ▸ orderOf_dvd_of_mem_zpowers htx
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · exact ht1 (orderOf_eq_one_iff.mp (by simpa using hkeq))
    · have ht2 : orderOf t = 2 := by simpa using hkeq
      have h1 := CFSG.RankTwoShapes.eq_pow_of_mem_zpowers_of_orderOf_eq_two (by norm_num) hx4
        htx ht2
      have h2 := CFSG.RankTwoShapes.eq_pow_of_mem_zpowers_of_orderOf_eq_two (by norm_num) hy4
        hty ht2
      norm_num at h1 h2
      exact hsqG (h1.symm.trans h2)
    · have hord2 : orderOf (t ^ 2) = 2 := by
        rw [orderOf_pow' t (by norm_num), hkeq]; norm_num
      have h1 := CFSG.RankTwoShapes.eq_pow_of_mem_zpowers_of_orderOf_eq_two (by norm_num) hx4
        (Subgroup.pow_mem _ htx 2) hord2
      have h2 := CFSG.RankTwoShapes.eq_pow_of_mem_zpowers_of_orderOf_eq_two (by norm_num) hy4
        (Subgroup.pow_mem _ hty 2) hord2
      norm_num at h1 h2
      exact hsqG (h1.symm.trans h2)
  have hxA : x ∈ A := ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyA : (y' : G) ∈ A := ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hxy.eq.symm⟩
  obtain ⟨-, hiso⟩ := nonempty_mulEquiv_homocyclic_of_commute hx4 hy4 hxy hdisj A hxA hyA
    (by rw [hcard]; norm_num)
  exact ⟨hcard, hiso⟩
theorem unitary_four_order_four_centralizer_odd_complement {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx : orderOf x = 4) :
    Nonempty (((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    (∃ P : Sylow 2 (Subgroup.centralizer ({x} : Set G)),
      (P : Subgroup (Subgroup.centralizer ({x} : Set G))) =
        ((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))) ∧
    Subgroup.normalizer ((((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G)) : Subgroup (Subgroup.centralizer ({x} : Set G))) :
          Set (Subgroup.centralizer ({x} : Set G))) =
      Subgroup.centralizer ((((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G)) : Subgroup (Subgroup.centralizer ({x} : Set G))) :
          Set (Subgroup.centralizer ({x} : Set G))) ∧
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).Normal ∧
    Odd (Nat.card (CFSG.oddCore (Subgroup.centralizer ({x} : Set G)))) ∧
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).index = 16 ∧
    (∀ K' : Subgroup (Subgroup.centralizer ({x} : Set G)), K'.Normal → Odd (Nat.card K') →
      K'.index = 16 → K' = CFSG.oddCore (Subgroup.centralizer ({x} : Set G))) ∧
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).Characteristic ∧
    CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) ⊔
        ((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G)) = ⊤ ∧
    CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) ⊓
        ((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G)) = ⊥ ∧
    Function.Bijective ((QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({x} : Set G)))).comp
      (((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G))).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg := (S : Subgroup G) with hSg
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set A := Sg ⊓ C with hA
  obtain ⟨hAcard, ⟨eA⟩⟩ := unitary_four_sylow_centralizer_order_four hT S U hSU hxS hx
  set A' := A.subgroupOf C with hA'
  have hAC : A ≤ C := inf_le_right
  have hA'card : Nat.card A' = 16 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hAcard]
  have hA'p : IsPGroup 2 A' := IsPGroup.of_card (n := 4) (by rw [hA'card]; norm_num)
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set xC : C := ⟨x, hxC⟩ with hxCdef
  have hxA' : xC ∈ A' := by
    rw [hA', Subgroup.mem_subgroupOf]
    exact ⟨hxS, hxC⟩
  obtain ⟨P, hA'P⟩ := hA'p.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup C) ≤ 16 := by
    set P' := (P : Subgroup C).map C.subtype with hP'
    have hP'p : IsPGroup 2 P' := P.isPGroup'.map _
    obtain ⟨c, -, hc⟩ := exists_conj_le_sylow_of_le S le_top le_top hP'p
    have hxP' : x ∈ P' := ⟨xC, hA'P hxA', rfl⟩
    have hxcS : c * x * c⁻¹ ∈ Sg := hc x hxP'
    have hxcord : orderOf (c * x * c⁻¹) = 4 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
    have hle : P'.map (MulAut.conj c).toMonoidHom ≤
        Sg ⊓ Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.mpr ⟨hc q hq, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      obtain ⟨q', hq', rfl⟩ := hq
      have hqx : (q' : G) * x = x * q' := Subgroup.mem_centralizer_singleton_iff.mp q'.2
      calc c * (q' : G) * c⁻¹ * (c * x * c⁻¹) = c * ((q' : G) * x) * c⁻¹ := by group
        _ = c * (x * q') * c⁻¹ := by rw [hqx]
        _ = c * x * c⁻¹ * (c * q' * c⁻¹) := by group
    have h16 := (unitary_four_sylow_centralizer_order_four hT S U hSU hxcS hxcord).1
    calc Nat.card (P : Subgroup C) = Nat.card P' := by
          rw [hP', Subgroup.card_map_of_injective C.subtype_injective]
      _ = Nat.card (P'.map (MulAut.conj c).toMonoidHom) :=
          (Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (K := P')
            (MulAut.conj c).injective).symm
      _ ≤ 16 := h16 ▸ Subgroup.card_le_of_le hle
  have hPeq : (P : Subgroup C) = A' :=
    (Subgroup.eq_of_le_of_card_ge hA'P (by rw [hA'card]; exact hPcard)).symm
  have eP : (P : Subgroup C) ≃* CFSG.RankTwoShapes.HomocyclicGroup 2 :=
    ((MulEquiv.subgroupCongr hPeq).trans (Subgroup.subgroupOfEquivOfLe hAC)).trans eA
  have hxP : xC ∈ (P : Subgroup C) := hPeq ▸ hxA'
  have hxC1 : xC ≠ 1 := by
    intro h
    have : x = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hNC : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro g hg
    apply CFSG.RankTwoShapes.homocyclic_mem_centralizer_of_fixed P eP (by norm_num) hg hxP hxC1
    apply Subtype.ext
    have hgx : (g : G) * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    change (g : G) * x * (g : G)⁻¹ = x
    rw [hgx, mul_inv_cancel_right]
  have hNCeq : Subgroup.normalizer ((A' : Subgroup C) : Set C) =
      Subgroup.centralizer ((A' : Subgroup C) : Set C) := by
    rw [← hPeq]
    exact le_antisymm hNC (Subgroup.centralizer_le_normalizer _)
  set K₀ := (MonoidHom.transferSylow P hNC).ker with hK₀
  have hcomp : K₀.IsComplement' (P : Subgroup C) := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hPcard16 : Nat.card (P : Subgroup C) = 16 := by rw [hPeq, hA'card]
  have hK₀idx : K₀.index = 16 := by rw [hcomp.symm.index_eq_card, hPcard16]
  have hK₀odd : Odd (Nat.card K₀) := by
    have hnd := P.not_dvd_index
    rw [hcomp.index_eq_card] at hnd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  set Kc := CFSG.oddCore C with hKc
  have hK₀le : K₀ ≤ Kc := le_sSup ⟨inferInstance, hK₀odd⟩
  have hleK₀ : Kc ≤ K₀ := by
    intro k hk
    have hq : orderOf (QuotientGroup.mk' K₀ k) ∣ 2 ^ 4 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' K₀ k)
      rwa [← Subgroup.index_eq_card, hK₀idx] at h
    have hq' : orderOf (QuotientGroup.mk' K₀ k) ∣ orderOf k := orderOf_map_dvd _ k
    have hodd : Odd (orderOf (QuotientGroup.mk' K₀ k)) :=
      (CFSG.Adapters.odd_orderOf_of_mem_oddCore hk).of_dvd_nat hq'
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' K₀ k)) (2 ^ 4) :=
      (Nat.coprime_two_right.mpr hodd).pow_right 4
    have h1 := Nat.Coprime.eq_one_of_dvd hcop hq
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hK₀eq : K₀ = Kc := le_antisymm hK₀le hleK₀
  have hKcodd : Odd (Nat.card Kc) := hK₀eq ▸ hK₀odd
  have hKcidx : Kc.index = 16 := hK₀eq ▸ hK₀idx
  have huniq : ∀ K' : Subgroup C, K'.Normal → Odd (Nat.card K') → K'.index = 16 → K' = Kc := by
    intro K' hK'n hK'odd hK'idx
    have hle : K' ≤ Kc := le_sSup ⟨hK'n, hK'odd⟩
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := Subgroup.card_mul_index K'
    have h2 := Subgroup.card_mul_index Kc
    rw [hK'idx] at h1
    rw [hKcidx] at h2
    omega
  have hchar : Kc.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    apply huniq
    · exact (CFSG.oddCore_normal C).map φ.toMonoidHom φ.surjective
    · rw [Subgroup.card_map_of_injective φ.injective]; exact hKcodd
    · have h1 := Subgroup.card_mul_index (Kc.map φ.toMonoidHom)
      have h2 := Subgroup.card_mul_index Kc
      rw [Subgroup.card_map_of_injective φ.injective] at h1
      rw [hKcidx] at h2
      have hpos : 0 < Nat.card Kc := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hsup : Kc ⊔ A' = ⊤ := by rw [← hK₀eq, ← hPeq]; exact hcomp.sup_eq_top
  have hinf : Kc ⊓ A' = ⊥ := by rw [← hK₀eq, ← hPeq]; exact disjoint_iff.mp hcomp.disjoint
  have hbij : Function.Bijective ((QuotientGroup.mk' Kc).comp A'.subtype) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro a ha
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
      have hmem : (a : C) ∈ Kc ⊓ A' := ⟨ha, a.2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro y
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Kc y
      have hc : c ∈ ((Kc ⊔ A' : Subgroup C) : Set C) := by rw [hsup]; exact Subgroup.mem_top c
      rw [Subgroup.normal_mul, Set.mem_mul] at hc
      obtain ⟨k, hk, a, ha, rfl⟩ := hc
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq]
      show a⁻¹ * (k * a) ∈ Kc
      have h := (CFSG.oddCore_normal C).conj_mem k hk a⁻¹
      rw [inv_inv] at h
      rwa [← mul_assoc]
  exact ⟨⟨eA⟩, ⟨P, hPeq⟩, hNCeq, inferInstance, hKcodd, hKcidx, huniq, hchar, hsup, hinf, hbij⟩

end CFSG.LyonsUnitaryFour
