module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.RankThree.PerfectCover

theorem exists_hom_lift_of_hopf_card {P S Y : Type} [Group P] [Finite P] [Group.IsPerfect P]
    [Group S] [Finite S] [Group Y] [Finite Y] (θ : P →* S) (hθ : Function.Surjective θ)
    (hθker : θ.ker ≤ Subgroup.center P)
    (hM : Nat.card (hopfMultiplier S) ≤ Nat.card θ.ker) (hM0 : Nat.card (hopfMultiplier S) ≠ 0)
    (q : Y →* S) (hq : Function.Surjective q) (hqker : q.ker ≤ Subgroup.center Y) :
    ∃ ρ : P →* Y, ∀ g, q (ρ g) = θ g := by
  classical
  haveI : Group.IsPerfect S := Group.IsPerfect.ofSurjective hθ
  obtain ⟨-, h, hph, -, hhs, hmap, eM, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier θ hθ hθker
  set M := hopfMultiplier S with hMdef
  set N := (h.comp M.subtype).ker with hN
  haveI : Finite M := Nat.finite_of_card_ne_zero hM0
  haveI : Finite N := inferInstance
  have hsplit : Nat.card M = Nat.card (M ⧸ N) * Nat.card N := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (N)
    exact this
  have hquot : Nat.card (M ⧸ N) = Nat.card θ.ker := Nat.card_congr eM.toEquiv
  have hN1 : Nat.card N = 1 := by
    have hpos : 0 < Nat.card θ.ker := Nat.card_pos
    have : Nat.card N ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h2 : Nat.card θ.ker * 2 ≤ Nat.card M := by
        rw [hsplit, hquot]
        exact Nat.mul_le_mul_left _ hgt
      omega
    exact le_antisymm this Nat.card_pos
  have hNbot : N = ⊥ := Subgroup.card_eq_one.1 hN1
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : hopfCoverMap S u = 1 := by
      rw [← hph, MonoidHom.comp_apply, hu, map_one]
    have hmem : (⟨u, hu'⟩ : M) ∈ N := by
      show h (⟨u, hu'⟩ : M) = 1
      exact hu
    rw [hNbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  let eh : HopfCover S ≃* P := MulEquiv.ofBijective h ⟨hinj, hhs⟩
  refine ⟨(hopfLift q hq hqker).comp eh.symm.toMonoidHom, fun g => ?_⟩
  have h1 : q (hopfLift q hq hqker (eh.symm g)) = hopfCoverMap S (eh.symm g) :=
    DFunLike.congr_fun (comp_hopfLift q hq hqker) (eh.symm g)
  have h2 : θ (h (eh.symm g)) = hopfCoverMap S (eh.symm g) :=
    DFunLike.congr_fun hph (eh.symm g)
  have h3 : h (eh.symm g) = g := eh.apply_symm_apply g
  show q (hopfLift q hq hqker (eh.symm g)) = θ g
  rw [h1, ← h2, h3]


theorem exists_twoSubgroup_of_lift {Y S : Type} [Group Y] [Finite Y] [Group S] [Finite S] (π : Y →* S)
    (hker : π.ker ≤ Subgroup.center Y) {U : Subgroup S} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hπ : Function.Surjective π) {E : Subgroup Y}
    (hE : E.map π ≤ Subgroup.normalizer (U : Set S)) :
    ∃ V : Subgroup Y, V ≠ ⊥ ∧ IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπZ : ∀ y, π y = 1 → y ∈ Subgroup.center Y := fun y hy => hker (MonoidHom.mem_ker.2 hy)
  set Ut : Subgroup Y := U.comap π with hUt
  haveI hUnil : Group.IsNilpotent U := hU2.isNilpotent
  have hnil : Group.IsNilpotent Ut := by
    refine Subgroup.isNilpotent_of_ker_le_center
      ((π.comp Ut.subtype).codRestrict U (fun x => x.2)) ?_
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := Subgroup.mem_center_iff.1 (hπZ _ h1)
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (h2 (g : Y))
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  haveI : (P : Subgroup Ut).Normal := inferInstance
  haveI : Unique (Sylow 2 Ut) := Sylow.unique_of_normal P inferInstance
  have hPiff : ∀ x : Ut, x ∈ (P : Subgroup Ut) ↔ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    · rintro ⟨k, hk⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
      have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
      obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
      have hQP : Q = P := Subsingleton.elim _ _
      subst hQP
      exact hQ (Subgroup.mem_zpowers x)
  let U₂ : Subgroup Y := (P : Subgroup Ut).map Ut.subtype
  have hU₂mem : ∀ y : Y, y ∈ U₂ ↔ y ∈ Ut ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := (hPiff x).1 hx
      exact ⟨x.2, k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨hy, k, hk⟩
      exact ⟨⟨y, hy⟩, (hPiff ⟨y, hy⟩).2 ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
  have hU₂p : IsPGroup 2 U₂ := P.isPGroup'.map Ut.subtype
  have hdvd : Nat.card U ∣ Nat.card Ut := by
    have h1 := Subgroup.card_map_dvd (H := Ut) π
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at h1
  have h2U : 2 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (Subgroup.eq_bot_of_card_eq U (by rw [hk]; rfl)) hU
    · rw [hk]; exact dvd_pow_self 2 hk0.ne'
  have hP2 : 2 ∣ Nat.card P := by
    have h1 : 2 ^ 1 ∣ Nat.card Ut := by simpa using h2U.trans hdvd
    simpa using P.pow_dvd_card_of_pow_dvd_card h1
  have hU₂ne : U₂ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card U₂ = Nat.card P := Subgroup.card_map_of_injective Ut.subtype_injective
    rw [hbot, Subgroup.card_bot] at h1
    rw [← h1] at hP2
    exact absurd (Nat.le_of_dvd one_pos hP2) (by norm_num)
  have hEtU : ∀ g ∈ E, ∀ y : Y, y ∈ Ut → g * y * g⁻¹ ∈ Ut := by
    intro g hg y hy
    have hg' : π g ∈ Subgroup.normalizer (U : Set S) := hE ⟨g, hg, rfl⟩
    have hy' : π y ∈ U := hy
    have := (Subgroup.mem_normalizer_iff.1 hg' (π y)).1 hy'
    change π (g * y * g⁻¹) ∈ U
    simpa [map_mul, map_inv] using this
  have hconj2 : ∀ g ∈ E, ∀ y ∈ U₂, g * y * g⁻¹ ∈ U₂ := by
    intro g hg y hy
    obtain ⟨hyU, k, hk⟩ := (hU₂mem y).1 hy
    refine (hU₂mem _).2 ⟨hEtU g hg y hyU, k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  refine ⟨U₂, hU₂ne, hU₂p, ?_⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => hconj2 g hg y hy
  · intro hy
    have := hconj2 g⁻¹ (E.inv_mem hg) _ hy
    simpa [mul_assoc] using this


theorem not_rkY_of_subgroup {Y S : Type} [Group Y] [Finite Y] [Group S] [Finite S]
    (π : Y →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center Y)
    {R : Subgroup Y} (hR : IsElemAbelian 3 R) (hcard : 3 ^ 4 ≤ Nat.card (R.map π))
    {U : Subgroup S} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hRU : R.map π ≤ Subgroup.normalizer (U : Set S)) : ¬ RkY Y := by
  classical
  intro hrk
  obtain ⟨V, hV, hV2, hRV⟩ := exists_twoSubgroup_of_lift π hker.le hU hU2 hπ (E := R) hRU
  obtain ⟨h4, h3⟩ := hrk V hV hV2 R hRV hR
  by_cases hz : R ⊓ Subgroup.center Y = ⊥
  · have hdvd : Nat.card (R.map π) ∣ Nat.card R := Subgroup.card_map_dvd (H := R) π
    have hle : Nat.card (R.map π) ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos hdvd
    have := h3 hz
    omega
  · have hex : ∃ z ∈ R ⊓ Subgroup.center Y, z ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hz ((Subgroup.eq_bot_iff_forall _).2 hno)
    obtain ⟨z, hzmem, hz1⟩ := hex
    let f : R →* S := π.comp R.subtype
    have hfrange : f.range = R.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hzker : (⟨z, hzmem.1⟩ : R) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have : z ∈ π.ker := by rw [hker]; exact hzmem.2
      exact this
    have hkerne : f.ker ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hzker
      exact hz1 (congrArg Subtype.val hzker)
    have hk2 : 2 ≤ Nat.card f.ker := (Subgroup.one_lt_card_iff_ne_bot f.ker).2 hkerne
    have hprod := Subgroup.card_ker_mul_card_range f
    rw [hfrange] at hprod
    have hmul : 2 * 3 ^ 4 ≤ Nat.card f.ker * Nat.card (R.map π) := Nat.mul_le_mul hk2 hcard
    have hEcard : Nat.card R = Nat.card f.ker * Nat.card (R.map π) := hprod.symm
    omega

theorem not_rkY_of_hom_lift {Y S P : Type} [Group Y] [Finite Y] [Group S] [Finite S] [Group P]
    (π : Y →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center Y)
    (ρ : P →* Y) (θ : P →* S) (hρθ : ∀ g, π (ρ g) = θ g) {E : Subgroup P}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card (E.map θ)) {U : Subgroup S} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : E.map θ ≤ Subgroup.normalizer (U : Set S)) : ¬ RkY Y := by
  have hcomp : π.comp ρ = θ := MonoidHom.ext hρθ
  have hE'π : (E.map ρ).map π = E.map θ := by
    rw [Subgroup.map_map, hcomp]
  exact not_rkY_of_subgroup π hπ hker (IsElemAbelian.map hE ρ) (by rw [hE'π]; exact hcard) hU hU2
    (by rw [hE'π]; exact hEU)

theorem exists_elemAbelian_three_lift {H P : Type} [Group H] [Finite H] [Group P] (h : H →* P)
    (hs : Function.Surjective h) (hcen : h.ker ≤ Subgroup.center H) (h2 : IsPGroup 2 h.ker)
    {E : Subgroup P} (hE : IsElemAbelian 3 E) :
    ∃ R : Subgroup H, IsElemAbelian 3 R ∧ R.map h = E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFinP : Finite P := Finite.of_surjective h hs
  set Et : Subgroup H := E.comap h with hEt
  haveI hEnil : Group.IsNilpotent E := (IsElemAbelian.isPGroup hE).isNilpotent
  have hnil : Group.IsNilpotent Et := by
    refine Subgroup.isNilpotent_of_ker_le_center ((h.comp Et.subtype).codRestrict E
      (fun x => x.2)) ?_
    intro x hx
    have h1 : h (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2' := Subgroup.mem_center_iff.1 (hcen (MonoidHom.mem_ker.2 h1))
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (h2' (g : H))
  obtain ⟨R⟩ : Nonempty (Sylow 3 Et) := inferInstance
  set R' : Subgroup H := (R : Subgroup Et).map Et.subtype with hR'
  have hR'3 : IsPGroup 3 R' := R.isPGroup'.map Et.subtype
  have hR'Et : ∀ r ∈ R', h r ∈ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hker : ∀ r ∈ R', h r = 1 → r = 1 := by
    intro r hr hr1
    obtain ⟨n, hn⟩ := hR'3 ⟨r, hr⟩
    obtain ⟨m, hm⟩ := h2 ⟨r, MonoidHom.mem_ker.2 hr1⟩
    have hn' : r ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hm' : r ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf r ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h2'' : orderOf r ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have : orderOf r ∣ Nat.gcd (3 ^ n) (2 ^ m) := Nat.dvd_gcd h1 h2''
    have hcop : Nat.Coprime (3 ^ n) (2 ^ m) :=
      Nat.Coprime.pow _ _ (by norm_num)
    rw [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  have hcomm : ∀ r ∈ R', ∀ t ∈ R', r * t = t * r := by
    intro r hr t ht
    have hc : r * t * (t * r)⁻¹ ∈ R' := R'.mul_mem (R'.mul_mem hr ht) (R'.inv_mem (R'.mul_mem ht hr))
    have h1 : h (r * t * (t * r)⁻¹) = 1 := by
      have : h r * h t = h t * h r :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨h r, hR'Et r hr⟩ ⟨h t, hR'Et t ht⟩)
      rw [map_mul, map_mul, map_inv, map_mul, this, mul_inv_cancel]
    have := hker _ hc h1
    exact (mul_inv_eq_one.1 this)
  have hexp : ∀ r ∈ R', r ^ 3 = 1 := by
    intro r hr
    refine hker _ (R'.pow_mem hr 3) ?_
    rw [map_pow]
    exact hE.2 _ (hR'Et r hr)
  have hR'ea : IsElemAbelian 3 R' :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩
  refine ⟨R', hR'ea, ?_⟩
  have hle : R'.map h ≤ E := by
    rintro _ ⟨r, hr, rfl⟩
    exact hR'Et r hr
  have hcardR' : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective Et.subtype_injective
  have hinj : Function.Injective (h.comp R'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    exact Subtype.ext (hker r r.2 hr)
  have hcardmap : Nat.card (R'.map h) = Nat.card R' := by
    have := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at this
    exact this.symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsElemAbelian.isPGroup hE)
  have hdvdE : Nat.card E ∣ Nat.card Et := by
    have h1 := Subgroup.card_map_dvd (H := Et) h
    rwa [Subgroup.map_comap_eq_self_of_surjective hs] at h1
  have hR : 3 ^ k ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (hk ▸ hdvdE)
  have hge : Nat.card E ≤ Nat.card (R'.map h) := by
    rw [hcardmap, hcardR', hk]
    exact Nat.le_of_dvd Nat.card_pos hR
  exact Subgroup.eq_of_le_of_card_ge hle hge


theorem exists_elemAbelian_lift_of_hopf_two_power {P S Y : Type} [Group P] [Finite P]
    [Group.IsPerfect P] [Group S] [Finite S] [Group Y] [Finite Y] (θ : P →* S)
    (hθ : Function.Surjective θ) (hθker : θ.ker ≤ Subgroup.center P)
    (hM0 : Nat.card (hopfMultiplier S) ≠ 0)
    (hM : ∃ k : ℕ, Nat.card (hopfMultiplier S) = Nat.card θ.ker * 2 ^ k)
    (q : Y →* S) (hq : Function.Surjective q) (hqker : q.ker ≤ Subgroup.center Y)
    {E : Subgroup P} (hE : IsElemAbelian 3 E) :
    ∃ R : Subgroup Y, IsElemAbelian 3 R ∧ R.map q = E.map θ := by
  classical
  haveI : Group.IsPerfect S := Group.IsPerfect.ofSurjective hθ
  obtain ⟨-, h, hph, -, hhs, hmap, eM, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier θ hθ hθker
  obtain ⟨k, hk⟩ := hM
  haveI : Finite (hopfMultiplier S) := Nat.finite_of_card_ne_zero hM0
  have hsurj : Function.Surjective (hopfCoverMap S) := hopfCoverMap_surjective
  have hrange : (hopfCoverMap S).range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have hcard1 := Subgroup.card_ker_mul_card_range (hopfCoverMap S)
  rw [hrange, Subgroup.card_top] at hcard1
  haveI : Finite (HopfCover S) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [← hcard1]
    exact mul_ne_zero hM0 Nat.card_pos.ne'
  have hker_le_M : h.ker ≤ hopfMultiplier S := by
    intro u hu
    show hopfCoverMap S u = 1
    rw [← hph, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hu, map_one]
  have hcen : h.ker ≤ Subgroup.center (HopfCover S) :=
    hker_le_M.trans hopfMultiplier_le_center
  have hrangeh : h.range = ⊤ := MonoidHom.range_eq_top.2 hhs
  have hcard2 := Subgroup.card_ker_mul_card_range h
  rw [hrangeh, Subgroup.card_top] at hcard2
  have hrangeθ : θ.range = ⊤ := MonoidHom.range_eq_top.2 hθ
  have hcard3 := Subgroup.card_ker_mul_card_range θ
  rw [hrangeθ, Subgroup.card_top] at hcard3
  have hker2 : Nat.card h.ker = 2 ^ k := by
    have hP0 : 0 < Nat.card P := Nat.card_pos
    have : Nat.card h.ker * Nat.card P = 2 ^ k * Nat.card P := by
      calc Nat.card h.ker * Nat.card P = Nat.card (HopfCover S) := hcard2
        _ = Nat.card (hopfMultiplier S) * Nat.card S := hcard1.symm
        _ = Nat.card θ.ker * 2 ^ k * Nat.card S := by rw [hk]
        _ = 2 ^ k * (Nat.card θ.ker * Nat.card S) := by ring
        _ = 2 ^ k * Nat.card P := by rw [hcard3]
    exact Nat.eq_of_mul_eq_mul_right hP0 this
  have h2 : IsPGroup 2 h.ker := IsPGroup.of_card (n := k) hker2
  obtain ⟨RH, hRH, hRHmap⟩ := exists_elemAbelian_three_lift h hhs hcen h2 hE
  refine ⟨RH.map (hopfLift q hq hqker), IsElemAbelian.map hRH _, ?_⟩
  rw [Subgroup.map_map, ← hRHmap, Subgroup.map_map]
  congr 1
  exact (comp_hopfLift q hq hqker).trans hph.symm

end CFSG.HardMathSupport.Dickson.Sec6.I1431
