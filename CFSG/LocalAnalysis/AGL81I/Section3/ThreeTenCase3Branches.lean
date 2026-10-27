module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase4SylowFive
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.QD32Facts
open CFSG.RankThree.GroupTheory.SteinbergBY
open CFSG.Quasithin.AutQ8D8 (fixSub mem_fixSub card_modEq_fixSub card_fixSub_dvd fixSub_eq_top)

theorem eq_one_of_odd_order_of_fixes_normal_and_quotient {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) {α : MulAut X}
    (hfixN : ∀ n : N, α n = n)
    (hquot : ∀ x : X, (QuotientGroup.mk (α x) : X ⧸ N) = QuotientGroup.mk x)
    (hodd : Odd (orderOf α)) : α = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  have hmem : α x * x⁻¹ ∈ N := by
    simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).mp (hquot x)
  let n : N := ⟨α x * x⁻¹, hmem⟩
  have hx : α x = (n : X) * x := by
    dsimp [n]
    group
  have hpow : ∀ k : ℕ, (α ^ k) x = ((n : X) ^ k) * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (α ^ (k + 1)) x = α ((α ^ k) x) := by rw [pow_succ', MulAut.mul_apply]
          _ = α (((n : X) ^ k) * x) := by rw [ih]
          _ = (α ((n : X) ^ k)) * (α x) := map_mul α _ _
          _ = ((n : X) ^ k) * ((n : X) * x) := by
              rw [hfixN ⟨(n : X) ^ k, N.pow_mem n.2 k⟩, hx]
          _ = ((n : X) ^ (k + 1)) * x := by rw [pow_succ']; group
  have hxd : x = ((n : X) ^ orderOf α) * x := by
    have h := hpow (orderOf α)
    rw [pow_orderOf_eq_one] at h
    simpa using h
  have hnpow : (n : X) ^ orderOf α = 1 := by
    have := congrArg (fun y => y * x⁻¹) hxd
    simpa [mul_assoc] using this.symm
  have hnpow' : n ^ orderOf α = 1 := Subtype.ext hnpow
  have hdvd : orderOf n ∣ orderOf α := orderOf_dvd_of_pow_eq_one hnpow'
  have hoddn : Odd (orderOf n) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨m, hm⟩ := hN.exists_orderOf_eq_pow n
  have hm0 : m = 0 := by
    by_contra hmne
    have h2 : Even (2 ^ m) :=
      Even.pow_of_ne_zero (by norm_num : Even 2) hmne
    exact (Nat.not_even_iff_odd.mpr (hm ▸ hoddn)) h2
  have hn1 : n = 1 := by
    rw [← orderOf_eq_one_iff, hm, hm0, pow_zero]
  rw [hx, hn1]
  simp

noncomputable def restrictAutTo {X : Type} [Group X] {N : Subgroup X} (α : MulAut X)
    (h : N.map α.toMonoidHom = N) : MulAut N :=
  (MulEquiv.subgroupMap α N).trans (MulEquiv.subgroupCongr h)

@[simp] theorem coe_restrictAutTo {X : Type} [Group X] {N : Subgroup X} (α : MulAut X)
    (h : N.map α.toMonoidHom = N) (x : N) : ((restrictAutTo α h x : N) : X) = α x := by
  rw [restrictAutTo, MulEquiv.trans_apply]
  rfl

theorem coe_restrictAutTo_pow {X : Type} [Group X] {N : Subgroup X} (α : MulAut X)
    (h : N.map α.toMonoidHom = N) (k : ℕ) (x : N) :
    ((((restrictAutTo α h) ^ k) x : N) : X) = (α ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, coe_restrictAutTo, ih, pow_succ', MulAut.mul_apply]

noncomputable def quotientAutOf {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (α : MulAut X) (h : N.map α.toMonoidHom = N) : MulAut (X ⧸ N) :=
  QuotientGroup.congr N N α h

@[simp] theorem quotientAutOf_mk {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (α : MulAut X) (h : N.map α.toMonoidHom = N) (x : X) :
    quotientAutOf α h (QuotientGroup.mk x) = QuotientGroup.mk (α x) := by
  exact QuotientGroup.congr_mk N N α h x

theorem quotientAutOf_pow_mk {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (α : MulAut X) (h : N.map α.toMonoidHom = N) (k : ℕ) (x : X) :
    (((quotientAutOf α h) ^ k) (QuotientGroup.mk x)) = QuotientGroup.mk ((α ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, quotientAutOf_mk, pow_succ', MulAut.mul_apply]

theorem pCore_eq_bot_of_isSimpleGroup_of_not_isPGroup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {p : ℕ} (h : ¬ IsPGroup p G) : CFSG.pCore p G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore p G) with hbot | htop
  · exact hbot
  · exfalso
    apply h
    have hP : IsPGroup p (↥(⊤ : Subgroup G)) := htop ▸ CFSG.pCore_isPGroup
    exact hP.of_equiv Subgroup.topEquiv

theorem pCore_two_eq_of_normal_isPGroup_of_simple_quotient {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hNp : IsPGroup 2 N) {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hQ : ¬ IsPGroup 2 Q) (e : (X ⧸ N) ≃* Q) :
    CFSG.pCore 2 X = N := by
  classical
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  have hNle : N ≤ CFSG.pCore 2 X := by
    rw [CFSG.pCore]
    exact le_sSup ⟨inferInstance, hNp⟩
  have hquot_bot : CFSG.pCore 2 (X ⧸ N) = ⊥ := by
    have hcoreQ : CFSG.pCore 2 Q = ⊥ := pCore_eq_bot_of_isSimpleGroup_of_not_isPGroup hQ
    have hmap : (CFSG.pCore 2 (X ⧸ N)).map e.toMonoidHom = ⊥ := by
      rw [CFSG.pCore_map_iso 2 e, hcoreQ]
    have hle : CFSG.pCore 2 (X ⧸ N) ≤ e.toMonoidHom.ker :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 (X ⧸ N)) (f := e.toMonoidHom)).mp hmap
    rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective, le_bot_iff] at hle
    exact hle
  have hmap_le : (CFSG.pCore 2 X).map q ≤ CFSG.pCore 2 (X ⧸ N) := by
    rw [CFSG.pCore]
    refine le_sSup ⟨Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 X).Normal) q
      (QuotientGroup.mk'_surjective N), IsPGroup.map (CFSG.pCore_isPGroup) q⟩
  have hmap_bot : (CFSG.pCore 2 X).map q = ⊥ :=
    le_bot_iff.mp (hmap_le.trans (le_of_eq hquot_bot))
  have hleN : CFSG.pCore 2 X ≤ N := by
    have := (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 X) (f := q)).mp hmap_bot
    simpa [q, QuotientGroup.ker_mk'] using this
  exact le_antisymm hleN hNle

theorem normal_card_two_le_center {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center X := by
  classical
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  have hzN : (⟨z, hz⟩ : N) = y := huniq _ (by simpa using hz1)
  have hconj : (⟨g * z * g⁻¹, (inferInstance : N.Normal).conj_mem z hz g⟩ : N) = y :=
    huniq _ (by
      intro h
      have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
      have hz' : z = 1 := by
        have := congrArg (fun t => g⁻¹ * t * g) h'
        simpa [mul_assoc] using this
      exact hz1 hz')
  have hzz : g * z * g⁻¹ = z := congrArg Subtype.val (hconj.trans hzN.symm)
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hzz]

theorem card_map_mk'_eq_of_inf_bot {X : Type} [Group X] {N H : Subgroup X} [N.Normal]
    (h : H ⊓ N = ⊥) : Nat.card (H.map (QuotientGroup.mk' N)) = Nat.card H := by
  classical
  let f : H → H.map (QuotientGroup.mk' N) := fun x =>
    ⟨QuotientGroup.mk' N (x : X), ⟨x, x.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' : (f x : X ⧸ N) = (f y : X ⧸ N) := congrArg Subtype.val hxy
    have hq : (QuotientGroup.mk (x : X) : X ⧸ N) = QuotientGroup.mk (y : X) := hxy'
    have hmemN : x.1 / y.1 ∈ N := (QuotientGroup.eq_iff_div_mem).mp hq
    have hmemH : x.1 / y.1 ∈ H := H.div_mem x.2 y.2
    have hbot : x.1 / y.1 ∈ (⊥ : Subgroup X) := by
      rw [← h]
      exact ⟨hmemH, hmemN⟩
    exact Subtype.ext (div_eq_one.mp (Subgroup.mem_bot.mp hbot))
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : H ≃ H.map (QuotientGroup.mk' N) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact Nat.card_congr e.symm

theorem subsingleton_mulAut_of_natCard_two {N : Type} [Group N] (hN : Nat.card N = 2) :
    Subsingleton (MulAut N) := by
  refine ⟨fun a b => MulEquiv.ext fun x => ?_⟩
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  have hx : x = 1 ∨ x = z := by
    by_cases h : x = 1
    · exact Or.inl h
    · exact Or.inr (huniq x h)
  rcases hx with rfl | hxz
  · rw [map_one, map_one]
  · rw [hxz]
    have haz : a z = z :=
      huniq (a z) (fun h => hz1 (a.injective (h.trans (map_one a).symm)))
    have hbz : b z = z :=
      huniq (b z) (fun h => hz1 (b.injective (h.trans (map_one b).symm)))
    rw [haz, hbz]

theorem eq_three_of_prime_dvd_1440 {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (h : d ∣ 1440) : d = 3 := by
  have h' : d ∣ 2 ^ 5 * 3 ^ 2 * 5 := by
    rw [show 2 ^ 5 * 3 ^ 2 * 5 = 1440 by norm_num]
    exact h
  rcases hd.dvd_mul.mp h' with h23 | h5
  · rcases hd.dvd_mul.mp h23 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp
        (hd.dvd_of_dvd_pow h2)) hd2
    · exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h3)
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5) hd5

theorem eq_three_or_five_of_prime_dvd_235 {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (h : d ∣ 2 ^ 7 * 3 * 5) : d = 3 ∨ d = 5 := by
  have h' : d ∣ 2 ^ 7 * (3 * 5) := by
    rw [show 2 ^ 7 * (3 * 5) = 2 ^ 7 * 3 * 5 by ring]
    exact h
  rcases hd.dvd_mul.mp h' with h2 | h35
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp
      (hd.dvd_of_dvd_pow h2)) hd2
  · rcases hd.dvd_mul.mp h35 with h3 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5)

theorem eq_three_of_prime_dvd_720 {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (h : d ∣ 720) : d = 3 := by
  have h' : d ∣ 2 ^ 4 * 3 ^ 2 * 5 := by
    rw [show 2 ^ 4 * 3 ^ 2 * 5 = 720 by norm_num]
    exact h
  rcases hd.dvd_mul.mp h' with h23 | h5
  · rcases hd.dvd_mul.mp h23 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp
        (hd.dvd_of_dvd_pow h2)) hd2
    · exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h3)
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5) hd5

theorem eq_three_of_prime_dvd_1920 {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (h : d ∣ 1920) : d = 3 := by
  have h' : d ∣ 2 ^ 7 * 3 * 5 := by
    rw [show 2 ^ 7 * 3 * 5 = 1920 by norm_num]
    exact h
  rcases hd.dvd_mul.mp h' with h23 | h5
  · rcases hd.dvd_mul.mp h23 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp
        (hd.dvd_of_dvd_pow h2)) hd2
    · exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5) hd5

theorem natCard_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem alt6_eq_top_of_index_le_five {H : Subgroup (alternatingGroup (Fin 6))}
    (hH : H.index ≤ 5) : H = ⊤ := by
  classical
  by_contra hne
  let x : alternatingGroup (Fin 6) ⧸ H := QuotientGroup.mk 1
  have hcases := CFSG.QuasithinUnique.Setup.X3.orbit_card_cases
    (Γ := alternatingGroup (Fin 6)) (X := alternatingGroup (Fin 6) ⧸ H)
    (MulEquiv.refl _) x
  have hstab : MulAction.stabilizer (alternatingGroup (Fin 6)) x = H := by
    simpa [x] using MulAction.stabilizer_quotient H
  have hidx : H.index = (MulAction.orbit (alternatingGroup (Fin 6)) x).ncard := by
    rw [← MulAction.index_stabilizer (G := alternatingGroup (Fin 6)) (x := x), hstab]
  rcases hcases with h1 | ⟨h6, -⟩
  · rw [← hidx] at h1
    exact hne (Subgroup.index_eq_one.mp h1)
  · rw [← hidx] at h6
    omega

theorem alternatingGroup_six_eq_top_of_card_five_card_nine
    {P E : Subgroup (alternatingGroup (Fin 6))}
    (hP : Nat.card P = 5) (hE : Nat.card E = 9) : P ⊔ E = ⊤ := by
  classical
  set H : Subgroup (alternatingGroup (Fin 6)) := P ⊔ E with hHdef
  have hPle : P ≤ H := le_sup_left
  have hEle : E ≤ H := le_sup_right
  have h5 : 5 ∣ Nat.card H := by
    rw [← hP]
    exact Subgroup.card_dvd_of_le hPle
  have h9 : 9 ∣ Nat.card H := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le hEle
  have h45 : 45 ∣ Nat.card H := by
    have hcop : Nat.Coprime 5 9 := by norm_num
    simpa using hcop.mul_dvd_of_dvd_of_dvd h5 h9
  have hHdvd : Nat.card H ∣ 360 := by
    rw [← natCard_alternatingGroup_six]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨k, hk⟩ := h45
  have hkdvd : k ∣ 8 := by
    rw [hk] at hHdvd
    rw [show (360 : ℕ) = 45 * 8 by norm_num] at hHdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 45)).mp hHdvd
  obtain ⟨j, hj, hjk⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 3) Nat.prime_two).mp (by simpa using hkdvd)
  subst hjk
  have hk45 : Nat.card H = 45 * 2 ^ j := hk
  interval_cases j
  · exact absurd hk45 (by
      intro h
      exact CFSG.QuasithinUnique.Setup.X3.no_subgroup_order (K := H) (Or.inr (Or.inr (by
        rw [h]; norm_num))))
  · have hidx : H.index ≤ 5 := by
      rw [Subgroup.index_eq_card_div, natCard_alternatingGroup_six, hk45]
      norm_num
    have htop := alt6_eq_top_of_index_le_five hidx
    rw [htop, Subgroup.card_top, natCard_alternatingGroup_six] at hk45
    norm_num at hk45
  · have hidx : H.index ≤ 5 := by
      rw [Subgroup.index_eq_card_div, natCard_alternatingGroup_six, hk45]
      norm_num
    have htop := alt6_eq_top_of_index_le_five hidx
    rw [htop, Subgroup.card_top, natCard_alternatingGroup_six] at hk45
    norm_num at hk45
  · exact Subgroup.eq_top_of_card_eq H (by rw [hk45, natCard_alternatingGroup_six]; norm_num)

theorem natCard_sylow_five_of_z5_extension {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X) :
    Nat.card (Sylow 5 X) = 16 := by
  classical
  have hXcard : Nat.card X = 160 := natCard_of_isExtNotation_zmod_five_q8d8 hX
  obtain ⟨N, hNnormal, hBN, hAN, hno⟩ := hX
  haveI := hNnormal
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hBN
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hPcard : Nat.card (P : Subgroup X) = 5 := by
    have h := P.card_eq_multiplicity
    rw [hXcard] at h
    have h5p : 5 ^ (160 : ℕ).factorization 5 = 5 := by decide +kernel
    rwa [h5p] at h
  have hdvd : Nat.card (Sylow 5 X) ∣ 32 := by
    have h := P.card_dvd_index
    rw [Subgroup.index_eq_card_div, hXcard, hPcard] at h
    norm_num at h
    exact h
  have hmod := card_sylow_modEq_one 5 X
  have hne1 : Nat.card (Sylow 5 X) ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow 5 X) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hPnormal : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
    have hPN : N ⊓ (P : Subgroup X) = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      rw [hNcard, hPcard]
      norm_num
    have hsup : N ⊔ (P : Subgroup X) = ⊤ := by
      have hcard := CFSG.ABGLocalTools.card_sup_of_coprime (p := 5) (N := N)
        (Q := (P : Subgroup X)) (by rw [hNcard]; norm_num) P.isPGroup'
      apply Subgroup.eq_top_of_card_eq
      rw [hcard, hPcard, hNcard, hXcard]
    exact hno ⟨(P : Subgroup X), hPnormal, hPN, hsup⟩
  obtain ⟨m, hmle, hm⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 5) Nat.prime_two).mp
      (by simpa [show (32 : ℕ) = 2 ^ 5 by norm_num] using hdvd)
  have hmod' : (2 : ℕ) ^ m % 5 = 1 := by
    rw [← hm]
    exact hmod
  interval_cases m
  · exact absurd (by rw [hm, pow_zero]) hne1
  · norm_num at hmod'
  · norm_num at hmod'
  · norm_num at hmod'
  · rw [hm]
    norm_num
  · norm_num at hmod'

theorem threeTenCase3Z5AutInput_holds : ThreeTenCase3Z5AutInput := by
  intro X _ _ hX d hd hd2 hd5 hdvd
  classical
  have hXcard : Nat.card X = 160 := natCard_of_isExtNotation_zmod_five_q8d8 hX
  have hSylowCard : Nat.card (Sylow 5 X) = 16 := natCard_sylow_five_of_z5_extension hX
  obtain ⟨N, hNnormal, hBN, hAN, hno⟩ := hX
  haveI := hNnormal
  have hNtype : IsQ8D8Type N := hBN
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hNtype
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 5) (by rw [hNcard]; norm_num)
  have hNchar : N.Characteristic := characteristic_of_isQ8D8Type_of_card hNtype hXcard
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨α, hαd⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hαd
    exact hd.ne_one hαd.symm
  have hNmap : N.map α.toMonoidHom = N :=
    Subgroup.characteristic_iff_map_eq.mp hNchar α
  let αN : MulAut N := restrictAutTo α hNmap
  let αq : MulAut (X ⧸ N) := quotientAutOf α hNmap
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (X ⧸ N) := isCyclic_of_card_dvd_prime (p := 5) (by rw [hAN])
  have hcardAutQuot : Nat.card (MulAut (X ⧸ N)) = 4 := by
    rw [IsCyclic.card_mulAut, hAN, Nat.totient_prime Nat.prime_five]
  have hαqpow : αq ^ d = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotientAutOf_pow_mk, ← hαd, pow_orderOf_eq_one]
    rfl
  have hαq1 : αq = 1 := by
    by_contra hq1
    have hαqorder : orderOf αq = d := by
      have hdvd' : orderOf αq ∣ d := orderOf_dvd_of_pow_eq_one hαqpow
      rcases (Nat.dvd_prime hd).mp hdvd' with h1 | hd'
      · exact absurd (orderOf_eq_one_iff.mp h1) hq1
      · exact hd'
    have hdvd4 : d ∣ 4 := by
      have h := orderOf_dvd_natCard αq
      rw [hαqorder, hcardAutQuot] at h
      exact h
    have hd2' : d = 2 := by
      obtain ⟨m, hmle, hm⟩ :=
        (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp
          (by simpa using hdvd4)
      rw [hm] at hd ⊢
      have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm012 with rfl | rfl | rfl
      · norm_num at hd
      · norm_num
      · norm_num at hd
    exact hd2 hd2'
  have hquot : ∀ x : X, (QuotientGroup.mk (α x) : X ⧸ N) = QuotientGroup.mk x := by
    intro x
    have h := congrArg (fun β : MulAut (X ⧸ N) => β (QuotientGroup.mk x)) hαq1
    simpa [αq] using h
  have hαN1 : αN ≠ 1 := by
    intro hN1
    have hfixN : ∀ n : N, α n = n := by
      intro n
      have h1 : αN n = n := by
        rw [hN1]
        rfl
      calc α n = ((αN n : N) : X) := (coe_restrictAutTo α hNmap n).symm
        _ = ((n : N) : X) := by rw [h1]
    have hαeq1 : α = 1 :=
      eq_one_of_odd_order_of_fixes_normal_and_quotient hNp hfixN hquot
        (by simpa [hαd] using hd.odd_of_ne_two hd2)
    exact hα1 hαeq1
  have hαNpow : αN ^ d = 1 := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    rw [coe_restrictAutTo_pow, ← hαd, pow_orderOf_eq_one]
    rfl
  have hαNorder : orderOf αN = d := by
    have hdvd' : orderOf αN ∣ d := orderOf_dvd_of_pow_eq_one hαNpow
    rcases (Nat.dvd_prime hd).mp hdvd' with h1 | hd'
    · exact absurd (orderOf_eq_one_iff.mp h1) hαN1
    · exact hd'
  obtain ⟨eN⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.nonempty_mulEquiv_QD32_of_isQ8D8Type hNtype hNcard
  have hcardAutN : Nat.card (MulAut N) = Nat.card (MulAut QD32) :=
    Nat.card_congr (MulAut.congr eN).toEquiv
  have hdvdAutN : d ∣ Nat.card (MulAut QD32) := by
    rw [← hcardAutN, ← hαNorder]
    exact orderOf_dvd_natCard αN
  have hdvd235 : d ∣ 2 ^ 7 * 3 * 5 := hdvdAutN.trans card_mulAut_QD32_dvd
  have hd3 : d = 3 := by
    rcases eq_three_or_five_of_prime_dvd_235 hd hd2 hdvd235 with h3 | h5
    · exact h3
    · exact absurd h5 hd5
  subst hd3
  exfalso
  let QAut : Subgroup (MulAut X) := Subgroup.zpowers α
  have hQAutP : IsPGroup 3 QAut := by
    apply IsPGroup.of_card (n := 1)
    dsimp [QAut]
    rw [Nat.card_zpowers, hαd]
  have hmodFix := hQAutP.card_modEq_card_fixedPoints (Sylow 5 X)
  have hfixpos : 0 < Nat.card (MulAction.fixedPoints QAut (Sylow 5 X)) := by
    by_contra h
    have h0 : Nat.card (MulAction.fixedPoints QAut (Sylow 5 X)) = 0 := by omega
    rw [hSylowCard, h0] at hmodFix
    norm_num at hmodFix
  haveI : Nonempty (MulAction.fixedPoints QAut (Sylow 5 X)) :=
    Finite.card_pos_iff.mp hfixpos
  obtain ⟨K, hK⟩ := Classical.choice
    (inferInstance : Nonempty (MulAction.fixedPoints QAut (Sylow 5 X)))
  have hαK : α • (K : Sylow 5 X) = (K : Sylow 5 X) :=
    hK ⟨α, Subgroup.mem_zpowers α⟩
  have hKmap : ((K : Sylow 5 X) : Subgroup X).map α.toMonoidHom =
      (K : Subgroup X) := by
    have h := Subgroup.pointwise_smul_def (a := α) ((K : Sylow 5 X) : Subgroup X)
    rw [← Sylow.pointwise_smul_def] at h
    rw [hαK] at h
    have hto : MulDistribMulAction.toMonoidEnd (MulAut X) X α = α.toMonoidHom := by
      ext x
      rfl
    rw [hto] at h
    exact h.symm
  have hKcard : Nat.card (K : Subgroup X) = 5 := by
    have h := (K : Sylow 5 X).card_eq_multiplicity
    rw [hXcard] at h
    have h5p : 5 ^ (160 : ℕ).factorization 5 = 5 := by decide +kernel
    rwa [h5p] at h
  let αK : MulAut (K : Subgroup X) := restrictAutTo α hKmap
  have hαK1 : αK = 1 := by
    by_contra hne
    have hαKpow : αK ^ 3 = 1 := by
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      rw [coe_restrictAutTo_pow, ← hαd, pow_orderOf_eq_one]
      rfl
    have hαKorder : orderOf αK = 3 := by
      have hdvd' : orderOf αK ∣ 3 := orderOf_dvd_of_pow_eq_one hαKpow
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h3
    have hmodK := card_modEq_fixSub αK (r := 3) (k := 1) (by simpa using hαKorder)
    have hfixdvd : Nat.card (fixSub αK) ∣ 5 := by
      simpa [hKcard] using card_fixSub_dvd αK
    have hmodK' : 5 ≡ Nat.card (fixSub αK) [MOD 3] := by
      simpa [hKcard] using hmodK
    have hfix5 : Nat.card (fixSub αK) = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp hfixdvd with h1 | h5
      · exfalso
        rw [h1] at hmodK'
        norm_num at hmodK'
      · exact h5
    exact hne (fixSub_eq_top (Subgroup.eq_top_of_card_eq _ (by rw [hfix5, hKcard])))
  have hfixK : ∀ k : (K : Subgroup X), α k = k := by
    intro k
    have h1 : αK k = k := by
      rw [hαK1]
      rfl
    calc α k = ((αK k : (K : Subgroup X)) : X) := (coe_restrictAutTo α hKmap k).symm
      _ = ((k : (K : Subgroup X)) : X) := by rw [h1]
  have hKne : (K : Subgroup X) ≠ ⊥ := by
    intro h
    have := hKcard
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨k0, hk0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  let ρ : X →* MulAut N := MulAut.conjNormal (H := N)
  let β : MulAut N := ρ (k0 : X)
  have hβapply : ∀ n : N, ((β n : N) : X) = (k0 : X) * (n : X) * (k0 : X)⁻¹ := by
    intro n
    simpa [β, ρ] using MulAut.conjNormal_apply (H := N) (k0 : X) n
  have hk0pow : (k0 : (K : Subgroup X)) ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := (K : Subgroup X)) (x := k0)
    rwa [hKcard] at h
  have hk0powX : (k0 : X) ^ 5 = 1 := by
    have h := congrArg (fun x : (K : Subgroup X) => (x : X)) hk0pow
    simpa using h
  have hβpow : β ^ 5 = 1 := by
    change ρ (k0 : X) ^ 5 = 1
    rw [← map_pow, hk0powX, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ
    have hk0ker : (k0 : X) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      change ρ (k0 : X) = 1
      exact hβ
    have hk0neX : (k0 : X) ≠ 1 := fun h => hk0ne (Subtype.ext h)
    have hk0order : orderOf (k0 : X) = 5 := by
      have hdvd' : orderOf (k0 : X) ∣ 5 := by
        have h := Subgroup.orderOf_dvd_natCard (K : Subgroup X) k0.2
        rwa [hKcard] at h
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd' with h1 | h5
      · exact absurd (orderOf_eq_one_iff.mp h1) hk0neX
      · exact h5
    have hKzp : Subgroup.zpowers (k0 : X) = (K : Subgroup X) := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr k0.2)
      rw [Nat.card_zpowers, hk0order, hKcard]
    have hKker : (K : Subgroup X) ≤ ρ.ker := by
      rw [← hKzp]
      exact Subgroup.zpowers_le.mpr hk0ker
    have hNnormK : N ≤ Subgroup.normalizer ((K : Subgroup X) : Set X) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      have hcommK : ∀ x ∈ (K : Subgroup X), n * x = x * n := by
        intro x hx
        have hρx : ρ x = 1 := by
          have := hKker hx
          simpa using this
        have hρapply : (ρ x) ⟨n, hn⟩ = ⟨n, hn⟩ := by rw [hρx]; rfl
        have hconj : x * n * x⁻¹ = n := by
          have := congrArg Subtype.val hρapply
          simpa [ρ] using this
        calc n * x = (x * n * x⁻¹) * x := by rw [hconj]
          _ = x * n := by group
      have hconjOf : ∀ x ∈ (K : Subgroup X), n * x * n⁻¹ = x := by
        intro x hx
        have hcomm := hcommK x hx
        calc n * x * n⁻¹ = x * n * n⁻¹ := by rw [hcomm]
          _ = x := by group
      intro k
      constructor
      · intro hk
        rw [hconjOf k hk]
        exact hk
      · intro hk
        have hcomm := hcommK (n * k * n⁻¹) hk
        have hconj : n * k * n⁻¹ = k := by
          calc n * k * n⁻¹ = n⁻¹ * (n * (n * k * n⁻¹)) := by group
            _ = n⁻¹ * ((n * k * n⁻¹) * n) := by rw [hcomm]
            _ = k := by group
        rwa [← hconj]
    have hNKsup : N ⊔ (K : Subgroup X) = ⊤ := by
      have hcard := CFSG.ABGLocalTools.card_sup_of_coprime (p := 5) (N := N)
        (Q := (K : Subgroup X)) (by rw [hNcard]; norm_num) (K : Sylow 5 X).isPGroup'
      apply Subgroup.eq_top_of_card_eq
      rw [hcard, hKcard, hNcard, hXcard]
    have hKnormal : (K : Subgroup X).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      apply top_le_iff.mp
      rw [← hNKsup]
      exact sup_le hNnormK Subgroup.le_normalizer
    have hNKbot : N ⊓ (K : Subgroup X) = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      rw [hNcard, hKcard]
      norm_num
    exact hno ⟨(K : Subgroup X), hKnormal, hNKbot, hNKsup⟩
  have hβ5 : orderOf β = 5 := by
    have hdvd' : orderOf β ∣ 5 := orderOf_dvd_of_pow_eq_one hβpow
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd' with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hβ1
    · exact h5
  have hγd : orderOf αN = 3 := hαNorder
  have hcomm : αN * β = β * αN := by
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    calc ((αN * β) n : X)
        = α ((β n : N) : X) := by rw [MulAut.mul_apply, coe_restrictAutTo]
      _ = α ((k0 : X) * (n : X) * (k0 : X)⁻¹) := by rw [hβapply n]
      _ = (k0 : X) * α (n : X) * (k0 : X)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hfixK k0]
      _ = (k0 : X) * ((αN n : N) : X) * (k0 : X)⁻¹ := by rw [coe_restrictAutTo]
      _ = ((β * αN) n : X) := by
          rw [MulAut.mul_apply, hβapply (αN n), coe_restrictAutTo]
  exact no_order_of_commute_order_five hNtype hβ1 hβ5 hcomm hd hd2 hd5 hγd

theorem threeTenCase3A5Q8D8FiniteInput_holds : ThreeTenCase3A5Q8D8FiniteInput := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX d hd hd2 hd5 hdvd
    have hcard : Nat.card X = 1920 :=
      natCard_of_isExtNotation_alternating_five_q8d8_ext hX
    by_cases hd3 : d = 3
    · subst hd3
      rw [hcard]
      norm_num
    · exact threeTenCase4ExtFiniteInput.1 X hX d hd hd2 hd3 hdvd
  · intro X _ _ P E d hX hd hd2 hd5 hP hE
    haveI : Fact d.Prime := ⟨hd⟩
    have hcardX : Nat.card X = 1920 :=
      natCard_of_isExtNotation_alternating_five_q8d8_ext hX
    by_cases hEbot : E = ⊥
    · have hN : Subgroup.normalizer (E : Set X) = ⊤ := by
        rw [hEbot]
        exact Subgroup.normalizer_eq_top (⊥ : Subgroup X)
      rw [hN, sup_top_eq]
    · have hcardE : Nat.card E = d ^ (Nat.card X).factorization d := by
        simpa [Subgroup.card_top] using hE.card_eq
      have hk : 0 < (Nat.card X).factorization d := by
        by_contra h
        have hk0 : (Nat.card X).factorization d = 0 := by omega
        have h1 : Nat.card E = 1 := by rw [hcardE, hk0, pow_zero]
        exact hEbot (Subgroup.eq_bot_of_card_eq E h1)
      have hdvdE : d ∣ Nat.card E := by
        rw [hcardE]
        exact dvd_pow_self d (n := (Nat.card X).factorization d)
          (Nat.pos_iff_ne_zero.mp hk)
      have hdvdX : d ∣ Nat.card X :=
        dvd_trans hdvdE (Subgroup.card_subgroup_dvd_card E)
      have hd3 : d = 3 :=
        eq_three_of_prime_dvd_1920 hd hd2 hd5 (by rwa [hcardX] at hdvdX)
      subst hd3
      have hgen := threeTenCase4ExtFiniteInput.2 X E P 5 hX Nat.prime_five
        (by norm_num) (by norm_num) hE hP
      rwa [sup_comm] at hgen

theorem normalizer_sup_eq_top_of_isExtNotation_alternating_six_two {X : Type} [Group X]
    [Finite X]
    (hX : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X)
    (P E : Subgroup X)
    (hP : CFSG.ABGLocalTools.IsSylowOf 5 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf 3 E ⊤) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  classical
  have hXcard : Nat.card X = 720 := natCard_of_isExtNotation_alternating_six_two hX
  obtain ⟨N, hNnormal, hBN, hAN, hno⟩ := hX
  haveI := hNnormal
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNcenter : N ≤ Subgroup.center X := normal_card_two_le_center hNcard
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card P = 5 := by
    have h := hP.card_eq
    rw [Subgroup.card_top, hXcard] at h
    have h5p : 5 ^ (720 : ℕ).factorization 5 = 5 := by decide +kernel
    rwa [h5p] at h
  have hEcard : Nat.card E = 9 := by
    have h := hE.card_eq
    rw [Subgroup.card_top, hXcard] at h
    have h3p : 3 ^ (720 : ℕ).factorization 3 = 9 := by decide +kernel
    rwa [h3p] at h
  let W : Subgroup X :=
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X)
  have hPleW : P ≤ W := Subgroup.le_normalizer.trans le_sup_left
  have hEleW : E ≤ W := Subgroup.le_normalizer.trans le_sup_right
  have hPN : P ⊓ N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hPcard, hNcard]
    norm_num
  have hEN : E ⊓ N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hEcard, hNcard]
    norm_num
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  have hPmapCard : Nat.card (P.map q) = 5 := by
    rw [card_map_mk'_eq_of_inf_bot hPN, hPcard]
  have hEmapCard : Nat.card (E.map q) = 9 := by
    rw [card_map_mk'_eq_of_inf_bot hEN, hEcard]
  let Pbar : Subgroup (alternatingGroup (Fin 6)) := (P.map q).map e.toMonoidHom
  let Ebar : Subgroup (alternatingGroup (Fin 6)) := (E.map q).map e.toMonoidHom
  have hPbar : Nat.card Pbar = 5 := by
    dsimp [Pbar]
    rw [Subgroup.card_map_of_injective e.injective, hPmapCard]
  have hEbar : Nat.card Ebar = 9 := by
    dsimp [Ebar]
    rw [Subgroup.card_map_of_injective e.injective, hEmapCard]
  have hgen : Pbar ⊔ Ebar = ⊤ :=
    alternatingGroup_six_eq_top_of_card_five_card_nine hPbar hEbar
  have hWmap : (W.map q).map e.toMonoidHom = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    refine sup_le ?_ ?_
    · exact Subgroup.map_mono (f := e.toMonoidHom) (Subgroup.map_mono (f := q) hPleW)
    · exact Subgroup.map_mono (f := e.toMonoidHom) (Subgroup.map_mono (f := q) hEleW)
  have htopmap : (⊤ : Subgroup (X ⧸ N)).map e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  have hWqTop : W.map q = ⊤ :=
    Subgroup.map_injective e.injective (hWmap.trans htopmap.symm)
  have hWsupN : W ⊔ N = ⊤ := by
    have h := Subgroup.comap_map_eq (f := q) W
    rw [hWqTop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hWnorm : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_le_iff.mp
    rw [← hWsupN]
    refine sup_le Subgroup.le_normalizer ?_
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hc : w * n = n * w := (Subgroup.mem_center_iff.mp (hNcenter hn)) w
    have hconj : n * w * n⁻¹ = w := by
      calc n * w * n⁻¹ = w * n * n⁻¹ := by rw [hc]
        _ = w := by group
    rw [hconj]
  by_contra hWne
  have hHne : W ⊓ N ≠ ⊥ := by
    intro hH
    exact hno ⟨W, hWnorm, by rwa [inf_comm], by rwa [sup_comm]⟩
  have hHtop : W ⊓ N = N := by
    have hHle : W ⊓ N ≤ N := inf_le_right
    have hdvd : Nat.card ↥(W ⊓ N) ∣ 2 := by
      have h := Subgroup.card_dvd_of_le hHle
      rwa [hNcard] at h
    have hHcard : Nat.card ↥(W ⊓ N) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hHne
      · exact h2
    exact Subgroup.eq_of_le_of_card_ge hHle (by rw [hHcard, hNcard])
  have hNleW : N ≤ W := inf_eq_right.mp hHtop
  have hWtop : W = ⊤ :=
    (sup_eq_left.mpr hNleW).symm.trans hWsupN
  exact hWne hWtop

theorem dvd_card_of_isExtNotation_alternating_six_two {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (hdvd : d ∣ Nat.card (MulAut X)) : d ∣ Nat.card X := by
  classical
  have hXcard : Nat.card X = 720 := natCard_of_isExtNotation_alternating_six_two hX
  obtain ⟨N, hNnormal, hBN, hAN, hno⟩ := hX
  haveI := hNnormal
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by rw [hNcard]; norm_num)
  have hQ : ¬ IsPGroup 2 (alternatingGroup (Fin 6)) := by
    intro h2
    obtain ⟨n, hn⟩ := h2.exists_card_dvd_pow
    have h3' : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
      rw [natCard_alternatingGroup_six]
      norm_num
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3'.trans hn)) (by norm_num)
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcore : CFSG.pCore 2 X = N :=
    pCore_two_eq_of_normal_isPGroup_of_simple_quotient hNp hQ e
  have hNchar : N.Characteristic := by
    rw [← hcore]
    infer_instance
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨α, hαd⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hαd
    exact hd.ne_one hαd.symm
  have hNmap : N.map α.toMonoidHom = N :=
    Subgroup.characteristic_iff_map_eq.mp hNchar α
  haveI : Subsingleton (MulAut N) := subsingleton_mulAut_of_natCard_two hNcard
  have hαN1 : restrictAutTo α hNmap = 1 := Subsingleton.elim _ _
  have hfixN : ∀ n : N, α n = n := by
    intro n
    have h1 : restrictAutTo α hNmap n = n := by
      rw [hαN1]
      rfl
    calc α n = ((restrictAutTo α hNmap n : N) : X) :=
          (coe_restrictAutTo α hNmap n).symm
      _ = ((n : N) : X) := by rw [h1]
  let αq : MulAut (X ⧸ N) := quotientAutOf α hNmap
  have hαqpow : αq ^ d = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotientAutOf_pow_mk, ← hαd, pow_orderOf_eq_one]
    rfl
  have hαq1 : αq ≠ 1 := by
    intro hq1
    have hquot : ∀ x : X,
        (QuotientGroup.mk (α x) : X ⧸ N) = QuotientGroup.mk x := by
      intro x
      have h := congrArg (fun β : MulAut (X ⧸ N) => β (QuotientGroup.mk x)) hq1
      simpa [αq] using h
    have hαeq1 : α = 1 :=
      eq_one_of_odd_order_of_fixes_normal_and_quotient hNp hfixN hquot
        (by simpa [hαd] using hd.odd_of_ne_two hd2)
    exact hα1 hαeq1
  have hαqorder : orderOf αq = d := by
    have hdvd' : orderOf αq ∣ d := orderOf_dvd_of_pow_eq_one hαqpow
    rcases (Nat.dvd_prime hd).mp hdvd' with h1 | hd'
    · exact absurd (orderOf_eq_one_iff.mp h1) hαq1
    · exact hd'
  have hcardAutQuot : Nat.card (MulAut (X ⧸ N)) =
      Nat.card (MulAut (alternatingGroup (Fin 6))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hdvdAut : d ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    rw [← hcardAutQuot, ← hαqorder]
    exact orderOf_dvd_natCard αq
  have hdvd1440 : d ∣ 1440 := by
    have h := hdvdAut.trans
      (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_six_dvd_two_mul)
    rwa [show 2 * Nat.factorial 6 = 1440 by norm_num] at h
  have hd3 : d = 3 := eq_three_of_prime_dvd_1440 hd hd2 hd5 hdvd1440
  rw [hXcard, hd3]
  norm_num

theorem threeTenCase3A6TwoFiniteInput_holds : ThreeTenCase3A6TwoFiniteInput := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX d hd hd2 hd5 hdvd
    exact dvd_card_of_isExtNotation_alternating_six_two hX hd hd2 hd5 hdvd
  · intro X _ _ P E d hX hd hd2 hd5 hP hE
    haveI : Fact d.Prime := ⟨hd⟩
    have hcardX : Nat.card X = 720 :=
      natCard_of_isExtNotation_alternating_six_two hX
    by_cases hEbot : E = ⊥
    · have hN : Subgroup.normalizer (E : Set X) = ⊤ := by
        rw [hEbot]
        exact Subgroup.normalizer_eq_top (⊥ : Subgroup X)
      rw [hN, sup_top_eq]
    · have hcardE : Nat.card E = d ^ (Nat.card X).factorization d := by
        simpa [Subgroup.card_top] using hE.card_eq
      have hk : 0 < (Nat.card X).factorization d := by
        by_contra h
        have hk0 : (Nat.card X).factorization d = 0 := by omega
        have h1 : Nat.card E = 1 := by rw [hcardE, hk0, pow_zero]
        exact hEbot (Subgroup.eq_bot_of_card_eq E h1)
      have hdvdE : d ∣ Nat.card E := by
        rw [hcardE]
        exact dvd_pow_self d (n := (Nat.card X).factorization d)
          (Nat.pos_iff_ne_zero.mp hk)
      have hdvdX : d ∣ Nat.card X :=
        dvd_trans hdvdE (Subgroup.card_subgroup_dvd_card E)
      have hd3 : d = 3 := by
        have h720 : d ∣ 720 := by rwa [hcardX] at hdvdX
        exact eq_three_of_prime_dvd_720 hd hd2 hd5 h720
      subst hd3
      have hE3 : CFSG.ABGLocalTools.IsSylowOf 3 E ⊤ := by simpa using hE
      exact normalizer_sup_eq_top_of_isExtNotation_alternating_six_two hX P E hP hE3

theorem threeTenCase3Z5FiniteInput_holds : ThreeTenCase3Z5FiniteInput :=
  threeTenCase3Z5FiniteInput_of_aut threeTenCase3Z5AutInput_holds

theorem threeTenCase3FiniteInput_holds : ThreeTenCase3FiniteInput :=
  threeTenCase3FiniteInput_of_branches threeTenCase3A6TwoFiniteInput_holds
    threeTenCase3A5Q8D8FiniteInput_holds threeTenCase3Z5FiniteInput_holds

end CFSG.LocalAnalysis.AGL81I.Section3
