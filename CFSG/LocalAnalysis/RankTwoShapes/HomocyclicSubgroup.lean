module

public import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
public import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.RankTwoShapes

open scoped commutatorElement

universe u

variable {Q : Type u} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_le_four_pow_of_commutative (hrank : TwoRankLeTwo Q) :
    ∀ (e : ℕ) (B : Subgroup Q), IsMulCommutative B → (∀ b ∈ B, b ^ (2 ^ e) = 1) →
      Nat.card B ≤ 4 ^ e := by
  intro e
  induction e with
  | zero =>
    intro B _ hB
    have hbot : B = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro b hb
      simpa using hB b hb
    simp [hbot]
  | succ e ih =>
    intro B hcomm hB
    have hc : ∀ a b : B, Commute (a : Q) (b : Q) := fun a b =>
      congrArg Subtype.val (hcomm.is_comm.comm a b)
    let sq : B →* Q :=
      { toFun := fun b => (b : Q) ^ 2
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul]
          exact (hc a b).mul_pow 2 }
    have hker : Nat.card sq.ker ≤ 4 := by
      let E : Subgroup Q := sq.ker.map B.subtype
      have hEcomm : IsMulCommutative E := by
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨a', -, ha⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨b', -, hb⟩ := Subgroup.mem_map.mp b.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← ha, ← hb]
        exact (hc a' b').eq
      have hEexp : ∀ e ∈ E, e ^ 2 = 1 := by
        intro e he
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp he
        exact hb
      have hcard : Nat.card E = Nat.card sq.ker :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ _ B.subtype_injective).symm.toEquiv
      rw [← hcard]
      exact hrank E hEcomm hEexp
    have hrange : Nat.card sq.range ≤ 4 ^ e := by
      apply ih
      · refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨a', ha⟩ := a.2
        obtain ⟨b', hb⟩ := b.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← ha, ← hb]
        exact ((hc a' b').pow_pow 2 2).eq
      · rintro _ ⟨b, rfl⟩
        change ((b : Q) ^ 2) ^ (2 ^ e) = 1
        rw [← pow_mul, ← pow_succ']
        exact hB b b.2
    have htotal := Subgroup.card_ker_mul_card_range sq
    calc Nat.card B = Nat.card sq.ker * Nat.card sq.range := htotal.symm
      _ ≤ 4 * 4 ^ e := Nat.mul_le_mul hker hrange
      _ = 4 ^ (e + 1) := by ring

omit [Finite Q] in
theorem eq_pow_of_mem_zpowers_of_orderOf_eq_two {x v : Q} {e : ℕ} (he : 1 ≤ e)
    (hx : orderOf x = 2 ^ e) (hv : v ∈ Subgroup.zpowers x) (hv2 : orderOf v = 2) :
    v = x ^ (2 ^ (e - 1)) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hsq : (x ^ m) ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one _
  have hm2 : x ^ (m * 2) = 1 := by rw [zpow_mul]; exact_mod_cast hsq
  have hdvd : ((2 : ℤ) ^ (e - 1)) * 2 ∣ m * 2 := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hm2
    rw [hx] at h
    have he' : ((2 ^ e : ℕ) : ℤ) = 2 ^ (e - 1) * 2 := by
      push_cast; rw [← pow_succ]; congr 1; omega
    rwa [he'] at h
  obtain ⟨t, ht⟩ := Int.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
  set u := x ^ (2 ^ (e - 1)) with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← pow_mul, ← pow_succ]
    have : e - 1 + 1 = e := by omega
    rw [this, ← hx]; exact pow_orderOf_eq_one x
  have hxm : x ^ m = u ^ t := by
    rw [ht, hu, zpow_mul]; norm_cast
  have hu2' : u ^ (2 : ℤ) = 1 := by exact_mod_cast hu2
  rcases Int.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    have h1 : x ^ m = 1 := by
      rw [hxm, hs, ← two_mul, zpow_mul, hu2', one_zpow]
    rw [h1, orderOf_one] at hv2
    norm_num at hv2
  · rw [hxm, hs, zpow_add, zpow_mul, hu2', one_zpow, one_mul, zpow_one]

theorem three_automorphism_homocyclic_subgroup (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q)
    (α : MulAut Q) (hα : α ^ 3 = 1) (hfpf : ∀ q : Q, α q = q → q = 1) (x : Q)
    (hxmax : ∀ y : Q, orderOf y ≤ orderOf x) {e : ℕ} (he : orderOf x = 2 ^ e) (he1 : 1 ≤ e) :
    (∀ a ∈ Subgroup.closure ({x, α x} : Set Q), α a ∈ Subgroup.closure ({x, α x} : Set Q)) ∧
      IsMulCommutative (Subgroup.closure ({x, α x} : Set Q)) ∧
      Nonempty (Subgroup.closure ({x, α x} : Set Q) ≃*
        Multiplicative (ZMod (2 ^ e)) × Multiplicative (ZMod (2 ^ e))) ∧
      Subgroup.center Q ≤ Subgroup.closure ({x, α x} : Set Q) ∧
      (Subgroup.closure ({x, α x} : Set Q)).Normal ∧
      Subgroup.centralizer (Subgroup.closure ({x, α x} : Set Q) : Set Q) =
        Subgroup.closure ({x, α x} : Set Q) ∧
      ((∀ a b : Q, a * b = b * a) → Subgroup.closure ({x, α x} : Set Q) = ⊤) := by
  classical
  set A := Subgroup.closure ({x, α x} : Set Q) with hA
  set y := α x with hy
  have hxy : Commute x y := fpfThree_commute α hα hfpf x
  have hnorm : x * y * α y = 1 := fpfThree_norm α hα hfpf x
  have hαy : α y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right hnorm
  have hxA : x ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyA : y ∈ A := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative A := by
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hinv : ∀ a ∈ A, α a ∈ A := by
    intro a ha
    have hle : A ≤ A.comap α.toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl
      · exact hyA
      · change α y ∈ A
        rw [hαy]; exact A.inv_mem (A.mul_mem hxA hyA)
    exact hle ha
  have hexp : ∀ b : Q, b ^ (2 ^ e) = 1 := by
    intro b
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ b
    have hle : 2 ^ k ≤ 2 ^ e := hk ▸ he ▸ hxmax b
    have hke : k ≤ e := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact Nat.pow_dvd_pow 2 hke
  have hbound : ∀ B : Subgroup Q, IsMulCommutative B → Nat.card B ≤ 4 ^ e := fun B hB =>
    card_le_four_pow_of_commutative hrank e B hB (fun b _ => hexp b)
  have hu : orderOf (x ^ (2 ^ (e - 1))) = 2 := by
    rw [orderOf_pow' x (by positivity), he]
    have h : Nat.gcd (2 ^ e) (2 ^ (e - 1)) = 2 ^ (e - 1) :=
      Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (Nat.sub_le e 1))
    rw [h]
    have : 2 ^ e = 2 ^ (e - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hyord : orderOf y = 2 ^ e := by
    rw [hy, MulEquiv.orderOf_eq]; exact he
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ w
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [pow_zero, orderOf_eq_one_iff] at hk; exact absurd hk hw1
      · exact h
    set v := w ^ (2 ^ (k - 1)) with hv
    have hv2 : orderOf v = 2 := by
      rw [hv, orderOf_pow' w (by positivity), hk]
      have h : Nat.gcd (2 ^ k) (2 ^ (k - 1)) = 2 ^ (k - 1) :=
        Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (Nat.sub_le k 1))
      rw [h]
      have : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    have hvx : v = x ^ (2 ^ (e - 1)) :=
      eq_pow_of_mem_zpowers_of_orderOf_eq_two he1 he (Subgroup.pow_mem _ hw.1 _) hv2
    have hvy : v = y ^ (2 ^ (e - 1)) :=
      eq_pow_of_mem_zpowers_of_orderOf_eq_two he1 hyord (Subgroup.pow_mem _ hw.2 _) hv2
    have hfix : α (x ^ (2 ^ (e - 1))) = x ^ (2 ^ (e - 1)) := by
      rw [map_pow, ← hy, ← hvy, hvx]
    have h1 := hfpf _ hfix
    rw [h1, orderOf_one] at hu
    norm_num at hu
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
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, he, hyord, ← mul_pow]
    norm_num
  have hcardA : Nat.card A = 4 ^ e := by
    apply le_antisymm (hbound A hcomm)
    calc 4 ^ e = Nat.card f.range := by
          rw [← hcardprod]; exact Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
      _ ≤ Nat.card A := Subgroup.card_le_of_le hfrange
  have hrangeEq : f.range = A :=
    Subgroup.eq_of_le_of_card_ge hfrange (by
      rw [hcardA, ← hcardprod]
      exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le)
  have hcent : Subgroup.centralizer (A : Set Q) = A := by
    apply le_antisymm
    · intro z hz
      let B := Subgroup.closure ((A : Set Q) ∪ {z})
      have hBcomm : IsMulCommutative B := by
        apply Subgroup.isMulCommutative_closure
        intro a ha b hb _
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        · rw [Set.mem_singleton_iff] at hb; subst hb
          exact Subgroup.mem_centralizer_iff.mp hz a ha
        · rw [Set.mem_singleton_iff] at ha; subst ha
          exact (Subgroup.mem_centralizer_iff.mp hz b hb).symm
        · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; exact Commute.refl _
      have hAB : A ≤ B := fun a ha => Subgroup.subset_closure (Or.inl ha)
      have hBA : B = A := (Subgroup.eq_of_le_of_card_ge hAB (by
        rw [hcardA]; exact hbound B hBcomm)).symm
      have hzB : z ∈ B := Subgroup.subset_closure (Or.inr rfl)
      exact hBA ▸ hzB
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hcenter : Subgroup.center Q ≤ A := by
    intro z hz
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro a _
    exact (Subgroup.mem_center_iff.mp hz a)
  have hnormal : A.Normal := by
    refine ⟨fun a ha q => ?_⟩
    have hc : ⁅q, a⁆ ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (fpfThree_commutatorElement_central α hα hfpf q a g).symm.eq
    have : q * a * q⁻¹ = ⁅q, a⁆ * a := by
      rw [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem (hcenter hc) ha
  refine ⟨hinv, hcomm, ?_, hcenter, hnormal, hcent, ?_⟩
  ·
    have hcyc : ∀ z : Q, orderOf z = 2 ^ e →
        Nonempty (Subgroup.zpowers z ≃* Multiplicative (ZMod (2 ^ e))) := by
      intro z hz
      have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ e := by rw [Nat.card_zpowers, hz]
      exact ⟨((zmodCyclicMulEquiv inferInstance).symm).trans
        (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)⟩
    obtain ⟨ex⟩ := hcyc x he
    obtain ⟨ey⟩ := hcyc y hyord
    exact ⟨((MulEquiv.subgroupCongr hrangeEq).symm.trans
      (MonoidHom.ofInjective hfinj).symm).trans (MulEquiv.prodCongr ex ey)⟩
  · intro habel
    rw [← hcent]
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_centralizer_iff]
    intro a _
    exact habel a z

end CFSG.RankTwoShapes
