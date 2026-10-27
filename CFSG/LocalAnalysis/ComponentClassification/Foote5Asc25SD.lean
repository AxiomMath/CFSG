module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSD
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4Four

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ComponentClassification.Foote5.HallGen

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {y a : G} (hy : y * y = 1) (ha : a ∈ zpowers y) :
    a = 1 ∨ a = y := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem false_of_four (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))
    (hc4 : orderOf c = 4) (hcD : c ∈ D) (hcard : Nat.card D = 2 * orderOf c) {S₀ : Subgroup G}
    (hDS : D ≤ S₀) (hcardS : Nat.card S₀ = 2 * Nat.card D) (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D)
    {v : G} (hvD : v ∈ D) (hvC : v ∉ zpowers c)
    (hcomm : ∀ s ∈ S₀, (s * v * s⁻¹) * v = v * (s * v * s⁻¹)) : False := by
  have hk : 4 ∣ orderOf c := by rw [hc4]
  have hz : cz c = c * c := by rw [cz, hc4, show 4 / 2 = 2 from rfl, sq]
  have hD0 : 0 < Nat.card D := Nat.card_pos
  have hconj : ∀ s ∈ S₀, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hd
    by_cases hsD : s ∈ D
    · exact mul_mem (mul_mem hsD hd) (inv_mem hsD)
    have h1 := inv_mul_mem_of_card_le hDS (by omega) (inv_mem hs) (mul_mem (hDS hd) (inv_mem hs))
      (fun h => hsD (by simpa using inv_mem h)) (fun h => hsD (by
        have := mul_mem (inv_mem hd) h
        simpa using inv_mem this))
    simpa [mul_assoc] using h1
  have hnorm : ∀ s ∈ S₀, s ∈ normalizer (D : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro d
    refine ⟨hconj s hs d, fun h => ?_⟩
    have := hconj s⁻¹ (inv_mem hs) _ h
    simpa [mul_assoc] using this
  obtain ⟨x, hxS, hxD⟩ : ∃ x ∈ S₀, x ∉ D := by
    by_contra h
    push Not at h
    have := card_le_of_le (fun s hs => h s hs : S₀ ≤ D)
    omega
  have hxN := hnorm x hxS
  have hv2 : v * v = 1 := by
    rcases hD v hvD with h | ⟨h, -⟩
    · exact absurd h hvC
    · exact h
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvc : v * c * v⁻¹ = c⁻¹ := by
    rcases hD v hvD with h | ⟨-, h⟩
    · exact absurd h hvC
    · exact h
  have hzc : ∀ g ∈ normalizer (D : Set G), g * cz c * g⁻¹ = cz c := fun g hg => conj_cz hD hk hg hcD
  have hcv : c * v * c⁻¹ = v * cz c := by
    have h1 : v⁻¹ * c * v = c⁻¹ := by
      calc v⁻¹ * c * v = v * c * v⁻¹ := by rw [hvi]
        _ = c⁻¹ := hvc
    have hc4' : c ^ 4 = 1 := by rw [← hc4]; exact pow_orderOf_eq_one c
    calc c * v * c⁻¹ = v * (v⁻¹ * c * v) * c⁻¹ := by group
      _ = v * (c⁻¹ * c⁻¹) := by rw [h1]; group
      _ = v * cz c := by
        rw [hz]
        congr 1
        calc c⁻¹ * c⁻¹ = c ^ 4 * c⁻¹ * c⁻¹ := by rw [hc4', one_mul]
          _ = c * c := by rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ,
                pow_one]; group
  have hxv : x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * cz c := by
    have hrefl : x * v * x⁻¹ ∈ D := (mem_normalizer_iff.mp hxN v).mp hvD
    have hreflC := conj_not_mem_zpowers hD hk hxN hcD hvC
    have hprod := mul_mem_zpowers_of_refl hD hk hvD hrefl hvC hreflC
    have hsq : (v * (x * v * x⁻¹)) * (v * (x * v * x⁻¹)) = 1 := by
      calc (v * (x * v * x⁻¹)) * (v * (x * v * x⁻¹)) =
          v * ((x * v * x⁻¹) * v) * (x * v * x⁻¹) := by group
        _ = v * (v * (x * v * x⁻¹)) * (x * v * x⁻¹) := by rw [hcomm x hxS]
        _ = (v * v) * (x * (v * v) * x⁻¹) := by group
        _ = 1 := by rw [hv2]; group
    rcases eq_one_or_eq_cz hk hprod hsq with h | h
    · left
      calc x * v * x⁻¹ = v⁻¹ * (v * (x * v * x⁻¹)) := by group
        _ = v := by rw [h, mul_one, hvi]
    · right
      calc x * v * x⁻¹ = v⁻¹ * (v * (x * v * x⁻¹)) := by group
        _ = v * cz c := by rw [h, hvi]
  obtain ⟨y, hyS, hyD, hyv⟩ : ∃ y ∈ S₀, y ∉ D ∧ y * v * y⁻¹ = v := by
    rcases hxv with h | h
    · exact ⟨x, hxS, hxD, h⟩
    · refine ⟨x * c, mul_mem hxS (hDS hcD), fun h' => hxD (by
        have := mul_mem h' (inv_mem hcD)
        simpa using this), ?_⟩
      calc x * c * v * (x * c)⁻¹ = x * (c * v * c⁻¹) * x⁻¹ := by group
        _ = x * (v * cz c) * x⁻¹ := by rw [hcv]
        _ = (x * v * x⁻¹) * (x * cz c * x⁻¹) := by group
        _ = v * cz c * cz c := by rw [h, hzc x hxN]
        _ = v := by rw [mul_assoc, cz_mul_cz hk, mul_one]
  have hyN := hnorm y hyS
  have hyv' : y * v = v * y := by
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [hyv]
  have hy2D : y * y ∈ D := by
    have h := inv_mul_mem_of_card_le hDS (by omega) (inv_mem hyS) hyS
      (fun h => hyD (by simpa using inv_mem h)) hyD
    rwa [inv_inv] at h
  have hy2C := sq_mem_zpowers hD hk hyN hcD hy2D
  have hy2 : y * y = cz c := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hy2C
    have h1 : v * c ^ i * v⁻¹ = c ^ (-i) := by rw [← conj_zpow, hvc, inv_zpow, zpow_neg]
    have h2 : v * (y * y) * v⁻¹ = y * y := by
      calc v * (y * y) * v⁻¹ = (v * y) * y * v⁻¹ := by group
        _ = (y * v) * y * v⁻¹ := by rw [← hyv']
        _ = y * (v * y) * v⁻¹ := by group
        _ = y * (y * v) * v⁻¹ := by rw [← hyv']
        _ = y * y := by group
    have hsq : (y * y) * (y * y) = 1 := by
      have h3 : c ^ i = c ^ (-i) := by rw [← h1, hi, h2]
      calc (y * y) * (y * y) = c ^ i * c ^ (-i) := by rw [← hi, ← h3]
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    rcases eq_one_or_eq_cz hk hy2C hsq with h | h
    · exact absurd (hinv y hyS h) hyD
    · exact h
  have hc2 : c * c = cz c := hz.symm
  have hycC := conj_c_mem hD hk hyN hcD
  have hyc2 : (y * c * y⁻¹) * (y * c * y⁻¹) = cz c := by
    rw [show (y * c * y⁻¹) * (y * c * y⁻¹) = y * (c * c) * y⁻¹ by group, hc2, hzc y hyN]
  have hzcc : c * cz c = cz c * c := comm_cz hD hk hcD
  rcases sq_eq_or_eq_inv hk hycC (mem_zpowers c) hyc2 hc2 with h | h
  ·
    apply hyD
    have hsq : (y * c) * (y * c) = 1 := by
      calc (y * c) * (y * c) = (y * c * y⁻¹) * (y * y) * c := by group
        _ = c * cz c * c := by rw [h, hy2]
        _ = cz c * (c * c) := by rw [hzcc]; group
        _ = 1 := by rw [hc2, cz_mul_cz hk]
    have := mul_mem (hinv _ (mul_mem hyS (hDS hcD)) hsq) (inv_mem hcD)
    simpa using this
  ·
    apply hyD
    have hzv : v * cz c = cz c * v := comm_cz hD hk hvD
    have hzc' : c⁻¹ * cz c = cz c * c⁻¹ := comm_cz hD hk (inv_mem hcD)
    have hsq : (y * c * v) * (y * c * v) = 1 := by
      calc (y * c * v) * (y * c * v) = (y * c * y⁻¹) * (y * v * y⁻¹) * (y * y) * (c * v) := by
            group
        _ = c⁻¹ * (v * cz c) * (c * v) := by rw [h, hyv, hy2]; group
        _ = c⁻¹ * (cz c * v) * (c * v) := by rw [hzv]
        _ = (c⁻¹ * cz c) * (v * c * v) := by group
        _ = (cz c * c⁻¹) * (v * c * v⁻¹) := by rw [hzc', hvi]
        _ = cz c * (c * c)⁻¹ := by rw [hvc]; group
        _ = 1 := by rw [hc2, mul_inv_cancel]
    have := mul_mem (mul_mem (hinv _ (mul_mem (mul_mem hyS (hDS hcD)) (hDS hvD)) hsq)
      (inv_mem hvD)) (inv_mem hcD)
    simpa [mul_assoc] using this

theorem isSemidihedral_of_inv (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))
    {m : ℕ} (hm : orderOf c = 2 ^ m) (hk : 4 ∣ orderOf c) (hcD : c ∈ D)
    (hcard : Nat.card D = 2 * orderOf c) {S₀ : Subgroup G} (hDS : D ≤ S₀)
    (hcardS : Nat.card S₀ = 2 * Nat.card D) (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D) :
    AschbacherTheorem3.IsSemidihedralTwoGroup S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S₀ := IsPGroup.of_card (n := m + 2) (by rw [hcardS, hcard, hm]; ring)
  obtain ⟨u, huD, huC⟩ := exists_refl hcard
  have hu2 : u * u = 1 := by
    rcases hD u huD with h | ⟨h, -⟩
    · exact absurd h huC
    · exact h
  have hstar : ∀ E : Subgroup S₀, E.Normal → E ≤ ⊤ → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False := by
    intro E hEn _ hEe hE4
    have hEsq : ∀ v ∈ E, (v : G) * v = 1 := fun v hv => by
      have := hEe.2 v hv
      rw [sq] at this
      exact congrArg Subtype.val this
    have hED : ∀ v ∈ E, (v : G) ∈ D := fun v hv => hinv _ v.2 (hEsq v hv)
    obtain ⟨v, hvE, hvC⟩ : ∃ v ∈ E, (v : G) ∉ zpowers c := by
      by_contra h
      push Not at h
      have hsub : (E : Set S₀) ⊆ {1, ⟨cz c, hDS (cz_mem hcD)⟩} := by
        intro v hv
        rcases eq_one_or_eq_cz hk (h v hv) (hEsq v hv) with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, ⟨cz c, hDS (cz_mem hcD)⟩} : Set S₀).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
      have h3 : Nat.card E = (E : Set S₀).ncard := Nat.card_coe_set_eq _
      omega
    have hvc : (v : G) * c * (v : G)⁻¹ = c⁻¹ := by
      rcases hD _ (hED v hvE) with h | ⟨-, h⟩
      · exact absurd h hvC
      · exact h
    have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right (hEsq v hvE)
    set c' : S₀ := ⟨c, hDS hcD⟩ with hc'
    have hw : v * (c' * v * c'⁻¹) ∈ E := mul_mem hvE (hEn.conj_mem v hvE c')
    have hwG : ((v * (c' * v * c'⁻¹) : S₀) : G) = c⁻¹ * c⁻¹ := by
      simp only [coe_mul, coe_inv, hc']
      calc (v : G) * (c * v * c⁻¹) = ((v : G) * c * (v : G)⁻¹) * c⁻¹ := by
            rw [hvi]
            group
        _ = c⁻¹ * c⁻¹ := by rw [hvc]
    have h4 : c⁻¹ * c⁻¹ * (c⁻¹ * c⁻¹) = 1 := by rw [← hwG]; exact hEsq _ hw
    have h5 : c ^ 4 = 1 := by
      have : (c ^ 4)⁻¹ = 1 := by rw [← h4]; group
      exact inv_eq_one.mp this
    have hc4 : orderOf c = 4 := le_antisymm (Nat.le_of_dvd (by norm_num)
      (orderOf_dvd_of_pow_eq_one h5)) (Nat.le_of_dvd (orderOf_pos c) hk)
    refine false_of_four hD hc4 hcD hcard hDS hcardS hinv (hED v hvE) hvC fun s hs => ?_
    have h1 : (⟨s, hs⟩ : S₀) * v * (⟨s, hs⟩ : S₀)⁻¹ ∈ E := hEn.conj_mem v hvE ⟨s, hs⟩
    have h2 := hEe.1.is_comm.comm (⟨_, h1⟩ : E) ⟨v, hvE⟩
    have h3 := congrArg (fun w : E => ((w : S₀) : G)) h2
    simpa using h3
  have hrank : ∃ E : Subgroup S₀, E ≤ ⊤ ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 2 := by
    set z' : S₀ := ⟨cz c, hDS (cz_mem hcD)⟩ with hz'
    set u' : S₀ := ⟨u, hDS huD⟩ with hu'
    have hzu : Commute z' u' := Subtype.ext (comm_cz hD hk huD).symm
    have hz2 : z' * z' = 1 := Subtype.ext (cz_mul_cz hk)
    have hu2' : u' * u' = 1 := Subtype.ext hu2
    have hz1 : z' ≠ 1 := fun h => cz_ne_one hk (congrArg Subtype.val h)
    have hu1 : u' ≠ 1 := fun h => huC (by
      have : u = 1 := congrArg Subtype.val h
      rw [this]
      exact one_mem _)
    have hzu' : z' ≠ u' := fun h => huC (by
      have : cz c = u := congrArg Subtype.val h
      rw [← this]
      exact cz_mem (mem_zpowers c))
    have hc : ∀ a ∈ zpowers z', ∀ b ∈ zpowers u', a * b = b * a := fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (hzu.zpow_zpow i j).eq
    have hinf : zpowers z' ⊓ zpowers u' = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [mem_bot]
      rcases eq_one_or_eq_of_mem_zpowers hz2 (mem_inf.mp ha).1 with h1 | h1
      · exact h1
      rcases eq_one_or_eq_of_mem_zpowers hu2' (mem_inf.mp ha).2 with h2 | h2
      · exact h2
      exact absurd (h1.symm.trans h2) hzu'
    have hoz : orderOf z' = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    have hou : orderOf u' = 2 := orderOf_eq_prime (by rw [sq]; exact hu2') hu1
    refine ⟨zpowers z' ⊔ zpowers u', le_top, FooteLit.F5.isElemAbelian_of_mul_self ?_, ?_⟩
    · intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := GH74.Uniqueness.Bender.exists_mul_of_mem_sup_of_commute hc hy
      have ha2 : a * a = 1 := by
        rcases eq_one_or_eq_of_mem_zpowers hz2 ha with h | h <;> rw [h]
        · rw [mul_one]
        · exact hz2
      have hb2 : b * b = 1 := by
        rcases eq_one_or_eq_of_mem_zpowers hu2' hb with h | h <;> rw [h]
        · rw [mul_one]
        · exact hu2'
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [(hc a ha b hb).symm]
        _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
    · rw [GH74.Uniqueness.Bender.card_sup_eq_mul_of_commute hc hinf, Nat.card_zpowers,
        Nat.card_zpowers, hoz, hou]
      norm_num
  rcases GH74.Uniqueness.SU.SU1.dihedral_or_semidihedral_of_no_normal_four hS2 (Q := ⊤) hstar
      hrank with ⟨N, -, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  ·
    exfalso
    set f' : S₀ ≃* DihedralGroup (2 ^ N) := Subgroup.topEquiv.symm.trans f with hf'
    have : NeZero (2 ^ N) := ⟨by positivity⟩
    have hcardP : Nat.card S₀ = 2 * 2 ^ N := by
      rw [Nat.card_congr f'.toEquiv, DihedralGroup.nat_card]
    have hsq : ∀ i : ZMod (2 ^ N), ((f'.symm (DihedralGroup.sr i) : S₀) : G) *
        (f'.symm (DihedralGroup.sr i) : S₀) = 1 := fun i => by
      rw [← coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, coe_one]
    let F : Option (ZMod (2 ^ N)) → D := fun o => o.elim 1 fun i =>
      ⟨(f'.symm (DihedralGroup.sr i) : S₀), hinv _ (f'.symm _).2 (hsq i)⟩
    have hF : Function.Injective F := by
      rintro (_ | i) (_ | j) h
      · rfl
      · exfalso
        have h1 : ((1 : D) : G) = (f'.symm (DihedralGroup.sr j) : S₀) := congrArg Subtype.val h
        have h2 : f'.symm (DihedralGroup.sr j) = 1 := Subtype.ext h1.symm
        rw [MulEquiv.symm_apply_eq, map_one] at h2
        cases h2
      · exfalso
        have h1 : ((f'.symm (DihedralGroup.sr i) : S₀) : G) = ((1 : D) : G) :=
          congrArg Subtype.val h
        have h2 : f'.symm (DihedralGroup.sr i) = 1 := Subtype.ext h1
        rw [MulEquiv.symm_apply_eq, map_one] at h2
        cases h2
      · have h1 : ((f'.symm (DihedralGroup.sr i) : S₀) : G) =
            ((f'.symm (DihedralGroup.sr j) : S₀) : G) := congrArg (Subtype.val : D → G) h
        have h2 := f'.symm.injective (Subtype.ext h1)
        simp only [DihedralGroup.sr.injEq] at h2
        rw [h2]
    have h1 := Nat.card_le_card_of_injective F hF
    rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, ZMod.card] at h1
    omega
  · exact ⟨n, hn, ⟨Subgroup.topEquiv.symm.trans f⟩⟩

end CFSG.ComponentClassification.Foote5.Asc25
