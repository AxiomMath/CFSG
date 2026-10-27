module

public import CFSG.GF2Type.Smith1980Orth.FourOne
public import CFSG.GF2Type.Smith1980Orth.S3Bad
public import CFSG.LargeExtraspecial.S14SMJWeak

public section

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial

theorem coxeterA3_pow_four {G : Type*} [Group G] {a z y : G} (ha : a * a = 1) (hz : z * z = 1)
    (hy : y * y = 1) (haz : a * z = z * a) (hay : (a * y) ^ 3 = 1) (hzy : (z * y) ^ 3 = 1) :
    (a * z * y) ^ 4 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have b1 : a * y * a = y * a * y := by
    have h : a * y * a * (y * a * y) = 1 := by
      rw [show a * y * a * (y * a * y) = (a * y) ^ 3 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]; exact hay
    calc a * y * a = (y * a * y)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = y * a * y := by rw [mul_inv_rev, mul_inv_rev, ha', hy', mul_assoc]
  have b2 : z * y * z = y * z * y := by
    have h : z * y * z * (y * z * y) = 1 := by
      rw [show z * y * z * (y * z * y) = (z * y) ^ 3 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]; exact hzy
    calc z * y * z = (y * z * y)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = y * z * y := by rw [mul_inv_rev, mul_inv_rev, hz', hy', mul_assoc]
  have ha2 : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hz2 : ∀ x, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  have hy2 : ∀ x, y * (y * x) = x := fun x => by rw [← mul_assoc, hy, one_mul]
  have hza : ∀ x, z * (a * x) = a * (z * x) := fun x => by rw [← mul_assoc, ← haz, mul_assoc]
  have hsq : (a * z * y) ^ 2 = z * y * a * z * y * z := by
    have e1 : (a * z * y) ^ 2 = a * z * (y * a * y) * (y * z * y) := by
      rw [sq]; simp only [mul_assoc]; rw [hy2]
    rw [e1, ← b1, ← b2]
    simp only [mul_assoc]
    rw [hza, ha2]
  calc (a * z * y) ^ 4 = (z * y * a * z * y * z) * (z * y * a * z * y * z) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hsq]
    _ = 1 := by
        simp only [mul_assoc]
        rw [hz2, hy2, hza, hz2, ha2, hy2, hz]


theorem oe421Three_of_inputs {G : Type} [Group G] [Finite G] (S : Setting G)
    (hLoc0 : OLocal S) (hLoc : ∀ g : G, OLocal (S.conjBy g)) (h34a : OE34a S)
    (hLine : OE24Line S) (hbad : ∀ k : G, ¬ Bad S k) (h41 : FourOne S) : OE421Three S := by
  intro x w y hx hwc hy hxz hzw hwy hxw hzy hxy h3 h3'
  have hinv : ∀ {u : G}, IsConj S.z u → u * u = 1 :=
    fun hu => S14.SmithQ.mul_self_eq_one_of_isConj S hu
  have hz1 : IsConj S.z S.z := IsConj.refl _
  have ord4 : ∀ {u v : G}, IsConj S.z u → IsConj S.z v → ¬ Commute u v → (u * v) ^ 4 = 1 →
      orderOf (u * v) = 4 := by
    intro u v hu hv huv h4
    have hd : orderOf (u * v) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hmem : orderOf (u * v) ∈ ({1, 2, 3, 4} : Set ℕ) := by
      have hle : orderOf (u * v) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      have hpos : 0 < orderOf (u * v) := Nat.pos_of_dvd_of_pos hd (by norm_num)
      interval_cases h : orderOf (u * v) <;> simp_all
    rcases S14.SME.orderOf_eq_three_or_four S hu hv huv hmem with h | h
    · rw [h] at hd; norm_num at hd
    · exact h
  have hxQ : x ∉ S.QG := by
    intro hxQ
    have h4 := pow_four_of_mem_Qa' S h34a (k := 1) hx hwc (by simpa using hxQ)
      (by simpa using hzw)
    have hd : orderOf (x * w) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    rw [h3] at hd; norm_num at hd
  obtain ⟨kx, rfl⟩ := isConj_iff.mp hx
  have hxM : kx * S.z * kx⁻¹ ∈ S.M := Subgroup.mem_centralizer_singleton_iff.mpr hxz.eq
  obtain ⟨a, ha, haQ, haQx⟩ := exists_of_not_bad (hbad kx) hxM hxQ
  have hax : Commute a (kx * S.z * kx⁻¹) := by
    have := (S.conjBy kx).QG_le_M haQx
    exact (Subgroup.mem_centralizer_singleton_iff.mp this)
  have haz : Commute a S.z := (Subgroup.mem_centralizer_singleton_iff.mp (S.QG_le_M haQ))
  have hazne : a ≠ S.z := by
    rintro rfl
    have h1 : kx * S.z * kx⁻¹ ∈ S.Qa 1 := by
      refine Setting.mem_Qa_symm S (g₁ := 1) (g₂ := kx) ?_ (by simpa using haQx)
      intro h; apply hxQ; rw [← h]; simpa using S.z_mem_QG
    exact hxQ (by simpa [S14.SME.mem_Qa_iff] using h1)
  have hza : IsConj S.z (S.z * a) := S14.SMJ.isConj_z_mul S ha haQ hazne
  have hzax : Commute (S.z * a) (kx * S.z * kx⁻¹) := hxz.symm.mul_left hax
  by_cases hay : Commute a y
  · exact ⟨a, ha, hax.symm, hay⟩
  by_cases hzay : Commute (S.z * a) y
  · exact ⟨S.z * a, hza, hzax.symm, hzay⟩
  have haw : ¬ Commute a w := by
    intro haw
    obtain ⟨ka, rfl⟩ := isConj_iff.mp ha
    have hne : ka * S.z * ka⁻¹ ≠ kx * S.z * kx⁻¹ := fun h => hxQ (h ▸ haQ)
    have hxQa : kx * S.z * kx⁻¹ ∈ S.Qa ka := Setting.mem_Qa_symm S hne haQx
    have h4 := pow_four_of_mem_Qa' S h34a (k := ka) (isConj_iff.mpr ⟨kx, rfl⟩) hwc
      ((S14.SME.mem_Qa_iff S ka _).mp hxQa) haw
    have hd : orderOf (kx * S.z * kx⁻¹ * w) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    rw [h3] at hd; norm_num at hd
  have haw4 : orderOf (a * w) = 4 :=
    ord4 ha hwc haw (pow_four_of_mem_Qa' S h34a (k := 1) ha hwc (by simpa using haQ)
      (by simpa using hzw))
  have hzaz : S.z * a = a * S.z := haz.eq.symm
  obtain ⟨b, hb, hbx, hby, hby4⟩ : ∃ b, IsConj S.z b ∧ Commute b (kx * S.z * kx⁻¹) ∧
      ¬ Commute b y ∧ orderOf (b * y) = 4 := by
    by_cases h1 : orderOf (a * y) = 3
    · refine ⟨S.z * a, hza, hzax, hzay, ord4 hza hy hzay ?_⟩
      have := coxeterA3_pow_four (hinv ha) (hinv hz1) (hinv hy) haz.eq
        (by rw [← h1]; exact pow_orderOf_eq_one _) (by rw [← h3']; exact pow_orderOf_eq_one _)
      rwa [hzaz]
    by_cases h2 : orderOf (S.z * a * y) = 3
    · refine ⟨a, ha, hax, hay, ord4 ha hy hay ?_⟩
      have := coxeterA3_pow_four (a := S.z * a) (z := S.z) (y := y) (hinv hza) (hinv hz1)
        (hinv hy) (by rw [mul_assoc, ← hzaz])
        (by rw [← h2]; exact pow_orderOf_eq_one _) (by rw [← h3']; exact pow_orderOf_eq_one _)
      rwa [hzaz, mul_assoc a S.z S.z, hinv hz1, mul_one] at this
    · refine ⟨a, ha, hax, hay, ?_⟩
      obtain ⟨v, hv, hav, hvy⟩ := four_gen' S hLoc0 h34a hLine ha hz1 hwc hy haz hzw hwy haw haw4
      obtain ⟨g, rfl⟩ := isConj_iff.mp hv
      have hT := local_of_OLocal (S.conjBy g) (hLoc g) a y
        ((isConj_iff.mpr ⟨g, rfl⟩).symm.trans ha) ((isConj_iff.mpr ⟨g, rfl⟩).symm.trans hy)
        (Subgroup.mem_centralizer_singleton_iff.mpr hav.eq)
        (Subgroup.mem_centralizer_singleton_iff.mpr hvy.symm.eq)
      rcases S14.SME.orderOf_eq_three_or_four S ha hy hay hT.1 with h | h
      · exact absurd h h1
      · exact h
  have hc : IsConj S.z ((b * y) ^ 2) := (h41 b y hb hy (by rw [hby4])).2
  have hbb := hinv hb
  have hyy := hinv hy
  have hsq : (b * y) ^ 2 = (y * b) ^ 2 := by
    have h4 : (b * y) ^ 4 = 1 := by rw [← hby4]; exact pow_orderOf_eq_one _
    have hyb : y * b = (b * y)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hbb]
    rw [hyb, inv_pow]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h4)).symm
  have hcb : Commute ((b * y) ^ 2) b := by
    show (b * y) ^ 2 * b = b * (b * y) ^ 2
    calc (b * y) ^ 2 * b = (y * b) ^ 2 * b := by rw [hsq]
      _ = b * (b * y) ^ 2 := by
        simp only [sq, mul_assoc]
        rw [← mul_assoc b b, hbb, one_mul]
        try simp only [mul_one]
  have hcy : Commute y ((b * y) ^ 2) := by
    show y * (b * y) ^ 2 = (b * y) ^ 2 * y
    calc y * (b * y) ^ 2 = y * (y * b) ^ 2 := by rw [hsq]
      _ = (b * y) ^ 2 * y := by
        simp only [sq, mul_assoc]
        rw [← mul_assoc y y, hyy, one_mul]
        try simp only [mul_one]
  have hyb4 : orderOf (y * b) = 4 := by
    rw [show y * b = b⁻¹ * (b * y) * b by group, S14.SME.orderOf_conj_inv]
    exact hby4
  obtain ⟨v, hv, hyv, hvx⟩ := four_gen' S hLoc0 h34a hLine hy hc hb (isConj_iff.mpr ⟨kx, rfl⟩)
    hcy hcb hbx (fun h => hby h.symm) hyb4
  exact ⟨v, hv, hvx.symm, hyv.symm⟩

end CFSG.GF2Type.Smith1980Orth