module

public import CFSG.CGT.Foote81L6.Bridge.Model

public section

namespace CFSG.CGT.Foote81L6.Bridge

@[expose] def qr (n : ℕ) : ZMod (2 ^ n) := 2 ^ (n - 2)

theorem hf_eq_two_mul_qr (n : ℕ) : hf n = 2 * qr n := rfl

theorem four_mul_qr (n : ℕ) : 4 * qr n = 0 := by
  rw [show (4 : ZMod (2 ^ n)) = 2 * 2 by norm_num, mul_assoc, ← hf_eq_two_mul_qr, two_mul_hf]

theorem two_mul_qr_sq {n : ℕ} (hn : 3 ≤ n) : 2 * qr n ^ 2 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h : (2 : ZMod (2 ^ (m + 3))) * qr (m + 3) ^ 2 =
      ((2 ^ (m + 3) : ℕ) : ZMod (2 ^ (m + 3))) * 2 ^ m := by
    simp only [qr, show m + 3 - 2 = m + 1 by omega]
    push_cast
    ring
  rw [h, ZMod.natCast_self, zero_mul]

theorem par_qr {n : ℕ} (hn : 3 ≤ n) : par (qr n) = 0 := by
  rw [qr, show n - 2 = (n - 3) + 1 by omega, pow_succ', par_two_mul (by omega)]

theorem qr_eq {n : ℕ} : qr n = ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n)) := by
  rw [qr]
  push_cast
  rfl

theorem qr_ne_zero {n : ℕ} : qr n ≠ 0 ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inr rfl
  · left
    rw [qr_eq, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h1 := Nat.le_of_dvd (by positivity) h
    have h2 : 2 ^ (n - 2) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem qr_ne_hf {n : ℕ} (hn : 2 ≤ n) : qr n ≠ hf n := by
  rw [qr_eq, hf_eq hn, Ne, ZMod.natCast_eq_natCast_iff']
  have h1 : 2 ^ (n - 2) < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt (h1.trans h2), Nat.mod_eq_of_lt h2]
  omega

theorem mem_zpowers_of_mul_self_eq_one {G : Type*} [Group G] {g x : G} (hg : g * g = 1) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h2 : g ^ 2 = 1 := by rw [pow_two, hg]
    rw [zpow_eq_zpow_emod' k h2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

namespace SD

variable {n : ℕ}

theorem ω_ne_one (hn : 1 ≤ n) : (ω : SD n) ≠ 1 := by
  intro h
  have h1 := congrArg par (congrArg SD.i h)
  rw [show (ω : SD n).i = 1 from rfl, show (1 : SD n).i = 0 from rfl, par_one hn,
    par_zero] at h1
  exact one_ne_zero h1

theorem ω_ne_z (hn : 1 ≤ n) : (ω : SD n) ≠ z := by
  intro h
  have h1 := congrArg par (congrArg SD.i h)
  rw [show (ω : SD n).i = 1 from rfl, show (z : SD n).i = hf n from rfl, par_one hn,
    par_hf] at h1
  exact one_ne_zero h1

end SD

namespace PHat

variable {n : ℕ}

@[expose] def zF : PHat n := ⟨1, 1, SD.z, 0⟩

theorem det_zF : (zF : PHat n).det = 0 := by
  simp [det, zF, SD.det_z]

theorem zF_comm (a : PHat n) : a * zF = zF * a := by
  obtain ⟨a₁, a₂, a₃, ae⟩ := a
  rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
    ext <;> simp [zF, SD.z_comm]

theorem zF_mul_zF : (zF : PHat n) * zF = 1 := by
  ext <;> simp [zF, SD.z_mul_self]

theorem sw₁_of_eq {y : PHat n} (h : y.x₁ = y.x₂) (e : ZMod 2) : sw₁ e y = y.x₁ := by
  rcases zmod_two_eq_zero_or_one e with rfl | rfl
  · rfl
  · exact h.symm

theorem sw₂_of_eq {y : PHat n} (h : y.x₁ = y.x₂) (e : ZMod 2) : sw₂ e y = y.x₁ := by
  rcases zmod_two_eq_zero_or_one e with rfl | rfl
  · exact h.symm
  · rfl

end PHat

@[expose] def zP (n : ℕ) : P n := ⟨PHat.zF, mem_P.2 PHat.det_zF⟩

theorem coe_zP (n : ℕ) : (zP n : PHat n) = PHat.zF := rfl

theorem coe_cP (n : ℕ) : (cP n : PHat n) = PHat.c := rfl

theorem zP_mem_center (n : ℕ) : zP n ∈ Subgroup.center (P n) :=
  Subgroup.mem_center_iff.2 fun g => Subtype.ext (PHat.zF_comm (g : PHat n))

theorem zP_mul_zP (n : ℕ) : zP n * zP n = 1 :=
  Subtype.ext PHat.zF_mul_zF

theorem zP_ne_one {n : ℕ} (hn : 2 ≤ n) : zP n ≠ 1 := fun h =>
  SD.z_ne_one hn (congrArg PHat.x₃ (congrArg Subtype.val h))

theorem zP_ne_cP {n : ℕ} (hn : 2 ≤ n) : zP n ≠ cP n := fun h =>
  SD.z_ne_one hn (congrArg PHat.x₁ (congrArg Subtype.val h)).symm

@[expose] def zS (n : ℕ) : SModel n := QuotientGroup.mk (zP n)

theorem zS_mem_center (n : ℕ) : zS n ∈ Subgroup.center (SModel n) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [zS, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    (Subgroup.mem_center_iff.1 (zP_mem_center n) g)]

theorem zS_mul_zS (n : ℕ) : zS n * zS n = 1 := by
  rw [zS, ← QuotientGroup.mk_mul, zP_mul_zP, QuotientGroup.mk_one]

theorem zS_ne_one {n : ℕ} (hn : 2 ≤ n) : zS n ≠ 1 := by
  intro h
  rw [zS, ← QuotientGroup.mk_one, SModel.mk_eq_mk_iff] at h
  rcases h with h | h
  · exact zP_ne_one hn h.symm
  · exact zP_ne_cP hn (by
      rw [eq_inv_of_mul_eq_one_left h.symm, inv_eq_of_mul_eq_one_right (cP_mul_cP n)])

theorem orderOf_zS {n : ℕ} (hn : 2 ≤ n) : orderOf (zS n) = 2 :=
  orderOf_eq_prime (by rw [pow_two, zS_mul_zS]) (zS_ne_one hn)

instance zpowers_zS_normal (n : ℕ) : (Subgroup.zpowers (zS n)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 (zS_mem_center n))

theorem comm_or_comm_c {n : ℕ} {y : P n}
    (hy : (QuotientGroup.mk y : SModel n) ∈ Subgroup.center (SModel n)) (g : P n) :
    (y : PHat n) * (g : PHat n) = (g : PHat n) * (y : PHat n) ∨
      (y : PHat n) * (g : PHat n) = (g : PHat n) * (y : PHat n) * PHat.c := by
  have h := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk g)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, SModel.mk_eq_mk_iff] at h
  rcases h with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem center_SModel {n : ℕ} (hn : 3 ≤ n) :
    Subgroup.center (SModel n) = Subgroup.zpowers (zS n) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨y₁, y₂, y₃, ye⟩, hy⟩ := y
    have hcomm := comm_or_comm_c hx
    have hdetω : (SD.ω : SD n).det = 1 := SD.det_ω (by omega)
    let gτ : P n := ⟨⟨1, 1, 1, 1⟩, mem_P.2 (by simp [PHat.det])⟩
    let g₂ : P n := ⟨⟨SD.ω, 1, SD.ω, 0⟩, mem_P.2 (by
      change (SD.ω : SD n).det + (1 : SD n).det + (SD.ω : SD n).det = 0
      rw [hdetω, SD.det_one]; rfl)⟩
    let g₃ : P n := ⟨⟨SD.ω, SD.ω, 1, 0⟩, mem_P.2 (by
      change (SD.ω : SD n).det + (SD.ω : SD n).det + (1 : SD n).det = 0
      rw [hdetω, SD.det_one]; rfl)⟩
    let g₄ : P n := ⟨⟨SD.σ, SD.σ, 1, 0⟩, mem_P.2 (by
      change (SD.σ : SD n).det + (SD.σ : SD n).det + (1 : SD n).det = 0
      rw [SD.det_σ, SD.det_one]; rfl)⟩
    let g₅ : P n := ⟨⟨SD.σ, 1, SD.σ, 0⟩, mem_P.2 (by
      change (SD.σ : SD n).det + (1 : SD n).det + (SD.σ : SD n).det = 0
      rw [SD.det_σ, SD.det_one]; rfl)⟩
    have h12 : y₂ = y₁ := by
      rcases hcomm gτ with h | h
      · have h1 := congrArg PHat.x₁ h
        rcases zmod_two_eq_zero_or_one ye with rfl | rfl <;>
          simpa [gτ] using h1.symm
      · exfalso
        have h3 := congrArg PHat.x₃ h
        simp [gτ, PHat.c] at h3
        exact SD.z_ne_one (n := n) (by omega) h3
    subst h12
    have he : ye = 0 := by
      rcases zmod_two_eq_zero_or_one ye with h0 | h1
      · exact h0
      · exfalso
        subst h1
        rcases hcomm g₂ with h | h
        · have h1 := congrArg PHat.x₁ h
          simp [g₂] at h1
          exact SD.ω_ne_one (n := n) (by omega) h1
        · have h1 := congrArg PHat.x₁ h
          simp [g₂, PHat.c] at h1
          apply SD.ω_ne_z (n := n) (by omega)
          have h2 : SD.ω * SD.z * y₂ = y₂ := by
            rw [mul_assoc, ← SD.z_comm y₂, ← mul_assoc]
            exact h1.symm
          have h3 : SD.ω * SD.z = 1 := mul_eq_right.1 h2
          rw [← mul_one SD.ω, ← SD.z_mul_self, ← mul_assoc, h3, one_mul]
    subst he
    have hc1 : ∀ g : SD n, (g = SD.ω ∨ g = SD.σ) → y₂ * g = g * y₂ := by
      rintro g (rfl | rfl)
      · rcases hcomm g₃ with h | h
        · simpa [g₃] using congrArg PHat.x₁ h
        · exfalso
          have h3 := congrArg PHat.x₃ h
          simp [g₃, PHat.c] at h3
          exact SD.z_ne_one (n := n) (by omega) h3
      · rcases hcomm g₄ with h | h
        · simpa [g₄] using congrArg PHat.x₁ h
        · exfalso
          have h3 := congrArg PHat.x₃ h
          simp [g₄, PHat.c] at h3
          exact SD.z_ne_one (n := n) (by omega) h3
    have hc3 : ∀ g : SD n, (g = SD.ω ∨ g = SD.σ) → y₃ * g = g * y₃ := by
      rintro g (rfl | rfl)
      · rcases hcomm g₂ with h | h
        · simpa [g₂] using congrArg PHat.x₃ h
        · exfalso
          have h2 := congrArg PHat.x₂ h
          simp [g₂, PHat.c] at h2
          exact SD.z_ne_one (n := n) (by omega) h2
      · rcases hcomm g₅ with h | h
        · simpa [g₅] using congrArg PHat.x₃ h
        · exfalso
          have h2 := congrArg PHat.x₂ h
          simp [g₅, PHat.c] at h2
          exact SD.z_ne_one (n := n) (by omega) h2
    have hy₂ := SD.eq_one_or_eq_z_of_comm hn (hc1 _ (Or.inl rfl)) (hc1 _ (Or.inr rfl))
    have hy₃ := SD.eq_one_or_eq_z_of_comm hn (hc3 _ (Or.inl rfl)) (hc3 _ (Or.inr rfl))
    rw [mem_zpowers_of_mul_self_eq_one (zS_mul_zS n)]
    rcases hy₂ with rfl | rfl <;> rcases hy₃ with rfl | rfl
    · left
      exact (congrArg QuotientGroup.mk (Subtype.ext rfl : (⟨⟨1, 1, 1, 0⟩, hy⟩ : P n) = 1)).trans
        (QuotientGroup.mk_one _)
    · right
      rfl
    · right
      rw [zS, SModel.mk_eq_mk_iff]
      right
      apply Subtype.ext
      ext1 <;> simp [coe_zP, coe_cP, PHat.zF, PHat.c, SD.z_mul_self]
    · left
      rw [← QuotientGroup.mk_one, SModel.mk_eq_mk_iff]
      right
      apply Subtype.ext
      ext1 <;> simp [coe_cP, PHat.c, SD.z_mul_self]
  · exact Subgroup.zpowers_le.2 (zS_mem_center n)

abbrev TM (n : ℕ) : Type := SModel n ⧸ Subgroup.zpowers (zS n)

@[expose] def πT (n : ℕ) : P n →* TM n :=
  (QuotientGroup.mk' (Subgroup.zpowers (zS n))).comp (QuotientGroup.mk' (Subgroup.zpowers (cP n)))

theorem πT_apply {n : ℕ} (y : P n) :
    πT n y = ((QuotientGroup.mk (QuotientGroup.mk y : SModel n)) : TM n) := rfl

theorem πT_eq_one_iff {n : ℕ} (y : P n) :
    πT n y = 1 ↔ y = 1 ∨ y = cP n ∨ y = zP n ∨ y = cP n * zP n := by
  have hcc := cP_mul_cP n
  have hcz : cP n * zP n = zP n * cP n :=
    (Subgroup.mem_center_iff.1 (cP_mem_center n) (zP n)).symm
  rw [πT_apply, QuotientGroup.eq_one_iff, mem_zpowers_of_mul_self_eq_one (zS_mul_zS n),
    ← QuotientGroup.mk_one, zS, SModel.mk_eq_mk_iff, SModel.mk_eq_mk_iff]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h.symm
    · right; left
      calc y = y * cP n * cP n := by rw [mul_assoc, hcc, mul_one]
        _ = cP n := by rw [← h, one_mul]
    · right; right; left
      exact h.symm
    · right; right; right
      calc y = y * cP n * cP n := by rw [mul_assoc, hcc, mul_one]
        _ = zP n * cP n := by rw [← h]
        _ = cP n * zP n := hcz.symm
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr hcc.symm)
    · exact Or.inr (Or.inl rfl)
    · right; right
      rw [hcz, mul_assoc, hcc, mul_one]

theorem πT_eq_iff {n : ℕ} (y y' : P n) :
    πT n y = πT n y' ↔
      ∃ ν : P n, (ν = 1 ∨ ν = cP n ∨ ν = zP n ∨ ν = cP n * zP n) ∧ y' = y * ν := by
  constructor
  · intro h
    refine ⟨y⁻¹ * y', (πT_eq_one_iff _).1 ?_, by rw [mul_inv_cancel_left]⟩
    rw [map_mul, map_inv, h, inv_mul_cancel]
  · rintro ⟨ν, hν, rfl⟩
    rw [map_mul, (πT_eq_one_iff ν).2 hν, mul_one]

theorem card_TM {n : ℕ} (hn : 2 ≤ n) : Nat.card (TM n) = 2 ^ (3 * n + 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (zS n))
  rw [Nat.card_zpowers, orderOf_zS hn, card_SModel hn, show 3 * n + 2 = (3 * n + 1) + 1 by ring,
    pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

@[expose] def liftT {n : ℕ} {M : Type*} [Group M] (f : P n →* M) (hc : f (cP n) = 1)
    (hz : f (zP n) = 1) : TM n →* M :=
  QuotientGroup.lift _
    (QuotientGroup.lift _ f (Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 hc)))
    (Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 hz))

@[expose] def PHat.eHom {n : ℕ} : PHat n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd a.e
  map_one' := rfl
  map_mul' a b := by rw [PHat.mul_e, ofAdd_add]

@[expose] def PHat.jHom {n : ℕ} : PHat n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd (a.x₁.j + a.x₂.j)
  map_one' := by simp
  map_mul' a b := by
    obtain ⟨a₁, a₂, a₃, ae⟩ := a
    rw [← ofAdd_add]
    congr 1
    rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
      · simp only [PHat.mul_x₁, PHat.mul_x₂, SD.mul_j, PHat.sw₁_zero, PHat.sw₂_zero,
          PHat.sw₁_one, PHat.sw₂_one]
        ring

@[expose] def PHat.j3Hom {n : ℕ} : PHat n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd a.x₃.j
  map_one' := rfl
  map_mul' a b := by rw [PHat.mul_x₃, SD.mul_j, ofAdd_add]

@[expose] def PHat.d3Hom {n : ℕ} : PHat n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd a.x₃.det
  map_one' := by simp
  map_mul' a b := by rw [PHat.mul_x₃, SD.det_mul, ofAdd_add]

@[expose] def eT (n : ℕ) : TM n →* Multiplicative (ZMod 2) :=
  liftT (PHat.eHom.comp (P n).subtype) rfl rfl

@[expose] def jT (n : ℕ) : TM n →* Multiplicative (ZMod 2) :=
  liftT (PHat.jHom.comp (P n).subtype) (by simp [PHat.jHom, coe_cP, PHat.c, SD.z])
    (by simp [PHat.jHom, coe_zP, PHat.zF])

@[expose] def j3T (n : ℕ) : TM n →* Multiplicative (ZMod 2) :=
  liftT (PHat.j3Hom.comp (P n).subtype) rfl rfl

@[expose] def d3T (n : ℕ) : TM n →* Multiplicative (ZMod 2) :=
  liftT (PHat.d3Hom.comp (P n).subtype)
    (by simp [PHat.d3Hom, coe_cP, PHat.c, SD.det_z])
    (by simp [PHat.d3Hom, coe_zP, PHat.zF, SD.det_z])

theorem eT_πT {n : ℕ} (y : P n) : eT n (πT n y) = Multiplicative.ofAdd (y : PHat n).e := rfl

theorem jT_πT {n : ℕ} (y : P n) :
    jT n (πT n y) = Multiplicative.ofAdd ((y : PHat n).x₁.j + (y : PHat n).x₂.j) := rfl

theorem j3T_πT {n : ℕ} (y : P n) : j3T n (πT n y) = Multiplicative.ofAdd (y : PHat n).x₃.j := rfl

theorem d3T_πT {n : ℕ} (y : P n) : d3T n (πT n y) = Multiplicative.ofAdd (y : PHat n).x₃.det :=
  rfl

@[expose] def Atil (n : ℕ) : Subgroup (P n) where
  carrier := {y | (y : PHat n).x₁ = 1 ∧ (y : PHat n).x₂ = 1 ∧ (y : PHat n).e = 0}
  one_mem' := ⟨rfl, rfl, rfl⟩
  mul_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, PHat.mul_x₁, ha1, ha3, PHat.sw₁_zero, hb1, mul_one]
    · rw [Subgroup.coe_mul, PHat.mul_x₂, ha2, ha3, PHat.sw₂_zero, hb2, mul_one]
    · rw [Subgroup.coe_mul, PHat.mul_e, ha3, hb3, add_zero]
  inv_mem' {a} ha := by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.coe_inv, PHat.inv_x₁, ha3, PHat.sw₁_zero, ha1, inv_one]
    · rw [Subgroup.coe_inv, PHat.inv_x₂, ha3, PHat.sw₂_zero, ha2, inv_one]
    · rw [Subgroup.coe_inv, PHat.inv_e, ha3]

@[expose] def Btil (n : ℕ) : Subgroup (P n) where
  carrier := {y | (y : PHat n).x₃ = 1}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    change (a : PHat n).x₃ * (b : PHat n).x₃ = 1
    rw [ha, hb, mul_one]
  inv_mem' {a} ha := by
    change (a : PHat n).x₃⁻¹ = 1
    rw [ha, inv_one]

theorem mem_Atil {n : ℕ} {y : P n} :
    y ∈ Atil n ↔ (y : PHat n).x₁ = 1 ∧ (y : PHat n).x₂ = 1 ∧ (y : PHat n).e = 0 := Iff.rfl

theorem mem_Btil {n : ℕ} {y : P n} : y ∈ Btil n ↔ (y : PHat n).x₃ = 1 := Iff.rfl

theorem Atil_comm_Btil {n : ℕ} {y y' : P n} (hy : y ∈ Atil n) (hy' : y' ∈ Btil n) :
    y * y' = y' * y := by
  obtain ⟨h1, h2, h3⟩ := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  ext1
  · rw [PHat.mul_x₁, PHat.mul_x₁, h1, h3, PHat.sw₁_zero, one_mul, PHat.sw₁_of_eq (by rw [h1, h2]),
      h1, mul_one]
  · rw [PHat.mul_x₂, PHat.mul_x₂, h2, h3, PHat.sw₂_zero, one_mul, PHat.sw₂_of_eq (by rw [h1, h2]),
      h1, mul_one]
  · rw [PHat.mul_x₃, PHat.mul_x₃, mem_Btil.1 hy', one_mul, mul_one]
  · rw [PHat.mul_e, PHat.mul_e, add_comm]

theorem inf_map_Atil_Btil {n : ℕ} (hn : 2 ≤ n) :
    (Atil n).map (πT n) ⊓ (Btil n).map (πT n) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨y, hy, rfl⟩, ⟨y', hy', hyy'⟩⟩
  rw [Subgroup.mem_bot]
  obtain ⟨ν, hν, hν'⟩ := (πT_eq_iff y y').1 hyy'.symm
  have h3 := congrArg PHat.x₃ (congrArg Subtype.val hν')
  rw [Subgroup.coe_mul, PHat.mul_x₃, mem_Btil.1 hy'] at h3
  obtain ⟨h1, h2, he⟩ := hy
  rw [πT_eq_one_iff]
  rcases hν with rfl | rfl | rfl | rfl
  · left
    have h : (y : PHat n).x₃ = 1 := by simpa using h3.symm
    apply Subtype.ext
    ext1 <;> simp [h1, h2, he, h]
  · right; right; left
    have h : (y : PHat n).x₃ = SD.z := by
      have := h3.symm
      simp only [coe_cP, PHat.c] at this
      calc (y : PHat n).x₃ = (y : PHat n).x₃ * SD.z * SD.z := by
            rw [mul_assoc, SD.z_mul_self, mul_one]
        _ = SD.z := by rw [this, one_mul]
    apply Subtype.ext
    ext1 <;> simp [h1, h2, he, h, coe_zP, PHat.zF]
  · right; right; left
    have h : (y : PHat n).x₃ = SD.z := by
      have := h3.symm
      simp only [coe_zP, PHat.zF] at this
      calc (y : PHat n).x₃ = (y : PHat n).x₃ * SD.z * SD.z := by
            rw [mul_assoc, SD.z_mul_self, mul_one]
        _ = SD.z := by rw [this, one_mul]
    apply Subtype.ext
    ext1 <;> simp [h1, h2, he, h, coe_zP, PHat.zF]
  · left
    have h : (y : PHat n).x₃ = 1 := by
      have := h3.symm
      simp only [Subgroup.coe_mul, coe_cP, coe_zP, PHat.c, PHat.zF, PHat.mul_x₃,
        SD.z_mul_self] at this
      simpa using this
    apply Subtype.ext
    ext1 <;> simp [h1, h2, he, h]

end CFSG.CGT.Foote81L6.Bridge
