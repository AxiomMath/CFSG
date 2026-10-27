module

public import CFSG.CGT.Foote81L6.Bridge.FooteModel

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

theorem mul_mul_mul_self_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [h]
    _ = a * a * (b * b) := by group

namespace Gen

variable {n : ℕ} (hn : 3 ≤ n)
include hn

theorem cz_mul_cz : cz n * cz n = 1 := by
  ext <;> simp [cz, SD.z_mul_self]

theorem cz_pow_qr : cz n ^ 2 ^ (n - 2) = 1 := by
  rw [show 2 ^ (n - 2) = 2 * 2 ^ (n - 3) by rw [← pow_succ']; congr 1; omega, pow_mul, pow_two,
    cz_mul_cz hn, one_pow]

omit hn in
theorem zF_mul_cz : PHat.zF * cz n = PHat.c := by
  rw [cz_eq, ← mul_assoc, ← PHat.zF_comm PHat.c, mul_assoc, PHat.zF_mul_zF, mul_one]

omit hn in
theorem sq_of_semiconj {G : Type*} [Group G] {w u c : G} (h : w * u = u⁻¹ * w)
    (hw : w * w = c) (hc : ∀ g : G, g * c = c * g) (k : ℕ) :
    (w * u ^ k) * (w * u ^ k) = c := by
  have h1 : w * u ^ k = (u⁻¹) ^ k * w := (show SemiconjBy w u u⁻¹ from h).pow_right k
  calc w * u ^ k * (w * u ^ k) = (w * u ^ k) * w * u ^ k := by group
    _ = (u⁻¹) ^ k * (w * w) * u ^ k := by rw [h1]; group
    _ = c := by rw [hw, hc, mul_assoc, inv_pow, inv_mul_cancel, mul_one]

theorem sA_rA_pow_sq (k : ℕ) : (sA n * rA n ^ k) * (sA n * rA n ^ k) = PHat.zF :=
  sq_of_semiconj (sA_mul_rA hn) (sA_mul_sA hn) PHat.zF_comm k

theorem κ₀_ρ₀_pow_sq (k : ℕ) : (κ₀ n * ρ₀ n ^ k) * (κ₀ n * ρ₀ n ^ k) = cz n :=
  sq_of_semiconj (κ₀_mul_ρ₀ hn) (κ₀_mul_κ₀ hn) cz_comm k

theorem κ₁_ρ₁_pow_sq (k : ℕ) : (κ₁ n * ρ₁ n ^ k) * (κ₁ n * ρ₁ n ^ k) = cz n :=
  sq_of_semiconj (κ₁_mul_ρ₁ hn) (κ₁_mul_κ₁ hn) cz_comm k

theorem b₀H_sq : b₀H n * b₀H n = cz n := by
  rw [← ρ₀_pow_qr hn, ← pow_add, ← two_mul, ← pow_succ', show n - 2 + 1 = n - 1 by omega,
    ρ₀_pow_hf hn]

theorem b₁H_sq : b₁H n * b₁H n = cz n := by
  rw [← ρ₁_pow_qr hn, ← pow_add, ← two_mul, ← pow_succ', show n - 2 + 1 = n - 1 by omega,
    ρ₁_pow_hf hn]

theorem aH_sq : aH n * aH n = PHat.zF := by
  rw [← ωt_pow_qr hn, ← pow_add, ← two_mul, ← pow_succ', show n - 2 + 1 = n - 1 by omega,
    ωt_pow_hf hn]

omit hn in
theorem mul_pow_of_mul_eq {G : Type*} [Group G] {x y c : G} (h : x * y = y * x * c)
    (hc : ∀ g : G, g * c = c * g) (k : ℕ) : x * y ^ k = y ^ k * x * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x * y ^ (k + 1) = x * y ^ k * y := by rw [pow_succ, mul_assoc]
      _ = y ^ k * x * (c ^ k * y) := by rw [ih]; group
      _ = y ^ k * (x * y) * c ^ k := by rw [(Commute.pow_left (hc y).symm k).eq]; group
      _ = y ^ (k + 1) * x * c ^ (k + 1) := by rw [h, pow_succ, pow_succ]; group

omit hn in
theorem pow_mul_of_mul_eq {G : Type*} [Group G] {x y c : G} (h : x * y = y * x * c)
    (hc : ∀ g : G, g * c = c * g) (k : ℕ) : x ^ k * y = y * x ^ k * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * y = x ^ k * (x * y) := by rw [pow_succ, mul_assoc]
      _ = x ^ k * y * x * c := by rw [h]; group
      _ = y * x ^ k * (c ^ k * x) * c := by rw [ih]; group
      _ = y * x ^ (k + 1) * c ^ (k + 1) := by
          rw [(Commute.pow_left (hc x).symm k).eq, pow_succ, pow_succ]; group

theorem commute_b₀H_b₁H : Commute (b₀H n) (b₁H n) := by
  rw [← ρ₀_pow_qr hn, ← ρ₁_pow_qr hn]
  exact (show Commute (ρ₀ n) (ρ₁ n) from ρ₀_mul_ρ₁ hn).pow_pow _ _

theorem commute_κ₀_ρ₀_pow_b₁H (k : ℕ) : Commute (κ₀ n * ρ₀ n ^ k) (b₁H n) := by
  have h1 : Commute (κ₀ n) (b₁H n) := by
    rw [Commute, SemiconjBy, ← ρ₁_pow_qr hn, mul_pow_of_mul_eq (κ₀_mul_ρ₁ hn) cz_comm,
      cz_pow_qr hn, mul_one]
  have h2 : Commute (ρ₀ n) (b₁H n) := by
    rw [← ρ₁_pow_qr hn]
    exact (show Commute (ρ₀ n) (ρ₁ n) from ρ₀_mul_ρ₁ hn).pow_right _
  exact h1.mul_left (h2.pow_left k)

theorem commute_κ₀ρ₀_κ₁ρ₁ (k : ℕ) : Commute (κ₀ n * ρ₀ n ^ k) (κ₁ n * ρ₁ n ^ k) := by
  have hczk : cz n ^ k * cz n ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pow_two, cz_mul_cz hn, one_pow]
  have hcz : ∀ g : PHat n, g * cz n ^ k = cz n ^ k * g := fun g =>
    (Commute.pow_right (cz_comm g) k).eq
  have h1 : ρ₀ n ^ k * κ₁ n = κ₁ n * ρ₀ n ^ k * cz n ^ k :=
    pow_mul_of_mul_eq (ρ₀_mul_κ₁ hn) cz_comm k
  have h2 : ρ₁ n ^ k * κ₀ n = κ₀ n * ρ₁ n ^ k * cz n ^ k := by
    rw [mul_pow_of_mul_eq (κ₀_mul_ρ₁ hn) cz_comm k, mul_assoc, hczk, mul_one]
  have h3 : ρ₀ n ^ k * ρ₁ n ^ k = ρ₁ n ^ k * ρ₀ n ^ k :=
    ((show Commute (ρ₀ n) (ρ₁ n) from ρ₀_mul_ρ₁ hn).pow_pow k k).eq
  have h4 := κ₀_mul_κ₁ hn
  have hUV : κ₀ n * ρ₀ n ^ k * (κ₁ n * ρ₁ n ^ k) =
      κ₀ n * κ₁ n * (ρ₀ n ^ k * ρ₁ n ^ k) * cz n ^ k := by
    calc κ₀ n * ρ₀ n ^ k * (κ₁ n * ρ₁ n ^ k) = κ₀ n * (ρ₀ n ^ k * κ₁ n) * ρ₁ n ^ k := by group
      _ = κ₀ n * κ₁ n * ρ₀ n ^ k * (cz n ^ k * ρ₁ n ^ k) := by rw [h1]; group
      _ = κ₀ n * κ₁ n * (ρ₀ n ^ k * ρ₁ n ^ k) * cz n ^ k := by rw [← hcz]; group
  have hVU : κ₁ n * ρ₁ n ^ k * (κ₀ n * ρ₀ n ^ k) =
      κ₀ n * κ₁ n * (ρ₀ n ^ k * ρ₁ n ^ k) * cz n ^ k := by
    calc κ₁ n * ρ₁ n ^ k * (κ₀ n * ρ₀ n ^ k) = κ₁ n * (ρ₁ n ^ k * κ₀ n) * ρ₀ n ^ k := by group
      _ = κ₁ n * κ₀ n * ρ₁ n ^ k * (cz n ^ k * ρ₀ n ^ k) := by rw [h2]; group
      _ = κ₁ n * κ₀ n * (ρ₁ n ^ k * ρ₀ n ^ k) * cz n ^ k := by rw [← hcz]; group
      _ = κ₀ n * κ₁ n * (ρ₀ n ^ k * ρ₁ n ^ k) * cz n ^ k := by rw [h4, h3]
  rw [Commute, SemiconjBy, hUV, hVU]

end Gen

variable {n : ℕ}

@[expose] def LiftsSqZ (x : TM n) : Prop :=
  ∀ y : SModel n, (QuotientGroup.mk y : TM n) = x → y ^ 2 = zS n

@[expose] def LiftsSq1 (x : TM n) : Prop :=
  ∀ y : SModel n, (QuotientGroup.mk y : TM n) = x → y ^ 2 = 1

theorem sq_eq_of_πT_eq {p p' : P n} (h : πT n p' = πT n p) : p' * p' = p * p := by
  obtain ⟨ν, hν, rfl⟩ := (πT_eq_iff p p').1 h.symm
  have hcen : ∀ g : P n, g * ν = ν * g := by
    have hc := cP_mem_center n
    have hz := zP_mem_center n
    rcases hν with rfl | rfl | rfl | rfl
    · intro g; simp
    · exact fun g => Subgroup.mem_center_iff.1 hc g
    · exact fun g => Subgroup.mem_center_iff.1 hz g
    · exact fun g => Subgroup.mem_center_iff.1 (Subgroup.mul_mem _ hc hz) g
  have hsq : ν * ν = 1 := by
    rcases hν with rfl | rfl | rfl | rfl
    · simp
    · exact cP_mul_cP n
    · exact zP_mul_zP n
    · rw [mul_mul_mul_self_of_comm (Subgroup.mem_center_iff.1 (zP_mem_center n) (cP n)),
        cP_mul_cP, zP_mul_zP, one_mul]
  rw [mul_mul_mul_self_of_comm (hcen p), hsq, mul_one]

theorem liftsSqZ_of {p : P n}
    (hp : (p : PHat n) * (p : PHat n) = (PHat.zF : PHat n) ∨
      (p : PHat n) * (p : PHat n) = Gen.cz n) :
    LiftsSqZ (πT n p) := by
  intro y hy
  obtain ⟨p', rfl⟩ := QuotientGroup.mk_surjective y
  rw [pow_two, ← QuotientGroup.mk_mul, sq_eq_of_πT_eq (show πT n p' = πT n p from hy)]
  rcases hp with hp | hp
  · rw [show p * p = zP n from Subtype.ext hp]
    rfl
  · rw [show p * p = cP n * zP n from Subtype.ext (by
      rw [Subgroup.coe_mul, hp, Subgroup.coe_mul, coe_cP, coe_zP, Gen.cz_eq]),
      QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (cP n)).2 (mem_zpowers _), one_mul]
    rfl

theorem liftsSq1_of {p : P n}
    (hp : (p : PHat n) * (p : PHat n) = 1 ∨ (p : PHat n) * (p : PHat n) = (PHat.c : PHat n)) :
    LiftsSq1 (πT n p) := by
  intro y hy
  obtain ⟨p', rfl⟩ := QuotientGroup.mk_surjective y
  rw [pow_two, ← QuotientGroup.mk_mul, sq_eq_of_πT_eq (show πT n p' = πT n p from hy)]
  rcases hp with hp | hp
  · rw [show p * p = 1 from Subtype.ext hp, QuotientGroup.mk_one]
  · rw [show p * p = cP n from Subtype.ext hp]
    exact (QuotientGroup.eq_one_iff (cP n)).2 (mem_zpowers _)

theorem coe_comm_of_mem_Atil_Btil {y y' : P n} (hy : y ∈ Atil n) (hy' : y' ∈ Btil n) :
    (y : PHat n) * (y' : PHat n) = (y' : PHat n) * (y : PHat n) :=
  congrArg (fun w : P n => (w : PHat n)) (Atil_comm_Btil hy hy')

variable (hn : 3 ≤ n)
include hn

theorem inv_AT_cases {x : TM n} (hx : x ∈ AT hn) (hx2 : orderOf x = 2) :
    x = aT n ∨ ∃ k : ℕ, x = sAT n * rAT n ^ k := by
  obtain ⟨d, rfl⟩ := hx
  have hd : orderOf d = 2 := by rwa [orderOf_injective _ (fA_injective hn)] at hx2
  rcases eq_zc_or_sr_of_orderOf_eq_two (by omega) hd with rfl | ⟨i, rfl⟩
  · exact Or.inl (aT_eq_fA hn).symm
  · exact Or.inr ⟨i.val, rfl⟩

theorem inv_B₀T_cases {r : TM n} (hr : r ∈ B₀T hn) (hr2 : orderOf r = 2) :
    r = b₀T hn ∨ ∃ k : ℕ, r = κ₀T n * ρ₀T n ^ k := by
  obtain ⟨d, rfl⟩ := hr
  have hd : orderOf d = 2 := by rwa [orderOf_injective _ (f₀_injective hn)] at hr2
  rcases eq_zc_or_sr_of_orderOf_eq_two (by omega) hd with rfl | ⟨i, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i.val, rfl⟩

theorem sA_rA_lift (k : ℕ) :
    sAT n * rAT n ^ k = πT n (toP (Gen.sA n) * toP (Gen.rA n) ^ k) ∧
      toP (Gen.sA n) * toP (Gen.rA n) ^ k ∈ Atil n ∧
      ((toP (Gen.sA n) * toP (Gen.rA n) ^ k : P n) : PHat n) = Gen.sA n * Gen.rA n ^ k := by
  refine ⟨by rw [map_mul, map_pow]; rfl, mul_mem ?_ (pow_mem ?_ _), ?_⟩
  · exact mem_Atil.2 (by rw [coe_toP (Gen.det_sA (n := n) (by omega))]; exact ⟨rfl, rfl, rfl⟩)
  · exact mem_Atil.2 (by rw [coe_toP Gen.det_rA]; exact ⟨rfl, rfl, rfl⟩)
  · rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP (Gen.det_sA (n := n) (by omega)),
      coe_toP Gen.det_rA]

theorem B₀_lift {r : TM n} (hr : r ∈ B₀T hn) (hr2 : orderOf r = 2) :
    ∃ R : P n, r = πT n R ∧ R ∈ Btil n ∧ (R : PHat n) * R = Gen.cz n ∧
      (R : PHat n) * Gen.b₁H n = Gen.b₁H n * R ∧
      (∃ R' : P n, tT n * r * (tT n)⁻¹ = πT n R' ∧ R' ∈ Btil n ∧ (R' : PHat n) * R' = Gen.cz n ∧
        (R : PHat n) * R' = R' * R) := by
  rcases inv_B₀T_cases hn hr hr2 with rfl | ⟨k, rfl⟩
  · refine ⟨toP (Gen.b₀H n), b₀T_eq' hn, mem_Btil.2 (by rw [coe_toP Gen.det_b₀H]; rfl), ?_, ?_,
      toP (Gen.b₁H n), ?_, mem_Btil.2 (by rw [coe_toP Gen.det_b₁H]; rfl), ?_, ?_⟩
    · rw [coe_toP Gen.det_b₀H, Gen.b₀H_sq hn]
    · rw [coe_toP Gen.det_b₀H]; exact (Gen.commute_b₀H_b₁H hn).eq
    · rw [← b₁T_eq' hn, b₀T_eq hn, b₁T_eq hn, ← conj_pow, tT_conj_ρ₀T hn]
    · rw [coe_toP Gen.det_b₁H, Gen.b₁H_sq hn]
    · rw [coe_toP Gen.det_b₀H, coe_toP Gen.det_b₁H]; exact (Gen.commute_b₀H_b₁H hn).eq
  · refine ⟨toP (Gen.κ₀ n) * toP (Gen.ρ₀ n) ^ k, by rw [map_mul, map_pow]; rfl,
      mul_mem (mem_Btil.2 (by rw [coe_toP Gen.det_κ₀]; rfl))
        (pow_mem (mem_Btil.2 (by rw [coe_toP Gen.det_ρ₀]; rfl)) _), ?_, ?_,
      toP (Gen.κ₁ n) * toP (Gen.ρ₁ n) ^ k, ?_,
      mul_mem (mem_Btil.2 (by rw [coe_toP Gen.det_κ₁]; rfl))
        (pow_mem (mem_Btil.2 (by rw [coe_toP Gen.det_ρ₁]; rfl)) _), ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP Gen.det_κ₀, coe_toP Gen.det_ρ₀,
        Gen.κ₀_ρ₀_pow_sq hn]
    · rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP Gen.det_κ₀, coe_toP Gen.det_ρ₀]
      exact (Gen.commute_κ₀_ρ₀_pow_b₁H hn k).eq
    · rw [map_mul, map_pow, show tT n * (κ₀T n * ρ₀T n ^ k) * (tT n)⁻¹ =
        (tT n * κ₀T n * (tT n)⁻¹) * (tT n * ρ₀T n * (tT n)⁻¹) ^ k by rw [conj_pow]; group,
        tT_conj_κ₀T hn, tT_conj_ρ₀T hn]
      rfl
    · rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP Gen.det_κ₁, coe_toP Gen.det_ρ₁,
        Gen.κ₁_ρ₁_pow_sq hn]
    · rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_pow,
        coe_toP Gen.det_κ₀, coe_toP Gen.det_ρ₀, coe_toP Gen.det_κ₁, coe_toP Gen.det_ρ₁]
      exact (Gen.commute_κ₀ρ₀_κ₁ρ₁ hn k).eq

theorem lifts_A : ∀ x ∈ AT hn, orderOf x = 2 → LiftsSqZ x := by
  intro x hx hx2
  rcases inv_AT_cases hn hx hx2 with rfl | ⟨k, rfl⟩
  · exact liftsSqZ_of (Or.inl (by rw [coe_toP (Gen.det_aH hn), Gen.aH_sq hn]))
  · obtain ⟨h1, -, h3⟩ := sA_rA_lift hn k
    rw [h1]
    exact liftsSqZ_of (Or.inl (by rw [h3, Gen.sA_rA_pow_sq hn]))

theorem lifts_i : ∀ x ∈ AT hn, orderOf x = 2 → x ≠ aT n → ∀ r ∈ B₀T hn, orderOf r = 2 →
    LiftsSq1 (x * r) := by
  intro x hx hx2 hxa r hr hr2
  obtain ⟨k, rfl⟩ := (inv_AT_cases hn hx hx2).resolve_left hxa
  obtain ⟨h1, hX, h3⟩ := sA_rA_lift hn k
  obtain ⟨R, rfl, hR, hR2, -, -⟩ := B₀_lift hn hr hr2
  rw [h1, ← map_mul]
  refine liftsSq1_of (Or.inr ?_)
  rw [Subgroup.coe_mul, mul_mul_mul_self_of_comm (coe_comm_of_mem_Atil_Btil hX hR),
    h3, Gen.sA_rA_pow_sq hn, hR2, Gen.zF_mul_cz]

theorem lifts_ii : ∀ r ∈ B₀T hn, orderOf r = 2 → LiftsSq1 (r * b₁T hn) := by
  intro r hr hr2
  obtain ⟨R, rfl, -, hR2, hRb, -⟩ := B₀_lift hn hr hr2
  rw [b₁T_eq' hn, ← map_mul]
  refine liftsSq1_of (Or.inl ?_)
  rw [Subgroup.coe_mul, coe_toP Gen.det_b₁H, mul_mul_mul_self_of_comm hRb, hR2,
    Gen.b₁H_sq hn, Gen.cz_mul_cz hn]

theorem lifts_iv : ∀ x ∈ AT hn, orderOf x = 2 → x ≠ aT n → ∀ r ∈ B₀T hn, orderOf r = 2 →
    LiftsSqZ (x * r * b₁T hn) ∧ LiftsSq1 (x * b₀T hn) := by
  intro x hx hx2 hxa r hr hr2
  obtain ⟨k, rfl⟩ := (inv_AT_cases hn hx hx2).resolve_left hxa
  obtain ⟨h1, hX, h3⟩ := sA_rA_lift hn k
  obtain ⟨R, rfl, hR, hR2, hRb, -⟩ := B₀_lift hn hr hr2
  have hb₁ : toP (Gen.b₁H n) ∈ Btil n := mem_Btil.2 (by rw [coe_toP Gen.det_b₁H]; rfl)
  have hb₀ : toP (Gen.b₀H n) ∈ Btil n := mem_Btil.2 (by rw [coe_toP Gen.det_b₀H]; rfl)
  constructor
  · rw [h1, b₁T_eq' hn, ← map_mul, ← map_mul, mul_assoc]
    refine liftsSqZ_of (Or.inl ?_)
    rw [Subgroup.coe_mul, mul_mul_mul_self_of_comm
      (coe_comm_of_mem_Atil_Btil hX (mul_mem hR hb₁)), h3, Gen.sA_rA_pow_sq hn, Subgroup.coe_mul,
      coe_toP Gen.det_b₁H, mul_mul_mul_self_of_comm hRb, hR2, Gen.b₁H_sq hn, Gen.cz_mul_cz hn,
      mul_one]
  · rw [h1, b₀T_eq' hn, ← map_mul]
    refine liftsSq1_of (Or.inr ?_)
    rw [Subgroup.coe_mul, mul_mul_mul_self_of_comm (coe_comm_of_mem_Atil_Btil hX hb₀),
      h3, Gen.sA_rA_pow_sq hn, coe_toP Gen.det_b₀H, Gen.b₀H_sq hn, Gen.zF_mul_cz]

theorem lifts_v : ∀ r ∈ B₀T hn, orderOf r = 2 → LiftsSq1 (r * (tT n * r * (tT n)⁻¹)) := by
  intro r hr hr2
  obtain ⟨R, rfl, -, hR2, -, R', hR', -, hR'2, hRR'⟩ := B₀_lift hn hr hr2
  rw [hR', ← map_mul]
  refine liftsSq1_of (Or.inl ?_)
  rw [Subgroup.coe_mul, mul_mul_mul_self_of_comm hRR', hR2, hR'2, Gen.cz_mul_cz hn]

@[expose] noncomputable def bT : TM n := b₀T hn * b₁T hn

theorem bT_mem_BT : bT hn ∈ BT hn :=
  mul_mem (B₀T_le_BT hn (b₀T_mem hn)) (B₁T_le_BT hn (b₁T_mem hn))

theorem bT_mul_bT : bT hn * bT hn = 1 := by
  have hb : b₀T hn * b₁T hn = b₁T hn * b₀T hn :=
    B₀T_comm_B₁T hn _ (b₀T_mem hn) _ (b₁T_mem hn)
  rw [bT, mul_mul_mul_self_of_comm hb, b₀T_mul_b₀T hn, b₁T_mul_b₁T hn, one_mul]

theorem bT_comm_AT {x : TM n} (hx : x ∈ AT hn) : x * bT hn = bT hn * x :=
  AT_comm_BT hn x hx _ (bT_mem_BT hn)

theorem sAbT_mul_self : (sAT n * bT hn) * (sAT n * bT hn) = 1 := by
  rw [mul_mul_mul_self_of_comm (bT_comm_AT hn (sAT_mem_AT hn)), sAT_mul_sAT hn, bT_mul_bT hn,
    one_mul]

theorem sAbT_conj_rAT : (sAT n * bT hn) * rAT n * (sAT n * bT hn)⁻¹ = (rAT n)⁻¹ := by
  rw [← sAT_conj_rAT hn, mul_inv_rev, mul_assoc (sAT n), (bT_comm_AT hn (rAT_mem_AT hn)).symm]
  group

@[expose] noncomputable def fAstar : DihedralGroup (2 ^ (n - 2)) →* TM n :=
  dihedralLift _ (rAT n) (sAT n * bT hn) (rAT_pow_qr hn) (sAbT_mul_self hn) (sAbT_conj_rAT hn)

theorem Astar_le : (footeCoreModel hn).Astar ≤ (fAstar hn).range := by
  rw [FooteCore.Astar, closure_le]
  rintro g ⟨x, hx, hx2, hxa, rfl⟩
  obtain ⟨k, rfl⟩ := (inv_AT_cases hn hx hx2).resolve_left hxa
  refine ⟨DihedralGroup.sr (k : ZMod (2 ^ (n - 2))), ?_⟩
  change sAT n * bT hn * rAT n ^ (k : ZMod (2 ^ (n - 2))).val = sAT n * rAT n ^ k * bT hn
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (rAT_pow_qr hn), mul_assoc, mul_assoc,
    (bT_comm_AT hn (pow_mem (rAT_mem_AT hn) k)).symm]

theorem lifts_Astar : ∀ x ∈ (footeCoreModel hn).Astar, orderOf x = 2 → LiftsSqZ x := by
  intro x hx hx2
  obtain ⟨d, rfl⟩ := Astar_le hn hx
  rcases d with i | i
  ·
    exact lifts_A hn _ (pow_mem (rAT_mem_AT hn) _) hx2
  ·
    change LiftsSqZ (sAT n * bT hn * rAT n ^ i.val)
    obtain ⟨h1, hX, h3⟩ := sA_rA_lift hn i.val
    have hb : toP (Gen.b₀H n) * toP (Gen.b₁H n) ∈ Btil n :=
      mul_mem (mem_Btil.2 (by rw [coe_toP Gen.det_b₀H]; rfl))
        (mem_Btil.2 (by rw [coe_toP Gen.det_b₁H]; rfl))
    rw [mul_assoc, (bT_comm_AT hn (pow_mem (rAT_mem_AT hn) _)).symm, ← mul_assoc, h1, bT,
      b₀T_eq' hn, b₁T_eq' hn, ← map_mul, ← map_mul]
    refine liftsSqZ_of (Or.inl ?_)
    rw [Subgroup.coe_mul, mul_mul_mul_self_of_comm (coe_comm_of_mem_Atil_Btil hX hb),
      h3, Gen.sA_rA_pow_sq hn, Subgroup.coe_mul, coe_toP Gen.det_b₀H, coe_toP Gen.det_b₁H,
      mul_mul_mul_self_of_comm (Gen.commute_b₀H_b₁H hn).eq, Gen.b₀H_sq hn, Gen.b₁H_sq hn,
      Gen.cz_mul_cz hn, mul_one]

end CFSG.CGT.Foote81L6.Bridge
